(* From Iris *)

From Ltac2 Require Ltac2.
From Coq Require Strings.String.
From Coq Require Init.Byte Ascii.
From stdpp Require base options.

Module ident_name.

Import base.
Import options.

(** [ident_name] is a way to remember an identifier within the binder of a
(trivial) function, which can be constructed and retrieved with Ltac but is easy
to forward around opaquely in Gallina (through typeclasses, for example) *)
Definition ident_name := unit → unit.

(** [to_ident_name id] returns a constr of type [ident_name] that holds [id] in
the binder name *)
Ltac to_ident_name id :=
  eval cbv in (ltac:(clear; intros id; assumption) : unit → unit).

(** to_ident_name is a Gallina-level version of [to_ident_name] for constructing
    [ident_name] literals. *)
Notation to_ident_name id := (λ id:unit, id) (only parsing).

(** The idea of [AsIdentName] is to convert the binder in [f] to an [ident_name]
representing the name of the binder. If [f] is not a lambda, this typeclass can
produce the fallback identifier [__unknown]. For example, if the user writes
[bi_exist Φ], there is no binder anywhere to extract.

This class has only one instance, a [Hint Extern] which implements that
conversion to resolve [name] in Ltac (see [solve_as_ident_name]). *)
Class AsIdentName {A B} (f : A → B) (name : ident_name) := as_ident_name {}.
Global Arguments as_ident_name {A B f} name : assert.

Ltac solve_as_ident_name :=
  lazymatch goal with
  (* The [H] here becomes the default name if the binder is anonymous. We use
     [H] with the idea that an unnamed and unused binder is likely to be a
     proposition. *)
  | |- AsIdentName (λ H, _) _ =>
    let name := to_ident_name H in
    notypeclasses refine (as_ident_name name)
  | |- AsIdentName _ _ =>
     let name := to_ident_name ident:(__unknown) in
     notypeclasses refine (as_ident_name name)
  | |- _ => fail "solve_as_ident_name: goal should be `AsIdentName`"
  end.

Global Hint Extern 1 (AsIdentName _ _) => solve_as_ident_name : typeclass_instances.

End ident_name.

Module string_name.

Import Strings.String.
Import Init.Byte Ascii.
Import options.

Import List.ListNotations.
Local Open Scope list.

Module StringToIdent.
  Import Ltac2.

  Ltac2 Type exn ::= [ NotStringLiteral(constr) | InvalidIdent(string) ].

  Ltac2 coq_byte_to_int (b : constr) : int :=
    match! b with
    (* generate this line with python3 -c 'print(" ".join([\'| x%02x => %d\' % (x,x) for x in range(256)]))' *)
    | x00 => 0 | x01 => 1 | x02 => 2 | x03 => 3 | x04 => 4 | x05 => 5 | x06 => 6 | x07 => 7 | x08 => 8 | x09 => 9 | x0a => 10 | x0b => 11 | x0c => 12 | x0d => 13 | x0e => 14 | x0f => 15 | x10 => 16 | x11 => 17 | x12 => 18 | x13 => 19 | x14 => 20 | x15 => 21 | x16 => 22 | x17 => 23 | x18 => 24 | x19 => 25 | x1a => 26 | x1b => 27 | x1c => 28 | x1d => 29 | x1e => 30 | x1f => 31 | x20 => 32 | x21 => 33 | x22 => 34 | x23 => 35 | x24 => 36 | x25 => 37 | x26 => 38 | x27 => 39 | x28 => 40 | x29 => 41 | x2a => 42 | x2b => 43 | x2c => 44 | x2d => 45 | x2e => 46 | x2f => 47 | x30 => 48 | x31 => 49 | x32 => 50 | x33 => 51 | x34 => 52 | x35 => 53 | x36 => 54 | x37 => 55 | x38 => 56 | x39 => 57 | x3a => 58 | x3b => 59 | x3c => 60 | x3d => 61 | x3e => 62 | x3f => 63 | x40 => 64 | x41 => 65 | x42 => 66 | x43 => 67 | x44 => 68 | x45 => 69 | x46 => 70 | x47 => 71 | x48 => 72 | x49 => 73 | x4a => 74 | x4b => 75 | x4c => 76 | x4d => 77 | x4e => 78 | x4f => 79 | x50 => 80 | x51 => 81 | x52 => 82 | x53 => 83 | x54 => 84 | x55 => 85 | x56 => 86 | x57 => 87 | x58 => 88 | x59 => 89 | x5a => 90 | x5b => 91 | x5c => 92 | x5d => 93 | x5e => 94 | x5f => 95 | x60 => 96 | x61 => 97 | x62 => 98 | x63 => 99 | x64 => 100 | x65 => 101 | x66 => 102 | x67 => 103 | x68 => 104 | x69 => 105 | x6a => 106 | x6b => 107 | x6c => 108 | x6d => 109 | x6e => 110 | x6f => 111 | x70 => 112 | x71 => 113 | x72 => 114 | x73 => 115 | x74 => 116 | x75 => 117 | x76 => 118 | x77 => 119 | x78 => 120 | x79 => 121 | x7a => 122 | x7b => 123 | x7c => 124 | x7d => 125 | x7e => 126 | x7f => 127 | x80 => 128 | x81 => 129 | x82 => 130 | x83 => 131 | x84 => 132 | x85 => 133 | x86 => 134 | x87 => 135 | x88 => 136 | x89 => 137 | x8a => 138 | x8b => 139 | x8c => 140 | x8d => 141 | x8e => 142 | x8f => 143 | x90 => 144 | x91 => 145 | x92 => 146 | x93 => 147 | x94 => 148 | x95 => 149 | x96 => 150 | x97 => 151 | x98 => 152 | x99 => 153 | x9a => 154 | x9b => 155 | x9c => 156 | x9d => 157 | x9e => 158 | x9f => 159 | xa0 => 160 | xa1 => 161 | xa2 => 162 | xa3 => 163 | xa4 => 164 | xa5 => 165 | xa6 => 166 | xa7 => 167 | xa8 => 168 | xa9 => 169 | xaa => 170 | xab => 171 | xac => 172 | xad => 173 | xae => 174 | xaf => 175 | xb0 => 176 | xb1 => 177 | xb2 => 178 | xb3 => 179 | xb4 => 180 | xb5 => 181 | xb6 => 182 | xb7 => 183 | xb8 => 184 | xb9 => 185 | xba => 186 | xbb => 187 | xbc => 188 | xbd => 189 | xbe => 190 | xbf => 191 | xc0 => 192 | xc1 => 193 | xc2 => 194 | xc3 => 195 | xc4 => 196 | xc5 => 197 | xc6 => 198 | xc7 => 199 | xc8 => 200 | xc9 => 201 | xca => 202 | xcb => 203 | xcc => 204 | xcd => 205 | xce => 206 | xcf => 207 | xd0 => 208 | xd1 => 209 | xd2 => 210 | xd3 => 211 | xd4 => 212 | xd5 => 213 | xd6 => 214 | xd7 => 215 | xd8 => 216 | xd9 => 217 | xda => 218 | xdb => 219 | xdc => 220 | xdd => 221 | xde => 222 | xdf => 223 | xe0 => 224 | xe1 => 225 | xe2 => 226 | xe3 => 227 | xe4 => 228 | xe5 => 229 | xe6 => 230 | xe7 => 231 | xe8 => 232 | xe9 => 233 | xea => 234 | xeb => 235 | xec => 236 | xed => 237 | xee => 238 | xef => 239 | xf0 => 240 | xf1 => 241 | xf2 => 242 | xf3 => 243 | xf4 => 244 | xf5 => 245 | xf6 => 246 | xf7 => 247 | xf8 => 248 | xf9 => 249 | xfa => 250 | xfb => 251 | xfc => 252 | xfd => 253 | xfe => 254 | xff => 255
    end.

  Ltac2 coq_byte_to_char (b : constr) : char :=
    Char.of_int (coq_byte_to_int b).

  Fixpoint coq_string_to_list_byte (s : string) : list byte :=
    match s with
    | EmptyString => []
    | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
    end.

  (** copy a list of Coq byte constrs into a string (already of the right length) *)
  Ltac2 rec coq_byte_list_blit_list (pos : int) (ls : constr) (str : string) : unit :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
    end.

  Ltac2 rec coq_string_length (s : constr) : int :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    | _ => Control.throw (NotStringLiteral s)
    end.

  Ltac2 compute (c : constr) : constr :=
    Std.eval_vm None c.

  (** [coq_string_to_string] converts a Gallina string in a constr to an Ltac2
  native string *)
  Ltac2 coq_string_to_string (s : constr) : string :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  Ltac2 string_to_ident (s : string) : ident :=
    match Ident.of_string s with
    | Some id => id
    | None => Control.throw (InvalidIdent s)
    end.

  (** [coq_string_to_ident] implements the ident to string conversion in Ltac2 *)
  Ltac2 coq_string_to_ident (s : constr) : ident :=
    string_to_ident (coq_string_to_string s).

  (** We want to wrap [coq_string_to_ident] in an Ltac1 API, but Ltac1-2 FFI
  does not support returning values from Ltac2 to Ltac1. So we provide
  [string_to_ident_cps] in CPS instead. *)

  Ltac string_to_ident_cps :=
    ltac2:(s1 r |- let s := Option.get (Ltac1.to_constr s1) in
                   let ident := coq_string_to_ident s in
                   Ltac1.apply r [Ltac1.of_ident ident] Ltac1.run).
End StringToIdent.

Module IdentToString.
  Import Ltac2.

  Ltac2 get_bit (n : int) (i : int) : bool :=
    Int.equal (Int.land (Int.lsr n i) 1) 1.

  Ltac2 get_bit_coq_bool (n : int) (i : int) : constr :=
    if get_bit n i then constr:(true) else constr:(false).

  Ltac2 char_to_coq_ascii (c : char) : constr :=
    let i := Char.to_int c in
    let bs := Array.init 8 (get_bit_coq_bool i) in
    Constr.Unsafe.make (Constr.Unsafe.App constr:(Ascii) bs).

  Ltac2 string_to_coq_string (s : string) : constr :=
    let len := String.length s in
    let rec to_string i :=
      if Int.equal i len then constr:(EmptyString) else
        let tail := to_string (Int.add i 1) in
        let head := char_to_coq_ascii (String.get s i) in
        constr:(String $head $tail)
    in
    to_string 0.

  Ltac2 ident_to_string (id : ident) : constr :=
    string_to_coq_string (Ident.to_string id).

  Ltac ident_to_string_cps :=
    ltac2:(id r |- let id := Option.get (Ltac1.to_ident id) in
                   let s := ident_to_string id in
                   Ltac1.apply r [Ltac1.of_constr s] Ltac1.run).
End IdentToString.

(** Finally we wrap everything up intro a tactic that renames a variable given
by ident [id] into the name given by string [s]. *)
Ltac rename_by_string id s :=
  StringToIdent.string_to_ident_cps s ltac:(fun x => rename id into x).

(* We also directly expose the CPS primitives. *)
Ltac string_to_ident_cps := StringToIdent.string_to_ident_cps.
Ltac ident_to_string_cps := IdentToString.ident_to_string_cps.

End string_name.

From stdpp Require Import strings.
Require HypercamlInterface.

Import string_name ident_name.

Class IdentNameAsString (name : ident_name) (str : string) := 
  ident_name_as_string {}.
Global Arguments ident_name_as_string {name} str : assert.

Import Ltac2.Ltac2.

Ltac2 get_ident_name (c : constr) : ident option :=
  match Constr.Unsafe.kind c with 
  | Constr.Unsafe.Lambda b _ => 
    Constr.Binder.name b
  | _ => None
  end.

Ltac2 get_id_name (c : constr) : ident :=
  match Constr.Unsafe.kind c with 
  | Constr.Unsafe.Var n => n
  | _ => Option.get (Ident.of_string "H")
  end.

From Ltac2 Require Import Notations.

Ltac2 solve_ident_name_as_string' () : unit :=
  lazy_match! goal with
  (* The [H] here becomes the default name if the binder is anonymous. We use
     [H] with the idea that an unnamed and unused binder is likely to be a
     proposition. *)
  | [|- IdentNameAsString ?x _] =>
    let str := Option.map_default Ident.to_string "" 
      (get_ident_name x) in 
    let coqstr := IdentToString.string_to_coq_string str in
    ltac1:(coqstr |- notypeclasses refine (ident_name_as_string coqstr)) 
      (Ltac1.of_constr coqstr)
  | [|- _] => 
    Message.print (Message.of_string "FAILED");
    ltac1:(fail "solve_ident_name_as_string': goal should be `IdentNameAsString`")
  end.

Ltac solve_ident_name_as_string :=
  ltac2:(solve_ident_name_as_string'()).

Global Hint Extern 1 (IdentNameAsString _ _) => solve_ident_name_as_string : 
  typeclass_instances.

Notation "'ident_name_to_string' idn" :=
  (ltac:(let r := eval cbv in 
    ltac:( let x := fresh in evar (x : string);
    let x := eval unfold x in x in 
    assert (IdentNameAsString idn x) by apply _;
    exact x) in exact r)) (at level 10, only parsing).

Notation "'ident_to_string' id" :=
  (ident_name_to_string (λ id:unit, id)) 
  (at level 10, only parsing).

Notation "'ident_to_string2' id" :=
  (ltac2:(let r := Message.to_string (HypercamlInterface.print_preterm id) in 
    let rc := IdentToString.string_to_coq_string r in
    exact $rc)) (id ident, at level 10, only parsing).


Declare Scope string_notation_scope.

Declare Custom Entry string.

Notation "x" := (ident_to_string2 x) 
  (x ident, in custom string at level 0, only parsing).

(* Notation "'[str' x ']'" := x
  (x custom string at level 0, at level 0). *)

(* 
Generated with the following python code, with some custom modifications to make it compile:

def ofb(b): return "true" if b else "false"
def ofi(i): return f"""Notation "'{chr(i)}' xs" := (String (Ascii.Ascii {ofb((i >> 0) & 0b1)} {ofb((i >> 1) & 0b1)} {ofb((i >> 2) & 0b1)} {ofb((i >> 3) & 0b1)} {ofb((i >> 4) & 0b1)} {ofb((i >> 5) & 0b1)} {ofb((i >> 6) & 0b1)} {ofb((i >> 7) & 0b1)}) xs) (in custom string at level 0, right associativity, only printing, format "'{chr(i)}' xs")."""
for i in range(255): print(ofi(i))

*)

Notation "'NULL' xs" := (String (Ascii.Ascii false false false false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'NULL' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true false false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'	' xs" := (String (Ascii.Ascii true false false true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'	' xs").
Notation "'
' xs" := (String (Ascii.Ascii false true false true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'
' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'
' xs" := (String (Ascii.Ascii true false true true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'
' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true true false false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true false true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true true true false false false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "' ' xs" := (String (Ascii.Ascii false false false false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "' ' xs").
Notation "'!' xs" := (String (Ascii.Ascii true false false false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'!' xs").
Notation "'QUOT' xs" := (String (Ascii.Ascii false true false false false true false false) xs) (in custom string at level 0, right associativity, only printing, format " 'QUOT' xs").
Notation "'#' xs" := (String (Ascii.Ascii true true false false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'#' xs").
Notation "'$' xs" := (String (Ascii.Ascii false false true false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'$' xs").
Notation "'%' xs" := (String (Ascii.Ascii true false true false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'%' xs").
Notation "'&' xs" := (String (Ascii.Ascii false true true false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'&' xs").
Notation "''' xs" := (String (Ascii.Ascii true true true false false true false false) xs) (in custom string at level 0, right associativity, only printing, format "''' xs").
Notation "'(' xs" := (String (Ascii.Ascii false false false true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'(' xs").
Notation "')' xs" := (String (Ascii.Ascii true false false true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "')' xs").
Notation "'*' xs" := (String (Ascii.Ascii false true false true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'*' xs").
Notation "'+' xs" := (String (Ascii.Ascii true true false true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'+' xs").
Notation "',' xs" := (String (Ascii.Ascii false false true true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "',' xs").
Notation "'-' xs" := (String (Ascii.Ascii true false true true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'-' xs").
Notation "'.' xs" := (String (Ascii.Ascii false true true true false true false false) xs) (in custom string at level 0, right associativity, only printing, format "'.' xs").
Notation "'/' xs" := (String (Ascii.Ascii true true true true false true false false) xs) (in custom string at level 0, right associativity, only printing, format " / xs").
Notation "'0' xs" := (String (Ascii.Ascii false false false false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'0' xs").
Notation "'1' xs" := (String (Ascii.Ascii true false false false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'1' xs").
Notation "'2' xs" := (String (Ascii.Ascii false true false false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'2' xs").
Notation "'3' xs" := (String (Ascii.Ascii true true false false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'3' xs").
Notation "'4' xs" := (String (Ascii.Ascii false false true false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'4' xs").
Notation "'5' xs" := (String (Ascii.Ascii true false true false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'5' xs").
Notation "'6' xs" := (String (Ascii.Ascii false true true false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'6' xs").
Notation "'7' xs" := (String (Ascii.Ascii true true true false true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'7' xs").
Notation "'8' xs" := (String (Ascii.Ascii false false false true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'8' xs").
Notation "'9' xs" := (String (Ascii.Ascii true false false true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'9' xs").
Notation "':' xs" := (String (Ascii.Ascii false true false true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "':' xs").
Notation "';' xs" := (String (Ascii.Ascii true true false true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "';' xs").
Notation "'<' xs" := (String (Ascii.Ascii false false true true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'<' xs").
Notation "'=' xs" := (String (Ascii.Ascii true false true true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'=' xs").
Notation "'>' xs" := (String (Ascii.Ascii false true true true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'>' xs").
Notation "'?' xs" := (String (Ascii.Ascii true true true true true true false false) xs) (in custom string at level 0, right associativity, only printing, format "'?' xs").
Notation "'@' xs" := (String (Ascii.Ascii false false false false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'@' xs").
Notation "'A' xs" := (String (Ascii.Ascii true false false false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'A' xs").
Notation "'B' xs" := (String (Ascii.Ascii false true false false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'B' xs").
Notation "'C' xs" := (String (Ascii.Ascii true true false false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'C' xs").
Notation "'D' xs" := (String (Ascii.Ascii false false true false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'D' xs").
Notation "'E' xs" := (String (Ascii.Ascii true false true false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'E' xs").
Notation "'F' xs" := (String (Ascii.Ascii false true true false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'F' xs").
Notation "'G' xs" := (String (Ascii.Ascii true true true false false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'G' xs").
Notation "'H' xs" := (String (Ascii.Ascii false false false true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'H' xs").
Notation "'I' xs" := (String (Ascii.Ascii true false false true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'I' xs").
Notation "'J' xs" := (String (Ascii.Ascii false true false true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'J' xs").
Notation "'K' xs" := (String (Ascii.Ascii true true false true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'K' xs").
Notation "'L' xs" := (String (Ascii.Ascii false false true true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'L' xs").
Notation "'M' xs" := (String (Ascii.Ascii true false true true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'M' xs").
Notation "'N' xs" := (String (Ascii.Ascii false true true true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'N' xs").
Notation "'O' xs" := (String (Ascii.Ascii true true true true false false true false) xs) (in custom string at level 0, right associativity, only printing, format "'O' xs").
Notation "'P' xs" := (String (Ascii.Ascii false false false false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'P' xs").
Notation "'Q' xs" := (String (Ascii.Ascii true false false false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'Q' xs").
Notation "'R' xs" := (String (Ascii.Ascii false true false false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'R' xs").
Notation "'S' xs" := (String (Ascii.Ascii true true false false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'S' xs").
Notation "'T' xs" := (String (Ascii.Ascii false false true false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'T' xs").
Notation "'U' xs" := (String (Ascii.Ascii true false true false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'U' xs").
Notation "'V' xs" := (String (Ascii.Ascii false true true false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'V' xs").
Notation "'W' xs" := (String (Ascii.Ascii true true true false true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'W' xs").
Notation "'X' xs" := (String (Ascii.Ascii false false false true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'X' xs").
Notation "'Y' xs" := (String (Ascii.Ascii true false false true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'Y' xs").
Notation "'Z' xs" := (String (Ascii.Ascii false true false true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'Z' xs").
Notation "'[' xs" := (String (Ascii.Ascii true true false true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "[ xs").
Notation "'\' xs" := (String (Ascii.Ascii false false true true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'\' xs").
Notation "']' xs" := (String (Ascii.Ascii true false true true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "] xs").
Notation "'^' xs" := (String (Ascii.Ascii false true true true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'^' xs").
Notation "'_' xs" := (String (Ascii.Ascii true true true true true false true false) xs) (in custom string at level 0, right associativity, only printing, format "'_' xs").
Notation "'`' xs" := (String (Ascii.Ascii false false false false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'`' xs").
Notation "'a' xs" := (String (Ascii.Ascii true false false false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'a' xs").
Notation "'b' xs" := (String (Ascii.Ascii false true false false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'b' xs").
Notation "'c' xs" := (String (Ascii.Ascii true true false false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'c' xs").
Notation "'d' xs" := (String (Ascii.Ascii false false true false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'d' xs").
Notation "'e' xs" := (String (Ascii.Ascii true false true false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'e' xs").
Notation "'f' xs" := (String (Ascii.Ascii false true true false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'f' xs").
Notation "'g' xs" := (String (Ascii.Ascii true true true false false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'g' xs").
Notation "'h' xs" := (String (Ascii.Ascii false false false true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'h' xs").
Notation "'i' xs" := (String (Ascii.Ascii true false false true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'i' xs").
Notation "'j' xs" := (String (Ascii.Ascii false true false true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'j' xs").
Notation "'k' xs" := (String (Ascii.Ascii true true false true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'k' xs").
Notation "'l' xs" := (String (Ascii.Ascii false false true true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'l' xs").
Notation "'m' xs" := (String (Ascii.Ascii true false true true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'m' xs").
Notation "'n' xs" := (String (Ascii.Ascii false true true true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'n' xs").
Notation "'o' xs" := (String (Ascii.Ascii true true true true false true true false) xs) (in custom string at level 0, right associativity, only printing, format "'o' xs").
Notation "'p' xs" := (String (Ascii.Ascii false false false false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'p' xs").
Notation "'q' xs" := (String (Ascii.Ascii true false false false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'q' xs").
Notation "'r' xs" := (String (Ascii.Ascii false true false false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'r' xs").
Notation "'s' xs" := (String (Ascii.Ascii true true false false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'s' xs").
Notation "'t' xs" := (String (Ascii.Ascii false false true false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'t' xs").
Notation "'u' xs" := (String (Ascii.Ascii true false true false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'u' xs").
Notation "'v' xs" := (String (Ascii.Ascii false true true false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'v' xs").
Notation "'w' xs" := (String (Ascii.Ascii true true true false true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'w' xs").
Notation "'x' xs" := (String (Ascii.Ascii false false false true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'x' xs").
Notation "'y' xs" := (String (Ascii.Ascii true false false true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'y' xs").
Notation "'z' xs" := (String (Ascii.Ascii false true false true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'z' xs").
Notation "'{' xs" := (String (Ascii.Ascii true true false true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'{' xs").
Notation "'|' xs" := (String (Ascii.Ascii false false true true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'|' xs").
Notation "'}' xs" := (String (Ascii.Ascii true false true true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'}' xs").
Notation "'~' xs" := (String (Ascii.Ascii false true true true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'~' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true true true true true false) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true false false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true true false false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true false true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false false true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false false true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true false true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true false true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false false true true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true false true true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii false true true true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "'' xs" := (String (Ascii.Ascii true true true true true false false true) xs) (in custom string at level 0, right associativity, only printing, format "'' xs").
Notation "' ' xs" := (String (Ascii.Ascii false false false false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "' ' xs").
Notation "'¡' xs" := (String (Ascii.Ascii true false false false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¡' xs").
Notation "'¢' xs" := (String (Ascii.Ascii false true false false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¢' xs").
Notation "'£' xs" := (String (Ascii.Ascii true true false false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'£' xs").
Notation "'¤' xs" := (String (Ascii.Ascii false false true false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¤' xs").
Notation "'¥' xs" := (String (Ascii.Ascii true false true false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¥' xs").
Notation "'¦' xs" := (String (Ascii.Ascii false true true false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¦' xs").
Notation "'§' xs" := (String (Ascii.Ascii true true true false false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'§' xs").
Notation "'¨' xs" := (String (Ascii.Ascii false false false true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¨' xs").
Notation "'©' xs" := (String (Ascii.Ascii true false false true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'©' xs").
Notation "'ª' xs" := (String (Ascii.Ascii false true false true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'ª' xs").
Notation "'«' xs" := (String (Ascii.Ascii true true false true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'«' xs").
Notation "'¬' xs" := (String (Ascii.Ascii false false true true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¬' xs").
Notation "'­' xs" := (String (Ascii.Ascii true false true true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'­' xs").
Notation "'®' xs" := (String (Ascii.Ascii false true true true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'®' xs").
Notation "'¯' xs" := (String (Ascii.Ascii true true true true false true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¯' xs").
Notation "'°' xs" := (String (Ascii.Ascii false false false false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'°' xs").
Notation "'±' xs" := (String (Ascii.Ascii true false false false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'±' xs").
Notation "'²' xs" := (String (Ascii.Ascii false true false false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'²' xs").
Notation "'³' xs" := (String (Ascii.Ascii true true false false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'³' xs").
Notation "'´' xs" := (String (Ascii.Ascii false false true false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'´' xs").
Notation "'µ' xs" := (String (Ascii.Ascii true false true false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'µ' xs").
Notation "'¶' xs" := (String (Ascii.Ascii false true true false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¶' xs").
Notation "'·' xs" := (String (Ascii.Ascii true true true false true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'·' xs").
Notation "'¸' xs" := (String (Ascii.Ascii false false false true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¸' xs").
Notation "'¹' xs" := (String (Ascii.Ascii true false false true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¹' xs").
Notation "'º' xs" := (String (Ascii.Ascii false true false true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'º' xs").
Notation "'»' xs" := (String (Ascii.Ascii true true false true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'»' xs").
Notation "'¼' xs" := (String (Ascii.Ascii false false true true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¼' xs").
Notation "'½' xs" := (String (Ascii.Ascii true false true true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'½' xs").
Notation "'¾' xs" := (String (Ascii.Ascii false true true true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¾' xs").
Notation "'¿' xs" := (String (Ascii.Ascii true true true true true true false true) xs) (in custom string at level 0, right associativity, only printing, format "'¿' xs").
Notation "'À' xs" := (String (Ascii.Ascii false false false false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'À' xs").
Notation "'Á' xs" := (String (Ascii.Ascii true false false false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Á' xs").
Notation "'Â' xs" := (String (Ascii.Ascii false true false false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Â' xs").
Notation "'Ã' xs" := (String (Ascii.Ascii true true false false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ã' xs").
Notation "'Ä' xs" := (String (Ascii.Ascii false false true false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ä' xs").
Notation "'Å' xs" := (String (Ascii.Ascii true false true false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Å' xs").
Notation "'Æ' xs" := (String (Ascii.Ascii false true true false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Æ' xs").
Notation "'Ç' xs" := (String (Ascii.Ascii true true true false false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ç' xs").
Notation "'È' xs" := (String (Ascii.Ascii false false false true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'È' xs").
Notation "'É' xs" := (String (Ascii.Ascii true false false true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'É' xs").
Notation "'Ê' xs" := (String (Ascii.Ascii false true false true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ê' xs").
Notation "'Ë' xs" := (String (Ascii.Ascii true true false true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ë' xs").
Notation "'Ì' xs" := (String (Ascii.Ascii false false true true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ì' xs").
Notation "'Í' xs" := (String (Ascii.Ascii true false true true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Í' xs").
Notation "'Î' xs" := (String (Ascii.Ascii false true true true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Î' xs").
Notation "'Ï' xs" := (String (Ascii.Ascii true true true true false false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ï' xs").
Notation "'Ð' xs" := (String (Ascii.Ascii false false false false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ð' xs").
Notation "'Ñ' xs" := (String (Ascii.Ascii true false false false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ñ' xs").
Notation "'Ò' xs" := (String (Ascii.Ascii false true false false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ò' xs").
Notation "'Ó' xs" := (String (Ascii.Ascii true true false false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ó' xs").
Notation "'Ô' xs" := (String (Ascii.Ascii false false true false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ô' xs").
Notation "'Õ' xs" := (String (Ascii.Ascii true false true false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Õ' xs").
Notation "'Ö' xs" := (String (Ascii.Ascii false true true false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ö' xs").
Notation "'×' xs" := (String (Ascii.Ascii true true true false true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'×' xs").
Notation "'Ø' xs" := (String (Ascii.Ascii false false false true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ø' xs").
Notation "'Ù' xs" := (String (Ascii.Ascii true false false true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ù' xs").
Notation "'Ú' xs" := (String (Ascii.Ascii false true false true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ú' xs").
Notation "'Û' xs" := (String (Ascii.Ascii true true false true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Û' xs").
Notation "'Ü' xs" := (String (Ascii.Ascii false false true true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ü' xs").
Notation "'Ý' xs" := (String (Ascii.Ascii true false true true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Ý' xs").
Notation "'Þ' xs" := (String (Ascii.Ascii false true true true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'Þ' xs").
Notation "'ß' xs" := (String (Ascii.Ascii true true true true true false true true) xs) (in custom string at level 0, right associativity, only printing, format "'ß' xs").
Notation "'à' xs" := (String (Ascii.Ascii false false false false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'à' xs").
Notation "'á' xs" := (String (Ascii.Ascii true false false false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'á' xs").
Notation "'â' xs" := (String (Ascii.Ascii false true false false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'â' xs").
Notation "'ã' xs" := (String (Ascii.Ascii true true false false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ã' xs").
Notation "'ä' xs" := (String (Ascii.Ascii false false true false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ä' xs").
Notation "'å' xs" := (String (Ascii.Ascii true false true false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'å' xs").
Notation "'æ' xs" := (String (Ascii.Ascii false true true false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'æ' xs").
Notation "'ç' xs" := (String (Ascii.Ascii true true true false false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ç' xs").
Notation "'è' xs" := (String (Ascii.Ascii false false false true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'è' xs").
Notation "'é' xs" := (String (Ascii.Ascii true false false true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'é' xs").
Notation "'ê' xs" := (String (Ascii.Ascii false true false true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ê' xs").
Notation "'ë' xs" := (String (Ascii.Ascii true true false true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ë' xs").
Notation "'ì' xs" := (String (Ascii.Ascii false false true true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ì' xs").
Notation "'í' xs" := (String (Ascii.Ascii true false true true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'í' xs").
Notation "'î' xs" := (String (Ascii.Ascii false true true true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'î' xs").
Notation "'ï' xs" := (String (Ascii.Ascii true true true true false true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ï' xs").
Notation "'ð' xs" := (String (Ascii.Ascii false false false false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ð' xs").
Notation "'ñ' xs" := (String (Ascii.Ascii true false false false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ñ' xs").
Notation "'ò' xs" := (String (Ascii.Ascii false true false false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ò' xs").
Notation "'ó' xs" := (String (Ascii.Ascii true true false false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ó' xs").
Notation "'ô' xs" := (String (Ascii.Ascii false false true false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ô' xs").
Notation "'õ' xs" := (String (Ascii.Ascii true false true false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'õ' xs").
Notation "'ö' xs" := (String (Ascii.Ascii false true true false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ö' xs").
Notation "'÷' xs" := (String (Ascii.Ascii true true true false true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'÷' xs").
Notation "'ø' xs" := (String (Ascii.Ascii false false false true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ø' xs").
Notation "'ù' xs" := (String (Ascii.Ascii true false false true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ù' xs").
Notation "'ú' xs" := (String (Ascii.Ascii false true false true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ú' xs").
Notation "'û' xs" := (String (Ascii.Ascii true true false true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'û' xs").
Notation "'ü' xs" := (String (Ascii.Ascii false false true true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ü' xs").
Notation "'ý' xs" := (String (Ascii.Ascii true false true true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'ý' xs").
Notation "'þ' xs" := (String (Ascii.Ascii false true true true true true true true) xs) (in custom string at level 0, right associativity, only printing, format "'þ' xs").


Notation "" := (EmptyString)
  (in custom string at level 0, right associativity, only printing,
  format "").




