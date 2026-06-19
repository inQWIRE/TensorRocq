From TensorRocq Require Import Props ProLike PropsGraphs PropGraphTerm Translation.AbstractTensorQuote.

Definition PRO_denote {Struct T T'} (f : T -> T') {n m}
  (p : PRO Struct T n m) : PRO Struct T' n m :=
  map_PRO (λ n m s, s) f p.

Class PRO_quote {Struct T} `{EqStruct : forall n m, Equiv (Struct n m)}
  `{Equiv T'} (f : T -> T') {n m}
  (p : PRO Struct T n m) (p' : PRO Struct T' n m) :=
  quote_pro : PRO_denote f p ≡ p'.

Lemma mk_PRO_quote {Struct T} `{EqStruct : forall n m, Equiv (Struct n m)}
  `{Equiv T'} (f : T -> T') {n m}
  (p : PRO Struct T n m) (p' : PRO Struct T' n m) : 
  PRO_denote f p ≡ p' -> PRO_quote f p p'.
Proof.
  done.
Qed.

From Ltac2 Require Import Ltac2.
From TensorRocq Require Import Ltac2.ConstrExtra Ltac2.FSetExtra.


Ltac2 Type rec JSON := [
  | Jarray (JSON array)
  | Jobject ((string, JSON) FMap.t)
  | Jstring (string)
  | Jfloat (float)
  | Jint (int)
  | Jbool (bool)
  | Jnull
].

Module JSON.

Import PrintingExtra Pp.

(* FIXME: This is a horrible hack... *)
Ltac2 of_float (f : float) : message :=
  of_constr (Constr.Unsafe.make (Unsafe.Float f)).



Ltac2 string_of_char_list (l : char list) : string :=
  let len := List.length l in 
  let s := String.make len (Char.of_int 0) in 
  List.iter2 (fun i c => String.set s i c) (List.seq 0 1 len) l;
  s.

Ltac2 between (i : int) (j : int) (k : int) : bool :=
  Bool.and (Int.le i j) (Int.le j k).

Ltac2 hex_to_char (i : int) : char :=
  if between 0 i 9 then
    Char.of_int (Int.add 48 i)
  else if Int.le i 15 then
    Char.of_int (Int.add 55 i)
  else Char.of_int 0.

Ltac2 char_to_hexes (c : char) : int * int :=
  let ci := Char.to_int c in 
  (Int.div ci 16, Int.mod ci 16).

Ltac2 char_to_unicode_escape (c : char) : string :=
  let (l, r) := char_to_hexes c in 
  string_of_char_list [hex_to_char l; hex_to_char r].

Ltac2 print_JSON_char (c : char) : string :=
  let ci := Char.to_int c in 
  match ci with
  | 8 => "\b"
  | 9 => "\t"
  | 10 => "\n"
  | 12 => "\f"
  | 13 => "\r"
  | 34 => _quote_str()
  | 47 => "\/"
  | 92 => "\\"
  | _ => 
    if Int.lt ci 20 then 
      String.app "\u00" (char_to_unicode_escape c)
    else
      String.make 1 c
  end.

Ltac2 print_JSON_string_aux (str : string) : string :=
  String.concat "" (List.map print_JSON_char (char_list_of_string str)).

Ltac2 str_JSON : string -> message :=
  fun s => quote (str (print_JSON_string_aux s)).

Ltac2 rec print_JSON (j : JSON) : message :=
  match j with
  | Jarray elems => of_list print_JSON (Array.to_list elems) (* TODO: Make array-native print *)
  | Jobject mems => print_map str_JSON print_JSON mems
  | Jstring s => str_JSON s
  | Jfloat f => of_float f
  | Jint i => of_int i
  | Jbool b => (* quote *) (of_bool b)
  | Jnull => (* quote *) (str "null")
  end.


(* Ltac2 Eval Message.print (print_JSON (Jstring "Hello, world")). *)





Ltac2 Type 'a parser := char list -> ('a * char list) option.


Ltac2 parse_may (f : 'a parser) : 'a option parser := 
  fun s => 
  match f s with
  | Some (a, s) => Some (Some a, s)
  | None => Some (None, s)
  end.

Ltac2 parse_seq (f : 'a parser)
  (g : 'b parser)
  (h : 'a -> 'b -> 'c) : 'c parser :=
  fun s => 
  match f s with
  | None => None
  | Some (a, s') => 
    match g s' with
    | None => None
    | Some (b, s'') => 
      Some (h a b, s'')
    end
  end.


Ltac2 parse_seq3 (f : 'a parser)
  (g : 'b parser)
  (h : 'c parser)
  (j : 'a -> 'b -> 'c -> 'd) : 'd parser :=
  fun s => 
  match f s with
  | None => None
  | Some (a, s) => 
    match g s with
    | None => None
    | Some (b, s) => 
      match h s with
      | None => None
      | Some (c, s) => 
        Some (j a b c, s)
      end
    end
  end.

Ltac2 skip (f : 'a parser) (s : char list) : char list :=
  match f s with
  | Some (_, s) => s
  | None => s
  end.

Ltac2 parse_either (f : 'a parser) 
  (g : 'b parser)
  (ofa : 'a -> 'c) (ofb : 'b -> 'c) : 'c parser :=
  fun s => 
  match f s with
  | Some (a, s) => Some (ofa a, s)
  | None => 
    match g s with
    | Some (b, s) => Some (ofb b, s)
    | None => None
    end
  end.

Ltac2 parse_or (f : 'a parser) 
  (g : 'a parser) : 'a parser :=
  fun s => 
  match f s with
  | Some (a, s) => Some (a, s)
  | None => 
    match g s with
    | Some (b, s) => Some (b, s)
    | None => None
    end
  end.


Ltac2 parse_char (c : char) : unit parser :=
  fun s => 
  match s with
  | [] => None
  | c' :: s => 
    if Char.equal c c' then Some ((), s)
    else None
  end.

Ltac2 parse_token_aux (tk : char list) : unit parser :=
  let rec go tk :=
    match tk with
    | [] => fun s => Some ((), s)
    | c :: tk => parse_seq (parse_char c) (go tk) (fun _ _ => ())
    end in 
  go tk.

Ltac2 parse_token (tk : string) : unit parser :=
  parse_token_aux (char_list_of_string tk).



Ltac2 parse_list_with_sep (f : 'a parser) (sep : unit parser)
  (ws : unit parser) : 'a list parser :=
  let rec go s :=
    let s := skip ws s in 
    match parse_seq3 f (parse_may ws) sep (fun a _ _ => a) s with
    | None => Some ([], s)
    | Some (a, s) =>
      match go s with
      | None => Some ([a], s)
      | Some (l, s) => Some (a :: l, s)
      end
    end
  in go.


Ltac2 parse_list_gen (open : unit parser) (close : unit parser) 
  (f : 'a parser) (sep : unit parser)
  (ws : unit parser) : 'a list parser :=
  parse_seq3 open (parse_list_with_sep f sep ws) close 
    (fun _ l _ => l).

Ltac2 map_parse (f : 'a -> 'b) (g : 'a parser) : 'b parser :=
  fun s => 
  match g s with
  | Some (a, s) => Some (f a, s)
  | None => None
  end.

Ltac2 parse_map_gen_aux (open : unit parser) (close : unit parser)
  (ws : unit parser) (sep : unit parser)
  (parse_k : 'k parser) (parse_v : 'v parser) 
  : ('k * 'v) list parser :=
  parse_list_gen open close
    (parse_seq3 (parse_seq ws parse_k (fun _ k => k))
      (parse_seq3 ws (parse_token ":") ws (fun _ _ _ => ()))
      (parse_seq parse_v ws (fun v _ => v))
      (fun k _ v => (k, v))) sep ws.


Ltac2 parse_map_gen (open : unit parser) (close : unit parser)
  (ws : unit parser) (sep : unit parser)
  (parse_k : 'k parser) (parse_v : 'v parser) 
  (k_tag : 'k FSet.Tags.tag) : ('k, 'v) FMap.t parser :=
  map_parse (FMap.of_list k_tag) (parse_map_gen_aux open close 
    ws sep parse_k parse_v).
  


Ltac2 parse_digit : int parser :=
  fun s => match s with
  | [] => None
  | c :: s => 
    let ic := Char.to_int c in 
    if between 48 ic 57 then
      Some (Int.sub ic 48, s)
    else None
  end.

Ltac2 int_of_digits (ds : int list) : int :=
  let rec go acc ds :=
    match ds with
    | [] => acc
    | d :: ds => go (Int.add (Int.mul acc 10) d) ds
    end in 
  go 0 ds.

Ltac2 parse_minus : bool parser :=
  fun s =>
  match s with
  | [] => None
  | c :: s => 
    let ci := (Char.to_int c) in
    if Int.equal ci 45 then Some (true, s) else 
    if Int.equal ci 43 then Some (false, s) else None
  end.

(* Ltac2 Eval int_of_digits [1;2;3]. *)


Ltac2 parse_digit_list : (int list) parser :=
  let rec go rds s :=
    match parse_digit s with
    | None => (List.rev rds, s)
    | Some (d, s) => go (d :: rds) s
    end
  in 
  fun s => 
  match go [] s with
  | ([], _) => None
  | (ds, s) => Some (ds, s)
  end.

Ltac2 parse_digits : int parser :=
  fun s => map_parse int_of_digits parse_digit_list s.

Ltac2 parse_int : int parser :=
  let rec go rds s :=
    match parse_digit s with
    | None => (List.rev rds, s)
    | Some (d, s) => go (d :: rds) s
    end
  in 
  fun s =>
  let (minus, s) := match parse_minus s with
    | Some (b, s) => (b, s)
    | None => (false, s)
    end in 
  match go [] s with
  | ([], _s) => None
  | (ds, s) =>
    let i := int_of_digits ds in 
    let i := if minus then Int.neg i else i in 
    Some (i, s)
  end.


Ltac2 parse_fraction : int list parser :=
  fun s => parse_seq (parse_token ".") parse_digit_list (fun _ l => l) s.

Ltac2 parse_exponent : int parser :=
  fun s => parse_seq (parse_or (parse_token "E") (parse_token "e")) parse_int (fun _ l => l) s.



Ltac2 parse_hex_digit : int parser :=
  fun s => match s with
  | [] => None
  | c :: s => 
    let ic := Char.to_int c in 
    if between 48 ic 57 then 
      Some (Int.sub ic 48, s)
    else 
    if between 65 ic 70 then
      Some (Int.sub ic 55, s)
    else
    if between 97 ic 102 then
      Some (Int.sub ic 87, s)
    else
      None
  end.



(* Import Printf. *)

Ltac2 backspace () : string :=
  string_of_char_list [Char.of_int 8].
Ltac2 formfeed () : string :=
  string_of_char_list [Char.of_int 11].
Ltac2 newline () : string :=
  string_of_char_list [Char.of_int 10].
Ltac2 carriagereturn () : string :=
  string_of_char_list [Char.of_int 13].
Ltac2 horiztab () : string :=
  string_of_char_list [Char.of_int 9].

Ltac2 parse_token_to (tk : string) (a : 'a) : 'a parser :=
  map_parse (fun _ => a) (parse_token tk).

Ltac2 rec parse_first (fs : 'a parser list) : 'a parser :=
  match fs with
  | [] => fun _ => None
  | f :: fs => 
      parse_or f (parse_first fs)
  end.

Ltac2 parse_unicode_escape_aux_char : char parser :=
  fun s => 
  parse_seq parse_hex_digit parse_hex_digit
  (fun l r => Char.of_int (Int.add (Int.mul l 256) r)) s.

Ltac2 parse_unicode_escape : string parser :=
  fun s => 
  parse_seq3 (parse_token "u")
    parse_unicode_escape_aux_char parse_unicode_escape_aux_char
    (fun _ c d => string_of_char_list [c; d]) s.

Ltac2 parse_string_escape_aux : string parser :=
  fun s => 
  parse_first [
    parse_token_to (_quote_str()) (_quote_str());
    parse_token_to "\" "\";
    parse_token_to "/" "/";
    parse_token_to "b" (backspace());
    parse_token_to "f" (formfeed());
    parse_token_to "n" (newline());
    parse_token_to "r" (carriagereturn());
    parse_token_to "t" (horiztab());
    parse_unicode_escape
  ] s.

Ltac2 rec parse_star (f : 'a parser) : 'a list parser :=
  fun s => 
  match f s with
  | None => Some ([], s)
  | Some (a, s) => 
    match parse_star f s with
    | None => Some ([a], s)
    | Some (l, s) => Some (a :: l, s)
    end
  end.

Ltac2 parse_string_character : string parser :=
  fun s => 
  match s with
  | [] => None
  | c :: s => 
    let ci := Char.to_int c in 
    if Int.lt ci 20 then 
      None
    else if Int.equal ci 34 then 
      None
    else if Int.equal ci 92 then
      parse_string_escape_aux s
    else
      Some (String.make 1 c, s)
  end.

Ltac2 parse_string_contents : string parser :=
  fun s => 
  map_parse (String.concat "")
  (parse_star parse_string_character) s.

Ltac2 parse_string : string parser :=
  fun s => parse_seq3 (parse_token (_quote_str()))
  parse_string_contents
  (parse_token (_quote_str()))
  (fun _ str _ => str) s.

Ltac2 ws_JSON : unit parser :=
  fun s => 
  map_parse (fun _ => ()) (parse_star (parse_first [
    parse_char (Char.of_int 0x20);
    parse_char (Char.of_int 0x0A);
    parse_char (Char.of_int 0x0D);
    parse_char (Char.of_int 0x09)
    (* parse_token "" *)
  ])) s.

Ltac2 parse_bool : bool parser :=
  fun s => 
  parse_first [
    parse_token_to "true" true;
    parse_token_to "false" false
  ] s.

Ltac2 Type number := [
  | Nint (int)
  | Nfloat (float)
].

Ltac2 jnumber (n : number) : JSON :=
  match n with
  | Nint i => Jint i
  | Nfloat f => Jfloat f
  end.

Ltac2 parse_JSON : JSON parser :=
  fun s => 
  let rec parse_element : JSON parser :=
    fun s => parse_seq3 ws_JSON parse_value ws_JSON (fun _ js _ => js) s
  with parse_value : JSON parser :=
    fun s => 
      parse_first [
        map_parse (fun m => Jobject m) parse_object;
        map_parse (fun a => Jarray a) parse_array;
        map_parse (fun s => Jstring s) parse_string;
        map_parse jnumber parse_number;
        map_parse (fun b => Jbool b) parse_bool;
        parse_token_to "null" Jnull
      ] s
  with parse_object : (string, JSON) FMap.t parser :=
    fun s => 
      parse_map_gen (parse_token "{") (parse_token "}")
        ws_JSON (parse_token ",")
        parse_string parse_element FSet.Tags.string_tag s

  with parse_array : JSON array parser :=
   fun s => 
    map_parse (fun l => Array.of_list l)
      (parse_list_gen (parse_token "[") (parse_token "]")
        parse_element (parse_token ",") ws_JSON) s
  with parse_number : number parser :=
    fun s => 
    map_parse (fun n => Nint n) parse_int s
  in 
  parse_element s.

Ltac2 parse_of_string (f : 'a parser) (s : string) : ('a * string) option :=
  Option.map (fun (a, c) => (a, string_of_char_list c)) (f (char_list_of_string s)).

Ltac2 to_obj (j : JSON) : (string, JSON) FMap.t option :=
  match j with
  | Jobject m => Some m
  | _ => None
  end.


Ltac2 rec equal (j : JSON) (j' : JSON) : bool :=
  match j, j' with
  | Jarray a, Jarray a' => Array.equal equal a a'
  | Jobject m, Jobject m' => 
    FMap.equal equal m m'
  | Jstring s, Jstring s' => String.equal s s'
  | Jfloat f, Jfloat f' => Float.equal f f'
  | Jint i, Jint i' => Int.equal i i'
  | Jbool b, Jbool b' => Bool.equal b b'
  | Jnull, Jnull => true
  | _, _ => false
  end.

Ltac2 find_opt (j : JSON) (s : string) : JSON option :=
  match j with
  | Jobject m => FMap.find_opt s m
  | _ => None
  end.

Ltac2 jlist (js : JSON list) : JSON :=
  Jarray (Array.of_list js).

End JSON.



(* Time Ltac2 Eval parse_of_string ws_JSON "                     ". *)
(* Ltac2 Eval parse_of_string parse_JSON "[33]".

Ltac2 Eval parse_JSON ([Char.of_int(123);Char.of_int(34);Char.of_int(97);Char.of_int(34);Char.of_int(58);Char.of_int(34);Char.of_int(98);Char.of_int(34);Char.of_int(44);Char.of_int(34);Char.of_int(97);Char.of_int(34);Char.of_int(58);Char.of_int(34);Char.of_int(99);Char.of_int(34);Char.of_int(125)]). *)
  





(* Ltac2 Eval parse_string_character (char_list_of_string
  "\n").


Ltac2 Eval parse_token (_quote_str()) 
  (char_list_of_string (String.concat (_quote_str())
  [""; ""])).

  
Ltac2 Eval parse_string (char_list_of_string (String.concat (_quote_str())
  ["";"\n"; ""])).

Ltac2 Eval parse_string_contents (char_list_of_string (String.concat (_quote_str())
  ["n"; ""])). *)






Ltac2 Type rec ('n, 's, 't) PRO := [
  | Pid ('n)
  | Pcompose (('n, 's, 't) PRO, ('n, 's, 't) PRO)
  | Pstack (('n, 's, 't) PRO, ('n, 's, 't) PRO)
  | Pstruct ('n, 'n, 's)
  | Pgen ('n, 'n, 't)
].

Ltac2 rec map_PRO (fn : 'n1 -> 'n2) (f : 's1 -> 's2) (g : 't1 -> 't2)
  (p : ('n1, 's1, 't1) PRO) : ('n2, 's2, 't2) PRO :=
  let rec go p :=
    match p with
    | Pid n => Pid (fn n)
    | Pcompose l r => Pcompose (go l) (go r)
    | Pstack l r => Pstack (go l) (go r)
    | Pstruct n m s => Pstruct (fn n) (fn m) (f s)
    | Pgen n m t => Pgen (fn n) (fn m) (g t)
    end
  in
  go p.

Ltac2 dim_PRO (nadd : 'n -> 'n -> 'n) (p : ('n, 's, 't) PRO) : 'n * 'n :=
  let rec go p :=
    match p with
    | Pid n => (n, n)
    | Pcompose l r =>
      let (n, _) := go l with (_, m) := go r in (n, m)
    | Pstack l r =>
      let (n1, m1) := go l with (n2, m2) := go r in (nadd n1 n2, nadd m1 m2)
    | Pstruct n m _ => (n, m)
    | Pgen n m _ => (n, m)
    end
  in go p.












Module Option.

Export Ltac2.Option.

Ltac2 map2 (f : 'a -> 'b -> 'c) (ma : 'a option) (mb : 'b option) :=
  match ma with
  | None => None
  | Some a => 
    match mb with
    | None => None
    | Some b => Some (f a b)
    end
  end.

Ltac2 bind2 (ma : 'a option) (mb : 'b option) (f : 'a -> 'b -> 'c option) :=
  match ma with
  | None => None
  | Some a => 
    match mb with
    | None => None
    | Some b => f a b
    end
  end.

Ltac2 map3 (f : 'a -> 'b -> 'c -> 'd) 
  (ma : 'a option) (mb : 'b option) (mc : 'c option) :=
  match ma with
  | None => None
  | Some a => 
    match mb with
    | None => None
    | Some b => 
      match mc with
      | None => None
      | Some c => Some (f a b c)
      end
    end
  end.
  
Ltac2 bind3 (ma : 'a option) (mb : 'b option) (mc : 'c option)
  (f : 'a -> 'b -> 'c -> 'd option) :=
  match ma with
  | None => None
  | Some a => 
    match mb with
    | None => None
    | Some b => 
      match mc with
      | None => None
      | Some c => f a b c
      end
    end
  end.

End Option.


Ltac2 Type ('a, 'b) Sum := [
  | Inl ('a)
  | Inr ('b)
].

Ltac2 inl (a : 'a) : ('a, 'b) Sum := Inl a.
Ltac2 inr (b : 'b) : ('a, 'b) Sum := Inr b.

Ltac2 sum_elim (f : 'a -> 'c) (g : 'b -> 'c) (s : ('a, 'b) Sum) : 'c :=
  match s with
  | Inl a => f a
  | Inr b => g b
  end.

Ltac2 sum_map (f : 'a -> 'c) (g : 'b -> 'd) (s : ('a, 'b) Sum) : ('c, 'd) Sum :=
  match s with
  | Inl a => Inl (f a)
  | Inr b => Inr (g b)
  end.


Ltac2 Type 'n Monoidal := [
  | Associator ('n, 'n, 'n)
  | InvAssociator ('n, 'n, 'n)
  | LUnit ('n)
  | InvLUnit ('n)
  | RUnit ('n)
  | InvRUnit ('n)
].

Ltac2 Type 'n Symmetry := [
  | Swap ('n, 'n)
].

Ltac2 Type 'n Autonomy := [
  | Cup ('n)
  | Cap ('n)
].

Ltac2 Type 'n Frobenial := [
  | Delta ('n, 'n)
].

Ltac2 Type 'n SymmetricG := ('n Monoidal, 'n Symmetry) Sum.
Ltac2 Type 'n Autonomous := ('n SymmetricG, 'n Autonomy) Sum.
Ltac2 Type 'n Frobenius := ('n Autonomous, 'n Frobenial) Sum.

Import Ltac2.FSetExtra.

Import MapNotations FSet.Tags.

Ltac2 json_of_PRO (of_n : 'n -> JSON) (of_s : 's -> JSON) (of_t : 't -> JSON)
  (p : ('n, 's, 't) PRO) : JSON :=
  let rec go p :=
    match p with
    | Pid n => Jobject (!Map(string_tag) {
      "type" : Jstring "id";
      "size" : of_n n})
    | Pstruct n m s => Jobject (!Map(string_tag) {
      "type" : Jstring "struct";
      "insize" : of_n n;
      "outsize" : of_n m;
      "data" : of_s s})
    | Pgen n m t => Jobject (!Map(string_tag) {
      "type" : Jstring "gen";
      "insize" : of_n n;
      "outsize" : of_n m;
      "data" : of_t t})
    | Pcompose l r => Jobject (!Map(string_tag) {
      "type" : Jstring "compose";
      "left" : go l;
      "right" : go r})
    | Pstack l r => Jobject (!Map(string_tag) {
      "type" : Jstring "stack";
      "top" : go l;
      "bottom" : go r})
    end in 
  go p.

Ltac2 json_to_PRO (to_n : JSON -> 'n option) 
  (to_s : JSON -> 's option) (to_t : JSON -> 't option)
  (j : JSON) : ('n, 's, 't) PRO option :=
  let rec go j := 
    match JSON.find_opt j "type" with
    | Some (Jstring t) => match t with
      | "id" => Option.bind (JSON.find_opt j "size")
        (fun s => Option.map (fun n => Pid n) (to_n s))
      | "struct" => 
        Option.bind3 (JSON.find_opt j "insize") (JSON.find_opt j "outsize")
          (JSON.find_opt j "data") 
        (fun ins outs s => 
          Option.map3 (fun n m s => Pstruct n m s) (to_n ins) (to_n outs) (to_s s))
      | "gen" => 
        Option.bind3 (JSON.find_opt j "insize") (JSON.find_opt j "outsize")
          (JSON.find_opt j "data") 
        (fun ins outs t => 
          Option.map3 (fun n m s => Pgen n m s) (to_n ins) (to_n outs) (to_t t))
      | "compose" => 
        Option.bind2 (JSON.find_opt j "left") (JSON.find_opt j "right")
          (fun l r => Option.map2 (fun l r => Pcompose l r) (go l) (go r))
      | "stack" => 
        Option.bind2 (JSON.find_opt j "top") (JSON.find_opt j "bottom")
          (fun l r => Option.map2 (fun l r => Pstack l r) (go l) (go r))
      | _ => None
      end
    | _ => None
    end
  in go j.

Ltac2 dim_Monoidal (nzero : 'n) (nplus : 'n -> 'n -> 'n)
  (ns : 'm -> 'n)
  (m : 'm Monoidal) : 'n * 'n :=
  match m with
  | Associator n m o =>
    (nplus (nplus (ns n) (ns m)) (ns o),
    nplus (ns n) (nplus (ns m) (ns o)))
  | InvAssociator n m o =>
    (nplus (ns n) (nplus (ns m) (ns o)),
    nplus (nplus (ns n) (ns m)) (ns o))
  | LUnit n => 
    (nplus nzero (ns n), ns n)
  | InvLUnit n => 
    (ns n, nplus nzero (ns n))
  | RUnit n => 
    (nplus (ns n) nzero, ns n)
  | InvRUnit n => 
    (ns n, nplus (ns n) nzero)
  end.

Ltac2 dim_Symmetry (_nzero : 'n) (nplus : 'n -> 'n -> 'n)
  (ns : 'm -> 'n)
  (m : 'm Symmetry) : 'n * 'n :=
  match m with
  | Swap n m =>
    (nplus (ns n) (ns m),
      nplus (ns m) (ns n))
  end.

Ltac2 dim_Autonomy (nzero : 'n) (nplus : 'n -> 'n -> 'n)
  (ns : 'm -> 'n)
  (m : 'm Autonomy) : 'n * 'n :=
  match m with
  | Cup n =>
    (nzero, nplus (ns n) (ns n))
  | Cap n =>
    (nplus (ns n) (ns n), nzero)
  end.


Ltac2 json_of_Monoidal (of_n : 'n -> JSON)
  (p : 'n Monoidal) : JSON :=
  let size := JSON.jlist 
    (List.map of_n (fst (dim_Monoidal [] List.append (fun x => [x]) p))) in
  Jobject (!Map(string_tag) {
    "type" : Jstring "associator";
    "size" : size}).

Ltac2 json_of_Symmetry (of_n : 'n -> JSON)
  (p : 'n Symmetry) : JSON :=
  let (n, m) := match p with | Swap n m => (n, m) end in 
  Jobject (!Map(string_tag) {
    "type" : Jstring "swap";
    "top" : of_n n;
    "bottom" : of_n m}).

Ltac2 json_of_Autonomy (of_n : 'n -> JSON)
  (p : 'n Autonomy) : JSON :=
  let (name, n) := match p with | Cup n => ("cup", n) | Cap n => ("cap", n) end in 
  Jobject (!Map(string_tag) {
    "type" : Jstring name;
    "size" : of_n n}).

Ltac2 json_of_Frobenial (of_n : 'n -> JSON)
  (p : 'n Frobenial) : JSON :=
  let (n, m) := match p with | Delta n m => (n, m) end in
  Jobject (!Map(string_tag) {
    "type" : Jstring "delta";
    "spidertype" : Jint 0; (* TODO: Fix when we have proper sense of sized deltas *)
    "insize" : of_n n;
    "outsize" : of_n m}).

Ltac2 json_of_SymmetricG (of_n : 'n -> JSON)
  (p : 'n SymmetricG) : JSON :=
  sum_elim (json_of_Monoidal of_n) (json_of_Symmetry of_n) p.

Ltac2 json_of_Autonomous (of_n : 'n -> JSON)
  (p : 'n Autonomous) : JSON :=
  sum_elim (json_of_SymmetricG of_n) (json_of_Autonomy of_n) p.

Ltac2 json_of_Frobenius (of_n : 'n -> JSON)
  (p : 'n Frobenius) : JSON :=
  sum_elim (json_of_Autonomous of_n) (json_of_Frobenial of_n) p.


Module CC.

Export ConstrExtra.CC.

Ltac2 to_PRO_safe (struct_T : constr) (t_T : constr)
  (to_n : 'n -> constr) (to_s : 's -> constr)
  (to_t : 't -> constr) : ('n, 's, 't) PRO -> constr * constr * constr :=
  let rec go p :=
    match p with
    | Pid n => let cn := to_n n in (cn, cn, '(@Pid $struct_T $t_T $cn))
    | Pcompose l r =>
      let (nl, _ml, cl) := go l with (nr, mr, cr) := go r in
      (nl, mr, '(@Pcompose $struct_T $t_T $nl $nr $mr $cl $cr))
    | Pstack l r =>
      let (nl, ml, cl) := go l with (nr, mr, cr) := go r in
      ('(Nat.add $nl $nr), '(Nat.add $ml $mr),
        '(@Pstack $struct_T $t_T $nl $ml $nr $mr $cl $cr))
    | Pstruct n m s =>
      let cn := to_n n with cm := to_n m with cs := to_s s in
      (cn, cm, '(@Pstruct $struct_T $t_T $cn $cm $cs))
    | Pgen n m t =>
      let cn := to_n n with cm := to_n m with ct := to_t t in
      (cn, cm, '(@Pgen $struct_T $t_T $cn $cm $ct))
    end
  in go.

Ltac2 to_PRO (to_n : 'n -> constr) (to_t : 't -> constr) (to_s : 's -> constr) :
  ('n, 's, 't) PRO -> constr :=
  let rec go p :=
    match p with
    | Pid n =>
      let cn := to_n n in
      '(Pid $cn)
    | Pcompose l r =>
      let cl := go l with cr := go r in
      '(Pcompose $cl $cr)
    | Pstack l r =>
      let cl := go l with cr := go r in
      '(Pstack $cl $cr)
    | Pstruct n m s =>
      let cn := to_n n with cm := to_n m with cs := to_s s in
      '(Pstruct $cn $cm $cs)
    | Pgen n m t =>
      let cn := to_n n with cm := to_n m with ct := to_t t in
      '(Pgen $cn $cm $ct)
    end
  in go.

Ltac2 of_PRO_safe
  (nadd : 'n -> 'n -> 'n)
  (of_n : constr -> 'n) (of_s : constr -> 's)
  (of_t : constr -> 't) : constr -> 'n * 'n * ('n, 's, 't) PRO :=
  let rec go p :=
    let step p :=
      lazy_match! p with
      | Pid ?n => let cn := of_n n in (cn, cn, (Pid cn))
      | Pcompose ?l ?r =>
        let (nl, _ml, cl) := go l with (_nr, mr, cr) := go r in
        (nl, mr, (Pcompose cl cr))
      | Pstack ?l ?r =>
        let (nl, ml, cl) := go l with (nr, mr, cr) := go r in
        (nadd nl nr, nadd ml mr, (Pstack cl cr))
      | Pstruct ?n ?m ?s =>
        let cn := of_n n with cm := of_n m with cs := of_s s in
        (cn, cm, (Pstruct cn cm cs))
      | Pgen ?n ?m ?t =>
        let cn := of_n n with cm := of_n m with ct := of_t t in
        (cn, cm, (Pgen cn cm ct))
      end
    in
    match! p with
    | ?p => step p
    | _ =>
      (* let p' := Std.eval_red p in
      if Constr.equal p' p then *)
        let p' := Std.eval_hnf p in
        if Constr.equal p' p then
          Control.throw_invalid_argument
            (String.app
              "of_PRO_safe: argument is not reducible to a [PRO] constant: "
              (Message.to_string (Message.of_constr p)))
        else step p'
      (* else step p' *)
    end
  in go.



Ltac2 of_PRO
  (of_n : constr -> 'n) (of_s : constr -> 's)
  (of_t : constr -> 't) : constr -> ('n, 's, 't) PRO :=
  let rec go p :=
    let step p :=
      lazy_match! p with
      | Pid ?n => let cn := of_n n in (Pid cn)
      | Pcompose ?l ?r =>
        let cl := go l with cr := go r in
        (Pcompose cl cr)
      | Pstack ?l ?r =>
        let cl := go l with cr := go r in
        Pstack cl cr
      | Pstruct ?n ?m ?s =>
        let cn := of_n n with cm := of_n m with cs := of_s s in
        Pstruct cn cm cs
      | Pgen ?n ?m ?t =>
        let cn := of_n n with cm := of_n m with ct := of_t t in
        Pgen cn cm ct
      end
    in
    Notations.orelse (fun _ => step p)
      (fun e => let p' := Std.eval_hnf p in
        if Constr.equal p' p then
          Control.zero e
          (* Control.throw_invalid_argument
            (String.app
              "of_PRO: argument is not reducible to a [PRO] constant: "
              (Message.to_string (Message.of_constr p))) *)
        else 
        Notations.orelse (fun _ => step p')
        (fun _ => 
        Control.throw_invalid_argument
            (String.app
              "of_PRO: argument is not PARSEABLE to a [PRO] constant: "
              (Message.to_string (Message.of_constr '($p, $p'))))))
  in go.


Ltac2 of_PRO_safe_with
  (nadd : 'n -> 'n -> 'n)
  (of_n : 'state -> constr -> 'state * 'n) (of_s : 'state -> constr -> 'state * 's)
  (of_t : 'state -> constr -> 'state * 't) : 'state -> constr -> 'state * 'n * 'n * ('n, 's, 't) PRO :=
  let rec go st p :=
    let step st p :=
      lazy_match! p with
      | Pid ?n => let (st, cn) := of_n st n in (st, cn, cn, (Pid cn))
      | Pcompose ?l ?r =>
        let (st, nl, _ml, cl) := go st l in let (st, _nr, mr, cr) := go st r in
        (st, nl, mr, (Pcompose cl cr))
      | Pstack ?l ?r =>
        let (st, nl, ml, cl) := go st l in let (st, nr, mr, cr) := go st r in
        (st, nadd nl nr, nadd ml mr, (Pstack cl cr))
      | Pstruct ?n ?m ?s =>
        let (st, cn) := of_n st n in let (st, cm) := of_n st m in let (st, cs) := of_s st s in
        (st, cn, cm, (Pstruct cn cm cs))
      | Pgen ?n ?m ?t =>
        let (st, cn) := of_n st n in let (st, cm) := of_n st m in let (st, ct) := of_t st t in
        (st, cn, cm, (Pgen cn cm ct))
      end
    in
    match! p with
    | ?p => step st p
    | _ =>
      (* let p' := Std.eval_red p in
      if Constr.equal p' p then *)
        let p' := Std.eval_hnf p in
        if Constr.equal p' p then
          Control.throw_invalid_argument
            (String.app
              "of_PRO_safe_with: argument is not reducible to a [Frobenius] constant: "
              (Message.to_string (Message.of_constr p)))
        else step st p'
      (* else step st p' *)
    end
  in go.


(* FIXME: Move *)
Ltac2 of_bool (c : constr) : bool :=
  let rec go p :=
    let step p :=
      match! p with
      | true => true
      | false => false
      end
    in
    match! p with
    | ?p => step p
    | _ =>
      let p' := Std.eval_red p in
      if Constr.equal p' p then
        let p' := Std.eval_hnf p in
        if Constr.equal p' p then
          Control.throw_invalid_argument
            (String.app
              "of_bool: argument is not reducible to a [bool] constant: " 
              (Message.to_string (Message.of_constr p)))
        else step p'
      else step p'
    end
  in go c.

Ltac2 to_bool (b : bool) : constr :=
  match b with
  | true => '(Datatypes.true)
  | false => '(Datatypes.false)
  end.

Ltac2 rec extend_evar_ended_list (cs : constr list) (cls : constr) : constr :=
  match! cls with
  | ?cl :: ?cls' => 
    match cs with
    | [] => cls
    | _ :: cs' =>
      let cs_cls := extend_evar_ended_list cs' cls' in 
      '(cons $cl $cs_cls)
    end
  | ?cls => 
    match cs with
    | [] => cls
    | c :: cs => 
      Std.unify '($c :: _) cls;
      extend_evar_ended_list (c :: cs) cls
    end
  end.


Import Message.

Ltac2 mk_of (fn_name : string) (type : string) (of : constr -> 'a) : constr -> 'a :=
  fun c => 
  Notations.orelse
    (fun _ => of c)
    (fun e => 
      let c' := Std.eval_hnf c in 
      (* Message.print (Message.concat (Message.of_string "mk_of reduced: ") 
        (Message.of_constr c')); *)
      if Constr.equal c c' then
        Control.zero e
      else
        Notations.orelse (fun _ => of c')
        (fun e' => 
          Control.throw_invalid_argument
          (String.concat "" [fn_name; ": argument is not parseable as a [";
            type; "] constant: "; to_string (of_constr c);
            " (reduced to "; to_string (of_constr c');
            "; parser failed first with error "; 
            to_string (of_exn e);
            ", then with error ";
            to_string (of_exn e')]))
      ).

Ltac2 of_Monoidal (of_n : constr -> 'n) (c : constr) : 'n Monoidal :=
  mk_of "of_Monoidal" "Monoidal"
  (
  let rec go c :=
    lazy_match! c with
    | @Associator ?n ?m ?o => 
      let n' := of_n n in 
      let m' := of_n m in 
      let o' := of_n o in 
      Associator n' m' o'
    | @InvAssociator ?n ?m ?o => 
      let n' := of_n n in 
      let m' := of_n m in 
      let o' := of_n o in 
      InvAssociator n' m' o'
    | @LUnit ?n => 
      let n' := of_n n in 
      LUnit n'
    | @InvLUnit ?n => 
      let n' := of_n n in 
      InvLUnit n'
    | @RUnit ?n => 
      let n' := of_n n in 
      RUnit n'
    | @InvRUnit ?n => 
      let n' := of_n n in 
      InvRUnit n'
    end in  go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Monoidal: argument is not reducible to a [Monoidal] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Monoidal: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_Symmetry (of_n : constr -> 'n) (c : constr) : 'n Symmetry :=
  mk_of "of_Symmetry" "Symmetry" (let rec go c :=
    lazy_match! c with
    | @Swap ?n ?m => 
      let n' := of_n n in 
      let m' := of_n m in
      Swap n' m'
    end in 
    go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Symmetry: argument is not reducible to a [Symmetry] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Symmetry: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_Autonomy (of_n : constr -> 'n) (c : constr) : 'n Autonomy :=
  mk_of "of_Autonomy" "Autonomy" (let rec go c :=
    lazy_match! c with
    | @Cup ?n => 
      let n' := of_n n in 
      Cup n'
    | @Cap ?n => 
      let n' := of_n n in 
      Cap n'
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Autonomy: argument is not reducible to a [Autonomy] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Autonomy: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_Frobenial (of_n : constr -> 'n) (c : constr) : 'n Frobenial :=
  mk_of "of_Frobenial" "Frobenial" (let rec go c :=
    lazy_match! c with
    | @Delta ?n ?m => 
      let n' := of_n n in 
      let m' := of_n m in 
      Delta n' m'
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Frobenial: argument is not reducible to a [Frobenial] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Frobenial: error with argument " (to_string (of_constr c)))
  end. *)



Ltac2 of_SymmetricG (of_n : constr -> 'n) (c : constr) : 'n SymmetricG :=
  mk_of "of_SymmetricG" "SymmetricG" (let rec go c :=
    lazy_match! c with
    | monoidal_inl ?m => 
      inl (of_Monoidal of_n m)
    | inl ?m => 
      inl (of_Monoidal of_n m)
    | symmetry_inr ?m => 
      inr (of_Symmetry of_n m)
    | inr ?m => 
      inr (of_Symmetry of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_SymmetricG: argument is not reducible to a [SymmetricG] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  (* | _ => 
    Control.throw_invalid_argument 
      (String.app "of_SymmetricG: error with argument " (to_string (of_constr c))) *)
  end. *)


Ltac2 of_Autonomous (of_n : constr -> 'n) (c : constr) : 'n Autonomous :=
  mk_of "of_Autonomous" "Autonomous" (let rec go c :=
    lazy_match! c with
    | symmetric_inl ?m => 
      inl (of_SymmetricG of_n m)
    | inl ?m => 
      inl (of_SymmetricG of_n m)
    | autonomy_inr ?m => 
      inr (of_Autonomy of_n m)
    | inr ?m => 
      inr (of_Autonomy of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Autonomous: argument is not reducible to a [Autonomous] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Autonomous: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_Frobenius (of_n : constr -> 'n) (c : constr) : 'n Frobenius :=
  mk_of "of_Frobenius" "Frobenius" (let rec go c :=
    lazy_match! c with
    | autonomous_inl ?m => 
      inl (of_Autonomous of_n m)
    | inl ?m => 
      inl (of_Autonomous of_n m)
    | frobenial_inr ?m => 
      inr (of_Frobenial of_n m)
    | inr ?m => 
      inr (of_Frobenial of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Frobenius: argument is not reducible to a [Frobenius] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Frobenius: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 to_Monoidal (to_n : 'n -> constr) (m : 'n Monoidal) : constr :=
  match m with
  | Associator n m o => 
    let n' := to_n n in 
    let m' := to_n m in 
    let o' := to_n o in 
    '(Associator $n' $m' $o')
  | InvAssociator n m o => 
    let n' := to_n n in 
    let m' := to_n m in 
    let o' := to_n o in 
    '(InvAssociator $n' $m' $o')
  | LUnit n => 
    let n' := to_n n in 
    '(LUnit $n')
  | InvLUnit n => 
    let n' := to_n n in 
    '(InvLUnit $n')
  | RUnit n => 
    let n' := to_n n in 
    '(RUnit $n')
  | InvRUnit n => 
    let n' := to_n n in 
    '(InvRUnit $n')
  end.

Ltac2 to_Symmetry (to_n : 'n -> constr) (m : 'n Symmetry) : constr :=
  match m with
  | Swap n m => 
    let n' := to_n n in 
    let m' := to_n m in 
    '(Swap $n' $m')
  end.

Ltac2 to_Autonomy (to_n : 'n -> constr) (m : 'n Autonomy) : constr :=
  match m with
  | Cup n => 
    let n' := to_n n in 
    '(Cup $n')
  | Cap n => 
    let n' := to_n n in 
    '(Cap $n')
  end.

Ltac2 to_Frobenial (to_n : 'n -> constr) (m : 'n Frobenial) : constr :=
  match m with
  | Delta n m => 
    let n' := to_n n in 
    let m' := to_n m in 
    '(Delta $n' $m')
  end.

Ltac2 to_SymmetricG (to_n : 'n -> constr) (m : 'n SymmetricG) : constr :=
  sum_elim (to_Monoidal to_n) (to_Symmetry to_n) m.

Ltac2 to_Autonomous (to_n : 'n -> constr) (m : 'n Autonomous) : constr :=
  sum_elim (to_SymmetricG to_n) (to_Autonomy to_n) m.

Ltac2 to_Frobenius (to_n : 'n -> constr) (m : 'n Frobenius) : constr :=
  sum_elim (to_Autonomous to_n) (to_Frobenial to_n) m.


(* Goal True.
Proof Mode "Classic".
evar (l : list nat).
let l := eval unfold l in l in assert (l = []).
Proof Mode "Ltac2".
match! goal with
| [|- ?l = _] => 
  extend_evar_ended_list ['(1); '(2)] l
end. *)


End CC.


Ltac2 rec map_PRO_with (fn : 'state -> 'n1 -> 'state * 'n2) 
  (f : 'state -> 's1 -> 'state * 's2) (g : 'state -> 't1 -> 'state * 't2)
  (st : 'state) (p : ('n1, 's1, 't1) PRO) : 'state * ('n2, 's2, 't2) PRO :=
  let rec go st p :=
    match p with
    | Pid n => 
      let (st, cn) := fn st n in (st, Pid cn)
    | Pcompose l r => 
      let (st, cl) := go st l in let (st, cr) := go st r in 
      (st, Pcompose cl cr)
    | Pstack l r => 
      let (st, cl) := go st l in let (st, cr) := go st r in 
      (st, Pstack cl cr)
    | Pstruct n m s => 
      let (st, cn) := fn st n in let (st, cm) := fn st m in
      let (st, cs) := f st s in 
      (st, Pstruct cn cm cs)
    | Pgen n m t => 
      let (st, cn) := fn st n in let (st, cm) := fn st m in
      let (st, ct) := g st t in 
      (st, Pgen cn cm ct)
    end
  in
  go st p.

From TensorRocq Require Import BWQuote.

Local Ltac2 pair : 'a -> 'b -> 'a * 'b := fun a b => (a, b).

Local Ltac2 id : 'a -> 'a := fun a => a.

Ltac2 intify_PRO (ns : constr list) (p : ('n, 's, constr) PRO) : constr list * ('n, 's, int) PRO :=
  map_PRO_with pair pair constr_get_nth ns p.

Ltac2 mk_PRO_quote_interp_discrete_hg_inhab () :=
  match! goal with
  | [|- PRO_quote (Struct:=?struct_T) (interp_discrete_hg_inhab (T:=?t_T) ?cts) 
    (n:=?_cn) (m:=?_cm) ?cqp ?cp] =>
    let p := CC.of_PRO id id id cp in 
    let ts := CC.of_list id cts in 
    let (ts', pi) := (intify_PRO ts p) in 
    let pi := map_PRO id id (fun x => CC.to_pos (Int.add x 1)) pi in 
    let (_, _, cpi) := CC.to_PRO_safe struct_T t_T id id id pi in
    let cts := CC.extend_evar_ended_list ts' cts in 
    Std.unify cqp cpi;
    refine '(mk_PRO_quote (interp_discrete_hg_inhab $cts) $cpi $cp _);
    reflexivity
  end.

(* Goal True.
Open Scope positive_scope.
Check ((Pgen 1 2 xH ;; Pswap 1 1 ;; Pgen 1 2 10%positive * Pgen 1 0 5%positive)%pro : PROP positive _ _).
Ltac2 Eval 
  let c := '((Pgen 1 2 xH ;; Pswap 1 1 ;; Pgen 1 2 10%positive * Pgen 1 0 5%positive)%pro : PROP positive _ _) in
  Std.resolve_tc c;
  let p := CC.of_PRO CC.of_nat (CC.of_SymmetricG CC.of_nat) id c in 
  let of_int := (fun i => JSON.jlist (List.repeat (Jint 0) i)) in
  let jp := json_of_PRO of_int
    (json_of_SymmetricG of_int)
    (fun i => Jstring (Message.to_string (Message.of_constr i))) p in 
  let dp := Jobject (!Map(string_tag){
    "type" : Jstring "diagram";
    "types" : JSON.jlist [Jstring "1"];
    "data" : jp
  }) in 
  Message.print (JSON.print_JSON (dp)).



Ltac2 Eval 
  let c := '(includeStruct (Swap 1 1) : SymmetricG _ _) in
  Std.resolve_tc c;
  CC.of_SymmetricG CC.of_nat c. *)

(* Ltac2 Eval 
  let c :=
  (CC.of_SymmetricG CC.of_nat)
  '(includeStruct (Swap 1 1) : SymmetricG _ _). *)


(* Ltac2 Eval
  let of_n := CC.of_nat in 
  let of_s := (CC.of_SymmetricG CC.of_nat) in 
  let p := '([str includeStruct (Swap 1 1)]%pro : PROP positive _ _) in 
  lazy_match! p with
  | Pstruct ?n ?m ?s =>
    let cn := of_n n with cm := of_n m with cs := of_s s in
    Pstruct cn cm cs
  end.



Set Ltac2 Backtrace.
 Ltac2 Eval CC.of_PRO CC.of_nat
  (CC.of_SymmetricG CC.of_nat)
  CC.of_pos
  '([str includeStruct (Swap 1 1)]%pro : PROP positive _ _).


  Ltac2 Eval CC.of_PRO CC.of_nat
  (CC.of_SymmetricG CC.of_nat)
  CC.of_pos
  '((Pgen 1 2 xH ;; Pswap 1 1 ;; Pgen 1 2 10%positive * Pgen 1 0 5%positive)%pro : PROP positive _ _). *)

(* Goal True.

eassert (PRO_quote (interp_discrete_hg_inhab _) _
  ((Pgen 1 2 xH ;; Pgen 1 2 10%positive * Pgen 1 0 5%positive)%pro : PROP positive _ _)).
mk_PRO_quote_interp_discrete_hg_inhab (). *)

(* constr_get_nth *)

(* Ltac2 Eval CC.of_PRO_safe (Int.add) CC.of_nat (fun s => s) CC.of_pos
  '((Pgen 1 2 xH ;; Pgen 1 2 10%positive * Pgen 1 0 5%positive)%pro : PROP positive _ _). *)

  