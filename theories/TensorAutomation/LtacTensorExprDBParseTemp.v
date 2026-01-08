Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

Require Import Aux_stdpp.
Require Import TensorExprDBSyntax.

Require Import Ltac2.Init.
Require Import LtacTensorExpr.
Require Import FSetExtra.
Require UTest.

Require Import ConstrExtra.


Ltac2 Type SRData := {
  ringType : constr;
  ringO : constr;
  ringI : constr;
  ringadd : constr;
  ringmul : constr;
  ringeq : constr;
  ringSR : constr;
}.

Ltac2 mk_SRData :=
  fun rT rO rI radd rmul req rSR =>
  {
  ringType := rT;
  ringO := rO;
  ringI := rI;
  ringadd := radd;
  ringmul := rmul;
  ringeq := req;
  ringSR := rSR;
}.

(* Get the SRData for a given type [rT] *)
Ltac2 get_SRData (rT : constr) :=
  let rO := (mk_evar rT) in 
  let rI := (mk_evar rT) in 
  let radd := (mk_evar '($rT -> $rT -> $rT)) in 
  let rmul := (mk_evar '($rT -> $rT -> $rT)) in 
  let req := (mk_evar '($rT -> $rT -> Prop)) in
  let rSR := (mk_evar '(SemiRing $rT $rO $rI $radd $rmul $req)) in
  Std.resolve_tc rSR;
  mk_SRData rT rO rI radd rmul req rSR.

Ltac2 get_summable (tA : constr) :=
  let sA := mk_evar '(Summable $tA) in 
  Std.resolve_tc sA;
  sA.

(*  
Section test.

Context `{SR : SemiRing R rO rI radd rmul req}.

Import Std.
Goal true.
(* Ltac2 Eval Std.unify '(1 : nat) '(2 : nat). *)
Ltac2 Eval Control.case (fun () => Std.unify '(1 : nat) '(2 : nat)).  false) 
  (fun _ => false).

Ltac2 Eval Control.plus (fun () => Std.eval_red (* Std.eval_cbn 
  {
    Std.rStrength := Std.Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := true;
    Std.rConst := [];
  } *)
((get_SRData 'R).(ringSR))) (fun _ => 'nat). *)


Import Ltac2.Notations.


Ltac2 Notation "!if" conds(list1(thunk(tactic(0)), "and")) "then" 
  t(thunk(tactic(5))) "else" f(thunk(tactic(5))) : 5 :=
  let rec get_val vs :=
    match vs with 
    | [] => false
    | [v] => v()
    | v :: vs => 
      if v() then true else get_val vs
    end in 
  if get_val conds then t() else f().

(* Ltac2 Notation "!and" l(thunk(tactic(2))) r(thunk(tactic(2))) : 5 :=
  if l() then r() else false.

Ltac2 Notation "!or" l(thunk(tactic(2))) r(thunk(tactic(2))) : 5 :=
  if l() then true else (r()). *)

(* Ltac2 Notation "pattern:" p(pattern) := p. *)
(* 
Ltac2 Notation "try" t(thunk(tactic(0))) 
  "catch" 
  list1(e(tactic(0)) "default" def(tactic(0)) : 5 :=
  Control.plus t (fun err => 
    match err with 
    | e => def
    | _ => Control.zero err
    end). *)

(* Ltac2 Eval 
  try (Some (Pattern.matches (pattern:(?f ?x ?y)) '(1)) )
    catch Match_failure default None. *)


Ltac2 char_list_of_string (s : string) : char list :=
  List.map (String.get s) (List.seq 0 1 (String.length s)).

Ltac2 int_of_string (s : string) : int :=
  List.fold_right (fun c acc => Int.add (Int.sub (Char.to_int c) 48) 
    (Int.mul 10 acc))
    (List.rev (char_list_of_string s)) 0.

Ltac2 constr_of_constr_list_typed (type : constr) (l : constr list) : constr :=
  let rec go l :=
  match l with 
  | [] => '(@nil $type)
  | x :: l' => 
    let res := go l' in 
    '(@cons $type $x $res)
  end in 
  go l.

Ltac2 constr_of_constr_list (l : constr list) : constr :=
  let rec go l :=
  match l with 
  | [] => 'nil
  | x :: l' => 
    let res := go l' in 
    '(cons $x $res)
  end in 
  go l.

Ltac2 constr_of_constr_pair_typed 
  (ts : constr * constr) : constr * constr -> constr :=
  fun (a, b) => 
  let (tA, tB) := ts in 
  '(@pair $tA $tB $a $b).

Ltac2 constr_of_constr_map (of_k : 'k -> constr) (of_v : 'v -> constr)
  (tk : constr) (tv : constr) (tm : constr) (m : ('k, 'v) FMap.t) : constr :=
  let mappings :=
    constr_of_constr_list_typed '(prod $tk $tv)
      (List.map (fun (k, v) => 
        let ck := of_k k with cv := of_v v in 
        '(@pair $tk $tv $ck $cv)) (FMap.bindings m)) in 
  let res := '(@list_to_map $tk $tv $tm _ _ $mappings) in 
  Std.resolve_tc res;
  res.

Ltac2 constr_of_string (s : string) : constr :=
  StringCustomNotation.string_name.IdentToString.string_to_coq_string s.

Ltac2 rec constr_of_pos (i : int) : constr :=
  match Int.compare i 1 with 
  | 1 => let res := constr_of_pos (Int.asr i 1) in 
    match Int.land i 1 with
    | 1 => '(xI $res)
    | _ => '(xO $res)
    end
  | 0 => 'xH
  | _ =>
    Control.throw_invalid_argument "constr_of_pos: nonpositive argument"
  end.


Ltac2 rec fold_left' (f : 'a -> 'a -> 'a) (d : 'a) (l : 'a list) : 'a :=
  let rec go l acc :=
  match l with 
  | [] => acc
  | x :: l => go l (f acc x)
  end in 
  match l with 
  | [] => d
  | x :: l => go l x
  end.

Ltac2 rec constr_nat_of_int (i : int) : constr :=
  if Int.le i 0 then 
    'O
  else 
    let n' := constr_nat_of_int (Int.sub i 1) in 
    '(S $n').

Ltac2 rec constr_of_tensorexpr (te : TensorExpr) : constr :=
  match te with 
  | Abstract name lower upper => 
    let cname := constr_of_string name in
    let clower := constr_of_constr_list_typed 'string
      (List.map (fun (_, s) => constr_of_string s) lower) in 
    let cupper := constr_of_constr_list_typed 'string
      (List.map (fun (_, s) => constr_of_string s) upper) in 
    '(tabstract $cname $clower $cupper)
  | Product tes => 
    fold_left' (fun l r => '(tproduct $l $r)) 'tone
      (List.map constr_of_tensorexpr tes)
  | Sum (ty, var) smd => 
    let cty := constr_nat_of_int (int_of_string ty) in 
    let cvar := constr_of_string var in 
    let csmd := constr_of_tensorexpr smd in 
    '(tsum $cvar $cty $csmd)
  end.


Ltac2 rec constr_of_tensorexpr' (te : TensorExpr) : constr :=
  match te with 
  | Abstract name lower upper => 
    let cname := constr_of_string name in
    let clower := constr_of_constr_list_typed 'string
      (List.map (fun (_, s) => constr_of_string s) lower) in 
    let cupper := constr_of_constr_list_typed 'string
      (List.map (fun (_, s) => constr_of_string s) upper) in 
    Constr.Unsafe.make (Constr.Unsafe.App '(tabstract) [|cname; clower; cupper|])
  | Product tes => 
    fold_left' (fun l r => 
      Constr.Unsafe.make (Constr.Unsafe.App '(tproduct) [|l; r|])) 'tone
      (List.map constr_of_tensorexpr' tes)
  | Sum (ty, var) smd => 
    let cty := constr_nat_of_int (int_of_string ty) in 
    let cvar := constr_of_string var in 
    let csmd := constr_of_tensorexpr' smd in 
    Constr.Unsafe.make (Constr.Unsafe.App '(tsum) [|cvar; cty; csmd|])
  end.

(* 
Ltac2 test_lhs () : TensorExpr :=
  Product
  [Sum ("1", "y")
 (Sum ("0", "x")
   (Product
	 [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
      "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
 [Sum ("1", "y")
  (Sum ("0", "x")
    (Product
      [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
       "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
  [Sum ("1", "y")
   (Sum ("0", "x")
     (Product
       [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
        "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
   [Sum ("1", "y")
    (Sum ("0", "x")
      (Product
        [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
         "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
    [Sum ("1", "y")
     (Sum ("0", "x")
       (Product
         [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
          "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
     [Sum ("1", "y")
      (Sum ("0", "x")
        (Product
          [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
           "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
      [Sum ("1", "y")
       (Sum ("0", "x")
         (Product
           [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
            "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
       [Sum ("1", "y")
        (Sum ("0", "x")
          (Product
            [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
             "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
        [Sum ("1", "y")
         (Sum ("0", "x")
           (Product
             [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
              "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
         [Sum ("1", "y")
          (Sum ("0", "x")
            (Product
              [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
               "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
          [Sum ("1", "y")
           (Sum ("0", "x")
             (Product
               [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
           [Sum ("1", "y")
            (Sum ("0", "x")
              (Product
                [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                 "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
            [Sum ("1", "y")
             (Sum ("0", "x")
               (Product
                 [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                  "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
             [Sum ("1", "y")
              (Sum ("0", "x")
                (Product
                  [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                   "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
              [Sum ("1", "y")
               (Sum ("0", "x")
                 (Product
                   [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                    "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
               [Sum ("1", "y")
                (Sum ("0", "x")
                  (Product
                    [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                     "f" [("0", "x"); ("1", "y")] 
                     [("0", "f")]])); Product
                [Sum ("1", "y")
                 (Sum ("0", "x")
                   (Product
                     [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
                      "f" [("0", "x"); ("1", "y")] 
                      [("0", "f")]])); Product
                 [Sum ("1", "y")
                  (Sum ("0", "x")
                    (Product
                      [Abstract "f0" [("0", "f")] 
                       [("1", "y")]; Abstract "f" 
                       [("0", "x"); ("1", "y")] [("0", "f")]])); Product
                  [Sum ("1", "y")
                   (Sum ("0", "x")
                     (Product
                       [Abstract "f0" [("0", "f")] 
                        [("1", "y")]; Abstract "f" 
                        [("0", "x"); ("1", "y")] [("0", "f")]])); Product
                   [Sum ("1", "y")
                    (Sum ("0", "x")
                      (Product
                        [Abstract "f0" [("0", "f")] 
                         [("1", "y")]; Abstract "f" 
                         [("0", "x"); ("1", "y")] 
                         [("0", "f")]])); Sum ("1", "y")
                    (Sum ("0", "x")
                      (Product
                        [Abstract "f0" [("0", "f")] 
                         [("1", "y")]; Abstract "f" 
                         [("0", "x"); ("1", "y")] 
                         [("0", "f")]]))]]]]]]]]]]]]]]]]]]]].

Ltac2 test_rhs () : TensorExpr := Product
  [Sum ("1", "y")
 (Sum ("0", "x")
   (Product
	 [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
      "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
 [Sum ("1", "y")
  (Sum ("0", "x")
    (Product
      [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
       "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
  [Sum ("1", "y")
   (Sum ("0", "x")
     (Product
       [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
        "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
   [Sum ("1", "y")
    (Sum ("0", "x")
      (Product
        [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
         "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
    [Sum ("1", "y")
     (Sum ("0", "x")
       (Product
         [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
          "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Product
     [Sum ("1", "y")
      (Sum ("0", "x")
        (Product
          [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
           "f" [("0", "x"); ("1", "y")] [("0", "f")]])); Sum 
      ("1", "y")
      (Sum ("0", "x")
        (Product
          [Abstract "f0" [("0", "f")] [("1", "y")]; Abstract 
           "f" [("0", "x"); ("1", "y")] [("0", "f")]]))]]]]]].

Time Ltac2 Eval 
  let _ := constr_of_tensorexpr (test_lhs()) in ().
Time Ltac2 Eval 
  let _ := constr_of_tensorexpr' (test_lhs()) in (). *)

Ltac2 mutable check_summable := false.

Ltac2 Type Var := [
  | Rel (int)
  | Loc (int)
  | Glob (int)
].

Ltac2 Type AbsIdx := int.
Ltac2 abs_tag : AbsIdx FSet.Tags.tag := FSet.Tags.int_tag.
Ltac2 Type VarIdx := int.
Ltac2 var_tag : VarIdx FSet.Tags.tag := FSet.Tags.int_tag.
Ltac2 Type AbsData := AbsIdx * Var list * Var list.

Ltac2 Type TEContext := {
  ctx_SR : SRData;
  ctx_vs : (constr * constr) list;
  ctx_abs : (AbsIdx, constr * int list * int list) FMap.t;
  ctx_mg : (VarIdx, int * constr) FMap.t;
  ctx_ml : int list; (* The types of the local variables 
    [Rel (length ctx_mr + i)], given by indices in ctx_vs *)
  ctx_mr : int list (* The types of the relative variables, given by 
    indices in ctx_vs *)
}.

Ltac2 mk_TEContext (ctx_SR : SRData)
  (ctx_vs : (constr * constr) list)
  (ctx_abs : (AbsIdx, constr * int list * int list) FMap.t)
  (ctx_mg : (VarIdx, int * constr) FMap.t) ctx_ml ctx_mr : TEContext := {
  ctx_SR := ctx_SR;
  ctx_vs := ctx_vs;
  ctx_abs := ctx_abs;
  ctx_mg := ctx_mg;
  ctx_ml := ctx_ml;
  ctx_mr := ctx_mr;
}.

Ltac2 empty_TEContext (cR : constr) : TEContext :=
  mk_TEContext (get_SRData cR) 
    [] (FMap.empty abs_tag) (FMap.empty var_tag)
    [] [].

Ltac2 fresh_idx (used : int FSet.t) : int :=
  let rec go n :=
    if FSet.mem n used then 
      go (Int.add 1 n)
    else n
    in
  go 1.


Ltac2 fresh_idx_of_list (used : int list) : int :=
  fresh_idx (FSet.of_list FSet.Tags.int_tag used).


Ltac2 fresh_idx_of_map (used : (int, 'a) FMap.t) : int :=
  fresh_idx (FMap.domain used).

Ltac2 fresh_string (used : string FSet.t) (base : string) : string :=
  (* let base := Option.default "" base in  *)
  let rec go n := 
    let s := String.app base (string_of_int n) in 
    if FSet.mem s used then 
      go (Int.add n 1)
    else
      s
  in
  go 0.

Ltac2 fresh_string_of_list (s : string list) (base : string) : string :=
  fresh_string (FSet.of_list string_tag s) base.

Ltac2 fresh_string_of_map (m : (string, 'a) FMap.t) (base : string) : string :=
  fresh_string (FMap.domain m) base.

(* Find a type in the [vs] map, adding it if necessary *)
Ltac2 lookup_vs (vs : (constr * constr) list) (tA : constr) (sA : constr) : 
  (constr * constr) list * int :=
  let rec go i vs' :=
  match vs' with 
  | [] => (List.append vs [(tA, sA)], i)
  | (tB, sB) :: vs'' => 
    !if (unify_eq tA tB) and check_summable and (unify_eq sA sB) then
      (vs, i)
    else 
      go (Int.add i 1) vs''
  end in 
  go 0 vs.

(* Find a type in the [vs] map, adding it if necessary *)
Ltac2 lookup_vs_no_sum (vs : (constr * constr) list) (tA : constr) : 
  (constr * constr) list * int :=
  let rec go i vs' :=
  match vs' with 
  | [] => 
    let sA := get_summable tA in 
    (List.append vs [(tA, sA)], i)
  | (tB, _sB) :: vs'' => 
    if (unify_eq tA tB) then
      (vs, i)
    else 
      go (Int.add i 1) vs''
  end in 
  go 0 vs.

Ltac2 ctx_lookup_type (ctx : TEContext) (tA : constr) (sA : constr) : 
  TEContext * int :=
  let (vs, ty) := lookup_vs (ctx.(ctx_vs)) tA sA in 
  ({ctx with ctx_vs := vs}, ty).

Ltac2 ctx_lookup_type_no_sum (ctx : TEContext) (tA : constr) : 
  TEContext * int :=
  let (vs, ty) := lookup_vs_no_sum (ctx.(ctx_vs)) tA in 
  ({ctx with ctx_vs := vs}, ty).

(* FIXME: Move *)
Ltac2 pair_equal (eqa : 'a -> 'a -> bool) (eqb : 'b -> 'b -> bool) : 
  'a * 'b -> 'a * 'b -> bool :=
  fun (a, b) (a', b') => if eqa a a' then eqb b b' else false.

Ltac2 parse_var (vs : (constr * constr) list) 
  (mg : (VarIdx, int * constr) FMap.t)
  (numrel : int) (* The number of binding local summands *)
  (val : constr) (type : constr) : 
  (constr * constr) list * (VarIdx, int * constr) FMap.t * (int * Var) :=
  let (vs, ty) := lookup_vs_no_sum vs type in 
  match Unsafe.is_Rel_data val with 
  | Some i => 
    if Int.le i numrel then (* le because everything is 1-indexed *)
      (vs, mg, (ty, Rel i))
    else (* Local variable *)
      (vs, mg, (ty, Loc (Int.sub i numrel)))
  | None =>
    (* TODO: Replace unify_eq with Unification.conv_full, in Rocq 9.0 *)
    match FMap.find_inv_opt (pair_equal Int.equal unify_eq) (ty, val) mg with 
    | Some idx => (vs, mg, (ty, Glob idx))
    | None => let name := fresh_idx_of_map mg in 
      (vs, FMap.add name (ty, val) mg, (ty, Glob name))
    end
  end.

Ltac2 parse_abs_val 
  (abs : (AbsIdx, constr * int list * int list) FMap.t)
  (f : constr) (low : int list) (up : int list) : 
  (AbsIdx, constr * int list * int list) FMap.t * AbsIdx :=
  let get_eq (f, low, up) (f', low', up') :=
    !if (unify_eq f f') and (List.equal Int.equal low low') and 
      (List.equal Int.equal up up') then true else false in 
  match FMap.find_inv_opt get_eq (f, low, up) abs with 
  | Some idx => (abs, idx)
  | None => let name := fresh_idx_of_map abs in 
    (FMap.add name (f, low, up) abs, name)
  end.

Ltac2 parse_abs_data (vs : (constr * constr) list) 
  (abs : (AbsIdx, constr * int list * int list) FMap.t) 
  (mg : (VarIdx, int * constr) FMap.t) (numrel : int)
  (head : constr) (lower : (constr * constr) list)
  (upper : (constr * constr) list) :
  (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
  (VarIdx, int * constr) FMap.t *
  AbsData :=
  let (vs, mg, lower_tyvars) :=
    List.fold_right (fun (val, type) (vs, vars, tyvars) => 
      let (vs, vars, tyvar) := parse_var vs vars numrel val type in 
      (vs, vars, tyvar :: tyvars)) lower (vs, mg, []) in 
  let (vs, mg, upper_tyvars) :=
    List.fold_right (fun (val, type) (vs, vars, tyvars) => 
      let (vs, vars, tyvar) := parse_var vs vars numrel val type in 
      (vs, vars, tyvar :: tyvars)) upper (vs, mg, []) in 
  let (abs, abs_idx) := parse_abs_val abs head 
    (List.map fst lower_tyvars) (List.map fst upper_tyvars) in 
  (vs, abs, mg, (abs_idx, List.map snd lower_tyvars, List.map snd upper_tyvars)).


Ltac2 ctx_parse_var ctx val type :=
  let (vs, vars, tyvar) := 
    parse_var (ctx.(ctx_vs)) (ctx.(ctx_mg)) (List.length (ctx.(ctx_mr))) val type in  
  ({ctx with ctx_vs := vs; ctx_mg := vars}, tyvar).

Ltac2 ctx_parse_abs_val ctx f low up :=
  let (abs, idx) := parse_abs_val (ctx.(ctx_abs)) f low up in  
  ({ctx with ctx_abs := abs}, idx).

Ltac2 ctx_parse_abs_data ctx head lower upper :=
  let (vs, abs, mg, absdata) :=
    parse_abs_data (ctx.(ctx_vs)) (ctx.(ctx_abs)) (ctx.(ctx_mg))
      (List.length (ctx.(ctx_mr)))
      head lower upper in 
  ({ctx with ctx_vs := vs; ctx_mg := mg; ctx_abs := abs}, 
    absdata).


Import PrintingExtra Pp.

Ltac2 helper_make_typing_map (vs : (constr * constr) list)
  (ml : int list) (mr : int list) : (int, constr) FMap.t :=
  FMap.of_list FSet.Tags.int_tag (
    List.mapi (fun i ty => (Int.add 1 i, fst (List.nth vs ty)))
    (List.rev (List.append ml mr))).


Ltac2 Type rec TensorExprDB := [
  TOne
| Abstract (AbsIdx, Var list, Var list) 
    (* An abstract tensor, along with the registers to which it is 
      applied as inputs and as outputs, respectively.
      Each index is stored along with its type. *)
| Product (TensorExprDB, TensorExprDB)
    (* The product of a list of tensor expressions, 
      conventionally left-associated *)
| Sum (int, TensorExprDB) 
    (* The sum/contraction of a tensor expression with respect to a
      given variable *)
].

Ltac2 rec parse_tensor_expr_aux_data
  (r : SRData)
  (to_abs : constr -> (* the constr to decompose. Note it will likely be unsafe 
    by containing [Rel _] terms. All these will be mapped in [relmap], however *)
    (int, constr) FMap.t -> (* The typing map for [Rel _] derived from 
      [relmap] and [vs] (i.e. [Rel i] has type [T = nth vs j] where [relmap !! i = (j, _)]) *)
    (constr * (* head symbol *)
      (constr * constr) list * (* lower arguments and their types *)
      (constr * constr) list (* upper arguments and their types *)) option) 
  (vs : (constr * constr) list) 
  (abs : (AbsIdx, constr * int list * int list) FMap.t) 
  (mg : (VarIdx, int * constr) FMap.t) (ml : int list) (mr : int list)
  (c : constr) : 
  (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
    (VarIdx, int * constr) FMap.t * int list * int list * TensorExprDB :=
  let rec go vs abs mg ml mr c : 
    (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
      (VarIdx, int * constr) FMap.t * int list * int list * TensorExprDB :=
  (* let rT := r.(ringType) in  *)
  (* print (str "go" ++ spc() ++ of_list (of_pair of_constr of_constr) vs ++
    spc() ++ print_map of_string of_constr abs ++ 
    spc() ++ print_map of_string of_constr vars ++
    spc() ++ of_list (of_pair of_int of_string) rels ++
    spc() ++ of_constr c);
  print (mt()); *)
  if unify_eq c (r.(ringI)) then (vs, abs, mg, ml, mr, TOne) else
  match! c with 
  | @sum_of _  _ _  _ _  _  _  ?tA ?sA ?f =>
      let (vs', idx_A) := lookup_vs vs tA sA in 
      let (_b, fbody) := Unsafe.decompose_lambda f in 
      let mr := idx_A :: mr in
      let (vs, abs, mg, ml, mr, body_te) :=
        go vs' abs mg ml mr
          fbody in
      (vs, abs, mg, ml, List.tl mr, Sum idx_A body_te)
      (* Product [] *)
      (* let rels := () *)
  | ?mul ?a ?b => 
    Std.unify mul (r.(ringmul));
    (* print (str "vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
    let (vs, abs, mg, ml, mr, tea) := 
      go vs abs mg ml mr a in 
    (* print (str "vs': " ++ of_list (of_pair of_constr of_constr) vs'); *)
    let (vs, abs, mg, ml, mr, teb) :=
      go vs abs mg ml mr b in
    (* print (str "vs'': " ++ of_list (of_pair of_constr of_constr) vs''); *)
    (vs, abs, mg, ml, mr, Product tea teb)
  (* | _ => None *)
  | _ => 
    (* print (str "rel_typing_map for " ++ of_constr c ++ str " from: " ++ 
      of_list (of_pair of_int of_string) rels ++ spc() ++
      str "vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
    let rel_typing_map := helper_make_typing_map vs ml mr in 
    match to_abs c rel_typing_map with 
    | None => Control.throw (Invalid_argument (Some (
      Message.concat (Message.of_string "Could not parse constr as TensorExpr: ")
        (Message.of_constr c)))) 
    | Some (head, lower, upper) => 
    (* print (str "_vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
      let (vs, abs, mg, (idx, l, u)) := 
        parse_abs_data vs abs mg (List.length mr) head lower upper in 
    (* print (str "_vs': " ++ of_list (of_pair of_constr of_constr) vs'); *)
      (vs, abs, mg, ml, mr, Abstract idx l u)
    end
  end in 
  go vs abs mg ml mr c. 



(** The function which parses abstract values (until extended, always fails!). 
  To extend this to other functions, do something like the following:
  Ltac2 Set parse_abstract as parse_abstract_old := fun c relmap => 
    lazy_match! c with
    | f ?x ?y ?z => Some ('f, [(x, 'A); (y, 'B)], [(z, 'A)])
    | _ => parse_abstract_old c relmap
    end. *)
Ltac2 mutable parse_abstract : constr -> (* the constr to decompose. Note it will likely be unsafe 
    by containing [Rel _] terms. All these will be mapped in [relmap], however *)
    (int, constr) FMap.t -> (* The typing map for [Rel _] derived from 
      [relmap] and [vs] (i.e. [Rel i] has type [T = nth vs j] where [relmap !! i = (j, _)]) *)
    (constr * (* head symbol *)
      (constr * constr) list * (* lower arguments and their types *)
      (constr * constr) list (* upper arguments and their types *)) option :=
  fun _c _relmap =>
  None.

Ltac2 parse_tensor_expr_aux 
  (ctx : TEContext) (c : constr) : 
  TEContext * TensorExprDB :=
  let (vs, abs, mg, ml, mr, te) := 
    parse_tensor_expr_aux_data (ctx.(ctx_SR)) parse_abstract 
      (ctx.(ctx_vs)) (ctx.(ctx_abs)) 
      (ctx.(ctx_mg)) (ctx.(ctx_ml)) (ctx.(ctx_mr)) c in 
  ({ctx with ctx_vs := vs; ctx_abs := abs; ctx_mg := mg; 
    ctx_ml := ml; ctx_mr := mr}, te).


Ltac2 parse_tensor_equality_aux ctx c : 
  TEContext * TensorExprDB * TensorExprDB :=
  let rec go ctx c : 
    TEContext * TensorExprDB * TensorExprDB :=
  (* let rT := r.(ringType) in  *)
  (* print (str "go" ++ spc() ++ of_list (of_pair of_constr of_constr) vs ++
    spc() ++ print_map of_string of_constr abs ++ 
    spc() ++ print_map of_string of_constr vars ++
    spc() ++ of_list (of_pair of_int of_string) rels ++
    spc() ++ of_constr c);
  print (mt()); *)
  match! c with 
  | ?req ?lhs ?rhs => 
    Std.unify req (ctx.(ctx_SR).(ringeq));
    let (ctx, telhs) := parse_tensor_expr_aux ctx lhs in 
    let (ctx, terhs) := parse_tensor_expr_aux ctx rhs in 
    (ctx, telhs, terhs)
  | _ => 
    let (b, cbody) := Unsafe.decompose_prod c in 
    let tA := Constr.Binder.type b in 
    let (ctx, idx_A) := ctx_lookup_type_no_sum ctx tA in 
    let ml := idx_A :: ctx.(ctx_ml) in
    go ({ctx with ctx_ml := ml}) cbody
  end in 
  go ctx c.


(* TODO: Helper function for parsing vector terms into split lists
Ltac2  *)






Require Import TensorExprDBSemantics.

Definition unit_Summable@{u} : Summable (unit : Type@{u}) :=
  (@sum_over (unit : Type@{u}) [ () ]).

Notation SummableType := ({A : Type & Summable A}).

Definition Summable_Type_inhabited : 
  Inhabited SummableType :=
  populate (existT (unit : Type) unit_Summable).

Ltac2 get_cV (vs : (constr * constr) list) : constr :=
  let cVs := constr_of_constr_list_typed 'SummableType
    (List.map (fun (tA, sA) => '(@existT _ Summable $tA $sA)) vs) in 
  '(fun (i : Ty) => 
    projT1 (@lookup_total Ty SummableType (list SummableType)
    (@list_lookup_total _ Summable_Type_inhabited) i $cVs)).


Ltac2 get_cVsum (vs : (constr * constr) list) : constr :=
  let cVs := constr_of_constr_list_typed 'SummableType
    (List.map (fun (tA, sA) => '(@existT _ Summable $tA $sA)) vs) in 
  '(fun (i : Ty) => 
    projT2 (@lookup_total Ty SummableType (list SummableType)
    (@list_lookup_total _ Summable_Type_inhabited) i $cVs)).


Ltac2 constr_of_typed_fun (cR : constr) (cV : constr (* : Ty -> Type *)) : 
  constr * int list * int list -> constr :=
  fun (f, low, up) => 
  let args := constr_of_constr_list_typed 'nat
    (List.map constr_nat_of_int (List.append low up)) in 
  '(@mk_Vfunc $cR $cV $args $f).

Ltac2 constr_of_typed_var (cV : constr) : 
  int * constr -> constr :=
  fun (ty, val) => 
  let cty := constr_nat_of_int ty in 
  '(@mk_Vval $cV $cty $val).

(* Ltac2 Eval constr_of_constr_map 
  StringCustomNotation.string_name.IdentToString.string_to_coq_string
  (fun x => x)
  'string 'nat '(gmap string N)
  (FMap.of_list string_tag [("a", '1); ("b", '1)]). *)

Ltac2 constr_of_var (v : Var) : constr :=
  match v with 
  | Rel r => let i := constr_of_pos r in 
    '(rel $i)
  | Loc l => let i := constr_of_pos l in 
    '(loc $i)
  | Glob g => let i := constr_of_pos g in 
    '(glob $i)
  end.

Ltac2 rec constr_of_tensorexprdb (te : TensorExprDB) : constr :=
  match te with
  | TOne => 'tone
  | Abstract f low up =>
    let cf := constr_of_pos f with
     clow := constr_of_constr_list_typed 'var (List.map constr_of_var low) with
     cup := constr_of_constr_list_typed 'var (List.map constr_of_var up) in 
    '(tabstract $cf $clow $cup)
  | Product l r => 
    let cl := constr_of_tensorexprdb l in 
    let cr := constr_of_tensorexprdb r in 
    '(tproduct $cl $cr)
  | Sum ty body =>
    let cty := constr_nat_of_int ty in 
    let cbody := constr_of_tensorexprdb body in 
    '(tsum $cty $cbody)
  end.

Ltac2 ctx_get_cV (ctx : TEContext) : constr :=
  get_cV (ctx.(ctx_vs)).

Ltac2 ctx_get_cVsum (ctx : TEContext) : constr :=
  get_cVsum (ctx.(ctx_vs)).

Ltac2 ctx_get_cR (ctx : TEContext) : constr :=
  ctx.(ctx_SR).(ringType).

Ltac2 ctx_get_cabs (ctx : TEContext) : constr :=
  let cV := ctx_get_cV ctx in 
  let cR := ctx_get_cR ctx in 
  constr_of_constr_map constr_of_pos 
    (constr_of_typed_fun cR cV) 
    'positive '(@Vfunc $cR $cV) '(Pmap (@Vfunc $cR $cV)) (ctx.(ctx_abs)).

Ltac2 ctx_get_cmg (ctx : TEContext) : constr :=
  let cV := ctx_get_cV ctx in 
  constr_of_constr_map constr_of_pos (constr_of_typed_var cV)
    'positive '(Vval $cV) '(Pmap (Vval $cV)) (ctx.(ctx_mg)).

Ltac2 ctx_get_ml_list (ctx : TEContext) : (int * int) list :=
  (List.mapi (fun idx ty => (Int.add 1 idx, ty)) (List.rev (ctx.(ctx_ml)))).

Ltac2 ctx_get_ml_map (ctx : TEContext) : (int, int) FMap.t :=
  FMap.of_list FSet.Tags.int_tag 
    (ctx_get_ml_list ctx).

Ltac2 ctx_get_cml (ctx : TEContext) : constr :=
  constr_of_constr_map constr_of_pos constr_of_pos
    'positive 'positive '(Pmap positive) (ctx_get_ml_map ctx).

Ltac2 constr_of_pair_typed (ts : constr * constr) 
  (cA : 'a -> constr) (cB : 'b -> constr) : 'a * 'b -> constr :=
  fun (a, b) => constr_of_constr_pair_typed ts (cA a, cB b).

Ltac2 ctx_get_cml_list (ctx : TEContext) : constr (*list (Idx * Ty) *):=
  constr_of_constr_list_typed '(prod Idx Ty) 
    (List.rev_map (constr_of_pair_typed ('Idx, 'Ty) constr_of_pos constr_nat_of_int)
      (ctx_get_ml_list ctx)). 



Ltac2 constr_semantics_of_tensorexpr_aux (ctx : TEContext) (cte : constr) :=
  let cSR := ctx.(ctx_SR).(ringSR) in 
  let cV := ctx_get_cV ctx in 
  let cVsum := ctx_get_cVsum ctx in 
  let cabs := ctx_get_cabs ctx in 
  let cmg := ctx_get_cmg ctx in 
  (* let cml := ctx_get_cml ctx in  *)
  '(@total_semantics_aux _ _ _ _ _ _ $cSR $cV $cVsum $cabs $cmg ∅ [] $cte).

Ltac2 constr_semantics_of_tensorexpr (ctx : TEContext) (te : TensorExprDB) :=
  constr_semantics_of_tensorexpr_aux ctx (constr_of_tensorexprdb te).


Ltac2 constr_semantics_of_tensor_equality (ctx : TEContext) 
  (lhs : TensorExprDB) (rhs : TensorExprDB) :=
  let cSR := ctx.(ctx_SR).(ringSR) in 
  let cV := ctx_get_cV ctx in 
  let cVsum := ctx_get_cVsum ctx in 
  let cabs := ctx_get_cabs ctx in 
  let cmg := ctx_get_cmg ctx in 
  let cml := ctx_get_cml_list ctx in 
  let clhs := constr_of_tensorexprdb lhs in 
  let crhs := constr_of_tensorexprdb rhs in 
  (* let cml := ctx_get_cml ctx in  *)
  '(@tensorequation_semantics_aux _ _ _ _ _ _ $cSR $cV $cVsum $cabs $cmg [] 
    $clhs $crhs $cml (@empty _ Pmap_empty)).


Ltac2 test_parse_tensor_equality (cR : constr) (tH : constr) : unit :=
  let ctx := empty_TEContext cR in 
  let (eqctx, lhs, rhs) := parse_tensor_equality_aux ctx tH in 
  let sem := constr_semantics_of_tensor_equality eqctx lhs rhs in 
  assert ($tH = $sem).
  
Ltac2 test_parse_tensorexpr (c : constr) : unit :=
  let cR := Constr.type c in 
  let ctx := empty_TEContext cR in 
  let (ctx, te) := parse_tensor_expr_aux ctx c in 
  let sem := constr_semantics_of_tensorexpr ctx te in
  assert ($c = $sem).


Ltac2 pos_of_constr (p : constr) : int :=
  let rec go p :=
  match! p with 
  | xH => 1
  | xI ?p => Int.add 1 (Int.lsl (go p) 1)
  | xO ?p => Int.lsl (go p) 1
  | _ =>
    let p' := Std.eval_red p in 
    if Constr.equal p' p then 
      let p' := Std.eval_vm None p in 
      if Constr.equal p' p then 
        Control.throw_invalid_argument 
          "pos_of_constr: argument is not reducible to a [positive] constant"
      else go p'
    else go p'
  end in 
  go p.

(* TODO: Support big numbers (Nat.of_num_uint, etc.)*)
Ltac2 nat_of_constr (n : constr) : int :=
  let rec go p :=
  match! p with 
  | O => 0
  | S ?n => Int.add 1 (go n)
  | _ =>
    let n' := Std.eval_red n in 
    if Constr.equal n' n then 
      let n' := Std.eval_vm None n in 
      if Constr.equal n' n then 
      Control.throw_invalid_argument 
        "nat_of_constr: argument is not reducible to a [nat] constant"
      else go n'
    else go n'
  end in 
  go n.


Ltac2 list_of_constr (f : constr -> 'a) : constr -> 'a list :=
  let rec go l :=
  match! l with 
  | nil => []
  | ?x :: ?l => f x :: go l
  | _ =>
    let l' := Std.eval_red l in 
    if Constr.equal l' l then 
      Control.throw_invalid_argument 
        "nat_of_constr: argument is not reducible to a [nat] constant"
    else go l'
  end in 
  go.

Ltac2 var_of_constr (v : constr) : Var :=
  let rec go v :=
  match! v with 
  | rel ?r => Rel (pos_of_constr r)
  | loc ?l => Loc (pos_of_constr l)
  | glob ?g => Glob (pos_of_constr g)
  | _ => 
    let v' := Std.eval_red v in 
    if Constr.equal v' v then 
      let v' := Std.eval_vm None v in 
      if Constr.equal v' v then 
      Control.throw_invalid_argument 
        "nat_of_constr: argument is not reducible to a [nat] constant"
      else go v'
    else go v'
  end in 
  go v.

Ltac2 tensorexprdb_of_constr (cte : constr) : TensorExprDB :=
  let rec go cte :=
  match! cte with
  | tone => TOne
  | tabstract ?f ?low ?up => 
    let vars_of_constr := list_of_constr var_of_constr in 
    Abstract (pos_of_constr f) (vars_of_constr low) (vars_of_constr up)
  | tproduct ?l ?r => 
    Product (go l) (go r)
  | tsum ?ty ?body => 
    Sum (nat_of_constr ty) (go body)
  end in 
  go cte.

(* Overwrite this to add simplification after rewriting *)
Ltac2 mutable red_te_semantics_post () : unit :=
  ().

Ltac2 red_te_semantics () : unit := 
  lazy [
  lookup_total list_lookup_total 
  insert map_insert 
  partial_alter Pmap_partial_alter 
    pmap.Pmap_partial_alter_aux pmap.Pmap_ne_partial_alter
    pmap.Pmap_ne_case pmap.PNode pmap.Pmap_ne_singleton
  empty Pmap_empty

  list_to_map fold_right

  projT1 fst snd

  tensorequation_semantics_aux
  total_semantics_aux 

  abstract_semantics 
  join_list from_option id
  app
  mbind option_bind
  fmap list_fmap option_fmap option_map

  get_var
  
  lookup Pmap_lookup Pmap_ne_lookup
  list_lookup pos_to_nat_pred 
  Nat.pred Pos.to_nat Pos.iter_op Nat.add
  
  Vapplys Vapply Vconst Vval_get
  mk_Vfunc mk_Vval

  decide decide_rel Nat.eq_dec PeanoNat.Nat.eq_dec
    nat_rec nat_rect f_equal_nat f_equal eq_rect_r eq_sym eq_rect
  ];
  red_te_semantics_post ().

Ltac2 te_rewrite_in_lhs (cR : constr) (tH : constr) : unit :=
  let goalctx := empty_TEContext cR in 
  let (goalctx, glhs, grhs) := parse_tensor_equality_aux goalctx (Control.goal()) in 
  let hypctx := {goalctx with ctx_ml := [] } in 
  let (hypctx, hlhs, hrhs) := parse_tensor_equality_aux hypctx tH in 
  let goalml := goalctx.(ctx_ml) in 
  let ctx := {hypctx with ctx_ml := goalml} in 

  let cglhs := constr_of_tensorexprdb glhs in 
  let chlhs := constr_of_tensorexprdb hlhs in 
  let chrhs := constr_of_tensorexprdb hrhs in 
  let rew_expr := '(match_rewrite_tensorlist (tensorlist_of_tensorexpr $chlhs) 
    (tensorlist_of_tensorexpr $chrhs) (tensorlist_of_tensorexpr $cglhs)) in 
  let new_lhs_expr := Std.eval_vm None rew_expr in 
  lazy_match! new_lhs_expr with 
  | None => Control.zero (Tactic_failure
    (Some (Message.of_string "te_rewrite_in_lhs: no rewrite found!")))
  | Some ?e => 
    let new_lhs_expr := '(tensorexpr_of_tensorlist $e) in 
    let new_lhs_expr := Std.eval_vm None new_lhs_expr in
    let new_lhs := tensorexprdb_of_constr new_lhs_expr in 
    let new_goal := constr_semantics_of_tensor_equality ctx new_lhs grhs in 
    enough ($new_goal) by Control.shelve();
    red_te_semantics()
  end.


Ltac2 te_rewrite_in_rhs (cR : constr) (tH : constr) : unit :=
  let goalctx := empty_TEContext cR in 
  let (goalctx, glhs, grhs) := parse_tensor_equality_aux goalctx (Control.goal()) in 
  let hypctx := {goalctx with ctx_ml := [] } in 
  let (hypctx, hlhs, hrhs) := parse_tensor_equality_aux hypctx tH in 
  let goalml := goalctx.(ctx_ml) in 
  let ctx := {hypctx with ctx_ml := goalml} in 

  let cgrhs := constr_of_tensorexprdb grhs in 
  let chlhs := constr_of_tensorexprdb hlhs in 
  let chrhs := constr_of_tensorexprdb hrhs in 
  let rew_expr := '(match_rewrite_tensorlist (tensorlist_of_tensorexpr $chlhs) 
    (tensorlist_of_tensorexpr $chrhs) (tensorlist_of_tensorexpr $cgrhs)) in 
  let new_rhs_expr := Std.eval_vm None rew_expr in 
  lazy_match! new_rhs_expr with 
  | None => Control.zero (Tactic_failure
    (Some (Message.of_string "te_rewrite_in_rhs: no rewrite found!")))
  | Some ?e => 
    let new_rhs_expr := '(tensorexpr_of_tensorlist $e) in 
    let new_rhs_expr := Std.eval_vm None new_rhs_expr in
    let new_rhs := tensorexprdb_of_constr new_rhs_expr in
    let new_goal := constr_semantics_of_tensor_equality ctx glhs new_rhs in 
    enough ($new_goal) by Control.shelve();
    red_te_semantics()
  end.

Ltac2 te_rewrite (cR : constr) (cH : constr) : unit :=
  let tH := Constr.type cH in 
  first [te_rewrite_in_lhs cR tH | te_rewrite_in_rhs cR tH].

(*
(* 
Ltac2 te_refl parse_abs' : unit :=
  lazy_match! goal with 
  | [|- ?_req ?lhs ?rhs] => 
    let rT := Constr.type lhs in 
    let sR := get_SRData rT in 
    let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux_data sR parse_abs'
      [] (FMap.empty string_tag) (FMap.empty string_tag) []
      lhs in 
    let (vs, abs, vars, _rels, ter) := 
      parse_tensor_expr_aux_data sR parse_abs'
      vs abs vars rels
      rhs in 

    let cV := get_cV vs in 
    let cVsum := get_cVsum vs in 
    let cabs := constr_of_constr_map constr_of_string
      (constr_of_typed_fun rT cV)
      'string '(@Vfunc $rT $cV) 
      '(gmap string (@Vfunc $rT $cV)) abs in

    let cvars := constr_of_constr_map constr_of_string
      (fun x => 
        let (_, tx) := lookup_vs_no_sum vs (Constr.type x) in 
        let ctx := constr_nat_of_int tx in 
        '(@mk_Vval $cV $ctx $x)) 'string '(Vval $cV)
        '(gmap string (Vval $cV)) vars in 
    
    let clhs := constr_of_tensorexpr tel in 
    let crhs := constr_of_tensorexpr ter in 
    let rSR := sR.(ringSR) in 
    apply (tensorexpr_eqb_correct_apply (SR:=$rSR)
      $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
    vm_compute;
    exact eq_refl
  end.

Ltac2 te_refl_no_check parse_abs' : unit :=
  lazy_match! goal with 
  | [|- ?_req ?lhs ?rhs] => 
    let rT := Constr.type lhs in 
    let sR := get_SRData rT in 
    let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux_data sR parse_abs'
      [] (FMap.empty string_tag) (FMap.empty string_tag) []
      lhs in 
    let (vs, abs, vars, _rels, ter) := 
      parse_tensor_expr_aux_data sR parse_abs'
      vs abs vars rels
      rhs in 

    let cV := get_cV vs in 
    let cVsum := get_cVsum vs in 
    let cabs := constr_of_constr_map constr_of_string
      (constr_of_typed_fun rT cV)
      'string '(@Vfunc $rT $cV) 
      '(gmap string (@Vfunc $rT $cV)) abs in

    let cvars := constr_of_constr_map constr_of_string
      (fun x => 
        let (_, tx) := lookup_vs_no_sum vs (Constr.type x) in 
        let ctx := constr_nat_of_int tx in 
        '(@mk_Vval $cV $ctx $x)) 'string '(Vval $cV)
        '(gmap string (Vval $cV)) vars in 
    
    let clhs := constr_of_tensorexpr tel in 
    let crhs := constr_of_tensorexpr ter in 
    let rSR := sR.(ringSR) in 
    apply (tensorexpr_eqb_correct_apply (SR:=$rSR)
      $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
    ltac1:(vm_cast_no_check (@eq_refl bool true))
  end.


Require Import TensorExprFastMatch.

Ltac2 te_refl_fast parse_abs' : unit :=
  lazy_match! goal with 
  | [|- ?_req ?lhs ?rhs] => 
    let rT := Constr.type lhs in 
    let sR := get_SRData rT in 
    let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux_data sR parse_abs'
      [] (FMap.empty string_tag) (FMap.empty string_tag) []
      lhs in 
    let (vs, abs, vars, _rels, ter) := 
      parse_tensor_expr_aux_data sR parse_abs'
      vs abs vars rels
      rhs in 

    let cV := get_cV vs in 
    let cVsum := get_cVsum vs in 
    let cabs := constr_of_constr_map constr_of_string
      (constr_of_typed_fun rT cV)
      'string '(@Vfunc $rT $cV) 
      '(gmap string (@Vfunc $rT $cV)) abs in

    let cvars := constr_of_constr_map constr_of_string
      (fun x => 
        let (_, tx) := lookup_vs_no_sum vs (Constr.type x) in 
        let ctx := constr_nat_of_int tx in 
        '(@mk_Vval $cV $ctx $x)) 'string '(Vval $cV)
        '(gmap string (Vval $cV)) vars in 
    
    let clhs := constr_of_tensorexpr tel in 
    let crhs := constr_of_tensorexpr ter in 
    let rSR := sR.(ringSR) in 
    apply (tensorexpr_eqb_correct_apply_db (SR:=$rSR)
      $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
    vm_compute;
    exact eq_refl
  end.

Ltac2 te_refl_fast_no_check parse_abs' : unit :=
  lazy_match! goal with 
  | [|- ?_req ?lhs ?rhs] => 
    let rT := Constr.type lhs in 
    let sR := get_SRData rT in 
    let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux_data sR parse_abs'
      [] (FMap.empty string_tag) (FMap.empty string_tag) []
      lhs in 
    let (vs, abs, vars, _rels, ter) := 
      parse_tensor_expr_aux_data sR parse_abs'
      vs abs vars rels
      rhs in 

    let cV := get_cV vs in 
    let cVsum := get_cVsum vs in 
    let cabs := constr_of_constr_map constr_of_string
      (constr_of_typed_fun rT cV)
      'string '(@Vfunc $rT $cV) 
      '(gmap string (@Vfunc $rT $cV)) abs in

    let cvars := constr_of_constr_map constr_of_string
      (fun x => 
        let (_, tx) := lookup_vs_no_sum vs (Constr.type x) in 
        let ctx := constr_nat_of_int tx in 
        '(@mk_Vval $cV $ctx $x)) 'string '(Vval $cV)
        '(gmap string (Vval $cV)) vars in 
    
    let clhs := constr_of_tensorexpr tel in 
    let crhs := constr_of_tensorexpr ter in 
    let rSR := sR.(ringSR) in 
    apply (tensorexpr_eqb_correct_apply_db (SR:=$rSR)
      $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
    ltac1:(vm_cast_no_check (@eq_refl bool true))
  end. *)



Section Testing.

  Parameter (A : Type).
  Parameter (SA : Summable A).

  Parameter (B : Type).
  Parameter (SB : Summable B).

  (* Convertible non-syntactically-equal type *)
  Definition C := A.
  Definition SC : Summable C := SA.
  Typeclasses Opaque C.

  Existing Instance SA.
  Existing Instance SB.
  Existing Instance SC.


  Context `{SR : SemiRing R rO rI radd rmul req}.
  Notation "0" := rO.
  Notation "1" := rI.
  Notation "x '==' y" := (req x y) (at level 70). 
  Infix "+" := radd. 
  Infix "*" := rmul.



  Parameter (f : A -> B -> A -> R).
  Parameter (g : A -> B -> R).

  (* #[export] *)
  (* Hint Extern 0 (ParseAT ?Vs _ _ _ (?f ?a1 ?b2 ?a3)) =>
    let tA := get_ty_nosum Vs A in 
    let tB := get_ty_nosum Vs B in 
    let V := constr:(λ i, projT1 (Vs !!! i)) in
    notypeclasses refine (Build_ParseAT Vs 
      (@existT (list Ty) (λ args, V_n_args V args R) 
        [tA;tB;tA] f : @Vfunc R V)
      [@mk_Vval V tA a1; @mk_Vval V tB b2] 
      [@mk_Vval V tA a3] 
      (f a1 b2 a3) _);
    constructor; reflexivity : typeclass_instances. *)

  (* #[export] *)
  (* Hint Extern 0 (ParseAT ?Vs _ _ _ (?g ?a1 ?b2)) =>
    let tA := get_ty_nosum Vs A in 
    let tB := get_ty_nosum Vs B in 
    let V := constr:(λ i, projT1 (Vs !!! i)) in
    notypeclasses refine (Build_ParseAT Vs 
      (@existT (list Ty) (λ args, V_n_args V args R) 
        [tA;tB] g : @Vfunc R V)
      [@mk_Vval V tA a1] [@mk_Vval V tB b2] 
      (g a1 b2) _);
    constructor; reflexivity : typeclass_instances. *)

  Parameter z : A.

  Local Definition te_lhs := 
    sum_of (fun x : A => sum_of (fun y : B => f x y z * g z y)).

  Local Definition te_rhs := 
    sum_of (fun y : B => sum_of (fun x : A => g z y * f x y z)).

  Definition te_prob n :=
    fold_right rmul te_lhs (repeat te_lhs n) == 
    fold_right rmul te_rhs (repeat te_rhs n).

  Arguments te_lhs /.
  Arguments te_rhs /.
  Arguments te_prob /.

  (* Local Ltac te_refl := 
    unshelve apply (ParseTE_reflexive_test _ _);
    [..|vm_compute; exact eq_refl];
    [exact nil|exact gmap_empty|exact gmap_empty]. *)

  (* Set Default Proof Mode "Classic". *)

From Ltac2 Require Import Notations.

Ltac2 Set parse_abstract as parse_abstract_old := fun c relmap => 
  lazy_match! c with
  | f ?x ?y ?z => Some ('f, [(x, 'A); (y, 'B)], [(z, 'A)])
  | g ?x ?y => Some ('g, [(x, 'A)], [(y, 'B)])
  | _ => parse_abstract_old c relmap
  end.


(* Set Default Proof Mode "Classic". *)

(* Local Ltac2 test (n : int) : unit :=
  print (of_int n); 
  let cn := constr_nat_of_int n in 
  ltac1:(cn |-
  let H := fresh in 
  assert (H : te_prob cn) by 
    ltac2:(cbn; te_refl parse_abs');
  clear H) (Ltac1.of_constr cn).

Local Ltac2 testf (n : int) : unit :=
  (* print (of_int n);  *)
  let cn := constr_nat_of_int n in 
  let h := Fresh.fresh (Fresh.Free.of_goal ()) ident:(H) in 
  assert ($h : te_prob $cn) by 
    (cbn; Control.time (Some (string_of_int n)) 
      (fun () => (te_refl_fast parse_abs')));
  clear $h. *)


(* Local Ltac2 testfU (n : int) : unit :=
  (* print (of_int n);  *)
  let cn := constr_nat_of_int n in 
  let h := Fresh.fresh (Fresh.Free.of_goal ()) ident:(H) in 
  assert ($h : te_prob $cn) by 
    (cbn; Control.time (Some (string_of_int n)) 
      (fun () => (te_refl_fast_UNSAFE parse_abs')));
  clear $h. *)



(*
Goal True.

test_parse_tensorexpr '(unfolded te_lhs).
reflexivity.


let c := '(unfolded te_lhs == unfolded te_rhs) in 
let ctx := empty_TEContext 'R in 
let (ctx, lhs, rhs) := parse_tensor_equality_aux ctx c in 
let cSR := ctx.(ctx_SR).(ringSR) in 
let cV := ctx_get_cV ctx in 
let cVsum := ctx_get_cVsum ctx in 
let cabs := ctx_get_cabs ctx in 
let cmg := ctx_get_cmg ctx in 
let cml := ctx_get_cml_list ctx in 
let clhs := constr_of_tensorexprdb lhs in 
let crhs := constr_of_tensorexprdb rhs in 
(* let clhs := constr_semantics_of_tensorexpr ctx lhs in 
let crhs := constr_semantics_of_tensorexpr ctx rhs in  *)
(* let cml := ctx_get_cml ctx in  *)
assert (@tensorequation_semantics_aux _ _ _ _ _ _ $cSR $cV $cVsum $cabs $cmg [] 
  $clhs $crhs $cml ∅).

red_te_semantics().

let cR := 'R in 
let c := '(
  forall z z', ∑ x : A, ∑ y : B, f x y z * g z' y ==
   ∑ y : B, ∑ x : A, g z' y * f x y z
) in 
Std.resolve_tc c;
te_rewrite_in_lhs cR c.
let tH := c in 

  let goalctx := empty_TEContext cR in 
  let (goalctx, glhs, grhs) := parse_tensor_equality_aux goalctx (Control.goal()) in 
  let hypctx := {goalctx with ctx_ml := [] } in 
  let (hypctx, hlhs, hrhs) := parse_tensor_equality_aux hypctx tH in 
  let goalml := goalctx.(ctx_ml) in 
  let ctx := {hypctx with ctx_ml := goalml} in 

  let cglhs := constr_of_tensorexprdb glhs in 
  let chlhs := constr_of_tensorexprdb hlhs in 
  let chrhs := constr_of_tensorexprdb hrhs in 
  let rew_expr := '(match_rewrite_tensorlist (tensorlist_of_tensorexpr $chlhs) 
    (tensorlist_of_tensorexpr $chrhs) (tensorlist_of_tensorexpr $cglhs)) in 
  let new_lhs_expr := Std.eval_vm None rew_expr in 
  match! new_lhs_expr with 
  | None => Control.throw_invalid_argument "te_rewrite_in_lhs: no rewrite found!"
  | Some ?e => 
    let new_lhs_expr := '(tensorexpr_of_tensorlist $e) in 
    let new_lhs_expr := Std.eval_vm None new_lhs_expr in
    let new_lhs := tensorexprdb_of_constr new_lhs_expr in 
    let new_goal := constr_semantics_of_tensor_equality ctx new_lhs grhs in 
    enough ($new_goal) by Control.shelve();
    red_te_semantics()
  end.

te_rewrite_in_lhs cR c.
test_parse_tensor_equality cR c.


reflexivity.
cbn.
remember @sum_of as s.
vm_compute.
subst s.


reflexivity.
vm_compute.

let ctx := empty_TEContext cR in ().
let (eqctx, lhs, rhs) := parse_tensor_equality_aux ctx tH in ().
let sem := constr_semantics_of_tensor_equality eqctx lhs rhs in 
assert ($tH = $sem).
vm_compute.
vm_compute (tensorequation_semantics_aux _ _ _ _ _ _).
cbv beta.
cbv -[sum_of].
reflexivity.

(* Ltac2 Eval  *)
let c := '(unfolded te_lhs == unfolded te_rhs) in 
let ctx := empty_TEContext 'R in 
let (ctx, lhs, rhs) := parse_tensor_equality_aux ctx c in 
let cSR := ctx.(ctx_SR).(ringSR) in 
let cV := ctx_get_cV ctx in 
let cVsum := ctx_get_cVsum ctx in 
let cabs := ctx_get_cabs ctx in 
let cmg := ctx_get_cmg ctx in 
let cml := ctx_get_cml_list ctx in 
let clhs := constr_of_tensorexprdb lhs in 
let crhs := constr_of_tensorexprdb rhs in 
(* let clhs := constr_semantics_of_tensorexpr ctx lhs in 
let crhs := constr_semantics_of_tensorexpr ctx rhs in  *)
(* let cml := ctx_get_cml ctx in  *)
'(@tensorequation_semantics_aux _ _ _ _ _ _ $cSR $cV $cVsum $cabs $cmg [] 
  $clhs $crhs $cml ∅)
test_parse_tensor_equalitydbR c.

rewrite (unfold te_lhs in te_lhs).

ltac1:(assert (Hrw : forall z w, ∑ x : A, ∑ y : B, f z y x * g x w ==
g z w) by admit).

Ltac2 Eval 
  let (ctx, rels, lhs, rhs) := parse_tensor_equality_aux 
  (empty_TEContext 'R) [] (Constr.type &Hrw) in 
  (ctx.(ctx_vs), FMap.bindings (ctx.(ctx_vars)), rels, lhs, rhs).

Constr.type 

let cn := constr_nat_of_int 0 in 
let h := Fresh.fresh (Fresh.Free.of_goal ()) ident:(H) in 
assert ($h : te_prob $cn).
cbn.

match! goal with 
| [|- ?g] => 
  let ganon := make_binders_anon g in 
  change $ganon
end.


Ltac2 Eval lazy_match! goal with 
  | [|- ?_req ?lhs ?rhs] => 
    let rT := Constr.type lhs in 
    let sR := get_SRData rT in 
    let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux_data sR parse_abs'
      [] (FMap.empty string_tag) (FMap.empty string_tag) []
      lhs in 
    tel
  end.

(* Time test 1.
Time test 2.
Time test 3.
Time test 4.
Time test 5.
Time test 6.
Time test 7.
Time test 8.
Time test 9.
Time test 10.
Time test 11.
Time test 12.
Time test 13.
Time test 14.
Time test 15.
Time test 16.
Time test 17.
Time test 18.
Time test 19.
Time test 20. *)


(* Time testf 1.
Time testf 2.
Time testf 3.
Time testf 4.
Time testf 5.
Time testf 6.
Time testf 7.
Time testf 8.
Time testf 9.
Time testf 10.
Time testf 11.
Time testf 12.
Time testf 13.
Time testf 14.
Time testf 15.
Time testf 16.
Time testf 17.
Time testf 18.
Time testf 19.
Time testf 20.
Time testf 21.
Time testf 22.
Time testf 23.
Time testf 24.
Time testf 25.
Time testf 26.
Time testf 27.
Time testf 28.
Time testf 29.
Time testf 30. *)
(* testf 40.
testf 50.
testf 60.
testf 70.
testf 80.
testf 90.
testf 100.
testf 40.
testf 50.
testf 60.
testf 70.
testf 80.
testf 90.
testf 100.
testf 40.
testf 50.
testf 60.
testf 70.
testf 80.
testf 90.
testf 100.
testf 40.
testf 50.
testf 60.
testf 70.
testf 80.
testf 90.
testf 100.
testf 40.
testf 50.
testf 60.
testf 70.
testf 80.
testf 90.
testf 100. *)


testfU 130.
testfU 140.
testfU 150.
testfU 160.
testfU 170.
testfU 180.
testfU 190.
testfU 200.

testfU 1.
testfU 2.
testfU 3.
testfU 4.
testfU 5.
testfU 6.
testfU 7.
testfU 8.
testfU 9.
testfU 10.
testfU 11.
testfU 12.
testfU 13.
testfU 14.
testfU 15.
testfU 16.
testfU 17.
testfU 18.
testfU 19.
testfU 20.
testfU 21.
testfU 22.
testfU 23.
testfU 24.
testfU 25.
testfU 26.
testfU 27.
testfU 28.
testfU 29.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.
testfU 30.
testfU 40.
testfU 50.
testfU 60.
testfU 70.
testfU 80.
testfU 90.
testfU 100.


(* ltac2:(
ltac1:(
let H := fresh in 
assert (H : let n := 10 in 
  foldr rmul te_lhs (repeat te_lhs n) == 
  foldr rmul te_lhs (repeat te_lhs n)));
cbn). *)

(* Ltac2 Eval (lookup_vs [('A, 'SA); ('B, 'SB)] 'A 'SB). *)

ltac1:(
let H := fresh in 
  assert (H : te_prob 20)).
cbn.


(* Time Ltac2 Eval
lazy_match! goal with 
| [|- ?_req ?lhs ?rhs] => 
  let rT := Constr.type lhs in 
  let sR := get_SRData rT in 
  let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux sR parse_abs'
    [] (FMap.empty string_tag) (FMap.empty string_tag) []
    lhs in 
  let (vs, abs, vars, rels, ter) := 
    parse_tensor_expr_aux sR parse_abs'
    vs abs vars rels
    rhs in 
  ter
end. *)

Time 

(* Time Ltac2 Eval *)
lazy_match! goal with 
| [|- ?_req ?lhs ?rhs] => 
  let rT := Constr.type lhs in 
  let sR := get_SRData rT in 
  let (vs, abs, vars, rels, tel) := parse_tensor_expr_aux sR parse_abs'
    [] (FMap.empty string_tag) (FMap.empty string_tag) []
    lhs in 
  let (vs, abs, vars, _rels, ter) := 
    parse_tensor_expr_aux sR parse_abs'
    vs abs vars rels
    rhs in 

  let cV := get_cV vs in 
  let cVsum := get_cVsum vs in 
  let cabs := constr_of_constr_map constr_of_string
    (constr_of_typed_fun rT cV)
    'string '(@Vfunc $rT $cV) 
    '(gmap string (@Vfunc $rT $cV)) abs in

  let cvars := constr_of_constr_map constr_of_string
    (fun x => 
      let (_, tx) := lookup_vs_no_sum vs (Constr.type x) in 
      let ctx := constr_nat_of_int tx in 
      '(@mk_Vval $cV $ctx $x)) 'string '(Vval $cV)
      '(gmap string (Vval $cV)) vars in 
(* ()
end).   *)
  let clhs := constr_of_tensorexpr tel in 
  let crhs := constr_of_tensorexpr ter in 
  let rSR := sR.(ringSR) in 
  (* let newlhs := '(total_semantics (SR:=$rSR)
    $cV (Vsum:=$cVsum) $cabs $cvars $clhs) in 
  let newrhs := '(total_semantics (SR:=$rSR)
    $cV (Vsum:=$cVsum) $cabs $cvars $crhs) in  *)
  
  apply (tensorexpr_eqb_correct_apply_db (SR:=$rSR)
    $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
  vm_compute; exact eq_refl
  (* ltac1:(vm_cast_no_check (@eq_refl bool true)) *)
  
    (* let prf := ('(tensorexpr_eqb_correct_apply (SR:=$rSR)
    $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs 
      ltac:(vm_cast_no_check (@eq_refl bool true)))) in 
  
  (exact $prf)
   *)
  
  
  (* Control.abstract *)
  (* let newgoal := '($req $newlhs $newrhs) in *)
  (* new *)
  (* ltac1:(prf |- pose proof prf as Heq) (Ltac1.of_constr prf) *)
  (* Std.vm_cast_no_check prf *)
    
  (* change $newgoal;
  refine '(tensorexpr_eqb_correct_apply (SR:=$rSR)
    $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs _);
  vm_compute; 
  exact eq_refl *)
  (* constr_of_constr_map *)
  (* constr_of_typed_fun rT cV 
    (snd (List.nth (FMap.bindings abs) 0)) *)
  (* (vs, FMap.bindings abs, FMap.bindings vars, rels, te) *)
  (* constr_of_tensorexpr te *)
end
.

Time vm_compute tensorlist_of_tensorexpr.
Time vm_compute.
done.

Time vm_compute.

(* From stdpp Require Import sorting.
Require Import TensorExprFastMatch.

match goal with
|- context[ tensorlist_of_tensorexpr ?te] => 
  assert (te_to_tldb te = mk_tldb [] [])
end.
1:{ 
  Time vm_compute.
}

replace tensorlist_of_tensorexpr with tensorlist_of_tensorexpr_alt_db.
Time vm_compute tensorlist_of_tensorexpr_alt_db. *)


do 2 idtac; [match goal with 
|- context [tensorlist_of_tensorexpr ?te] => 
  replace (tensorlist_of_tensorexpr te) with 
    (tensorlist_of_tensorexpr_alt te)
end|..].
2,3: vm_compute; reflexivity.

(* Time vm_compute. *)
Time vm_compute tensorlist_of_tensorexpr_alt.
Time vm_compute.
unfold tensorlist_eqb.
vm_compute bool_decide at 1.
cbv match.
vm_compute canonify_tl_aux''.
cbv match.
vm_compute bool_decide at 1.
cbv match.
(* Time vm_compute match_tensorlist. *)
(* Time vm_compute. *)
Require Import TensorExprFastMatch.

(* Time vm_compute.  *)
match goal with
|- context [match_tensorlist ?l ?r] =>
  replace (match_tensorlist l r) with (match_tensorlist_fast l r) by admit
end.

Time vm_compute.
(* Notation "'!Pset' '_'" := (PNodes _) (only printing). *)
unfold match_tensorlist_fast.
Time vm_compute list_to_set.
cbv delta [match_tensorlist_fast_aux] beta.
Time vm_compute collate.
Time vm_compute.
(* rewrite map_fold_foldr. *)

Time vm_compute map_to_list.
Time vm_compute.
(* Time vm_compute. *)
cbv delta [map_fold] beta.
Pmap_fold
Time vm_compute map_fold.
Time vm_compute.
Time vm_compute match_tensorlist_fast.

(* match goal with 
|- context [mk_tl _ ?abs] => 
  match abs with 
  | merge_sort _ _ => fail 1
  | _ => 
  replace abs with 
    (merge_sort (fun f g => String.le f.1.1 g.1.1) abs) by admit
  end
end. *)

do 2 match goal with 
|- context [mk_tl _ ?abs] => 
  match abs with 
  | merge_sort _ _ => fail 1
  | _ => 
  replace abs with 
    (merge_sort (fun f g => lexico f g) abs) by admit
  end
end.

vm_compute merge_sort.
Time vm_compute.


evar (tll : tensorlist).
evar (tlr : tensorlist).

transitivity (tensorlist_eqb tll tlr).
apply f_equal2.

Time vm_compute; reflexivity.
Time vm_compute; reflexivity.
subst tll tlr.
unfold tensorlist_eqb.
vm_compute bool_decide at 1.
cbv match.
vm_compute canonify_tl_aux''.
cbv match.
vm_compute bool_decide at 1.
cbv match.
Time vm_compute match_tensorlist at 1.
Time vm_compute.

match goal with 
|- context [@bool_decide ?P ?HP] => 
  vm_compute (@bool_decide P HP)
end.
replace (bool_decide _) with true.
2: vm_compute; reflexivity.

vm_compute (bool_decide _).
(* replace "f0" with "g". *)
vm_compute.
Time vm_compute; reflexivity.
Time 




match goal with 
| 

done.
Time Qed.

Time exact Heq.


done.
(* ltac1:(done). *)
Time Qed.
easy.

  

Time te_refl.
[cbn; time te_refl|clear H].
]
cbn.
Time te_refl.


assert (let n := 1%nat in 
fold_right rmul te_lhs (repeat te_lhs n) == 
fold_right rmul te_rhs (repeat te_rhs n)).
cbn. 
unfold te_lhs, te_rhs.
Time 



evar (a : A).
evar (a' : A).
evar (a'' : A).
evar (z : A).
evar (b : B).
evar (b' : B).
evar (b'' : B).

set (te_lhs := sum_of (fun x : A => 
  sum_of (fun y : B => f x y z * g z y))).
set (te_rhs := 
  sum_of (fun y : B => sum_of (fun x : A => g z y * f x y z))).

assert (let n := 1%nat in 
fold_right rmul te_lhs (repeat te_lhs n) == 
fold_right rmul te_rhs (repeat te_rhs n)).
cbn. 
unfold te_lhs, te_rhs.
Time 
unshelve apply (ParseTE_reflexive_test _ _);
[..|vm_compute; exact eq_refl];
[exact nil|exact gmap_empty|exact gmap_empty].
  sum_of (fun x => faaa a'' a' x) * sum_of (fun x : A => faaa a a' a'')).
Time 
unshelve apply (ParseTE_reflexive_test _ _);
[first [exact nil | exact gmap_empty]..|];
vm_compute; exact eq_refl.


(* #[export] *)
Hint Extern 0 (ParseAT ?Vs _ _ _ (?faab ?a1 ?a2 ?b3)) =>
  let tA := get_ty_nosum Vs A in 
  let tB := get_ty_nosum Vs B in 
  let V := constr:(λ i, projT1 (Vs !!! i)) in
  notypeclasses refine (Build_ParseAT Vs (@existT (list Ty) (λ args, V_n_args V args R) 
    [tA;tA;tB] faab : @Vfunc R V)
    [@mk_Vval V tA a1] [@mk_Vval V tA a2; @mk_Vval V tB b3] 
    (faab a1 a2 b3) _);
  constructor; reflexivity : typeclass_instances.





Goal True.

evar (a : A).
evar (a' : A).
evar (a'' : A).
evar (b : B).
evar (b' : B).
evar (b'' : B).







Parameter (faaa : A -> A -> A -> R).
Parameter (faab : A -> A -> B -> R).
Parameter (faba : A -> B -> A -> R).
Parameter (fabb : A -> B -> B -> R).
Parameter (fbaa : B -> A -> A -> R).
Parameter (fbab : B -> A -> B -> R).
Parameter (fbba : B -> B -> A -> R).
Parameter (fbbb : B -> B -> B -> R).


(* #[export] *)
Hint Extern 0 (ParseAT ?Vs _ _ _ (?faaa ?a1 ?a2 ?a3)) =>
  let tA := get_ty_nosum Vs A in 
  let V := constr:(λ i, projT1 (Vs !!! i)) in
  notypeclasses refine (Build_ParseAT Vs (@existT (list Ty) (λ args, V_n_args V args R) 
    [tA;tA;tA] faaa : @Vfunc R V)
    [@mk_Vval V tA a1] [@mk_Vval V tA a2; @mk_Vval V tA a3] 
    (faaa a1 a2 a3) _);
  constructor; reflexivity : typeclass_instances.

(* #[export] *)
Hint Extern 0 (ParseAT ?Vs _ _ _ (?faab ?a1 ?a2 ?b3)) =>
  let tA := get_ty_nosum Vs A in 
  let tB := get_ty_nosum Vs B in 
  let V := constr:(λ i, projT1 (Vs !!! i)) in
  notypeclasses refine (Build_ParseAT Vs (@existT (list Ty) (λ args, V_n_args V args R) 
    [tA;tA;tB] faab : @Vfunc R V)
    [@mk_Vval V tA a1] [@mk_Vval V tA a2; @mk_Vval V tB b3] 
    (faab a1 a2 b3) _);
  constructor; reflexivity : typeclass_instances.





Goal True.

evar (a : A).
evar (a' : A).
evar (a'' : A).
evar (b : B).
evar (b' : B).
evar (b'' : B).


assert ((sum_of (fun x : A => faaa a a' a'' * sum_of (fun x => faaa a'' a' x))) == 
  sum_of (fun x => faaa a'' a' x) * sum_of (fun x : A => faaa a a' a'')).
   *)

End Testing.
*)