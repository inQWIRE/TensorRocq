Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

Require Import Aux_stdpp.
Require Import TensorExprSyntax.

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


Ltac2 Type TEContext := {
  ctx_SR : SRData;
  ctx_vs : (constr * constr) list;
  ctx_abs : (AbsIdx, constr * int list * int list) FMap.t;
  ctx_vars : (VarIdx, constr) FMap.t; (* TODO: Keep type (as int) here as well *)
}.

Ltac2 mk_TEContext (ctx_SR : SRData)
  (ctx_vs : (constr * constr) list)
  (ctx_abs : (AbsIdx, constr * int list * int list) FMap.t)
  (ctx_vars : (VarIdx, constr) FMap.t) : TEContext := {
  ctx_SR := ctx_SR;
  ctx_vs := ctx_vs;
  ctx_abs := ctx_abs;
  ctx_vars := ctx_vars;
}.

Ltac2 empty_TEContext (cR : constr) : TEContext :=
  mk_TEContext (get_SRData cR) 
    [] (FMap.empty string_tag) (FMap.empty string_tag).



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

Ltac2 parse_var (vs : (constr * constr) list) 
  (vars : (VarIdx, constr) FMap.t) (rels : (int * VarIdx) list)
  (val : constr) (type : constr) : 
  (constr * constr) list * (VarIdx, constr) FMap.t * (int * VarIdx) :=
  match Unsafe.is_Rel_data val with 
  | Some i => 
    let i := Int.sub i 1 in (* Rel variables are 1-indexed! *)
    match List.nth_opt rels i with 
    | Some val => (vs, vars, val)
    | None => 
      Control.throw_invalid_argument (String.app "parse_var " (string_of_int i))
    end

    (* (vs, vars, List.nth rels i) *)
  | None =>
    let (vs, ty) := lookup_vs_no_sum vs type in 
    match FMap.find_inv_opt unify_eq val vars with 
    | Some idx => (vs, vars, (ty, idx))
    | None => let name := fresh_string (List.fold_right FSet.add 
            (List.map snd rels) (FMap.domain vars)) "x" in 
      (vs, FMap.add name val vars, (ty, name))
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
  | None => let name := fresh_string_of_map abs "f" in 
    (FMap.add name (f, low, up) abs, name)
  end.

Ltac2 parse_abs (vs : (constr * constr) list) 
  (abs : (AbsIdx, constr * int list * int list) FMap.t) 
  (vars : (VarIdx, constr) FMap.t) (rels : (int * VarIdx) list)
  (head : constr) (lower : (constr * constr) list)
  (upper : (constr * constr) list) :
  (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
  (VarIdx, constr) FMap.t * (int * VarIdx) list * 
  AbsData :=
  let (vs', vars', lower_tyvars) :=
    List.fold_right (fun (val, type) (vs, vars, tyvars) => 
      let (vs_, vars_, tyvar) := parse_var vs vars rels val type in 
      (vs_, vars_, tyvar :: tyvars)) lower (vs, vars, []) in 
  let (vs'', vars'', upper_tyvars) :=
    List.fold_right (fun (val, type) (vs, vars, tyvars) => 
      let (vs_, vars_, tyvar) := parse_var vs vars rels val type in 
      (vs_, vars_, tyvar :: tyvars)) upper (vs', vars', []) in 
  let (abs, abs_idx) := parse_abs_val abs head 
    (List.map fst lower_tyvars) (List.map fst upper_tyvars) in 
  let mk_strs := List.map (fun (i, v) => (string_of_int i, v)) in 
  (vs'', abs, vars'', rels, (abs_idx, mk_strs lower_tyvars, mk_strs upper_tyvars)).


Ltac2 ctx_parse_var ctx rels val type :=
  let (vs, vars, tyvar) := 
    parse_var (ctx.(ctx_vs)) (ctx.(ctx_vars)) rels val type in 
  ({ctx with ctx_vs := vs; ctx_vars := vars}, tyvar).

Ltac2 ctx_parse_abs_val ctx f low up :=
  let (abs, idx) := parse_abs_val (ctx.(ctx_abs)) f low up in  
  ({ctx with ctx_abs := abs}, idx).

Ltac2 ctx_parse_abs ctx rels head lower upper :=
  let (vs, abs, vars, rels, absdata) :=
    parse_abs (ctx.(ctx_vs)) (ctx.(ctx_abs)) (ctx.(ctx_vars)) rels 
      head lower upper in 
  ({ctx with ctx_vs := vs; ctx_vars := vars; ctx_abs := abs}, 
    rels, absdata).


Import PrintingExtra Pp.

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
  (vars : (VarIdx, constr) FMap.t) (* TODO: Keep type (as int) here as well *)
  (rels : (int * VarIdx) list) (* A mapping from unbound [Rel i] terms
    to their types (as indices of vs) and variables *)
  (c : constr) : 
  (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
    (VarIdx, constr) FMap.t * ((int * VarIdx) list) * TensorExpr :=
  let rec go vs abs vars rels c : 
    (constr * constr) list * (AbsIdx, constr * int list * int list) FMap.t * 
      (VarIdx, constr) FMap.t * ((int * VarIdx) list) * TensorExpr :=
  (* let rT := r.(ringType) in  *)
  (* print (str "go" ++ spc() ++ of_list (of_pair of_constr of_constr) vs ++
    spc() ++ print_map of_string of_constr abs ++ 
    spc() ++ print_map of_string of_constr vars ++
    spc() ++ of_list (of_pair of_int of_string) rels ++
    spc() ++ of_constr c);
  print (mt()); *)
  if unify_eq c (r.(ringI)) then (vs, abs, vars, rels, Product []) else
  match! c with 
  | @sum_of _  _ _  _ _  _  _  ?tA ?sA ?f =>
      let (vs', idx_A) := lookup_vs vs tA sA in 
      let (b, fbody) := Unsafe.decompose_lambda f in 
      let varname := match Constr.Binder.name b with 
        | Some n => Ident.to_string n
        | None => fresh_string (List.fold_right FSet.add 
            (List.map snd rels) (FMap.domain vars)) "x"
        end in 
      let rels' := (idx_A, varname) :: rels in
      let (vs'', abs, vars, rels'', body_te) :=
        go vs' abs vars (* To Done: Do we need to add [varname] somehow? *)
          rels' fbody in
      (vs'', abs, vars, List.tl rels'', Sum (string_of_int idx_A, varname) body_te)
      (* Product [] *)
      (* let rels := () *)
  | ?mul ?a ?b => 
    Std.unify mul (r.(ringmul));
    (* print (str "vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
    let (vs', abs', vars', rels', tea) := 
      go vs abs vars rels a in 
    (* print (str "vs': " ++ of_list (of_pair of_constr of_constr) vs'); *)
    let (vs'', abs'', vars'', rels'', teb) :=
      go vs' abs' vars' rels' b in
    (* print (str "vs'': " ++ of_list (of_pair of_constr of_constr) vs''); *)
    (vs'', abs'', vars'', rels'', Product [tea; teb])
  (* | _ => None *)
  | _ => 
    (* print (str "rel_typing_map for " ++ of_constr c ++ str " from: " ++ 
      of_list (of_pair of_int of_string) rels ++ spc() ++
      str "vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
    let rel_typing_map :=
      FMap.of_list FSet.Tags.int_tag
        (List.mapi (fun i (ty, _) => 
          (i, fst (List.nth vs ty)))
        rels) in 
    match to_abs c rel_typing_map with 
    | None => Control.throw (Invalid_argument (Some (
      Message.concat (Message.of_string "Could not parse constr as TensorExpr: ")
        (Message.of_constr c)))) 
    | Some (head, lower, upper) => 
    (* print (str "_vs: " ++ of_list (of_pair of_constr of_constr) vs); *)
      let (vs', abs', vars', rels', (idx, l, u)) := 
        parse_abs vs abs vars rels head lower upper in 
    (* print (str "_vs': " ++ of_list (of_pair of_constr of_constr) vs'); *)
      (vs', abs', vars', rels', Abstract idx l u)
    end
  end in 
  go vs abs vars rels c. 



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
  (ctx : TEContext) (rels : (int * VarIdx) list) (c : constr) : 
  TEContext * (int * VarIdx) list * TensorExpr :=
  let (vs, abs, vars, rels, te) := 
    parse_tensor_expr_aux_data (ctx.(ctx_SR)) parse_abstract 
      (ctx.(ctx_vs)) (ctx.(ctx_abs)) (ctx.(ctx_vars)) rels c in 
  ({ctx with ctx_vs := vs; ctx_abs := abs; ctx_vars := vars}, rels, te).


Ltac2 parse_tensor_equality_aux ctx rels c : 
  TEContext * (int * VarIdx) list * TensorExpr * TensorExpr :=
  let rec go ctx (rels : (int * VarIdx) list) c : 
    TEContext * (int * VarIdx) list * TensorExpr * TensorExpr :=
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
    let (ctx, rels, telhs) := parse_tensor_expr_aux ctx rels lhs in 
    let (ctx, rels, terhs) := parse_tensor_expr_aux ctx rels rhs in 
    (ctx, rels, telhs, terhs)
  | _ => 
    let (b, cbody) := Unsafe.decompose_prod c in 
    let tA := Constr.Binder.type b in 
    let (ctx, idx_A) := ctx_lookup_type_no_sum ctx tA in 
    let varname := match Constr.Binder.name b with 
      | Some n => Ident.to_string n
      | None => fresh_string (List.fold_right FSet.add 
          (List.map snd rels) (FMap.domain (ctx.(ctx_vars)))) "x"
      end in 
    let rels' := (idx_A, varname) :: rels in
    go ctx rels' cbody
  end in 
  go ctx rels c.

(* 
fresh_string (List.fold_right FSet.add 
            (List.map snd rels) (FMap.domain vars)) "x" *)

(* TODO: Helper function for parsing vector terms into split lists
Ltac2  *)






Require Import TensorExprSemantics.

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

(* Ltac2 Eval constr_of_constr_map 
  StringCustomNotation.string_name.IdentToString.string_to_coq_string
  (fun x => x)
  'string 'nat '(gmap string N)
  (FMap.of_list string_tag [("a", '1); ("b", '1)]). *)

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
  end.

(* Ltac2 te_refl_fast_UNSAFE parse_abs' : unit :=
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
    
    let clhs := constr_of_tensorexpr tel in 
    let crhs := constr_of_tensorexpr ter in 
    let rSR := sR.(ringSR) in 
    apply (tensorlistdebruijn_eqb_correct_apply (SR:=$rSR)
      $cV (Vsum:=$cVsum) $cabs $cvars $clhs $crhs);
    vm_compute;
    exact eq_refl
  end. *)
(* 
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

Local Ltac2 mutable parse_abs' : constr -> (* the constr to decompose. Note it will likely be unsafe 
    by containing [Rel _] terms. All these will be mapped in [relmap], however *)
    (int, constr) FMap.t -> (* The typing map for [Rel _] derived from 
      [relmap] and [vs] (i.e. [Rel i] has type [T = nth vs j] where [relmap !! i = (j, _)]) *)
    (constr * (* head symbol *)
      (constr * constr) list * (* lower arguments and their types *)
      (constr * constr) list (* upper arguments and their types *)) option :=
  fun _c _relmap =>
  None.

Ltac2 Set parse_abs' as parse_abs'_old := fun c relmap => 
  lazy_match! c with
  | f ?x ?y ?z => Some ('f, [(x, 'A); (y, 'B)], [(z, 'A)])
  | _ => parse_abs'_old c relmap
  end.
Ltac2 Set parse_abs' as parse_abs'_old := fun c relmap => 
  lazy_match! c with
  | g ?x ?y => 
    (* print (of_constr x); *)
    Some ('g, [(x, 'A)], [(y, 'B)])
  | _ => parse_abs'_old c relmap
  end.

Ltac2 Set parse_abstract as parse_abstract_old := fun c relmap => 
  lazy_match! c with
  | f ?x ?y ?z => Some ('f, [(x, 'A); (y, 'B)], [(z, 'A)])
  | g ?x ?y => Some ('g, [(x, 'A)], [(y, 'B)])
  | _ => parse_abstract_old c relmap
  end.


(* Set Default Proof Mode "Classic". *)

Local Ltac2 test (n : int) : unit :=
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
  clear $h.


(* Local Ltac2 testfU (n : int) : unit :=
  (* print (of_int n);  *)
  let cn := constr_nat_of_int n in 
  let h := Fresh.fresh (Fresh.Free.of_goal ()) ident:(H) in 
  assert ($h : te_prob $cn) by 
    (cbn; Control.time (Some (string_of_int n)) 
      (fun () => (te_refl_fast_UNSAFE parse_abs')));
  clear $h. *)

Goal True.

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