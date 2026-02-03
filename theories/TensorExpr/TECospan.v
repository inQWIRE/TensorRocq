Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp Aux_pos.

Require Export TESyntax.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.




Definition make_vecs_map {A n m} (ins : vec Idx n) (outs : vec Idx m)
  (insv : vec A n) (outsv : vec A m) : Pmap A :=
  list_to_map (vzip ins insv ++ vzip outs outsv).


Record CospanTensorExpr {n m : nat} := mk_cote {
  cote_expr : tensorexpr;
  cote_inputs : vec Idx n;
  cote_outputs : vec Idx m;
}.

Record CospanTensorList {n m : nat} := mk_cotl {
  cotl_expr : tensorlist;
  cotl_inputs : vec Idx n;
  cotl_outputs : vec Idx m;
}.

Record CospanNamedTensorList {n m : nat} := mk_contl {
  contl_expr : namedtensorlist;
  contl_inputs : vec Idx n;
  contl_outputs : vec Idx m;
}.

#[global] Arguments CospanTensorExpr (_ _) : clear implicits, assert.
#[global] Arguments CospanTensorList (_ _) : clear implicits, assert.
#[global] Arguments CospanNamedTensorList (_ _) : clear implicits, assert.

#[global] Arguments mk_cote {_ _} (_ _ _) : assert.
#[global] Arguments mk_cotl {_ _} (_ _ _) : assert.
#[global] Arguments mk_contl {_ _} (_ _ _) : assert.

#[global] Coercion cote_expr : CospanTensorExpr >-> tensorexpr.
#[global] Coercion cotl_expr : CospanTensorList >-> tensorlist.
#[global] Coercion contl_expr : CospanNamedTensorList >-> namedtensorlist.


Definition cospantensorlist_of_cospantensorexpr {n m} (cote : CospanTensorExpr n m) :
  CospanTensorList n m :=
  mk_cotl (tensorlist_of_tensorexpr cote.(cote_expr))
    cote.(cote_inputs) cote.(cote_outputs).

Definition cospantensorexpr_of_cospantensorlist {n m} (cotl : CospanTensorList n m) :
  CospanTensorExpr n m :=
  mk_cote (tensorexpr_of_tensorlist cotl.(cotl_expr))
    cotl.(cotl_inputs) cotl.(cotl_outputs).

(* FIXME: align naming of all these, decide on coercions *)
Definition cotl2contl {n m} (cotl : CospanTensorList n m) :
  CospanNamedTensorList n m :=
  mk_contl (tl2ntl cotl.(cotl_expr))
    cotl.(cotl_inputs) cotl.(cotl_outputs).

Definition contl2cotl {n m} (contl : CospanNamedTensorList n m) :
  CospanTensorList n m :=
  mk_cotl (ntl2tl contl.(contl_expr))
    contl.(contl_inputs) contl.(contl_outputs).


Definition relabel_cotl f {n m} (cotl : CospanTensorList n m) :=
  mk_cotl (relabel_tl (relabel_frees f) cotl)
    (vmap f cotl.(cotl_inputs)) (vmap f cotl.(cotl_outputs)).

Definition relabel_contl_free f {n m} (contl : CospanNamedTensorList n m) :=
  mk_contl (relabel_ntl_free f contl)
    (vmap f contl.(contl_inputs)) (vmap f contl.(contl_outputs)).

Definition relabel_contl_bound f {n m} (contl : CospanNamedTensorList n m) :=
  mk_contl (relabel_ntl_bound f contl)
    contl.(contl_inputs) contl.(contl_outputs).



Definition swapped_stack_contl_aux {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n' + n) (m + m') :=
  mk_contl (ntl_times_aux contl contl')
    (contl'.(contl_inputs) +++ contl.(contl_inputs))
    (contl.(contl_outputs) +++ contl'.(contl_outputs)).

Definition swapped_stack_contl {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n' + n) (m + m') :=
  swapped_stack_contl_aux (relabel_contl_free (bcons false) contl)
    (relabel_contl_free (bcons true) contl').


Definition add_top_loop_contl_spec {n m} 
  (contl : CospanNamedTensorList (S n) (S m)) : 
  CospanNamedTensorList n m :=
  mk_contl (add_loop_ntl (vhd contl.(contl_inputs)) (vhd contl.(contl_outputs))
    contl) (vtl contl.(contl_inputs)) (vtl contl.(contl_outputs)).

Definition add_top_loop_contl {n m} 
  (contl : CospanNamedTensorList (S n) (S m)) : 
  CospanNamedTensorList n m :=
  mk_contl (add_loop_ntl_alt (vhd contl.(contl_inputs)) (vhd contl.(contl_outputs))
    contl) (vtl contl.(contl_inputs)) (vtl contl.(contl_outputs)).

Fixpoint add_top_loops_contl {n m o} :
  forall (contl : CospanNamedTensorList (n + m) (n + o)), 
    CospanNamedTensorList m o :=
  match n with
  | O => fun contl => contl
  | S n' => fun contl => 
    add_top_loops_contl (add_top_loop_contl contl)
  end.





Require Export Tensor TESemantics.

Section Semantics.

Context `{SR : SemiRing R rO rI radd rmul req}.

Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.


Context `{SA : Summable A, AEQ : EqDecision A}.

Let Tensor n m := (@Tensor R n m A).

Let DimensionlessTensor := (@DimensionlessTensor R A).


Notation varcontext := (Pmap A).

Notation abscontext := (Pmap DimensionlessTensor).


Definition cote_semantics (mabs : abscontext)
  {n m} (cote : CospanTensorExpr n m) : Tensor n m :=
  fun v w =>
  total_semantics mabs (make_vecs_map cote.(cote_inputs) cote.(cote_outputs) v w)
    cote.(cote_expr).

Definition cotl_semantics (mabs : abscontext)
  {n m} (cotl : CospanTensorList n m) : Tensor n m :=
  fun v w =>
  tl_total_semantics mabs
    (make_vecs_map cotl.(cotl_inputs) cotl.(cotl_outputs) v w)
    cotl.(cotl_expr).

Definition contl_semantics (mabs : abscontext)
  {n m} (contl : CospanNamedTensorList n m) : Tensor n m :=
  fun v w =>
  ntl_total_semantics mabs
    (make_vecs_map contl.(contl_inputs) contl.(contl_outputs) v w)
    contl.(contl_expr).


End Semantics.


