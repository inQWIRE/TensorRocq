(* Require StringCustomNotation. *)

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

From TensorRocq Require Import Aux_stdpp Aux_pos Summable.
From TensorRocq Require Export TESyntax.








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
  mk_contl (ntl_relabel_free f contl)
    (vmap f contl.(contl_inputs)) (vmap f contl.(contl_outputs)).

Definition relabel_contl_bound f {n m} (contl : CospanNamedTensorList n m) :=
  mk_contl (ntl_relabel_bound f contl)
    contl.(contl_inputs) contl.(contl_outputs).


Definition reindex_contl f {n m} (contl : CospanNamedTensorList n m) :=
  mk_contl (ntl_relabel_absidx f contl) contl.(contl_inputs) contl.(contl_outputs).


Definition swapped_stack_contl_aux {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n' + n) (m + m') :=
  mk_contl (ntl_times contl contl')
    (contl'.(contl_inputs) +++ contl.(contl_inputs))
    (contl.(contl_outputs) +++ contl'.(contl_outputs)).

Definition swapped_stack_contl {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n' + n) (m + m') :=
  swapped_stack_contl_aux (relabel_contl_free (bcons false) contl)
    (relabel_contl_free (bcons true) contl').


Definition stack_contl_aux {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n + n') (m + m') :=
  mk_contl (ntl_times contl contl')
    (contl.(contl_inputs) +++ contl'.(contl_inputs))
    (contl.(contl_outputs) +++ contl'.(contl_outputs)).

Definition stack_contl {n m n' m'}
  (contl : CospanNamedTensorList n m)
  (contl' : CospanNamedTensorList n' m') : CospanNamedTensorList (n + n') (m + m') :=
  stack_contl_aux (relabel_contl_free (bcons false) contl)
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


Definition ntl_cons_delta l u ntl :=
  mk_ntl ntl.(ntl_sums) ntl.(ntl_abstracts) ((l, u) :: ntl.(ntl_deltas)).

Definition ntl_app_deltas delt ntl :=
  mk_ntl ntl.(ntl_sums) ntl.(ntl_abstracts) (delt ++ ntl.(ntl_deltas)).

Definition compose_contl_aux {n m o} 
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList m o) : 
  CospanNamedTensorList n o :=
  mk_contl (ntl_app_deltas (vzip_with (λ l u, (free l, free u)) 
    contl.(contl_outputs) contl'.(contl_inputs)) $
    ntl_times_aux contl contl')
    (contl.(contl_inputs)) (contl'.(contl_outputs)).


Definition compose_contl {n m o} 
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList m o) : 
  CospanNamedTensorList n o :=
  compose_contl_aux (relabel_contl_free (bcons false) contl)
    (relabel_contl_free (bcons true) contl').


Lemma ntl_ext ntl ntl' :
  ntl.(ntl_sums) = ntl'.(ntl_sums) ->
  ntl.(ntl_abstracts) = ntl'.(ntl_abstracts) ->
  ntl.(ntl_deltas) = ntl'.(ntl_deltas) ->
  ntl = ntl'.
Proof.
  destruct ntl, ntl'; cbn; congruence.
Qed.


Definition WT_contl {n m} (contl : CospanNamedTensorList n m) : Prop :=
  WT_ntl (list_to_set (contl.(contl_inputs) ++ contl.(contl_outputs)))
    contl.(contl_expr).



Lemma ntl_relabel_free_ext_strong f g ntl :
  (forall i, i ∈ ntl_free_varset ntl -> f i = g i) ->
  ntl_relabel_free f ntl = ntl_relabel_free g ntl.
Proof.
  intros Hfg.
  apply ntl_ext; cbn.
  - done.
  - apply list_fmap_ext.
    intros _ flu Hflu%elem_of_list_lookup_2.
    apply relabel_abs_ext_strong.
    intros v Hv.
    destruct v as [|v]; [done|].
    cbn.
    f_equal.
    apply Hfg.
    apply elem_of_union; left.
    apply elem_of_abstracts_free_vars.
    destruct flu as [[]]; eauto.
  - apply list_fmap_ext.
    intros _ lu Hlu%elem_of_list_lookup_2.
    apply relabel_delt_ext_strong.
    intros v Hv.
    destruct v as [|v]; [done|].
    cbn.
    f_equal.
    apply Hfg.
    apply elem_of_union; right.
    apply elem_of_deltas_free_vars.
    exists lu.1, lu.2.
    destruct lu as []; cbn in *; naive_solver.
Qed.

Lemma ntl_relabel_free_id ntl :
  ntl_relabel_free id ntl = ntl.
Proof.
  apply ntl_ext; cbn.
  - done.
  - apply list_fmap_id'; intros flu _.
    apply relabel_abs_id'.
    now intros [].
  - apply list_fmap_id'; intros lu _.
    apply relabel_delt_id'.
    now intros [].
Qed.

Lemma ntl_relabel_free_compose f g ntl :
  ntl_relabel_free g (ntl_relabel_free f ntl) =
  ntl_relabel_free (g ∘ f) ntl.
Proof.
  apply ntl_ext; cbn.
  - done.
  - rewrite <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ flu _.
    cbn.
    rewrite relabel_abs_compose.
    apply relabel_abs_ext.
    now intros [].
  - rewrite <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ lu _.
    cbn.
    rewrite relabel_delt_compose.
    apply relabel_delt_ext.
    now intros [].
Qed.

Lemma contl_ext {n m} (contl contl' : CospanNamedTensorList n m) :
  contl.(contl_expr) = contl'.(contl_expr) ->
  contl.(contl_inputs) = contl'.(contl_inputs) ->
  contl.(contl_outputs) = contl'.(contl_outputs) ->
  contl = contl'.
Proof.
  destruct contl, contl'; cbn; congruence.
Qed.

Lemma relabel_contl_free_ext_strong f g {n m} (contl : CospanNamedTensorList n m) :
  (forall i, i ∈ ntl_free_varset contl.(contl_expr) ∪
    list_to_set (contl.(contl_inputs) ++ contl.(contl_outputs)) -> f i = g i) ->
  relabel_contl_free f contl = relabel_contl_free g contl.
Proof.
  intros Hfg.
  apply contl_ext; cbn.
  - apply ntl_relabel_free_ext_strong.
    intros i Hi.
    apply Hfg.
    set_solver +Hi.
  - apply vec_to_list_inj2.
    rewrite 2 vec_to_list_map.
    apply list_fmap_ext.
    intros _ ? Hx%elem_of_list_lookup_2.
    apply Hfg; set_solver +Hx.
  - apply vec_to_list_inj2.
    rewrite 2 vec_to_list_map.
    apply list_fmap_ext.
    intros _ ? Hx%elem_of_list_lookup_2.
    apply Hfg; set_solver +Hx.
Qed.

Lemma relabel_contl_free_id {n m} (contl : CospanNamedTensorList n m) :
  relabel_contl_free id contl = contl.
Proof.
  apply contl_ext; [|apply Vector.map_id..].
  apply ntl_relabel_free_id.
Qed.

Lemma relabel_contl_free_compose f g {n m} (contl : CospanNamedTensorList n m) :
  relabel_contl_free g (relabel_contl_free f contl) =
  relabel_contl_free (g ∘ f) contl.
Proof.
  apply contl_ext; cbn; [|now rewrite Vector.map_map..].
  apply ntl_relabel_free_compose.
Qed.


Inductive contl_interface_eq {n m} : relation (CospanNamedTensorList n m) :=
  | interface_contl_eq_of_inj f `{Hf : !Inj eq eq f}
    (ins : vec _ n) (outs : vec _ m) ntl :
    contl_interface_eq (mk_contl ntl ins outs)
      (mk_contl (ntl_relabel_free f ntl) (vmap f ins) (vmap f outs)).


Lemma contl_interface_eq_iff_exists {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' <->
  exists f, Inj eq eq f /\
  relabel_contl_free f contl = contl'.
Proof.
  split.
  - intros [].
    eexists.
    split; [eassumption|].
    done.
  - intros (f & Hf & <-).
    now destruct contl; constructor.
Qed.


Lemma contl_interface_eq_iff_exists_partial {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' <->
  exists f, set_Forall2 (fun i j => f i = f j -> i = j)
    (ntl_free_varset contl.(contl_expr) ∪
      list_to_set (contl.(contl_inputs) ++ contl.(contl_outputs))) /\
  relabel_contl_free f contl = contl'.
Proof.
  rewrite contl_interface_eq_iff_exists.
  split.
  - intros (f & Hf & Hfcontl).
    exists f.
    split; [|apply Hfcontl].
    intros ? ? ? ?; apply Hf.
  - intros (f & Hf & <-).
    apply partial_injection_extension' in Hf as (g & Hg & Hgf).
    exists g.
    split; [easy|].
    now apply relabel_contl_free_ext_strong.
Qed.

Lemma contl_interface_eq_refl {n m} (contl : CospanNamedTensorList n m) :
  contl_interface_eq contl contl.
Proof.
  apply contl_interface_eq_iff_exists.
  exists id.
  split; [apply _|].
  apply relabel_contl_free_id.
Qed.

Lemma abstracts_free_vars_relabel_frees (f : positive -> positive)
  (abs : list _) :
  abstracts_free_vars (relabel_abs (relabel_frees f) <$> abs) =
  set_map f (abstracts_free_vars abs).
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_map, elem_of_abstracts_free_vars.
  setoid_rewrite elem_of_abstracts_free_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  setoid_rewrite exists_pair.
  split.
  - intros (_ & _ & _ & (idx & low & up & [= -> -> ->] & Hlu) & Hr).
    rewrite <- fmap_app, elem_of_list_fmap in Hr.
    destruct Hr as ([] & [= ->] & Hr).
    eauto 20.
  - intros (r' & -> & idx & low & up & Hlu & Hr').
    eexists _, _, _.
    split; [exists idx, low, up; split; [cbn; reflexivity|easy]|].
    rewrite <- fmap_app.
    apply (elem_of_list_fmap_1 (relabel_frees f) _ _ Hr').
Qed.
Lemma deltas_free_vars_relabel_frees (f : positive -> positive)
  (delt : list _) :
  deltas_free_vars (relabel_delt (relabel_frees f) <$> delt) =
  set_map f (deltas_free_vars delt).
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_map, elem_of_deltas_free_vars.
  setoid_rewrite elem_of_deltas_free_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  cbn.
  split; [|set_solver].
  intros (l & u & (a & b & [= -> ->] & Hab) & Hor).
  destruct a, b; cbn in *; naive_solver.
Qed.


Lemma abstracts_bound_vars_relabel_frees (f : positive -> positive)
  (abs : list _) :
  abstracts_bound_vars (relabel_abs (relabel_frees f) <$> abs) =
  abstracts_bound_vars abs.
Proof.
  rewrite abstracts_bound_vars_relabel_abs.
  rewrite <- set_omap_v2bound_abstracts_vars.
  unfold set_omap.
  f_equal.
  apply list_omap_ext, Forall_Forall2_diag.
  rewrite Forall_forall.
  now intros [] _.
Qed.
Lemma deltas_bound_vars_relabel_frees (f : positive -> positive)
  (delt : list _) :
  deltas_bound_vars (relabel_delt (relabel_frees f) <$> delt) =
  deltas_bound_vars delt.
Proof.
  rewrite deltas_bound_vars_relabel_delt.
  rewrite <- set_omap_v2bound_deltas_vars.
  unfold set_omap.
  f_equal.
  apply list_omap_ext, Forall_Forall2_diag.
  rewrite Forall_forall.
  now intros [] _.
Qed.

Lemma ntl_free_varset_ntl_relabel_free f ntl :
  ntl_free_varset (ntl_relabel_free f ntl) =
  set_map f (ntl_free_varset ntl).
Proof.
  destruct ntl as [isums abs delt].
  unfold ntl_free_varset; cbn [ntl_abstracts ntl_deltas ntl_relabel_free].
  rewrite abstracts_free_vars_relabel_frees,
    deltas_free_vars_relabel_frees.
  now rewrite set_map_union_L.
Qed.


Lemma contl_interface_eq_symm {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' -> contl_interface_eq contl' contl.
Proof.
  intros (f & Hf & <-)%contl_interface_eq_iff_exists.
  apply contl_interface_eq_iff_exists_partial.
  exists (invfun f (elements (ntl_free_varset contl.(contl_expr) ∪
      list_to_set (contl.(contl_inputs) ++ contl.(contl_outputs))))).
  split.
  - cbn.
    rewrite ntl_free_varset_ntl_relabel_free.
    rewrite 2 vec_to_list_map, <- fmap_app,
      <- (set_map_list_to_set_L (SA:=Pset)).
    rewrite <- set_map_union_L.
    rewrite <- (list_to_set_elements_L (C:=Pset)).
    rewrite <- (fmap_elements _).
    rewrite set_Forall2_list_to_set.
    apply invfun_inj.
    intros ? ? ? ?; apply Hf.
  - rewrite relabel_contl_free_compose.
    etransitivity; [|apply relabel_contl_free_id].
    apply relabel_contl_free_ext_strong.
    intros i Hi%elem_of_elements.
    cbn.
    apply invfun_linv, Hi.
    intros ? ? ? ?; apply Hf.
Qed.

Lemma contl_interface_eq_trans {n m} (contl contl' contl'' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' -> contl_interface_eq contl' contl'' ->
  contl_interface_eq contl contl''.
Proof.
  intros (f & Hf & <-)%contl_interface_eq_iff_exists
    (g & Hg & <-)%contl_interface_eq_iff_exists.
  apply contl_interface_eq_iff_exists.
  exists (g ∘ f).
  split; [apply _|].
  now rewrite relabel_contl_free_compose.
Qed.

Add Parametric Relation {n m} : (CospanNamedTensorList n m) contl_interface_eq
  reflexivity proved by contl_interface_eq_refl
  symmetry proved by contl_interface_eq_symm
  transitivity proved by contl_interface_eq_trans
  as contl_interface_eq_setoid.


Lemma ntl_relabel_free_WF f ntl :
  WF_ntl (ntl_relabel_free f ntl) <-> WF_ntl ntl.
Proof.
  unfold WF_ntl.
  cbn -[abstracts_bound_vars deltas_bound_vars].
  rewrite abstracts_bound_vars_relabel_frees,
    deltas_bound_vars_relabel_frees.
  done.
Qed.

Lemma ntl_relabel_free_WT tl f ntl :
  WT_ntl tl ntl -> WT_ntl (set_map f tl) (ntl_relabel_free f ntl).
Proof.
  unfold WT_ntl.
  rewrite ntl_relabel_free_WF.
  cbn -[abstracts_free_vars deltas_free_vars].
  rewrite abstracts_free_vars_relabel_frees,
    deltas_free_vars_relabel_frees.
  intros (?&?&?);
  split_and!; [now apply set_map_mono..|easy].
Qed.

Lemma contl_interface_eq_WT_fwd {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' ->
  WT_contl contl -> WT_contl contl'.
Proof.
  unfold WT_contl.
  intros [].
  cbn [contl_inputs contl_outputs contl_expr].
  rewrite 2 vec_to_list_map, <- fmap_app, <- (set_map_list_to_set_L (SA:=Pset)).
  apply ntl_relabel_free_WT.
Qed.


Lemma contl_interface_eq_WT {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_interface_eq contl contl' ->
  WT_contl contl <-> WT_contl contl'.
Proof.
  intros Heq; split; apply contl_interface_eq_WT_fwd; [|symmetry]; easy.
Qed.



Inductive contl_eq_step {n m} : relation (CospanNamedTensorList n m) :=
  | ntl_eq_contl_eq_step (ins : vec _ n) (outs : vec _ m) ntl ntl' :
    ntl_eq (list_to_set (ins ++ outs)) ntl ntl' ->
    contl_eq_step (mk_contl ntl ins outs) (mk_contl ntl' ins outs)
  | interface_contl_eq_step contl contl' : contl_interface_eq contl contl' ->
    contl_eq_step contl contl'.

Lemma contl_eq_step_symm {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_eq_step contl contl' -> contl_eq_step contl' contl.
Proof.
  intros [].
  - apply ntl_eq_contl_eq_step.
    now symmetry.
  - apply interface_contl_eq_step.
    now symmetry.
Qed.

Definition contl_eq {n m} : relation (CospanNamedTensorList n m) :=
  rtc contl_eq_step.

#[export] Instance contl_eq_setoid {n m} : Equivalence (@contl_eq n m).
Proof.
  apply rtc_equivalence; intros ? ?; apply contl_eq_step_symm.
Qed.

(* FIXME: Move *)
Lemma ntl_eq_WF tl (ntl ntl' : namedtensorlist) :
  ntl_eq tl ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  intros Heq.
  induction Heq as [|x y z Hstep]; [done|].
  etransitivity; [|eassumption].
  destruct Hstep as [Haeq|Hdelt].
  - split; apply ntl_aeq_WF; [|symmetry]; easy.
  - now apply (ntl_delta_eq_WF tl).
Qed.
Lemma ntl_eq_WT tl (ntl ntl' : namedtensorlist) :
  ntl_eq tl ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  intros Heq.
  induction Heq as [|x y z Hstep]; [done|].
  etransitivity; [|eassumption].
  destruct Hstep as [Haeq|Hdelt].
  - split; apply ntl_aeq_WT; [|symmetry]; easy.
  - now apply ntl_delta_eq_WT.
Qed.


Lemma contl_eq_step_WT {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_eq_step contl contl' ->
  WT_contl contl <-> WT_contl contl'.
Proof.
  intros [].
  - now apply ntl_eq_WT.
  - now apply contl_interface_eq_WT.
Qed.

Lemma contl_eq_WT {n m} (contl contl' : CospanNamedTensorList n m) :
  contl_eq contl contl' ->
  WT_contl contl <-> WT_contl contl'.
Proof.
  intros Heq.
  induction Heq; [done|].
  etransitivity; [|eassumption].
  now apply contl_eq_step_WT.
Qed.



(* FIXME: Move *)
Lemma contl_mk_surj {n m} (contl : CospanNamedTensorList n m) :
  contl = mk_contl contl.(contl_expr) contl.(contl_inputs) contl.(contl_outputs).
Proof.
  now destruct contl.
Qed.
Lemma contl_eq_of_ntl_eq {n m} (ins : vec _ n) (outs : vec _ m) ntl ntl' :
  ntl_eq (list_to_set (ins ++ outs)) ntl ntl' ->
  contl_eq (mk_contl ntl ins outs) (mk_contl ntl' ins outs).
Proof.
  intros Heq.
  apply rtc_once.
  now constructor.
Qed.
Lemma contl_eq_relabel_free f `{Hf : !Inj eq eq f}
  {n m} (contl : CospanNamedTensorList n m) :
  contl_eq contl (relabel_contl_free f contl).
Proof.
  apply rtc_once.
  constructor.
  apply contl_interface_eq_iff_exists.
  eauto.
Qed.

(* FIXME: Move!!! *)


Lemma WT_ntl_free_varset_subseteq tl ntl :
  WT_ntl tl ntl -> ntl_free_varset ntl ⊆ tl.
Proof.
  intros (?&?&?).
  unfold ntl_free_varset.
  now apply union_subseteq.
Qed.

Lemma WT_ntl_alt_varset tl ntl :
  WT_ntl tl ntl <->
  ntl_free_varset ntl ⊆ tl /\
  WF_ntl ntl.
Proof.
  unfold WT_ntl, ntl_free_varset.
  rewrite union_subseteq.
  tauto.
Qed.

Lemma ntl_free_varset_insert_sum x ntl :
  ntl_free_varset (ntl_insert_sum x ntl) = ntl_free_varset ntl.
Proof.
  done.
Qed.

Lemma ntl_bound_varset_insert_sum x ntl :
  ntl_bound_varset (ntl_insert_sum x ntl) = ntl_bound_varset ntl.
Proof.
  done.
Qed.


Lemma ntl_varset_decomp ntl :
  ntl_varset ntl = set_map bound (ntl_bound_varset ntl) ∪
    set_map free (ntl_free_varset ntl).
Proof.
  unfold ntl_varset, ntl_bound_varset, ntl_free_varset.
  rewrite 2 set_map_union_L.
  rewrite abstracts_vars_decomp, deltas_vars_decomp.
  apply set_eq.
  intros x.
  rewrite !elem_of_union.
  tauto.
Qed.


#[global] Arguments abstracts_vars : simpl never.
#[global] Arguments deltas_vars : simpl never.
#[global] Arguments abstracts_bound_vars : simpl never.
#[global] Arguments deltas_bound_vars : simpl never.
#[global] Arguments abstracts_free_vars : simpl never.
#[global] Arguments deltas_free_vars : simpl never.

Lemma ntl_free_varset_relabel_ntl f ntl :
  ntl_free_varset (relabel_ntl f ntl) =
  set_omap (v2free ∘ f) (ntl_varset ntl).
Proof.
  unfold ntl_free_varset, ntl_varset.
  cbn.
  rewrite abstracts_free_vars_relabel_abs,
    deltas_free_vars_relabel_delt, set_omap_union_L.
  done.
Qed.

Lemma ntl_bound_varset_relabel_ntl f ntl :
  ntl_bound_varset (relabel_ntl f ntl) =
  set_omap (v2bound ∘ f) (ntl_varset ntl).
Proof.
  unfold ntl_bound_varset, ntl_varset.
  cbn.
  rewrite abstracts_bound_vars_relabel_abs,
    deltas_bound_vars_relabel_delt, set_omap_union_L.
  done.
Qed.



Lemma ntl_free_varset_add_loop_ntl_alt_as l r x ntl :
  ntl_free_varset (add_loop_ntl_alt_as l r x ntl) =
  ntl_free_varset ntl ∖ {[l; r]}.
Proof.
  unfold add_loop_ntl_alt_as.
  rewrite ntl_free_varset_insert_sum.
  rewrite ntl_free_varset_relabel_ntl.
  rewrite ntl_varset_decomp.
  apply leibniz_equiv_iff.
  rewrite set_omap_union, set_omap_set_map.
  unfold compose at 1 2.
  cbn -[union].
  rewrite set_omap_None, (union_empty_l _).
  rewrite set_omap_set_map.
  unfold compose; cbn -[union].
  remember (ntl_free_varset ntl) as vs eqn:Hvs.
  clear Hvs.
  set_unfold.
  intros k.
  split.
  - intros (j & Hj & Hjvs).
    case_decide; [done|].
    revert Hj.
    cbn.
    intros [= <-].
    done.
  - intros (Hkvs & Hk).
    exists k.
    now rewrite decide_False by done.
Qed.


Lemma ntl_bound_varset_add_loop_ntl_alt_as l r x ntl :
  ntl_bound_varset (add_loop_ntl_alt_as l r x ntl) ⊆
  ntl_bound_varset ntl ∪ {[x]}.
Proof.
  unfold add_loop_ntl_alt_as.
  rewrite ntl_bound_varset_insert_sum.
  rewrite ntl_bound_varset_relabel_ntl.
  rewrite ntl_varset_decomp.
  rewrite set_omap_union, set_omap_set_map.
  unfold compose at 1 2.
  cbn -[union].
  rewrite set_omap_Some, set_map_id.
  apply union_mono_l.
  rewrite set_omap_set_map.
  unfold compose; cbn -[union].

  remember (ntl_free_varset ntl) as vs eqn:Hvs.
  clear Hvs.
  set_unfold.
  intros k (? & Hk & _).
  case_decide; [|done].
  cbn in Hk.
  congruence.
Qed.


Lemma WT_ntl_mono tl tl' ntl : tl ⊆ tl' ->
  WT_ntl tl ntl -> WT_ntl tl' ntl.
Proof.
  intros Htl.
  rewrite 2 WT_ntl_alt_varset.
  intros [].
  now split; [rewrite <- Htl|].
Qed.

Lemma WF_ntl_alt_varset ntl :
  WF_ntl ntl <-> NoDup ntl.(ntl_sums) /\ ntl_bound_varset ntl ⊆ list_to_set ntl.(ntl_sums).
Proof.
  unfold WF_ntl, ntl_bound_varset.
  rewrite union_subseteq.
  tauto.
Qed.

Lemma add_loop_ntl_alt_as_WF ntl i o x : x ∉ ntl.(ntl_sums) ->
  WF_ntl ntl -> WF_ntl (add_loop_ntl_alt_as i o x ntl).
Proof.
  intros Hx.
  rewrite 2 WF_ntl_alt_varset.
  intros [Hdup Hsub].
  split.
  - cbn.
    now apply NoDup_cons.
  - rewrite ntl_bound_varset_add_loop_ntl_alt_as.
    cbn -[union].
    set_solver +Hsub.
Qed.

Lemma add_loop_ntl_alt_as_WT tl ntl i o x : x ∉ ntl.(ntl_sums) ->
  WT_ntl tl ntl -> WT_ntl (tl ∖ {[i;o]}) (add_loop_ntl_alt_as i o x ntl).
Proof.
  intros Hx.
  rewrite 2 WT_ntl_alt_varset.
  rewrite ntl_free_varset_add_loop_ntl_alt_as.
  intros [Hsub Hwf].
  split; [|now apply add_loop_ntl_alt_as_WF].
  now apply difference_mono_r.
Qed.

Lemma add_loop_ntl_alt_WF ntl i o :
  WF_ntl ntl ->
  WF_ntl (add_loop_ntl_alt i o ntl).
Proof.
  apply add_loop_ntl_alt_as_WF, infinite_is_fresh.
Qed.

Lemma add_loop_ntl_alt_WT tl ntl i o :
  WT_ntl tl ntl ->
  WT_ntl (tl ∖ {[i;o]}) (add_loop_ntl_alt i o ntl).
Proof.
  apply add_loop_ntl_alt_as_WT, infinite_is_fresh.
Qed.

Lemma WT_add_top_loop_contl {n m} (contl : CospanNamedTensorList (S n) (S m)) :
  WT_contl contl -> WT_contl (add_top_loop_contl contl).
Proof.
  destruct contl as [ntl ins outs].
  induction ins as [i ins] using vec_S_inv.
  induction outs as [o outs] using vec_S_inv.
  cbn.
  unfold add_top_loop_contl; cbn.
  intros HWT%(add_loop_ntl_alt_WT _ _ i o).
  cbn -[union] in HWT.
  eapply WT_ntl_mono; [|apply HWT].
  cbn -[union].
  set_solver +.
Qed.



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


Context `{SA : Summable A, AEQ : EqDecision A, WFA : !WFSummable A}.



Lemma ntl_total_semantics_add_loop_ntl_alt_as mabs ml i o x ntl :
  WF_ntl ntl ->
  (* i ∈ dom ml -> o ∈ dom ml ->  *)x ∉ ntl.(ntl_sums) ->
  ntl_total_semantics mabs ml (add_loop_ntl_alt_as i o x ntl) ==
  ∑ a : A,
  ntl_total_semantics mabs (<[i := a]> (<[o := a]> ml)) ntl.
Proof.
  intros Hntl (* Hi Ho *) Hx.
  rewrite ntl_total_semantics_alt by
    now apply add_loop_ntl_alt_as_WF; try apply Hntl.
  cbn -[abstracts_semantics_alt deltas_semantics_alt ntl_abstracts ntl_deltas].
  rewrite sum_of_Vmap_cons'.
  apply sum_of_ext; intros a.
  rewrite ntl_total_semantics_alt by apply Hntl.
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  f_equiv.
  - apply eq_reflexivity, abstracts_semantics_alt_ext.
    apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall; intros [[f low] up] Hflu.
    cbn.
    split; [done|].
    split.
    + rewrite <- list_fmap_compose.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      cbn.
      destruct v as [r|l].
      * cbn.
        unfold Vmap;
        apply lookup_insert_ne.
        intros ->.
        apply Hx.
        apply (elem_of_list_to_set (C:=Pset)), Hntl.2.1.
        rewrite elem_of_abstracts_bound_vars.
        set_solver + Hflu Hv.
      * cbn.
        case_decide as Hl_io.
        --cbn.
          unfold Vmap.
          rewrite lookup_insert.
          symmetry.
          rewrite 2 lookup_insert_case.
          do 2 (case_decide; [done|]).
          now destruct Hl_io as [-> | ->].
        --cbn.
          unfold Vmap.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; left.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; right.
          done.
    + rewrite <- list_fmap_compose.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      cbn.
      destruct v as [r|l].
      * cbn.
        unfold Vmap;
        apply lookup_insert_ne.
        intros ->.
        apply Hx.
        apply (elem_of_list_to_set (C:=Pset)), Hntl.2.1.
        rewrite elem_of_abstracts_bound_vars.
        set_solver + Hflu Hv.
      * cbn.
        case_decide as Hl_io.
        --cbn.
          unfold Vmap.
          rewrite lookup_insert.
          symmetry.
          rewrite 2 lookup_insert_case.
          do 2 (case_decide; [done|]).
          now destruct Hl_io as [-> | ->].
        --cbn.
          unfold Vmap.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; left.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; right.
          done.
  - apply eq_reflexivity, deltas_semantics_alt_ext.
    apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall; intros [l u] Hflu.
    cbn.
    split.
    + rename l into v.
      destruct v as [r|l].
      * cbn.
        unfold Vmap;
        apply lookup_insert_ne.
        intros ->.
        apply Hx.
        apply (elem_of_list_to_set (C:=Pset)), Hntl.2.2.
        rewrite elem_of_deltas_bound_vars.
        set_solver + Hflu.
      * cbn.
        case_decide as Hl_io.
        --cbn.
          unfold Vmap.
          rewrite lookup_insert.
          symmetry.
          rewrite 2 lookup_insert_case.
          do 2 (case_decide; [done|]).
          now destruct Hl_io as [-> | ->].
        --cbn.
          unfold Vmap.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; left.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; right.
          done.
    + rename u into v.
      rename l into l'.
      destruct v as [r|l].
      * cbn.
        unfold Vmap;
        apply lookup_insert_ne.
        intros ->.
        apply Hx.
        apply (elem_of_list_to_set (C:=Pset)), Hntl.2.2.
        rewrite elem_of_deltas_bound_vars.
        set_solver + Hflu.
      * cbn.
        case_decide as Hl_io.
        --cbn.
          unfold Vmap.
          rewrite lookup_insert.
          symmetry.
          rewrite 2 lookup_insert_case.
          do 2 (case_decide; [done|]).
          now destruct Hl_io as [-> | ->].
        --cbn.
          unfold Vmap.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; left.
          rewrite lookup_insert_ne by now intros ->; apply Hl_io; right.
          done.
Qed.


Lemma ntl_total_semantics_add_loop_ntl_alt mabs ml i o ntl :
  WF_ntl ntl ->
  ntl_total_semantics mabs ml (add_loop_ntl_alt i o ntl) ==
  ∑ a : A,
  ntl_total_semantics mabs (<[i := a]> (<[o := a]> ml)) ntl.
Proof.
  intros HWF.
  now apply ntl_total_semantics_add_loop_ntl_alt_as, infinite_is_fresh.
Qed.





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

#[global] Arguments cote_semantics _ {_ _} _ _ _ / : assert.
#[global] Arguments cotl_semantics _ {_ _} _ _ _ / : assert.
#[global] Arguments contl_semantics _ {_ _} _ _ _ / : assert.


Lemma contl_semantics_WT_alt {n m} (contl : CospanNamedTensorList n m) (v w : vec A _) :
  WT_contl contl ->
  WT_ntl (dom (make_vecs_map contl.(contl_inputs) contl.(contl_outputs) v w))
    contl.(contl_expr).
Proof.
  now rewrite dom_make_vecs_map.
Qed.

Definition relabel_tl_free (f : positive -> positive) (tl : tensorlist) : tensorlist :=
  mk_tl tl.(tl_sums) (relabel_abs (relabel_frees f) <$> tl.(tl_abstracts))
    (relabel_delt (relabel_frees f) <$> tl.(tl_deltas)).

Lemma relabel_tl_free_semantics_aux_kmap f `{Hf : !Inj eq eq f}
  mabs ml mr sums abs delt :
  tl_total_semantics_aux mabs (kmap f ml) mr sums
    (relabel_abs (relabel_frees f) <$> abs)
    (relabel_delt (relabel_frees f) <$> delt) ==
  tl_total_semantics_aux mabs ml mr sums abs delt.
Proof.
  revert mr; induction sums; intros mr;
    [|cbn; apply sum_of_ext; intros x; apply IHsums].
  apply tl_total_semantics_aux_ext_base; apply Forall2_fmap_l, Forall_Forall2_diag;
  rewrite Forall_forall.
  - intros [[idx low] up] _.
    cbn.
    split; [done|].
    split; apply Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall; (intros [|] _; [done|]; cbn; apply (lookup_kmap _)).
  - intros [l u] _.
    cbn.
    split; [destruct l|destruct u]; try done; apply (lookup_kmap _).
Qed.


Lemma relabel_tl_free_semantics_kmap f `{Hf : !Inj eq eq f} mabs ml tl :
  tl_total_semantics mabs (kmap f ml) (relabel_tl_free f tl) ==
  tl_total_semantics mabs ml tl.
Proof.
  apply (relabel_tl_free_semantics_aux_kmap _).
Qed.

Lemma ntl2tl_ntl_relabel_free f ntl :
  ntl2tl (ntl_relabel_free f ntl) = relabel_tl_free f (ntl2tl ntl).
Proof.
  destruct ntl as [isums abs delt];
  apply tl_ext; cbn.
  - done.
  - rewrite <- 2 list_fmap_compose.
    apply list_fmap_ext.
    intros _ flu _.
    cbn.
    rewrite 2 relabel_abs_compose.
    now apply relabel_abs_ext; intros [].
  - rewrite <- 2 list_fmap_compose.
    apply list_fmap_ext.
    intros _ [[] []] _; done.
Qed.

Lemma ntl_relabel_free_semantics_kmap mabs ml f `{Hf : !Inj eq eq f} ntl :
  ntl_total_semantics mabs (kmap f ml) (ntl_relabel_free f ntl) ==
  ntl_total_semantics mabs ml ntl.
Proof.
  unfold ntl_total_semantics.
  rewrite ntl2tl_ntl_relabel_free.
  apply (relabel_tl_free_semantics_kmap _).
Qed.




Lemma contl_semantics_relabel_contl_free mabs f `{Hf : !Inj eq eq f} {n m}
  (contl : CospanNamedTensorList n m) : WT_contl contl ->
  contl_semantics mabs (relabel_contl_free f contl) ≡ contl_semantics mabs contl.
Proof.
  intros Hwf v w Hv Hw.
  unfold contl_semantics.
  cbn -[ntl_total_semantics].
  rewrite <- (ntl_relabel_free_semantics_kmap _ _ f contl).
  f_equiv.
  unfold make_vecs_map.
  rewrite <- 2 list_to_map_app.
  symmetry.
  rewrite (kmap_list_to_map _).
  now rewrite fmap_app, 4 vec_to_list_zip_with,
    2 vec_to_list_map, <- 2 zip_fmap_l.
Qed.

Lemma contl_interface_eq_correct
  `{!WFSummable A} (mabs : abscontext) {n m}
  (contl contl' : CospanNamedTensorList n m) :
  WT_contl contl ->
  contl_interface_eq contl contl' ->
  contl_semantics mabs contl ≡ contl_semantics mabs contl'.
Proof.
  intros HWT Heq.
  apply contl_interface_eq_iff_exists in Heq as (f & Hf & <-).
  now rewrite (contl_semantics_relabel_contl_free _ _).
Qed.


Lemma contl_eq_step_correct `{!WFSummable A} (mabs : abscontext) {n m}
  (contl contl' : CospanNamedTensorList n m) :
  WT_contl contl ->
  contl_eq_step contl contl' ->
  contl_semantics mabs contl ≡ contl_semantics mabs contl'.
Proof.
  intros HWT Heq.
  induction Heq.
  - intros v w Hv Hw.
    unfold contl_semantics; cbn -[make_vecs_map].
    apply ntl_eq_correct;
    [now apply make_vecs_map_SummedElements|
    rewrite dom_make_vecs_map; easy..].
  - now apply contl_interface_eq_correct.
Qed.

Lemma contl_eq_correct `{!WFSummable A} (mabs : abscontext) {n m}
  (contl contl' : CospanNamedTensorList n m) :
  WT_contl contl ->
  contl_eq contl contl' ->
  contl_semantics mabs contl ≡ contl_semantics mabs contl'.
Proof.
  intros HWF Heq.
  induction Heq as [|contl contl' contl'' Hstep Hsteps IHeq]; [done|].
  rewrite <- IHeq by now rewrite (contl_eq_step_WT _ _ Hstep) in HWF.
  now apply contl_eq_step_correct.
Qed.



Lemma contl_semantics_add_top_loop_gen mabs
  {n m} (contl : CospanNamedTensorList (S n) (S m)) :
  WF_ntl contl ->
  vhd contl.(contl_outputs) ∉@{list _} vtl contl.(contl_inputs) ->
  contl_semantics mabs (add_top_loop_contl contl) ≡
  join_stack_1_tl_tr (contl_semantics mabs contl).
Proof.
  destruct contl as [ntl ins outs].
  induction ins as [i ins] using vec_S_inv.
  induction outs as [o outs] using vec_S_inv.
  unfold add_top_loop_contl; cbn.
  intros Hwf Ho_ins.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics].
  unfold contl_semantics;
  cbn -[ntl_total_semantics make_vecs_map].
  rewrite ntl_total_semantics_add_loop_ntl_alt by easy.
  apply sum_of_ext; intros a.
  f_equiv.
  cbn.
  unfold make_vecs_map.
  rewrite <- insert_union_l, <- insert_union_r, <- list_to_map_app; [done|].
  apply not_elem_of_dom.
  rewrite dom_list_to_map.
  now rewrite vec_to_list_zip_with, fst_zip, elem_of_list_to_set
    by now rewrite 2 length_vec_to_list.
Qed.

Definition contl_boundary {n m} (contl : CospanNamedTensorList n m) : Pset :=
  list_to_set (contl.(contl_inputs) ++ contl.(contl_outputs)).

Lemma contl_semantics_swapped_stack_aux mabs {n m n' m'}
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList n' m') :
  WF_ntl contl -> WF_ntl contl' ->
  ntl_free_varset contl ## contl_boundary contl' ->
  ntl_free_varset contl' ## contl_boundary contl ->
  (* vhd contl.(contl_outputs) ∉@{list _} vtl contl.(contl_inputs) -> *)
  contl_semantics mabs (swapped_stack_contl_aux contl contl') ≡
  swapped_stack_tensor (contl_semantics mabs contl)
    (contl_semantics mabs contl').
Proof.
  intros Hwf Hwf' Hdisj Hdisj' v w Hv Hw.
  unfold contl_semantics;
  cbn -[ntl_total_semantics ntl_times].
  induction v as [vl vr] using vec_add_inv.
  induction w as [wl wr] using vec_add_inv.
  rewrite 2 vsplitl_app, 2 vsplitr_app, 2 vzip_with_app,
    2 vec_to_list_app, 2 list_to_map_app.
  (* rewrite 4 vzip_map_l, 4 vec_to_list_map.
  rewrite <- 4 (kmap_list_to_map (M1:=Pmap) _). *)

  rewrite ntl_total_semantics_ntl_times by easy.

  f_equiv.
  - apply ntl_total_semantics_free_varset_ext.
    intros l Hl.
    apply Hdisj in Hl as Hl'.
    change (l ∉ contl_boundary contl') in Hl'.
    unfold contl_boundary in Hl'.
    rewrite list_to_set_app, not_elem_of_union in Hl'.
    rewrite 3 lookup_union.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite (not_elem_of_dom _ _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    rewrite (left_id None _).
    f_equal.
    rewrite (not_elem_of_dom (list_to_map (vzip _ wr)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    apply (right_id _ _).
  - apply ntl_total_semantics_free_varset_ext.
    intros l Hl.
    apply Hdisj' in Hl as Hl'.
    change (l ∉ contl_boundary contl) in Hl'.
    unfold contl_boundary in Hl'.
    rewrite list_to_set_app, not_elem_of_union in Hl'.
    rewrite 3 lookup_union.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite (not_elem_of_dom (list_to_map (vzip _ vr)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    rewrite (not_elem_of_dom (list_to_map (vzip _ wl)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    now rewrite (left_id None _), (right_id None _).
Qed.

Lemma contl_boundary_relabel_contl_free f {n m} 
  (contl : CospanNamedTensorList n m) : 
  contl_boundary (relabel_contl_free f contl) =
  set_map f (contl_boundary contl).
Proof.
  unfold contl_boundary; cbn.
  now rewrite 2 vec_to_list_map, set_map_list_to_set_L, fmap_app.
Qed.

Lemma contl_semantics_swapped_stack mabs {n m n' m'}
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList n' m') :
  WT_contl contl -> WT_contl contl' ->
  (* vhd contl.(contl_outputs) ∉@{list _} vtl contl.(contl_inputs) -> *)
  contl_semantics mabs (swapped_stack_contl contl contl') ≡
  swapped_stack_tensor (contl_semantics mabs contl)
    (contl_semantics mabs contl').
Proof.
  intros Hwf Hwf'.
  unfold swapped_stack_contl.
  rewrite contl_semantics_swapped_stack_aux by first [
    now apply ntl_relabel_free_WF; apply Hwf || apply Hwf'|
    rewrite contl_boundary_relabel_contl_free; cbn; 
    rewrite ntl_free_varset_ntl_relabel_free;
    intros ? []%elem_of_map []%elem_of_map; lia].
  now apply swapped_stack_tensor_mor; 
  apply (contl_semantics_relabel_contl_free _ _).
Qed.


Lemma contl_semantics_stack_aux mabs {n m n' m'}
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList n' m') :
  WF_ntl contl -> WF_ntl contl' ->
  ntl_free_varset contl ## contl_boundary contl' ->
  ntl_free_varset contl' ## contl_boundary contl ->
  contl_semantics mabs (stack_contl_aux contl contl') ≡
  stack_tensor (contl_semantics mabs contl)
    (contl_semantics mabs contl').
Proof.
  intros Hwf Hwf' Hdisj Hdisj' v w Hv Hw.
  unfold contl_semantics;
  cbn -[ntl_total_semantics ntl_times].
  induction v as [vl vr] using vec_add_inv.
  induction w as [wl wr] using vec_add_inv.
  rewrite 2 vsplitl_app, 2 vsplitr_app, 2 vzip_with_app,
    2 vec_to_list_app, 2 list_to_map_app.
  (* rewrite 4 vzip_map_l, 4 vec_to_list_map.
  rewrite <- 4 (kmap_list_to_map (M1:=Pmap) _). *)

  rewrite ntl_total_semantics_ntl_times by easy.

  f_equiv.
  - apply ntl_total_semantics_free_varset_ext.
    intros l Hl.
    apply Hdisj in Hl as Hl'.
    change (l ∉ contl_boundary contl') in Hl'.
    unfold contl_boundary in Hl'.
    rewrite list_to_set_app, not_elem_of_union in Hl'.
    rewrite 3 lookup_union.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite (not_elem_of_dom (list_to_map (vzip _ vr)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    rewrite (right_id_L None _).
    f_equal.
    rewrite (not_elem_of_dom (list_to_map (vzip _ wr)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    apply (right_id_L _ _).
  - apply ntl_total_semantics_free_varset_ext.
    intros l Hl.
    apply Hdisj' in Hl as Hl'.
    change (l ∉ contl_boundary contl) in Hl'.
    unfold contl_boundary in Hl'.
    rewrite list_to_set_app, not_elem_of_union in Hl'.
    rewrite 3 lookup_union.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite (not_elem_of_dom (list_to_map (vzip _ vl)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    rewrite (not_elem_of_dom (list_to_map (vzip _ wl)) _).1 by now
      rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip by 
        now rewrite 2 length_vec_to_list.
    now rewrite 2 (left_id_L None _).
Qed.

Lemma contl_semantics_stack mabs {n m n' m'}
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList n' m') :
  WT_contl contl -> WT_contl contl' ->
  (* vhd contl.(contl_outputs) ∉@{list _} vtl contl.(contl_inputs) -> *)
  contl_semantics mabs (stack_contl contl contl') ≡
  stack_tensor (contl_semantics mabs contl)
    (contl_semantics mabs contl').
Proof.
  intros Hwf Hwf'.
  unfold stack_contl.
  rewrite contl_semantics_stack_aux by first [
    now apply ntl_relabel_free_WF; apply Hwf || apply Hwf'|
    rewrite contl_boundary_relabel_contl_free; cbn; 
    rewrite ntl_free_varset_ntl_relabel_free;
    intros ? []%elem_of_map []%elem_of_map; lia].
  now apply stack_tensor_mor; 
  apply (contl_semantics_relabel_contl_free _ _).
Qed.


End Semantics.


