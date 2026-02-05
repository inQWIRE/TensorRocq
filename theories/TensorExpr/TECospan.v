Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp Aux_pos.

Require Export TESyntax.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.

Lemma delete_list_to_map `{FinMap K M} {A}
  (l : list (K * A)) k :
  delete k (list_to_map l :> M A) =
  list_to_map (filter (λ ka, ka.1 ≠ k) l).
Proof.
  induction l; [apply delete_empty|].
  cbn.
  case_decide as Hak.
  - cbn.
    setoid_rewrite <- IHl.
    now apply delete_insert_ne.
  - rewrite Hak.
    rewrite delete_insert_delete.
    apply IHl.
Qed.



Lemma kmap_list_to_map `{FinMap K1 M1, FinMap K2 M2} {A} f `{Hf : !Inj eq eq f}
  (l : list (K1 * A)) :
  kmap f (list_to_map l :> M1 A) =@{M2 A}
    list_to_map (fmap (prod_map f id) l).
Proof.
  unfold kmap.
  induction l as [l IHl] using (Nat.measure_induction _ length).
  destruct l; [cbn; now rewrite map_to_list_empty|].
  cbn.
  rewrite <- insert_delete_insert.
  erewrite list_to_map_proper.
  2: {
    rewrite fsts_prod_map.
    apply (NoDup_fmap _).
    apply NoDup_fst_map_to_list.
  }
  2:{
    rewrite map_to_list_insert by now rewrite lookup_delete.
    cbn.
    done.
  }
  cbn.
  symmetry.
  rewrite <- insert_delete_insert.
  change ((prod_map _ _ _).1) with (f p.1).
  rewrite delete_list_to_map.
  rewrite list_filter_fmap.
  unfold compose.
  rewrite delete_list_to_map.
  f_equal.
  rewrite IHl by now cbn; apply -> Nat.succ_le_mono; apply length_filter.
  f_equal.
  f_equal.
  apply list_filter_iff.
  intros []; cbn.
  split; [now intros ? ->|].
  now intros ? ->%(inj _).
Qed.


Definition make_vecs_map {A n m} (ins : vec Idx n) (outs : vec Idx m)
  (insv : vec A n) (outsv : vec A m) : Pmap A :=
  list_to_map (vzip ins insv ++ vzip outs outsv).


Lemma dom_make_vecs_map {A n m} (ins : vec _ n) (outs : vec _ m)
  (v w : vec A _) :
  dom (make_vecs_map ins outs v w) =
  list_to_set (ins ++ outs).
Proof.
  unfold_leibniz.
  unfold make_vecs_map.
  rewrite dom_list_to_map.
  rewrite fmap_app, 2 vec_to_list_zip_with.
  now rewrite 2 fst_zip by now rewrite 2 length_vec_to_list.
Qed.




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


Definition ntl_free_varset (ntl : namedtensorlist) : Pset :=
  abstracts_free_vars ntl.(ntl_abstracts) ∪
    deltas_free_vars ntl.(ntl_deltas).

Lemma relabel_ntl_free_ext_strong f g ntl :
  (forall i, i ∈ ntl_free_varset ntl -> f i = g i) ->
  relabel_ntl_free f ntl = relabel_ntl_free g ntl.
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

Lemma relabel_ntl_free_id ntl :
  relabel_ntl_free id ntl = ntl.
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

Lemma relabel_ntl_free_compose f g ntl :
  relabel_ntl_free g (relabel_ntl_free f ntl) =
  relabel_ntl_free (g ∘ f) ntl.
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
  - apply relabel_ntl_free_ext_strong.
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
  apply relabel_ntl_free_id.
Qed.

Lemma relabel_contl_free_compose f g {n m} (contl : CospanNamedTensorList n m) :
  relabel_contl_free g (relabel_contl_free f contl) =
  relabel_contl_free (g ∘ f) contl.
Proof.
  apply contl_ext; cbn; [|now rewrite Vector.map_map..].
  apply relabel_ntl_free_compose.
Qed.


Inductive contl_interface_eq {n m} : relation (CospanNamedTensorList n m) :=
  | interface_contl_eq_of_inj f `{Hf : !Inj eq eq f}
    (ins : vec _ n) (outs : vec _ m) ntl :
    contl_interface_eq (mk_contl ntl ins outs)
      (mk_contl (relabel_ntl_free f ntl) (vmap f ins) (vmap f outs)).


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

Lemma ntl_free_varset_relabel_ntl_free f ntl :
  ntl_free_varset (relabel_ntl_free f ntl) =
  set_map f (ntl_free_varset ntl).
Proof.
  destruct ntl as [isums abs delt].
  unfold ntl_free_varset; cbn [ntl_abstracts ntl_deltas relabel_ntl_free].
  rewrite abstracts_free_vars_relabel_frees,
    deltas_free_vars_relabel_frees.
  now rewrite set_map_union_L.
Qed.


Lemma fmap_elements `{FinSet A SA, FinSet B SB} (f : A -> B) `{!Inj eq eq f} (X : SA) :
  f <$> elements X ≡ₚ
  elements (set_map f X :> SB).
Proof.
  apply NoDup_Permutation;
  [apply (NoDup_fmap_2 _ _), NoDup_elements|apply NoDup_elements|].
  set_solver.
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
    rewrite ntl_free_varset_relabel_ntl_free.
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


Lemma relabel_ntl_free_WF f ntl :
  WF_ntl (relabel_ntl_free f ntl) <-> WF_ntl ntl.
Proof.
  unfold WF_ntl.
  cbn -[abstracts_bound_vars deltas_bound_vars].
  rewrite abstracts_bound_vars_relabel_frees,
    deltas_bound_vars_relabel_frees.
  done.
Qed.

Lemma relabel_ntl_free_WT tl f ntl :
  WT_ntl tl ntl -> WT_ntl (set_map f tl) (relabel_ntl_free f ntl).
Proof.
  unfold WT_ntl.
  rewrite relabel_ntl_free_WF.
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
  apply relabel_ntl_free_WT.
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


Require Export Tensor TESemantics.



Lemma make_vecs_map_SummedElements `{SA : Summable A} {n m}
  (ins : vec _ n) (outs : vec _ m) (v w : vec A _) :
  SummedElement v -> SummedElement w ->
  map_Forall (λ _ a, SummedElement a)
  (make_vecs_map ins outs v w).
Proof.
  intros Hv Hw.
  intros i a Hia%elem_of_list_to_map_2%(elem_of_list_fmap_1 snd).
  cbn in Hia.
  rewrite fmap_app, 2 vec_to_list_zip_with,
    2 snd_zip in Hia by now rewrite 2 length_vec_to_list.
  rewrite SummedElement_vec_iff in Hw.
  rewrite SummedElement_vec_iff in Hv.
  apply elem_of_app in Hia as []; auto.
Qed.


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

Lemma ntl2tl_relabel_ntl_free f ntl :
  ntl2tl (relabel_ntl_free f ntl) = relabel_tl_free f (ntl2tl ntl).
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

Lemma relabel_ntl_free_semantics_kmap mabs ml f `{Hf : !Inj eq eq f} ntl :
  ntl_total_semantics mabs (kmap f ml) (relabel_ntl_free f ntl) ==
  ntl_total_semantics mabs ml ntl.
Proof.
  unfold ntl_total_semantics.
  rewrite ntl2tl_relabel_ntl_free.
  apply (relabel_tl_free_semantics_kmap _).
Qed.




Lemma contl_semantics_relabel_contl_free mabs f `{Hf : !Inj eq eq f} {n m}
  (contl : CospanNamedTensorList n m) : WT_contl contl ->
  contl_semantics mabs (relabel_contl_free f contl) ≡ contl_semantics mabs contl.
Proof.
  intros Hwf v w Hv Hw.
  unfold contl_semantics.
  cbn -[ntl_total_semantics].
  rewrite <- (relabel_ntl_free_semantics_kmap _ _ f contl).
  f_equiv.
  unfold make_vecs_map.
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

End Semantics.


