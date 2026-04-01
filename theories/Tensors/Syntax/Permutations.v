From TensorRocq Require Import Summable Syntax.Cospans.
(* Require StringCustomNotation. *)

Require Import SetoidList SetoidPermutation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

From TensorRocq Require Import Aux_stdpp Aux_pos.

#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.

Local Open Scope positive_scope.
Local Open Scope list_scope.

From TensorRocq Require Export Syntax.Definitions.

Section abs_strongperm_eq.

Context {A B : Type}.

Definition abs_strongperm_eq : relation (A * list B * list B) :=
  fun flu flu' =>
  flu.1.1 = flu'.1.1 /\
  flu.1.2 ++ flu.2 ≡ₚ flu'.1.2 ++ flu'.2.

Lemma abs_strongperm_eq_refl flu : abs_strongperm_eq flu flu.
Proof.
  easy.
Qed.

Lemma abs_strongperm_eq_symm flu flu' :
  abs_strongperm_eq flu flu' -> abs_strongperm_eq flu' flu.
Proof.
  intros []; split; now symmetry.
Qed.

Lemma abs_strongperm_eq_trans flu flu' flu'' :
  abs_strongperm_eq flu flu' -> abs_strongperm_eq flu' flu'' ->
  abs_strongperm_eq flu flu''.
Proof.
  intros [] []; split; etransitivity; eauto.
Qed.

End abs_strongperm_eq.

Add Parametric Relation {A B} : (A * list B * list B) (@abs_strongperm_eq A B)
  reflexivity proved by abs_strongperm_eq_refl
  symmetry proved by abs_strongperm_eq_symm
  transitivity proved by abs_strongperm_eq_trans
    as abs_strongperm_eq_setoid.


Definition ntl_strongperm_eq (ntl ntl' : namedtensorlist) :=
  ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\
  PermutationA abs_strongperm_eq ntl.(ntl_abstracts) ntl'.(ntl_abstracts) /\
  PermutationA prod_swap_eq ntl.(ntl_deltas) ntl'.(ntl_deltas).

Lemma ntl_strongperm_eq_refl ntl :
  ntl_strongperm_eq ntl ntl.
Proof.
  easy.
Qed.

Lemma ntl_strongperm_eq_symm ntl ntl' :
  ntl_strongperm_eq ntl ntl' -> ntl_strongperm_eq ntl' ntl.
Proof.
  intros (?&?&?); split; [|split]; now symmetry.
Qed.

Lemma ntl_strongperm_eq_trans ntl ntl' ntl'' :
  ntl_strongperm_eq ntl ntl' -> ntl_strongperm_eq ntl' ntl'' ->
  ntl_strongperm_eq ntl ntl''.
Proof.
  intros (?&?&?) (?&?&?); split; [|split]; now etransitivity; eauto.
Qed.


Add Parametric Relation : namedtensorlist ntl_strongperm_eq
  reflexivity proved by ntl_strongperm_eq_refl
  symmetry proved by ntl_strongperm_eq_symm
  transitivity proved by ntl_strongperm_eq_trans
    as ntl_strongperm_eq_setoid.




Lemma deltas_vars_permA_mor :
  Proper (PermutationA prod_swap_eq ==> eq) deltas_vars.
Proof.
  intros delt delt' Hdelt.
  induction Hdelt as [|x y delt delt' Hx Hdelt| |];
    [reflexivity| |set_solver|etransitivity; eassumption].
  rewrite 2 deltas_vars_cons.
  f_equiv; [|easy].
  destruct Hx as [<- | <-]; [done|].
  unfold_leibniz.
  apply list_to_set_perm.
  destruct x as []; cbn; solve_Permutation.
Qed.


Lemma abstracts_vars_cons flu abs :
  abstracts_vars (flu :: abs) =
  list_to_set (flu.1.2 ++ flu.2) ∪ abstracts_vars abs.
Proof.
  unfold abstracts_vars.
  cbn.
  destruct flu as [[]]; cbn.
  apply list_to_set_app_L.
Qed.

Lemma abstracts_vars_permA_mor :
  Proper (PermutationA abs_strongperm_eq ==> eq) abstracts_vars.
Proof.
  intros delt delt' Hdelt.
  induction Hdelt as [|x y delt delt' Hx Hdelt| |];
    [reflexivity| |set_solver|etransitivity; eassumption].
  rewrite 2 abstracts_vars_cons.
  f_equiv; [|easy].
  apply list_to_set_perm_L, Hx.
Qed.

Lemma abstracts_bound_vars_permA_mor :
  Proper (PermutationA abs_strongperm_eq ==> eq) abstracts_bound_vars.
Proof.
  intros delt delt' Hdelt.
  rewrite <- 2 set_omap_v2bound_abstracts_vars.
  f_equal.
  now apply abstracts_vars_permA_mor.
Qed.

Lemma abstracts_free_vars_permA_mor :
  Proper (PermutationA abs_strongperm_eq ==> eq) abstracts_free_vars.
Proof.
  intros delt delt' Hdelt.
  rewrite <- 2 set_omap_v2free_abstracts_vars.
  f_equal.
  now apply abstracts_vars_permA_mor.
Qed.

Lemma ntl_varset_ntl_strongperm_eq ntl ntl' :
  ntl_strongperm_eq ntl ntl' ->
  ntl_varset ntl = ntl_varset ntl'.
Proof.
  unfold ntl_varset.
  intros (_ & Habs & Hdelt).
  f_equal.
  - now apply abstracts_vars_permA_mor.
  - now apply deltas_vars_permA_mor.
Qed.

Lemma ntl_free_varset_ntl_strongperm_eq ntl ntl' :
  ntl_strongperm_eq ntl ntl' ->
  ntl_free_varset ntl = ntl_free_varset ntl'.
Proof.
  unfold ntl_free_varset.
  intros (_ & Habs & Hdelt).
  f_equal.
  - now apply abstracts_free_vars_permA_mor.
  - now apply deltas_free_vars_permA_mor.
Qed.

Lemma ntl_bound_varset_ntl_strongperm_eq ntl ntl' :
  ntl_strongperm_eq ntl ntl' ->
  ntl_bound_varset ntl = ntl_bound_varset ntl'.
Proof.
  unfold ntl_bound_varset.
  intros (_ & Habs & Hdelt).
  f_equal.
  - now apply abstracts_bound_vars_permA_mor.
  - now apply deltas_bound_vars_permA_mor.
Qed.

Lemma ntl_strongperm_eq_WF ntl ntl' :
  ntl_strongperm_eq ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  rewrite 2 WF_ntl_alt_varset.
  intros Heq.
  apply ntl_bound_varset_ntl_strongperm_eq in Heq as Hvars.
  rewrite <- Hvars.
  rewrite <- Heq.1.
  done.
Qed.

Lemma ntl_strongperm_eq_WT tl ntl ntl' :
  ntl_strongperm_eq ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  rewrite 2 WT_ntl_alt_varset.
  intros Heq.
  f_equiv; [|now apply ntl_strongperm_eq_WF].
  now apply ntl_free_varset_ntl_strongperm_eq in Heq as <-.
Qed.


Definition abstracts_indices {A} (abs : list (Idx * list A * list A)) : Pset :=
  list_to_set ((fst ∘ fst) <$> abs).

Lemma abstracts_indices_ntl2tl ntl :
  abstracts_indices (ntl2tl ntl).(tl_abstracts) =
  abstracts_indices ntl.(ntl_abstracts).
Proof.
  destruct ntl as [isums abs].
  cbn.
  rewrite <- list_fmap_compose.
  f_equal.
  apply list_fmap_ext; now intros _ [[]] _.
Qed.

Lemma abstracts_indices_relabel_abs `(f : A -> B) abs :
  abstracts_indices (relabel_abs f <$> abs) = abstracts_indices abs.
Proof.
  unfold abstracts_indices.
  rewrite <- list_fmap_compose.
  f_equal.
  now apply list_fmap_ext; intros _ [[]] _.
Qed.

Lemma abstracts_indices_ntl_aeq ntl ntl' :
  ntl =ntl= ntl' ->
  abstracts_indices ntl.(ntl_abstracts) =
  abstracts_indices ntl'.(ntl_abstracts).
Proof.
  intros (f & _ & _ & Habs & Hdelt).
  unfold abstracts_indices.
  rewrite <- Habs.
  symmetry.
  apply abstracts_indices_relabel_abs.
Qed.

Lemma abstracts_indices_relabel_absidx f ntl :
  abstracts_indices (ntl_relabel_absidx f ntl).(ntl_abstracts) =
  set_map f (abstracts_indices ntl.(ntl_abstracts)).
Proof.
  unfold abstracts_indices.
  cbn.
  rewrite <- list_fmap_compose.
  unfold compose, prod_map; cbn.
  rewrite set_map_list_to_set_L.
  rewrite <- list_fmap_compose.
  done.
Qed.

Lemma abstracts_indices_permA_mor {A} abs abs' :
  PermutationA abs_strongperm_eq abs abs' ->
  @abstracts_indices A abs = abstracts_indices abs'.
Proof.
  intros Hperm.
  induction Hperm as [|x y delt delt' Hx Hdelt| |];
    [reflexivity| |set_solver|etransitivity; eassumption].
  cbn -[union].
  f_equiv; [|easy].
  now rewrite Hx.1.
Qed.

Section ntl_strongperm_eq_corr.

Local Open Scope nat_scope.

Import Tensor.

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


Lemma tl_total_semantics_aux_absidxs_ext
  mabs mabs' ml mr sums abs delt :
  (forall i, i ∈ abstracts_indices abs -> mabs !! i = mabs' !! i) ->
  req (tl_total_semantics_aux (SR:=SR) mabs ml mr sums abs delt)
    (tl_total_semantics_aux mabs' ml mr sums abs delt).
Proof.
  intros Habs.
  revert mr;
  induction sums; intros mr;
  [|cbn; apply sum_of_ext; intros ?; apply IHsums].
  apply tl_total_semantics_aux_ext_base; apply Forall_Forall2_diag;
  rewrite Forall_forall.
  - intros [[f low] up] Hflu.
    split; [|split; apply Forall_Forall2_diag;
      rewrite Forall_forall; intros; reflexivity].
    cbn.
    apply Habs.
    set_unfold.
    now exists (f, low, up).
  - easy.
Qed.

Lemma ntl_total_semantics_absidxs_ext
  mabs mabs' ml ntl :
  (forall i, i ∈ abstracts_indices ntl.(ntl_abstracts) -> mabs !! i = mabs' !! i) ->
  req (ntl_total_semantics (SR:=SR) mabs ml ntl)
    (ntl_total_semantics mabs' ml ntl).
Proof.
  intros Habs.
  apply tl_total_semantics_aux_absidxs_ext.
  destruct ntl as [isums abs delt].
  rewrite abstracts_indices_ntl2tl.
  apply Habs.
Qed.


Lemma ntl_total_semantics_relabel_free
  f `{Hf : !Inj eq eq f} mabs ml ntl :
  req (ntl_total_semantics (SR:=SR) mabs (kmap f ml) (ntl_relabel_free f ntl))
    (ntl_total_semantics mabs ml ntl).
Proof.
  unfold ntl_total_semantics.
  rewrite ntl2tl_ntl_relabel_free.
  apply (relabel_tl_free_semantics_aux_kmap _).
Qed.

Lemma abstracts_semantics_alt_cons mabs ml mr flu abs :
  abstracts_semantics_alt mabs ml mr (flu :: abs) =
  abstract_semantics_alt (rO:=rO) mabs ml mr flu.1.1 flu.1.2 flu.2 *
  abstracts_semantics_alt (A:=A) mabs ml mr abs.
Proof.
  now destruct flu as [[]].
Qed.

Lemma deltas_semantics_alt_cons ml mr lu delt :
  deltas_semantics_alt ml mr (lu :: delt) =
  delta_semantics_alt (rO:=rO) ml mr lu.1 lu.2 *
  deltas_semantics_alt (A:=A) ml mr delt.
Proof.
  now destruct lu as [].
Qed.

Lemma abstract_semantics_alt_to_app mabs ml mr f low up :
  abstract_semantics_alt (rO:=rO) (A:=A) mabs ml mr f low up =
  default 0 (lrargs ← join_list (get_var_alt ml mr <$> (low ++ up));
    dt ← mabs !! f;
    Some $ Vapplys dt (take (length low) lrargs) (drop (length low) lrargs)).
Proof.
  unfold abstract_semantics_alt.
  rewrite fmap_app, join_list_app, option_bind_assoc'.
  destruct (join_list (_ <$> low)) as [largs|] eqn:Hlargs; [cbn|done].
  rewrite option_fmap_bind; unfold compose; cbn.
  destruct (join_list (_ <$> up)) as [uargs|] eqn:Huargs; [cbn|done].
  destruct (mabs !! f) as [dt|]; [cbn|done].
  apply join_list_Some_length in Hlargs.
  rewrite length_fmap in Hlargs.
  f_equal; symmetry;
  [etransitivity; [|apply take_app_length]|
   etransitivity; [|apply drop_app_length]]; now f_equal.
Qed.

Lemma deltas_semantics_alt_permA ml mr (delt delt' : list (var * var)) : 
  PermutationA prod_swap_eq delt delt' ->
  deltas_semantics_alt ml mr delt == deltas_semantics_alt (A:=A) ml mr delt'.
Proof.
  intros Hdelt.
  unfold deltas_semantics_alt.
  apply Rlist_prod_perm_mor.
  induction Hdelt as [|? ? ? ? Heq | |].
  - done.
  - cbn.
    f_equiv; [|easy].
    do 2 case_match.
    rewrite prod_swap_eq_pair in Heq.
    destruct Heq as [[-> ->]|[-> ->]]; [done|].
    apply eq_reflexivity, delta_semantics_alt_comm.
  - apply (Permutation_PermutationA _).
    solve_Permutation.
  - now etransitivity; eassumption.
Qed.

End ntl_strongperm_eq_corr.
