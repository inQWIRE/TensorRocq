Require Import SetoidList SetoidPermutation.
From stdpp Require Import fin_maps.
Require Import TEPerm.
Require Export TensorGraph
  TensorGraphExpr GraphRewriting TensorGraphSemantics TensorGraphFacts.

Import GraphRewriting (compose).



(* The (strong) permutation relation on graphs, and its correctness *)

Definition hg_strongperm_eq {T n m} (cohg cohg' : CospanHyperGraph T n m) : Prop :=
  cohg.(inputs) = cohg'.(inputs) /\
  cohg.(outputs) = cohg'.(outputs) /\
  cohg.(hedges).(hypervertices) = cohg'.(hedges).(hypervertices) /\
  map_relation (λ _ tio tio', abs_strongperm_eq tio tio')
    (λ _ _, False) (λ _ _, False)
    cohg.(hedges).(hyperedges) cohg'.(hedges).(hyperedges).


Lemma hg_strongperm_eq_alt {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' ->
  cohg.(inputs) = cohg'.(inputs) /\
  cohg.(outputs) = cohg'.(outputs) /\
  vertices cohg = vertices cohg' /\
  map_relation (λ _ tio tio', abs_strongperm_eq tio tio')
    (λ _ _, False) (λ _ _, False)
    cohg.(hedges).(hyperedges) cohg'.(hedges).(hyperedges).
Proof.
  intros (Hins & Houts & Hverts & Hrel).
  split_and!; try done.
  unfold vertices.
  rewrite <- Hins, <- Houts.
  f_equal.
  unfold vertices_hg.
  rewrite <- Hverts.
  f_equal.
  apply map_relation_to_map_to_list in Hrel.
  apply list_to_set_perm_L.
  induction Hrel as [|x y l l' Hxy]; [done|].
  cbn.
  f_equiv; [|done].
  apply Hxy.2.
Qed.

Lemma hg_strongperm_eq_refl {T n m} (cohg : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg.
Proof.
  split_and!; [done..|].
  intros i.
  destruct (_ !! _); done.
Qed.

Lemma hg_strongperm_eq_symm {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' -> hg_strongperm_eq cohg' cohg.
Proof.
  intros (Hins & Houts & Hverts & Hrel).
  split_and!; [now symmetry..|].
  intros i.
  generalize (Hrel i).
  destruct (_ !! _), (_ !! _); cbn; done.
Qed.

Lemma hg_strongperm_eq_trans {T n m} (cohg cohg' cohg'' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' -> hg_strongperm_eq cohg' cohg'' ->
  hg_strongperm_eq cohg cohg''.
Proof.
  intros (Hins & Houts & Hverts & Hrel)
    (Hins' & Houts' & Hverts' & Hrel').
  split_and!; [now etransitivity; eauto..|].
  intros i.
  generalize (Hrel i), (Hrel' i).
  destruct (_ !! _), (_ !! _); try done;
  destruct (_ !! _); [|done]; cbn.
  apply transitivity.
Qed.

Add Parametric Relation {T n m} : (CospanHyperGraph T n m) hg_strongperm_eq
  reflexivity proved by hg_strongperm_eq_refl
  symmetry proved by hg_strongperm_eq_symm
  transitivity proved by hg_strongperm_eq_trans as hg_strongperm_eq_setoid.

Add Parametric Morphism {A B C} f : (@relabel_abs A B C f) with signature
  abs_strongperm_eq ==> abs_strongperm_eq as relabel_abs_strongperm_mor.
Proof.
  intros [[a l] u] [[a' l'] u'] Habs.
  split; [apply Habs.1|].
  cbn.
  rewrite <- 2 fmap_app.
  f_equiv.
  apply Habs.
Qed.


Add Parametric Morphism {A B C} (f : A -> B) :
  (prod_map (prod_map f (@id (list C))) (@id (list C))) with signature
  abs_strongperm_eq ==> abs_strongperm_eq as reindex_abs_strongperm_mor.
Proof.
  intros [[a l] u] [[a' l'] u'] Habs.
  cbn.
  split; [f_equal/=; apply Habs.1|].
  apply Habs.
Qed.

Add Parametric Morphism {T n m} f : (@relabel_graph T n m f) with signature
  hg_strongperm_eq ==> hg_strongperm_eq as relabel_graph_strongperm_mor.
Proof.
  intros cohg cohg' (Hins & Houts & Hverts & Hrel).
  split_and!; cbn; [now f_equal..|
    now f_equal|].
  intros i.
  rewrite 2 lookup_fmap.
  generalize (Hrel i).
  destruct (_ !! _), (_ !! _); [|done..].
  cbn.
  intros; now f_equiv.
Qed.

Add Parametric Morphism {T n m} f : (@reindex_graph T n m f) with signature
  hg_strongperm_eq ==> hg_strongperm_eq as reindex_graph_strongperm_mor.
Proof.
  intros cohg cohg' (Hins & Houts & Hverts & Hrel).
  split_and!; cbn; [done..|].
  apply map_relation_list_to_map.
  apply map_relation_to_map_to_list in Hrel.
  apply Forall2_fmap.
  eapply Forall2_impl; [apply Hrel|].
  intros [k tio] [k' tio'] [[= <-] Heq].
  cbn.
  done.
Qed.

Add Parametric Morphism {T n m n' m'} : (@stack_graphs_aux T n m n' m')
  with signature hg_strongperm_eq ==> hg_strongperm_eq ==> hg_strongperm_eq
    as stack_graphs_aux_strongperm_mor.
Proof.
  intros ? ? (Hins1 & Houts1 & Hverts1 & Hrel1)
    ? ? (Hins2 & Houts2 & Hverts2 & Hrel2).
  split_and!; [now f_equal/=..|].
  cbn.
  now apply map_relation_union.
Qed.


Add Parametric Morphism {T n m n' m'} : (@stack_graphs T n m n' m')
  with signature hg_strongperm_eq ==> hg_strongperm_eq ==> hg_strongperm_eq
    as stack_graphs_strongperm_mor.
Proof.
  intros ? ? ? ? ? ?.
  unfold stack_graphs.
  now repeat f_equiv.
Qed.

Add Parametric Morphism {T n m o} : (@compose T n m o)
  with signature hg_strongperm_eq ==> hg_strongperm_eq ==> hg_strongperm_eq
    as compose_strongperm_mor.
Proof.
  intros cohg1 cohg1' (Hins1 & Houts1 & Hverts1 & Hrel1)
    cohg2 cohg2' (Hins2 & Houts2 & Hverts2 & Hrel2).
  unfold compose.
  rewrite <- Hins1, <- Hins2, <- Houts1, <- Houts2.
  f_equiv.
  split_and!; [try done..|now do 2 f_equal/=|].
  cbn.
  now apply map_relation_union.
Qed.

Add Parametric Morphism {T n m o} : (@compose_unsafe T n m o)
  with signature hg_strongperm_eq ==> hg_strongperm_eq ==> hg_strongperm_eq
    as compose_unsafe_strongperm_mor.
Proof.
  intros cohg1 cohg1' (Hins1 & Houts1 & Hverts1 & Hrel1)
    cohg2 cohg2' (Hins2 & Houts2 & Hverts2 & Hrel2).
  unfold compose_unsafe.
  rewrite <- ?Hins1, <- ?Hins2, <- ?Houts1, <- ?Houts2.
  split_and!; [try done..|now do 2 f_equal/=|].
  cbn.
  now apply map_relation_union.
Qed.

Add Parametric Morphism {T n m o} : (@compose_safe T n m o)
  with signature hg_strongperm_eq ==> hg_strongperm_eq ==> hg_strongperm_eq
    as compose_safe_strongperm_mor.
Proof.
  intros cohg1 cohg1' Heq1
    cohg2 cohg2' Heq2.
  rewrite 2 compose_safe_to_compose.
  (do 3 f_equiv); assumption.
Qed.

Lemma graph_namedtensorlist_semantics_hg_strongperm_eq
  {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' ->
  ntl_strongperm_eq (graph_namedtensorlist_semantics cohg)
    (graph_namedtensorlist_semantics cohg').
Proof.
  intros (Hins & Houts & Hverts & Hperm)%hg_strongperm_eq_alt.
  apply map_relation_to_map_to_list in Hperm.
  split; [|split].
  - cbn.
    now rewrite <- Hverts.
  - cbn.
    apply eqlistA_PermutationA, eqlistA_altdef.
    unfold tg_abstracts.
    apply Forall2_fmap.
    eapply Forall2_impl; [apply Hperm|].
    intros (k, tio) (k', tio').
    cbn.
    intros [<- Heq].
    split; [done|].
    cbn.
    rewrite <- 2 fmap_app.
    f_equiv.
    apply Heq.
  - cbn.
    now rewrite <- Hins, Houts.
Qed.

Section Correctness.

Context `{TensT : TensorLike R rO rI radd rmul req A T}.

Lemma graph_mabs_hg_strongperm_eq 
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' ->
  graph_mabs cohg.(hedges) = graph_mabs cohg'.(hedges).
Proof.
  intros (Hins & Houts & Hverts & Hperm).
  unfold graph_mabs.
  apply map_eq; intros i.
  specialize (Hperm i).
  rewrite 2 lookup_fmap.
  destruct (_ !! _), (_ !! _); [|done..].
  cbn in *.
  now rewrite Hperm.1.
Qed.

Lemma hg_strongperm_eq_correct `{!StronglyPermutativeTensorLike TensT}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' ->
  graph_semantics (SR:=SR) cohg ≡ graph_semantics cohg'.
Proof.
  intros Hperm.
  apply graph_mabs_hg_strongperm_eq in Hperm as Hmabs.
  apply graph_namedtensorlist_semantics_hg_strongperm_eq in Hperm as Hntl.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics].
  unfold namedtensorlist_to_tensor.
  rewrite <- Hmabs.
  apply ntl_strongperm_eq_correct.
  - apply graph_namedtensorlist_semantics_WF.
  - done.
  - intros i dt _ Hidt.
    unfold graph_mabs in Hidt.
    rewrite lookup_fmap in Hidt.
    destruct (cohg.(hedges).(hyperedges) !! i); [|done].
    revert Hidt.
    intros [= <-].
    apply interpretTensorStronglyPermutative.
Qed.

End Correctness.

Lemma mk_hg_strongperm_eq' {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg.(inputs) = cohg'.(inputs) ->
  cohg.(outputs) = cohg'.(outputs) ->
  cohg.(hedges).(hypervertices) = cohg'.(hedges).(hypervertices) ->
  map_relation (λ _ tio tio', abs_strongperm_eq tio tio')
    (λ _ _, False) (λ _ _, False)
    cohg.(hedges).(hyperedges) cohg'.(hedges).(hyperedges) ->
  hg_strongperm_eq cohg cohg'.
Proof.
  intros Hins Houts Hhverts Hperm.
  done.
Qed.
