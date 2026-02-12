Require Import SetoidList SetoidPermutation.
From stdpp Require Import fin_maps.
Require Import TEPerm.
Require Export TensorGraph TensorGraphExpr TensorGraphSemantics TensorGraphFacts.


Lemma map_relation_to_dom' `{FinMap K M} {A} P (m1 m2 : M A) :
  map_relation P (λ _ _, False) (λ _ _, False) m1 m2 ->
  (forall j, is_Some (m1 !! j) <-> is_Some (m2 !! j)).
Proof.
  intros Hrel j.
  specialize (Hrel j).
  rewrite 2 is_Some_alt.
  do 2 case_match; done.
Qed.

Lemma map_relation_to_map_to_list `{FinMap K M} {A} P (m1 m2 : M A) :
  map_relation P (λ _ _, False) (λ _ _, False) m1 m2 ->
  Forall2 (λ ka kb, ka.1 = kb.1 /\ P ka.1 ka.2 kb.2)
    (map_to_list m1) (map_to_list m2).
Proof.
  revert m2; induction m1 as [|i a m1 Hm1i H1fst IHm1] using map_first_key_ind; intros m2 Hrel.
  - replace m2 with (∅ :> M A); [now rewrite map_to_list_empty|].
    symmetry.
    apply map_empty.
    intros i.
    pose proof ((map_relation_to_dom' _ _ _ Hrel i).2) as Hsome.
    rewrite lookup_empty in Hsome.
    rewrite 2 is_Some_alt in Hsome.
    now destruct (m2 !! i).
  - specialize (map_relation_to_dom' _ _ _ Hrel) as Hdom'.
    rewrite map_to_list_insert_first_key by done.
    assert (H2fst : map_first_key m2 i). 1:{
      revert H1fst.
      now refine (map_first_key_dom' _ _ _ _).1.
    }
    assert (Hm2i : is_Some (m2 !! i)) by now rewrite <- Hdom', lookup_insert.
    destruct Hm2i as [m2i Hm2i].
    rewrite <- (insert_delete _ _ _ Hm2i) in Hrel |- *.
    rewrite map_to_list_insert_first_key by
      first [apply lookup_delete|now rewrite insert_delete].
    constructor.
    + specialize (Hrel i).
      now rewrite 2 lookup_insert in Hrel.
    + apply IHm1.
      intros j.
      generalize (Hrel j).
      rewrite 2 lookup_insert_case.
      case_decide as Hij; [subst; now rewrite Hm1i, lookup_delete|].
      done.
Qed.


(* The (strong) permutation relation on graphs, and its correctness *)

Definition hg_strongperm_eq {T n m} (cohg cohg' : CospanHyperGraph T n m) : Prop :=
  cohg.(inputs) = cohg'.(inputs) /\
  cohg.(outputs) = cohg'.(outputs) /\
  vertices cohg = vertices cohg' /\
  map_relation (λ _ tio tio', abs_strongperm_eq tio tio')
    (λ _ _, False) (λ _ _, False)
    cohg.(hedges).(hyperedges) cohg'.(hedges).(hyperedges).

Lemma graph_namedtensorlist_semantics_hg_strongperm_eq
  {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  hg_strongperm_eq cohg cohg' ->
  ntl_strongperm_eq (graph_namedtensorlist_semantics cohg)
    (graph_namedtensorlist_semantics cohg').
Proof.
  intros (Hins & Houts & Hverts & Hperm).
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

Lemma graph_mabs_hg_strongperm_eq `{TensorLike R A T}
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

Lemma hg_strongperm_eq_correct `{TensT : TensorLike R A T,
  SR : SemiRing R rO rI radd rmul req,
  !StronglyPermutativeTensorLike TensT,
  SA : Summable A, EQA : EqDecision A}
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


