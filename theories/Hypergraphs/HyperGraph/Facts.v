From TensorRocq Require Export Aux_relset Aux_pos Syntax.
Require Import SetoidList.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.

Lemma option_relation_Forall2 {A B} (P : A -> B -> Prop) ma mb :
  option_relation P (λ _, False) (λ _, False) ma mb <->
  option_Forall2 P ma mb.
Proof.
  rewrite option_Forall2_alt.
  done.
Qed.

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


Lemma map_relation_union `{FinMap K M} {A} P (m1 m1' m2 m2' : M A) :
  map_relation P (λ _ _, False) (λ _ _, False) m1 m1' ->
  map_relation P (λ _ _, False) (λ _ _, False) m2 m2' ->
  map_relation P (λ _ _, False) (λ _ _, False) (m1 ∪ m2) (m1' ∪ m2').
Proof.
  intros Hm1 Hm2 i.
  rewrite 2 lookup_union.
  specialize (Hm1 i).
  destruct (m1 !! i), (m1' !! i); [rewrite 2 union_Some_l|..]; [done..|].
  rewrite 2 (left_id_L None _).
  apply Hm2.
Qed.

Lemma map_equiv_map_relation `{FinMap K M} `{Equiv A} (m1 m2 : M A) :
  m1 ≡ m2 <-> map_relation (λ _, equiv) (λ _ _, False) (λ _ _, False) m1 m2.
Proof.
  apply forall_proper; intros i.
  rewrite option_relation_Forall2.
  done.
Qed.

Lemma map_to_list_equiv `{FinMap K M} `{Equiv A} (m1 m2 : M A) :
  m1 ≡ m2 -> Forall2 (prod_relation eq equiv) (map_to_list m1) (map_to_list m2).
Proof.
  intros Hall2%map_equiv_map_relation%map_relation_to_map_to_list.
  apply Hall2.
Qed.

Lemma list_to_map_equiv `{FinMap K M} `{Equiv A} (l l' : list (K * A)) :
  Forall2 (prod_relation eq equiv) l l' ->
  list_to_map l ≡@{M A} list_to_map l'.
Proof.
  intros Heq.
  induction Heq as [|k k' l l' Hk Hl IHl]; [now apply map_empty_equiv_eq|].
  cbn.
  rewrite <- Hk.1.
  apply insert_proper, IHl.
  apply Hk.2.
Qed.

Add Parametric Morphism `{FinMap K M} `{Equiv A} : (@map_to_list K A (M A) _)
  with signature (≡) ==> eqlistA (prod_relation eq equiv) as map_to_list_proper.
Proof.
  intros m1 m2 Heq.
  rewrite eqlistA_altdef.
  now apply map_to_list_equiv.
Qed.

Add Parametric Morphism `{FinMap K1 M1, FinMap K2 M2} `{Equiv A} (f : K1 -> K2) :
  (kmap f) with signature (≡@{M1 A}) ==> (≡@{M2 A}) as map_kmap_proper.
Proof.
  intros m1 m2 Heq%map_to_list_equiv.
  unfold kmap.
  apply list_to_map_equiv.
  rewrite Forall2_fmap.
  eapply Forall2_impl; [apply Heq|].
  intros [] [] [[= ->] Hequiv].
  split; done.
Qed.