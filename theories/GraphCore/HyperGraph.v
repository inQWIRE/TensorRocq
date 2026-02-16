Require Export Aux_relset Aux_pos TESyntax.
Require Import SetoidList.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.

(* FIXME: Move *)
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



(* A hyper edge is an indicator for the edge type and the source and target vertices *)
Notation HyperEdge T := (T * list positive * list positive)%type.
(* A HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)
#[export] Instance HyperEdge_equiv `{Equiv T} : Equiv (HyperEdge T) :=
  prod_relation (prod_relation (≡) (=)) (=).

Record HyperGraph {T} := mk_hg {
  (* The edges of the hypergraph *)
  hyperedges : Pmap (T * list positive * list positive);
  (* Additional vertices of the hypergraph, which are often
    disjoint from the referrenced vertices of [hyperedges]
    (in practice, we only care about the subset of [hypervertices]
    not referrenced in [hyperedges], but do not enforce disjointness) *)
  hypervertices : Pset;
}.

#[global] Arguments HyperGraph (_) : clear implicits, assert.
#[global] Arguments mk_hg {_} _ _ : assert.

#[global] Coercion hyperedges : HyperGraph >-> Pmap.

Lemma hg_ext {T} (hg hg' : HyperGraph T) :
  hg.(hyperedges) = hg'.(hyperedges) ->
  hg.(hypervertices) = hg'.(hypervertices) ->
  hg = hg'.
Proof.
  destruct hg, hg'; cbn; congruence.
Qed.

#[export] Instance hypergraph_empty {T} :
  Empty (HyperGraph T) := mk_hg ∅ ∅.

#[export] Instance hypergraph_partialalter {T} :
  PartialAlter positive (T * list positive * list positive) (HyperGraph T) :=
  fun f i hg => mk_hg (partial_alter f i hg.(hyperedges)) hg.(hypervertices).

Definition reindex_hg {T} (f : positive -> positive) (hg : HyperGraph T) :
  HyperGraph T :=
  mk_hg (kmap f hg.(hyperedges)) hg.(hypervertices).

Definition relabel_hg {T} (f : positive -> positive) (hg : HyperGraph T) :
  HyperGraph T :=
  mk_hg (relabel_abs f <$> hg.(hyperedges)) (set_map f hg.(hypervertices)).

Definition vertices_hg {T} (hg : HyperGraph T) : Pset :=
  list_to_set (map_to_list (hg.(hyperedges)) ≫=
    λ k_flu : (positive*(T*list _*list _)), (k_flu.2.1.2 ++ k_flu.2.2)) ∪
  hg.(hypervertices).

#[export] Instance hypergraph_union {T} : Union (HyperGraph T) :=
  fun hg hg' =>
    mk_hg (hg.(hyperedges) ∪ hg'.(hyperedges))
      (hg.(hypervertices) ∪ hg'.(hypervertices)).

#[export] Instance hypergraph_disjunion {T} : DisjUnion (HyperGraph T) :=
  fun hg hg' =>
  reindex_hg (bcons false) (relabel_hg (bcons false) hg) ∪
  reindex_hg (bcons true) (relabel_hg (bcons true) hg').

#[export] Instance hypergraph_equiv `{Equiv T} : Equiv (HyperGraph T) :=
  fun hg hg' =>
  hg.(hyperedges) ≡ hg'.(hyperedges) /\
  hg.(hypervertices) = hg'.(hypervertices).

#[export] Instance hypergraph_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence (≡@{HyperGraph T}).
Proof.
  apply rel_intersection_equiv.
  - refine (rel_preimage_equiv hyperedges _ _).
  - refine (rel_preimage_equiv hypervertices _ _).
Qed.


Add Parametric Morphism `{Equiv T} : (@vertices_hg T) with signature
  (≡) ==> eq as vertices_hg_equiv.
Proof.
  intros hg hg' [Heq Hverts].
  unfold vertices_hg.
  rewrite <- Hverts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L (_++_)).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} f : (@relabel_abs T positive positive f) with signature
  (≡) ==> (≡) as relabel_abs_proper.
Proof.
  intros [[t i] o] [[t' i'] o'] [[? ?] ?]; split; [split|]; cbn; now f_equal.
Qed.

Add Parametric Morphism `{Equiv T, Reflexive T equiv} f : (@relabel_hg T f) with signature
  (≡) ==> (≡) as relabel_hg_proper.
Proof.
  intros hg hg' [Heq Hverts].
  split; [|cbn; now f_equal].
  cbn.
  apply (map_fmap_proper _ _); [|done].
  apply relabel_abs_proper_Proper.
Qed.

Add Parametric Morphism `{Equiv T, Reflexive T equiv} f : (@reindex_hg T f) with signature
  (≡) ==> (≡) as reindex_hg_proper.
Proof.
  intros hg hg' [Heq Hverts].
  split; [|apply Hverts].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T} : (@union (HyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as hypergraph_union_proper.
Proof.
  intros hg1 hg1' Hhg1 hg2 hg2' Hhg2.
  split; [|cbn; f_equal; [apply Hhg1|apply Hhg2]].
  cbn.
  apply union_proper; [apply Hhg1|apply Hhg2].
Qed.


Add Parametric Morphism `{Equiv T} : (@disj_union (HyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as hypergraph_disj_union_proper.
Proof.
  intros hg1 hg1' Hhg1 hg2 hg2' Hhg2.
  split; [|cbn; do 2 f_equal; [apply Hhg1|apply Hhg2]].
  cbn.
  apply union_proper; f_equiv; 
  (apply map_fmap_proper; [apply relabel_abs_proper_Proper|]); 
  [apply Hhg1|apply Hhg2].
Qed.



(* Notation HyperGraph T := (Pmap (T * list positive * list positive)).

Definition disj_union_hypergraph {T} (hg0 hg1 : HyperGraph T) : HyperGraph T :=
  (kmap (bcons false) (relabel_abs (bcons false) <$> hg0) ∪
    (kmap (bcons true) (relabel_abs (bcons true) <$> hg1))).

Instance Disjoint_union_hypergraph {T} : DisjUnion (HyperGraph T) :={
  disj_union := disj_union_hypergraph
}.

Definition targets {T} (he : HyperEdge T) : list positive :=
  snd he.
Definition sources {T} (he : HyperEdge T) : list positive :=
  snd (fst he).

Definition in_target {T} (v e : positive) (hg : HyperGraph T) :=
  is_Some (In v <$> (targets <$> (hg !! e))).

Lemma in_target_means_lookup_succeeds {T} (v e : positive) (hg : HyperGraph T) :
  in_target v e hg -> is_Some (hg !! e).
Proof.
  intros.
  inversion H.
  destruct (hg !! e).
  - easy.
  - contradict H0; easy.
Qed.

Definition in_source {T} (v e : positive) (hg : HyperGraph T) :=
  is_Some (In v <$> (sources <$> (hg !! e))).

Definition predecessor {T} (h h' : positive) (hg : HyperGraph T) :=
  exists x, in_target x h hg /\ in_source x h' hg.

Definition successor {T} (h h' : positive) (hg : HyperGraph T) :=
  exists x, in_target x h' hg /\ in_source x h hg.


Local Open Scope positive.
Definition example_disj_union : HyperGraph positive :=
  ({[ 1 := (1, [], []) ; 2 := (2, [], []) ]} ⊎ {[ 1 := (2, [1], [1]) ]}).

Definition example_1 : HyperGraph positive := {[ 1:= (1, [], [])]}.

Lemma disjoint_example : example_1 ##ₘ {[ 2 := (2, [], []) ]}.
Proof.
  compute_done.
Qed. *)
