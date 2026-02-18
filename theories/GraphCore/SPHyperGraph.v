Require Export Aux_pos TESyntax.
From stdpp Require Export gmultiset list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export HyperGraphAux.

(* A strongly permutative hyper edge is an indicator for the edge type and the source and target vertices *)
Notation SPHyperEdge T := (T * gmultiset positive)%type.
(* A S[trongly]P[ermutative]HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)

#[export] Instance SPHyperEdge_equiv `{Equiv T} : Equiv (SPHyperEdge T) :=
  prod_relation (≡) (=).

Record SPHyperGraph {T} := mk_sphg {
  (* The edges of the hypergraph *)
  sphyperedges : Pmap (SPHyperEdge T);
  (* Additional vertices of the hypergraph, which are often
    disjoint from the referrenced vertices of [sphyperedges]
    (in practice, we only care about the subset of [sphypervertices]
    not referrenced in [sphyperedges], but do not enforce disjointness) *)
  sphypervertices : Pset;
}.

#[global] Arguments SPHyperGraph (_) : clear implicits, assert.
#[global] Arguments mk_sphg {_} _ _ : assert.

#[global] Coercion sphyperedges : SPHyperGraph >-> Pmap.

Lemma sphg_ext {T} (sphg sphg' : SPHyperGraph T) :
  sphg.(sphyperedges) = sphg'.(sphyperedges) ->
  sphg.(sphypervertices) = sphg'.(sphypervertices) ->
  sphg = sphg'.
Proof.
  destruct sphg, sphg'; cbn; congruence.
Qed.

#[export] Instance sphypergraph_empty {T} :
  Empty (SPHyperGraph T) := mk_sphg ∅ ∅.

#[export] Instance sphypergraph_partialalter {T} :
  PartialAlter positive (SPHyperEdge T) (SPHyperGraph T) :=
  fun f i sphg => mk_sphg (partial_alter f i sphg.(sphyperedges)) sphg.(sphypervertices).

Definition reindex_sphg {T} (f : positive -> positive) (sphg : SPHyperGraph T) :
  SPHyperGraph T :=
  mk_sphg (kmap f sphg.(sphyperedges)) sphg.(sphypervertices).

Definition relabel_sphg {T} (f : positive -> positive) (sphg : SPHyperGraph T) :
  SPHyperGraph T :=
  mk_sphg (prod_map id (gmultiset_map f) <$> sphg.(sphyperedges)) (set_map f sphg.(sphypervertices)).

Definition vertices_sphg {T} (sphg : SPHyperGraph T) : Pset :=
  list_to_set (map_to_list (sphg.(sphyperedges)) ≫=
    λ k_flu : (positive*(SPHyperEdge T)), (elements k_flu.2.2)) ∪
  sphg.(sphypervertices).

#[export] Instance sphypergraph_union {T} : Union (SPHyperGraph T) :=
  fun sphg sphg' =>
    mk_sphg (sphg.(sphyperedges) ∪ sphg'.(sphyperedges))
      (sphg.(sphypervertices) ∪ sphg'.(sphypervertices)).

#[export] Instance sphypergraph_disjunion {T} : DisjUnion (SPHyperGraph T) :=
  fun sphg sphg' =>
  reindex_sphg (bcons false) (relabel_sphg (bcons false) sphg) ∪
  reindex_sphg (bcons true) (relabel_sphg (bcons true) sphg').


#[export] Instance sphypergraph_equiv `{Equiv T} : Equiv (SPHyperGraph T) :=
  fun sphg sphg' =>
  sphg.(sphyperedges) ≡ sphg'.(sphyperedges) /\
  sphg.(sphypervertices) = sphg'.(sphypervertices).

#[export] Instance sphypergraph_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence (≡@{SPHyperGraph T}).
Proof.
  apply rel_intersection_equiv.
  - refine (rel_preimage_equiv sphyperedges _ _).
  - refine (rel_preimage_equiv sphypervertices _ _).
Qed.


Add Parametric Morphism `{Equiv T} : (@vertices_sphg T) with signature
  (≡) ==> eq as vertices_sphg_equiv.
Proof.
  intros sphg sphg' [Heq Hverts].
  unfold vertices_sphg.
  rewrite <- Hverts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.2.2.
Qed.

Add Parametric Morphism `{Equiv T} (f : positive -> positive) : 
  (prod_map (@id T) (gmultiset_map f)) with signature
  (≡) ==> (≡) as relabel_spabs_proper.
Proof.
  intros [t v] [t' v'] [? ?]; split; cbn; [done|now f_equal].
Qed.

Add Parametric Morphism `{Equiv T, Reflexive T equiv} f : (@relabel_sphg T f) with signature
  (≡) ==> (≡) as relabel_sphg_proper.
Proof.
  intros sphg sphg' [Heq Hverts].
  split; [|cbn; now f_equal].
  cbn.
  apply (map_fmap_proper _ _); [|done].
  apply relabel_spabs_proper_Proper.
Qed.

Add Parametric Morphism `{Equiv T, Reflexive T equiv} f : (@reindex_sphg T f) with signature
  (≡) ==> (≡) as reindex_sphg_proper.
Proof.
  intros sphg sphg' [Heq Hverts].
  split; [|apply Hverts].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T} : (@union (SPHyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as sphypergraph_union_proper.
Proof.
  intros sphg1 sphg1' Hsphg1 sphg2 sphg2' Hsphg2.
  split; [|cbn; f_equal; [apply Hsphg1|apply Hsphg2]].
  cbn.
  apply union_proper; [apply Hsphg1|apply Hsphg2].
Qed.


Add Parametric Morphism `{Equiv T} : (@disj_union (SPHyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as sphypergraph_disj_union_proper.
Proof.
  intros sphg1 sphg1' Hsphg1 sphg2 sphg2' Hsphg2.
  split; [|cbn; do 2 f_equal; [apply Hsphg1|apply Hsphg2]].
  cbn.
  apply union_proper; f_equiv; 
  (apply map_fmap_proper; [apply relabel_spabs_proper_Proper|]); 
  [apply Hsphg1|apply Hsphg2].
Qed.


Lemma sphyperedges_singleton {T} k abs :
  sphyperedges (T:=T) {[k := abs]} = {[k := abs]}.
Proof.
  done.
Qed.