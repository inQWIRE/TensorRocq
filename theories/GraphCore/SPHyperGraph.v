Require Export Aux_pos TESyntax.
From stdpp Require Export gmultiset list sorting fin_maps.
From stdpp Require Export pmap gmap.

(* A strongly permutative hyper edge is an indicator for the edge type and the source and target vertices *)
Notation SPHyperEdge T := (T * gmultiset positive)%type.
(* A S[trongly]P[ermutative]HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)

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