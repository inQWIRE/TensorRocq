Require Export Aux_pos TESyntax.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.


(* A hyper edge is an indicator for the edge type and the source and target vertices *)
Notation HyperEdge T := (T * list positive * list positive)%type.
(* A HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)

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
