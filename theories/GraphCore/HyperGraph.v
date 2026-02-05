Require Export Aux_pos TESyntax.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.


(* A hyper edge is an indicator for the edge type and the source and target vertices *)
Notation HyperEdge T := (T * list positive * list positive)%type.
(* A HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)
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
