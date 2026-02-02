Require Export Aux_pos TESyntax.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.

(* A HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)
Notation HyperGraph T := (Pmap (T * list positive * list positive)).

(* Instance Union_hypergraph {T} : Union (HyperGraph T) := {
  union := union
}. *)


Definition disj_union_hypergraph {T} (hg0 hg1 : HyperGraph T) : HyperGraph T :=
  (kmap (bcons false) (relabel_abs (bcons false) <$> hg0) ∪ 
    (kmap (bcons true) (relabel_abs (bcons true) <$> hg1))).

Instance Disjoint_union_hypergraph {T} : DisjUnion (HyperGraph T) :={
  disj_union := disj_union_hypergraph
}.

Local Open Scope positive.
Definition example_disj_union : HyperGraph positive := 
  ({[ 1 := (1, [], []) ; 2 := (2, [], []) ]} ⊎ {[ 1 := (2, [1], [1]) ]}).

Definition example_1 : HyperGraph positive := {[ 1:= (1, [], [])]}.

Lemma disjoint_example : example_1 ##ₘ {[ 2 := (2, [], []) ]}.
Proof.
  compute_done.
Qed.
