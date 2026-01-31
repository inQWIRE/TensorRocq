From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.

(* A HyperGraph representation where edges have a type T and the graph is represented as a map of positives to (edge_data, input_vertices, output_vertices) *)
Notation HyperGraph T := (Pmap (T * list positive * list positive)).

(* Instance Union_hypergraph {T} : Union (HyperGraph T) := {
  union := union
}. *)

Definition vert_map {T} (f : positive -> positive) (x : T * list positive * list positive)  : (T * list positive * list positive) :=
  (x.1.1, f <$> x.1.2, f <$> x.2).

Definition disj_union_hypergraph {T} (hg0 hg1 : HyperGraph T) : HyperGraph T :=
  (kmap xI (vert_map xI <$> hg0) ∪ (kmap xO (vert_map xO <$> hg1))).

Instance Union_hypergraph {T} : Union (HyperGraph T) :={
  union := union
}.

Instance Disjoint_union_hypergraph {T} : DisjUnion (HyperGraph T) :={
  disj_union := disj_union_hypergraph
}.

Local Open Scope positive.
Definition example_disj_union : HyperGraph positive := 
  ({[ 1 := (1, [], []) ; 2 := (2, [], []) ]} ⊎ {[ 1 := (2, [1], [1]) ]}).

Definition example_1 : HyperGraph positive := {[ 1:= (1, [], [])]}.

Lemma disjoint_example : example_1 ##ₘ {[ 2 := (2, [], []) ]}.
Proof.
  unfold example_1.
  rewrite map_disjoint_spec.
  intros.
  rewrite lookup_singleton_Some in H.
  destruct H as [Hi Hx].
  subst.
  rewrite lookup_singleton_Some in H0.
  destruct H0 as [Hc Hy].
  contradict Hc.
  lia. 
Qed.
