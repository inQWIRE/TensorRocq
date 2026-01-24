Require Export TensorGraphSemantics.


(* Definition example_graph : TensorGraph (R:=C) (A:=bool) :=
  ∅G +[ 1 := (fun n m => @zsp n m 0) ]
     +[ 3 := (fun n m => @zsp n m 0) ]
     +{ (1,2) ; (1,3) ; (1,2) ; (1,3) ; (1,4) }.


Definition example_graph' : TensorGraph (R:=C) (A:=bool) :=
  ∅G +[ 1 := (fun n m => @zsp n m 0) ]
     +[ 3 := (fun n m => @zsp n m 0) ]
     +{ (1,2) ; (1,3) ; (3,4) }.

Compute graph_tensorlist_semantics example_graph.

Compute elements $ inputs example_graph.

Compute elements $ outputs example_graph.

Compute graph_tensorlist_semantics example_graph'.

Compute elements $ inputs example_graph'.

Compute elements $ outputs example_graph'. *)


(*
From VyZX Require Import CoreData.

Open Scope ZX_scope.

Open Scope nat_scope.

Example example_graph'_map_semantics : forall b b',
  graph_map_semantics example_graph'
    ∅ {[2:=b; 4:=b']} =
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_map_semantics].
  unfold kron.
  cbn -[graph_map_semantics].
  intros [] []; cbn -[graph_map_semantics]; (etransitivity;
    [unfold example_graph';
      remember @zsp as zsp' eqn:Hzsp;
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp];
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.

Example example_graph'_list_semantics : forall b b',
  graph_list_semantics example_graph'
    [] [b; b'] =
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_list_semantics].
  unfold kron.
  cbn -[graph_list_semantics].
  intros [] []; cbn -[graph_list_semantics]; (etransitivity;
    [unfold example_graph';
      remember @zsp as zsp' eqn:Hzsp;
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp];
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.

Example example_graph'_vector_semantics : forall b b',
  graph_vector_semantics example_graph'
    [# ] [# b; b'] =
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_vector_semantics].
  unfold kron.
  cbn -[graph_vector_semantics].
  intros [] []; cbn -[graph_vector_semantics]; (etransitivity;
    [unfold example_graph';
      remember @zsp as zsp' eqn:Hzsp;
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp];
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.
 *)