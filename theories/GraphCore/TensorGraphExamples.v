Require Export TensorGraphSemantics ZXGraph.
Local Open Scope positive_scope.

(* Definition example_graph : TensorGraph (R:=C) (A:=bool) :=
  ∅G +[ 1 := (fun n m => @zsp n m 0) ]
     +[ 3 := (fun n m => @zsp n m 0) ]
     +{ (1,2) ; (1,3) ; (1,2) ; (1,3) ; (1,4) }. *)


Definition example_graph' : CospanHyperGraph (option (bool*R)) 0 2 :=
  [#] -> {[ 1 := (Some (false, 0%R), [], [2;1]) ; 
        3 := (Some (false, 0%R), [1], [3])]} <- [# 2;3].

(* Compute graph_tensorlist_semantics example_graph.

Compute elements $ inputs example_graph.

Compute elements $ outputs example_graph.

Compute graph_tensorlist_semantics example_graph'.

Compute elements $ inputs example_graph'.

Compute elements $ outputs example_graph'. *)


Import ZXCore.
From VyZX Require Import CoreData.

Open Scope ZX_scope.

Open Scope nat_scope.

Locate HyperEdge.

Print HyperEdge.

Locate "ZXG".

Open Scope positive.

Definition example_graph_tp : CospanHyperGraph ZXVERT 1 1 :=
 [# 1] -> {[ 1 := (Some (true,  0%R), [1], [2; 3]);
             2 := (Some (false, 0%R), [2; 4], [5]);
             3 := (Some (true, 0%R), [3], []) ]} <- [# 5].

Locate cohg_semantic_eq.

Search TensorLike.
Print ZXVERT.



Lemma teleportation : example_graph_tp ≡ₜ@{ ZXCALC } id_graph 1.
Proof.
  unfold example_graph_tp.
  unfold id_graph.
  cbv.
Admitted.

Example example_graph'_semantics : forall b b',
  graph_semantics example_graph'
    [#] [#b;b'] =
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_semantics].
  unfold kron.
  cbn -[graph_semantics].
  intros [] []; cbn -[graph_semantics]; 
  (etransitivity;
    [unfold example_graph', ZXCALC, ZXCALC_tensor; cbn;

      remember @zsp as zsp' eqn:Hzsp;
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp];
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.
