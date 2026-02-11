Require Export VyZXTensor.
From stdpp Require Import vector. 
Require Import TensorGraph TensorGraphSemantics 
  TensorGraphFacts GraphRewriting ZXGraph.


Fixpoint ZX_graph_semantics {n m} (zx : ZX n m) : 
  @CospanHyperGraph (option (bool * R)) n m :=
  match zx with 
  | ⦰ => id_graph 0
  | ⊂ => cup_graph 1
  | ⊃ => cap_graph 1
  | ⨉ => swap_graph 1 1
  | — => id_graph 1
  | □ => graph_of_tensor None 1 1
  | X n m α => graph_of_tensor (Some (true, α)) n m
  | Z n m α => graph_of_tensor (Some (false, α)) n m
  | zx0 ↕ zx1 => stack_graphs (ZX_graph_semantics zx0) (ZX_graph_semantics zx1)
  | zx0 ⟷ zx1 => compose_safe (ZX_graph_semantics zx0) (ZX_graph_semantics zx1)
  end.




Lemma ZX_graph_semantics_correct {n m} (zx : ZX n m) :
  graph_semantics (ZX_graph_semantics zx) ≡ ZX_tensor_semantics zx.
Proof.
  induction zx.
  - cbn.
    apply graph_semantics_id.
  - apply graph_semantics_cup_1_1.
  - apply graph_semantics_cap_1_1.
  - apply graph_semantics_swap_1_1.
  - apply graph_semantics_id.
  - cbn.
    rewrite graph_semantics_graph_of_tensor.
    apply h_stack1'_11.
  - refine (graph_semantics_graph_of_tensor _ _ _).
  - refine (graph_semantics_graph_of_tensor _ _ _).
  - cbn.
    rewrite graph_semantics_stack_graphs.
    now apply stack_tensor_mor.
  - cbn.
    rewrite graph_semantics_compose_safe.
    now apply compose_tensor_mor.
Qed.


Example iso_test_example α : 
  (⊂ ↕ Z 1 1 α) ⟷ (— ↕ ⊃) ∝= Z 1 1 α.
Proof.
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  rewrite <- 2 ZX_graph_semantics_correct.
  rewrite <- 2 (graph_semantics_norm_verts (ZX_graph_semantics _)).
  eapply graph_semantics_isomorphic.
  Time
  eapply (graph_iso_conditions_correct _ _ 0);
  vm_compute;
  reflexivity.
Qed.


Example iso_test_example' α β : 
  (⊂ ↕ Z 1 1 α) ⟷ (Z 1 1 β ↕ ⊃) ∝= 
    (Z 1 1 α ↕ ⊂) ⟷ (⊃ ↕ Z 1 1 β).
Proof.
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  rewrite <- 2 ZX_graph_semantics_correct.
  rewrite <- 2 (graph_semantics_norm_verts (ZX_graph_semantics _)).
  eapply graph_semantics_isomorphic.
  Time
  eapply (graph_iso_conditions_correct _ _ 0);
  vm_compute;
  reflexivity.
Qed.


Example iso_test_example'' α β : 
  (Z 0 0 α) ⟷ (Z 0 0 β) ∝= 
  (Z 0 0 α) ↕ (Z 0 0 β).
Proof.
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  rewrite <- 2 ZX_graph_semantics_correct.
  rewrite <- 2 (graph_semantics_norm_verts (ZX_graph_semantics _)).
  eapply graph_semantics_isomorphic.
  Fail eapply (graph_iso_conditions_correct _ _ 1);
  vm_compute;
  reflexivity.
  eapply (graph_iso_conditions_correct _ _ 0);
  vm_compute;
  reflexivity.
Qed.


