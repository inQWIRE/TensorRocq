Require Export VyZXTensor.
Require Import SPTensorGraph SPTensorGraphGraph 
  SPIsomorphismTesting TensorGraph TensorGraphSemantics
  TensorGraphFacts TensorGraphSP GraphRewriting SPGraphRewriting ZXGraph.
Require Import VyZXHyperGraph.
From stdpp Require Import vector pretty.

Fixpoint ZX_spgraph_semantics {n m} (zx : ZX n m) :
  @CospanSPHyperGraph (option (bool * R)) n m :=
  match zx with
  | ⦰ => id_spgraph 0
  | ⊂ => cup_spgraph 1
  | ⊃ => cap_spgraph 1
  | ⨉ => swap_spgraph 1 1
  | — => id_spgraph 1
  | □ => spgraph_of_tensor None 1 1
  | X n m α => spgraph_of_tensor (Some (true, α)) n m
  | Z n m α => spgraph_of_tensor (Some (false, α)) n m
  | zx0 ↕ zx1 => stack_spgraphs (ZX_spgraph_semantics zx0) (ZX_spgraph_semantics zx1)
  | zx0 ⟷ zx1 => spcompose_safe (ZX_spgraph_semantics zx0) (ZX_spgraph_semantics zx1)
  end.


Lemma ZX_spgraph_semantics_correct_aux {n m} (zx : ZX n m) :
  hg_strongperm_eq (cosphg2cohg (ZX_spgraph_semantics zx)) 
    (ZX_graph_semantics zx).
Proof.
  induction zx.
  - apply eq_reflexivity, cosphg2cohg_id_spgraph.
  - apply eq_reflexivity, (cosphg2cohg_cup_spgraph (n:=1)).
  - apply eq_reflexivity, (cosphg2cohg_cap_spgraph (n:=1)).
  - apply eq_reflexivity, (@cosphg2cohg_swap_spgraph _ 1 1).
  - apply eq_reflexivity, cosphg2cohg_id_spgraph.
  - apply cosphg2cohg_spgraph_of_tensor.
  - apply cosphg2cohg_spgraph_of_tensor.
  - apply cosphg2cohg_spgraph_of_tensor.
  - cbn.
    now rewrite cosphg2cohg_stack_spgraphs, IHzx1, IHzx2.
  - cbn.
    now rewrite cosphg2cohg_spcompose_safe, IHzx1, IHzx2.
Qed.

Lemma ZX_spgraph_semantics_correct {n m} (zx : ZX n m) :
  graph_semantics (cosphg2cohg (ZX_spgraph_semantics zx)) ≡ 
    ZX_tensor_semantics zx.
Proof.
  rewrite <- ZX_graph_semantics_correct.
  apply hg_strongperm_eq_correct, ZX_spgraph_semantics_correct_aux.
Qed.

Lemma ZX_propeq_of_spgraph_spisomorphic {n m} (zx zx' : ZX n m) :
  spisomorphic (norm_spverts $ ZX_spgraph_semantics zx) 
    (norm_spverts $ ZX_spgraph_semantics zx') ->
  zx ∝= zx'.
Proof.
  intros (cohg & Hcohg & Hiso)%cosphg2cohg_spisomorphic_gen.
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  rewrite <- 2 ZX_spgraph_semantics_correct.
  rewrite <- 2 (graph_semantics_norm_verts (cosphg2cohg _)).
  rewrite <- 2 cosphg2cohg_norm_spverts.
  etransitivity; [|apply hg_strongperm_eq_correct; eassumption].
  now apply graph_semantics_isomorphic.
Qed.

Example spiso_test_example α : 
  — ↕ Z 1 1 α ⟷ ⊃ ∝= Z 2 0 α.
Proof.
  apply ZX_propeq_of_spgraph_spisomorphic.
  apply (spgraph_iso_conditions_correct _ _ 0).
  vm_compute.
  reflexivity.
Qed.

Ltac spgraph_iso_with n :=
  apply (spgraph_iso_conditions_correct _ _ n);
  vm_compute;
  reflexivity.

Ltac zx_ocm_with n :=
  apply ZX_propeq_of_spgraph_spisomorphic;
  spgraph_iso_with n.
  

Ltac zx_ocm :=
  apply ZX_propeq_of_spgraph_spisomorphic;
  let rec go n :=
    tryif (
      apply (spgraph_iso_conditions_correct _ _ n);
      vm_compute;
      lazymatch goal with 
      | [|- False] => fail 2 "zx_ocm: No isomorphism found!"
      | [|- _] => refine ((λ 
      (_ : (String.concat "" ["Use 'zx_ocm_with "; pretty n; "'"] = "")%string), eq_refl) _);
        vm_compute
      end
    ) then idtac else go constr:(S n) in 
  go constr:(O). 


Example ocm_example : 
  (Z 1 1 0 ↕ X 1 2 0 ↕ Z 1 1 0) ⟷
  (X 2 2 0 ↕ X 2 2 0) ⟷ 
  (Z 1 1 0 ↕ ⊃ ↕ Z 1 1 0) ∝=
  (Z 1 1 0 ↕ (⨉ ⟷ (Z 1 1 0 ↕ X 1 2 0))) ⟷
  (— ↕ ⨉ ↕ —) ⟷
  (X 2 2 0 ↕ n_wire 2) ⟷
  (Z 1 1 0 ↕ (X 3 1 0 ⟷ Z 1 1 0)).
Proof.
  zx_ocm_with 0.
Qed.


Example ocm_example' α β γ : 
  (Z 1 1 γ ↕ X 1 2 α ↕ Z 1 1 β) ⟷
  (X 2 2 0 ↕ X 2 2 0) ⟷ 
  (Z 1 1 0 ↕ ⊃ ↕ Z 1 1 0) ∝=
  (Z 1 1 γ ↕ (⨉ ⟷ (Z 1 1 β ↕ X 1 2 α))) ⟷
  (— ↕ ⨉ ↕ —) ⟷
  (X 2 2 0 ↕ n_wire 2) ⟷
  (Z 1 1 0 ↕ (X 3 1 0 ⟷ Z 1 1 0)).
Proof.
  zx_ocm_with 0.
Qed.

(* Fixpoint example_Z_stack_prf (n : nat) : S n = n + 1 :=
  match n with
  | O => eq_refl
  | S n' => f_equal S (example_Z_stack_prf n')
  end.

Fixpoint example_Z_stack (n : nat) : ZX n n :=
  match n with 
  | O => ⦰
  | S n' => cast _ _ (example_Z_stack_prf n') (example_Z_stack_prf n')
    $ example_Z_stack n' ↕ Z 1 1 (INR n')
  end.

Fixpoint example_Z_stack_rev (n : nat) : ZX n n :=
  match n with 
  | O => ⦰
  | S n' => Z 1 1 (INR n') ↕ example_Z_stack_rev n'
  end.

Example ocm_example'' : forall n, 
  Z 1 n 0 ⟷ example_Z_stack n ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ example_Z_stack_rev n ⟷ Z n 1 0.
Proof.
  intros n.
  assert (n = 5) by admit.
  subst.
  Time zx_ocm. *)
