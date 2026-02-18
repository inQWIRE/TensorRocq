Require Export VyZXTensor.
Require Import SPTensorGraph SPTensorGraphGraph
  SPIsomorphismTesting TensorGraph TensorGraphSemantics
  TensorGraphFacts TensorGraphSP GraphRewriting SPGraphRewriting SPTensorGraphQuote ZXGraph.
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
  | zx0 ⟷ zx1 => compose_spgraphs (ZX_spgraph_semantics zx0) (ZX_spgraph_semantics zx1)
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
    now rewrite cosphg2cohg_compose_spgraphs, IHzx1, IHzx2.
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

Lemma ZX_propeq_of_spgraph_equiv {n m} (zx zx' : ZX n m) :
   (norm_spverts $ ZX_spgraph_semantics zx) ≡
    (norm_spverts $ ZX_spgraph_semantics zx') ->
  zx ∝= zx'.
Proof.
  intros (cohg & Hcohg & Hiso)%cosphg2cohg_equiv_gen.
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  rewrite <- 2 ZX_spgraph_semantics_correct.
  rewrite <- 2 (graph_semantics_norm_verts (cosphg2cohg _)).
  rewrite <- 2 cosphg2cohg_norm_spverts.
  symmetry.
  etransitivity; [|apply hg_strongperm_eq_correct; eassumption].
  now apply graph_semantics_equiv.
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


Typeclasses Opaque compose_spgraphs compose_spgraphs_aux stack_spgraphs
  stack_spgraphs_aux spgraph_of_tensor.


Typeclasses Opaque compose_graphs compose_graphs_aux stack_graphs
  stack_graphs_aux graph_of_tensor.


#[export] Hint Extern 0 (CospanSPHyperGraphDenote _ _ (@stack_spgraphs ?T ?n ?m ?n' ?m' ?cohg ?cohg') _) =>
  notypeclasses refine 
    (cosphg_denote_stack_spgraphs _ _ (n:=n) (m:=m) (n':=n') (m':=m') 
      cohg cohg' _ _ _ _) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphDenote _ _ (@cup_spgraph ?T ?n) _) =>
  notypeclasses refine 
    (cosphg_denote_cup_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphDenote _ _ (@cap_spgraph ?T ?n) _) =>
  notypeclasses refine 
    (cosphg_denote_cap_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphDenote _ _ (@id_spgraph ?T ?n) _) =>
  notypeclasses refine 
    (cosphg_denote_id_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphDenote _ _ (@swap_spgraph ?T ?n ?m) _) =>
  notypeclasses refine 
    (cosphg_denote_swap_spgraph _ _ (n:=n) (m:=m)) : typeclass_instances.

#[export] Hint Extern 0 (CospanSPHyperGraphQuote _ _ _ (@stack_spgraphs ?T ?n ?m ?n' ?m' ?cohg ?cohg')) =>
  notypeclasses refine 
    (cosphg_quote_stack_spgraphs _ _ (n:=n) (m:=m) (n':=n') (m':=m') 
      _ _ cohg cohg' _ _) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphQuote _ _ _ (@cup_spgraph ?T ?n)) =>
  notypeclasses refine 
    (cosphg_quote_cup_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphQuote _ _ _ (@cap_spgraph ?T ?n)) =>
  notypeclasses refine 
    (cosphg_quote_cap_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphQuote _ _ _ (@id_spgraph ?T ?n)) =>
  notypeclasses refine 
    (cosphg_quote_id_spgraph _ _ (n:=n)) : typeclass_instances.
#[export] Hint Extern 0 (CospanSPHyperGraphQuote _ _ _ (@swap_spgraph ?T ?n ?m)) =>
  notypeclasses refine 
    (cosphg_quote_swap_spgraph _ _ (n:=n) (m:=m)) : typeclass_instances.

Example ocm_example'_alt γ :
  (Z 1 (2+2) γ) ⟷ (X 2 2 0 ↕ X 2 2 0) ∝=
  (Z 1 (2+2) γ) ⟷ (X 2 2 0 ↕ X 2 2 0).
Proof.
  apply ZX_propeq_of_spgraph_equiv.

    (* apply spgraph_test_isomorphism_quote. *)
  unshelve (notypeclasses refine (spgraph_test_isomorphism_quote _ _ _ _ _ _ _ _
    _ _ _ _); [apply _..|]); [apply nil|].
  vm_compute.
  done.
Qed.


Example ocm_example''_alt α β γ :
  (Z 1 1 γ ↕ X 1 2 α ↕ Z 1 1 β) ⟷
  (X 2 2 0 ↕ X 2 2 0) ⟷
  (Z 1 1 0 ↕ ⊃ ↕ Z 1 1 0) ∝=
  (Z 1 1 γ ↕ (⨉ ⟷ (Z 1 1 β ↕ X 1 2 α))) ⟷
  (— ↕ ⨉ ↕ —) ⟷
  (X 2 2 0 ↕ n_wire 2) ⟷
  (Z 1 1 0 ↕ (X 3 1 0 ⟷ Z 1 1 0)).
Proof.
  apply ZX_propeq_of_spgraph_equiv.

    (* apply spgraph_test_isomorphism_quote. *)
  unshelve (notypeclasses refine (spgraph_test_isomorphism_quote _ _ _ _ _ _ _ _
    _ _ _ _); [cbn; apply _..|]); [apply nil|];
  vm_compute.
  done.
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

Section alt.

Context `{Equiv T, !RelDecision (≡@{T})}.
Fixpoint sphyperedge_map_isos_extending_aux' 
  (hg hg' : list (positive * (T * list (positive * positive))))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => match hg' with | [] => [mhe_mv] | _::_ => [] end
  | (k, (t, v)) :: hg =>
    list_select (λ k_tv, t ≡ k_tv.2.1 /\ 
      sum_list_with Pos.to_nat (k_tv.2.2).*2 = 
      sum_list_with Pos.to_nat v.*2) hg'
      ≫= λ '(k_tv, hg'rest),
      match pupdate k k_tv.1 mhe_mv.1 with
      | None => []
      | Some mhe' =>
        mv' ← gmultiset_pre_isos_extending_aux_alt v k_tv.2.2 mhe_mv.2;
        sphyperedge_map_isos_extending_aux' hg hg'rest
         (mhe', mv')
      end
  end.

Import Datatypes.

Definition sphyperedge_map_isos_extending'
  (hg hg' : Pmap (SPHyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  sphyperedge_map_isos_extending_aux' 
    (prod_map id (prod_map id (map_to_list (M:=gmap positive positive) ∘ gmultiset_car)) <$> 
      (map_to_list hg :> list (positive * (T * gmultiset positive))))
    (prod_map id (prod_map id (map_to_list (M:=gmap positive positive) ∘ gmultiset_car)) <$> 
      (map_to_list hg' :> list (positive * (T * gmultiset positive))))
    mhe_mv.

Definition spgraph_isos' {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  list (Piso * Piso) :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    default []
      (mv ← pupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
      Some
      (sphyperedge_map_isos_extending' cohg.(sphedges).(sphyperedges)
        cohg'.(sphedges).(sphyperedges) (∅, mv)))
  else
    [].

End alt.

Example ocm_example'' : forall n,
  Z 1 n 0 ⟷ example_Z_stack n ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ example_Z_stack_rev n ⟷ Z n 1 0.
Proof.
  intros n.
  assert (n = 7) by admit.
  subst.
  
  apply ZX_propeq_of_spgraph_equiv.

    (* apply spgraph_test_isomorphism_quote. *)
  Time unshelve (notypeclasses refine (spgraph_test_isomorphism_quote _ _ _ _ _ _ _ _
    _ _ _ _); [cbn; apply _..|]); [apply nil|];
  remember (@spgraph_iso_partial_test _ _ _) as f eqn:Hf;
  vm_compute;
  subst f.
  unfold spgraph_iso_partial_test.
  replace @spgraph_isos with @spgraph_isos' by admit.
  Time vm_compute.
  replace @spgraph_isos with @spgraph_isos' by admit.

  vm_compute.
  done.
Qed.
  Time zx_ocm. *)
