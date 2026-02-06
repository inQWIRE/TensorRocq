Require Export Tensor ZXCore.
From VyZX Require Export CoreData.


Fixpoint ZX_tensor_semantics {n m} (zx : ZX n m) : @Tensor C n m bool :=
  match zx with 
  | ⦰ => delta_tensor
  | ⊂ => cup_tensor (n:=1)
  | ⊃ => cap_tensor (n:=1)
  | ⨉ => swap_tensor (n:=1) (m:=1)
  | — => delta_tensor
  | □ => h_stack
  | X n m α => xsp α
  | Z n m α => zsp α
  | zx0 ↕ zx1 => stack_tensor (ZX_tensor_semantics zx0) (ZX_tensor_semantics zx1)
  | zx0 ⟷ zx1 => compose_tensor (ZX_tensor_semantics zx0) (ZX_tensor_semantics zx1)
  end.

(* 
Open Scope ZX_scope.

Open Scope nat_scope.

Example example_graph'_semantics : forall b b',
  graph_semantics example_graph'
    [#] [#b;b'] =
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_semantics].
  unfold kron.
  cbn -[graph_semantics].
  intros [] []; cbn -[graph_semantics]; (etransitivity;
    [unfold example_graph', ZXCALC;

      remember @zsp as zsp' eqn:Hzsp;
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp];
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed. *)