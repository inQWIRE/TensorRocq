Require Export AbstractTensorQuote ZXGraph SPTensorGraph
  VyZXSPHyperGraph AProp SPIsomorphismTestingAlt.

Fixpoint zx2aprop {n m} (zx : ZX n m) : AProp ZXVERT n m :=
  match zx with
  | ZXCore.Empty => Aid 0
  | Cup => Acup 1
  | Cap => Acap 1
  | Wire => Aid 1
  | Swap => Aswap 1 1
  | Box => Agen None 1 1
  | Z_Spider n m α => Agen (Some (false, α)) n m
  | X_Spider n m α => Agen (Some (true, α)) n m
  | Compose zx0 zx1 => Acompose (zx2aprop zx0) (zx2aprop zx1)
  | Stack zx0 zx1 => Astack (zx2aprop zx0) (zx2aprop zx1)
  end.

Lemma zx2aprop_correct {n m} (zx : ZX n m) :
  AProp_semantics (zx2aprop zx) ≡ ZX_tensor_semantics zx.
Proof.
  induction zx; [done..| | | | |].
  - cbn.
    rewrite h_stack1'_11.
    done.
  - done.
  - done.
  - cbn.
    now apply stack_tensor_mor.
  - cbn.
    now apply compose_tensor_mor.
Qed.

(* #[export] Instance TensorLikeHom_interp_discrete_hg_inhab
  `{Inhabited T, Equiv T, Equivalence T equiv}
  `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A, EqA : EqDecision A, WFA : WFSummable A}
  `{TensT : !TensorLike R A T} (ctx : list T) :
  TensorLikeHom R A (interp_discrete_hg_inhab ctx). *)

Lemma ZX_isomorphism_correct ctx {n m} (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  norm_spverts (AProp_spgraph_semantics ap) ≡
    norm_spverts (AProp_spgraph_semantics ap') ->
  zx ∝= zx'.
Proof.
  intros Hzx Hzx' Heq%(APropQuote_correct_spisomorphic interp_discrete_hg_inhab ctx (T':=ZXVERT)
    ap ap' (zx2aprop zx)
      (zx2aprop zx') Hzx Hzx').
  rewrite 2 zx2aprop_correct in Heq.
  apply matrix_of_tensor_of_equiv in Heq.
  rewrite 2 ZX_tensor_semantics_correct in Heq.
  now prep_matrix_equivalence.
Qed.

Require Import SPIsomorphismTesting.

Lemma ZX_isomorphism_correct' ctx {n m} apvm apvm' (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  apvm = (AProp_spgraph_semantics ap) -> apvm' = (AProp_spgraph_semantics ap') ->
  spgraph_iso_partial_test apvm apvm' = true ->
  zx ∝= zx'.
Proof.
  intros Hzx Hzx' -> -> Heq%spgraph_iso_partial_test_correct.
  revert Hzx Hzx' Heq.
  apply ZX_isomorphism_correct.
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
  unshelve (refine (ZX_isomorphism_correct _ _ _ _ _ _ _ _);
  [cbn; apply _..|]); [apply nil|].
  apply spgraph_iso_partial_test_correct.
  Time vm_compute; done.
Qed.

Local Open Scope nat_scope.

Fixpoint example_Z_stack_prf (n : nat) : S n = n + 1 :=
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



(* Goal True.

assert (forall n,
  match (partial_permutations_fast (fun _ _ => True) (seq 0 n) (seq 0 n))
  with | [] => false
  | _ :: _ => true
  end = true).
intros n.
remember @partial_permutations_fast as f eqn:Heqf.
vm_compute in Heqf.
subst f.
remember (seq 0 n) as l eqn:Hl.
vm_compute.
(* cbn. *)
(* vm_compute. *)
assert (n = 200) as -> by admit.
vm_compute in Hl.
Time subst l.


Time lazy.
Time vm_compute.
subst.
vm_compute.
induction (eq_sym Heq).
Time vm_compute.
assert (n = 300) as -> by admit.
Time vm_compute.
assert (n = 200) as -> by admit.
Time vm_compute.
assert (n = 100) as -> by admit.
Time vm_compute.
 *)



Lemma ZX_isomorphism_correct'' ctx {n m} apvm apvm' (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  apvm = (AProp_spgraph_semantics ap) -> apvm' = (AProp_spgraph_semantics ap') ->
  spgraph_iso_partial_test' apvm apvm' = true ->
  zx ∝= zx'.
Proof.
  intros Hzx Hzx' -> -> Heq%spgraph_iso_partial_test'_correct%(APropQuote_correct_spisomorphic interp_discrete_hg_inhab ctx (T':=ZXVERT)
    ap ap' (zx2aprop zx)
      (zx2aprop zx') Hzx Hzx').
  rewrite 2 zx2aprop_correct in Heq.
  apply matrix_of_tensor_of_equiv in Heq.
  rewrite 2 ZX_tensor_semantics_correct in Heq.
  now prep_matrix_equivalence.
Qed.


Lemma ZX_isomorphism_correct_fast ctx {n m} apvm apvm' (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  apvm = (AProp_spgraph_semantics ap) -> apvm' = (AProp_spgraph_semantics ap') ->
  spgraph_iso_partial_test_fast apvm apvm' = true ->
  zx ∝= zx'.
Proof.
  intros Hzx Hzx' -> -> Heq%spgraph_iso_partial_test_fast_correct%(APropQuote_correct_spisomorphic interp_discrete_hg_inhab ctx (T':=ZXVERT)
    ap ap' (zx2aprop zx)
      (zx2aprop zx') Hzx Hzx').
  rewrite 2 zx2aprop_correct in Heq.
  apply matrix_of_tensor_of_equiv in Heq.
  rewrite 2 ZX_tensor_semantics_correct in Heq.
  now prep_matrix_equivalence.
Qed.

Lemma ZX_isomorphism_correct_fast' ctx {n m} apvm apvm' (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  apvm = (AProp_spgraph_semantics ap) -> apvm' = (AProp_spgraph_semantics ap') ->
  spgraph_iso_partial_test_fast' apvm apvm' = true ->
  zx ∝= zx'.
Proof.
  rewrite spgraph_iso_partial_test_fast'_correct.
  intros Hzx Hzx' -> -> Heq%spgraph_iso_partial_test_fast_correct%(APropQuote_correct_spisomorphic interp_discrete_hg_inhab ctx (T':=ZXVERT)
    ap ap' (zx2aprop zx)
      (zx2aprop zx') Hzx Hzx').
  rewrite 2 zx2aprop_correct in Heq.
  apply matrix_of_tensor_of_equiv in Heq.
  rewrite 2 ZX_tensor_semantics_correct in Heq.
  now prep_matrix_equivalence.
Qed.


Lemma ZX_isomorphism_correct_fast'' ctx {n m} apvm apvm' (ap ap' : AProp positive n m)
  (zx zx' : ZX n m) :
  APropQuote interp_discrete_hg_inhab ctx ap (zx2aprop zx) ->
  APropQuote interp_discrete_hg_inhab ctx ap' (zx2aprop zx') ->
  apvm = (AProp_spgraph_semantics ap) -> apvm' = (AProp_spgraph_semantics ap') ->
  spgraph_iso_partial_test_fast'' apvm apvm' = true ->
  zx ∝= zx'.
Proof.
  intros Hzx Hzx' -> -> Heq%spgraph_iso_partial_test_fast''_correct%(APropQuote_correct_spisomorphic interp_discrete_hg_inhab ctx (T':=ZXVERT)
    ap ap' (zx2aprop zx)
      (zx2aprop zx') Hzx Hzx').
  rewrite 2 zx2aprop_correct in Heq.
  apply matrix_of_tensor_of_equiv in Heq.
  rewrite 2 ZX_tensor_semantics_correct in Heq.
  now prep_matrix_equivalence.
Qed.

Ltac quote_discrete :=
  lazymatch goal with
  | |- APropQuote interp_discrete_hg_inhab ?ctx _ ?t =>
    notypeclasses refine (abstens_quote_discrete_inhab ctx _ t _);
    get_nth
  | |- APropQuote interp_discrete_hg ?ctx _ ?t =>
    notypeclasses refine (abstens_quote_discrete ctx _ t _);
    get_nth
  end.

Ltac quote_AP :=
  lazymatch goal with
  | |- APropQuote ?f ?ctx _ ?apv =>
    lazymatch apv with
    | Agen ?t ?n ?m =>
      notypeclasses refine (aprop_quote_gen f ctx _ t n m _);
      first [quote_discrete|typeclasses eauto|idtac]
    | Acompose ?apv1 ?apv2 =>
      notypeclasses refine (aprop_quote_compose f ctx _ _ apv1 apv2 _ _);
      quote_AP
    | Astack ?apv1 ?apv2 =>
      notypeclasses refine (aprop_quote_stack f ctx _ _ apv1 apv2 _ _);
      quote_AP
    | Aid ?n => notypeclasses refine (aprop_quote_id f ctx n)
    | Acup ?n => notypeclasses refine (aprop_quote_cup f ctx n)
    | Acap ?n => notypeclasses refine (aprop_quote_cap f ctx n)
    | Aswap ?n ?m => notypeclasses refine (aprop_quote_swap f ctx n m)
    end
  end.

Example ocm_example'' : forall n,
  Z 1 n 0 ⟷ n_stack1 n (Z 1 1 0) ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ n_stack1 n (Z 1 1 0) ⟷ Z n 1 0.
Proof.
  intros n.
  (* assert (n = 20) by admit.
  subst.
  Time unshelve (refine (ZX_isomorphism_correct_fast'' _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  Undo 3. *)
  done.
Qed.

From VyZX Require Import ZXpermFacts ZXRules CastRules DiagramRules ComposeRules.

Example ocm_example''' : forall n,
  Z 1 n 0 ⟷ example_Z_stack n ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ example_Z_stack_rev n ⟷ Z n 1 0.
Proof.
  intros n.
  (* assert (n = 20%nat) by admit.
  subst.
  Time unshelve (refine (ZX_isomorphism_correct_fast'' _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  Undo 3. *)
  rewrite <- (Z_zx_of_perm_absorbtion_right 1 n 0 (reflect_perm n)) at 1.
  rewrite <- (Z_zxperm_absorbtion_left n n 1 0 (zx_of_perm n (reflect_perm n))) at 1
    by auto_zxperm.
  rewrite 3 compose_assoc.
  f_equiv.
  rewrite <- 2 compose_assoc.
  f_equiv.
  induction n; [now cbn; rewrite zx_of_perm_0, 2 compose_empty_l|].
  cbn.
  rewrite cast_compose_r, cast_zx_of_perm_nonsquare.
  rewrite (stack_comm (Z 1 1 (INR n))).
  rewrite <- IHn.
  rewrite cast_compose_l, cast_zx_of_perm_nonsquare.
  rewrite <- (nwire_removal_r (Z 1 1 _)) at 2.
  rewrite stack_compose_distr.
  rewrite <- (nwire_removal_l (Z 1 1 _)) at 2.
  rewrite stack_compose_distr.
  rewrite cast_id.
  symmetry.
  rewrite <- 2 compose_assoc, compose_assoc.
  f_equiv; [f_equiv|].
  - by_perm_eq_nosimpl.
    cbn -[Nat.add n_wire].
    rewrite perm_of_zx_comm, perm_of_zx_of_perm_eq_WF by auto_perm.
    rewrite perm_of_n_wire.
    rewrite perm_of_zx_of_perm_cast_eq by auto_perm.
    rewrite (reflect_perm_defn (S n)).
    rewrite Nat.add_comm.
    erewrite stack_perms_proper_eq by 
      first [apply reflect_perm_defn|apply perm_eq_refl].
    rewrite big_swap_perm_defn, stack_perms_defn.
    intros k Hk.
    cbn.
    bdestruct (k <? n); bdestruct_one; lia.
  - by_perm_eq_nosimpl.
    cbn -[Nat.add n_wire].
    rewrite perm_of_zx_comm, perm_of_zx_of_perm_eq_WF by auto_perm.
    rewrite perm_of_n_wire.
    rewrite perm_of_zx_of_perm_cast_eq by now rewrite Nat.add_comm; auto_perm.
    rewrite reflect_perm_defn.
    rewrite stack_perms_defn, Nat.add_comm, big_swap_perm_defn,
      reflect_perm_defn.
    intros k Hk.
    cbn.
    bdestruct (k <=? 0); bdestruct_one; lia.
Qed.
(* 
Example ocm_example'' : forall n,
  Z 1 n 0 ⟷ n_stack1 n (Z 1 1 0) ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ n_stack1 n (Z 1 1 0) ⟷ Z n 1 0.
Proof.
  intros n.
  assert (n = 20) by admit.
  subst.
  Time unshelve (refine (ZX_isomorphism_correct_fast' _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  Time unshelve (refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  ].
  unfold spgraph_iso_partial_test_fast.
  unfold spgraph_isos_fast.
  rewrite decide_True by compute_done.
  cbn [spinputs spoutputs sphedges].
  remember (pupdates _ _) as pu eqn:Hpu.
  vm_compute in Hpu.
  subst pu.
  cbn [mbind option_bind].
  unfold maybe_vertex_map.
  remember (partial_permutations _ _ _) as pp eqn:Hpp.
  assert (match pp with | [] => false | _ :: _ => true end = true). 1:{
    subst pp.
    (* remember (@partial_permutations) as f eqn:Hf.
    vm_compute in Hf.
    subst f. *)
    Time vm_compute.
    Time compute_done.
  }
  refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|].
  remember @spgraph_iso_partial_test_fast as f eqn:Hf.
  Notation "'!EQ'" := (eq _ _) (only printing).
  Timeout 10 vm_compute in Hf.
  subst f.
  Time unshelve (refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].


Example ocm_example'' : forall n,
  Z 1 n 0 ⟷ example_Z_stack n ⟷ Z n 1 0 ∝=
  Z 1 n 0 ⟷ example_Z_stack_rev n ⟷ Z n 1 0.
Proof.
  intros n.
  assert (n = 30) by admit.
  subst.
  Time unshelve (refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn -[INR]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn [zx2aprop example_Z_stack example_Z_stack_rev example_Z_stack_prf cast f_equal];
    quote_AP..| | |].
  Time unshelve (refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn [zx2aprop]; quote_AP..| | |]; [time vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  Time unshelve (refine (ZX_isomorphism_correct_fast _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn; apply _..| | |]; [vm_compute; reflexivity..|]); [apply nil|
  time vm_compute; done].
  Time unshelve (refine (ZX_isomorphism_correct'' _ _ _ _ _ _ _ _ _ _ _ _);
  [cbn; apply _..| | |]; [vm_compute; reflexivity..|]); [apply nil|vm_compute; done].



  unshelve (refine (ZX_isomorphism_correct _ _ _ _ _ _ _ _);
  [cbn; apply _..|]); [apply nil|].
  apply spgraph_iso_partial_test_correct.
  remember (AProp_spgraph_semantics _) as x eqn:Hx.
  remember (@spgraph_iso_partial_test _ _ _) as f eqn:Hf.
  Time vm_compute; subst f; vm_compute; done.
  Time vm_compute; done.

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