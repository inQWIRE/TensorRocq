From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.

From TensorRocqEx Require Import VyZXExample_withdiags.


Import ZXsymm ZXauto ZXfrob.


Import ZXmsymm.
  Import SizedProQuote.
  Import SizedRewriting SizedProLike.
  Import SizedPropsGraphs PropsGraphs.

Import BW.

Import ComposeRules.

Open Scope nat_scope.

Ltac visualize_flag ::= fail.


From TensorRocqEx Require Export NonZXAux.

From TensorRocqEx Require Export SZXAux.








From TensorRocq Require Import Matrix.

From TensorRocqEx Require Export MatrixAux.

Import prf_notations.



Definition b2zx (b : bool) : ZX 1 1 :=
  if b then — else zx_invsqrt2 ↕ (Z 1 0 0 ⟷ X 0 1 0).

Definition b2zx' (b : bool) : ZX 1 1 :=
  if b then — else Z 1 0 0 ⟷ X 0 1 0.


Lemma b2zx'_to_b2zx b : (√ 2 ^ Nat.b2n b) .* b2zx' b ∝= √ 2 .* b2zx b.
Proof.
  destruct b; cbn.
  - rewrite Cmult_1_r.
    done.
  - rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_assoc, zx_scale_eq_1_l by C_field.
    now rewrite stack_empty_l.
Qed.

Lemma b2zx_to_b2zx' b : b2zx b ∝= (√ 2 ^ Nat.b2n b) / √ 2 .* b2zx' b.
Proof.
  pose proof (b2zx'_to_b2zx b) as Hrw.
  rewrite zx_scale_eq_r in Hrw by nonzero.
  rewrite <- Hrw.
  distribute_zxscale.
  f_equiv; C_field.
Qed.

Lemma b2zx_compose b c :
  b2zx b ⟷ b2zx c ∝= b2zx (b && c).
Proof.
  destruct b.
  - cbn.
    rewrite wire_removal_l.
    now destruct c.
  - cbn.
    destruct c.
    + cbn.
      now rewrite wire_removal_r.
    + cbn.
      zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
      rewrite const_of_zx_X_0_1_0_Z_1_0_0.
      rewrite (gadget_is_scaled_empty zx_invsqrt2).
      rewrite const_of_zx_invsqrt2.
      rewrite zx_of_const_to_scaled_empty.
      distribute_zxscale.
      apply zx_scale_simplify_eq; [C_field|].
      zxscat.
Qed.

Lemma b2zx_compose' b c :
  b2zx b ⟷ b2zx c ∝= b2zx (c && b).
Proof.
  rewrite b2zx_compose, andb_comm.
  done.
Qed.

Lemma b2zx_plus b c :
  Z 1 2 0 ⟷ (b2zx b ↕ b2zx c) ⟷ X 2 1 0 ∝=
  / √ 2 .* b2zx (b ⊕ c).
Proof.
  destruct b, c; cbn.
  - zxsrw (to_gadget hopf_rule_Z_X).
    rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    rewrite zx_of_const_to_scaled_empty.
    distribute_zxscale.
    rewrite zx_scale_assoc.
    apply zx_scale_simplify_eq; [C_field|zxscat].
  - rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_r, zx_scale_compose_distr_r, zx_scale_compose_distr_l.
    apply zx_scale_simplify_eq; [done|].
    rewrite !X_to_Z.
    zxfrw box_compose.
    rewrite box_compose.
    done.
  - rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_l, zx_scale_compose_distr_r, zx_scale_compose_distr_l.
    apply zx_scale_simplify_eq; [done|].
    rewrite !X_to_Z.
    zxfrw box_compose.
    rewrite box_compose.
    done.
  - zxsrw <- (@X_add_l 0 0 1 0 0 0).
    rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    zxfcat.
Qed.

Lemma b2zx_plus' b c :
  √2 .* (Z 1 2 0 ⟷ (b2zx b ↕ b2zx c) ⟷ X 2 1 0) ∝=
  b2zx (b ⊕ c).
Proof.
  rewrite b2zx_plus, zx_scale_assoc, Cinv_r, zx_scale_1_l by nonzero.
  done.
Qed.

Lemma b2zx_copy b : b2zx b ⟷ Z 1 2 0 ∝= Z 1 2 0 ⟷ (b2zx b ↕ b2zx b).
Proof.
  destruct b; cbn.
  - zxscat.
  - zxsrw (to_gadget (X_state_copy'' false 2 0 eq_refl eq_refl)).
    cbn.
    rewrite Cmult_1_r, zx_of_const_invsqrt2.
    zxfcat.
Qed.

Lemma b2zx_erase b : b2zx b ⟷ Z 1 0 0 ∝= Z 1 0 0.
Proof.
  destruct b; [zxscat|].
  cbn.
  zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_of_const_invsqrt2.
  rewrite <- zx_of_const_mult', Cinv_r, zx_of_const_1; [zxscat|nonzero].
Qed.

Lemma b2zx_hadamard b : b2zx b ⟷ □ ∝= □ ⟷ transpose (b2zx b).
Proof.
  destruct b; [zxscat|].
  cbn.
  rewrite gadget_transpose.
  rewrite <- (colorswap_involutive (Z 1 0 0 ⟷ X 0 1 0)), colorswap_is_bihadamard.
  cbn.
  zxsrw box_compose.
  zxscat.
Qed.

Import MatrixAux ComposeRules vector Tensors.Matrix.
Notation Cpow_inv := NonZXAux.Cpow_inv.

Fixpoint zx_binmat_aux_r {n} : forall (A : vec bool (S n)), ZX (S n) 1 :=
  match n with
  | 0 => fun A => b2zx (vhd A)
  | S n =>
    fun A =>
    (Z 0 1 0 ⟷ X 1 0 0) ↕ (b2zx (vhd A) ↕ zx_binmat_aux_r (vtl A) ⟷ X 2 1 0)
  end.

Fixpoint zx_binmat_aux_l {m n} : forall (A : Matrix bool (S m) (S n)), ZX (S n) (S m) :=
  match m with
  | 0 => fun A => zx_binmat_aux_r (vhd A)
  | S m =>
    fun A =>
    ZX_bcopy (S n) (!()) (!() + !()) (Z 1 2 0) ⟷
     (zx_binmat_aux_r (vhd A) ↕ zx_binmat_aux_l (vtl A))
  end.



Definition zx_binmat {m n} (A : Matrix bool m n) : ZX n m :=
  match n, m, A with
  | 0, 0, _ => ⦰
  | 0, S m, _ => (* TODO: What goes here? Any phase tricks? *)
    ZX_bcopy (S m) 0 (!()) (zx_invsqrt2 ↕ X 0 1 0)
  | S n, 0, _ =>
    ZX_bcopy (S n) (!()) 0 (Z 1 0 0)
  | S n, S m, A => zx_binmat_aux_l A
  end.

Typeclasses Opaque Matrix.

#[export] Instance zx_binmat_proper n m : Proper (equiv ==> eq) (@zx_binmat n m).
Proof.
  intros A A' HA.
  f_equal.
  apply mx_eq.
  rewrite mx_equiv in HA.
  done.
Qed.

Definition mx_weight {m n} (A : Matrix bool m n) : nat :=
  sum_list_with (sum_list_with Nat.b2n ∘ vec_to_list) (vec_to_list A).


Definition mx_biadj {m n} (A : Matrix bool m n) : ZX (m * n) (m * n) :=
  n_stackv (λ row, cast _ _ mul_1_r' mul_1_r' (n_stackv b2zx' row)) A.

Lemma mx_biadj_alt {m n} (A : Matrix bool m n) :
  mx_biadj A ∝=
  cast _ _ mul_1_r' mul_1_r' $ n_stackv b2zx' (vjoin A).
Proof.
  induction A; [zxscat|].
  cbn.
  rewrite n_stackv_vapp.
  rewrite cast_contract_eq'.
  auto_cast_eqn rewrite cast_stack_distribute.
  f_equiv; [cast_irrelevance|].
  rewrite IHA.
  cast_irrelevance.
Qed.


Lemma mx_biadj_0_r {m} (A : vec (vec bool 0) m) :
  mx_biadj A ∝= cast _ _ (Nat.mul_0_r _) (Nat.mul_0_r _) ⦰.
Proof.
  induction A; [cbn; zxscat|].
  cbn.
  rewrite IHA.
  (* Suffices: 
  inv_all_vec_fin; 
  cbn; zxpscat. *)
  rewrite cast_id, stack_empty_l.
  cast_irrelevance.
Qed.



Lemma zx_binmat_alt_aux_l {m n} (A : vec (vec bool (S n)) (S m)) :
  zx_binmat_aux_l A ∝=
  (√2 ^ mx_weight A / √ 2 ^ S m) .*
  cast _ _ mul_1_r' mul_1_r'
  (S n ⇑ Z 1 (S m) 0 ⟷ zx_mul_comm _ _ ⟷
    mx_biadj A ⟷
      S m ⇑ X (S n) 1 0).
Proof.
  induction m as [[|m] IHm] using lt_wf_ind.
  - clear IHm.
    cbn [zx_binmat_aux_l].
    inv_vec A.
    intros A.
    cbn [vhd Vector.caseS].
    rewrite zx_mul_comm_1_r.
    rewrite Z_is_wire, wire_to_n_wire.
    rewrite n_stack_n_wire.
    rewrite nwire_removal_l, compose_assoc, n_wire_removal_l', cast_contract_eq'.
    rewrite n_stack_1.
    rewrite mx_biadj_alt.
    rewrite cast_X.
    rewrite cast_compose_l, cast_X, cast_contract_eq'.
    cbn [vjoin].
    rewrite (n_stackv_vapp b2zx' A [#]).
    change (n_stackv _ [#]) with ⦰.
    rewrite stack_empty_r_fwd, cast_contract_eq'.
    rewrite cast_compose_l, cast_X, cast_contract_eq'.
    induction n.
    + rewrite X_is_wire, wire_removal_r.
      cbn.
      inv_all_vec_fin.
      cbn.
      rewrite b2zx_to_b2zx'.
      cbn.
      rewrite 2 (Nat.add_0_r (Nat.b2n _)), Cmult_1_r.
      zxscat.
    + cbn [zx_binmat_aux_r].
      induction A as [h A] using vec_S_inv.
      cbn [vhd vtl Vector.caseS].
      rewrite IHn.
      clear IHn.
      rewrite <- zx_scale_sqrt2_alt.
      distribute_zxscale.
      rewrite n_stackv_vcons.
      rewrite b2zx_to_b2zx'.
      distribute_zxscale.
      apply zx_scale_simplify_eq.
      1:{
        cbn.
        rewrite 2 Nat.add_0_r, Cpow_add_r.
        C_field.
      }
      (* Ltac enable_timing ::= idtac. *)
      (* Set Typeclasses Debug.
      let lem := constr:(dominated_X_spider_fusion_bot_right (S n * 1) 0 1 1 0 0) in 
      let match_number := constr:(O) in 
      let Hrw := fresh "Hrw" in
      let le := fresh "le" in evar (le : list ZXDVERT);
      zxpsrw_lhs_setup Hrw le;
      zxpsrw_lhs_parse Hrw lem match_number;
      zxpsrw_lhs_quotes Hrw.
      zxpsrw_lhs_to_pos Hrw.
      let ln := fresh "ln" in evar (ln : list nat);
      zxpsrw_lhs_to_sized Hrw ln.
      zxpsrw_lhs_compute Hrw.
      zxpsrw_lhs_from_sized Hrw.
      zxpsrw_lhs_from_pos Hrw.
      zxpsrw_lhs_denote Hrw.
      zxpsrw_lhs_final Hrw le ln. *)
      zxpsrw (dominated_X_spider_fusion_bot_right (S n * 1) 0 1 1 0 0).
      zxpscat.
      (* zxpscat. *)
  - cbn [zx_binmat_aux_l].
    induction A as [v A] using vec_S_inv.
    cbn [vhd vtl Vector.caseS].
    rewrite (IHm 0 ltac:(lia) [#v]).
    rewrite IHm by lia.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_r.
    apply zx_scale_simplify_eq.
    1:{
      cbn.
      rewrite Nat.add_0_r.
      rewrite Cpow_add_r.
      unfold mx_weight.
      C_field.
    }
    rewrite 2 (n_stack_to_ZX_copy _ (Z _ _ _)).
    rewrite zx_mul_comm_1_r.
    rewrite 2 n_wire_removal_l'.

    rewrite !cast_compose_distribute, !cast_contract_eq', !cast_id_eq.
    rewrite !stack_compose_distr.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, cast_contract_eq'.
    rewrite ZX_copy_stack_back, cast_contract_eq'.
    unfold ZX_bcopy.
    rewrite <- !compose_assoc.
    rewrite cast_compose_eq_mid_join.
    rewrite <- ZX_copy_compose.
    rewrite <- Z_add_r.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    2:{
      rewrite cast_stack_r_fwd, cast_contract_eq'.
      cbn -[cast].
      rewrite stack_empty_r_fwd, cast_stack_l_fwd, cast_contract_eq'.
      cast_irrelevance.
    }
    rewrite cast_compose_distribute, cast_id.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    2:{
      unfold mx_biadj.
      rewrite 2 n_stackv_vcons, n_stackv_vnil, stack_empty_r_fwd, 2 cast_contract_eq'.
      rewrite 2 cast_stack_l_fwd, cast_contract_eq'.
      cast_irrelevance.
    }
    rewrite compose_assoc, cast_compose_distribute, cast_contract_eq'.

    unfold ZX_copy.
    cbn [bsize btree_size].
    rewrite zx_mul_comm_1_l.
    rewrite n_wire_removal_l'.
    rewrite cast_compose_distribute, cast_contract_eq', compose_assoc.
    rewrite 2 Rplus_0_l.
    f_equiv; [cast_irrelevance|].
    rewrite <- stack_compose_distr.
    rewrite n_wire_removal_l', cast_contract_eq', cast_n_wire.
    rewrite zx_mul_comm_cancel.
    rewrite n_wire_stack.
    rewrite nwire_removal_r.
    cast_irrelevance.
Qed.


Lemma zx_binmat_alt {m n} (A : vec (vec bool n) m) :
  zx_binmat A ∝=
  (√2 ^ mx_weight A / √ 2 ^ m) .*
  cast _ _ mul_1_r' mul_1_r'
  (n ⇑ Z 1 m 0 ⟷ zx_mul_comm _ _ ⟷
    mx_biadj A ⟷
      m ⇑ X n 1 0).
Proof.
  induction m.
  - cbn.
    rewrite cast_compose_r, 3 compose_empty_r, 2 cast_contract_eq'.
    inv_vec A.
    cbn.
    rewrite Cdiv_1_r, zx_scale_1_l.
    destruct n.
    + cbn.
      zxscat.
    + cbn -[n_stack].
      unfold ZX_bcopy.
      cbn -[n_stack].
      unfold ZX_copy.
      rewrite zx_mul_comm_0_r, cast_compose_r, compose_empty_r, 2 cast_contract_eq'.
      rewrite zx_mul_comm_1_l, cast_compose_l, nwire_removal_l, 2 cast_contract_eq'.
      cast_irrelevance.
  - destruct n.
    + cbn [zx_binmat].
      replace (mx_weight A) with 0. 2:{
        unfold mx_weight.
        symmetry.
        induction A; cbn; inv_all_vec_fin; cbn; lia.
      }
      rewrite mx_biadj_0_r.
      rewrite zx_mul_comm_0_l.
      change (0 ⇑ _) with ⦰.
      rewrite compose_empty_l.
      rewrite cast_compose_eq_mid_join, compose_empty_l.
      rewrite cast_compose_l, compose_empty_l, 2 cast_contract_eq'.
      change (_ ^ 0)%C with C1.
      unfold Cdiv; rewrite Cmult_1_l.
      rewrite <- Cpow_inv.
      rewrite <- zx_scale_cast.
      generalize (S m) as m'.
      clear.
      intros m.
      unfold ZX_bcopy.
      cbn.
      unfold ZX_copy.
      rewrite zx_mul_comm_0_l, zx_mul_comm_1_r.
      rewrite cast_compose_l, compose_empty_l, cast_compose_r,
        nwire_removal_r, 4 cast_contract_eq'.
      cast_irrelevance.
      induction m.
      * cbn.
        rewrite zx_scale_1_l.
        done.
      * cbn.
        rewrite IHm.
        rewrite (gadget_is_scaled_empty zx_invsqrt2).
        rewrite const_of_zx_invsqrt2.
        rewrite 2 zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
        rewrite stack_empty_l.
        done.
    + apply zx_binmat_alt_aux_l.
Qed.




Lemma zx_binmat_cast {n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix bool n m) :
  zx_binmat (cast_matrix Hn Hm A) =
  cast _ _ (eq_sym Hm) (eq_sym Hn) (zx_binmat A).
Proof.
  subst.
  rewrite cast_matrix_id, cast_id_eq.
  done.
Qed.

Lemma zx_binmat_0_l n A : @zx_binmat 0 n A ∝= ZX_bcopy n (!()) 0 (Z 1 0 0).
Proof.
  destruct n.
  - cbn.
    rewrite ZX_bcopy_0, cast_id.
    done.
  - cbn.
    done.
Qed.

Lemma zx_binmat_0_r m A : @zx_binmat m 0 A ∝= ZX_bcopy m 0 (!()) (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  destruct m.
  - cbn.
    rewrite ZX_bcopy_0, cast_id.
    done.
  - cbn.
    done.
Qed.


Lemma zx_binmat_aux_l_vblock {n n' m} (A : Matrix bool (S n) (S m)) (B : Matrix bool (S n') (S m)) :
  zx_binmat_aux_l (mx_vblock A B) ∝=
  ZX_bcopy (S m) (!()) (!() + !()) (Z 1 2 0) ⟷
  (zx_binmat_aux_l A ↕ zx_binmat_aux_l B).
Proof.
  induction n; [inv_vec A; done|].
  cbn [zx_binmat_aux_l].
  rewrite vtl_mx_vblock.
  rewrite IHn.
  rewrite <- (nwire_removal_l (zx_binmat_aux_r _)).
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  rewrite <- (ZX_bcopy_n_wire (S m) (!())).
  rewrite <- (@ZX_bcopy_stack (S m) (!()) (!()) (!()) (!() + !())).
  rewrite <- (@ZX_bcopy_compose (S m) (!()) (!() + !()) (!() + (!() + !()))).
  rewrite <- (nwire_removal_l (zx_binmat_aux_l B)) at 2.
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  rewrite <- (ZX_bcopy_n_wire (S m) (!())).
  rewrite <- (@ZX_bcopy_stack (S m) (!()) (!() + !()) (!()) (!())).
  rewrite <- (@ZX_bcopy_compose (S m) (!()) (!() + !()) ((!() + !()) + !())).
  rewrite (stack_assoc_fwd (zx_binmat_aux_r (vhd A)) (zx_binmat_aux_l (vtl A)) (zx_binmat_aux_l B)).
  rewrite cast_compose_r, cast_compose_distribute, 2 cast_id.
  f_equiv; [|now inv_vec A].
  unfold ZX_bcopy.
  rewrite cast_contract_eq'.
  cast_irrelevance.
  f_equiv.
  zxfcat.
Qed.

Lemma zx_binmat_vblock {n n' m} (A : Matrix bool n m) (B : Matrix bool n' m) :
  zx_binmat (mx_vblock A B) ∝=
  ZX_bcopy m (!()) (!() + !()) (Z 1 2 0) ⟷
  (zx_binmat A ↕ zx_binmat B).
Proof.
  destruct n'. 1:{
    inv_vec B.
    rewrite mx_vblock_nil_r.
    rewrite zx_binmat_cast.
    rewrite <- nwire_removal_l.
    rewrite stack_split_antidiag, <- compose_assoc.
    apply compose_simplify_casted_abs; [lia|intros..];
    [|rewrite stack_empty_r_fwd, cast_contract_eq'; cast_irrelevance].
    clear.
    rewrite (proof_irrel _ add_0_r').
    clear Hm'.
    rewrite zx_binmat_0_l.
    rewrite <- (ZX_bcopy_n_wire m (!())).
    rewrite <- (@ZX_bcopy_stack m (!()) (!()) (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (!() + 0)).
    rewrite ZX_bcopy_n_wire.
    unfold ZX_bcopy.
    rewrite cast_contract_eq'.
    rewrite ZX_copy_1_1.
    rewrite (ltac:(zxfcat) : Z 1 2 0 ⟷ (n_wire 1 ↕ Z 1 0 0) ∝= —).
    symmetry.
    fold (n_wire (1 * m)).
    rewrite cast_n_wire.
    done.
  }
  destruct n.
  1:{
    inv_vec A.
    change (mx_vblock _ B) with B.
    rewrite zx_binmat_0_l.
    rewrite stack_split_diag, <- compose_assoc.
    rewrite <- (ZX_bcopy_n_wire m (!())).
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) (!()) ).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + !())).
    rewrite stack_empty_l.
    rewrite (ltac:(zxfcat) : Z 1 2 0 ⟷ (Z 1 0 0 ↕ n_wire 1) ∝= n_wire 1).
    unfold ZX_bcopy.
    rewrite ZX_copy_n_wire, cast_n_wire.
    rewrite nwire_removal_l.
    done.
  }
  destruct m.
  - unfold Matrix in A, B.
    rewrite 3 zx_binmat_0_r.
    unfold ZX_bcopy.
    rewrite 3 (ZX_copy_le_1 _ (zx_invsqrt2 ↕ X 0 1 0)) by lia.
    cbn -[n_stack Nat.add].
    rewrite 3 cast_contract_eq'.
    auto_cast_eqn rewrite <- cast_stack_distribute.
    auto_cast_eqn rewrite nstack_split, cast_contract_eq'.
    rewrite ZX_copy_0.
    rewrite cast_contract_eq', n_wire_removal_l', cast_contract_eq'.
    cast_irrelevance.
  - apply zx_binmat_aux_l_vblock.
Qed.



Lemma zx_binmat_aux_r_app {m m'} (vA : vec bool (S m)) (vB : vec bool (S m')) :
  zx_binmat_aux_r (vA +++ vB) ∝=
  zx_binmat_aux_r vA ↕ zx_binmat_aux_r vB ⟷
  ((√ 2) .* X 2 1 0).
Proof.
  induction m.
  - inv_vec vA; intros h.
    cbn.
    rewrite gadget_is_scaled_empty, <- const_of_zx_colorswap.
    simpl.
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    distribute_zxscale.
    apply zx_scale_simplify_eq; [lca|].
    (* FIXME: zxpscat doesn't work here!!! *)
    rewrite stack_empty_l.
    done.
  - induction vA as [a vA] using vec_S_inv.
    cbn.

    rewrite gadget_is_scaled_empty, <- const_of_zx_colorswap.
    simpl.
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite IHm.
    rewrite 2 zx_scale_compose_distr_r, 3 zx_scale_stack_distr_l,
      zx_scale_stack_distr_r, 2 stack_empty_l, 2 zx_scale_compose_distr_l.
    rewrite 2 zx_scale_assoc.
    apply zx_scale_simplify_eq; [cbn; C_field|].
    rewrite stack_push_br.
    rewrite stack_push_tr.
    rewrite (stack_assoc_back_fwd (b2zx a) (zx_binmat_aux_r vA) (zx_binmat_aux_r vB)).
    rewrite 2 compose_assoc.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    + cast_irrelevance.
    + rewrite cast_id.
      apply colorswap_diagrams_eq.
      cbn.
      zxfcat.
Qed.


Lemma zx_binmat_aux_l_hblock {n m m'} (A : Matrix bool (S n) (S m)) (B : Matrix bool (S n) (S m')) :
  zx_binmat_aux_l (mx_hblock A B) ∝=
  zx_binmat_aux_l A ↕ zx_binmat_aux_l B ⟷
  ((√ 2 ^ S n) .* ZX_bcopy (S n) (!() + !()) (!()) (X 2 1 0)).
Proof.
  fold Nat.add.
  induction n.
  1:{
    inv_vec A; intros vA.
    inv_vec B; intros vB.
    cbn.
    rewrite zx_binmat_aux_r_app.
    rewrite ZX_bcopy_1, cast_id.
    rewrite Cmult_1_r.
    done.
  }

  induction A as [vA A] using vec_S_inv.
  induction B as [vB B] using vec_S_inv.
  rewrite mx_hblock_cons.
  cbn [zx_binmat_aux_l].
  cbn.
  rewrite IHn.
  rewrite zx_binmat_aux_r_app.
  rewrite stack_compose_distr.
  rewrite stack_compose_distr.
  rewrite (stack_mid_comm (zx_binmat_aux_r vA) (zx_binmat_aux_r vB) (zx_binmat_aux_l A) (zx_binmat_aux_l B)).
  rewrite <- 3 compose_assoc, compose_assoc.
  change (S (?x + S ?y)) with (S x + S y).
  f_equiv; [f_equiv; [|done]|].
  - change (S (?x + S ?y)) with (S x + S y).
    unfold ZX_bcopy.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, cast_contract_eq'.
    auto_cast_eqn rewrite cast_compose_l, cast_backwards_eq.
    symmetry.
    rewrite cast_contract_eq'.
    cbn [bsize].
    unfold ZX_copy.
    rewrite 3 zx_mul_comm_1_l.
    rewrite 3 n_wire_removal_l'.
    rewrite 4 cast_compose_l.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, 3 cast_contract_eq'.
    rewrite stack_compose_distr.
    auto_cast_eqn rewrite nstack_split.
    rewrite compose_assoc, cast_compose_distribute, cast_contract_eq'.
    rewrite 2 cast_compose_distribute.
    apply compose_simplify_casted_abs; [lia|intros ?..];
    [rewrite cast_contract_eq'; cast_irrelevance|].
    rewrite 3 cast_contract_eq'.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, 2 cast_contract_eq'.

    apply prop_eq_of_perm_eq; [auto_zxperm..|].
    cbn [perm_of_zx].
    rewrite 3 perm_of_zx_cast.
    cbn [perm_of_zx].
    rewrite perm_of_zx_mid_comm, 3 perm_of_zx_mul_comm.
    intros i Hi.
    cbn -[Nat.add].
    rewrite stack_perms_defn by lia.
    bdestruct_one.
    2:{
      rewrite stack_perms_right by lia.
      rewrite Nat.sub_add by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite mod_n_to_2n by lia.
      rewrite (fun H => (Kronecker.div_eq_iff i _ 1 H).2) by lia.
      rewrite mod_n_to_2n by lia.
      rewrite (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      lia.
    }
    rewrite stack_perms_defn by lia.
    bdestruct_one.
    1:{
      rewrite stack_perms_left by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite 2 Nat.mod_small, 2 Nat.div_small by lia.
      lia.
    }
    rewrite big_swap_perm_defn by lia.
    bdestruct_one.
    1:{
      rewrite stack_perms_left by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      lia.
    }
    rewrite stack_perms_right by lia.
    rewrite 2 kron_comm_perm_defn by lia.
    rewrite Nat.mod_small, Nat.div_small by lia.
    rewrite Nat.mod_small, Nat.div_small by lia.
    lia.
  - unfold ZX_bcopy.
    rewrite zx_scale_stack_distr_r, zx_scale_stack_distr_l,
       zx_scale_assoc, zx_scale_compose_distr_r.
    apply zx_scale_simplify_eq; [cbn; C_field|].
    rewrite cast_stack_r_fwd, cast_compose_r.
    cbn -[cast Nat.add].
    symmetry.
    auto_cast_eqn rewrite cast_backwards_eq.
    rewrite cast_contract_eq'.
    rewrite cast_compose_distribute, cast_id.
    unfold ZX_copy.
    rewrite 2 zx_mul_comm_1_r.
    rewrite 2 n_wire_removal_r'.
    rewrite cast_stack_r_fwd, cast_compose_eq_mid_join.
    rewrite stack_push_bl.
    rewrite <- compose_assoc.
    auto_cast_eqn rewrite cast_backwards_eq, cast_contract_eq'.
    rewrite cast_compose_distribute, cast_id.
    f_equiv; [|done].

    apply prop_eq_of_perm_eq; [auto_zxperm..|].
    cbn [perm_of_zx].
    rewrite 2 perm_of_zx_cast, perm_of_n_wire.
    rewrite perm_of_zx_mid_comm, 2 perm_of_zx_mul_comm.
    replace (1 + S n + (1 + S n)) with (2 * S (S n)) by lia.
    rewrite kron_comm_perm_2_n_succ_alt.
    rewrite Nat.add_comm.
    rewrite <- stack_perms_assoc.
    cbn.
    rewrite Nat.add_0_r, Nat.add_1_r.
    done.
  Unshelve.
    cbn; lia.
Qed.





Lemma zx_binmat_hblock {n m m'} (A : Matrix bool n m) (B : Matrix bool n m') :
  zx_binmat (mx_hblock A B) ∝=
  (√ 2 ^ n) .* (zx_binmat A ↕ zx_binmat B ⟷
  ZX_bcopy n (!() + !()) (!()) (X 2 1 0)).
Proof.
  destruct m'. 1:{
    rewrite zx_binmat_0_r.
    rewrite <- zx_scale_compose_distr_l, <- zx_scale_stack_distr_r.
    rewrite mx_hblock_nil_r.
    rewrite zx_binmat_cast.

    rewrite stack_split_diag, compose_assoc.
    rewrite <- nwire_removal_r.
    apply compose_simplify_casted_abs; [lia|intros..];
    [rewrite stack_empty_r_fwd, cast_contract_eq'; cast_irrelevance|].
    clear.
    rewrite (proof_irrel _ add_0_r').
    clear Hm'.
    rewrite <- (ZX_bcopy_n_wire n (!())).
    distribute_zxscale.
    rewrite <- (@ZX_bcopy_stack n (!()) (!()) 0 (!())).
    rewrite zx_scale_cast.
    rewrite <- (@ZX_bcopy_compose n (!() + 0) (!() + !()) (!())).
    assert (Hrw : n_wire 1 ↕ (zx_invsqrt2 ↕ X 0 1 0) ⟷ X 2 1 0 ∝= zx_invsqrt2 ↕ n_wire 1).
    1:{
      apply colorswap_diagrams_eq.
      simpl.
      zxfcat.
    }
    rewrite Hrw.
    clear Hrw.
    rewrite ZX_bcopy_n_wire.
    cbn.
    unfold ZX_bcopy.
    rewrite cast_contract_eq'.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite (ZX_copy_stack n zx_invsqrt2 —).
    rewrite ZX_copy_le_1 by lia.
    rewrite n_stack_gadget_to_scalar, const_of_zx_invsqrt2.
    rewrite cast_contract_eq', ZX_copy_wire.
    rewrite cast_stack_l_fwd.
    rewrite zx_scale_stack_distr_l, n_wire_stack, cast_contract_eq'.
    rewrite zx_scale_cast, cast_n_wire.
    rewrite zx_scale_assoc, zx_scale_eq_1_l; [done|].
    rewrite <- Cpow_mul_l, Cinv_r by nonzero.
    rewrite Cpow_1_l.
    done.
  }
  destruct m.
  1:{
    rewrite mx_hblock_nil_l.
    rewrite zx_binmat_0_r.
    rewrite <- nwire_removal_r at 1.
    rewrite stack_split_antidiag, compose_assoc, stack_empty_l.
    rewrite <- zx_scale_compose_distr_r.
    f_equiv.
    rewrite <- (ZX_bcopy_n_wire n (!())).
    rewrite <- (@ZX_bcopy_stack n 0 (!()) (!()) (!()) ).
    rewrite <- (@ZX_bcopy_compose n (0 + !()) (!() + !()) (!())).

    assert (Hrw : (zx_invsqrt2 ↕ X 0 1 0) ↕ n_wire 1 ⟷ X 2 1 0 ∝= zx_invsqrt2 ↕ n_wire 1).
    1:{
      apply colorswap_diagrams_eq.
      simpl.
      zxfcat.
    }
    rewrite Hrw.
    clear Hrw.
    rewrite ZX_bcopy_n_wire.
    cbn.
    unfold ZX_bcopy.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite (ZX_copy_stack n zx_invsqrt2 —).
    rewrite ZX_copy_le_1 by lia.
    rewrite n_stack_gadget_to_scalar, const_of_zx_invsqrt2.
    rewrite cast_contract_eq', ZX_copy_wire.
    rewrite cast_stack_l_fwd.
    rewrite zx_scale_stack_distr_l, n_wire_stack, cast_contract_eq'.
    rewrite zx_scale_cast, cast_n_wire.
    rewrite zx_scale_assoc, zx_scale_eq_1_l; [done|].
    rewrite <- Cpow_mul_l, Cinv_r by nonzero.
    rewrite Cpow_1_l.
    done.
  }
  destruct n.
  - unfold Matrix in A, B.
    cbn.
    rewrite zx_scale_1_l, ZX_bcopy_0, n_wire_removal_r', cast_id.
    unfold ZX_bcopy.
    rewrite 3 (ZX_copy_le_1) by (cbn; lia).
    cbn -[n_stack].
    change (S (?x + S ?y)) with (S x + S y).
    auto_cast_eqn rewrite nstack_split, 2 cast_contract_eq'.
    change 0 with (0 + 0).
    rewrite cast_stack_distribute.
    rewrite 2 cast_contract_eq'.
    done.
  - rewrite <- zx_scale_compose_distr_r.
    apply zx_binmat_aux_l_hblock.
Qed.

















Lemma zx_binmat_copy {n m} (A : Matrix bool n m) :
  zx_binmat A ⟷ ZX_bcopy n (!()) (!() + !()) (Z 1 2 0) ∝=
  ZX_bcopy m (!()) (!() + !()) (Z 1 2 0) ⟷ (zx_binmat A ↕ zx_binmat A).
Proof.
  induction n, m, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite ZX_bcopy_0, cast_id, nwire_removal_r.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    unfold ZX_bcopy.
    cast_irrelevance.
    f_equiv.
    zxfcat.
  - rewrite zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) (!() + !())).
    rewrite <- (@ZX_bcopy_stack n 0 (!()) 0 (!())).
    rewrite ZX_bcopy_0, cast_id, nwire_removal_l.
    unfold ZX_bcopy.
    cast_irrelevance.
    f_equiv.
    zxsrw (to_gadget (X_state_copy'' false 2 0 eq_refl eq_refl)).
    cbn.
    rewrite Cmult_1_r, zx_of_const_invsqrt2.
    zxscat.
  - hnf in A.
    inv_all_vec_fin.
    cbn.
    rewrite ZX_bcopy_1, cast_id.
    apply b2zx_copy.
  - rewrite zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) (!() + !())).
    rewrite (to_gadget bi_algebra_rule_Z_X).
    rewrite <- zx_scale_defn.
    rewrite ZX_bcopy_scale.
    rewrite zx_scale_compose_distr_r.
    unfold bi_alg_Z_X.
    rewrite compose_assoc.
    rewrite (@ZX_bcopy_compose n _ ((!() + !()) + (!() + !()))).
    rewrite ZX_bcopy_stack.
    rewrite <- compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite IHA1, IHA2.
    rewrite (@ZX_bcopy_compose n _ ((!() + !()) + (!() + !()))).
    rewrite ZX_bcopy_to_zx_mid_comm.
    rewrite stack_compose_distr.
    rewrite <- compose_assoc.

    rewrite (compose_assoc _ (zx_binmat A1 ↕ zx_binmat A1 ↕ (zx_binmat A2 ↕ zx_binmat A2))).
    rewrite zx_mid_comm_commutes_r.
    rewrite ZX_bcopy_stack.
    rewrite 2 compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- compose_assoc.
    setoid_rewrite <- ZX_bcopy_1_2_add.
    distribute_zxscale.
    done.
  - rewrite zx_binmat_vblock.
    rewrite ZX_bcopy_1_2_add.
    rewrite compose_assoc.
    cbn.
    rewrite <- (compose_assoc (_ ↕ _)), <- stack_compose_distr.
    rewrite IHA1, IHA2, 2 stack_compose_distr.
    rewrite compose_assoc.
    rewrite (zx_mid_comm_commutes_r (zx_binmat A1) (zx_binmat A1) (zx_binmat A2) (zx_binmat A2)).
    rewrite <- ! compose_assoc.
    rewrite <- 2 (@ZX_bcopy_stack m (!()) (!() + !()) (!()) (!() + !())).
    rewrite <- 2 (@ZX_bcopy_compose m (!()) (!() + !()) ((!() + !()) + (!() + !()))).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_compose m (!()) ((!() + !()) + (!() + !())) ((!() + !()) + (!() + !()))).
    f_equiv.
    f_equiv.
    zxfcat.
Qed.







Lemma zx_binmat_erase {n m} (A : Matrix bool n m) :
  zx_binmat A ⟷ ZX_bcopy n (!()) 0 (Z 1 0 0) ∝=
  ZX_bcopy m (!()) 0 (Z 1 0 0).
Proof.
  induction n, m, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite ZX_bcopy_0, cast_id, nwire_removal_r.
    done.
  - rewrite zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) 0).
    rewrite ZX_bcopy_0, cast_id.
    rewrite pull_out_top, compose_assoc.
    rewrite (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_of_const_to_scaled_empty.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite <- zx_of_const_mult', Cinv_l, zx_of_const_1 by nonzero.
    rewrite ZX_bcopy_n_wire.
    done.
  - hnf in A.
    inv_all_vec_fin.
    cbn.
    rewrite ZX_bcopy_1, cast_id.
    apply b2zx_erase.
  - rewrite zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l, compose_assoc.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) 0).
    rewrite <- zx_scale_compose_distr_r.
    rewrite <- (ZX_bcopy_scale n _ (!() + !()) 0).
    assert (Hrw : √ 2 .* (X 2 1 0 ⟷ Z 1 0 0) ∝= Z 1 0 0 ↕ Z 1 0 0); [|revert Hrw; intros ->].
    1:{
      apply transpose_diagrams_eq.
      rewrite zx_scale_transpose.
      cbn.
      rewrite (to_gadget (Z_state_copy'' false 2 0 eq_refl eq_refl)).
      rewrite zx_scale_defn.
      zxaclean_lhs.
      rewrite <- zx_of_const_mult'.
      rewrite zx_of_const_1' by (cbn; C_field).
      zxscat.
    }
    rewrite (ZX_bcopy_cast_r _ _ _ _ (@bluniti _ 0)).
    rewrite cast_compose_r_eq_mid.
    rewrite 2 cast_id.
    rewrite ZX_bcopy_stack.
    cbn.
    rewrite <- (@stack_compose_distr _ _ 0 _ _ 0).
    rewrite IHA1, IHA2.
    rewrite ZX_bcopy_1_0_add.
    done.
  - rewrite zx_binmat_vblock.
    rewrite ZX_bcopy_1_0_add.
    rewrite compose_assoc.
    cbn.
    rewrite <- (@stack_compose_distr _ _ 0 _ _ 0).
    rewrite IHA1, IHA2.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    zxfcat.
Qed.





Lemma zx_binmat_hadamard {m n} (A : Matrix bool m n) :
  √2 ^ m .* zx_binmat A ⟷ m ↑ □ ∝= √2 ^ n .* n ↑ □ ⟷ (zx_binmat (mx_transpose A)) ⊤.
Proof.
  induction m, n, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite zx_binmat_0_r.
    rewrite (ZX_bcopy_transpose m 0 (!())).
    cbn.
    rewrite gadget_transpose.
    rewrite zx_scale_1_l, zx_scale_compose_distr_l.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose m (!()) (!()) 0).
    rewrite <- (@ZX_bcopy_scale m _ (!()) 0).
    rewrite compose_empty_r.
    f_equiv.
    change (X 1 0 0) with (⊙ (Z 1 0 0)).
    rewrite colorswap_is_bihadamard.
    cbn.
    zxsrw box_compose.
    rewrite <- zx_of_const_invsqrt2, <- zx_of_const_mult', Cinv_l, zx_of_const_1, stack_empty_l by nonzero.
    done.
  - rewrite zx_binmat_0_l.
    rewrite zx_binmat_0_r.
    rewrite (ZX_bcopy_transpose n (!()) 0).
    cbn.
    rewrite zx_scale_1_l, zx_scale_compose_distr_l.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) (!())).
    rewrite <- (@ZX_bcopy_scale n _ 0 (!())).
    rewrite compose_empty_l.
    f_equiv.
    change (X 0 1 0) with (⊙ (Z 0 1 0)).
    rewrite colorswap_is_bihadamard.
    cbn.
    zxsrw box_compose.
    rewrite <- zx_of_const_invsqrt2, <- zx_of_const_mult', Cinv_l, zx_of_const_1, stack_empty_l by nonzero.
    done.
  - hnf in A.
    inv_all_vec_fin.
    rewrite nstack1_1, Cpow_1_r.
    cbn.
    rewrite 2 zx_scale_compose_distr_l, b2zx_hadamard.
    done.
  - rewrite zx_binmat_hblock.
    rewrite 3 zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) (!())).
    rewrite X_to_Z, 3 compose_assoc, nstack1_1, box_compose, wire_removal_r.
    rewrite (@ZX_bcopy_compose n _ (!() + !())).
    cbn.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite ZX_bcopy_stack, ZX_bcopy_1_1.
    rewrite <- compose_assoc, <- stack_compose_distr.
    rewrite <- 2 zx_scale_compose_distr_l, <- zx_scale_stack_distr_l,
      <- zx_scale_compose_distr_l, <- zx_scale_stack_distr_r, <- zx_scale_compose_distr_l.
    rewrite IHA1, IHA2.
    rewrite mx_transpose_hblock.
    rewrite zx_binmat_vblock.
    cbn.
    rewrite (ZX_bcopy_transpose n (! ()) (!() + !())).
    cbn.
    rewrite nstack1_split.
    rewrite <- compose_assoc, <- stack_compose_distr.
    distribute_zxscale.
    rewrite Cmult_comm, <- Cpow_add_r.
    done.

  - rewrite zx_binmat_vblock, Cpow_add_r.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc, <- zx_scale_compose_distr_r, nstack1_split.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_r, <- zx_scale_stack_distr_l.
    rewrite <- 2 zx_scale_compose_distr_l.
    rewrite IHA1, IHA2.
    distribute_zxscale.
    rewrite stack_compose_distr.
    rewrite <- compose_assoc.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_stack m (!()) (!()) (!()) (!())).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (!() + !())).

    rewrite Z_to_X, nstack1_1.
    cbn.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite compose_assoc, <- (stack_compose_distr Box Box Box Box), box_compose.
    rewrite wire_to_n_wire, n_wire_stack, nwire_removal_r.
    rewrite mx_transpose_vblock.
    rewrite zx_binmat_hblock.
    rewrite zx_scale_transpose.
    cbn.
    rewrite (ZX_bcopy_transpose m (!() + !()) (! ())).
    cbn.
    distribute_zxscale.
    f_equiv.
    rewrite <- compose_assoc.
    rewrite <- (@ZX_bcopy_compose m (!()) (!()) (!() + !())).
    done.
Qed.

Lemma zx_binmat_colorswap {m n} (A : Matrix bool m n) :
  ⊙ (zx_binmat A) ∝=
    √ 2 ^ n / √ 2 ^ m .* (zx_binmat (mx_transpose A)) ⊤.
Proof.
  rewrite colorswap_is_bihadamard.
  pose proof (zx_binmat_hadamard A) as Hrw.
  rewrite zx_scale_compose_distr_l in Hrw.
  rewrite zx_scale_eq_l in Hrw by nonzero.
  rewrite Hrw.
  distribute_zxscale.
  rewrite <- compose_assoc.
  rewrite <- n_stack1_compose, box_compose, nwire_removal_l.
  f_equiv.
  C_field.
Qed.


Lemma zx_binmat_cocopy {m n} (A : Matrix bool m n) :
  √2 ^ n .* (ZX_bcopy n (!()+!()) (!()) (X 2 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ m .* (zx_binmat A ↕ zx_binmat A ⟷ ZX_bcopy m (!()+!()) (!()) (X 2 1 0)).
Proof.
  apply colorswap_diagrams_eq.
  rewrite 2 zx_scale_colorswap.
  cbn [color_swap].
  rewrite ZX_bcopy_colorswap.
  rewrite (ZX_bcopy_colorswap m (!()+!()) (!())).
  cbn.
  rewrite zx_binmat_colorswap.
  distribute_zxscale.
  apply transpose_diagrams_eq.
  rewrite 2 zx_scale_transpose.
  cbn.
  rewrite transpose_involutive.
  rewrite (ZX_bcopy_transpose n (!()+!()) (!())), (ZX_bcopy_transpose m (!()+!()) (!())).
  cbn.
  rewrite zx_binmat_copy.
  f_equiv; [|done].
  C_field.
Qed.


Lemma zx_binmat_coerase {m n} (A : Matrix bool m n) :
  √2 ^ m .* (ZX_bcopy n 0 (!()) (X 0 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ n .* (ZX_bcopy m 0 (!()) (X 0 1 0)).
Proof.
  apply colorswap_diagrams_eq.
  rewrite 2 zx_scale_colorswap.
  cbn [color_swap].
  rewrite (ZX_bcopy_colorswap n 0 (!())).
  rewrite (ZX_bcopy_colorswap m 0 (!())).
  cbn.
  rewrite zx_binmat_colorswap.
  distribute_zxscale.
  apply transpose_diagrams_eq.
  rewrite 2 zx_scale_transpose.
  cbn.
  rewrite transpose_involutive.
  rewrite (ZX_bcopy_transpose n 0 (!())).
  rewrite (ZX_bcopy_transpose m 0 (!())).
  cbn.
  rewrite zx_binmat_erase.
  f_equiv.
  C_field.
Qed.


Lemma zx_binmat_cocopy' {m n} (A : Matrix bool m n) :
  (ZX_bcopy n (!()+!()) (!()) (X 2 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ m / √2 ^ n .* (zx_binmat A ↕ zx_binmat A ⟷ ZX_bcopy m (!()+!()) (!()) (X 2 1 0)).
Proof.
  unfold Cdiv.
  rewrite Cmult_comm, <- zx_scale_assoc.
  rewrite <- zx_scale_eq_l by nonzero.
  apply zx_binmat_cocopy.
Qed.


Lemma zx_binmat_coerase' {m n} (A : Matrix bool m n) :
  (ZX_bcopy n 0 (!()) (X 0 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ n / √2 ^ m .* (ZX_bcopy m 0 (!()) (X 0 1 0)).
Proof.
  unfold Cdiv.
  rewrite Cmult_comm, <- zx_scale_assoc.
  rewrite <- zx_scale_eq_l by nonzero.
  apply zx_binmat_coerase.
Qed.




Lemma zx_binmat_plus {m n} (A B : Matrix bool m n) :
  √2 ^ m .* (ZX_bcopy n (!()) (!() + !()) (Z 1 2 0) ⟷
    (zx_binmat A ↕ zx_binmat B) ⟷ ZX_bcopy m (!() + !()) (!()) (X 2 1 0)) ∝=
  zx_binmat (mx_plus A B).
Proof.
  revert m n A B.
  (* FIXME: Debug... *)
  apply matrix_double_nonempty_hblock_vblock_ind; intros *.
  - rewrite 3 zx_binmat_0_l.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    cbn.
    rewrite ZX_bcopy_0, cast_id, compose_empty_r, zx_scale_1_l.
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    zxfcat.
  - rewrite 3 zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_stack n 0 (!()) 0 (!())).
    cbn.
    rewrite ZX_bcopy_0, cast_id, compose_empty_l.
    rewrite <- (@ZX_bcopy_compose n (0 + 0) (!() + !()) (!())).
    rewrite (ZX_bcopy_cast_l _ _ _ blunit), 2 cast_id.
    rewrite <- (@ZX_bcopy_scale n _ 0 (!())).
    f_equiv.
    apply colorswap_diagrams_eq.
    rewrite zx_scale_colorswap.
    cbn.
    rewrite gadget_colorswap.
    cbn.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_scale_defn.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l, zx_scale_assoc.
    apply zx_scale_simplify_eq; [C_field|zxfcat].
  - hnf in A, B.
    inv_all_vec_fin.
    cbn.
    rewrite 2 ZX_bcopy_1, 2 cast_id, Cmult_1_r.
    rewrite b2zx_plus'.
    done.
  - intros Hn Hm Hm' IHA IHB.
    rewrite 2 zx_binmat_hblock.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc,
      zx_scale_compose_distr_r, zx_scale_compose_distr_l, zx_scale_assoc.
    rewrite stack_compose_distr.
    rewrite ZX_bcopy_1_2_add.
    rewrite <- compose_assoc.
    cbn.
    rewrite (compose_assoc _ (zx_mid_comm _ _ _ _)).
    rewrite <- zx_mid_comm_commutes_r, <- compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite 2 compose_assoc, <- (compose_assoc (zx_mid_comm _ _ _ _)).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_stack n (!()+!()) (!()) (!()+!()) (!())).
    rewrite <- (@ZX_bcopy_compose n ((!()+!())+(!()+!()))
      ((!()+!())+(!()+!())) (!()+!())).
    rewrite <- (@ZX_bcopy_compose n ((!()+!())+(!()+!())) (!()+!()) (!())).
    assert (Hrw : — ↕ ⨉ ↕ — ⟷ (X 2 1 0 ↕ X 2 1 0) ⟷ X 2 1 0 ∝=
      (X 2 1 0 ↕ X 2 1 0) ⟷ X 2 1 0) by (apply colorswap_diagrams_eq; cbn; zxfcat).
    rewrite Hrw.
    rewrite (@ZX_bcopy_compose n _ (!()+!())).
    rewrite ZX_bcopy_stack.
    rewrite <- compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- zx_scale_assoc, <- zx_scale_compose_distr_l.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_l, <- zx_scale_stack_distr_r.
    rewrite IHA, IHB.
    rewrite mx_plus_hblock.
    rewrite zx_binmat_hblock.
    done.
  - intros Hn Hn' Hm IHA IHB.
    rewrite 2 zx_binmat_vblock.
    rewrite stack_compose_distr.
    cbn.
    rewrite stack_mid_comm, <- 3 compose_assoc.
    rewrite <- (@ZX_bcopy_stack m (!()) (!()+!()) (!()) (!()+!())).
    rewrite <- (@ZX_bcopy_compose m (!()) (!()+!()) ((!()+!())+(!()+!()))).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_compose m (!()) ((!()+!())+(!()+!())) ((!()+!())+(!()+!()))).
    assert (Hrw : Z 1 2 0 ⟷ (Z 1 2 0 ↕ Z 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ∝=
      Z 1 2 0 ⟷ (Z 1 2 0 ↕ Z 1 2 0)) by zxfcat.
    rewrite Hrw.
    rewrite (@ZX_bcopy_compose m _ (!()+!())).
    rewrite ZX_bcopy_stack.
    rewrite 2 compose_assoc.
    rewrite ZX_bcopy_2_1_add, <- (compose_assoc (zx_mid_comm _ _ _ _)).
    rewrite <- zx_mid_comm_transpose, zxperm_transpose_left_inverse, nwire_removal_l by auto_zxperm.
    rewrite <- stack_compose_distr, compose_assoc.
    cbn.
    rewrite <- stack_compose_distr, <- 2 compose_assoc.
    rewrite <- zx_scale_compose_distr_r, Cpow_add_r, Cmult_comm.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_l, <- zx_scale_stack_distr_r.
    rewrite IHA, IHB.
    rewrite mx_plus_vblock.
    rewrite zx_binmat_vblock.
    done.
Qed.




Lemma zx_binmat_aux_r_const_false n : zx_binmat_aux_r (Vector.const false (S n)) ∝=
  ZX_bcopy (S n) (! ()) 0 (Z 1 0 0) ⟷ (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  induction n.
  + cbn.
    rewrite ZX_bcopy_1, cast_id.
    zxscat.
  + cbn [zx_binmat_aux_r].
    rewrite IHn.
    cbn.
    rewrite <- zx_of_const_invsqrt2, <- 2zx_scale_defn.
    distribute_zxscale.
    rewrite (stack_compose_distr (Z 1 0 0)).
    rewrite zx_scale_compose_distr_l, compose_assoc.
    rewrite <- X_add_l, 2 Rplus_0_l.
    rewrite <- zx_sqrt2_defn'_ZX.
    rewrite <- zx_of_const_sqrt2.
    rewrite <- zx_scale_defn.
    distribute_zxscale.
    rewrite Cmult_assoc, Cinv_r, Cmult_1_l by nonzero.
    do 2 f_equiv; [|done].
    unfold ZX_bcopy.
    rewrite cast_stack_r_fwd.
    cbn.
    rewrite 2 ZX_copy_le_1 by lia.
    rewrite cast_stack_r_fwd.
    rewrite 2 cast_contract_eq'.
    cast_irrelevance.
Qed.

Lemma zx_binmat_const_false n m :
  zx_binmat (const_matrix false) ∝= ZX_bcopy n (! ()) 0 (Z 1 0 0)
    ⟷ ZX_bcopy m 0 (! ()) (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  rewrite const_matrix_alt.
  cbn.

  destruct n. 1:{
    rewrite zx_binmat_0_r, ZX_bcopy_0, cast_id, compose_empty_l.
    done.
  }
  destruct m. 1:{
    rewrite zx_binmat_0_l, ZX_bcopy_0, cast_id, compose_empty_r.
    done.
  }
  cbn [zx_binmat].
  induction m.
  - cbn [zx_binmat_aux_l].
    rewrite zx_binmat_aux_r_const_false, ZX_bcopy_1, cast_id.
    done.
  - cbn [zx_binmat_aux_l].
    rewrite IHm.
    rewrite zx_binmat_aux_r_const_false.
    rewrite stack_compose_distr, <- compose_assoc.
    rewrite <- (@ZX_bcopy_stack (S n) (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose (S n) (!()) (!()+!()) (0+0)).
    rewrite <- (@Z_add_r 1 0 0), 2 Rplus_0_l.
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    unfold ZX_bcopy.
    rewrite cast_stack_r_fwd.
    cast_irrelevance.
    cbn.
    rewrite 2 ZX_copy_le_1 by lia.
    rewrite cast_stack_r_fwd.
    cast_irrelevance.
Qed.


Lemma zx_binmat_compose {k m n} (A : Matrix bool m n) (C : Matrix bool k m) :
  zx_binmat A ⟷ zx_binmat C ∝= zx_binmat (compose_matrix C A).
Proof.
  induction k, m, n, C, A using matrix_composable_double_nonempty_hblock_vblock_ind.
  - rewrite 2 zx_binmat_0_l.
    clear.
    rewrite zx_binmat_erase.
    done.
  - rewrite compose_matrix_0_mid.
    rewrite zx_binmat_0_l, zx_binmat_0_r.
    setoid_rewrite zx_binmat_const_false.
    done.
  - rewrite 2 zx_binmat_0_r.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_scale_defn.
    rewrite 2 ZX_bcopy_scale, zx_scale_compose_distr_l.
    rewrite 2 Cpow_inv.
    rewrite <- zx_scale_eq_l by nonzero.
    rewrite zx_scale_assoc, Cmult_comm, <- zx_scale_assoc.
    rewrite <- zx_scale_eq_r by nonzero.
    apply zx_binmat_coerase.
  - unfold Matrix in *.
    inv_all_vec_fin.
    cbn.
    rewrite b2zx_compose', xorb_false_r.
    done.
  - rewrite compose_matrix_vblock_l, 2 zx_binmat_vblock.
    rewrite <- compose_assoc.
    rewrite zx_binmat_copy.
    rewrite compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite IHA1, IHA2.
    done.
  - rewrite compose_matrix_hblock_r, 2 zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- zx_scale_compose_distr_r.
    rewrite (zx_binmat_cocopy A1).
    rewrite zx_scale_compose_distr_r, <- compose_assoc, <- stack_compose_distr.
    rewrite IHA1, IHA2.
    done.
  - rewrite zx_binmat_vblock, zx_binmat_hblock, compose_matrix_hblock_vblock.
    rewrite <- zx_binmat_plus.
    rewrite zx_scale_compose_distr_r.
    f_equiv.
    rewrite <- compose_assoc.
    f_equiv.
    rewrite compose_assoc.
    f_equiv.
    cbn.
    rewrite <- stack_compose_distr, IHA1, IHA2.
    done.
Qed.














(* Lemma ZX_bvcopy_compose_gen {A B} {n m o} (f : A -> ZX n m) (g : B -> ZX m o) *)















Definition X_pi_wire (b : bool) : ZX 1 1 :=
  X 1 1 (if b then PI else 0).

Lemma Z_state_0_erase α :
  Z 0 1 0 ⟷ X 1 1 α ∝= Z 0 1 0.
Proof.
  rewrite (to_gadget (Z_state_copy'' false 1 α eq_refl eq_refl)).
  rewrite zx_of_const_1.
  zxscat.
Qed.

Lemma Z_state_0_coerase α :
  X 1 1 α ⟷ Z 1 0 0 ∝= Z 1 0 0.
Proof.
  transpose_of (Z_state_0_erase α).
Qed.

Lemma X_state_0_erase α :
  X 0 1 0 ⟷ Z 1 1 α ∝= X 0 1 0.
Proof.
  colorswap_of (Z_state_0_erase α).
Qed.

Lemma X_state_0_coerase α :
  Z 1 1 α ⟷ X 1 0 0 ∝= X 1 0 0.
Proof.
  transpose_of (X_state_0_erase α).
Qed.


Lemma X_pi_wire_b2zx b c :
  X_pi_wire b ⟷ b2zx c ∝=
  b2zx c ⟷ X_pi_wire (b && c).
Proof.
  destruct b, c; unfold X_pi_wire; cbn.
  - rewrite wire_removal_l, wire_removal_r.
    done.
  - rewrite X_is_wire, wire_removal_r.
    zxsrw (Z_state_0_coerase PI).
    zxscat.
  - rewrite wire_removal_l, wire_removal_r.
    done.
  - rewrite X_is_wire.
    rewrite wire_removal_l, wire_removal_r.
    done.
Qed.

Lemma X_pi_wire_plus b c :
  X_pi_wire b ↕ X_pi_wire c ⟷ X 2 1 0 ∝=
  X 2 1 0 ⟷ X_pi_wire (b ⊕ c).
Proof.
  unfold X_pi_wire.
  rewrite <- X_add_l, X_spider_1_1_fusion.
  rewrite Rplus_0_l, Rplus_0_r.
  destruct b, c; [|f_equiv; cbn; lra..].
  apply X_eq_2_PI.
  lra.
Qed.

Definition Z_pi_wire (b : bool) : ZX 1 1 :=
  Z 1 1 (if b then PI else 0).

Lemma zx_binmat_red_pi_action {m n} (A : Matrix bool m n) (v : vec bool n) :
  n_stackv1 X_pi_wire v ⟷ zx_binmat A ∝= zx_binmat A ⟷ n_stackv1 X_pi_wire (mx_vec_prod A v).
Proof.
  induction n as [[|[|n]] IHn] using lt_wf_ind.
  - rewrite zx_binmat_0_r.
    cbn.
    rewrite compose_empty_l.
    rewrite mx_vec_prod_0.
    rewrite (n_stackv1_const' (X 1 1 0)). 2:{
      intros i.
      rewrite lookup_fun_to_vec.
      done.
    }
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose m 0 (!()) (!())).
    rewrite X_is_wire, wire_removal_r.
    done.
  - clear IHn.
    induction m as [[|[|m]] IHm] using lt_wf_ind.
    + rewrite zx_binmat_0_l.
      rewrite ZX_bcopy_1, cast_id.
      cbn.
      rewrite compose_empty_r.
      rewrite stack_empty_r_fwd, cast_id.
      unfold X_pi_wire.
      apply transpose_diagrams_eq.
      cbn.
      rewrite (to_gadget (Z_state_copy'' false 1 (if (vhd v) then PI else 0) eq_refl eq_refl)).
      rewrite cast_id, zx_of_const_1.
      zxscat.
    + unfold Matrix in *.
      clear.
      inv_all_vec_fin.
      cbn.
      rewrite 2 stack_empty_r_fwd, 2 cast_id, xorb_false_r.
      rewrite X_pi_wire_b2zx.
      done.
    + change (S (S m)) with (1 + S m) in *.
      rewrite <- (mx_vblock_split A).
      rewrite zx_binmat_vblock.
      rewrite mx_vec_prod_vblock, n_stackv1_vapp.
      rewrite compose_assoc.
      cbn [btree_fold].
      rewrite <- stack_compose_distr.
      rewrite <- 2 IHm by lia.
      rewrite stack_compose_distr.
      rewrite <- 2 compose_assoc.
      f_equiv.
      rewrite ZX_bcopy_1, cast_id.
      clear.
      inv_vec v.
      intros []; unfold X_pi_wire; cbn; rewrite stack_empty_r_fwd, cast_id.
      * rewrite (X_pi_copy _ eq_refl eq_refl).
        cbn.
        rewrite stack_empty_r_fwd, cast_id.
        done.
      * rewrite X_is_wire.
        zxscat.
  - change (S (S n)) with (1 + S n) in *.
    induction v as [vl vr] using vec_add_inv.
    rewrite <- (mx_hblock_split A).
    pose proof (mx_vec_prod_hblock_app (mx_splitl A) (mx_splitr A) vl vr) as Hrw.
    pose proof (leibniz_equiv_iff (A:=vec bool m)) as Hleib.
    apply Hleib in Hrw.
    rewrite Hrw.
    rewrite zx_binmat_hblock.
    fold (vec_equiv (A:=bool) (n:=1 + S n)) in Hrw.
    rewrite zx_scale_compose_distr_r.
    rewrite n_stackv1_vapp.
    rewrite <- compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite 2 IHn by lia.
    cbn [btree_fold].
    distribute_zxscale.
    f_equiv.
    rewrite stack_compose_distr, 2 compose_assoc.
    f_equiv.
    rewrite <- 3 ZX_bvcopy_1_1.
    rewrite (vec_to_vmap_lookup_vfinseq (mx_vec_prod _ vl)).
    rewrite (vec_to_vmap_lookup_vfinseq (mx_vec_prod _ vr)).
    rewrite 2 ZX_bvcopy_vmap.
    rewrite <- (ZX_bvcopy_stack (!()) (!()) (!()) (!()) m).
    rewrite vzip_with_map.
    rewrite vzip_with_diag, ZX_bvcopy_vmap.
    erewrite <- (@ZX_bvcopy_const (fin m)) at 1.
    rewrite <- (ZX_bvcopy_compose (!()+!()) (!()+!()) (!()) m).
    erewrite <- (@ZX_bvcopy_const (fin m)) at 1.
    rewrite <- (ZX_bvcopy_compose (!()+!()) (!()) (!()) m).
    apply (ZX_bvcopy_ext_eq (!()+!()) (!()) m).
    intros i.
    cbn.
    rewrite lookup_vfinseq.
    rewrite X_pi_wire_plus.
    done.
Qed.


Lemma zx_binmat_green_pi_action {m n} (A : Matrix bool m n) (v : vec bool m) :
  zx_binmat A ⟷ n_stackv1 Z_pi_wire v ∝=
  n_stackv1 Z_pi_wire (mx_vec_prod (mx_transpose A) v) ⟷ zx_binmat A.
Proof.
  apply colorswap_diagrams_eq, transpose_diagrams_eq.
  cbn.
  rewrite 2 n_stackv1_colorswap, 2 n_stackv1_transpose.
  rewrite zx_binmat_colorswap.
  rewrite zx_scale_transpose, transpose_involutive.
  distribute_zxscale.
  unfold Z_pi_wire.
  cbn.
  rewrite zx_binmat_red_pi_action.
  done.
Qed.





(* Lemma mx_biadj_vblock {n n' m} (A : Matrix bool n m) (B : Matrix bool n' m) :
  mx_biadj (mx_vblock A B) ∝=
  cast _ _ mul_add_distr_r mul_add_distr_r (mx_biadj A ↕ mx_biadj B).

Notation BinMatrix m n := (vec (vec bool n) m).

Declare Scope binmatrix_scope.
Delimit Scope binmatrix_scope with binmatrix.
Bind Scope binmatrix_scope with BinMatrix.

Definition binmx_vblock

Lemma zx_binmat_vapp {m m' n} (A : BinMatrix ) *)

