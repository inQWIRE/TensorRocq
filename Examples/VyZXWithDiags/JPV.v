From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.
From TensorRocq Require Import Aux.


From TensorRocqEx Require Import Rmodeq.

From TensorRocqEx Require Import VyZXExample_withdiags.
From TensorRocqEx Require Import SZXAux.


Module JPV.

Import ZXsymm ZXauto ZXfrob.

Local Open Scope C_scope.

Lemma zx_triangle_left_defn : zx_triangle_left = zx_triangle ⊤.
Proof. reflexivity. Qed.

Lemma zx_triangle_defn : zx_triangle = X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 4) ⟷ (Z 0 1 (PI / 4) ↕ — ⟷ X 2 1 0)
⟷ (Z 1 2 0 ⟷ (— ↕ (X 1 2 0 ⟷ (Z 1 0 (- PI / 4) ↕ Z 1 0 (- PI / 4))))).
Proof. reflexivity. Qed.


Lemma cup_is_controlized :
  is_controlized ⊂
  cupcap_controlizer.
Proof.
  unfold cupcap_controlizer.
  split.
  - unfold is_controlled_state.
    zxsrw (Z_1_2_state_0 0).
    zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    zxsrw left_triangle_state_0.
    zxsrw (Z_1_n_state0 0 0).
    zxsrw (triangle_state_0).
    pose proof (Z_state_copy 0 2 PI eq_refl eq_refl) as Hcopy.
    rewrite Rmult_0_l in Hcopy.
    zxsrw (to_gadget Hcopy).
    rewrite Cexp_0, Cexp_PI.
    replace ((C1 + C1) * (C1 - (-1)%R) + C2 * (-1)%R)%C with C2 by lca.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [unfold uniform_state; cbn; zxscat|].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    cbn.
    autorewrite with RtoC_db.
    C_field.
  - (* rewrite <- compose_assoc. *)
    zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_to_scaled_empty, zx_scale_1_l.
    zxsrw left_triangle_state_1.
    zxsrw (@Z_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    rewrite (gadget_is_scaled_empty (Z 0 0 0)).
    rewrite const_of_zx_Z_gen.
    rewrite Cexp_0.
    zxsrw triangle_state_1.
    zxsrw (@X_1_n_state_1 2 PI).
    zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite X_eq_2_PI by lra.
    rewrite <- ! zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxacat|].
    cbn.
    C_field; lca.
Qed.

Lemma JPV'_27 : Z 1 2 0 ⟷ (◁ ↕ —) ⟷ X 2 1 0 ∝= / √2 .* ◁.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  destruct b; cbn.
  - zxsrw (Z_1_2_state_1 0).
    zxsrw left_triangle_state_1.
    zxsrw (X_zxperm_absorbtion_left 2 2 1 0 ⨉ ltac:(auto_zxperm)).
    zxsrw left_triangle_state_1.
    rewrite state_1_defn.
    zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 0 1 PI 0 eq_refl eq_refl).
    pose proof (Z_state_copy 0 1 PI eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l in Hrw.
    rewrite Rplus_0_r.
    unfold n_stack in Hrw.
    zxsrw (to_gadget Hrw).
    clear Hrw.
    rewrite <- !zx_of_const_mult'.
    f_equiv.
    f_equiv.
    rewrite Cexp_0, Cexp_PI.
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
  - zxsrw (Z_1_2_state_0 0).
    zxsrw left_triangle_state_0.
    zxsrw left_triangle_state_0.
    rewrite state_0_defn.
    (* zxsrw (X_zxperm_absorbtion_left 2 2 1 0 ⨉ ltac:(auto_zxperm)). *)
    zxsrw <- (@X_add_l 0 0 1 0 0 0).
    rewrite 2 Rplus_0_r.
    zxscat.
Qed.

Lemma X_0_0_PI_zero : X 0 0 PI ∝= zx_zero.
Proof.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_gen.
  rewrite Cexp_PI.
  replace (C1 + (-1)%R) with C0 by lca.
  apply zx_scale_0_l.
Qed.

Import ComposeRules.
Lemma JPV_2_17 : (— ↕ X 0 2 PI) ⟷ ((Z 2 1 0 ⟷ ▷) ↕ ◁) ⟷ (Z 2 1 0) ∝=
  /√ 2 .* (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros br.
  apply transpose_diagrams_eq.
  cbn.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros bl.
  rewrite left_triangle_transpose, triangle_transpose.
  rewrite zx_scale_transpose.
  cbn.
  destruct bl, br.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite left_triangle_state_1, triangle_state_1.
    rewrite Z_spider_1_1_fusion, Rplus_0_r.
    pose proof (X_wrap_over_top_right 1 0 PI) as Hrw.
    rewrite cap_Z in Hrw.
    rewrite state_1_defn at 2 4.
    rewrite !zx_scale_transpose.
    zxsrw <- Hrw.
    zxsrw <- state_0_defn.
    zxsrw (@X_1_n_state_0 0 PI).
    zxsrw (@X_1_n_state_1 1 PI).
    zxsrw (@X_spider_1_1_fusion 0 0 (PI + PI) PI).
    rewrite (X_Rmodeq_2PI _ PI) by (exists (1 : BinInt.Z); lra).
    rewrite X_0_0_PI_zero.
    rewrite ?zx_scale_0_l.
    rewrite ?compose_0_l, ?stack_0_l.
    done.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite left_triangle_state_1, triangle_state_1.
    rewrite Z_spider_1_1_fusion, Rplus_0_r.
    pose proof (X_wrap_over_top_right 1 0 PI) as Hrw.
    rewrite cap_Z in Hrw.
    rewrite state_0_defn at 1 2.
    rewrite !zx_scale_transpose.
    zxsrw <- Hrw.
    rewrite state_1_defn.
    zxsrw (@X_spider_1_1_fusion 0 1 PI PI).

    rewrite (X_eq_2_PI 0 1 (PI + PI)) by lra.
    zxsrw (@X_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    zxsrw (to_gadget (X_state_pi_copy 0 eq_refl eq_refl)).
    zxsrw (@X_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    rewrite (gadget_is_scaled_empty (X 0 0 0)).
    rewrite const_of_zx_X_gen.
    rewrite Cexp_0.
    replace (C1 + C1) with C2 by lca.
    etransitivity; [apply gadget_is_scaled_empty|etransitivity; [|symmetry; apply gadget_is_scaled_empty] ].
    f_equiv.
    rewrite ? const_of_zx_compose, ?const_of_zx_stack.
    rewrite ? const_of_zx_of_const.
    rewrite const_of_zx_scale.
    cbn.
    autorewrite with RtoC_db.
    C_field.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_0.

    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite triangle_state_0, left_triangle_state_0.
    rewrite Z_1_2_state_0.
    rewrite state_1_defn at 1 2.
    rewrite !zx_scale_transpose.
    cbn.
    rewrite state_0_defn.
    zxsrw (@X_spider_1_1_fusion 0 0 0 PI).
    zxsrw (@X_spider_1_1_fusion 0 0 0 PI).
    rewrite Rplus_0_l.
    now rewrite X_0_0_PI_zero, ?compose_0_l, ?stack_0_l.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_0.

    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite triangle_state_0, left_triangle_state_0.
    rewrite Z_1_2_state_0.
    rewrite state_0_defn at 3 5.
    rewrite !zx_scale_transpose.
    cbn.
    rewrite state_0_defn at 1 2.
    zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 0 0 0 PI eq_refl eq_refl).
    pose proof (Z_state_copy 0 0 PI eq_refl eq_refl) as Hrw.
    rewrite Rplus_0_l.
    rewrite Rmult_0_l in Hrw.
    zxsrw (to_gadget Hrw).
    zxsrw (Z_1_n_state0 0 0).
    rewrite <- ! zx_of_const_mult'.
    f_equiv.
    f_equiv.
    rewrite Cexp_PI, Cexp_0.
    cbn.
    autorewrite with RtoC_db.
    C_field.
    lca.
Qed.

Lemma JPV_2_4_a : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 1 0 ⟷ X 1 0 0) ∝= ⦰.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_stack.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_invsqrt2_defn.
  rewrite const_of_zx_invsqrt2.
  etransitivity; [|apply zx_scale_1_l].
  f_equiv.
  C_field.
Qed.

Lemma JPV_2_4_b : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 3 0 ⟷ X 3 0 0) ↕ Z 0 0 0 ∝= ⦰.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite <- zx_invsqrt2_defn.
  rewrite gadget_is_scaled_empty.
  rewrite 2 const_of_zx_stack.
  rewrite const_of_zx_Z_0.
  rewrite const_of_zx_invsqrt2.
  etransitivity; [|apply zx_scale_1_l].
  f_equiv.
  C_field.
Qed.


Lemma JPV_2_5 α β : (Z 0 1 PI ⟷ X 1 0 α) ↕ (Z 0 1 PI ⟷ X 1 0 β) ∝=
  (Z 0 1 PI ⟷ X 1 0 (α + β)) ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  apply transpose_diagrams_eq.
  cbn.
  apply const_of_zx_inj.
  rewrite 2 const_of_zx_stack.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite 3 const_of_zx_X_0_1_Z_1_0_gen.
  rewrite 5 (Cexp_add).
  rewrite Cexp_PI.
  C_field.
  lca.
Qed.

#[export] Instance ZXDVERT_inhab : Inhabited ZXDVERT := _.

Lemma JPV_2_6 : Z 1 1 PI ⟷ X 1 2 0 ∝= X 1 2 0 ⟷ (Z 1 1 PI ↕ Z 1 1 PI).
Proof.
  pose proof (Z_copy 2 1 eq_refl eq_refl) as Hrw.
  rewrite Rmult_1_l in Hrw.
  zxsrw <- Hrw.
  zxscat.
Qed.


(* FIXME: Move *)
Lemma fold_state_0 : X 0 1 0 ∝= √2 .* state_0.
Proof.
  rewrite state_0_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.
Lemma fold_state_1 : X 0 1 PI ∝= √2 .* state_1.
Proof.
  rewrite state_1_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.


Lemma JPV_2_7 : X 0 1 0 ⟷ zx_triangle ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  rewrite fold_state_0.
  zxsrw triangle_state_0.
  rewrite (gadget_is_scaled_empty (_ ⟷ _)).
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  zxscat.
Qed.

Lemma JPV_2_8 : X 0 1 0 ⟷ zx_triangle_left ∝= X 0 1 0.
Proof.
  rewrite fold_state_0.
  zxsrw left_triangle_state_0.
  zxscat.
Qed.

Lemma JPV_2_9 : X 0 1 PI ⟷ zx_triangle ∝= X 0 1 PI.
Proof.
  rewrite fold_state_1.
  zxsrw triangle_state_1.
  zxscat.
Qed.

Lemma JPV_2_10 : X 0 1 PI ⟷ zx_triangle_left ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  rewrite fold_state_1.
  zxsrw left_triangle_state_1.
  rewrite (gadget_is_scaled_empty (_ ⟷ _)).
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  zxscat.
Qed.

Lemma JPV_2_11 : X 1 1 PI ⟷ zx_triangle_left ∝= zx_triangle ⟷ X 1 1 PI.
Proof.
  prep_matrix_equivalence.
  rewrite 2 zx_compose_spec.
  pose proof not_semantics as Hrw.
  rewrite not_defn in Hrw.
  rewrite Hrw.
  rewrite zx_triangle_semantics.
  rewrite zx_triangle_left_semantics.
  by_cell; lca.
Qed.

Lemma JPV_2_12 : Z 1 2 0 ⟷ (zx_triangle_left ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —) ∝=
  Z 1 2 0 ⟷ (X 1 2 0 ↕ zx_triangle_left) ⟷ (— ↕ Z 2 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same.
  rewrite zx_of_const_1, 2 stack_empty_l.
  zxsrw (@X_1_n_state_b 2 0 b).
  zxsrw (@X_1_n_state_b 2 0 b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - rewrite Rplus_0_r.
    zxfcat.
  - zxsrw_rhs (@Z_self_swap_absorbtion_left_base 1 0).
    rewrite <- cap_X.
    zxfcat.
Qed.



Lemma JPV_2_13 : Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ (zx_triangle ⟷ zx_triangle)) ∝=
  zx_triangle ⟷ Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ —).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (left_triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  rewrite Cexp_0, Tauto.if_same.
  rewrite zx_of_const_1, stack_empty_l.
  destruct b.
  - zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_1, stack_empty_l.
    zxsrw left_triangle_state_1.
    zxsrw triangle_state_1.
    zxscat.
  - zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    rewrite Rplus_0_r.
    rewrite <- cap_Z.
    zxarw_rhs (cup_pullthrough_top (zx_triangle_left ⟷ Z 1 0 0) —).
    zxsrw_rhs <- (eq_reflexivity (RA:=proportional_by_1)  _ _ zx_triangle_defn).
    zxsrw (Z_1_n_state0 0 0).
    zxscat.
Qed.

(* FIXME: Move *)
Lemma triangle_left_transpose : zx_triangle_left ⊤ = zx_triangle.
Proof.
  rewrite zx_triangle_left_defn.
  apply transpose_involutive_eq.
Qed.
Lemma zx_invsqrt2_defn' : zx_invsqrt2 ∝= Z 0 3 0 ⟷ X 3 0 0.
Proof.
  symmetry.
  rewrite gadget_is_scaled_empty.
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite <- zx_invsqrt2_defn.
  rewrite <- gadget_is_scaled_empty.
  done.
Qed.

Lemma JPV_2_14 : (Z 0 1 0 ⟷ zx_triangle) ↕
  (Z 0 1 0 ⟷ zx_triangle_left) ⟷ Z 2 1 0 ∝= Z 0 0 0 ↕ Z 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose, triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_n_state_b b 0 0).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - zxsrw (Z_1_n_state_b true 0 0).
    rewrite Cexp_0, zx_of_const_1.
    zxfcat.
  - zxsrw (Z_1_n_state_b false 0 0).
    rewrite zx_of_const_1.
    zxfcat.
Qed.

Lemma JPV_2_15 : Z 1 2 0 ⟷ (□ ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝=
  (Z 0 3 0 ⟷ X 3 0 0) ↕
  zx_triangle_left ⟷ Z 1 1 PI.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw <- zx_invsqrt2_defn'.
  rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2.
  destruct b.
  - cbn.
    zxsrw box_state_1.
    rewrite state_minus_defn.
    zxfcat.
  - cbn.
    zxsrw box_state_0.
    rewrite state_plus_defn.
    zxsrw (Z_1_n_state0 1 PI).
    rewrite state_0_defn.
    zxfcat.
Qed.

Lemma JPV_2_16 : Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝= —.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b; zxfcat.
Qed.

(* FIXME: Move *)
Lemma const_of_zx_zero : const_of_zx zx_zero = 0.
Proof.
  unfold const_of_zx.
  rewrite zx_zero_semantics.
  done.
Qed.
Lemma zx_of_const_0 : zx_of_const 0 ∝= zx_zero.
Proof.
  apply const_of_zx_inj.
  rewrite const_of_zx_of_const, const_of_zx_zero.
  done.
Qed.
Lemma Z_2_1_0_states_b b c :
  state_b b ↕ state_b c ⟷ Z 2 1 0 ∝=
  (if eqb b c then state_b b else zx_zero).
Proof.
  apply transpose_diagrams_eq.
  cbn [transpose].
  apply prop_eq_by_eq_on_state_b_1_n.
  intros d.
  zxsrw (Z_1_n_state_b d 2 0).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (state_b_state_b_transpose d c).
  zxsrw (state_b_state_b_transpose d b).
  rewrite <- zx_of_const_mult'.
  rewrite <- RtoC_mult, b2R_mult.
  replace (_ && _) with (eqb b c && eqb d b) by (unfold eqb; Btauto.btauto).
  destruct (eqb b c); [|cbn; rewrite zx_zero_transpose, zx_of_const_0, compose_0_r; done].
  rewrite state_b_state_b_transpose.
  rewrite gadget_is_scaled_empty, const_of_zx_of_const.
  done.
Qed.


Lemma JPV_2_17' : Z 1 2 0 ⟷ (zx_triangle ↕ (X 1 1 PI ⟷ zx_triangle_left)) ⟷ Z 2 1 0 ∝=
  (X 0 3 0 ⟷ Z 3 0 0) ↕ (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  rewrite <- not_defn.
  zxsrw (not_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b (¬ b)).
  zxsrw (@X_1_n_state_b 0 0 b).
  rewrite Rplus_0_r.
  destruct b.
  - cbn.
    rewrite X_0_0_PI_zero.
    rewrite compose_0_l, 2 stack_0_l.
    pose proof (Z_2_1_0_states_b true false) as Hrw.
    cbn in Hrw.
    rewrite <- Hrw.
    zxscat.
  - cbn.
    zxsrw <- (Aux.eq_reflexivity _ _ zx_invsqrt2_defn :> _ ∝= _).
    rewrite gadget_is_scaled_empty.
    rewrite 2 const_of_zx_compose, const_of_zx_invsqrt2, const_of_zx_of_const.
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_Z_0.
    rewrite zx_scale_eq_1_l by C_field.
    zxfcat.
Qed.

Lemma JPV_2_18_a : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 PI ⟷ zx_triangle_left) ↕
  zx_triangle_left) ⟷ Z 2 1 0) ∝=
  zx_triangle_left ↕ zx_triangle_left ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_left_transpose.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  destruct b.
  - zxsrw (@X_1_n_state_1 2 PI).
    rewrite X_eq_2_PI by lra.
    rewrite <- cap_X.
    zxsrw <- (Z_wrap_over_top_right 1 1 0).
    zxsrw (Z_1_2_state_1 0).
    rewrite <- !zx_of_const_mult'.
    rewrite Cexp_0.
    rewrite zx_of_const_1' by C_field.
    zxscat.
  - pose proof (Z_state_copy 0 2 PI eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l, Cexp_0, Cexp_PI in Hrw.
    zxsrw (to_gadget Hrw).
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxfcat|].
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
Qed.

Lemma JPV_2_18_b : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 0 ⟷ zx_triangle) ↕
  zx_triangle) ⟷ Z 2 1 0) ∝=
  zx_triangle ↕ zx_triangle ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - pose proof (Z_state_copy 0 2 0 eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l, Cexp_0 in Hrw.
    zxsrw (to_gadget Hrw).
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxfcat|].
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
  - zxsrw (@X_1_n_state_0 2 0).
    rewrite <- cap_X.
    zxsrw <- (Z_wrap_over_top_right 1 1 0).
    zxsrw (Z_1_2_state_0 0).
    rewrite <- !zx_of_const_mult'.
    rewrite zx_of_const_1' by C_field.
    zxscat.
Qed.

(* FIXME: Remove when in VyZX: *)


Definition wrap_otl {n m o} (zx : ZX (n + m) o) : ZX m (n + o) :=
  n_cap n ↕ n_wire m ⟷
    cast _ _ (eq_sym (Nat.add_assoc _ _ _)) eq_refl (n_wire n ↕ zx).

Definition wrap_otr {n m o} (zx : ZX n (m + o)) : ZX (m + n) o :=
  cast _ _ eq_refl (eq_sym (Nat.add_assoc _ _ _)) (n_wire m ↕ zx)
  ⟷ (n_cup m ↕ n_wire o).

Definition wrap_ubl {n m o} (zx : ZX (n + m) o) : ZX n (o + m) :=
  cast _ _ (eq_sym (Nat.add_0_r _))
    (eq_sym (Nat.add_assoc _ _ _)) (n_wire n ↕ n_cap m) ⟷
    (zx ↕ n_wire m).

Definition wrap_ubr {n m o} (zx : ZX n (m + o)) : ZX (n + o) m :=
  (zx ↕ n_wire o) ⟷
    cast _ _ (eq_sym (Nat.add_assoc _ _ _))
      (eq_sym (Nat.add_0_r _)) (n_wire m ↕ n_cup o).
Import Setoid.

Add Parametric Morphism {n m o} : (@wrap_otl n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_otl_mor.
Proof.
  unfold wrap_otl.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_otr n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_otr_mor.
Proof.
  unfold wrap_otr.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_ubl n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_ubl_mor.
Proof.
  unfold wrap_ubl.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_ubr n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_ubr_mor.
Proof.
  unfold wrap_ubr.
  now intros ? ? ->.
Qed.


Global Arguments wrap_otl : simpl never.
Global Arguments wrap_otr : simpl never.
Global Arguments wrap_ubl : simpl never.
Global Arguments wrap_ubr : simpl never.

Import CastRules.

Lemma cast_compose_mid_distribute {n n' m o o' : nat}
  (m' : nat) (prfm : m' = m) (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo :
  cast n' o' prfn prfo (zx0 ⟷ zx1) =
  cast n' m' prfn prfm zx0 ⟷ cast m' o' prfm prfo zx1.
Proof.
  subst.
  reflexivity.
Qed.

Lemma wrap_otl_otr {n m o} (zx : ZX n (m + o)) :
  wrap_otl (wrap_otr zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r_fwd, stack_assoc_back_fwd, cast_contract_eq', n_wire_stack.

  unshelve erewrite (cast_compose_mid_distribute (m + m + (m + o))); [lia|].
  rewrite <- compose_assoc.
  rewrite cast_contract_eq'.
  rewrite cast_id.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_l, nwire_removal_r.
  rewrite push_out_top.
  rewrite <- (nwire_removal_r zx) at 2.
  rewrite compose_assoc.
  Morphisms.f_equiv.
  rewrite <- n_wire_stack.
  rewrite stack_assoc_back_fwd.
  rewrite (stack_assoc_back_fwd (n_wire m) (n_cup m) (n_wire o)).
  rewrite cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_l, <- stack_nwire_distribute_r.
  rewrite <- cast_stack_l.
  Morphisms.f_equiv.
  rewrite cast_id.
  apply big_yank_l.
  Unshelve.
  all: lia.
Qed.

Lemma wrap_otr_otl {n m o} (zx : ZX (n + m) o) :
  wrap_otr (wrap_otl zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r_fwd, stack_assoc_back_fwd, cast_contract_eq', n_wire_stack.
  unshelve erewrite (cast_compose_mid_distribute (n + n + (n + m))); [lia|].
  rewrite compose_assoc.
  rewrite cast_contract_eq'.
  rewrite cast_id.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_l, nwire_removal_r.
  rewrite pull_out_top.
  rewrite <- (nwire_removal_l zx) at 2.
  rewrite <- compose_assoc.
  Morphisms.f_equiv.
  rewrite <- n_wire_stack.
  rewrite stack_assoc_back_fwd.
  rewrite (stack_assoc_back_fwd (n_wire n) (n_cap n) (n_wire m)).
  rewrite cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  cbn [Nat.add].
  rewrite <- cast_stack_l, <- stack_nwire_distribute_r.
  rewrite <- cast_stack_l.
  Morphisms.f_equiv.

  rewrite big_yank_r.
  rewrite cast_contract_eq', cast_id.
  reflexivity.
  Unshelve.
  all: lia.
Qed.



Lemma wrap_ubl_ubr {n m o} (zx : ZX n (m + o)) :
  wrap_ubl (wrap_ubr zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite cast_stack_l_fwd, stack_assoc_fwd, n_wire_stack.
  rewrite <- compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
  unshelve erewrite push_out_bot, (cast_compose_mid_distribute (m + o)); [lia..|].
  rewrite cast_contract_eq', cast_id.
  rewrite compose_assoc.
  rewrite <- (nwire_removal_r zx) at 2.
  Morphisms.f_equiv.

  rewrite <- n_wire_stack.
  rewrite 2 stack_assoc_fwd.
  rewrite 2 cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_r, <- stack_nwire_distribute_l.
  rewrite <- cast_stack_r.
  Morphisms.f_equiv.
  rewrite big_yank_r.
  rewrite cast_contract_eq', cast_id.
  reflexivity.
  Unshelve.
  all: lia.
Qed.


Lemma wrap_ubr_ubl {n m o} (zx : ZX (n + m) o) :
  wrap_ubr (wrap_ubl zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite cast_stack_l_fwd, (stack_assoc_fwd zx), n_wire_stack.

  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
  unshelve erewrite pull_out_bot, (cast_compose_mid_distribute (n + m)); [lia..|].
  rewrite cast_contract_eq', cast_id.
  rewrite <- compose_assoc.
  rewrite <- (nwire_removal_l zx) at 2.
  Morphisms.f_equiv.

  rewrite <- n_wire_stack.
  rewrite 2 stack_assoc_fwd.
  rewrite 2 cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_r, <- stack_nwire_distribute_l.
  rewrite <- cast_stack_r.
  Morphisms.f_equiv.
  rewrite big_yank_l.
  rewrite cast_id.
  reflexivity.
  Unshelve.
  all: lia.
Qed.


Lemma wrap_over_top_left {n m o} (zx zx' : ZX (n + m) o) :
  wrap_otl zx ∝= wrap_otl zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_otr_mor.
  now rewrite 2 wrap_otr_otl in Hzx.
Qed.

Lemma wrap_over_top_right {n m o} zx zx' :
  wrap_otr zx ∝= @wrap_otr n m o zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_otl_mor.
  now rewrite 2 wrap_otl_otr in Hzx.
Qed.

Lemma wrap_under_bottom_left {n m o} (zx zx' : ZX (n + m) o) :
  wrap_ubl zx ∝= wrap_ubl zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_ubr_mor.
  now rewrite 2 wrap_ubr_ubl in Hzx.
Qed.

Lemma wrap_under_bottom_right {n m o} zx zx' :
  wrap_ubr zx ∝= @wrap_ubr n m o zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_ubl_mor.
  now rewrite 2 wrap_ubl_ubr in Hzx.
Qed.


Lemma wrap_otl_compose {n m o p} (zx0 : ZX (n + m) o) (zx1 : ZX o p) :
  wrap_otl (zx0 ⟷ zx1) ∝= wrap_otl zx0 ⟷ (n_wire n ↕ zx1).
Proof.
  unfold wrap_otl.
  rewrite stack_nwire_distribute_l, <- cast_compose_l_eq_mid.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_otr_compose {n m o p} (zx0 : ZX n m) (zx1 : ZX m (o + p)) :
  wrap_otr (zx0 ⟷ zx1) ∝= (n_wire o ↕ zx0) ⟷ wrap_otr zx1.
Proof.
  unfold wrap_otr.
  rewrite stack_nwire_distribute_l, <- cast_compose_r_eq_mid.
  rewrite compose_assoc.
  reflexivity.
Qed.


Lemma wrap_ubl_compose {n m o p} (zx0 : ZX (n + m) o) (zx1 : ZX o p) :
  wrap_ubl (zx0 ⟷ zx1) ∝= wrap_ubl zx0 ⟷ (zx1 ↕ n_wire m).
Proof.
  unfold wrap_ubl.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_ubr_compose {n m o p} (zx0 : ZX n m) (zx1 : ZX m (o + p)) :
  wrap_ubr (zx0 ⟷ zx1) ∝= (zx0 ↕ n_wire p) ⟷ wrap_ubr zx1.
Proof.
  unfold wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_otl_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_otl (zx0 ↕ zx1) ∝=
  cast o _ eq_refl (Nat.add_assoc _ _ _) (proc_to_state zx0 ↕ zx1).
Proof.
  unfold wrap_otl, proc_to_state.
  rewrite stack_assoc_back_fwd, cast_contract_eq'.
  rewrite cast_compose_r_eq_mid.
  rewrite <- stack_compose_distr.
  cast_irrelevance.
  now rewrite nwire_removal_l.
Qed.

Lemma wrap_otr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_otr (zx0 ↕ zx1) ∝=
  cast _ _ (Nat.add_assoc _ _ _) eq_refl ((n_wire m ↕ zx0 ⟷ n_cup m) ↕ zx1).
Proof.
  unfold wrap_otr.
  rewrite stack_assoc_back_fwd, cast_contract_eq'.
  rewrite cast_compose_l_eq_mid.
  rewrite <- stack_compose_distr.
  cast_irrelevance.
  now rewrite nwire_removal_r.
Qed.


Lemma wrap_ubl_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubl (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_0_r _)) (eq_sym (Nat.add_assoc _ _ _))
    (zx0 ↕ (n_cap o ⟷ (zx1 ↕ n_wire o))).
Proof.
  unfold wrap_ubl.
  rewrite stack_assoc_fwd.
  rewrite cast_compose_eq_mid_join.
  cast_irrelevance.
  now rewrite <- stack_compose_distr, nwire_removal_l.
Qed.

Lemma wrap_ubr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubr (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_0_r _))
    (zx0 ↕ (zx1 ↕ n_wire p ⟷ n_cup p)).
Proof.
  unfold wrap_ubr.
  rewrite stack_assoc_fwd, cast_compose_eq_mid_join.
  cast_irrelevance.
  rewrite <- stack_compose_distr, nwire_removal_r.
  reflexivity.
Qed.



Lemma wrap_otl_transpose {n m o} zx :
	(@wrap_otl n m o zx) ⊤ ∝= wrap_otr (zx ⊤).
Proof.
	unfold wrap_otl, wrap_otr.
	cbn [transpose].
	rewrite n_cap_transpose, cast_transpose.
	cbn [transpose].
	now rewrite !n_wire_transpose.
Qed.

Lemma wrap_otr_transpose {n m o} zx :
	(@wrap_otr n m o zx) ⊤ ∝= wrap_otl (zx ⊤).
Proof.
	apply transpose_diagrams_eq.
	rewrite wrap_otl_transpose.
	now rewrite 2!transpose_involutive.
Qed.

Lemma wrap_ubl_transpose {n m o} zx :
	(@wrap_ubl n m o zx) ⊤ ∝= wrap_ubr (zx ⊤).
Proof.
	unfold wrap_ubl, wrap_ubr.
	cbn [transpose].
	rewrite cast_transpose.
	cbn [transpose].
	rewrite n_cap_transpose.
	now rewrite !n_wire_transpose.
Qed.

Lemma wrap_ubr_transpose {n m o} zx :
	(@wrap_ubr n m o zx) ⊤ ∝= wrap_ubl (zx ⊤).
Proof.
	apply transpose_diagrams_eq.
	rewrite wrap_ubl_transpose.
	now rewrite 2!transpose_involutive.
Qed.

#[export] Hint Rewrite
  @wrap_otl_transpose @wrap_otr_transpose
  @wrap_otl_transpose @wrap_otr_transpose : transpose_db.


Lemma wrap_otl_colorswap {n m o} zx :
	⊙ (@wrap_otl n m o zx) ∝= wrap_otl (⊙ zx).
Proof.
	unfold wrap_otl.
	cbn [color_swap].
	rewrite n_cap_colorswap, cast_colorswap.
	cbn [color_swap].
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_otr_colorswap {n m o} zx :
	⊙ (@wrap_otr n m o zx) ∝= wrap_otr (⊙ zx).
Proof.
	unfold wrap_otr.
	cbn [color_swap].
	rewrite n_cup_colorswap, cast_colorswap.
	cbn [color_swap].
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_ubl_colorswap {n m o} zx :
	⊙ (@wrap_ubl n m o zx) ∝= wrap_ubl (⊙ zx).
Proof.
	unfold wrap_ubl.
	cbn [color_swap].
	rewrite cast_colorswap.
	cbn [color_swap].
	rewrite n_cap_colorswap.
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_ubr_colorswap {n m o} zx :
	⊙ (@wrap_ubr n m o zx) ∝= wrap_ubr (⊙ zx).
Proof.
	unfold wrap_ubr.
	cbn [color_swap].
	rewrite cast_colorswap.
	cbn [color_swap].
	rewrite n_cup_colorswap.
	now rewrite !n_wire_colorswap.
Qed.

#[export] Hint Rewrite
  @wrap_otl_colorswap @wrap_otr_colorswap
  @wrap_otl_colorswap @wrap_otr_colorswap : colorswap_db.


(* FIXME: Move *)
Lemma zx_of_const_transpose c : (zx_of_const c) ⊤ ∝= zx_of_const c.
Proof.
  prep_matrix_equivalence; rewrite semantics_transpose_comm; now by_cell.
Qed.
Lemma fold_state_plus : Z 0 1 0 ∝= √ 2 .* state_plus.
Proof.
  rewrite state_plus_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.
Lemma fold_state_minus : Z 0 1 PI ∝= √ 2 .* state_minus.
Proof.
  rewrite state_minus_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.

Lemma JPV_2_19 : (— ↕ (Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left))) ⟷
  (X 2 1 PI ↕ —) ⟷ Z 2 1 0 ∝=
  ((Z 1 2 0 ⟷ (zx_triangle_left ↕ zx_triangle)) ↕ —) ⟷
  (— ↕ X 2 1 PI) ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose, triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, 2 stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (@X_1_n_state_b 2 PI b).
  zxsrw (@X_1_n_state_b 2 PI b).
  zxsrw (triangle_state_b b).
  apply (@wrap_over_top_right 0 1 1).
  unfold wrap_otr.
  zxsrw <- (X_wrap_over_top_left 0 1 (if b then (PI + PI)%R else PI)).
  zxaclean_rhs.
  destruct b.
  - rewrite X_eq_2_PI by lra.
    rewrite (X_eq_2_PI 0 2) by lra.
    rewrite <- cap_X.
    apply transpose_diagrams_eq.
    cbn [transpose].
    autorewrite with transpose_db.
    rewrite ?zx_of_const_transpose.
    apply prop_eq_by_eq_on_state_b_1_n.
    intros b.
    zxsrw (Z_1_2_state_b 0 b).
    zxaclean_rhs.
    zxsrw_rhs (cup_pullthrough_top (state_1 ⊤) —).
    rewrite transpose_involutive.
    zxfclean_rhs.
    zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_1.
    zxsrw triangle_state_1.
    zxsrw (cap_pullthrough_top state_1 (state_b b)).
    zxsrw_rhs (state_b_state_b_transpose b true).
    zxsrw (state_b_state_b_transpose b true).
    rewrite <- !zx_of_const_mult'.
    zxsrw (triangle_state_b b).
    destruct b; [rewrite Cmult_1_r; done|].
    cbn.
    rewrite 2 Cmult_0_l, zx_of_const_0, ? stack_0_l.
    done.
  - rewrite X_0_2_PI_to_cup_not.
    apply transpose_diagrams_eq.
    cbn [transpose].
    autorewrite with transpose_db.
    rewrite ?zx_of_const_transpose.
    apply prop_eq_by_eq_on_state_b_1_n.
    intros b.
    zxsrw (Z_1_2_state_b 0 b).
    zxaclean_rhs.
    rewrite <- not_defn.
    zxarw (not_state_b b).
    zxfclean_rhs.
    zxarw (cap_pullthrough_top (state_b (¬ b)) —).
    zxarw <- (n_cap_pullthrough_bot (state_b (¬ b))).
    rewrite (cup_pullthrough_top_1 zx_triangle —).
    rewrite triangle_transpose.
    zxaclean_rhs.
    rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
    rewrite (left_triangle_state_b (¬ b)).
    zxsrw (triangle_state_b b).
    zxsrw (Z_1_n_state_b b 0 0).
    rewrite Cexp_0, Tauto.if_same, zx_of_const_1, compose_empty_l.
    f_equiv.
    destruct b.
    + cbn.
      rewrite not_state_1.
      zxscat.
    + cbn.
      rewrite fold_state_plus.
      zxsrw not_state_plus.
      zxscat.
Qed.

(* FIXME: Move *)
Lemma zx_invsqrt2_to_const :
  zx_invsqrt2 ∝= zx_of_const (/ √ 2).
Proof.
  apply const_of_zx_inj.
  rewrite const_of_zx_invsqrt2, const_of_zx_of_const.
  done.
Qed.

Lemma JPV_2_20 : (Z 0 1 0 ⟷ X 1 0 0) ↕ (Z 1 2 0 ⟷ (— ↕ zx_triangle_left) ⟷ X 2 1 0) ∝=
  zx_triangle_left.
Proof.
  rewrite gadget_is_scaled_empty.
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  rewrite state_b_defn'.
  zxsrw (dominated_X_spider_fusion_top_right 0 0 1 1 (if b then PI else 0) 0).
  rewrite Rplus_0_r.
  rewrite zx_invsqrt2_to_const, <- zx_of_const_mult'.
  rewrite zx_of_const_1' by C_field.
  destruct b.
  - rewrite <- not_defn, fold_state_plus.
    zxsrw not_state_plus.
    zxscat.
  - zxsrw (@X_1_n_state_0 1 0).
    rewrite state_0_defn.
    zxscat.
Qed.

(* FIXME: Move *)
Lemma triangle_state_plus : state_plus ⟷ zx_triangle ∝= state_plus .+ / √ 2 .* state_1.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_semantics.
  rewrite zx_plus_semantics, zx_scale_semantics.
  rewrite state_plus_semantics, state_1_semantics.
  by_cell; lca.
Qed.

Lemma triangle_state_minus : state_minus ⟷ zx_triangle ∝= / √ 2 .* state_0.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_semantics.
  rewrite zx_scale_semantics.
  rewrite state_minus_semantics, state_0_semantics.
  by_cell; lca.
Qed.

Lemma left_triangle_state_plus : state_plus ⟷ zx_triangle_left ∝= state_plus .+ / √ 2 .* state_0.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_left_semantics.
  rewrite zx_plus_semantics, zx_scale_semantics.
  rewrite state_plus_semantics, state_0_semantics.
  by_cell; lca.
Qed.

Lemma left_triangle_state_minus : state_minus ⟷ zx_triangle_left ∝= - / √ 2 .* state_1.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_left_semantics.
  rewrite zx_scale_semantics.
  rewrite state_minus_semantics, state_1_semantics.
  by_cell; lca.
Qed.


Lemma JPV_2_21 : zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI
  ∝= Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (left_triangle_state_b b).
  zxsrw (Z_1_n_state_b b 1 PI).
  rewrite Cexp_PI.
  zxsrw (left_triangle_state_b b).
  destruct b.
  - zxsrw (@Z_spider_1_1_fusion 0 1 0 PI).
    zxsrw (@Z_spider_1_1_fusion 0 1 0 PI).
    rewrite Rplus_0_l.
    rewrite fold_state_minus.
    zxsrw left_triangle_state_minus.
    zxsrw (Z_1_n_state1 1 PI).
    zxsrw left_triangle_state_minus.
    rewrite <- !zx_of_const_mult'.
    do 2 f_equiv.
    rewrite Cexp_PI.
    lca.
  - zxsrw (Z_1_n_state0 1 PI).
    zxsrw (Z_1_n_state0 1 PI).
    zxsrw left_triangle_state_0.
    zxsrw left_triangle_state_0.
    zxsrw (Z_1_n_state0 1 PI).
    rewrite zx_of_const_1.
    zxscat.
Qed.

(* FIXME: Unstateable! Lemma JPV_2_22 : ... *)

Lemma JPV_2_23 β : X 0 1 PI ⟷ zx_triangle_left ⟷ Z 1 2 PI ⟷
  (zx_triangle_left ↕ X 1 2 β) ⟷ ((Z 2 1 PI ⟷ X 1 0 0) ↕ —) ∝=
  (Z 0 1 0 ⟷ X 1 0 0) ↕ (Z 0 1 PI ⟷ X 1 1 β).
Proof.
  zxsrw JPV_2_10.
  zxsrw (gadget_is_scaled_empty (Z 0 1 0 ⟷ X 1 0 0)).
  zxsrw (gadget_is_scaled_empty (Z 0 1 0 ⟷ X 1 0 0)).
  f_equiv.
  pose proof (f_equiv transpose (to_gadget (X_state_copy 0 2 PI eq_refl eq_refl))) as Hrw.
  rewrite Rmult_0_l, Cexp_0, Cexp_PI in Hrw.
  cbn in Hrw.
  rewrite zx_of_const_transpose in Hrw.
  zxsrw Hrw.
  clear Hrw.
  zxsrw (@Z_spider_1_1_fusion 0 2 0 PI).
  rewrite Rplus_0_l.
  pose proof (f_equiv transpose JPV_2_7) as Hrw.
  cbn in Hrw.
  rewrite triangle_transpose in Hrw.
  zxsrw Hrw.
  clear Hrw.
  zxsrw (dominated_X_spider_fusion_top_left 0 0 1 1 0 β).
  zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 0 0 PI).
  rewrite 2 Rplus_0_l.
  zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_of_const_mult'.
  rewrite zx_of_const_1' by (autorewrite with RtoC_db; C_field; lca).
  zxscat.
Qed.



Lemma JPV_2_24 β : Z 1 2 0 ⟷ ((zx_triangle ⟷ X 1 1 β) ↕ (zx_triangle_left ⟷ X 1 1 β))
  ⟷ (— ↕ Z 1 2 0) ⟷ (X 2 1 PI ↕ —) ∝=
  Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left)
  ⟷ (— ↕ Z 1 2 0) ⟷ (X 2 1 PI ↕ X 1 1 β).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  do 2 zxsrw (Z_1_2_state_b 0 b).
  do 2 zxsrw (triangle_state_b b).
  do 2 zxsrw (left_triangle_state_b b).
  f_equiv.
  destruct b.
  - zxsrw (to_gadget (Z_state_copy' false 1 β eq_refl eq_refl)).
    rewrite zx_of_const_1' by (cbn; C_field; lca).
    zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    rewrite Rplus_0_r.
    zxaclean_lhs.
    zxsrw <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxarw_rhs <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxsrw (@X_1_n_state_1 1 β).
    zxsrw (@X_spider_1_1_fusion 0 2 (PI + β) PI).
    rewrite (X_Rmodeq_2PI _ β) by (exists (1 : BinInt.Z); lra).
    zxsrw (@X_1_n_state_1 2 PI).
    rewrite (X_eq_2_PI _ _ (_ + _)) by lra.
    f_equiv.
    rewrite <- (X_proc_to_state 1 1 β).
    unfold proc_to_state.
    zxacat.
  - zxsrw (to_gadget (Z_state_copy' false 1 β eq_refl eq_refl)).
    rewrite zx_of_const_1' by (cbn; C_field; lca).
    zxsrw (@X_1_n_state_0 1 β).
    zxarw_lhs <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxsrw (to_gadget (Z_state_copy' false 2 PI eq_refl eq_refl)).
    rewrite <- zx_of_const_mult'.
    rewrite (f_equal zx_of_const (y:=/ C2)) by (cbn; C_field).
    zxsrw (dominated_Z_spider_fusion_top_right 0 0 1 0 0 0).
    rewrite Rplus_0_r.
    zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 1 0 0).
    rewrite Rplus_0_r.
    zxsrw (Z_1_2_state_0 0).
    zxarw_rhs <- (X_wrap_under_bot_left 1 1 PI eq_refl eq_refl).
    zxsrw (to_gadget (Z_state_copy' false 2 PI eq_refl eq_refl)).
    symmetry.
    rewrite (f_equal zx_of_const (y:=/√2)) by
      (cbn; C_field; lca).
    zxsrw (dominated_Z_spider_fusion_top_right 0 0 1 0 0 0).
    rewrite Rplus_0_r.
    zxsrw (Z_1_n_state0 0 0).
    zxsrw (@X_1_n_state_0 1 β).
    rewrite <- zx_of_const_mult'.
    rewrite (f_equal zx_of_const (y:=/ C2)) by C_field.
    zxscat.
Qed.

(* FIXME: Move *)
Lemma to_const (zx : ZX 0 0) : zx ∝= zx_of_const (const_of_zx zx).
Proof.
  apply const_of_zx_inj.
  now rewrite const_of_zx_of_const.
Qed.

Lemma Z_2_1_states_b b c α :
  state_b b ↕ state_b c ⟷ Z 2 1 α ∝=
  (if eqb b c then (if b then Cexp α else C1) .* state_b b else zx_zero).
Proof.
  rewrite <- (Rplus_0_l α), <- Z_spider_1_1_fusion.
  rewrite <- compose_assoc.
  rewrite (Z_2_1_0_states_b b c).
  destruct (eqb b c); [|now rewrite compose_0_l].
  rewrite (Z_1_n_state_b b 1 α).
  rewrite Rplus_0_l, n_stack_1, 2 cast_id_eq.
  done.
Qed.


Lemma JPV_2_25 :
  (X 1 1 PI ⟷ Z 1 2 0) ↕
  (X 0 1 0 ⟷ Z 1 2 PI) ⟷
  (— ↕ (zx_triangle_left ↕ zx_triangle ⟷ Z 2 2 PI) ↕ —) ⟷
  (X 2 1 0 ↕ X 2 1 0) ⟷ ⨉ ∝=
  - C1 .*
  (Z 1 2 PI) ↕
  (X 0 1 PI ⟷ Z 1 2 PI) ⟷
  (— ↕ (zx_triangle ↕ zx_triangle_left ⟷ Z 2 2 PI) ↕ —) ⟷
  (X 2 1 0 ↕ X 2 1 0).
Proof.
  transitivity (X 1 1 PI ⟷ Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 2 PI) ↕ —) ⟷
    (— ↕ X 2 1 0)). 1:{
    zxsrw (to_gadget (X_state_copy'' false 2 PI eq_refl eq_refl)).
    zxsrw JPV_2_7.
    zxsrw (to_const (Z 0 1 0 ⟷ X 1 0 0)).
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1' by (C_field; lca).
    zxsrw (dominated_Z_spider_fusion_bot_right 0 0 1 2 0 PI).
    rewrite Rplus_0_l.
    zxsrw (dominated_X_spider_fusion_bot_right 0 0 1 1 0 0).
    rewrite Rplus_0_r.
    rewrite X_0_is_wire.
    zxfcat.
  }
  transitivity (Z 1 2 PI ⟷ (— ↕ (zx_triangle ⟷ Z 1 2 PI)) ⟷
    (X 2 1 0 ↕ X 1 1 PI)). 2:{
    zxsrw (to_gadget (X_state_copy'' true 2 PI eq_refl eq_refl)).
    zxsrw JPV_2_10.
    zxsrw (to_const (Z 0 1 0 ⟷ X 1 0 0)).
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_mult'.
    rewrite Cexp_PI'.
    zxsrw (dominated_Z_spider_fusion_bot_right 0 0 1 2 0 PI).
    rewrite Rplus_0_l.
    zxsrw (dominated_X_spider_fusion_bot_right 0 0 1 1 PI 0).
    rewrite Rplus_0_r.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1' by (C_field; lca).
    zxscat.
  }
  transitivity (Z 1 2 0 ⟷ (— ↕ (zx_triangle ⟷ Z 1 2 0)) ⟷
    ((X 2 1 0 ⟷ Z 1 1 PI) ↕ X 1 1 PI)). 2:{
    symmetry.
    rewrite <- (Rplus_0_r PI).
    rewrite <- (@dominated_Z_spider_fusion_top_left 1 0 1 1).
    rewrite Rplus_0_r.
    cbn.
    rewrite (X_wrap_over_top_left 1 1 0) at 1.
    zxsrw JPV_2_6.

    zxsrw (dominated_Z_spider_fusion_top_right 1 0 1 0 PI 0).
    zxsrw (dominated_Z_spider_fusion_bot_right 1 0 1 0 PI (PI + 0)).
    rewrite (Z_eq_2_PI 2 0 (PI + _)) by lra.
    zxsrw <- (X_wrap_over_top_left 1 1 0).
    zxscat.
  }
  transitivity (X 1 1 PI ⟷ Z 1 2 0 ⟷
    (— ↕ (zx_triangle_left ⟷ Z 1 2 0)) ⟷
    ((X 2 1 0 ⟷ Z 1 1 PI) ↕ —)). 2:{
    symmetry.
    rewrite (Z_wrap_over_top_right 1 1 0) at 2.

    pose proof JPV_2_6 as Hrw.
    apply (f_equiv (color_swap ∘ transpose)%prg) in Hrw.
    cbn in Hrw.
    zxsrw Hrw.
    clear Hrw.
    zxsrw <- JPV_2_11.

    zxsrw (cup_pullthrough_bot_1 (X 1 1 PI) —).
    zxsrw (dominated_X_spider_fusion_bot_right 1 0 1 1 PI 0).
    zxsrw <- (dominated_X_spider_fusion_top_right 1 0 1 1 PI 0).
    zxsrw <- (f_equiv color_swap JPV_2_6).
    zxfcat.
  }
  zxsrw notc_is_notc_r.
  zxsrw <- JPV_2_12.
  zxsrw <- cnot_is_cnot_r.
  zxfcat.
Qed.


Fixpoint JPV_2_22_lhs_aux n : ZX (1 + (1 + n)) 1 :=
  match n with
  | 0 => Z (1 + 1) 1 0
  | S n =>
    — ↕ ((Z (1 + 1) 1 0 ⟷ zx_triangle_left) ↕ n_wire n) ⟷ JPV_2_22_lhs_aux n
  end.



Lemma JPV_2_22_aux :
  ⊂ ⟷ (◁ ↕ —) ⟷ Z 2 1 0 ∝= Z 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_n_state_b b 2 0).
  rewrite Cexp_0.
  rewrite zx_of_const_1' by now destruct b.
  zxsrw (triangle_state_b b).
  zxarw (cap_pullthrough_bot (state_b b) —).
  rewrite <- gadget_transpose.
  cbn.
  rewrite transpose_involutive_eq.
  zxsrw (Z_1_n_state_b b 0 0).
  rewrite Cexp_0.
  rewrite zx_of_const_1' by now destruct b.


  destruct b.
  - cbn.
    rewrite (state_b_state_b_transpose true true).
    cbn.
    rewrite zx_scale_1_l.
    done.
  - cbn.
    zxsrw (Z_1_n_state0 0 0).
    done.
Qed.



(* Lemma JPV_2_22 n :
  Z 0 1 0 ↕ Z 0 1 0 ↕ n_wire n ⟷ JPV_2_22_lhs_aux n ∝=
  (⊂ ⟷ (zx_triangle_left ↕ —)) ↕ n_wire n ⟷ JPV_2_22_lhs_aux n.
Proof.
  induction n.
  - cbn.
    zxfclean.
    zxsrw JPV_2_22_aux.
    done.
  - cbn -[n_wire].

    zxpsrw_rhs JPV_2_22_aux.

  assert (n = 1)%nat as -> by admit.
  cbn.
  zxsclean.
  zxfclean. *)


(* Lemma JPV_2_26 *)

End JPV.