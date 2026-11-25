From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.


From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)


From TensorRocqEx Require Import VyZXExample_copy.

Import -(notations) ZXsymm.


Module GeneratorNotations.

Definition cap_X := CapCupRules.cup_X.
Definition cup_X := CapCupRules.cap_X.
Definition cap_Z := CapCupRules.cup_Z.
Definition cup_Z := CapCupRules.cap_Z.


Notation "'const' a" := (Some (inr a)) (a at level 10, only printing, at level 1).

Notation "'Z' a" := (Some (inl (false, a))) (a at level 200, only printing, at level 1).
Notation "'Z'" := (Some (inl (false, IZR 0))) (only printing, at level 1).

Notation "'X' a" := (Some (inl (true, a))) (a at level 200, only printing, at level 1).
Notation "'X'" := (Some (inl (true, IZR 0))) (only printing, at level 1).

Notation "'H'" := ((None :> ZXCVERT)) (only printing, at level 1).

Tactic Notation "zxrw" uconstr(lem) :=
  zxsrw lem.

Tactic Notation "zxrw" "<-" uconstr(lem) :=
  zxsrw <- lem.
  
Tactic Notation "zxcat" := zxscat.

Tactic Notation "zxviz" := zxsviz.

End GeneratorNotations.

Import GeneratorNotations.








(* Lemmas for _3_cnot_swap_is_swap *)

Import -(notations) ComposeRules.

Lemma cnot_involutive : _CNOT_R ⟷ _CNOT_ ∝[/ C2] n_wire 2.
Proof.
  apply prop_by_iff_zx_scale; split; [|apply nonzero_div_nonzero; nonzero].
  zxrw (@Z_spider_1_1_fusion 2 2 0 0).
  rewrite (X_wrap_over_top_left 1 1).
  rewrite (X_wrap_over_top_right 1 1) at 1.
  rewrite cap_X, cup_X.
  zxrw (@X_spider_1_1_fusion 2 2 0 0).
  rewrite Rplus_0_l.
  zxrw (X_spider_fusion_top_left_bot_right 1 0 1 0 2 0 0 eq_refl eq_refl).
  rewrite <- cap_X, cap_Z.
  zxrw (Z_spider_fusion_top_left_bot_right 1 0 1 2 0 0 0 eq_refl eq_refl).
  rewrite Rplus_0_r.
  zxviz.
  rewrite grow_X_top_right, (@grow_Z_bot_left 1 2).
  zxrw (to_gadget hopf_rule_X_Z).
  zxrw <- (X_appendix_rot_r 1 1 0 0).
  zxrw <- (@grow_Z_bot_left 1 0 1 0).
  rewrite Rplus_0_r.
  rewrite X_0_is_wire.
  zxcat.
Qed.


Lemma cnot_is_cnot_r : _CNOT_ ∝= _CNOT_R.
Proof.
  zxviz.
  rewrite (Z_wrap_under_bot_left 1 1 _ eq_refl eq_refl); zxviz.
  rewrite (X_wrap_over_top_left 1 1); zxviz.
  zxrw (yank_r).
  zxcat.
Qed.


Lemma cnot_inv_is_swapped_cnot : _CNOT_inv_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉.
Proof.
  zxrw <- (colorswap_is_bihadamard _CNOT_).
  rewrite cnot_is_cnot_r; zxviz.
  rewrite <- (Z_zxperm_absorbtion_left _ _ _ _ ⨉) at 1 by auto_zxperm; zxviz.
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) at 1 by auto_zxperm; zxviz.
  zxcat.
Qed.

(* Immediate consequences of the above, used in final proof: *)

Lemma notc_is_swapp_cnot : _NOTC_ ∝= ⨉ ⟷ _CNOT_ ⟷ ⨉.
Proof.
  rewrite <- cnot_inv_is_swapped_cnot.
  rewrite compose_assoc.
  rewrite <- colorswap_is_bihadamard.
  rewrite cnot_is_cnot_r.
  easy.
Qed.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  rewrite notc_is_swapp_cnot.
  rewrite compose_assoc, (compose_assoc _ ⨉).
  rewrite swap_compose, nwire_removal_r.
  rewrite <- compose_assoc.
  now rewrite swap_compose, nwire_removal_l.
Qed.

Lemma notc_r_is_swapp_cnot_r : _NOTC_R ∝= ⨉ ⟷ _CNOT_R ⟷ ⨉.
Proof.
  rewrite <- cnot_is_cnot_r.
  rewrite <- cnot_inv_is_swapped_cnot.
  rewrite compose_assoc.
  rewrite <- colorswap_is_bihadamard.
  easy.
Qed.

Lemma notc_is_notc_r : _NOTC_ ∝= _NOTC_R.
Proof.
  rewrite notc_is_swapp_cnot.
  rewrite cnot_is_cnot_r.
  rewrite <- notc_r_is_swapp_cnot_r.
  easy.
Qed.



Theorem bi_algebra_rule_X_over_Z :
  X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ ⨉
  ⟷ (X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0) ∝[/ (√2)%R]
  Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0).
Proof.
  zxsymmetry.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].
  zxviz.
  rewrite (Z_wrap_over_top_right).
  rewrite (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl).
  rewrite cap_Z, cup_Z.
  zxrw (to_gadget bi_algebra_rule_X_Z).
  assert (Hrw1 : X 1 2 0 ∝= — ↕ ⊂ ⟷ (— ↕ X 1 2 0 ↕ —) ⟷ (⊃ ↕ n_wire 2)). 1:{
    rewrite cup_X, cap_X.
    zxrw (dominated_X_spider_fusion_top_left 2 0 1 0 0 0).
    rewrite Rplus_0_l.
    zxrw (X_spider_fusion_bot_left_top_right 1 0 2 0 0 0 0 eq_refl eq_refl).
    now rewrite Rplus_0_l.
  }
  assert (Hrw2 : Z 2 1 0 ∝= (n_wire 2 ↕ ⊂) ⟷ (— ↕ Z 2 1 0 ↕ —) ⟷ (⊃ ↕ —)). 1:{
    rewrite cup_Z, cap_Z.
    zxrw (Z_spider_fusion_bot_left_top_right 1 0 1 0 1 0 0 eq_refl eq_refl).
    rewrite Rplus_0_l.
    zxrw (Z_spider_fusion_bot_left_top_right 1 0 1 1 0 0 0 eq_refl eq_refl).
    now rewrite Rplus_0_l.
  }
  zxviz.
  rewrite Hrw1 at 2; zxviz.
  zxrw yank_r.
  rewrite Hrw2 at 1; zxviz.
  zxrw yank_r.
  zxrw yank_r.
  zxcat.
Qed.


Theorem hopf_rule_Z_X_vert n m top bot α β prf :
  Z n (top + 2) α ↕ n_wire bot ⟷
  cast _ _ prf eq_refl
    (n_wire top ↕ X (2 + bot) m β) ∝[/ C2] Z n top α ↕ X bot m β.
Proof.
  rewrite <- (Rplus_0_l α), <- (dominated_Z_spider_fusion_bot_left _ 0).
  rewrite <- (Rplus_0_l β), <- (dominated_X_spider_fusion_top_right _ 0).
  rewrite stack_nwire_distribute_l.
  rewrite stack_assoc_back_fwd, cast_compose_l, cast_contract_eq'.
  rewrite cast_compose_distribute, CastRules.cast_id.
  rewrite <- ComposeRules.compose_assoc.
  rewrite <- stack_nwire_distribute_r.
  rewrite ComposeRules.compose_assoc, <- stack_nwire_distribute_l.
  zxrewrite hopf_rule_Z_X.
  rewrite stack_nwire_distribute_l, <- compose_assoc.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  rewrite stack_assoc_fwd, cast_contract_eq'.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_nwire_distribute_l.
  rewrite dominated_Z_spider_fusion_bot_left,
    dominated_X_spider_fusion_top_right.
  cbn.
  rewrite cast_stack_distribute, cast_id.
  rewrite <- stack_compose_distr.
  rewrite cast_Z_contract_r, nwire_removal_r, cast_Z.
  rewrite nwire_removal_l.
  zxrefl.
  Unshelve.
  all: lia.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxcat.
Qed.






(* #[local] Coercion Nat.b2n : bool >-> nat. *)

(* RNR: Commented out *)
(* #[local] Coercion INR : nat >-> R. *)

Local Notation "'H'" := None (at level 0).

Local Open Scope R_scope.

Definition bell_state_prep :=
  (((X 0 1 0) ↕ (X 0 1 0)) ⟷ (□ ↕ —) ⟷
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0))).  

Lemma bell_state_prep_correct : bell_state_prep ∝= ⊂.
Proof.
  zxviz.
  zxrw <- (colorswap_is_bihadamard (X 0 1 0)).
  zxrw ( @Z_spider_1_1_fusion 0 2 0 0).
  zxrw (X_spider_fusion_bot_left_top_right 1 0 0 0 1 0 0 eq_refl eq_refl).
  rewrite Rplus_0_r, X_0_is_wire; zxviz.
  zxcat.
Qed.


Definition teleportation (a b : nat) :=
  (⊂ ↕ Z 1 2 0) ⟷ ((X 1 1 (INR b * PI) ⟷ Z 1 1 (INR a * PI)) ↕
    (((X 2 1 0) ↕ (Z 1 0 (INR a * PI)) ⟷ (□ ⟷ Z 1 0 (INR b * PI))))).


Lemma teleportation_correct : forall a b, teleportation a b ∝= —.
Proof.
  intros a b.
  unfold teleportation.
  zxviz.
  zxrw <- (colorswap_is_bihadamard (Z 1 0 (INR b * PI))).
  zxrw ( @X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  rewrite cup_X; zxrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  rewrite ?Rplus_0_l, ?Rplus_0_r; zxviz.
  (* About X_spider_fusion_top_left_bot_right. *)
  zxrw (X_spider_fusion_top_left_bot_right 1 0 1 0 0 (INR b * PI) (INR b * PI) eq_refl eq_refl).
  replace ((INR b * PI + INR b * PI))%R with (INR b * 2 * PI)%R by lra;
  zxviz.
  rewrite X_2_PI, X_0_is_wire;
  zxviz.
  zxrw (Z_spider_fusion_top_left_bot_right 1 0 0 1 0 0 (INR a * PI) eq_refl eq_refl).
  rewrite Rplus_0_l; zxviz.
  zxrw ( @Z_spider_1_1_fusion 1 1 (INR a * PI) (INR a * PI)).
  replace ((INR a * PI + INR a * PI))%R with (INR a * 2 * PI)%R by lra;
  zxviz.
  rewrite Z_2_PI, Z_0_is_wire;
  zxcat.
Qed.



Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split; [|apply nonzero_div_nonzero, Cmult_neq_0; nonzero].
  zxviz.
  rewrite cnot_is_swapp_notc at 2; zxviz.
  rewrite notc_is_notc_r; zxviz.
  zxrw (to_gadget bi_algebra_rule_X_over_Z).
  zxrw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  rewrite Rplus_0_l; zxviz.
  zxrw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  rewrite Rplus_0_l; zxviz.
  zxrw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxrw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr; zxviz.
  zxcat.
Qed.









Definition bell_measurement (a b : nat) :=
  (_CNOT_ ⟷ (((Z 1 0 ((INR a) * PI))) ↕ (X 1 0 ((INR b) * PI)))).

Lemma bell_measurement_eq : forall a b,
  bell_measurement a b ∝= (Z 1 1 (INR a * PI) ⟷ X 1 1 (INR b * PI)) ↕ — ⟷ ⊃.
Proof.
  intros a b.
  zxviz.
  zxrw ( @X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  zxrw <- (Z_appendix_rot_r 1 1 0 (INR a * PI)).
  rewrite Rplus_0_l, Rplus_0_r;
  zxviz.
  rewrite cap_X;
  zxrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  rewrite Rplus_0_r.
  zxcat.
Qed.

Definition teleportation_2
  (a b : nat) :=
  (— ↕ bell_state_prep) ⟷ ((bell_measurement a b) ↕
                          (X 1 1 (INR b * PI) ⟷ (Z 1 1 (INR a * PI)))).

Lemma teleportation_2_correct : forall (a b : nat), teleportation_2 a b ∝= —.
Proof.
  intros a b.
  zxviz.
  zxrw (bell_measurement_eq a b).
  rewrite cap_X;
  zxrw (bell_state_prep_correct).
  rewrite cup_X;
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) by auto_zxperm;
  zxviz.
  zxrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  zxrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  rewrite Rplus_0_r;
  rewrite <- (X_zxperm_absorbtion_left _ _ _ _ ⨉) by auto_zxperm;
  zxviz.
  zxrw (X_spider_fusion_top_left_bot_right 1 0 1 0 0 (INR b * PI) (INR b * PI) eq_refl eq_refl).
  replace ((INR b * PI + INR b * PI))%R with (INR b * 2 * PI)%R by lra;
  rewrite X_2_PI, X_0_is_wire; zxviz.
  zxrw ( @Z_spider_1_1_fusion 1 1 (INR a * PI) (INR a * PI)).
  replace ((INR a * PI + INR a * PI))%R with (INR a * 2 * PI)%R by lra;
  rewrite Z_2_PI, Z_0_is_wire;
  zxcat.
Qed.