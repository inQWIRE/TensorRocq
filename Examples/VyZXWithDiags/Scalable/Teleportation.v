From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules
GateDefinitions ZXCore CoreRules Bell.

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


Local Coercion INR : nat >-> R.

Definition bell_state_prep :=
  (((X 0 1 0) ↕ (X 0 1 0)) ⟷ (□ ↕ —) ⟷
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0))).

Lemma bell_state_prep_correct : bell_state_prep ∝= ⊂.
Proof.
  (* Reset Ltac Profile. *)
  zxsrw <- (colorswap_is_bihadamard (X 0 1 0)).
  zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
  zxsrw (X_spider_fusion_bot_left_top_right 1 0 0 0 1 0 0 eq_refl eq_refl).
  rewrite <- cap_Z, X_0_is_wire.
  zxscat.
  (* Show Ltac Profile. *)
(* Time *) Qed.


Definition teleportation (a b : nat) :=
  (⊂ ↕ Z 1 2 0) ⟷ ((X 1 1 (INR b * PI) ⟷ Z 1 1 (INR a * PI)) ↕
    (((X 2 1 0) ↕ (Z 1 0 (INR a * PI)) ⟷ (□ ⟷ Z 1 0 (INR b * PI))))).


Lemma teleportation_correct : forall a b, teleportation a b ∝= —.
Proof.
  (* Reset Ltac Profile. *)
  intros a b.
  unfold teleportation.
  rewrite cap_X.
  zxsrw <- (colorswap_is_bihadamard (Z 1 0 (INR b * PI))).
  zxsrw (@X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  zxsrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) by auto_zxperm.
  rewrite <- (X_zxperm_absorbtion_left _ _ _ _ ⨉) by auto_zxperm.
  zxsrw (X_spider_fusion_bot_left_top_right 1 0 1 0 0 (b * PI) (b * PI) eq_refl eq_refl).
  replace (2 * b * PI)%R with (INR b * 2 * PI)%R by lra.
  rewrite X_2_PI, X_0_is_wire.
  zxsrw <- (@Z_add_r 1 1 0 (a * PI) 0 (a * PI)).
  replace ((INR a * PI + 0 + INR a * PI))%R with (INR a * 2 * PI)%R by lra.
  replace (2 * a * PI)%R with (a * 2 * PI)%R by lra.
  rewrite Z_2_PI, Z_0_is_wire.
  zxscat.
  (* Show Ltac Profile. *)
(* Time *) Qed.


Definition bell_measurement (a b : nat) :=
  (_CNOT_ ⟷ (((Z 1 0 ((INR a) * PI))) ↕ (X 1 0 ((INR b) * PI)))).

Lemma bell_measurement_eq : forall a b,
  bell_measurement a b ∝= (Z 1 1 (INR a * PI) ⟷ X 1 1 (INR b * PI)) ↕ — ⟷ ⊃.
Proof.
  (* Set Ltac Profiling.
  Reset Ltac Profile. *)
  intros a b.
  zxsrw (@X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  zxsrw <- (Z_appendix_rot_r 1 1 0 (INR a * PI)).
  rewrite cup_X.
  zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  zxscat.
  (* Show Ltac Profile. *)
(* Time *) Qed.

Definition teleportation_2
  (a b : nat) :=
  (— ↕ bell_state_prep) ⟷ ((bell_measurement a b) ↕
                          (X 1 1 (INR b * PI) ⟷ (Z 1 1 (INR a * PI)))).

Lemma teleportation_2_correct : forall (a b : nat), teleportation_2 a b ∝= —.
Proof.
  (* Set Ltac Profiling.
  Reset Ltac Profile. *)
  intros a b.
  zxsrw (bell_measurement_eq a b).
  zxsrw (bell_state_prep_correct).
  rewrite <- cap_Z, cap_X.
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) by auto_zxperm.
  zxsrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  rewrite <- cup_Z, cup_X.
  zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  rewrite <- (X_zxperm_absorbtion_left _ _ _ _ ⨉) by auto_zxperm.
  zxsrw (X_spider_fusion_top_left_bot_right 1 0 1 0 0 (INR b * PI) (INR b * PI) eq_refl eq_refl).
  replace ((2 * b * PI))%R with (INR b * 2 * PI)%R by lra.
  rewrite X_2_PI, X_0_is_wire.
  zxsrw (@Z_spider_1_1_fusion 1 1 (INR a * PI) (INR a * PI)).
  replace (2 * a * PI)%R with (INR a * 2 * PI)%R by lra.
  rewrite Z_2_PI, Z_0_is_wire.
  reflexivity.
  (* Show Ltac Profile. *)
(* Time *) Qed.
