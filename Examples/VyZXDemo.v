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

Notation "'const' a" := (Some (inr a)) (a at level 10, only printing, at level 1).

Notation "'Z' a" := (Some (inl (false, a))) (a at level 10, only printing, at level 1).
Notation "'Z'" := (Some (inl (false, IZR 0))) (only printing, at level 1).

Notation "'X' a" := (Some (inl (true, a))) (a at level 10, only printing, at level 1).
Notation "'X'" := (Some (inl (true, IZR 0))) (only printing, at level 1).

Notation "'H'" := ((None :> ZXCVERT)) (only printing, at level 1).

End GeneratorNotations.


(* #[local] Coercion Nat.b2n : bool >-> nat. *)

#[local] Coercion INR : nat >-> R.

Local Notation "'H'" := None (at level 0).

Local Open Scope R_scope.

Definition bell_state_prep :=
  (((X 0 1 0) ↕ (X 0 1 0)) ⟷ (□ ↕ —) ⟷
  ((Z 1 2 0 ↕ —) ⟷ (— ↕ X 2 1 0))).

Lemma bell_state_prep_correct : bell_state_prep ∝= ⊂.
Proof.
  zxsviz.
  zxsrw <- (colorswap_is_bihadamard (X 0 1 0)).
  zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
  zxsrw (X_spider_fusion_bot_left_top_right 1 0 0 0 1 0 0 eq_refl eq_refl).
  rewrite Rplus_0_r, X_0_is_wire;
  zxscat.
Qed.


Definition teleportation (a b : nat) :=
  (⊂ ↕ Z 1 2 0) ⟷ ((X 1 1 (INR b * PI) ⟷ Z 1 1 (INR a * PI)) ↕
    (((X 2 1 0) ↕ (Z 1 0 (INR a * PI)) ⟷ (□ ⟷ Z 1 0 (INR b * PI))))).


Lemma teleportation_correct : forall a b, teleportation a b ∝= —.
Proof.
  intros a b.
  unfold teleportation.
  zxsviz.
  rewrite cap_X;
  zxsviz.
  zxsrw <- (colorswap_is_bihadamard (Z 1 0 (INR b * PI))).
  zxsrw (@X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  zxsrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) by auto_zxperm;
  rewrite <- (X_zxperm_absorbtion_left _ _ _ _ ⨉) by auto_zxperm;
  rewrite Rplus_0_l, Rplus_0_r;
  zxsviz.
  zxsrw (X_spider_fusion_bot_left_top_right 1 0 1 0 0 (b * PI) (b * PI) eq_refl eq_refl).
  replace ((INR b * PI + INR b * PI))%R with (INR b * 2 * PI)%R by lra;
  zxsviz.
  rewrite X_2_PI, X_0_is_wire;
  zxsviz.
  zxsrw <- (@Z_add_r 1 1 0 (a * PI) 0 (a * PI)).
  replace ((INR a * PI + 0 + INR a * PI))%R with (INR a * 2 * PI)%R by lra.
  zxsviz.
  rewrite Z_2_PI, Z_0_is_wire;
  zxscat.
Qed.


Definition bell_measurement (a b : nat) :=
  (_CNOT_ ⟷ (((Z 1 0 ((INR a) * PI))) ↕ (X 1 0 ((INR b) * PI)))).

Lemma bell_measurement_eq : forall a b,
  bell_measurement a b ∝= (Z 1 1 (INR a * PI) ⟷ X 1 1 (INR b * PI)) ↕ — ⟷ ⊃.
Proof.
  intros a b.
  zxsviz.
  zxsrw (@X_spider_1_1_fusion 2 0 0 (INR b * PI)).
  zxsrw <- (Z_appendix_rot_r 1 1 0 (INR a * PI)).
  rewrite Rplus_0_l, Rplus_0_r;
  zxsviz.
  zxsrw cup_X.
  zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  rewrite Rplus_0_r.
  zxscat.
Qed.

Definition teleportation_2
  (a b : nat) :=
  (— ↕ bell_state_prep) ⟷ ((bell_measurement a b) ↕
                          (X 1 1 (INR b * PI) ⟷ (Z 1 1 (INR a * PI)))).

Lemma teleportation_2_correct : forall (a b : nat), teleportation_2 a b ∝= —.
Proof.
  intros a b.
  zxsviz.
  zxsrw (bell_measurement_eq a b).
  rewrite cup_X;
  zxsrw (bell_state_prep_correct).
  rewrite cap_X;
  rewrite <- (X_zxperm_absorbtion_right _ _ _ _ ⨉) by auto_zxperm;
  zxsviz.
  zxsrw (X_spider_fusion_bot_left_top_right 0 0 1 0 1 0 (INR b * PI) eq_refl eq_refl).
  zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 1 0 (INR b * PI) 0 eq_refl eq_refl).
  rewrite Rplus_0_r;
  rewrite <- (X_zxperm_absorbtion_left _ _ _ _ ⨉) by auto_zxperm;
  zxsviz.
  zxsrw (X_spider_fusion_top_left_bot_right 1 0 1 0 0 (INR b * PI) (INR b * PI) eq_refl eq_refl).
  replace ((INR b * PI + INR b * PI))%R with (INR b * 2 * PI)%R by lra;
  rewrite X_2_PI, X_0_is_wire; zxsviz.
  zxsrw (@Z_spider_1_1_fusion 1 1 (INR a * PI) (INR a * PI)).
  replace ((INR a * PI + INR a * PI))%R with (INR a * 2 * PI)%R by lra;
  rewrite Z_2_PI, Z_0_is_wire;
  zxscat.
Qed.