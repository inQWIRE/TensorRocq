Require Import Setoid Reals Lra.
From QuantumLib Require Import RealAux.

Open Scope R_scope.

Definition Rmodeq (q : R) : relation R :=
  fun r r' => exists (z : Z), r = r' + q * IZR z.

Notation "r '=[mod'  q ']' r'" := (Rmodeq q r%R r'%R) 
  (at level 70) : R_scope.

Lemma Rmodeq_refl q r : r =[mod q] r.
Proof.
  exists 0%Z.
  lra.
Qed.

Lemma Rmodeq_symm q r r' : r =[mod q] r' -> r' =[mod q] r.
Proof.
  intros (z & ->).
  exists (Z.opp z).
  rewrite opp_IZR.
  lra.
Qed.

Lemma Rmodeq_trans q r r' r'' : r =[mod q] r' -> r' =[mod q] r'' -> r =[mod q] r''.
Proof.
  intros (z & ->) (z' & ->).
  exists (z + z')%Z.
  rewrite plus_IZR.
  lra.
Qed.

Add Parametric Relation q : R (Rmodeq q)
  reflexivity proved by (Rmodeq_refl q)
  symmetry proved by (Rmodeq_symm q)
  transitivity proved by (Rmodeq_trans q)
  as Rmodeq_setoid.

Lemma Rmodeq_mult q (z : Z) r r' : 
  r =[mod IZR z * q] r' -> r =[mod q] r'.
Proof.
  intros (z' & ->).
  exists (z * z')%Z.
  rewrite mult_IZR.
  lra.
Qed.

Lemma Rmodeq_mult_Z_l q (z : Z) r r' : 
  r =[mod q] r' -> IZR z * r =[mod q] IZR z * r'.
Proof.
  intros (z' & ->).
  exists (z * z')%Z.
  rewrite mult_IZR.
  lra.
Qed.

Lemma Rmodeq_mult_Z_r q (z : Z) r r' : 
  r =[mod q] r' -> r * IZR z =[mod q] r' * IZR z.
Proof.
  intros (z' & ->).
  exists (z * z')%Z.
  rewrite mult_IZR.
  lra.
Qed.

Lemma Rmodeq_self q : 
  q =[mod q] 0.
Proof.
  exists 1%Z.
  lra.
Qed.

Lemma Rmodeq_self_mul_Z_l q (z : Z) : 
  IZR z * q =[mod q] 0.
Proof.
  exists z%Z.
  lra.
Qed.

Lemma Rmodeq_self_mul_Z_r q (z : Z) : 
  q * IZR z =[mod q] 0.
Proof.
  exists z%Z.
  lra.
Qed.

Add Parametric Morphism q : Rplus with signature
  Rmodeq q ==> Rmodeq q ==> Rmodeq q as Rmodeq_plus.
Proof.
  intros _ r (z & ->) _ s (z' & ->).
  exists (z + z')%Z.
  rewrite plus_IZR.
  lra.
Qed.

Add Parametric Morphism q : Ropp with signature
  Rmodeq q ==> Rmodeq q as Rmodeq_opp.
Proof.
  intros _ r (z & ->).
  exists (Z.opp z)%Z.
  rewrite opp_IZR.
  lra.
Qed.

Add Parametric Morphism q : Rminus with signature
  Rmodeq q ==> Rmodeq q ==> Rmodeq q as Rmodeq_minus.
Proof.
  intros _ r (z & ->) _ s (z' & ->).
  exists (z - z')%Z.
  rewrite minus_IZR.
  lra.
Qed.

Lemma sin_2PI_Z (z : Z) : 
  sin (2 * PI * IZR z) = 0.
Proof.
  induction z using Z.peano_ind.
  - now rewrite Rmult_0_r, sin_0.
  - rewrite succ_IZR, Rmult_plus_distr_l, Rmult_1_r, sin_plus.
    rewrite sin_2PI, cos_2PI, IHz.
    lra.
  - unfold Z.pred. 
    rewrite plus_IZR, Rmult_plus_distr_l, sin_plus.
    replace (2 * PI * -1) with (- (2 * PI)) by lra.
    rewrite cos_neg, sin_neg.
    rewrite sin_2PI, cos_2PI, IHz.
    lra.
Qed.

Lemma cos_2PI_Z (z : Z) : 
  cos (2 * PI * IZR z) = 1.
Proof.
  induction z using Z.peano_ind.
  - now rewrite Rmult_0_r, cos_0.
  - rewrite succ_IZR, Rmult_plus_distr_l, Rmult_1_r, cos_plus.
    rewrite sin_2PI, cos_2PI, IHz.
    lra.
  - unfold Z.pred. 
    rewrite plus_IZR, Rmult_plus_distr_l, cos_plus.
    replace (2 * PI * -1) with (- (2 * PI)) by lra.
    rewrite cos_neg, sin_neg.
    rewrite sin_2PI, cos_2PI, IHz.
    lra.
Qed.


Add Parametric Morphism : sin with signature 
  Rmodeq (2 * PI) ==> eq as Rmodeq2PI_sin.
Proof.
  intros _ r (z & ->).
  rewrite sin_plus, sin_2PI_Z, cos_2PI_Z.
  lra.
Qed.

Add Parametric Morphism : cos with signature 
  Rmodeq (2 * PI) ==> eq as Rmodeq2PI_cos.
Proof.
  intros _ r (z & ->).
  rewrite cos_plus, sin_2PI_Z, cos_2PI_Z.
  lra.
Qed.