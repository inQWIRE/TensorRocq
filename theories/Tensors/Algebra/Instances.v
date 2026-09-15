Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
From TensorRocq Require Import Aux.
From TensorRocq Require Export Algebra.Definitions.
From stdpp Require Import vector fin.
From stdpp Require Export base list.

#[global] Instance Prop_SemiRingData : SemiRingData Prop False True or and := mk_SRD.

#[global] Instance Prop_SemiRing : SemiRing Prop False True or and iff.
Proof.
  split.
  - split; tauto.
  - split; apply _.
  - apply (_ : Equivalence iff).
Qed.

(* Common instances of semirings *)

#[global] Instance nat_SemiRingData : SemiRingData nat 0 1 Nat.add Nat.mul := mk_SRD.

#[global] Instance nat_SemiRing : SemiRing nat 0 1 Nat.add Nat.mul eq.
Proof.
  do 2 constructor; repeat (hnf; intros); lia.
Qed.

#[global] Instance N_SemiRingData : SemiRingData N 0%N 1%N N.add N.mul := mk_SRD.

#[global] Instance N_SemiRing : SemiRing N 0%N 1%N N.add N.mul eq.
Proof.
  do 2 constructor; repeat (hnf; intros); lia.
Qed.

#[global] Instance bool_SemiRingData : SemiRingData bool false true xorb andb := mk_SRD.

#[global] Instance bool_SemiRing : SemiRing bool false true xorb andb eq.
Proof.
  do 2 constructor; repeat (hnf; intros); subst; Btauto.btauto.
Qed.

(* FIXME: Move *)
Lemma fin_add_prf {n} (i j : fin n) : (i + j) mod n < n.
Proof.
  apply Nat.mod_upper_bound.
  inversion i; done.
Qed.
Lemma fin_mul_prf {n} (i j : fin n) : (i * j) mod n < n.
Proof.
  apply Nat.mod_upper_bound.
  inversion i; done.
Qed.
Definition fin_add {n} (i j : fin n) : fin n :=
  nat_to_fin (fin_add_prf i j).
Definition fin_mul {n} (i j : fin n) : fin n :=
  nat_to_fin (fin_mul_prf i j).
Lemma fin_to_nat_add {n} (i j : fin n) :
  fin_add i j =@{nat} (i + j) mod n.
Proof.
  apply fin_to_nat_to_fin.
Qed.
Lemma fin_to_nat_mul {n} (i j : fin n) :
  fin_mul i j =@{nat} (i * j) mod n.
Proof.
  apply fin_to_nat_to_fin.
Qed.

#[global] Instance fin_SemiRingData n : SemiRingData (fin (S (S n))) 0%fin 1%fin fin_add fin_mul := mk_SRD.

#[global] Instance fin_SemiRing n : SemiRing (fin (S (S n))) 0%fin 1%fin fin_add fin_mul eq.
Proof.
  constructor; [| split; apply _|apply eq_equivalence].
  split; intros i; pose proof (fin_to_nat_lt i);
  (try (intros j; pose proof (fin_to_nat_lt j)));
  (try (intros k; pose proof (fin_to_nat_lt k))); apply fin_to_nat_inj; rewrite ?fin_to_nat_mul, ? fin_to_nat_add, ?fin_to_nat_mul.
  - cbn -[Nat.modulo].
    apply Nat.mod_small; done.
  - f_equal; lia.
  - rewrite Nat.Div0.add_mod_idemp_r, Nat.Div0.add_mod_idemp_l.
    f_equal; lia.
  - cbn -[Nat.modulo].
    rewrite Nat.mod_small; lia.
  - cbn -[Nat.modulo].
    rewrite Nat.mod_small; lia.
  - f_equal; lia.
  - rewrite Nat.Div0.mul_mod_idemp_r, Nat.Div0.mul_mod_idemp_l.
    f_equal; lia.
  - rewrite Nat.Div0.mul_mod_idemp_l, <- Nat.Div0.add_mod.
    f_equal; lia.
Qed.

#[global] Instance Z_SemiRingData : SemiRingData Z 0%Z 1%Z Z.add Z.mul := mk_SRD.

#[global] Instance Z_SemiRing : SemiRing Z 0%Z 1%Z Z.add Z.mul eq.
Proof.
  do 2 constructor; repeat (hnf; intros); lia.
Qed.

Require Import Lqa.

Import QArith.

#[global] Instance Q_SemiRingData : SemiRingData Q 0%Q 1%Q Qplus Qmult := mk_SRD.

#[global] Instance Q_SemiRing : SemiRing Q 0%Q 1%Q Qplus Qmult Qeq.
Proof.
  constructor; [|split; apply _|split; apply _].
  constructor; intros; lra.
Qed.

#[global] Instance unit_SemiRingData : SemiRingData unit () () 
  (fun _ _ => ()) (fun _ _ => ()) := mk_SRD.

#[global] Instance unit_SemiRing : SemiRing unit () () 
  (fun _ _ => ()) (fun _ _ => ()) eq.
Proof.
  do 2 constructor; repeat (hnf; intros); repeat_on_hyps ltac:(fun H => try destruct H); done.
Qed.

#[global] Instance prod_SemiRingData {R S} `{SRD : SemiRingData R rO rI radd rmul,
  SSD : SemiRingData S sO sI sadd smul} : SemiRingData (R * S) (rO, sO) (rI, sI)
    (λ '(r, s) '(r', s'), (radd r r', sadd s s'))
    (λ '(r, s) '(r', s'), (rmul r r', smul s s')) := mk_SRD.

#[global] Instance prod_SemiRing {R S seq} `{SR : SemiRing R rO rI radd rmul req,
  SS : SemiRing S sO sI sadd smul seq} : SemiRing (R * S) (rO, sO) (rI, sI)
    (λ '(r, s) '(r', s'), (radd r r', sadd s s'))
    (λ '(r, s) '(r', s'), (rmul r r', smul s s')) (prod_relation req seq).
Proof.
  eassert (Equivalence _) by apply SR.
  eassert (Hradd : Proper _ radd) by apply SR.
  eassert (Hrmul : Proper (req ==> _) rmul) by apply SR.
  eassert (Equivalence _) by apply SS.
  eassert (Hsadd : Proper _ sadd) by apply SS.
  eassert (Hsmul : Proper (seq ==> _) smul) by apply SS.
  split.
  - split; intros [r s]; (try intros [r' s']); (try intros [r'' s'']); split; cbn;
    first [apply SR|apply SS].
  - split; intros [] [] [] [] [] []; split; cbn in *; f_equiv; done.
  - split; apply _.
Qed.




