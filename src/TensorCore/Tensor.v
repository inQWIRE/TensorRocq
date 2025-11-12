Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Summation.
Require Import Vector.
Import Vector.VectorNotations.

Require Import FieldSum.

Section Tensor.

  Variable A : Type.
  Variable F : Type.
  Context `{fieldF : Field F}.
  Context `{fsumA : FieldSum A F}.

  Definition Tensor {F : Type} `{FieldF : Field F} 
    (n m : nat) (A : Type) := 
    Vector.t A n -> Vector.t A m -> F.

  Definition PackedTensor {F : Type} `{FieldF : Field F} (A : Type) :=
    {n : nat & {m : nat & Tensor n m A}}.

  Program Fixpoint fsum_vec {n: nat} (f: Vector.t A n -> F) : F :=
      match n with
      | O => f []
      | S _ => fsum (fun b : A => fsum_vec (fun bs => f (b :: bs)))
      end.

  Theorem fsum_vec_ext {n: nat} (f g: Vector.t A n -> F) :
      (forall bs, f bs = g bs) ->
      fsum_vec f = fsum_vec g.
      induction n.
      - simpl. easy.
      - simpl. 
        intros feqg.
        apply fsum_ext.
        intros b.
        destruct (IHn (fun bs => f (b :: bs)) (fun bs => g (b :: bs))).
        intros bs.
        apply (feqg (b :: bs)).
        reflexivity.
  Qed.

  Theorem fsum_vec_succ0 {n: nat} (f: Vector.t A (S n) -> F) :
      fsum_vec f = fsum (fun b => fsum_vec (fun bs => f (b :: bs))).
  Proof.
      reflexivity.
  Qed.

  Theorem fsum_vec_comm1_0 {n : nat} (f: A -> Vector.t A n -> F) :
      fsum (fun b => fsum_vec (fun bs => f b bs)) =
      fsum_vec (fun bs => fsum (fun b => f b bs)).
  Proof.
      induction n.
      - easy.
      - setoid_rewrite fsum_vec_succ0 at 1.
        rewrite fsum_comm.
        setoid_rewrite IHn at 1.
        rewrite fsum_vec_succ0.
        reflexivity.
  Qed.

  Instance fsum_vec_morphism {n : nat}:
          Proper (pointwise_relation (Vector.t A n) eq ==> eq) fsum_vec.
  Proof.
      simpl_relation.
      apply fsum_vec_ext.
      assumption.
  Qed.

  Theorem fsum_vec_comm {n m : nat} (f : Vector.t A n -> Vector.t A m -> F):
      fsum_vec (fun a => fsum_vec (fun b => f a b)) =
      fsum_vec (fun b => fsum_vec (fun a => f a b)).
  Proof.
      induction n.
      - easy.
      - setoid_rewrite fsum_vec_succ0.
        rewrite <- fsum_vec_comm1_0.
        apply fsum_ext.
        intros b.
        apply IHn.
  Qed.

  Theorem fsum_vec_distr {n: nat} (f: Vector.t A n -> F) (c : F):
      c * fsum_vec f = fsum_vec (fun bs => c * f bs).
  Proof.
      induction n.
      - reflexivity.
      - simpl.
        rewrite fsum_distr.
        apply fsum_ext; intros.
        apply IHn.
  Qed.


  #[global] Instance FieldSum_vec {n: nat}: FieldSum (Vector.t A n) F :=
    { fsum := fsum_vec;
      fsum_ext := fsum_vec_ext;
      fsum_comm := fsum_vec_comm;
      fsum_distr := fsum_vec_distr }.

  Theorem fsum_vec_zero (f : Vector.t A 0 -> F) :
      fsum f = f [].
      reflexivity.
  Qed.

  Theorem fsum_vec_succ {n: nat} (f: Vector.t A (S n) -> F) :
      fsum f = fsum (fun b => fsum (fun bs => f (b :: bs))).
  Proof.
      reflexivity.
  Qed.

  Theorem fsum_vec_comm1 {n : nat} (f: A -> Vector.t A n -> F) :
      fsum (fun b => fsum (fun bs => f b bs)) =
      fsum (fun bs => fsum (fun b => f b bs)).
  Proof.
      assert (fsumveceq : forall n (f : Vector.t A n -> F), fsum f = fsum_vec f).
      reflexivity.
      setoid_rewrite fsumveceq.
      rewrite fsum_vec_comm1_0.
      reflexivity.
  Qed.

  Theorem fsum_vec_singleton (f: Vector.t A 1 -> F) :
      fsum f = fsum (fun b => f [b]).
  Proof.
      easy.
  Qed.

  Theorem fsum_vec_append {n m: nat} (f: Vector.t A (n + m) -> F) :
      fsum f = fsum (fun bs1 => fsum (fun bs2 => f (bs1 ++ bs2))).
  Proof.
      induction n as [|n IHn].
      - simpl. reflexivity.
      - simpl.
        repeat rewrite fsum_vec_succ.
        apply fsum_ext.
        intros b.
        rewrite IHn.
        simpl.
        reflexivity.
  Qed.

End Tensor.