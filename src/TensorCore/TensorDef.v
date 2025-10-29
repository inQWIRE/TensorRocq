Require Import Vector.
Require Import QuantumLib.Summation.
Import Vector.VectorNotations.
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.

(* From mathcomp Require Import ssreflect ssrnat ssrbool tuple. *)

Class FieldSum (A : Type) (F : Type) `{FieldF : Field F} :=
{ fsum : (A -> F) -> F;
  fsum_ext (f g : A -> F) : (forall b, f b = g b) -> fsum f = fsum g;
  fsum_comm (f : A -> A -> F):
    fsum (fun a => fsum (fun b => f a b)) =
    fsum (fun b => fsum (fun a => f a b)) ;
  fsum_distr (f : A -> F) (b : F):
    b * fsum (fun a => f a) = fsum (fun a => b * f a)  }.

#[global] Opaque fsum.
#[global] Notation "∑ x , e" := 
  (fsum (fun x => (e))) (at level 50, x at level 60).
#[global] Notation "∑ x : n , e" := 
  (fsum (fun x : Vector.t _ n => (e))) 
    (at level 50, x at level 60, n at level 60).

Locate Field.

Section SumDefs.

Generalizable All Variables.
Variable A : Type.
Variable F : Type.
Context `{fieldF : Field F}.
Context `{fsumA : FieldSum A F}.

  Add Field F_field_field : G_field_theory.

(* enables rewriting to be done underneath a summation, via "setoid_rewrite" *)
#[global] Instance fsum_morphism :
    Proper (pointwise_relation A eq ==> eq) fsum.
Proof.
    simpl_relation.
    unfold pointwise_relation in H.
    apply fsum_ext.
    assumption.
Qed.

Theorem fsum_distl (f : A -> F) (c : F):
    (∑ a , f a) * c = ∑ a , f a * c.
Proof.
    rewrite Gmult_comm.
    rewrite fsum_distr.
    apply fsum_ext; intros.
    rewrite Gmult_comm.
    reflexivity.
Qed.

Definition fsum_bool (f : bool -> F) : F :=
  f false + f true.

Theorem fsum_bool_ext (f g: bool -> F):
    (forall b, f b = g b) -> fsum_bool f = fsum_bool g.
Proof.
    intros.
    unfold fsum_bool.
    repeat rewrite H9.
    reflexivity.
Qed.

Theorem fsum_bool_comm (f : bool -> bool -> F):
      fsum_bool (fun a => fsum_bool (fun b => f a b)) =
      fsum_bool (fun b => fsum_bool (fun a => f a b)).
Proof.
    unfold fsum_bool.
    field.
Qed.

Theorem fsum_bool_distr (f : bool -> F) (c : F):
    c * fsum_bool f = fsum_bool (fun b => c * f b).
Proof.
    unfold fsum_bool.
    ring.
Qed.

#[global] Instance FieldSum_bool : FieldSum bool F :=
  { fsum := fsum_bool;
    fsum_ext := fsum_bool_ext;
    fsum_comm := fsum_bool_comm;
    fsum_distr := fsum_bool_distr }.

Theorem fsum_bool_def (f : bool -> F): fsum f = f false + f true.
Proof.
    reflexivity.
Qed.


Fixpoint fsum_vec {n: nat} (f: Vector.t A n -> F) : F :=
    match n, f with
    | O, _ => f []
    | S _, _ => fsum (fun b : A => fsum_vec (fun bs => f (b :: bs)))
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

End SumDefs.

