Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Summation.
Require Import Fin.

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

  Fixpoint fsum_fin {n : nat} (f : Fin.t n -> F) : F :=
  match n, f with
  | O, _ => 0
  | S k, _ => f F1 + fsum_fin (fun fin => f (FS fin))
  end.

  Lemma fsum_fin_ext {n : nat} (f g : Fin.t n -> F) : 
    (forall b, f b = g b) -> fsum_fin f = fsum_fin g.
  Proof.
    intros.
    induction n.
    - reflexivity.
    - simpl.
      rewrite H9.
      rewrite (IHn (fun fin : t n => f (FS fin)) (fun fin : t n => g (FS fin))).
      reflexivity.
      intros.
      apply H9.
  Qed.

  Lemma fsum_fin_zero {n : nat} :
    @fsum_fin n (fun fin => 0) = 0.
  Proof.
    induction n.
    - reflexivity.
    - simpl.
      rewrite IHn.
      field.
  Qed.

  Lemma fsum_fin_distr_plus {n : nat} : forall (f0 f1 : Fin.t n -> F),
    @fsum_fin n (fun fin => f0 fin + f1 fin) = @fsum_fin n (fun fin => f0 fin) + @fsum_fin n (fun fin => f1 fin).
  Proof.
    intros.
    induction n.
    - simpl. field.
    - simpl.
      field_simplify.
      rewrite IHn.
      field.
  Qed.

  Lemma fsum_fin_comm {n m : nat} (f : Fin.t n -> Fin.t m -> F):
        fsum_fin (fun a => fsum_fin (fun b => f a b)) =
        fsum_fin (fun b => fsum_fin (fun a => f a b)).
  Proof.
    induction n.
    - rewrite fsum_fin_zero.
      reflexivity.
    - simpl.
      rewrite fsum_fin_distr_plus.
      rewrite IHn.
      field.
  Qed.

  Lemma fsum_fin_distr {n : nat} (f : Fin.t n -> F) (b : F) :
    b * fsum_fin (fun a => f a) = fsum_fin (fun a => b * f a).
  Proof.
    induction n.
    - simpl. field.
    - simpl.
      field_simplify.
      rewrite IHn.
      field.
  Qed.

  #[global] Instance FieldSum_fin {n : nat} : FieldSum (Fin.t n) F :=
    { fsum := fsum_fin;
      fsum_ext := fsum_fin_ext;
      fsum_comm := fsum_fin_comm;
      fsum_distr := fsum_fin_distr }.

End SumDefs.