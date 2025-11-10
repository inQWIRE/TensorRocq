Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Require Import QuantumLib.Complex.
Require Import QuantumLib.Summation.
Require Import Vector.
Import Vector.VectorNotations.


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

End SumDefs.