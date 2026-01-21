Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Set Warnings "-stdlib-vector".
Require Vector.
Import Vector.VectorNotations.

Require Export Summable.

Definition Tensor {R} (n m : nat) (A : Type) := 
  Vector.t A n -> Vector.t A m -> R.

Definition PackedTensor {R} (A : Type) :=
  {n : nat & {m : nat & Tensor (R:=R) n m A}}.

Definition DimensionlessTensor {R} (A : Type) :=
  forall n m,
    Tensor (R:=R) n m A.