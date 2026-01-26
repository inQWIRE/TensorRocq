Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

Require Export Summable.

Definition Tensor {R} (n m : nat) (A : Type) := 
  Vector.t A n -> Vector.t A m -> R.

Definition PackedTensor {R} (A : Type) :=
  {n : nat & {m : nat & Tensor (R:=R) n m A}}.

Definition DimensionlessTensor {R} (A : Type) :=
  forall n m,
    Tensor (R:=R) n m A.

Class TensorLike (R : Type) (A : Type) (T  : Type) := {
  interpretTensor (x : T) : DimensionlessTensor (R:=R) A
}.

#[global] Hint Mode TensorLike - - + : typeclass_instances.


(* NB : We require a semiring (even though we use only equality)
  so typeclass inference is better-behaved *)
Definition permutative_tensor `{SemiRing R rO rI radd rmul req} {n m} {A}
  (t : Tensor n m A) :=
  forall v v' w w', Permutation (vec_to_list v) (vec_to_list v') ->
    Permutation (vec_to_list w) (vec_to_list w') ->
    req (t v w) (t v' w').

(* TODO: Reason about *)
Definition strongly_permutative_tensor `{SemiRing R rO rI radd rmul req} {A}
  (t : DimensionlessTensor A) : Prop :=
  forall n m n' m' v w v' w',
    Permutation (vec_to_list v ++ vec_to_list w) 
      (vec_to_list v' ++ vec_to_list w') ->
    req (t n m v w) (t n' m' v' w').

Class PermutativeTensorLike `{SemiRing R rO rI radd rmul req}
  `(TensT : TensorLike R A T) := {
  interpretTensorPermutative (x : T) n m : 
    permutative_tensor (interpretTensor x n m);
}.

Class StronglyPermutativeTensorLike `{SemiRing R rO rI radd rmul req}
  `(TensT : TensorLike R A T) := {
  interpretTensorStronglyPermutative (x : T) : 
    strongly_permutative_tensor (interpretTensor x);
}.

Lemma strongly_permutative_tensor_permutative_tensor 
  `{SemiRing R rO rI radd rmul req} {A} (t : @DimensionlessTensor R A) : 
  strongly_permutative_tensor t -> forall n m,
  permutative_tensor (t n m).
Proof.
  intros Hperm n m v v' w w' Hv Hw.
  apply Hperm.
  now apply Permutation_app.
Qed.

#[global] Instance StronglyPermutativeTensorLike_PermutativeTensorLike
  `{SemiRing R rO rI radd rmul req} `(TensT : TensorLike R A T) 
  (SP : StronglyPermutativeTensorLike TensT) : PermutativeTensorLike TensT.
Proof.
  constructor; intros; apply strongly_permutative_tensor_permutative_tensor, 
    interpretTensorStronglyPermutative.
Qed.
