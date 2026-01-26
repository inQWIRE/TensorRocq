Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

Require Export SummableWF.

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

Definition tensoreq `{SemiRing R rO rI radd rmul req} 
  `{Summable A} {n m} : relation (@Tensor R n m A) :=
  fun t t' => forall v w, SummedElement v -> SummedElement w -> 
    req (t v w) (t' v w).

(* TODO: refl, sym, trans lemmas, and Add Parametric Relation 
  Also, do we want to factor as summable_relation (same type 
  as pointwise relation) for better integration? *)

#[global] Instance Tensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} {n m} : Equiv (@Tensor R n m A) := tensoreq.

Section TensorOps.

Context {R : Type}.

Let Tensor := (@Tensor R).

Definition delta_tensor `{Summable A, EqDecision A, SemiRing R rO rI radd rmul req}
  {n : nat} : Tensor n n A :=
  fun v w => if decide (v = w) then rI else rO.


Definition compose_tensor `{Summable A, SemiRing R rO rI radd rmul req}
  {n m o} (t : Tensor n m A) (t' : Tensor m o A) :
  Tensor n o A :=
  fun v w =>
  ∑ u : vec A m, rmul (t v u) (t' u w).


Section TensorOpFacts.

Context `{SR : SemiRing R rO rI radd rmul req}.

Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.

Context `{Summable A, EqDecision A}.

Lemma delta_tensor_eq {n} (v : vec A n) :
  delta_tensor v v = 1.
Proof.
  unfold delta_tensor.
  now apply decide_True.
Qed.

Lemma delta_tensor_eq' {n} (v w : vec A n) : v = w ->
  delta_tensor v w = 1.
Proof.
  intros ->; apply delta_tensor_eq.
Qed.

Lemma delta_tensor_neq {n} (v w : vec A n) : v ≠ w ->
  delta_tensor v w = 0.
Proof.
  unfold delta_tensor.
  now apply decide_False.
Qed.

Lemma delta_tensor_comm {n} (v w : vec A n) :
  delta_tensor v w = delta_tensor w v.
Proof.
  now apply decide_ext.
Qed.


Lemma sum_of_delta_l `{!WFSummable A} {n} {w : vec A n}
  `{Hw : !SummedElement w} (f : vec A n -> R) :
  ∑ v : vec A n, delta_tensor v w * f v == f w.
Proof.
  rewrite (sum_of_unique' _ w), delta_tensor_eq; [ring|].
  intros b _ Hb.
  rewrite delta_tensor_neq; [ring|easy].
Qed.

Lemma sum_of_delta_r `{!WFSummable A} {n} {w : vec A n}
  `{Hw : !SummedElement w} (f : vec A n -> R) :
  ∑ v : vec A n, delta_tensor w v * f v == f w.
Proof.
  setoid_rewrite delta_tensor_comm.
  apply sum_of_delta_l.
Qed.


Lemma compose_delta_l `{!WFSummable A} {n m} (t : Tensor n m A) :
  compose_tensor delta_tensor t ≡ t.
Proof.
  intros v w Hv Hw.
  unfold compose_tensor.
  now rewrite sum_of_delta_r.
Qed.

(* TODO: More *)



End TensorOpFacts.

End TensorOps.