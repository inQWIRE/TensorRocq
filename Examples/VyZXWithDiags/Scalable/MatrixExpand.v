From TensorRocq Require Export Algebra Matrix Tensor.
From TensorRocqEx Require Export MatrixAux.

From TensorRocq Require Import Aux_stdpp.
From stdpp Require Import vector.



Definition matrix_expand_gen `{SemiRing R rO rI radd rmul req}
  {A} (f : A -> R)
  {n m} (M : Matrix R n m) : @Tensor R n m A :=
  fun v w => vec_dot (vmap f v) (mx_vec_prod M (vmap f w)).

(* Lemma  *)