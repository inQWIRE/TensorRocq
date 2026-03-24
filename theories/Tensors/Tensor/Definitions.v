Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Auxillary.Aux_stdpp.
From TensorRocq Require Export Summable.

Definition Tensor {R} (n m : nat) (A : Type) :=
  Vector.t A n -> Vector.t A m -> R.

Definition PackedTensor {R} (A : Type) :=
  {n : nat & {m : nat & Tensor (R:=R) n m A}}.

Definition DimensionlessTensor {R} (A : Type) :=
  forall n m,
    Tensor (R:=R) n m A.

Definition tensoreq `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} {n m} : relation (@Tensor R n m A) :=
  fun t t' => forall v w, SummedElement v -> SummedElement w ->
    req (t v w) (t' v w).

#[global] Instance Tensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} {n m} : Equiv (@Tensor R n m A) := tensoreq.

Definition dimensionlesstensoreq `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} : relation (@DimensionlessTensor R A) :=
  fun t t' => forall n m, t n m ≡@{@Tensor R n m A} t' n m.

#[global] Instance DimensionlessTensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} : Equiv (@DimensionlessTensor R A) := dimensionlesstensoreq.


Class TensorLike (R : Type) `{SR : SemiRing R rO rI radd rmul req} 
  (A : Type) `{SA : Summable A, EQA : EqDecision A} (T : Type) `{Equiv T}
    `{Equivalence T equiv} := {
  interpretTensor (x : T) : DimensionlessTensor (R:=R) A;
  interpretTensorProper :: Proper (equiv ==> equiv) interpretTensor
}.

#[global] Hint Mode TensorLike - - - - - - -   - - -   + - - : typeclass_instances.

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

Class PermutativeTensorLike
  `(TensT : TensorLike R rO rI radd rmul req A T) := {
  interpretTensorPermutative (x : T) n m :
    permutative_tensor (interpretTensor x n m);
}.

Class StronglyPermutativeTensorLike
  `(TensT : TensorLike R rO rI radd rmul req A T) := {
  interpretTensorStronglyPermutative (x : T) :
    strongly_permutative_tensor (interpretTensor x);
}.

Section TensorOps.

  Context {R : Type}.

  Let Tensor := (@Tensor R).

  Definition const_tensor {A} {n m} (r : R) : @Tensor n m A :=
    fun _ _ => r.

  Definition delta_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req}
    {n : nat} : Tensor n n A :=
    fun v w => if decide (v = w) then rI else rO.


  Definition compose_tensor `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req}
    {n m o} (t : Tensor n m A) (t' : Tensor m o A) :
    Tensor n o A :=
    fun v w =>
    ∑ u : vec A m, rmul (t v u) (t' u w).

  Definition stack_tensor `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req}
    {n m n' m'} (t : Tensor n m A) (t' : Tensor n' m' A) :
    Tensor (n + n') (m + m') A :=
    fun v w =>
    rmul (t (vsplitl v) (vsplitl w)) (t' (vsplitr v) (vsplitr w)).


  Definition swapped_stack_tensor `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req}
    {n m n' m'} (t : Tensor n m A) (t' : Tensor n' m' A) :
    Tensor (n' + n) (m + m') A :=
    fun v w =>
    rmul (t (vsplitr v) (vsplitl w)) (t' (vsplitl v) (vsplitr w)).


  Definition join_stack_1_tr_bl `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m o}
    (t : Tensor (n + (S m)) ((S m) + o) A) : Tensor (n + m) (m + o) A :=
    fun v w =>
    ∑ a : A, t (vsplitl v +++ a ::: vsplitr v) (a ::: w).

  Fixpoint join_stack_tr_bl `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m o} :
    forall (t : Tensor (n + m) (m + o) A), Tensor n o A :=
    match m with
    | 0 => fun t v w => t (v +++ [#]) w
    | S m => fun t =>
      join_stack_tr_bl (join_stack_1_tr_bl t)
    end.


  Definition join_stack_1_tl_tr `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m}
    (t : Tensor (S n) (S m) A) : Tensor n m A :=
    fun v w =>
    ∑ a : A, t (a ::: v) (a ::: w).

  Fixpoint join_stack_tl_tr `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m o} :
    forall (t : Tensor (n + m) (n + o) A), Tensor m o A :=
    match n with
    | 0 => fun t => t
    | S m => fun t =>
      join_stack_tl_tr (join_stack_1_tl_tr t)
    end.

  Definition cup_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n} :
    Tensor 0 (n + n) A := fun v w =>
    delta_tensor (vsplitl w) (vsplitr w).

  Definition cap_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n} :
    Tensor (n + n) 0 A := fun v w =>
    delta_tensor (vsplitl v) (vsplitr v).

  Definition swap_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m} :
    Tensor (n + m) (m + n) A := fun v w =>
    delta_tensor v (vsplitr w +++ vsplitl w).

  Definition tensor_11_to_fun {A} (t : Tensor 1 1 A) : A -> A -> R :=
    fun a b => t [# a] [# b].

  Definition stack_n_tensor_1 `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n} (t : Tensor 1 1 A) : Tensor n n A :=
    fun v w =>
    Vector.fold_right rmul (vzip_with (tensor_11_to_fun t) v w) rI.

  Definition tensor_to_dimensionless `{SR : SemiRing R rO rI radd rmul req}
    {A n m} (t : Tensor n m A) : @DimensionlessTensor R A :=
    fun n' m' v' w' =>
    default rO (vec_cast_opt v' n ≫= λ v, vec_cast_opt w' m ≫= λ w, Some (t v w)).

  Definition fn_delta_tensor_l `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
    (f : vec A n -> vec A m) : Tensor n m A := 
    fun v w => delta_tensor (f v) w.

  Definition fn_delta_tensor_r `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
    (f : vec A m -> vec A n) : Tensor n m A := 
    fun v w => delta_tensor v (f w).

  Definition assoc_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} n m o : Tensor (n + m + o) (n + (m + o)) A :=
    fn_delta_tensor_l (fun v => vsplitl (vsplitl v) +++ (vsplitr (vsplitl v) +++ vsplitr v)).

  Definition invassoc_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} n m o : Tensor (n + (m + o)) (n + m + o) A :=
    fn_delta_tensor_l (fun v => (vsplitl v +++ vsplitl (vsplitr v)) +++ vsplitr (vsplitr v)).

  Definition perm_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m} (f : fin n -> fin m) : Tensor n m A :=
    fun v w => 
    delta_tensor v (fun_to_vec $ (w !!!.) ∘ f).

  Definition permute_tensor_l {A n m o} (f : fin n -> fin m) (t : Tensor n o A) : Tensor m o A :=
    fun v w => t (fun_to_vec $ (v !!!.) ∘ f) w.

  Definition permute_tensor_r {A n m o} (f : fin m -> fin o) (t : Tensor n m A) : Tensor n o A :=
    fun v w => t v (fun_to_vec $ (w !!!.) ∘ f).

  Definition tensor_wrap_l_under {A n m o} (t : Tensor n (m + o) A) : Tensor (n + o) m A :=
    fun v w => t (vsplitl v) (w +++ vsplitr v).

  Definition tensor_wrap_r_under {A n m o} (t : Tensor n (m + o) A) : Tensor (n + o) m A :=
    fun v w => t (vsplitl v) (w +++ vsplitr v).

  Definition strong_permute_tensor {A n m n' m'} (f : fin (n + m) -> fin (n' + m'))
    (t : Tensor n m A) : Tensor n' m' A :=
    fun v w => t (vsplitl (fun_to_vec $ (v +++ w !!!.) ∘ f))
      (vsplitr (fun_to_vec $ (v +++ w !!!.) ∘ f)).


  #[global] Arguments const_tensor {_} {_ _} _ _ _ / : assert.
  #[global] Arguments delta_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments compose_tensor {_ _} {_ _ _ _ _ _} {_ _ _} (_ _) _ _ / : assert.
  #[global] Arguments stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
  #[global] Arguments swapped_stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
  #[global] Arguments join_stack_1_tr_bl {_ _} {_ _ _ _ _ _} {_ _ _} (_) _ _ / : assert.
  #[global] Arguments join_stack_tr_bl {_ _} {_ _ _ _ _ _} {_ !_ _} (_) / _ _ : assert.
  #[global] Arguments join_stack_1_tl_tr {_ _} {_ _ _ _ _ _} {_ _} (_) _ _ / : assert.
  #[global] Arguments join_stack_tl_tr {_ _} {_ _ _ _ _ _} {!_ _ _} (_) / _ _ : assert.

  #[global] Arguments cup_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments cap_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments swap_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ / : assert.
  #[global] Arguments stack_n_tensor_1 {_ _} {_ _ _ _ _ _} {_} _ _ _ / : assert.
  #[global] Arguments tensor_to_dimensionless {_ _ _ _ _ _} {_} {_ _} _ _ _ _ _ / : assert.
  #[global] Arguments tensor_11_to_fun {_} _ _ _ / : assert.

  #[global] Arguments fn_delta_tensor_l {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.
  #[global] Arguments fn_delta_tensor_r {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments assoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments invassoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments perm_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments permute_tensor_l {_ _ _ _} _ _ _ _ / : assert.
  #[global] Arguments permute_tensor_r {_ _ _ _} _ _ _ _ / : assert.

  #[global] Arguments tensor_wrap_l_under {_ _ _ _} _ _ _ / : assert.
  #[global] Arguments tensor_wrap_r_under {_ _ _ _} _ _ _ / : assert.

  #[global] Arguments strong_permute_tensor {_ _ _ _ _} _ _ _ _ / : assert.

End TensorOps.