Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Auxillary.Aux_stdpp.
From TensorRocq Require Export Summable.

(* A tensor with dimensions [n] and [m] taking arguments in [A] and
  values in [R] *)
Definition Tensor {R} (n m : nat) (A : Type) :=
  Vector.t A n -> Vector.t A m -> R.

(* A tensor with arguments in [A] and values in [R] parametric over
  its dimensions *)
Definition DimensionlessTensor {R} (A : Type) :=
  forall n m,
    Tensor (R:=R) n m A.

(* The default equivalence relation on tensors with arguments in a
  [Summable] type [A] and values in a [SemiRing], [R]. Two tensors
  are equivalent if they agree (up to the semiring equality [req]
  of [R]) on all arguments whose elements are [SummedElement]s, i.e.
  appear in the list of summed elements of [A].
  This is registered as the [Equiv] ([(≡)]) instance for tensors. *)
Definition tensoreq `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} {n m} : relation (Tensor (R:=R) n m A) :=
  fun t t' => forall v w, SummedElement v -> SummedElement w ->
    req (t v w) (t' v w).

#[global] Instance Tensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} {n m} : Equiv (Tensor (R:=R) n m A) := tensoreq.

(* The default equivalence relation on dimensionless tensors,
  lifting that of tensors by quantifying over all possible dimensions.
  This is registered as the [Equiv] ([(≡)]) instance for dimensionless tensors. *)
Definition dimensionlesstensoreq `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} : relation (DimensionlessTensor (R:=R) A) :=
  fun t t' => forall n m, t n m ≡@{@Tensor R n m A} t' n m.

#[global] Instance DimensionlessTensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} : Equiv (DimensionlessTensor (R:=R) A) := dimensionlesstensoreq.

(* A class registering that elements [T] can be interpreted as
  dimensionless tensors with arguments in [A] and values in [R].
  This interpretation should respect the [Equiv] instance of [T]. *)
Class TensorLike (R : Type) `{SR : SemiRing R rO rI radd rmul req}
  (A : Type) `{SA : Summable A, EQA : EqDecision A} (T : Type) `{Equiv T}
    `{Equivalence T equiv} := {
  interpretTensor (x : T) : DimensionlessTensor (R:=R) A;
  interpretTensorProper :: Proper (equiv ==> equiv) interpretTensor
}.

#[global] Hint Mode TensorLike - - - - - - -   - - -   + - - : typeclass_instances.

Class StrictTensorLike (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type) `{SA : Summable A, EQA : EqDecision A} (T : nat -> nat -> Type)
  `{EqT : forall n m, Equiv (T n m)} `{EquivT : forall n m, @Equivalence (T n m) equiv} := {
  strictInterpretTensor {n m} (x : T n m) : Tensor (R:=R) n m A;
  strictInterpretTensorProper :: forall n m, Proper (equiv ==> equiv) (@strictInterpretTensor n m)
}.

#[global] Hint Mode StrictTensorLike - - - - -   - - -   - - + - - : typeclass_instances.

Section TensorOps.

  Context {R : Type}.

  Let Tensor := (Tensor (R:=R)).

  Definition const_tensor {A} {n m} (r : R) : Tensor n m A :=
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

  Definition delta_spider_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m} : Tensor n m A :=
    fun v w => if decide (Sorted.Sorted eq (v +++ w)) then rI else rO.

  Definition delta_spider_tensor' `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
      (vi : vec positive n) (wi : vec positive m) : Tensor n m A :=
    fun v w =>
      if decide (equal_on_indices (vzip (vi +++ wi) (v +++ w))) then rI else rO.

  Definition copy_tensor {A} `{SR : SemiRing R rO rI radd rmul req} 
    (k : nat) {n m} (f : Tensor n m A) : 
      Tensor (n * k) (m * k) A :=
    fun v w => 
      Rlist_prod (Vector.map2 f (vunjoin' v) (vunjoin' w)).

  Definition delta_spider_tensor_bundled `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} k n m : Tensor (n * k) (m * k) A :=
    copy_tensor k delta_spider_tensor.

  Definition tensor_11_to_fun {A} (t : Tensor 1 1 A) : A -> A -> R :=
    fun a b => t [# a] [# b].

  Definition stack_n_tensor_1 `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n} (t : Tensor 1 1 A) : Tensor n n A :=
    fun v w =>
    Vector.fold_right rmul (vzip_with (tensor_11_to_fun t) v w) rI.

  Fixpoint n_stack_tensor `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req}
    k {n m} (t : Tensor n m A) : Tensor (k * n) (k * m) A :=
    match k with
    | 0 => const_tensor rI
    | S k => stack_tensor t (n_stack_tensor k t)
    end.

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
    delta_tensor v (permute_vec f w).

  Definition permute_tensor_l {A n m o} (f : fin n -> fin m) (t : Tensor n o A) : Tensor m o A :=
    fun v w => t (permute_vec f v) w.

  Definition permute_tensor_r {A n m o} (f : fin m -> fin o) (t : Tensor n m A) : Tensor n o A :=
    fun v w => t v (permute_vec f w).

  Definition permute_tensor {A n m n' m'} 
    (fl : fin n -> fin n') (fr : fin m -> fin m')
    (t : Tensor n m A) : Tensor n' m' A :=
    fun v w => t (permute_vec fl v) (permute_vec fr w).

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

  #[global] Arguments delta_spider_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ / : assert.
  #[global] Arguments delta_spider_tensor' {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ _ / : assert.

  #[global] Arguments copy_tensor {_} {_ _ _ _ _ _} _ {_ _} _ _ _ / : assert.
  #[global] Arguments delta_spider_tensor_bundled {_ _ _} {_ _ _ _ _ _} _ {_ _} _ _ / : assert.

  #[global] Arguments stack_n_tensor_1 {_ _} {_ _ _ _ _ _} {_} _ _ _ / : assert.
  #[global] Arguments n_stack_tensor {_ _} {_ _ _ _ _ _} !_ {_ _} / _ _ _ : assert.
  #[global] Arguments tensor_to_dimensionless {_ _ _ _ _ _} {_} {_ _} _ _ _ _ _ / : assert.
  #[global] Arguments tensor_11_to_fun {_} _ _ _ / : assert.

  #[global] Arguments fn_delta_tensor_l {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.
  #[global] Arguments fn_delta_tensor_r {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments assoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments invassoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments perm_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments permute_tensor_l {_ _ _ _} _ _ _ _ / : assert.
  #[global] Arguments permute_tensor_r {_ _ _ _} _ _ _ _ / : assert.
  #[global] Arguments permute_tensor {_ _ _ _ _} _ _ _ _ _ / : assert.

  #[global] Arguments tensor_wrap_l_under {_ _ _ _} _ _ _ / : assert.
  #[global] Arguments tensor_wrap_r_under {_ _ _ _} _ _ _ / : assert.

  #[global] Arguments strong_permute_tensor {_ _ _ _ _} _ _ _ _ / : assert.

End TensorOps.


Definition MorUnion {A B} (T T' : A -> B -> Type) : A -> B -> Type :=
  λ a b, (T a b + T' a b)%type.


#[export] Instance morunion_equiv {A B}
  (T : A -> B -> Type) `{EqT : forall n m, Equiv (T n m)}
  (T' : A -> B -> Type) `{EqT' : forall n m, Equiv (T' n m)} :
  forall n m, Equiv (MorUnion T T' n m) := _.


#[export] Instance morunion_equivalence {A B}
  (T : A -> B -> Type) `{EqT : forall n m, Equiv (T n m)}
  `{EquivT : forall n m, @Equivalence (T n m) equiv}
  (T' : A -> B -> Type) `{EqT' : forall n m, Equiv (T' n m)}
  `{EquivT' : forall n m, @Equivalence (T' n m) equiv} :
  forall n m, Equivalence (≡@{MorUnion T T' n m}) := λ n m, sum_relation_equiv _ _.

#[local] Instance sum_rect_proper `{RA : relation A, RB : relation B, RC : relation C}
  (f : A -> C) (g : B -> C) {Hf : Proper (RA ==> RC) f} {Hg : Proper (RB ==> RC) g} :
  Proper (sum_relation RA RB ==> RC) (sum_rect (λ _, C) f g).
Proof.
  intros a b Hab.
  induction Hab; cbn; now f_equiv.
Qed.


#[export] Instance strictTensorLike_MorUnion
  (R : Type) `{SR : SemiRing R rO rI radd rmul req}
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (T : nat -> nat -> Type) `{EqT : forall n m, Equiv (T n m)}
  `{EquivT : forall n m, @Equivalence (T n m) equiv} {TensT : StrictTensorLike R A T}
  (T' : nat -> nat -> Type) `{EqT' : forall n m, Equiv (T' n m)}
  `{EquivT' : forall n m, @Equivalence (T' n m) equiv} {TensT' : StrictTensorLike R A T'} :
  StrictTensorLike R A (MorUnion T T')%type := {
  strictInterpretTensor n m s := sum_rect (λ _, _) strictInterpretTensor strictInterpretTensor s;
  strictInterpretTensorProper n m := sum_rect_proper _ _
}.