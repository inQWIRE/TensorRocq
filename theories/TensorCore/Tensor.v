Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Set Warnings "-stdlib-vector".
Require Import Aux_stdpp.
From stdpp Require vector.
Import vector.

(* FIXME: Move *)

Require Export SummableWF.


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

Lemma strongly_permutative_tensor_permutative_tensor
  `{SemiRing R rO rI radd rmul req} {A} (t : @DimensionlessTensor R A) :
  strongly_permutative_tensor t -> forall n m,
  permutative_tensor (t n m).
Proof.
  intros Hperm n m v v' w w' Hv Hw.
  apply Hperm.
  now apply Permutation_app.
Qed.

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

#[global] Instance StronglyPermutativeTensorLike_PermutativeTensorLike
  `{SR : SemiRing R rO rI radd rmul req} `(TensT : TensorLike R A T)
  (SP : StronglyPermutativeTensorLike TensT) : PermutativeTensorLike TensT.
Proof.
  constructor; intros; apply strongly_permutative_tensor_permutative_tensor,
    interpretTensorStronglyPermutative.
Qed.

Class TensorLikeHom (R : Type) `{SR : SemiRing R rO rI radd rmul req} 
  (A : Type) `{SA : Summable A, EQA : EqDecision A} `{Equiv T, Equiv T'} 
  `{Equivalence T equiv, Equivalence T' equiv}
  `{!TensorLike R A T, !TensorLike R A T'}
  (f : T -> T') `{!Proper (equiv ==> equiv) f} := {
  interpretTensor_hom t : interpretTensor (f t) ≡ interpretTensor t
}.


Section tensoreq.

Context `{SR : SemiRing R rO rI radd rmul req} `{SA : Summable A}.

Lemma tensoreq_refl {n m} (t : @Tensor R n m A) : t ≡ t.
Proof. hnf; intros; apply SR. Qed.
Lemma tensoreq_symm {n m} (t t' : @Tensor R n m A) : t ≡ t' -> t' ≡ t.
Proof.
  intros Ht.
  hnf; intros.
  now apply SR.(Req_equiv).(Equivalence_Symmetric), Ht.
Qed.
Lemma tensoreq_trans {n m} (t t' t'' : @Tensor R n m A) : t ≡ t' -> t' ≡ t'' -> t ≡ t''.
Proof.
  intros Ht Ht'.
  hnf; intros.
  now eapply SR.(Req_equiv).(Equivalence_Transitive); [apply Ht|apply Ht'].
Qed.

Lemma dimensionlesstensoreq_refl (t : @DimensionlessTensor R A) : t ≡ t.
Proof. hnf; intros; apply tensoreq_refl. Qed.
Lemma dimensionlesstensoreq_symm (t t' : @DimensionlessTensor R A) : t ≡ t' -> t' ≡ t.
Proof.
  intros Ht.
  hnf; intros.
  now apply tensoreq_symm.
Qed.
Lemma dimensionlesstensoreq_trans (t t' t'' : @DimensionlessTensor R A) : t ≡ t' -> t' ≡ t'' -> t ≡ t''.
Proof.
  intros Ht Ht'.
  hnf; intros.
  now eapply tensoreq_trans; [apply Ht|apply Ht'].
Qed.

End tensoreq.

Add Parametric Relation `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} {n m} : (@Tensor R n m A) tensoreq
  reflexivity proved by tensoreq_refl
  symmetry proved by tensoreq_symm
  transitivity proved by tensoreq_trans
  as tensoreq_setoid.

Add Parametric Relation `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} : (@DimensionlessTensor R A) dimensionlesstensoreq
  reflexivity proved by dimensionlesstensoreq_refl
  symmetry proved by dimensionlesstensoreq_symm
  transitivity proved by dimensionlesstensoreq_trans
  as dimensionlesstensoreq_setoid.



(* TODO: refl, sym, trans lemmas, and Add Parametric Relation
  Also, do we want to factor as summable_relation (same type
  as pointwise relation) for better integration? *)


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







Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m} :
    (@const_tensor A n m) with signature
    req ==> equiv as const_tensor_mor.
Proof.
  intros r r' Hr v w _ _; apply Hr.
Qed.


Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m o} :
    (compose_tensor (SA:=SA) (SR:=SR) (n:=n) (m:=m) (o:=o)) with signature
    equiv ==> equiv ==> equiv as compose_tensor_mor.
Proof.
  intros l l' Hl r r' Hr v w Hv Hw.
  cbn.
  apply sum_of_ext'; intros u Hu%SummedElement_iff.
  apply SR.
  - now apply Hl.
  - now apply Hr.
Qed.

Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m n' m'} :
    (stack_tensor (SA:=SA) (SR:=SR) (n:=n) (m:=m) (n':=n') (m':=m')) with signature
    equiv ==> equiv ==> equiv as stack_tensor_mor.
Proof.
  intros l l' Hl r r' Hr v w Hv Hw.
  cbn.
  apply SR.
  - now apply Hl; try apply _.
  - now apply Hr; try apply _.
Qed.



Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m n' m'} :
    (swapped_stack_tensor (SA:=SA) (SR:=SR) (n:=n) (m:=m) (n':=n') (m':=m')) with signature
    equiv ==> equiv ==> equiv as swapped_stack_tensor_mor.
Proof.
  intros l l' Hl r r' Hr v w Hv Hw.
  cbn.
  apply SR.
  - now apply Hl; try apply _.
  - now apply Hr; try apply _.
Qed.


Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m} :
    (join_stack_1_tl_tr (SA:=SA) (SR:=SR) (n:=n) (m:=m)) with signature
    equiv ==> equiv as join_stack_1_tl_tr_mor.
Proof.
  intros t t' Ht v w Hv Hw.
  cbn.
  apply sum_of_ext'; intros a Ha%SummedElement_iff.
  apply Ht; apply _.
Qed.

Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m o} :
    (join_stack_tl_tr (SA:=SA) (SR:=SR) (n:=n) (m:=m) (o:=o)) with signature
    equiv ==> equiv as join_stack_tl_tr_mor.
Proof.
  intros t t' Ht.
  induction n; [done|].
  cbn.
  apply IHn.
  now f_equiv.
Qed.


Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m o} :
    (join_stack_1_tr_bl (SA:=SA) (SR:=SR) (n:=n) (m:=m) (o:=o)) with signature
    equiv ==> equiv as join_stack_1_tr_bl_mor.
Proof.
  intros t t' Ht v w Hv Hw.
  cbn.
  apply sum_of_ext'; intros a Ha%SummedElement_iff.
  apply Ht; apply _.
Qed.

Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m o} :
    (join_stack_tr_bl (SA:=SA) (SR:=SR) (n:=n) (m:=m) (o:=o)) with signature
    equiv ==> equiv as join_stack_tr_bl_mor.
Proof.
  intros t t' Ht.
  induction m.
  - cbn.
    intros v w Hv Hw; now apply Ht; apply _.
  - cbn.
    apply IHm.
    now f_equiv.
Qed.

Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n} :
  (stack_n_tensor_1 (SA:=SA) (SR:=SR) (n:=n)) with signature
  (≡) ==> (≡) as stack_n_tensor_1_mor.
Proof.
  intros f g Hfg v w Hv Hw.
  cbn.
  rewrite SummedElement_vec_iff_Forall, vec_to_list_to_list, 
    <- Vector.to_list_Forall in Hv, Hw.
  revert Hv Hw.
  vec_double_ind v w; [intros; apply SR|].
  intros n v w IHvw hv hw [Hvh Hv]%Vector.Forall_cons_iff
    [Hwh Hw]%Vector.Forall_cons_iff.
  cbn.
  apply SR.
  - cbn.
    apply Hfg; apply _.
  - now apply IHvw.
Qed.

Add Parametric Morphism `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m} :
  (tensor_to_dimensionless (SR:=SR) (A:=A) (n:=n) (m:=m)) with signature
  (≡) ==> (≡) as tensor_to_dimensionless_mor.
Proof.
  intros f g Hfg n' m' v w Hv Hw.
  cbn.
  rewrite 2 vec_cast_opt_spec.
  do 2 (case_guard; [subst; cbn|apply SR]).
  apply Hfg; now rewrite cast_id.
Qed.



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
  rewrite <- sum_of_delta_l.
  apply sum_of_ext; now intros; rewrite delta_tensor_comm.
Qed.


Lemma sum_of_delta_l_1 `{!WFSummable A} {w : vec A 1}
  `{Hw : !SummedElement w} (f : A -> R) :
  ∑ a : A, delta_tensor [#a] w * f a == f (Vector.hd w).
Proof.
  erewrite sum_of_ext. 2:{
    intros a.
    change (f a) with (f (Vector.hd [# a])).
    refine (reflexivity _).
  }
  rewrite <- (sum_of_vec_1 (λ va, delta_tensor va w * f (Vector.hd va))).
  now rewrite sum_of_delta_l.
Qed.

Lemma sum_of_delta_r_1 `{!WFSummable A} {w : vec A 1}
  `{Hw : !SummedElement w} (f : A -> R) :
  ∑ a : A, delta_tensor w [#a] * f a == f (Vector.hd w).
Proof.
  setoid_rewrite delta_tensor_comm.
  apply sum_of_delta_l_1.
Qed.


Lemma compose_delta_l `{!WFSummable A} {n m} (t : Tensor n m A) :
  compose_tensor delta_tensor t ≡ t.
Proof.
  intros v w Hv Hw.
  unfold compose_tensor.
  now rewrite sum_of_delta_r.
Qed.

Lemma compose_delta_r `{!WFSummable A} {n m} (t : Tensor n m A) :
  compose_tensor t delta_tensor ≡ t.
Proof.
  intros v w Hv Hw.
  unfold compose_tensor.
  setoid_rewrite rmul_comm.
  now rewrite sum_of_delta_l.
Qed.

Lemma stack_delta_tensors {n m} :
  stack_tensor (delta_tensor (n:=n)) (delta_tensor (n:=m)) ≡
  delta_tensor.
Proof.
  intros v w Hv Hw.
  unfold stack_tensor.
  unfold delta_tensor.
  rewrite (decide_ext _ _ _ _ (vsplit_eq v w)).
  case_decide; case_decide; case_decide; tauto + ring.
Qed.

Lemma compose_succ_mid {n m o} (t : Tensor n (S m) A) (t' : Tensor (S m) o A) :
  compose_tensor t t' ≡
  fun v w => ∑ a : A, compose_tensor (fun v w => t v (a:::w))
    (fun v w => t' (a:::v) w) v w.
Proof.
  intros v w Hv Hw.
  cbn.
  now rewrite sum_of_vec_succ.
Qed.

Lemma join_stack_tr_bl_alt {n m o} (t : Tensor (n + m) (m + o) A) :
  join_stack_tr_bl t ≡ fun v w => ∑ u : vec A m, t (v+++u) (u+++w).
Proof.
  induction m.
  - intros v w Hv Hw.
    cbn.
    now rewrite sum_of_vec_0.
  - cbn.
    rewrite IHm.
    intros v w Hv Hw.
    rewrite sum_of_vec_succ, sum_of_comm.
    apply sum_of_ext; intros u.
    cbn.
    apply sum_of_ext; intros a.
    now rewrite vsplitl_app, vsplitr_app.
Qed.

Lemma compose_to_stack {n m o} (t : Tensor n m A) (t' : Tensor m o A) :
  compose_tensor t t' ≡
  join_stack_tr_bl (stack_tensor t t').
Proof.
  rewrite join_stack_tr_bl_alt.
  intros v w Hv Hw.
  cbn.
  apply sum_of_ext; intros u.
  now rewrite !vsplitl_app, !vsplitr_app.
Qed.


Lemma join_stack_tl_tr_alt {n m o} (t : Tensor (n + m) (n + o) A) :
  join_stack_tl_tr t ≡ fun v w => ∑ u : vec A n, t (u+++v) (u+++w).
Proof.
  induction n.
  - intros v w Hv Hw.
    cbn.
    now rewrite sum_of_vec_0.
  - cbn.
    rewrite IHn.
    intros v w Hv Hw.
    cbn.
    rewrite sum_of_vec_succ, sum_of_comm.
    reflexivity.
Qed.


Lemma compose_to_swapped_stack {n m o} (t : Tensor n m A) (t' : Tensor m o A) :
  compose_tensor t t' ≡
  join_stack_tl_tr (swapped_stack_tensor t t').
Proof.
  rewrite join_stack_tl_tr_alt.
  intros v w Hv Hw.
  cbn.
  apply sum_of_ext; intros u.
  now rewrite !vsplitl_app, !vsplitr_app.
Qed.

Lemma stack_n_tensor_1_succ {n} (t : Tensor 1 1 A) :
  stack_n_tensor_1 (n:=S n) t ≡
  stack_tensor t (stack_n_tensor_1 t).
Proof.
  intros v w Hv Hw.
  cbn.
  induction v as [vh v] using vec_S_inv.
  induction w as [wh w] using vec_S_inv.
  cbn.
  done.
Qed.

Lemma tensor_to_dimensionless_refl {n m} (t : Tensor n m A) :
  tensor_to_dimensionless t n m ≡ t.
Proof.
  intros v w Hv Hw.
  cbn.
  now rewrite 2 vec_cast_opt_refl.
Qed.

Lemma tensor_to_dimensionless_ne_l {n m} (t : Tensor n m A) n' m' :
  n <> n' ->
  tensor_to_dimensionless t n' m' ≡ const_tensor 0.
Proof.
  intros Hn v w Hv Hw.
  cbn.
  rewrite (vec_cast_opt_ne v) by done.
  done.
Qed.

Lemma tensor_to_dimensionless_ne_r {n m} (t : Tensor n m A) n' m' :
  m <> m' ->
  tensor_to_dimensionless t n' m' ≡ const_tensor 0.
Proof.
  intros Hn v w Hv Hw.
  cbn.
  rewrite (vec_cast_opt_ne w) by done.
  now destruct (vec_cast_opt _ _).
Qed.



(* TODO: More *)



End TensorOpFacts.

End TensorOps.