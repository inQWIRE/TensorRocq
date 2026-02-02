Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Btauto.
Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

(* FIXME: Move *)
Definition vsplitl {A n m} (v : vec A (n + m)) : vec A n :=
  (Vector.splitat n v).1.
Definition vsplitr {A n m} (v : vec A (n + m)) : vec A m :=
  (Vector.splitat n v).2.
Definition app_vsplit {A n m} (v : vec A (n + m)) :
  vsplitl v +++ vsplitr v = v.
Proof.
  apply symmetry, Vector.append_splitat, surjective_pairing.
Qed.
Lemma vsplit_eq {A n m} (v w : vec A (n + m)) : 
  v = w <-> vsplitl v = vsplitl w /\ vsplitr v = vsplitr w.
Proof.
  split; [now intros ->|].
  intros [Hl Hr].
  rewrite <- (app_vsplit v), <- (app_vsplit w).
  congruence.
Qed.
Lemma vsplitl_app {A n m} (v : vec A n) (w : vec A m) : 
  vsplitl (v +++ w) = v.
Proof.
  unfold vsplitl.
  now rewrite Vector.splitat_append.
Qed.
Lemma vsplitr_app {A n m} (v : vec A n) (w : vec A m) : 
  vsplitr (v +++ w) = w.
Proof.
  unfold vsplitr.
  now rewrite Vector.splitat_append.
Qed.

Require Export SummableWF.

Lemma SummedElement_vec_iff `{Summable A} {n} (v : vec A n) :
  SummedElement v <-> (forall a, a ∈@{list _} v -> SummedElement a).
Proof.
  split; [|apply SummedElement_vec].
  setoid_rewrite SummedElement_iff.
  setoid_rewrite elem_of_list_In.
  intros Hv%vec_elements_in%Vector.to_list_Forall.
  apply List.Forall_forall.
  revert Hv.
  now rewrite vec_to_list_to_list.
Qed.

Lemma SummedElement_vec_iff_Forall `{Summable A} {n} (v : vec A n) :
  SummedElement v <-> Forall SummedElement v.
Proof.
  now rewrite SummedElement_vec_iff, <- Forall_forall.
Qed.
#[export] Instance SummedElement_vsplitl `{Summable A} {n m} (v : vec A (n + m)) :
  SummedElement v -> SummedElement (vsplitl v).
Proof.
  rewrite 2 SummedElement_vec_iff_Forall.
  rewrite <- (app_vsplit v), vec_to_list_app, Forall_app at 1.
  easy.
Qed.
#[export] Instance SummedElement_vsplitr `{Summable A} {n m} (v : vec A (n + m)) :
  SummedElement v -> SummedElement (vsplitr v).
Proof.
  rewrite 2 SummedElement_vec_iff_Forall.
  rewrite <- (app_vsplit v), vec_to_list_app, Forall_app at 1.
  easy.
Qed.

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
  `{SR : SemiRing R rO rI radd rmul req} `(TensT : TensorLike R A T)
  (SP : StronglyPermutativeTensorLike TensT) : PermutativeTensorLike TensT.
Proof.
  constructor; intros; apply strongly_permutative_tensor_permutative_tensor,
    interpretTensorStronglyPermutative.
Qed.

Definition tensoreq `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} {n m} : relation (@Tensor R n m A) :=
  fun t t' => forall v w, SummedElement v -> SummedElement w ->
    req (t v w) (t' v w).

#[global] Instance Tensor_equiv `{SemiRing R rO rI radd rmul req}
  `{Summable A} {n m} : Equiv (@Tensor R n m A) := tensoreq.

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

End tensoreq.

Add Parametric Relation `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A} {n m} : (@Tensor R n m A) tensoreq 
  reflexivity proved by tensoreq_refl
  symmetry proved by tensoreq_symm
  transitivity proved by tensoreq_trans
  as tensoreq_setoid.

(* TODO: refl, sym, trans lemmas, and Add Parametric Relation
  Also, do we want to factor as summable_relation (same type
  as pointwise relation) for better integration? *)


Section TensorOps.

Context {R : Type}.

Let Tensor := (@Tensor R).

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


Definition join_stack_1_tl_bl `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m} 
  (t : Tensor (S n) (S m) A) : Tensor n m A :=
  fun v w => 
  ∑ a : A, t (a ::: v) (a ::: w).

Fixpoint join_stack_tl_bl `{SA : Summable A,
  SR : SemiRing R rO rI radd rmul req} {n m o} : 
  forall (t : Tensor (n + m) (n + o) A), Tensor m o A :=
  match n with
  | 0 => fun t => t
  | S m => fun t => 
    join_stack_tl_bl (join_stack_1_tl_bl t)
  end.

#[global] Arguments delta_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
#[global] Arguments compose_tensor {_ _} {_ _ _ _ _ _} {_ _ _} (_ _) _ _ / : assert.
#[global] Arguments stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
#[global] Arguments swapped_stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
#[global] Arguments join_stack_1_tr_bl {_ _} {_ _ _ _ _ _} {_ _ _} (_) _ _ / : assert.
#[global] Arguments join_stack_tr_bl {_ _} {_ _ _ _ _ _} {_ !_ _} (_) / _ _ : assert.
#[global] Arguments join_stack_1_tl_bl {_ _} {_ _ _ _ _ _} {_ _} (_) _ _ / : assert.
#[global] Arguments join_stack_tl_bl {_ _} {_ _ _ _ _ _} {!_ _ _} (_) / _ _ : assert.



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


Lemma join_stack_tl_bl_alt {n m o} (t : Tensor (n + m) (n + o) A) :
  join_stack_tl_bl t ≡ fun v w => ∑ u : vec A n, t (u+++v) (u+++w).
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
  join_stack_tl_bl (swapped_stack_tensor t t').
Proof.
  rewrite join_stack_tl_bl_alt.
  intros v w Hv Hw.
  cbn.
  apply sum_of_ext; intros u.
  now rewrite !vsplitl_app, !vsplitr_app.
Qed.

(* TODO: More *)



End TensorOpFacts.

End TensorOps.