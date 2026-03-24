Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Aux Aux_stdpp Tensor.Definitions.
From TensorRocq Require Export Summable.

(* NB : We require a semiring (even though we use only equality)
  so typeclass inference is better-behaved *)


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


Section TensorOpsFacts.


  Context {R : Type}.

  Let Tensor := (@Tensor R).

  Lemma SummedElement_fun_to_vec_iff `{Summable A} {n} 
    (f : fin n -> A) : SummedElement (fun_to_vec f) <->  (forall i, SummedElement (f i)).
  Proof.
    rewrite SummedElement_vec_iff_Forall.
    rewrite Forall_vlookup.
    apply forall_iff.
    intros i.
    now rewrite lookup_fun_to_vec.
  Qed.

  #[export] Instance SummedElement_fun_to_vec `{Summable A} {n} 
    (f : fin n -> A) : (forall i, SummedElement (f i)) -> SummedElement (fun_to_vec f).
  Proof.
    now rewrite SummedElement_fun_to_vec_iff.
  Qed.

  #[export] Instance SummedElement_vlookup `{Summable A} {n} 
    (v : vec A n) i : SummedElement v -> SummedElement (v !!! i).
  Proof.
    rewrite SummedElement_vec_iff_Forall, Forall_vlookup.
    auto.
  Qed.

  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m n' m'} f :
      (@strong_permute_tensor R A n m n' m' f) with signature
      equiv ==> equiv as strong_permute_tensor_mor.
  Proof.
    intros r r' Hr v w Hv Hm; apply Hr; apply _.
  Qed.

  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m} :
      (@const_tensor R A n m) with signature
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
    delta_tensor (R:=R) v w = delta_tensor w v.
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
    stack_tensor (delta_tensor (R:=R) (n:=n)) (delta_tensor (n:=m)) ≡
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

End TensorOpsFacts.
