Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Aux Aux_stdpp Tensor.Definitions.
From TensorRocq Require Export Summable Homomorphism.

(* NB : We require a semiring (even though we use only equality)
  so typeclass inference is better-behaved *)


(* A typeclass recording that a functions preserves the interpretation of
  tensors between two [TensorLike] types [T] and [T']. *)
(* Class TensorLikeHom (R : Type) `{SR : SemiRing R rO rI radd rmul req}
  (A : Type) `{SA : Summable A, EQA : EqDecision A} `{Equiv T, Equiv T'}
  `{Equivalence T equiv, Equivalence T' equiv}
  `{!TensorLike R A T, !TensorLike R A T'}
  (f : T -> T') `{!Proper (equiv ==> equiv) f} := {
  interpretTensor_hom t : interpretTensor (f t) ≡ interpretTensor t
}. *)


Class TensorLikeHom
  `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
  (f : R -> R') (A : Type)
  `{SA : Summable A, EQA : EqDecision A}
  {T T'} `{EqT : Equiv T, EqT' : Equiv T'}
  `{EquivT : Equivalence T equiv, EquivT' : Equivalence T' equiv}
  (fT : T -> T')
  {TensT : TensorLike R A T} {TensT' : TensorLike R' A T'} := {
  TLH_SRH :: SemiRingHomomorphism f;
  TLH_proper : Proper (equiv ==> equiv) fT;
  interpretTensor_hom t n m :
    tensor_apply_hom f (interpretTensor t n m) ≡
    interpretTensor (fT t) n m
}.


(* Class FreeStrictTensorLike
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (T : nat -> nat -> Type) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A T} := {
  strictInterpretTensor_free
    `{SR : SemiRing R rO rI radd rmul req}
    `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
    {n m} (t : T n m) :
    tensor_apply_hom f (strictInterpretTensor t) ≡
    strictInterpretTensor t
}. *)

Class StrictTensorLikeHom
  `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (T : nat -> nat -> Type) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  {STL : StrictTensorLike R A T}
  {STL' : StrictTensorLike R' A T} := {
  strictInterpretTensor_hom {n m} (t : T n m) :
    tensor_apply_hom f (strictInterpretTensor t) ≡
    strictInterpretTensor t
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


Lemma tensor_equiv_alt
  {n m} (t t' : @Tensor R n m A) :
  t ≡ t' <-> Forall (λ v, Forall (λ w, req (t v w) (t' v w)) sum_elements) sum_elements.
Proof.
  rewrite Forall_forall.
  setoid_rewrite Forall_forall.
  unfold equiv, Tensor_equiv, tensoreq.
  setoid_rewrite SummedElement_iff.
  firstorder.
Qed.

#[export] Instance tensor_equiv_dec (HRdec : RelDecision req)
  {n m} : RelDecision (≡@{@Tensor R n m A}).
refine (fun t t' => cast_if (decide (Forall (λ v, Forall (λ w, req (t v w) (t' v w)) sum_elements) sum_elements)));
abstract (now rewrite tensor_equiv_alt).
Defined.

Lemma tensor_equiv_to_bool
  (reqb : R -> R -> bool) (Hreqb : forall r s, reqb r s = true <-> req r s)
  {n m} (t t' : @Tensor R n m A) :
  t ≡ t' <-> forallb (λ v, forallb (λ w, reqb (t v w) (t' v w)) sum_elements) sum_elements = true.
Proof.
  rewrite <- Is_true_true.
  rewrite forallb_True.
  rewrite tensor_equiv_alt.
  f_equiv.
  intros v.
  rewrite forallb_True.
  f_equiv.
  intros w.
  now rewrite Is_true_true, Hreqb.
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

  (* FIXME: Move *)
  Lemma SummedElement_vlookup_iff `{Summable A} {n} (v : vec A n) :
    SummedElement v <-> forall i : fin n, SummedElement (v !!! i).
  Proof.
    split; [apply _|].
    intros Hi.
    rewrite SummedElement_vec_iff.
    intros _ [i <-]%elem_of_vlookup.
    auto.
  Qed.

  (* FIXME: Move *)
  #[export] Instance vjoin_SummedElement `{Summable A} {n m} (v : vec (vec A n) m) :
    SummedElement v -> SummedElement (vjoin v).
  Proof.
    intros Hv.
    rewrite SummedElement_vlookup_iff.
    intros i.
    rewrite lookup_vjoin.
    apply _.
  Qed.

  #[export] Instance vjoin'_SummedElement `{Summable A} {n m} (v : vec (vec A n) m) :
    SummedElement v -> SummedElement (vjoin' v).
  Proof.
    intros Hv.
    rewrite SummedElement_vlookup_iff.
    intros i.
    rewrite lookup_vjoin'.
    apply _.
  Qed.

  #[export] Instance vunjoin_SummedElement `{Summable A} {n m} (v : vec A (n * m)) :
    SummedElement v -> SummedElement (vunjoin v).
  Proof.
    intros Hv.
    rewrite SummedElement_vlookup_iff.
    intros i.
    rewrite SummedElement_vlookup_iff.
    intros j.
    rewrite lookup_vunjoin.
    apply _.
  Qed.

  #[export] Instance vunjoin'_SummedElement `{Summable A} {n m} (v : vec A (n * m)) :
    SummedElement v -> SummedElement (vunjoin' v).
  Proof.
    intros Hv.
    rewrite SummedElement_vlookup_iff.
    intros i.
    rewrite SummedElement_vlookup_iff.
    intros j.
    rewrite lookup_vunjoin'.
    apply _.
  Qed.

  #[export] Instance permute_vec_SummedElement `{Summable A} {n m}
    (f : fin n -> fin m) (v : vec A m) :
    SummedElement v -> SummedElement (permute_vec f v).
  Proof.
    intros Hv.
    rewrite SummedElement_vlookup_iff.
    intros i.
    rewrite lookup_permute_vec.
    apply _.
  Qed.

  (* FIXME: Move *)
  #[export] Instance vhd_SummedElement `{Summable A} {n} (v : vec A (S n)) :
    SummedElement v -> SummedElement (vhd v).
  Proof.
    rewrite SummedElement_vlookup_iff.
    intros Hv.
    specialize (Hv 0%fin).
    inv_all_vec_fin; done.
  Qed.



  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} k {n m} :
    (copy_tensor (A:=A) (SR:=SR) k (n:=n) (m:=m)) with signature
    (≡) ==> (≡) as copy_tensor_mor.
  Proof.
    intros f g Hfg.
    intros v w Hv Hw.
    cbn.
    apply Rlist_prod_ext.
    apply Forall2_vlookup.
    intros i.
    rewrite 2 vlookup_zip_with.
    apply Hfg; apply _.
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
    SR : SemiRing R rO rI radd rmul req} k {n m} :
    (n_stack_tensor (A:=A) (SR:=SR) k (n:=n) (m:=m)) with signature
    (≡) ==> (≡) as n_stack_tensor_mor.
  Proof.
    intros f g Hfg.
    induction k; [done|].
    cbn.
    now f_equiv.
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

  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m o} :
    (permute_tensor_l (R:=R) (A:=A) (n:=n) (m:=m) (o := o)) with signature
    pointwise_relation _ eq ==> (≡) ==> (≡) as permute_tensor_l_mor.
  Proof.
    intros f g Hfg t t' Ht.
    intros v w Hv Hw.
    cbn.
    rewrite Hfg.
    apply Ht; apply _.
  Qed.

  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m o} :
    (permute_tensor_r (R:=R) (A:=A) (n:=n) (m:=m) (o := o)) with signature
    pointwise_relation _ eq ==> (≡) ==> (≡) as permute_tensor_r_mor.
  Proof.
    intros f g Hfg t t' Ht.
    intros v w Hv Hw.
    cbn.
    rewrite Hfg.
    apply Ht; apply _.
  Qed.

  Add Parametric Morphism `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n m n' m'} :
    (permute_tensor (R:=R) (A:=A) (n:=n) (m:=m) (n':=n') (m':=m')) with signature
    equiv ==> equiv ==>
      (≡) ==> (≡) as permute_tensor_mor.
  Proof.
    intros fl fl' Hfl fr fr' Hfr t t' Ht.
    intros v w Hv Hw.
    cbn.
    rewrite Hfl, Hfr.
    apply Ht; apply _.
  Qed.


  #[export] Instance perm_tensor_proper
    `{SA : Summable A, EqA : EqDecision A, SR : SemiRing R rO rI radd rmul req}
    {n m} : Proper (equiv ==> equiv) (perm_tensor (A:=A) (R:=R) (n:=n) (m:=m)).
  Proof.
    intros f f' Hf v w _ _.
    cbn.
    erewrite permute_vec_ext; [apply SR| |done].
    apply Hf.
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

  Lemma delta_spider_tensor_alt {n m} `{!WFSummable A} : (n + m <> 0)%nat ->
    delta_spider_tensor (n:=n) (m:=m) ≡ (fun v w =>
    if decide (Forall (λ a, Some a = head (v +++ w)) (v +++ w)) then rI else rO).
  Proof.
    intros Hnm.
    intros v w Hv Hw.
    unfold delta_spider_tensor.
    assert (Hvw : SummedElement (v +++ w)) by apply _.
    revert Hvw.
    generalize (v +++ w).
    revert Hnm.
    generalize (n + m)%nat as nm.
    intros [|nm]; [done|intros _].
    intros t Ht.
    rewrite (sum_of_unique' _ (vhd t)).
    - apply eq_reflexivity.
      apply decide_ext.
      inv_all_vec_fin.
      cbn.
      apply Forall_iff.
      naive_solver.
    - intros b Hb Hne.
      rewrite decide_False; [done|].
      inv_all_vec_fin.
      cbn.
      rewrite Forall_cons.
      naive_solver.
  Qed.

  Lemma delta_spider_tensor_alt_posdim {n m} `{!WFSummable A} : (n + m <> O)%nat ->
    delta_spider_tensor (n:=n) (m:=m) ≡ (fun v w =>
    if decide (Sorted.Sorted eq (v +++ w)) then rI else rO).
  Proof.
    intros Hnm.
    rewrite delta_spider_tensor_alt by done.
    intros v w _ _.
    apply eq_reflexivity.
    apply decide_ext.
    now rewrite Sorted_eq_iff.
  Qed.

  Lemma delta_spider_tensor'_alt {n m} vi wi :
    delta_spider_tensor' (SR:=SR) (n:=n) (m:=m) vi wi ≡
    (fun v w =>
    if decide (forall (i j : fin (n + m)),
      (vi +++ wi) !!! i = (vi +++ wi) !!! j ->
      (v +++ w) !!! i = (v +++ w) !!! j) then rI else rO).
  Proof.
    intros v w _ _.
    unfold delta_spider_tensor'.
    apply eq_reflexivity, decide_ext.
    unfold equal_on_indices.
    split.
    - intros Hall i j.
      apply (Hall (_ !!! _, _ !!! _) (_ !!! _, _ !!! _)); apply elem_of_list_In.
      + apply elem_of_list_lookup.
        exists i.
        rewrite lookup_vec_to_list_fin.
        rewrite vlookup_zip_with.
        done.
      + apply elem_of_list_lookup.
        exists j.
        rewrite lookup_vec_to_list_fin.
        rewrite vlookup_zip_with.
        done.
    - intros Hall ia jb [i <-]%elem_of_list_In%elem_of_vlookup [j <-]%elem_of_list_In%elem_of_vlookup.
      rewrite 2 vlookup_zip_with.
      cbn.
      apply Hall.
  Qed.


  Lemma n_stack_tensor_alt k {n m} (f : Tensor n m A) :
    n_stack_tensor k f ≡ fun v w => Rlist_prod (vzip_with f (vunjoin v) (vunjoin w)).
  Proof.
    induction k; [done|].
    cbn.
    rewrite IHk.
    done.
  Qed.

  Lemma copy_tensor_alt k {n m} (f : Tensor n m A) :
    copy_tensor k f ≡ permute_tensor fin_prod_comm fin_prod_comm (n_stack_tensor k f).
  Proof.
    rewrite n_stack_tensor_alt.
    intros v w Hv Hw.
    cbn.
    rewrite <- 2 vunjoin'_to_vunjoin.
    done.
  Qed.

  Lemma permute_tensor_compose {n n' n'' m m' m''}
    (fn : fin n -> fin n') (fn' : fin n' -> fin n'')
    (fm : fin m -> fin m') (fm' : fin m' -> fin m'')
    (g : Tensor n m A) :
    permute_tensor fn' fm' (permute_tensor fn fm g) ≡
    permute_tensor (fn' ∘ fn) (fm' ∘ fm) g.
  Proof.
    intros v w Hv Hw.
    cbn.
    rewrite 2 permute_vec_compose.
    done.
  Qed.


  Lemma compose_perm_tensor_l `{WFA : !WFSummable A}
    {n m o} (Hnm : n = m)
    (f : fin n -> fin m) {Hf : Inj eq eq f}
    (g : Tensor m o A) : compose_tensor (perm_tensor f) g ≡
    permute_tensor (fin_perm_inv_cast Hnm f) id g.
  Proof.
    subst m.
    intros v w Hv Hw.
    cbn.
    rewrite fin_perm_inv_cast_id.
    rewrite (sum_of_unique' _ (permute_vec (fin_perm_inv f) v)).
    - rewrite (permute_vec_cancel _ _ _).
      rewrite decide_True by done.
      rewrite permute_vec_id.
      ring.
    - intros b Hb.
      intros Hbneq.
      case_decide as Hvb; [|ring].
      subst v.
      rewrite (permute_vec_cancel _ _ _) in Hbneq.
      done.
  Qed.

  Lemma compose_perm_tensor_r `{WFA : !WFSummable A}
    {n m o} (g : Tensor n m A)
    (f : fin m -> fin o) {Hf : Inj eq eq f} (Hmo : m = o) : compose_tensor g (perm_tensor f) ≡
    permute_tensor id f g.
  Proof.
    intros v w Hv Hw.
    cbn.
    rewrite (sum_of_unique' _ (permute_vec f w)).
    - rewrite decide_True by done.
      rewrite permute_vec_id; ring.
    - intros; rewrite decide_False by done.
      ring.
  Qed.

  Lemma perm_tensor_ext
    {n m} (f g : fin n -> fin m) (Hfg : forall i, f i = g i) :
    perm_tensor f ≡@{Tensor n m A} perm_tensor g.
  Proof.
    now apply perm_tensor_proper.
  Qed.

  Lemma perm_tensor_id'
    {n} (f : fin n -> fin n) (Hf : forall i, f i = i) :
    perm_tensor f ≡@{@Tensor n n A} delta_tensor.
  Proof.
    pose proof SR as [_ _ []].
    intros v w _ _.
    cbn.
    rewrite permute_vec_id' by done.
    done.
  Qed.

  Lemma perm_tensor_compose {WFA : WFSummable A}
    {n m o} (f : fin n -> fin m) (g : fin m -> fin o) :
    compose_tensor (perm_tensor f) (perm_tensor g) ≡@{@Tensor n o A} perm_tensor (g ∘ f).
  Proof.
    pose proof SR as [_ _ []].
    intros v w Hv Hw.
    cbn.
    etransitivity;
    [refine (
      sum_of_unique' (SR:=SR) _ (permute_vec g w)
      _)|].
    - intros b Hb Hne.
      rewrite (decide_False (P:=b = _)) by done.
      apply rmul_0_r.
    - rewrite (decide_True (P:=permute_vec g w = _)) by done.
      rewrite rmul_1_r.
      apply Aux.eq_reflexivity.
      apply decide_ext.
      f_equiv.
      rewrite permute_vec_compose.
      done.
  Qed.


  Lemma perm_tensor_stack {WFA : WFSummable A}
    {n m n' m'} (f : fin n -> fin m) (g : fin n' -> fin m') :
    stack_tensor (perm_tensor f) (perm_tensor g) ≡@{@Tensor _ _ A}
    perm_tensor (fin_perm_stack f g).
  Proof.
    pose proof SR as [_ _ []].
    intros v w Hv Hw.
    cbn.
    induction v as [vl vr] using vec_add_inv.
    induction w as [wl wr] using vec_add_inv.
    rewrite 2 vsplitl_app, 2 vsplitr_app.
    transitivity (if decide
          (vl = permute_vec f wl /\
            vr = permute_vec g wr)
          then rI else rO); [(repeat case_decide); first [easy | exfalso; tauto | apply SR]|].
    apply Aux.eq_reflexivity, decide_ext.
    rewrite vapp_eq_iff.
    do 2 f_equiv.
    - apply vec_eq; intros i.
      rewrite lookup_vsplitl.
      rewrite 2 lookup_permute_vec.
      rewrite fin_perm_stack_L.
      rewrite lookup_vapp_L.
      done.
    - apply vec_eq; intros i.
      rewrite lookup_vsplitr.
      rewrite 2 lookup_permute_vec.
      rewrite fin_perm_stack_R.
      rewrite lookup_vapp_R.
      done.
  Qed.



End TensorOpsFacts.


Section TensorHom.

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


Context `{SR' : SemiRing R' rO' rI' radd' rmul' req'}.

Notation "0'" := rO'.
Notation "1'" := rI'.
Notation "x '=='' y" := (req' x y) (at level 70).
Infix "+'" := radd' (at level 50, left associativity).
Infix "*'" := rmul' (at level 40, left associativity).

Add Ring R' : SR'.(RSRth)
  (setoid SR'.(Req_equiv) SR'.(Req_ext)).

Let Req_equivalence' : Equivalence req' := Req_equiv.
Local Existing Instance Req_equivalence'.

Let Radd_proper' := Req_ext.(SRadd_ext) : Proper (req' ==> req' ==> req') radd'.
Local Existing Instance Radd_proper'.

Let Rmul_proper' := Req_ext.(SRmul_ext) : Proper (req' ==> req' ==> req') rmul'.
Local Existing Instance Rmul_proper'.



#[export] Instance tensor_apply_hom_mor (f : R -> R')
  {Hf : SemiRingHomomorphism f} {n m} `{SA : Summable A} :
  Proper (equiv ==> equiv) (tensor_apply_hom f (n:=n) (m:=m) (A:=A)).
Proof.
  intros t t' Ht v w Hv Hw.
  cbn.
  apply Hf.
  now apply Ht.
Qed.

Lemma tensor_apply_hom_delta (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {n} :
  tensor_apply_hom f (delta_tensor (n:=n)) ≡ delta_tensor (A:=A) (n:=n).
Proof.
  intros v w Hv Hw.
  cbn.
  case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_swap (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {n m} :
  tensor_apply_hom f (swap_tensor (n:=n) (m:=m)) ≡ swap_tensor (A:=A).
Proof.
  intros v w Hv Hw.
  cbn.
  case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_cup (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {n} :
  tensor_apply_hom f (cup_tensor (n:=n)) ≡ cup_tensor (A:=A) (n:=n).
Proof.
  intros v w Hv Hw.
  cbn.
  case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_cap (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {n} :
  tensor_apply_hom f (cap_tensor (n:=n)) ≡ cap_tensor (A:=A) (n:=n).
Proof.
  intros v w Hv Hw.
  cbn.
  case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_delta_spider (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {n m} :
  tensor_apply_hom f (delta_spider_tensor (n:=n) (m:=m))
    ≡ delta_spider_tensor (A:=A).
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite (sum_of_SRH f).
  apply sum_of_ext.
  intros a.
  case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_delta_spider_bundled (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EqA : EqDecision A}
  {k n m} :
  tensor_apply_hom f (delta_spider_tensor_bundled k (n:=n) (m:=m))
    ≡ delta_spider_tensor_bundled (A:=A) k.
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite (SRH_Rlist_prod _).
  apply Rlist_prod_ext.
  rewrite Forall2_fmap_l.
  rewrite Forall2_vlookup.
  intros i.
  cbn.
  rewrite 2 vlookup_zip_with.
  apply tensor_apply_hom_delta_spider; apply _.
Qed.

Lemma tensor_apply_hom_stack_tensor (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A}
  {n m o p} (t : Tensor n m A) (t' : Tensor o p A) :
  tensor_apply_hom f (stack_tensor t t') ≡
  stack_tensor (tensor_apply_hom f t) (tensor_apply_hom f t').
Proof.
  intros v w Hv Hw.
  cbn.
  apply Hf.
Qed.

Lemma tensor_apply_hom_compose_tensor (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A}
  {n m o} (t : Tensor n m A) (t' : Tensor m o A) :
  tensor_apply_hom f (compose_tensor t t') ≡
  compose_tensor (tensor_apply_hom f t) (tensor_apply_hom f t').
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite (sum_of_SRH _).
  apply sum_of_ext.
  intros a.
  apply Hf.
Qed.

Lemma tensor_apply_hom_perm_tensor (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A, EQA : EqDecision A} 
  {n m} (fi : fin n -> fin m) :
  tensor_apply_hom f (perm_tensor fi) ≡
  perm_tensor fi.
Proof.
  intros v w _ _; cbn; case_decide; apply Hf.
Qed.

Lemma tensor_apply_hom_tensor_to_dimensionless (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A}
  {n m} (t : @Tensor R n m A) n' m' : 
  tensor_apply_hom f (tensor_to_dimensionless t n' m') ≡
  tensor_to_dimensionless (tensor_apply_hom f t) n' m'.
Proof.
  intros v w Hv Hw.
  cbn.
  do 2 (destruct (vec_cast_opt _ _); cbn); 
  [done|apply Hf..].
Qed.


Lemma tensor_apply_hom_id `{SA : Summable A} 
  {n m} (t : @Tensor R n m A) :
  tensor_apply_hom id t ≡ t.
Proof.
  done.
Qed.

Lemma tensor_apply_hom_ext_strong 
  (f g : R -> R')
  `{SA : Summable A} 
  {n m} (t : @Tensor R n m A) 
  (Hfg : forall v w, SummedElement v -> SummedElement w -> f (t v w) ==' g (t v w)):
  tensor_apply_hom f t ≡ tensor_apply_hom g t.
Proof.
  intros v w Hv Hw.
  cbn.
  auto.
Qed.

Lemma tensor_apply_hom_ext
  (f g : R -> R')
  (Hfg : forall r, f r ==' g r) 
  `{SA : Summable A} 
  {n m} (t : @Tensor R n m A) :
  tensor_apply_hom f t ≡ tensor_apply_hom g t.
Proof.
  intros v w Hv Hw.
  cbn.
  auto.
Qed.

End TensorHom.

