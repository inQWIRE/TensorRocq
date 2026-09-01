From TensorRocq Require Import Aux_stdpp Algebra Tensor.
From stdpp Require Import vector.

Definition tensor_apply_hom {R R'} (f : R -> R')
  {n m A} (t : @Tensor R n m A) : @Tensor R' n m A :=
  fun v w => f (t v w).

#[global] Arguments tensor_apply_hom {_ _} _ {_ _ _} _ _ _ / : assert.



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

(* FIXME: Move *)
Lemma tensor_equiv_alt `{SA : Summable A, EqA : EqDecision A}
  {n m} (t t' : @Tensor R n m A) :
  t ≡ t' <-> Forall (λ v, Forall (λ w, t v w == t' v w) sum_elements) sum_elements.
Proof.
  rewrite Forall_forall.
  setoid_rewrite Forall_forall.
  unfold equiv, Tensor_equiv, tensoreq.
  setoid_rewrite SummedElement_iff.
  firstorder.
Qed.

#[export] Instance tensor_equiv_dec (HRdec : RelDecision req)
  `{SA : Summable A, EqA : EqDecision A} {n m} : RelDecision (≡@{@Tensor R n m A}).
refine (fun t t' => cast_if (decide (Forall (λ v, Forall (λ w, t v w == t' v w) sum_elements) sum_elements)));
abstract (now rewrite tensor_equiv_alt).
Defined.

Lemma tensor_equiv_to_bool `{SA : Summable A, EqA : EqDecision A}
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

Lemma tensor_apply_hom_stack (f : R -> R')
  {Hf : SemiRingHomomorphism f} `{SA : Summable A}
  {n m o p} (t : Tensor n m A) (t' : Tensor o p A) :
  tensor_apply_hom f (stack_tensor t t') ≡
  stack_tensor (tensor_apply_hom f t) (tensor_apply_hom f t').
Proof.
  intros v w Hv Hw.
  cbn.
  apply Hf.
Qed.

Lemma tensor_apply_hom_compose (f : R -> R')
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

Lemma tensor_apply_hom_perm (f : R -> R')
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


End TensorHom.


From TensorRocq Require Import ProLike.

From TensorRocq Require Import ProQuote.

Class TensorLikeHom'
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
  (T : Mor nat) `{EqT : ∀ n m, Equiv (T n m),
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
  (T : Mor nat) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  {STL : StrictTensorLike R A T}
  {STL' : StrictTensorLike R' A T} := {
  strictInterpretTensor_hom {n m} (t : T n m) :
    tensor_apply_hom f (strictInterpretTensor t) ≡
    strictInterpretTensor t
}.

Section STLH.

Context `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
  (A : Type) `{SA : Summable A, EQA : EqDecision A, WFA : WFSummable A}.

#[export] Instance STLH_morunion 
  (T : Mor nat) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  (T' : Mor nat) `{EqT' : ∀ n m, Equiv (T' n m),
    EquivT' : ∀ n m, @Equivalence (T' n m) equiv}
  {STL : StrictTensorLike R A T}
  {STL' : StrictTensorLike R' A T}
  {ST'L : StrictTensorLike R A T'}
  {ST'L' : StrictTensorLike R' A T'} 
  {STLH : StrictTensorLikeHom f A T}
  {ST'LH : StrictTensorLikeHom f A T'} : 
  StrictTensorLikeHom f A (MorUnion T T').
Proof.
  split.
  intros n m [t|t']; cbn; apply strictInterpretTensor_hom.
Qed.



#[export] Instance STLH_Monoidal : 
  StrictTensorLikeHom f A Monoidal.
Proof.
  split.
  intros n m t.
  rewrite Monoidal_semantics.
  rewrite (tensor_apply_hom_perm _).
  rewrite <- Monoidal_semantics.
  done.
Qed.

#[export] Instance STLH_Symmetry : 
  StrictTensorLikeHom f A Symmetry.
Proof.
  split.
  intros n m [n' m'].
  cbn.
  apply (tensor_apply_hom_swap _).
Qed.

#[export] Instance STLH_Autonomy : 
  StrictTensorLikeHom f A Autonomy.
Proof.
  split.
  intros n m [k|k];
  cbn;
  [apply (tensor_apply_hom_cup _)|apply (tensor_apply_hom_cap _)].
Qed.

#[export] Instance STLH_Frobenial : 
  StrictTensorLikeHom f A Frobenial.
Proof.
  split.
  intros n m t;
  induction t as [|n m|k n m];
  cbn.
  - apply (tensor_apply_hom_delta_spider _).
  - apply (tensor_apply_hom_delta_spider _).
  - apply (tensor_apply_hom_delta_spider_bundled _).
Qed.

#[export] Instance STLH_SymmetricG : 
  StrictTensorLikeHom f A SymmetricG := _.

#[export] Instance STLH_Autonomous : 
  StrictTensorLikeHom f A Autonomous := _.

#[export] Instance STLH_Frobenius : 
  StrictTensorLikeHom f A Frobenius := _.

End STLH.

  



Lemma map_PRO_id_semantics
  `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (Struct : Mor nat) `{EqS : ∀ n m, Equiv (Struct n m),
    EquivS : ∀ n m, @Equivalence (Struct n m) equiv}
  {STL : StrictTensorLike R A Struct}
  {STL' : StrictTensorLike R' A Struct}
  {STLH : StrictTensorLikeHom f A Struct}
  {T T'} `{EqT : Equiv T, EqT' : Equiv T'}
  `{EquivT : Equivalence T equiv, EquivT' : Equivalence T' equiv}
  (fT : T -> T')
  {TensT : TensorLike R A T} {TensT' : TensorLike R' A T'}
  {TLH : TensorLikeHom' f A fT}
  {n m} (p : PRO Struct T n m) :
  PRO_semantics (map_PRO (λ _ _ s, s) fT p) ≡
  tensor_apply_hom f (PRO_semantics p).
Proof.
  induction p.
  - cbn.
    now rewrite tensor_apply_hom_delta.
  - cbn.
    rewrite tensor_apply_hom_compose by done.
    apply compose_tensor_mor; done.
  - cbn.
    rewrite tensor_apply_hom_stack by done.
    apply stack_tensor_mor; done.
  - cbn.
    rewrite strictInterpretTensor_hom.
    done.
  - cbn.
    rewrite TLH.(interpretTensor_hom).
    done.
Qed.

Lemma PRO_denote_semantics
  `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (Struct : Mor nat) `{EqS : ∀ n m, Equiv (Struct n m),
    EquivS : ∀ n m, @Equivalence (Struct n m) equiv}
  {STL : StrictTensorLike R A Struct}
  {STL' : StrictTensorLike R' A Struct}
  {STLH : StrictTensorLikeHom f A Struct}
  {T T'} `{EqT : Equiv T, EqT' : Equiv T'}
  `{EquivT : Equivalence T equiv, EquivT' : Equivalence T' equiv}
  (fT : T -> T')
  {TensT : TensorLike R A T} {TensT' : TensorLike R' A T'}
  {TLH : TensorLikeHom' f A fT}
  {n m} (p : PRO Struct T n m) :
  PRO_semantics (PRO_denote fT p) ≡
  tensor_apply_hom f (PRO_semantics p).
Proof.
  apply (map_PRO_id_semantics f A Struct fT p).
Qed.

#[export] Instance PRO_semantics_equiv
  `{SR : SemiRing R rO rI radd rmul req}
  {A : Type} `{SA : Summable A, EQA : EqDecision A}
  {Struct : Mor nat} `{EqS : ∀ n m, Equiv (Struct n m),
    EquivS : ∀ n m, @Equivalence (Struct n m) equiv}
  {T} `{EqT : Equiv T, EquivT : Equivalence T equiv}
  {STL : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T} {n m} : 
  Proper ((≡@{PRO Struct T n m}) ==> (≡@{@Tensor R n m A})) PRO_semantics.
Proof.
  intros p q Hpq.
  induction Hpq.
  - done.
  - cbn.
    now f_equiv.
  - cbn.
    now apply interpretTensorProper.
  - cbn.
    now apply compose_tensor_mor.
  - cbn.
    now apply stack_tensor_mor.
Qed.


Lemma PRO_semantics_eq_by_quote `{SR : SemiRing R rO rI radd rmul req}
  `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (Struct : Mor nat) `{EqS : ∀ n m, Equiv (Struct n m),
    EquivS : ∀ n m, @Equivalence (Struct n m) equiv}
  {STL : StrictTensorLike R A Struct}
  {STL' : StrictTensorLike R' A Struct}
  {STLH : StrictTensorLikeHom f A Struct}
  {T T'} `{EqT : Equiv T, EqT' : Equiv T'}
  `{EquivT : Equivalence T equiv, EquivT' : Equivalence T' equiv}
  (fT : T -> T')
  {TensT : TensorLike R A T} {TensT' : TensorLike R' A T'}
  {TLH : TensorLikeHom' f A fT}
  {n m} (dp dq : PRO Struct T n m) (p q : PRO Struct T' n m) :
  PRO_quote fT dp p -> PRO_quote fT dq q ->
  PRO_semantics dp ≡@{@Tensor _ n m A} PRO_semantics dq ->
  PRO_semantics p ≡@{@Tensor _ n m A} PRO_semantics q.
Proof.
  intros Hp Hq Hdpq.
  rewrite <- (Hp : _ ≡ _), <- (Hq : _ ≡ _).
  rewrite 2 (PRO_denote_semantics f A _ fT).
  f_equiv.
  done.
Qed.




