From TensorRocq Require Export Homomorphism Props PropsGraphs
  ProLike FreeSemiRing Summable CospanHyperGraph.
From stdpp Require Import vector.


(* FIXME: Move *)
Class FreeStrictTensorLike
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (T : nat -> nat -> Type) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  {STLD : forall `{SRD : SemiRingData R rO rI radd rmul},
    StrictTensorLikeData R A T}
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A T} := {
  strictInterpretTensor_free
    `{SR : SemiRing R rO rI radd rmul req}
    `{SR' : SemiRing R' rO' rI' radd' rmul' req'}
    (f : R -> R') {Hf : SemiRingHomomorphism f}
    {n m} (t : T n m) :
    tensor_apply_hom f (strictInterpretTensor t) ≡@{@Tensor R' n m A}
    strictInterpretTensor t
}.

#[export] Instance FSTL_MorUnion
  (A : Type) `{SA : Summable A, EQA : EqDecision A}
  (T : nat -> nat -> Type) `{EqT : ∀ n m, Equiv (T n m),
    EquivT : ∀ n m, @Equivalence (T n m) equiv}
  {STLD : forall `{SRD : SemiRingData R rO rI radd rmul},
    StrictTensorLikeData R A T}
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A T}
  (T' : nat -> nat -> Type) `{EqT' : ∀ n m, Equiv (T' n m),
    EquivT' : ∀ n m, @Equivalence (T' n m) equiv}
  {STLD' : forall `{SRD : SemiRingData R rO rI radd rmul},
    StrictTensorLikeData R A T'}
  {STL' : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A T'}
  {FSTL : FreeStrictTensorLike A T}
  {FSTL' : FreeStrictTensorLike A T'} :
  FreeStrictTensorLike A (MorUnion T T').
Proof.
  split.
  intros until f.
  intros Hf n m [t|t]; cbn; now apply strictInterpretTensor_free.
Qed.


#[export] Instance FSTL_Monoidal
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Monoidal.
Proof.
  split.
  intros until f.
  intros Hf n m t.
  rewrite 2 Monoidal_semantics.
  now rewrite (tensor_apply_hom_perm_tensor _).
Qed.

#[export] Instance FSTL_Symmetry
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Symmetry.
Proof.
  split.
  intros until f.
  intros Hf n m t.
  induction t as [n m].
  cbn.
  now apply tensor_apply_hom_swap.
Qed.

#[export] Instance FSTL_Autonomy
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Autonomy.
Proof.
  split.
  intros until f.
  intros Hf n m t.
  induction t as [n|n];
  cbn;
  [now apply tensor_apply_hom_cup|now apply tensor_apply_hom_cap].
Qed.

#[export] Instance FSTL_Frobenial
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Frobenial.
Proof.
  split.
  intros until f.
  intros Hf n m t.
  induction t as [|n m|k n m]; cbn.
  - apply (tensor_apply_hom_delta_spider _).
  - apply (tensor_apply_hom_delta_spider _).
  - apply (tensor_apply_hom_delta_spider_bundled _).
Qed.


#[export] Instance FSTL_SymmetricG
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A SymmetricG := _.

#[export] Instance FSTL_Autonomous
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Autonomous := _.

#[export] Instance FSTL_Frobenius
  (A : Type) `{SA : Summable A, EQA : EqDecision A} :
  FreeStrictTensorLike A Frobenius := _.




Structure Signature {Struct : Mor nat} {A : Type} := {
  #[canonical=yes] gens : Type;
  #[canonical=no] gens_equiv :: Equiv gens;
  #[canonical=no] gens_equivalence :: @Equivalence gens equiv;

  (* #[canonical=no] gen_arity_proper : Proper (equiv ==> eq) gen_arity; *)
  #[canonical=no] rules : forall {n m}, relation (PRO Struct gens n m);
}.

#[global] Arguments Signature _ _ : clear implicits, assert.

Definition rules_of_rule_list {Struct T}
  (rules : list ({n & {m & (PRO Struct T n m * PRO Struct T n m)%type}})) :
  (forall n m, relation (PRO Struct T n m)) :=
  fun n m ap ap' => existT n (existT m (ap, ap')) ∈ rules.

Inductive SigTens {Struct A}
  (Sig : Signature Struct A) : Type :=
  | SigTensApp (f : Sig.(gens)) {n m}
    (v : vec A n) (w : vec A m) : SigTens Sig.

Definition SigRing {Struct A} (Sig : Signature Struct A) : Type :=
  FreeSemiRing nat (SigTens Sig).

#[global] Typeclasses Opaque SigRing.

#[global] Instance SigRing_SRD {Struct A}
  (Sig : Signature Struct A) : SemiRingData (SigRing Sig) FSR_zero FSR_one
    FSR_add FSR_mul := mk_SRD.

#[global] Instance SignatureTensorLikeData
  {Struct A}
  (Sig : Signature Struct A) :
  TensorLikeData (SigRing Sig) A (Sig.(gens)) := {|
  interpretTensor f :=
    fun n m v w => FSR_mono nat (SigTensApp Sig f v w);
|}.


Inductive PROEqRel {Struct A} `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
  relation (SigRing Sig) :=
  | PROEqRelAt (v : vec A n) (w : vec A m) :
    SummedElement v -> SummedElement w ->
    PROEqRel Sig lhs rhs
      (PRO_semantics lhs v w)
      (PRO_semantics rhs v w).

Inductive SigTensRel {Struct A} {EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  : relation (SigRing Sig) :=
  | SigTensRelIn {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
    Sig.(rules) lhs rhs ->
    forall x y,
    PROEqRel Sig lhs rhs x y -> SigTensRel Sig x y
  | SigTensRelEquiv (f f' : Sig.(gens)) {n m} (v : vec A n) (w : vec A m) :
    SummedElement v ->
    SummedElement w ->
    f ≡ f' ->
    SigTensRel Sig (FSR_mono nat $ SigTensApp Sig f v w)
    (FSR_mono nat $ SigTensApp Sig f' v w).

Definition SigRing_eq {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct} :
  relation (SigRing Sig) := FSR_eqg nat (SigTensRel Sig).

#[export] Instance SigRing_SR {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct} :
  SemiRing (SigRing Sig) FSR_zero FSR_one
    FSR_add FSR_mul (SigRing_eq Sig)
    (SRD:=SigRing_SRD Sig) := FSR_SR_eqg nat _.

#[export] Instance SigRing_equiv {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct} : Equiv (SigRing Sig) :=
  SR_equiv.

#[export] Instance SigRing_equivalence {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct} :
  Equivalence (≡@{SigRing Sig}) :=
  SR_equivalence.

#[export, program] Instance SignatureTensorLike {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct} :
  TensorLike (SigRing Sig) A Sig.(gens).
Next Obligation.
  intros until TensSD.
  intro TensS.
  intros f f' Hf n m v w Hv Hw.
  apply FSR_eqg_R_subrelation.
  apply SigTensRelEquiv; done.
Qed.

Definition SigTensPRO_eq {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
   {n m} : relation (PRO Struct Sig.(gens) n m) :=
  fun d d' =>
  PRO_semantics d ≡ PRO_semantics d'.

#[export] Instance SigTensPRO_equivalence {Struct A} {EqA : EqDecision A}
  (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
   {n m} : @Equivalence (PRO Struct Sig.(gens) n m)
    (SigTensPRO_eq Sig) := Aux_relset.rel_preimage_equiv _ _ _.

#[export] Instance Pstack_sigeq {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct} {n m n' m'} :
  Proper (SigTensPRO_eq Sig ==> SigTensPRO_eq Sig ==> SigTensPRO_eq Sig)
  (@Pstack Struct Sig.(gens) n m n' m').
Proof.
  unfold SigTensPRO_eq.
  intros x x' Hx y y' Hy.
  cbn.
  apply stack_tensor_mor; assumption.
Qed.

#[export] Instance Pcompose_sigeq {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct}
  {LSA : LawfulSummableOver (SigRing Sig) A} {n m o} :
  Proper (SigTensPRO_eq Sig ==> SigTensPRO_eq Sig ==> SigTensPRO_eq Sig)
  (@Pcompose Struct Sig.(gens) n m o).
Proof.
  intros x x' Hx y y' Hy.
  unfold SigTensPRO_eq.
  cbn.
  apply compose_tensor_mor; assumption.
Qed.


Notation "d  '≡ᵣ@{' Sig '}'  d'" := (SigTensPRO_eq Sig d%pro d'%pro)
  (at level 70).

Notation "d '≡ᵣ' d'" := (d%pro ≡ᵣ@{_} d'%pro)
  (at level 70).

Lemma rules_hold {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct}
  {LSA : LawfulSummableOver (SigRing Sig) A}
  {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
  Sig.(rules) lhs rhs ->
  lhs ≡ᵣ rhs.
Proof.
  intros Hrule.
  unfold SigTensPRO_eq.
  intros v w Hv Hw.
  apply FSR_eqg_R_subrelation.
  econstructor; [eauto|].
  now constructor.
Qed.


Lemma SigTens_graph_semantics_correct {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct}
  {LSA : LawfulSummableOver (SigRing Sig) A}
  {WFA : WFSummableOver (SigRing Sig) A}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct Sig.(gens)
    (TensT:=SignatureTensorLike Sig)}
   {n m} (ap : PRO Struct Sig.(gens) n m) :
  graph_semantics (PRO_graph_semantics ap) ≡
  PRO_semantics ap.
Proof.
  apply PRO_graph_semantics_correct.
Qed.

Lemma SigTens_graph_semantics_syntactic_eq {Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct}
  {LSA : LawfulSummableOver (SigRing Sig) A}
  {WFA : WFSummableOver (SigRing Sig) A}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct Sig.(gens)
    (TensT:=SignatureTensorLike Sig)}

  {n m} (ap ap' : PRO Struct Sig.(gens) n m) :
  PRO_graph_semantics ap ≡ₛ PRO_graph_semantics ap' ->
  ap ≡ᵣ ap'.
Proof.
  unfold SigTensPRO_eq.
  intros Heq%(graph_semantics_syntactic_eq  (TensT:=SignatureTensorLike Sig)).

  rewrite 2 PRO_graph_semantics_correct in Heq.
  done.
Qed.



Lemma SigTens_graph_semantics_semantic_eq{Struct}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})}
  `{EqA : EqDecision A} (Sig : Signature Struct A)
  {SA : SummableOver (SigRing Sig) A}
  {TensSD : StrictTensorLikeData (SigRing Sig) A Struct}
  {TensS : StrictTensorLike (SigRing Sig) A Struct}
  {LSA : LawfulSummableOver (SigRing Sig) A}
  {WFA : WFSummableOver (SigRing Sig) A}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct Sig.(gens)
    (TensT:=SignatureTensorLike Sig)}
  {n m} (ap ap' : PRO Struct Sig.(gens) n m) :
  PRO_graph_semantics ap ≡ₜ@{SignatureTensorLikeData Sig} PRO_graph_semantics ap' ->
  ap ≡ᵣ ap'.
Proof.
  unfold SigTensPRO_eq.
  unfold cohg_semantic_eq.
  rewrite 2 (SigTens_graph_semantics_correct _).
  done.
Qed.



