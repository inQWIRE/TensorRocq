From TensorRocq Require Export Homomorphism Props PropsGraphs 
  ProLike FreeSemiRing Summable CospanHyperGraph.
From stdpp Require Import vector.

Structure Signature {Struct : Mor nat} {A : Type} `{SA : Summable A, EqA : EqDecision A} := {
  #[canonical=yes] gens : Type;
  #[canonical=no] gens_equiv :: Equiv gens;
  #[canonical=no] gens_equivalence :: @Equivalence gens equiv;

  (* #[canonical=no] gen_arity_proper : Proper (equiv ==> eq) gen_arity; *)
  #[canonical=no] rules : forall {n m}, relation (PRO Struct gens n m);
}.

#[global] Arguments Signature _ _ {_ _} : assert.

Definition rules_of_rule_list {Struct T}
  (rules : list ({n & {m & (PRO Struct T n m * PRO Struct T n m)%type}})) :
  (forall n m, relation (PRO Struct T n m)) :=
  fun n m ap ap' => existT n (existT m (ap, ap')) ∈ rules.

Inductive SigTens {Struct} `{SA : Summable A, EqA : EqDecision A}
  (Sig : Signature Struct A) : Type :=
  | SigTensApp (f : Sig.(gens)) {n m}
    (v : vec A n) (w : vec A m) : SigTens Sig.


Definition SignatureTensorLike_base {Struct} `{SA : Summable A, EqA : EqDecision A}
  (Sig : Signature Struct A) : @TensorLike (FreeSemiRing nat (SigTens Sig))
    _ _ _ _ _ (FSR_SR nat)
    A _ _
    (Sig.(gens)) eq eq_equivalence := {|
  interpretTensor f :=
    fun n m v w => FSR_mono nat (SigTensApp Sig f v w);
|}.

Inductive PROEqRel {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct}
  {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
  relation (FreeSemiRing nat (SigTens Sig)) :=
  | PROEqRelAt (v : vec A n) (w : vec A m) :
    SummedElement v -> SummedElement w ->
    PROEqRel Sig lhs rhs
      (PRO_semantics (TensT:=SignatureTensorLike_base Sig) lhs v w)
      (PRO_semantics (TensT:=SignatureTensorLike_base Sig) rhs v w).

Inductive SigTensRel {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct}
  : relation (FreeSemiRing nat (SigTens Sig)) :=
  | SigTensRelIn {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
    Sig.(rules) lhs rhs ->
    forall x y,
    PROEqRel Sig lhs rhs x y -> SigTensRel Sig x y
  | SigTensRelEquiv (f f' : Sig.(gens)) {n m} (v : vec A n) (w : vec A m) :
    SummedElement v -> SummedElement w ->
    f ≡ f' ->
    SigTensRel Sig (FSR_mono nat $ SigTensApp Sig f v w)
    (FSR_mono nat $ SigTensApp Sig f' v w).


#[export] Instance SignatureTensorLike {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct} : TensorLike (FreeSemiRing nat (SigTens Sig))
    (SR:=FSR_SR_eqg nat (SigTensRel Sig)) A
    Sig.(gens) := {|
  interpretTensor f := fun n m v w => FSR_mono _ (SigTensApp Sig f v w);
  interpretTensorProper f f' Hf n m v w Hv Hw :=
    FSR_eqg_R_subrelation _ _ _ _ (SigTensRelEquiv Sig f f' v w Hv Hw Hf)
|}.

Definition SigTensPRO_eq {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct}
   {n m} : relation (PRO Struct Sig.(gens) n m) :=
  fun d d' =>
  @equiv _ (@Tensor_equiv _ _ _ _ _ _ (FSR_SR_eqg nat (SigTensRel Sig)) _ _ _ _)
  (PRO_semantics (TensT:=SignatureTensorLike_base Sig) d)
  (PRO_semantics (TensT:=SignatureTensorLike_base Sig) d').

#[export] Instance SigTensPRO_equivalence {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct} {n m} : @Equivalence (PRO Struct Sig.(gens) n m)
    (SigTensPRO_eq Sig) := Aux_relset.rel_preimage_equiv _ _ _.

#[export] Instance Pstack_sigeq {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct} {n m n' m'} :
  Proper (SigTensPRO_eq Sig ==> SigTensPRO_eq Sig ==> SigTensPRO_eq Sig)
  (@Pstack Struct Sig.(gens) n m n' m').
Proof.
  intros x x' Hx y y' Hy v w Hv Hw.
  unfold SigTensPRO_eq in *.
  cbn.
  apply FSR_eqg_mul.
  - apply Hx; apply _.
  - apply Hy; apply _.
Qed.

#[export] Instance Pcompose_sigeq {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct} {n m o} :
  Proper (SigTensPRO_eq Sig ==> SigTensPRO_eq Sig ==> SigTensPRO_eq Sig)
  (@Pcompose Struct Sig.(gens) n m o).
Proof.
  intros x x' Hx y y' Hy v w Hv Hw.
  unfold SigTensPRO_eq in *.
  cbn.
  change (sum_of ?f) with (id (sum_of f)).
  rewrite 2 (sum_of_SRH id (Hf:=id_FSR_eq_eqg _ _)).
  apply (sum_of_ext' (SR:=FSR_SR_eqg nat (SigTensRel Sig))).
  intros u Hu%SummedElement_iff.
  cbn.
  apply FSR_eqg_mul.
  - apply Hx; apply _.
  - apply Hy; apply _.
Qed.


Notation "d  '≡ᵣ@{' Sig '}'  d'" := (SigTensPRO_eq Sig d%pro d'%pro)
  (at level 70).

Notation "d '≡ᵣ' d'" := (d%pro ≡ᵣ@{_} d'%pro)
  (at level 70).

Lemma rules_hold {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A} (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct} {n m} (lhs rhs : PRO Struct Sig.(gens) n m) :
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
  `{SA : Summable A, EqA : EqDecision A, WFA : !WFSummable A} 
  (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct _ 
  (TensT:=SignatureTensorLike_base Sig)}
   {n m} (ap : PRO Struct Sig.(gens) n m) :
  graph_semantics (TensT:=SignatureTensorLike_base Sig) (PRO_graph_semantics ap) ≡
  PRO_semantics (TensT:=SignatureTensorLike_base Sig) ap.
Proof.
  apply PRO_graph_semantics_correct.
Qed.


Lemma SigTens_graph_semantics_correct' {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A, WFA : !WFSummable A} 
  (Sig : Signature Struct A)
  {TensS : StrictTensorLike (FreeSemiRing nat (SigTens Sig)) A Struct}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct _ 
  (TensT:=SignatureTensorLike_base Sig)} {n m} (ap : PRO Struct Sig.(gens) n m) :
  @equiv _ (@Tensor_equiv _ _ _ _ _ _ (FSR_SR_eqg nat (SigTensRel Sig)) _ _ _ _)
  (graph_semantics (TensT:=SignatureTensorLike_base Sig) (PRO_graph_semantics ap))
  (PRO_semantics (TensT:=SignatureTensorLike_base Sig) ap).
Proof.
  intros v w Hv Hw.
  apply FSReq_eqg.
  now apply SigTens_graph_semantics_correct.
Qed.

Lemma SigTens_graph_semantics_correct'' {Struct} 
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  `{SA : Summable A, EqA : EqDecision A, WFA : !WFSummable A} 
  (Sig : Signature Struct A)
  {TensS : forall `{SR : SemiRing R rO rI radd rmul req}, 
    StrictTensorLike R A Struct}
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct _ 
  (SR:=FSR_SR_eqg nat (SigTensRel Sig))
  (TensT:=SignatureTensorLike Sig)} {n m} (ap : PRO Struct Sig.(gens) n m) :
  @equiv _ (@Tensor_equiv _ _ _ _ _ _ (FSR_SR_eqg nat (SigTensRel Sig)) _ _ _ _)
  (graph_semantics (TensT:=SignatureTensorLike Sig) (PRO_graph_semantics ap))
  (PRO_semantics (TensT:=SignatureTensorLike Sig) ap).
Proof.
  apply PRO_graph_semantics_correct.
Qed.

(* FIXME: Move *)
Class FreeStrictTensorLike
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
}.


Lemma SignatureTensorLike_base_correct {Struct A} 
  `{SA : !Summable A, EqA : !EqDecision A}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A Struct}
  {FSTL : FreeStrictTensorLike A Struct}
   (Sig : Signature Struct A)
  {n m} (p : PRO Struct Sig.(gens) n m) :
  @equiv _ (@Tensor_equiv _ _ _ _ _ _ (FSR_SR_eqg nat (SigTensRel Sig)) _ _ _ _)
  (PRO_semantics (TensT:=SignatureTensorLike_base Sig) p)
  (PRO_semantics (TensT:=SignatureTensorLike Sig) p).
Proof.
  induction p.
  - done.
  - cbn.
    intros v w Hv Hw.
    cbn.
    (* symmetry. *)
    change (sum_of ?f) with (id (sum_of f)) at 1.
    rewrite (sum_of_SRH id (Hf:=id_FSR_eq_eqg _ _)).
    apply (sum_of_ext' (SR:=FSR_SR_eqg nat (SigTensRel Sig))).
    intros u Hu%SummedElement_iff.
    cbn.
    apply FSR_eqg_mul.
    + apply IHp1; apply _.
    + apply IHp2; apply _.
  - cbn.
    intros v w Hv Hw.
    cbn.
    apply FSR_eqg_mul.
    + apply IHp1; apply _.
    + apply IHp2; apply _.
  - etransitivity; [symmetry; apply (tensor_apply_hom_id (PRO_semantics _))|].
    apply strictInterpretTensor_free.
    apply id_SRH_subrel.
    apply _.
  - done.
Qed.

Lemma SigTens_graph_semantics_syntactic_eq {Struct A} 
  `{SA : !Summable A, EqA : !EqDecision A, WFA : !WFSummable A}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A Struct}
  {FSTL : FreeStrictTensorLike A Struct}  
   (Sig : Signature Struct A)
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct _ 
    (SR:=FSR_SR_eqg nat (SigTensRel Sig))
    (TensT:=SignatureTensorLike Sig)}

  {n m} (ap ap' : PRO Struct Sig.(gens) n m) :
  PRO_graph_semantics ap ≡ₛ PRO_graph_semantics ap' ->
  ap ≡ᵣ ap'.
Proof.
  unfold SigTensPRO_eq.
  intros Heq%(graph_semantics_syntactic_eq  (TensT:=SignatureTensorLike Sig)).

  rewrite 2 PRO_graph_semantics_correct in Heq.
  rewrite 2 SignatureTensorLike_base_correct.
  done.
Qed.



Lemma SigTens_graph_semantics_semantic_eq{Struct A} 
  `{SA : !Summable A, EqA : !EqDecision A, WFA : !WFSummable A}
  `{EqS : ∀ n m, Equiv (Struct n m), EquivS : ∀ n m, Equivalence (≡@{Struct n m})} 
  {STL : forall `{SR : SemiRing R rO rI radd rmul req},
    StrictTensorLike R A Struct}
  {FSTL : FreeStrictTensorLike A Struct}  
   (Sig : Signature Struct A)
  {GraphS : StructGraphable Struct Sig.(gens)}
  {LawGraphS : LawfulStructGraphable Struct _ 
    (SR:=FSR_SR_eqg nat (SigTensRel Sig))
    (TensT:=SignatureTensorLike Sig)}
  {n m} (ap ap' : PRO Struct Sig.(gens) n m) :
  PRO_graph_semantics ap ≡ₜ@{SignatureTensorLike Sig} PRO_graph_semantics ap' ->
  ap ≡ᵣ ap'.
Proof.
  unfold SigTensPRO_eq.
  unfold cohg_semantic_eq.
  rewrite 2 (SigTens_graph_semantics_correct'' _).
  rewrite 2 SignatureTensorLike_base_correct.
  done.
Qed.



