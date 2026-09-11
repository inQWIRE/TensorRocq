Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Set Warnings "-stdlib-vector".
Require Import SetoidList SetoidPermutation.
Require Import Ring.
From stdpp Require Import vector fin.
From stdpp Require Export base list.
From TensorRocq Require Import Aux_stdpp Aux.
From TensorRocq Require Export Algebra.Definitions.

(* FIXME: Move to Algebra when it has stdpp*)
Lemma Rlist_sum_bind `{SR : SemiRing R rO rI radd rmul req} {A} (f : A -> list R) l :
  req (Rlist_sum (l ≫= f)) (Rlist_sum ((λ x, Rlist_sum (f x)) <$> l)).
Proof.
  induction l; [apply SR|].
  cbn.
  eapply SR.(Req_equiv).(Equivalence_Transitive);
  [apply Rlist_sum_app|].
  apply SR; [apply SR|].
  apply IHl.
Qed.

Lemma Rlist_prod_bind `{SR : SemiRing R rO rI radd rmul req} {A} (f : A -> list R) l :
  req (Rlist_prod (l ≫= f)) (Rlist_prod ((λ x, Rlist_prod (f x)) <$> l)).
Proof.
  induction l; [apply SR|].
  cbn.
  eapply SR.(Req_equiv).(Equivalence_Transitive);
  [apply Rlist_prod_app|].
  apply SR; [apply SR|].
  apply IHl.
Qed.



(* FIXME: Move *)
#[export] Instance SR_equiv `{SR : SemiRing R rO rI radd rmul req} :
  Equiv R := req.

#[export] Instance SR_equivalence `{SR : SemiRing R rO rI radd rmul req} :
  @Equivalence R equiv := SR.(Req_equiv).

(* A typeclass indicating a type can be summed over, hence
  used in tensor expressions. Note that this is in fact just
  expressing that there are some distinguished elements of the
  type. It is expected that the types used are finite and that
  these lists of elements are complete, but this is not enforced
  as it is not needed for proofs. So, if desirable, infinite types
  can be used, though only finitely many values will be used.

  The motivation for this definition is that it means multiple
  instances automatically commute with each other, which is not
  enforcable if the summation function is abstract. (In that case,
  a separate compatability typeclass would be required, which would
  make summations over lists of registers highly impractical and
  balloon proof requirements.) *)
Class Summable (A : Type) := sum_over {
  sum_elements : list A
}.

#[global] Arguments sum_over {_} _ : assert.


Class SummableOver R (A : Type) := sum_by {
  sum_of_internal (f : A -> R) : R;
  summable_element (a : A) : Prop;
}.

#[global] Arguments sum_by {_ _} _ _ : assert.
#[global] Arguments summable_element {_ _ _} _ : assert.
#[global] Arguments sum_of_internal {_ _ _} _%_function_scope : assert.

Class SummedElement `{SRA : SummableOver R A} (a : A) :=
  is_summable_element : summable_element a.


(* The sum of a function over a domain [A]. *)
Definition sum_of {R A} {SRA : SummableOver R A} (f : A -> R) : R :=
  sum_of_internal f.

#[global] Arguments sum_of {_ _ _} _%_function_scope : assert.

(* The sum of a function over a summable domain [A].
  We require the codomain to be a SemiRing so that
  typeclass search can find the definitions of 0
  and addition.  *)
#[global] Instance summable_summableover
  `{SR : SemiRing R rO rI radd rmul req} `{SA : Summable A} :
  SummableOver R A := sum_by (fun f => Rlist_sum (f <$> sum_elements)) (.∈ sum_elements).


Lemma sum_of_defn_abstract `{SRA : SummableOver R A} (f : A -> R) :
  sum_of f = SRA.(sum_of_internal) f.
Proof. reflexivity. Qed.

Lemma sum_of_defn_abstract' `{SRA : SummableOver R A} :
  sum_of = SRA.(sum_of_internal).
Proof. reflexivity. Qed.


(* Lemma to unfold [sum_of]. Should not be to reason about
  tensor expressions directly, only to reason about their
  definition, such as in relation to other libraries. *)
Lemma sum_of_defn `{SemiRing R rO rI radd rmul req} `{Summable A} (f : A -> R) :
  sum_of f = Rlist_sum (List.map f sum_elements).
Proof. reflexivity. Qed.

(* We want to prevent [sum_of] ever being evaluated, as this
  would be catastrophic in many concrete cases (for example,
  [Vector.t bool 10] has [sum_elements] with length [2^10]). *)
Global Opaque sum_of.

(** Tactics to manipulate expressions involving [sum_of] *)

(* Replaces [sum_of] with its definition in all hypotheses and goals *)
Ltac unfold_sum_of :=
  rewrite_strat (bottomup sum_of_defn).

(* Generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_elem l :=
  match goal with
  |- context [@sum_elements ?A ?SA] =>
    generalize (@sum_elements A SA);
    intros l
  end.

(* Replaces [sum_of] with its definition in all hypotheses and goals
  and generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_of l :=
  try unfold_sum_of;
  gen_sum_elem l.

(* Tries to solve a goal about [sum_of] by repeatedly unfolding
  [sum_of], generalizing [sum_elements], and inducting on the
  resulting goals. Applies [basetac] to the base case and
  [indtac IHl] to the inductive case *)
Ltac solve_sum_of basetac indtac :=
  let l := fresh "l" in
  let IHl := fresh "IHl" in
  gen_sum_of l;
  induction l as [|? l IHl];
  [basetac | indtac IHl].

(* Tries to solve a goal about [sum_of] by repeatedly unfolding
  [sum_of], generalizing [sum_elements], and inducting on the
  resulting goals. Solves goals with [simpl; ring], or
  [simpl; ring [IHl]] in the inductive case *)
Ltac solve_sum_of_ring :=
  solve_sum_of ltac:(simpl; ring) ltac:(fun IHl => simpl; ring [IHl]).

(* We have a special notation to make it easier to refer to summing over
  a uniformly summable domain *)
Notation sum_of' SA :=
  (@sum_of _ _ (summable_summableover (SA:=SA))).

(* We have a specific notation for a sum over a single register, so
  that sums over many registers can look better. *)
Notation " '∑' x ':' T ',' f " :=
  (@sum_of _ T _ (fun x => f))
  (at level 60,
  x name, T at level 200, f at level 69,
  right associativity).

Notation " '∑' x ',' f " :=
  (∑ x : _, f)
  (at level 60,
  x name, f at level 69,
  right associativity,
  only parsing).


(* A class denoting that a [SummableOver R A] instance behaves like
  a sum over (possibly a subset of) [A], with respect to the semiring
  structure of [R] *)
Class LawfulSummableOver R (A : Type)
  `{SR : SemiRing R rO rI radd rmul req}
  `{SRA : SummableOver R A} := {
  sum_of_ext (f g : A -> R)
    (Hfg : forall a, SummedElement a -> req (f a) (g a)) :
    req (sum_of f) (sum_of g);
  sum_of_0 : req (sum_of (fun _ => rO)) rO;
  sum_of_add (f g : A -> R) :
    req (sum_of (fun a => radd (f a) (g a))) (radd (sum_of f) (sum_of g));
  sum_of_distr_l (f : A -> R) r :
    req (rmul (sum_of f) r) (sum_of (fun a => rmul (f a) r));
  sum_of_comm_abstract (f : A -> A -> R) :
    req (∑ a, ∑ b, f a b) (∑ b, ∑ a, f a b);
}.

Section summable_lawfulsummableover.

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

Context `{SA : Summable A}.

#[global] Instance summable_lawfulsummableover : LawfulSummableOver R A.
Proof.
  assert (Hext : ∀ f g : A → R,
  (∀ a : A, SummedElement (R:=R) a → f a == g a) → ∑ x : A, f x == ∑ x : A, g x).
  1:{
    unfold SummedElement.
    cbn.
    intros f g Hfg.
    unfold_sum_of.
    induction sum_elements as [|a l IHl]; [done|].
    cbn.
    f_equiv; auto using elem_of_list.
  }
  split.
  - done.
  - solve_sum_of_ring.
  - intros; solve_sum_of_ring.
  - intros; solve_sum_of_ring.
  - intros f.
    rewrite (Hext _ (λ a, Rlist_sum (map (λ b : A, f a b) sum_elements)))
      by now intros; rewrite sum_of_defn.
    rewrite sum_of_defn.
    rewrite (Hext _ (λ b, Rlist_sum (map (λ a : A, f a b) sum_elements)))
      by now intros; rewrite sum_of_defn.
    rewrite sum_of_defn.
    generalize sum_elements at 1 4.
    generalize sum_elements.
    intros lB lA.
    induction lB.
    + cbn.
      symmetry.
      induction lA; [done|].
      cbn.
      rewrite IHlA; ring.
    + cbn.
      rewrite IHlB.
      clear IHlB. 
      induction lA.
      * cbn; ring.
      * cbn.
        rewrite <- IHlA.
        ring.
Qed.

End summable_lawfulsummableover.


Section SumTheory.

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


Lemma sum_of_ext_gen `{Summable A} (f g : A -> R)
  (eqR : relation R) : Reflexive eqR ->
  Morphisms.Proper (eqR ==> eqR ==> eqR) radd ->
  (forall x, eqR (f x) (g x)) ->
  eqR (∑ x, f x) (∑ x, g x).
Proof.
  intros Heq Hadd Hfg.
  gen_sum_of l.
  induction l; [reflexivity|].
  simpl.
  apply Hadd.
  - apply Hfg.
  - apply IHl.
Qed.

Lemma sum_of_ext_eq `{Summable A} (f g : A -> R) :
  (forall x, f x = g x) ->
  ∑ x, f x = ∑ x, g x.
Proof.
  apply sum_of_ext_gen; apply _.
Qed.



Lemma sum_of_distr_r `{SummableOver R A,
  !LawfulSummableOver R A} (f : A -> R) (r : R) :
  r * (∑ x, f x) == ∑ x, r * f x.
Proof.
  rewrite rmul_comm, sum_of_distr_l.
  apply sum_of_ext.
  intros.
  apply rmul_comm.
Qed.

Lemma sum_of_0' `{SummableOver R A,
  !LawfulSummableOver R A} (f : A -> R) :
  (forall a, SummedElement a -> f a == 0) ->
  sum_of f == 0.
Proof.
  intros Hf.
  rewrite <- sum_of_0.
  apply sum_of_ext; done.
Qed.


Lemma sum_of_comm_l `{Summable A, SummableOver R B, !LawfulSummableOver R B} (f : A -> B -> R) :
  ∑ x, ∑ y, f x y == ∑ y, ∑ x, f x y.
Proof.
  rewrite sum_of_defn.
  erewrite sum_of_ext by
    now intros; apply eq_reflexivity, sum_of_defn.
  gen_sum_elem lA.
  induction lA.
  - cbn.
    now rewrite sum_of_0.
  - simpl.
    rewrite sum_of_add.
    rewrite IHlA.
    reflexivity.
Qed.

Lemma sum_of_comm `{Summable A, Summable B} (f : A -> B -> R) :
  ∑ x, ∑ y, f x y == ∑ y, ∑ x, f x y.
Proof.
  apply sum_of_comm_l.
Qed.

Lemma sum_of_mul_sum_of `{Summable A, Summable B} (f : A -> R) (g : B -> R) :
  (∑ x, f x) * (∑ y, g y) == ∑ x, ∑ y, f x * g y.
Proof.
  rewrite sum_of_distr_l.
  apply sum_of_ext; intros x.
  now rewrite sum_of_distr_r.
Qed.

Lemma sum_of_ext' `{Summable A} (f g : A -> R) :
  (forall a, a ∈ sum_elements -> f a == g a) ->
  sum_of f == sum_of g.
Proof.
  intros Hfg.
  unfold_sum_of.
  apply Rlist_sum_ext.
  rewrite Forall2_fmap_l, Forall2_fmap_r.
  apply Forall_Forall2_diag.
  now apply Forall_forall.
Qed.

Lemma sum_of_relabel `{Summable A, Summable B} (f : A -> B) (g : B -> R) :
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ b : B, g b == ∑ a : A, g (f a).
Proof.
  unfold_sum_of.
  intros Hperm.
  apply Rlist_sum_perm.
  rewrite <- Hperm, list_map_fmap, <- list_fmap_compose.
  reflexivity.
Qed.

Lemma sum_of_relabel'_l2r `{Summable A, Summable B}
  (f : A -> B) (g : A -> R) (h : B -> R) :
  (forall a, a ∈ sum_elements -> g a == h (f a)) ->
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ a : A, g a == ∑ b : B, h b.
Proof.
  intros Hfh Hf.
  rewrite (sum_of_relabel f h) by assumption.
  now apply sum_of_ext'.
Qed.


Lemma sum_of_relabel'_r2l `{Summable A, Summable B}
  (f : B -> A) (g : A -> R) (h : B -> R) :
  (forall b, b ∈ sum_elements -> g (f b) == h b) ->
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ a : A, g a == ∑ b : B, h b.
Proof.
  intros Hfh Hf.
  rewrite (sum_of_relabel f g) by assumption.
  now apply sum_of_ext'.
Qed.

End SumTheory.


Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req}
  {A} {SRA : SummableOver R A} `{!LawfulSummableOver R A} : (@sum_of R A _)
  with signature Morphisms.pointwise_relation A req ==> req as
  sum_of_mor.
Proof.
  intros; apply sum_of_ext; auto.
Qed.

Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req}
  {A} {SA : Summable A} : (@sum_of R A _)
  with signature Morphisms.pointwise_relation A eq ==> (@eq R) as
  sum_of_mor_eq.
Proof.
  apply sum_of_ext_eq.
Qed.

