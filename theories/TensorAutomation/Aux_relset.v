From stdpp Require Import relations sets.

#[export] Instance relation_elem_of {A B} : ElemOf (A * B) (A -> B -> Prop) :=
  fun ab R => R ab.1 ab.2.
#[export] Instance relation_empty {A B} : Empty (A -> B -> Prop) :=
  fun a b => False.
#[export] Instance relation_top {A B} : Top (A -> B -> Prop) :=
  fun a b => True.
#[export] Instance relation_singleton {A B} : Singleton (A * B) (A -> B -> Prop) :=
  fun ab => fun a b => (a, b) = ab.
#[export] Instance relation_union {A B} : Union (A -> B -> Prop) :=
  fun R R' => fun a b => R a b \/ R' a b.
#[export] Instance relation_intersection {A B} : Intersection (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ R' a b.
#[export] Instance relation_difference {A B} : Difference (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ ~ R' a b.

#[global] Arguments relation_elem_of {_ _} _ _ / : assert.
#[global] Arguments relation_empty {_ _} _ _ / : assert.
#[global] Arguments relation_top {_ _} _ _ / : assert.
#[global] Arguments relation_singleton {_ _} _ _ _ / : assert.
#[global] Arguments relation_union {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_intersection {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_difference {_ _} _ _ _ _ / : assert.




#[export] Program Instance relation_semi_set {A B} : SemiSet (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_set {A B} : Set_ (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_top_set {A B} : TopSet (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Instance rel_empty_symm {A} : @Symmetric A ∅.
Proof. easy. Qed.

#[export] Instance rel_empty_trans {A} : @Transitive A ∅.
Proof. easy. Qed.

#[export] Instance rel_top_equiv {A} : @Equivalence A ⊤.
Proof. easy. Qed.


#[export] Instance rel_union_refl {A} {R R' : relation A} :
  TCOr (Reflexive R) (Reflexive R') -> Reflexive (R ∪ R').
Proof.
  intros [HR|HR']; [left|right]; reflexivity.
Qed.

#[export] Instance rel_union_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∪ R').
Proof.
  unfold Symmetric.
  unfold union, relation_union.
  firstorder.
Qed.


#[export] Instance rel_intersection_refl {A} {R R' : relation A} :
  Reflexive R -> Reflexive R' -> Reflexive (R ∩ R').
Proof.
  intros; split; reflexivity.
Qed.

#[export] Instance rel_intersection_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∩ R').
Proof.
  unfold Symmetric.
  unfold intersection, relation_intersection.
  firstorder.
Qed.

#[export] Instance rel_intersection_trans {A} {R R' : relation A} :
  Transitive R -> Transitive R' -> Transitive (R ∩ R').
Proof.
  intros ? ?.
  intros ? ? ? [] []; split; etransitivity; eauto.
Qed.

#[export] Instance rel_intersection_equiv {A} {R R' : relation A} :
  Equivalence R -> Equivalence R' -> Equivalence (R ∩ R').
Proof.
  intros ? ?; split; apply _.
Qed.


#[export] Instance rel_difference_refl {A} {R R' : relation A} :
  Reflexive R -> Irreflexive R' -> Reflexive (R ∖ R').
Proof.
  intros HR HR'; split; [apply HR|apply HR'].
Qed.

#[export] Instance rel_difference_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∖ R').
Proof.
  intros ? ?.
  intros a a' [HRa%symmetry HR'a%not_symmetry].
  now split.
Qed.

Section preimage.
Context {A B} (f : A -> B) (R : relation B).
Definition rel_preimage : relation A :=
  fun a b => R (f a) (f b).

#[export] Instance rel_preimage_refl : Reflexive R -> Reflexive rel_preimage.
Proof.
  intros ? ?; hnf; reflexivity.
Qed.

#[export] Instance rel_preimage_symm : Symmetric R -> Symmetric rel_preimage.
Proof.
  intros ? ? ? ?; hnf; symmetry; easy.
Qed.

#[export] Instance rel_preimage_trans : Transitive R -> Transitive rel_preimage.
Proof.
  unfold rel_preimage.
  intros ? ? ? ? ? ?; etransitivity; eauto.
Qed.

#[export] Instance rel_preimage_equiv : Equivalence R -> Equivalence rel_preimage.
Proof.
  intros ?; split; apply _.
Qed.

End preimage.