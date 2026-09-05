From TensorRocq Require Export Aux.
From stdpp Require Import base.


Lemma forall_iff {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) → (∀ a, P a) ↔ (∀ a, Q a).
Proof. firstorder. Qed.

Lemma exists_iff {A} (P Q : A → Prop) :
  (∀ a, P a ↔ Q a) → (∃ a, P a) ↔ (∃ a, Q a).
Proof. firstorder. Qed.

Lemma forall_and_r {A} (P : A → Prop) Q :
  A →
  (∀ a, P a) ∧ Q ↔ (∀ a, P a ∧ Q).
Proof. firstorder. Qed.

Lemma forall_impl_and_r {A} (P Q : A → Prop) R :
  (exists a, P a) →
  (∀ a, P a → Q a) ∧ R ↔ (∀ a, P a → Q a /\ R).
Proof. firstorder. Qed.

Lemma forall_impl_unique {A} (P Q : A → Prop) :
  ∀ a, P a → (∀ b, P b → b = a) →
  (∀ a, P a → Q a) ↔ Q a.
Proof. firstorder congruence. Qed.

Lemma impl_False_l (P Q : Prop) : ~ P → (P → Q) ↔ True.
Proof. firstorder. Qed.

Lemma and_true_r (P Q : Prop) : Q → (P ∧ Q ↔ P).
Proof. firstorder. Qed.


Lemma and_iff_from_l' {P P' Q R : Prop} : (P ↔ P') → (P -> Q ↔ R) ->
  (P ∧ Q ↔ P' ∧ R).
Proof.
  firstorder.
Qed.
Lemma or_is_true_l {P Q : Prop} : P -> P \/ Q <-> True.
Proof.
  intuition idtac.
Qed.
Lemma or_is_true_r {P Q : Prop} : Q -> P \/ Q <-> True.
Proof.
  intuition idtac.
Qed.
Lemma or_is_false_l {P Q : Prop} : ~ P -> P \/ Q <-> Q.
Proof.
  intuition idtac.
Qed.
Lemma or_is_false_r {P Q : Prop} : ~ Q -> P \/ Q <-> P.
Proof.
  intuition idtac.
Qed.
Lemma and_is_true_l {P Q : Prop} : P -> P /\ Q <-> Q.
Proof.
  intuition idtac.
Qed.
Lemma and_is_true_r {P Q : Prop} : Q -> P /\ Q <-> P.
Proof.
  intuition idtac.
Qed.
Lemma and_is_false_l {P Q : Prop} : ~ P -> P /\ Q <-> False.
Proof.
  intuition idtac.
Qed.
Lemma and_is_false_r {P Q : Prop} : ~ Q -> P /\ Q <-> False.
Proof.
  intuition idtac.
Qed.


Lemma exists_impl_iff {A} (P : A -> Prop) (Q : Prop) :
  ((exists a, P a) -> Q) <-> forall a, P a -> Q.
Proof.
  firstorder.
Qed.
Lemma and_impl_iff (P Q R : Prop) :
  (P /\ Q -> R) <-> (P -> Q -> R).
Proof.
  firstorder.
Qed.
Lemma or_impl_iff (P Q R : Prop) :
  ((P \/ Q) -> R) <-> ((P -> R) /\ (Q -> R)).
Proof.
  firstorder.
Qed.
Lemma forall_prod_iff {A B} (P : A * B -> Prop) :
  (forall ab, P ab) <-> forall a b, P (a, b).
Proof.
  split; try intros ? []; firstorder.
Qed.


Lemma exists_and_r {A} (P : A -> Prop) Q :
  ex P /\ Q <-> ex (λ a, P a /\ Q).
Proof.
  firstorder.
Qed.
Lemma exists_and_l {A} (P : A -> Prop) Q :
  Q /\ ex P <-> ex (λ a, Q /\ P a).
Proof.
  firstorder.
Qed.
Lemma exists_or {A} (P Q : A -> Prop) :
  ex (λ a, P a \/ Q a) <-> ex P \/ ex Q.
Proof.
  firstorder.
Qed.



Class Bijection {A B} (RA : relation A) (RB : relation B)
  (f : A -> B) := {
  bij_prop :: Proper (RA ==> RB) f;
  bij_inj :: Inj RA RB f;
  bij_surj :: Surj RB f;
}.

Lemma cancel_bijection {A B} {RA : relation A} {RB : relation B}
  {HRA : Equivalence RA}
  {f : A -> B} {g : B -> A}
  {Hgf : Cancel RA g f} {Hfg : Cancel RB f g}
  {Hf : Proper (RA ==> RB) f}
  {Hg : Proper (RB ==> RA) g} : Bijection RA RB f.
Proof.
  split.
  - apply _.
  - apply cancel_inj.
  - apply cancel_surj.
Qed.


Lemma exists_surjection {A B} {RB : relation B}
  (f : A -> B) {Hf : Surj RB f}
  (P : B -> Prop) {HP : Proper (RB ==> iff) P} :
  ex P <-> ex (P ∘ f).
Proof.
  split; [|now intros []; eauto].
  intros (x & Hx).
  specialize (Hf x) as [y Hy].
  rewrite <- Hy in Hx.
  eauto.
Qed.

Lemma exists_relabel'_l2r {A B} (f : A -> B)
  (P : A -> Prop) (Q : B -> Prop)
  {RA : relation A} {RB : relation B}
  (HQ : Proper (RB ==> iff) Q)
  (Hf : Surj RB f)
  (HPQ : forall a, P a <-> Q (f a)) :
  ex P <-> ex Q.
Proof.
  split; [now intros [? ?%HPQ]; eauto|].
  intros (y & Hy).
  destruct (surj f y) as [x Hx].
  rewrite <- Hx in Hy.
  rewrite <- HPQ in Hy.
  eauto.
Qed.


Lemma exists_relabel'_r2l {A B} (f : B -> A)
  (P : A -> Prop) (Q : B -> Prop)
  {RA : relation A} {RB : relation B}
  (HP : Proper (RA ==> iff) P)
  (Hf : Surj RA f)
  (HPQ : forall a, P (f a) <-> Q a) :
  ex P <-> ex Q.
Proof.
  split; [|now intros [? ?%HPQ]; eauto].
  intros (y & Hy).
  destruct (surj f y) as [x Hx].
  rewrite <- Hx in Hy.
  rewrite HPQ in Hy.
  eauto.
Qed.

Lemma exists_iff_of_unique {A} {P : A -> Prop} (a : A) :
  (∀ b, P b -> b = a) ->
  (∃ b, P b) <-> P a.
Proof.
  intros HP.
  split; [|eauto].
  intros [b Hb].
  apply HP in Hb as Hab.
  now subst.
Qed.

Lemma exists_eq_l_iff {A} (P : A -> Prop) (b : A) :
  (∃ a, a = b ∧ P a) ↔ P b.
Proof.
  split; [|eauto].
  now intros (? & -> & ?).
Qed.

Lemma exists_eq_l_iff' {A} (P : A -> Prop) (b : A) :
  (∃ a, b = a ∧ P a) ↔ P b.
Proof.
  setoid_rewrite (eq_comm b).
  apply exists_eq_l_iff.
Qed.

Lemma exists_eq_r_iff {A} (P : A -> Prop) (b : A) :
  (∃ a, P a ∧ a = b) ↔ P b.
Proof.
  setoid_rewrite (and_comm (P _)).
  apply exists_eq_l_iff.
Qed.

Lemma exists_eq_r_iff' {A} (P : A -> Prop) (b : A) :
  (∃ a, P a ∧ b = a) ↔ P b.
Proof.
  setoid_rewrite (and_comm (P _)).
  apply exists_eq_l_iff'.
Qed.