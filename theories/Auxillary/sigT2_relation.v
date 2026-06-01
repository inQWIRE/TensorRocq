Require Import Setoid. 
From TensorRocq Require Import Aux_stdpp.
From stdpp Require Import base.


(* TODO: Factor sigT2_relation out into a file, with another specializing it to
  graphs. (TODO: Maybe a scope [rel_scope] with bare notations "≡ := equiv", etc,
    to support having a metanotation "[≡]ₕ" (meaning heterogenous ≡, but where
      ≡ could also be ≡ᵥ, etc. )) *)

Inductive sigT2_relation {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) : relation {ab : A * B & P ab.1 ab.2} :=
  | mk_sigT2_relation {a b} (x y : P a b) : R a b x y ->
    sigT2_relation R (existT (a, b) x) (existT (a, b) y).

Lemma sigT2_relation_alt {A B}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) x y :
  sigT2_relation R x y <-> exists Hab, R _ _ (projT2 x) (eq_rect_r _ (projT2 y) Hab).
Proof.
  split.
  - intros HR.
    induction HR.
    cbn.
    now exists eq_refl.
  - destruct x as [[a b] x], y as [[a' b'] y].
    intros (Hab & HR).
    cbn in Hab.
    revert y HR.
    revert Hab.
    generalize (a', b').
    intros p <-.
    cbn.
    now constructor.
Qed.

Lemma mk_sigT2_relation_alt {A B}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b))
  {a b a' b'} (x : P a b) (y : P a' b') :
  (exists Ha Hb, R _ _ x
    (eq_rect_r (x:=(a',b')) (λ ab, P ab.1 ab.2) y
    (eq_trans (f_equal (a,.) Hb) (f_equal (.,b') Ha) : (a, b) = (a', b')))) ->
  sigT2_relation R (existT (a, b) x) (existT (a', b') y).
Proof.
  intros (-> & -> & Hrel).
  now constructor.
Qed.


#[export] Instance sigT2_relation_refl {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Reflexive (R a b)} :
  Reflexive (sigT2_relation R).
Proof.
  intros [[a b] x].
  constructor.
  reflexivity.
Qed.

#[export] Instance sigT2_relation_symm {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Symmetric (R a b)} :
  Symmetric (sigT2_relation R).
Proof.
  intros x y Hxy.
  induction Hxy.
  constructor.
  now symmetry.
Qed.

#[export] Instance sigT2_relation_trans {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Transitive (R a b)} :
  Transitive (sigT2_relation R).
Proof.
  intros x y z Hxy Hyz.
  rewrite sigT2_relation_alt in *.
  destruct Hxy as (Hab & Hxy), Hyz as (Hbc & Hyz).
  exists (eq_trans Hab Hbc).
  destruct x, y, z; cbn in *.
  subst.
  cbn in *.
  now etransitivity; eauto.
Qed.

#[export] Instance sigT2_relation_equivalence {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Equivalence (R a b)} :
  Equivalence (sigT2_relation R).
Proof.
  split; apply _.
Qed.

#[export] Instance sigT2_relation_subrelation {A B} {P : A -> B -> Type}
  (R R' : forall a b, relation (P a b)) `{HR : forall a b, subrelation (R a b) (R' a b)} :
  subrelation (sigT2_relation R) (sigT2_relation R').
Proof.
  intros x y Hxy.
  induction Hxy.
  constructor.
  now apply subrel.
Qed.