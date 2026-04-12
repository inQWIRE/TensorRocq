Require Import SetoidList.
From TensorRocq Require Import Algebra.Definitions.
From stdpp Require Import base list.

Class Monoid (M : Type) (mO : M) (madd : M -> M -> M) (meq : relation M) := {
  meq_equivalence : Equivalence meq;
  madd_proper : Proper (meq ==> meq ==> meq) madd;
  madd_assoc : forall x y z, meq (madd x (madd y z)) (madd (madd x y) z);
  madd_0_l : forall x, meq (madd mO x) x;
  madd_0_r : forall x, meq (madd x mO) x;
}.

#[global] Hint Mode Monoid + - - - : typeclass_instances.

#[export] Instance Monoid_nat : Monoid nat 0 Nat.add eq.
Proof.
  split; first [typeclasses eauto|intros; lia].
Qed.

Fixpoint Mlist_sum `{MD : Monoid M mO madd meq} (l : list M) :=
  match l with
  | [] => mO
  | a :: l => madd a (Mlist_sum l)
  end.

Fixpoint Mlist_sum' `{MD : Monoid M mO madd meq} (l : list M) : M :=
  match l with 
  | [] => mO
  | [x] => x
  | x :: l => madd x (Mlist_sum' l)
  end.


Section Monoid.

Context `{MD : Monoid M mO madd meq}.

Notation "0" := mO.
Notation "x '==' y" := (meq x y) (at level 70).
Infix "+" := madd.


(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Meq_equivalence : Equivalence meq := meq_equivalence.
Local Existing Instance Meq_equivalence.

Let Madd_proper : Proper (meq ==> meq ==> meq) madd := madd_proper.
Local Existing Instance Madd_proper.

#[export] Instance Mlist_sum_perm_mor : Proper (eqlistA meq ==> meq) Mlist_sum.
Proof.
  intros l l' Hl.
  induction Hl.
  - done.
  - cbn.
    now f_equiv.
Qed.

Lemma Mlist_sum_app (l l' : list M) :
  Mlist_sum (l ++ l') == Mlist_sum l + Mlist_sum l'.
Proof.
  induction l; [cbn; now rewrite madd_0_l|].
  cbn.
  rewrite IHl.
  now rewrite madd_assoc.
Qed.

Lemma Mlist_sum'_correct (l : list M) : 
  meq (Mlist_sum' l) (Mlist_sum l).
Proof.
  induction l; [done|].
  destruct l; [|cbn; f_equiv; apply IHl].
  cbn.
  now rewrite madd_0_r.
Qed.

End Monoid.


Class MonoidSize `{MD : Monoid M mO madd meq} (f : M -> nat) := {
  msize := f;
  msize_proper : Proper (meq ==> eq) f;
  msize_mO : f mO = 0;
  msize_add x y : f (madd x y) = f x + f y;
}.

#[global] Hint Mode MonoidSize + - - - - - : typeclass_instances.

#[export] Instance nat_MonoidSize : MonoidSize id.
Proof.
  split; [apply _|done..].
Qed.

(* A class expressing that M is the free (non-commutative)
  monoid over some set X of generators *)
Class FreeMonoid (M : Type) `{MD : Monoid M mO madd meq} (X : Type) := {
  mdecomp : M -> list X;
  mdecomp_inv : X -> M;
  mdecomp_proper :: Proper (meq ==> eq) mdecomp;
  mdecomp_inj :: Inj meq eq mdecomp;
  mdecomp_madd m n : mdecomp (madd m n) = mdecomp m ++ mdecomp n;
  mdecomp_rinv : forall x, mdecomp (mdecomp_inv x) = [x];
}.

#[global] Hint Mode FreeMonoid ! - - - - - : typeclass_instances.

Lemma mdecomp_mO `{FreeMonoid M mO madd meq X} :
  mdecomp mO = [].
Proof.
  specialize (mdecomp_proper (madd mO mO) mO (madd_0_l mO)).
  rewrite mdecomp_madd.
  intros Hlen%(f_equal length).
  apply length_zero_iff_nil.
  rewrite length_app in Hlen.
  lia.
Qed.

#[refine] Instance nat_FreeMonoid : FreeMonoid nat unit := {
  mdecomp n := replicate n ();
  mdecomp_inv _ := 1;
}.
Proof.
  - abstract (intros n m Heq%(f_equal length);
    now rewrite 2 length_replicate in Heq).
  - abstract (intros n m;
    now rewrite replicate_add).
  - abstract (intros (); reflexivity).
Defined.
