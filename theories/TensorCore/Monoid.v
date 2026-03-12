Require Import SetoidList Algebra.
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
