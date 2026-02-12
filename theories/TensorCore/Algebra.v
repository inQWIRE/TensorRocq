(* We make variables generalizable so that the unbundled
  definition of SemiRing is usable as
  [`{SR : SemiRing R rO rI radd rmul req}].
  Additionally, it is not practical to declare only these
  variables generalizable, as this causes an error when
  all variables are later declared generalizable (such as
  in stdpp). *)
#[global]
Generalizable All Variables.

Require Export Aux.
Require Ring_theory.
Require Integral_domain.
Require List.
Require SetoidList.
Require SetoidPermutation.
Require Import Ring.
Import Morphisms Setoid.


(** A semiring is a structure with associative and commutative
  addition and multiplication, which are also distributive. It
  has no guarantee of additive or multiplicative inverses.

  Implementation note: We have the operations as parameters
  rather than projections to make automation and rewriting
  hopefully more robust. We may in future provide a bundled
  version. *)
Class SemiRing (R : Type) (rO : R) (rI : R)
  (radd : R -> R -> R) (rmul : R -> R -> R)
  (req : R -> R -> Prop) := {
  RSRth : Ring_theory.semi_ring_theory rO rI radd rmul req;
  Req_ext : Ring_theory.sring_eq_ext radd rmul req;
  Req_equiv : Setoid.Setoid_Theory R req;
}.
Global Hint Mode SemiRing + - - - - - : typeclass_instances.

(* The development is parametric over domain, which we require to be
  a semiring. *)
Section SemiRing.

Context `{SR : SemiRing R rO rI radd rmul req}.

(* The following commands work only within the section, as outside there
 is no definition for R, rO, rI, etc. As such, they should be used at the
 start of any section developing theory over semirings. *)

Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.


(* Include the basic facts about semirings, for convenience *)
Import Ring_theory.

Lemma radd_0_l r : 0 + r == r.
Proof. apply RSRth. Qed.

Lemma radd_comm r s : r + s == s + r.
Proof. apply RSRth. Qed.

Lemma radd_assoc r s t : r + (s + t) == (r + s) + t.
Proof. apply RSRth. Qed.

Lemma radd_0_r r : r + 0 == r.
Proof. rewrite radd_comm; apply radd_0_l. Qed.

Lemma rmul_1_l r : 1 * r == r.
Proof. apply RSRth. Qed.

Lemma rmul_0_l r : 0 * r == 0.
Proof. apply RSRth. Qed.

Lemma rmul_comm r s : r * s == s * r.
Proof. apply RSRth. Qed.

Lemma rmul_assoc r s t : r * (s * t) == (r * s) * t.
Proof. apply RSRth. Qed.

Lemma distr_l r s t : (r + s) * t == r * t + s * t.
Proof. apply RSRth. Qed.

Lemma rmul_1_r r : r * 1 == r.
Proof. rewrite rmul_comm. apply RSRth. Qed.

Lemma rmul_0_r r : r * 0 == 0.
Proof. rewrite rmul_comm. apply RSRth. Qed.

Lemma distr_r r s t : r * (s + t) == r * s + r * t.
Proof. rewrite 3(rmul_comm r). apply distr_l. Qed.

Lemma rmul_comm_double (r0 r1 r2 r3 : R) :
  (r0 * r1) * (r2 * r3) == (r0 * r2) * (r1 * r3).
Proof.
  ring.
Qed.

End SemiRing.

Import List ListNotations Permutation SetoidPermutation.

Fixpoint Rlist_sum `{SR : SemiRing R rO rI radd rmul req} (l : list R) : R :=
  match l with
  | [] => rO
  | r :: l => radd r (Rlist_sum l)
  end.

Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req} :
  Rlist_sum with signature PermutationA req ==> req as Rlist_sum_perm_mor.
Proof.
  set (HR := Req_equiv : Equivalence req).
  set (HRadd := SR.(Req_ext).(SRadd_ext)).
  intros l l' Hl.
  induction Hl; cbn.
  - reflexivity.
  - now f_equiv.
  - now rewrite 2 radd_assoc, (radd_comm y).
  - etransitivity; eauto.
Qed.

Fixpoint Rlist_prod `{SR : SemiRing R rO rI radd rmul req} (l : list R) : R :=
  match l with
  | [] => rI
  | r :: l => rmul r (Rlist_prod l)
  end.

Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req} :
  Rlist_prod with signature PermutationA req ==> req as Rlist_prod_perm_mor.
Proof.
  set (HR := Req_equiv : Equivalence req).
  set (HRmul := SR.(Req_ext).(SRmul_ext)).
  intros l l' Hl.
  induction Hl; cbn.
  - reflexivity.
  - now f_equiv.
  - now rewrite 2 rmul_assoc, (rmul_comm y).
  - etransitivity; eauto.
Qed.



Section Rlist_sum.

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



Lemma Rlist_sum_fold_right l :
  Rlist_sum l = fold_right radd rO l.
Proof.
  induction l; cbn; congruence.
Qed.

Lemma Rlist_sum_nil : Rlist_sum [] = 0.
Proof.
  reflexivity.
Qed.

Lemma Rlist_sum_cons a l :
  Rlist_sum (a :: l) = a + Rlist_sum l.
Proof.
  reflexivity.
Qed.

Lemma Rlist_sum_app l l' :
  Rlist_sum (l ++ l') == Rlist_sum l + Rlist_sum l'.
Proof.
  induction l as [|r l IHl]; cbn; [ring|ring [IHl]].
Qed.

Lemma Rlist_sum_concat ls :
  Rlist_sum (concat ls) == Rlist_sum (map Rlist_sum ls).
Proof.
  induction ls; [reflexivity|cbn].
  now rewrite Rlist_sum_app, IHls.
Qed.

Lemma Rlist_sum_ext (rs rs' : list R) :
  Forall2 req rs rs' -> Rlist_sum rs == Rlist_sum rs'.
Proof.
  intros ?%SetoidList.eqlistA_altdef%SetoidPermutation.eqlistA_PermutationA.
  now apply Rlist_sum_perm_mor.
Qed.

(* FIXME: make Morphism *)
Lemma Rlist_sum_perm rs rs' : Permutation rs rs' -> Rlist_sum rs == Rlist_sum rs'.
Proof.
  intros Hperm.
  apply Rlist_sum_perm_mor.
  now apply SetoidPermutation.Permutation_PermutationA.
Qed.

Lemma Rlist_sum_zeros (rs : list R) :
  Forall (fun r => r == rO) rs ->
  Rlist_sum rs == 0.
Proof.
  intros Hrs.
  induction Hrs; [easy|].
  cbn.
  rewrite IHHrs, radd_0_r.
  easy.
Qed.

End Rlist_sum.


Section Rlist_prod.

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



Lemma Rlist_prod_fold_right l :
  Rlist_prod l = fold_right rmul rI l.
Proof.
  induction l; cbn; congruence.
Qed.

Lemma Rlist_prod_nil : Rlist_prod [] = 1.
Proof.
  reflexivity.
Qed.

Lemma Rlist_prod_cons a l :
  Rlist_prod (a :: l) = a * Rlist_prod l.
Proof.
  reflexivity.
Qed.

Lemma Rlist_prod_app l l' :
  Rlist_prod (l ++ l') == Rlist_prod l * Rlist_prod l'.
Proof.
  induction l as [|r l IHl]; cbn; [ring|ring [IHl]].
Qed.

Lemma Rlist_prod_concat ls :
  Rlist_prod (concat ls) == Rlist_prod (map Rlist_prod ls).
Proof.
  induction ls; [reflexivity|cbn].
  now rewrite Rlist_prod_app, IHls.
Qed.

Lemma Rlist_prod_ext (rs rs' : list R) :
  Forall2 req rs rs' -> Rlist_prod rs == Rlist_prod rs'.
Proof.
  intros ?%SetoidList.eqlistA_altdef%SetoidPermutation.eqlistA_PermutationA.
  now apply Rlist_prod_perm_mor.
Qed.

(* FIXME: make Morphism *)
Lemma Rlist_prod_perm rs rs' : Permutation rs rs' -> Rlist_prod rs == Rlist_prod rs'.
Proof.
  intros Hperm.
  apply Rlist_prod_perm_mor.
  now apply SetoidPermutation.Permutation_PermutationA.
Qed.

Lemma Rlist_prod_ones (rs : list R) :
  Forall (fun r => r == 1) rs ->
  Rlist_prod rs == 1.
Proof.
  intros Hrs.
  induction Hrs; [easy|].
  cbn.
  now rewrite IHHrs, rmul_1_r.
Qed.

End Rlist_prod.