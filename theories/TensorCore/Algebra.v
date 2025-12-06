Require Export Aux.
Require Ring_theory.
Require Integral_domain.
Require List.
Require Permutation.
Require SetoidList.
Require Import Ring.
Import Morphisms Setoid.

(* We make these variables generalizable so that the unbundled 
  definition of SemiRing is usable as 
  [`{SR : SemiRing R rO rI radd rmul req}]*)
#[global]
Generalizable Variables R rO rI radd rmul req.

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

End SemiRing.
