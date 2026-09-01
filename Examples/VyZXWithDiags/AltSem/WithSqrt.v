From TensorRocq Require Import Aux.
Require Ring_theory.
Require Integral_domain.
Require List.
Require SetoidList.
Require SetoidPermutation.
Require Import Ring.
Import Morphisms Setoid.

Module Field.
(* We make variables generalizable so that the unbundled
  definition of SemiRing is usable as
  [`{SR : SemiRing R rO rI radd rmul req}].
  Additionally, it is not practical to declare only these
  variables generalizable, as this causes an error when
  all variables are later declared generalizable (such as
  in stdpp). *)
#[global]
Generalizable All Variables.

From TensorRocq Require Import Aux.
Require Ring_theory.
Require Integral_domain.
Require List.
Require SetoidList.
Require SetoidPermutation.
Require Import Ring.
Import Morphisms Setoid.
Import Field_theory.
Export setoid_ring.Field.


Class Field (R : Type) (rO : R) (rI : R)
  (radd : R -> R -> R) (rmul : R -> R -> R)
  (rsub : R -> R -> R) (ropp : R -> R)
  (rdiv : R -> R -> R) (rinv : R -> R)
  (req : R -> R -> Prop) := {
  Fth : Field_theory.field_theory rO rI radd rmul rsub ropp rdiv rinv req;
  Feq_ext : ring_eq_ext radd rmul ropp req;
  Finv_ext : Proper (req ==> req) rinv;
  Feq_equiv : Equivalence req;
  Finv_0 : req (rinv rO) rO;
  Feq_classical : forall r s, req r s \/ ~ req r s;
  FAFth : almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req :=
    F2AF Feq_equiv Feq_ext Fth;
  Fadd_proper : Proper (req ==> req ==> req) radd := Feq_ext.(Radd_ext);
  Fmul_proper : Proper (req ==> req ==> req) rmul := Feq_ext.(Rmul_ext);
  Fsub_proper : Proper (req ==> req ==> req) rsub := rsub_ext_Proper Feq_equiv Feq_ext FAFth;
  Fopp_proper : Proper (req ==> req) ropp := Feq_ext.(Ropp_ext);
  Finv_proper : Proper (req ==> req) rinv := Finv_ext;
  Fdiv_proper : Proper (req ==> req ==> req) rdiv := rdiv_ext Feq_equiv Feq_ext Finv_ext FAFth;
}.

Global Hint Mode Field ! - - - - - - - - - : typeclass_instances.

Section Field.

Context `{FTH : Field R rO rI radd rmul rsub ropp rdiv rinv req}.


Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "-" := rsub.
Infix "*" := rmul.
Infix "/" := rdiv.
Notation "- x" := (ropp x).
Notation "/ x" := (rinv x).

Let Feq_equiv : Equivalence req := FTH.(Feq_equiv).

Local Existing Instance Feq_equiv.

Let Fadd_proper := FTH.(Fadd_proper).
Local Existing Instance Fadd_proper.
Let Fmul_proper := FTH.(Fmul_proper).
Local Existing Instance Fmul_proper.
Let Fsub_proper := FTH.(Fsub_proper).
Local Existing Instance Fsub_proper.
Let Fopp_proper := FTH.(Fopp_proper).
Local Existing Instance Fopp_proper.
Let Fdiv_proper := FTH.(Fdiv_proper).
Local Existing Instance Fdiv_proper.
Let Finv_proper := FTH.(Finv_proper).
Local Existing Instance Finv_proper.

Add Field Ffield : FTH.(Fth).

Lemma Fadd_0_l r : 0 + r == r.
Proof. ring. Qed.

Lemma Fadd_0_r r : r + 0 == r.
Proof. ring. Qed.

Lemma Fmul_0_l r : 0 * r == 0.
Proof. ring. Qed.

Lemma Fmul_0_r r : r * 0 == 0.
Proof. ring. Qed.

Lemma Fmul_1_l r : 1 * r == r.
Proof. ring. Qed.

Lemma Fmul_1_r r : r * 1 == r.
Proof. ring. Qed.

Lemma F_1_neq_0 : ~ (1 == 0).
Proof. apply FTH.(Fth).(F_1_neq_0). Qed.

Lemma F_0_neq_1 : ~ (0 == 1).
Proof. now intros []%symmetry%F_1_neq_0. Qed.

Lemma Finv_l r : ~ (r == 0) -> / r * r == 1.
Proof. apply FTH.(Fth).(Finv_l). Qed.

Lemma Finv_r r : ~ (r == 0) -> r * / r == 1.
Proof. intros; field; easy. Qed.

Lemma Fdiv_def r s : r / s == r * / s.
Proof.
  apply FTH.(Fth).(Fdiv_def).
Qed.

Lemma Fsub_eq_l r s t : r - s == t <-> r == s + t.
Proof.
  split; intros Hr; [|ring [Hr]].
  rewrite <- Hr.
  ring.
Qed.

Lemma Fsub_eq_0_l r s : r - s == 0 <-> r == s.
Proof.
  rewrite Fsub_eq_l; split; intros ->; ring.
Qed.

Lemma Fadd_eq_l r s t : r + s == t <-> r == t - s.
Proof.
  split; [intros <-|intros ->]; ring.
Qed.

Lemma Fadd_eq_0_l r s : r + s == 0 <-> r == - s.
Proof.
  rewrite Fadd_eq_l.
  split; intros ->; ring.
Qed.

Lemma Fdiv_1_l r : 1 / r == / r.
Proof. rewrite Fdiv_def; ring. Qed.

Lemma Fdiv_1_r r : r / 1 == r.
Proof. symmetry; apply (rdiv1 _ FTH.(Feq_ext) FTH.(FAFth)). Qed.


Lemma Finv_invol r : / / r == r.
Proof.
  destruct (Feq_classical r 0) as [Hr|Hr]; [now rewrite Hr, 2 Finv_0|].
  field; split; auto using F_1_neq_0.
Qed.

Lemma Finv_inj r s : / r == / s <-> r == s.
Proof.
  split; [|now intros ->].
  intros Hrs.
  rewrite <- (Finv_invol r), Hrs, Finv_invol.
  easy.
Qed.

Lemma Fopp_invol r : - - r == r.
Proof.
  ring.
Qed.

Lemma Fopp_inj r s : - r == - s <-> r == s.
Proof.
  split; [|now intros ->].
  intros Hrs.
  rewrite <- (Fopp_invol r), Hrs, Fopp_invol.
  easy.
Qed.


End Field.

End Field.


From TensorRocq Require Import Aux_stdpp.


(* From TensorRocqEx *) Import Field.


Inductive WithSqrt {R} {d : R} :=
  mk_WithSqrt (a b : R).

#[global] Arguments WithSqrt {_} _ : assert.

Section WSField.

Context `{FTH : Field R rO rI radd rmul rsub ropp rdiv rinv req}.


Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "-" := rsub.
Infix "*" := rmul.
Infix "/" := rdiv.
Notation "- x" := (ropp x).
Notation "/ x" := (rinv x).

Let Feq_equiv : Equivalence req := FTH.(Feq_equiv).

Local Existing Instance Feq_equiv.

Let Fadd_proper := FTH.(Fadd_proper).
Local Existing Instance Fadd_proper.
Let Fmul_proper := FTH.(Fmul_proper).
Local Existing Instance Fmul_proper.
Let Fsub_proper := FTH.(Fsub_proper).
Local Existing Instance Fsub_proper.
Let Fopp_proper := FTH.(Fopp_proper).
Local Existing Instance Fopp_proper.
Let Fdiv_proper := FTH.(Fdiv_proper).
Local Existing Instance Fdiv_proper.
Let Finv_proper := FTH.(Finv_proper).
Local Existing Instance Finv_proper.

Add Field Ffield : FTH.(Fth).



Context {d : R}.

Let WithSqrt := WithSqrt d.

Local Notation "'(' a ','  b ')'" := (@mk_WithSqrt _ _ a b).

Definition WS0 : WithSqrt := (0, 0).
Definition WS1 : WithSqrt := (1, 0).
Definition WS_sqrtd : WithSqrt := (0, 1).
Definition WSadd (x y : WithSqrt) : WithSqrt :=
  let '(a, b) := x in
  let '(a', b') := y in
  (a + a', b + b').
Definition WSmul (x y : WithSqrt) : WithSqrt :=
  let '(a, b) := x in
  let '(a', b') := y in
  (a * a' + b * b' * d, a * b' + a' * b).
Definition WSopp (x : WithSqrt) : WithSqrt :=
  let '(a, b) := x in (-a, -b).
Definition WSsub (x y : WithSqrt) :=
  WSadd x (WSopp y).
Definition WSinv (x : WithSqrt) : WithSqrt :=
  let '(a, b) := x in
  let denfact := a * a - b * b * d in
  (a / denfact, - b / denfact).
Definition WSdiv (x y : WithSqrt) : WithSqrt :=
  WSmul x (WSinv y).
Definition WSeq (x y : WithSqrt) : Prop :=
  let '(a, b) := x in
  let '(a', b') := y in
  a == a' /\ b == b'.

Declare Scope WithSqrt.
Delimit Scope WithSqrt with WS.
Bind Scope WithSqrt with WithSqrt.


Notation "0" := WS0 : WithSqrt.
Notation "1" := WS1 : WithSqrt.
Notation "x '==' y" := (WSeq x y) (at level 70) : WithSqrt.
Infix "+" := WSadd : WithSqrt.
Infix "-" := WSsub : WithSqrt.
Infix "*" := WSmul : WithSqrt.
Infix "/" := WSdiv : WithSqrt.
Notation "- x" := (WSopp x) : WithSqrt.
Notation "/ x" := (WSinv x) : WithSqrt.


#[export] Instance WSeq_equiv : Equivalence WSeq.
Proof.
  split.
  - intros []; split; reflexivity.
  - intros [] []; cbn; easy.
  - intros [] [] [] [] []; split; etransitivity; eauto.
Qed.

#[export] Instance WSadd_proper : Proper (WSeq ==> WSeq ==> WSeq) WSadd.
Proof.
  repeat intros []; split; f_equiv; easy.
Qed.

#[export] Instance WSmul_proper : Proper (WSeq ==> WSeq ==> WSeq) WSmul.
Proof.
  repeat intros []; split; repeat f_equiv; easy.
Qed.

#[export] Instance WSopp_proper : Proper (WSeq ==> WSeq) WSopp.
Proof.
  repeat intros []; split; repeat f_equiv; easy.
Qed.

#[export] Instance WSsub_proper : Proper (WSeq ==> WSeq ==> WSeq) WSsub.
Proof.
  unfold WSsub.
  solve_proper.
Qed.

#[export] Instance WSinv_proper : Proper (WSeq ==> WSeq) WSinv.
Proof.
  repeat intros []; split; repeat f_equiv; easy.
Qed.

#[export] Instance WSdiv_proper : Proper (WSeq ==> WSeq ==> WSeq) WSdiv.
Proof.
  unfold WSdiv.
  solve_proper.
Qed.


Definition WSring : ring_theory WS0 WS1 WSadd WSmul WSsub WSopp WSeq.
Proof.
  split;
  repeat intros []; split; ring.
Qed.

Lemma WSinv_l (Hd : forall r : R, ~ (r * r == d))
  (x : WithSqrt) : (~ (x == 0) -> / x * x == 1)%WS.
Proof.
  destruct x as [a b].
  cbn.
  intros Hx.
  assert (Hab : ~ a * a - b * b * d == 0). 1:{
    intros Habd.
    destruct (Feq_classical b 0) as [Hb0|Hbn0].
    + rewrite Hb0 in Habd.
      ring_simplify in Habd.
      apply Hx.
      split; [|easy].
      destruct (Feq_classical a 0) as [Ha0|Hanz]; [easy|].
      apply (f_equiv (RB:=req) (fun b => rdiv b a) (Hf:=ltac:(solve_proper))) in Habd.
      rewrite (Fdiv_def 0 a) in Habd.
      ring_simplify in Habd.
      field_simplify in Habd; easy.
    + apply (Hd (a / b)).
      transitivity ((a * a) / (b * b)); [field; easy|].
      rewrite Fsub_eq_0_l in Habd.
      rewrite Habd.
      field; easy.
  }
  split; field; easy.
Qed.


#[program]
Definition WSfield_theory (Hd : forall r : R, ~ (r * r == d)) :
  field_theory WS0 WS1 WSadd WSmul WSsub WSopp WSdiv WSinv WSeq := {|
    F_R := WSring;
  |}.
Next Obligation.
  simpl.
  intros _ [[]%F_1_neq_0 _].
Qed.
Next Obligation.
  easy.
Qed.
Next Obligation.
  apply WSinv_l.
Qed.


Lemma WS_sqrtd_not_sqrt (Hd : forall r : R, ~ (r * r == - d)) :
  forall x : WithSqrt, ~ (x * x == (rO, rI))%WS.
Proof.
  intros [a b].
  simpl.
  intros [Hab Hplus].
  assert (Ha : ~ a == 0) by (intros Ha; rewrite Ha in Hplus; 
    ring_simplify in Hplus; now apply F_0_neq_1 in Hplus).
  assert (Hb : ~ b == 0) by (intros Hb; rewrite Hb in Hplus; 
    ring_simplify in Hplus; now apply F_0_neq_1 in Hplus).
  apply (Hd (a / b)).
  transitivity ((a * a) / (b * b)); [field; easy|].
  rewrite Fadd_eq_0_l in Hab.
  rewrite Hab.
  field; easy.
Qed.

Lemma WS_neg_sqrtd_not_sqrt (Hd : forall r : R, ~ (r * r == - d)) :
  forall x : WithSqrt, ~ (x * x == (rO, ropp rI))%WS.
Proof.
  intros [a b].
  simpl.
  intros [Hab Hplus].
  assert (Ha : ~ a == 0). 1:{
    intros Ha; rewrite Ha in Hplus.
    apply Fopp_inj in Hplus.
    ring_simplify in Hplus.
    now apply F_0_neq_1 in Hplus.
  }
  assert (Hb : ~ b == 0). 1:{
    intros Hb; rewrite Hb in Hplus.
    apply Fopp_inj in Hplus.
    ring_simplify in Hplus.
    now apply F_0_neq_1 in Hplus.
  }
  apply (Hd (a / b)).
  transitivity ((a * a) / (b * b)); [field; easy|].
  rewrite Fadd_eq_0_l in Hab.
  rewrite Hab.
  field; easy.
Qed.

End WSField.

(* Lemma Q_two_not_square (r s : Q) : 

Local Lemma sqrt2_irrational' q : √ 2 <> Q2R q.
Proof.
  pose proof (sqrt2_irrational (Qnum q) (Z.pos (Qden q)) ltac:(lia)) as Hne.
  intros Heq.
  apply Hne.
  rewrite Heq.
  unfold Q2R.
  field.
  apply eq_IZR_contrapositive.
  lia.
Qed. *)


(* Fixpoint Qnth_sqrt2_aux n : {T : Type & T * T}
  match n with
  | 0 => existT Q (0%Q, 2%Q)
  | S n => 
    let '(existT T (t0, t2)) := Qnth_sqrt2_aux n in 
    existT (WithSqrt t2) (mk_WithSqrt t0 t0, mk_WithSqrt t0 t2)
  end. *)

