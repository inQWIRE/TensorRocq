Require Export Summable.
From stdpp Require Import vector fin.
From stdpp Require Export list.

(* A Summable instance is WF if its list of elements is
  duplicate-free (hence a delta-tensor can be defined using
  an equality test) *)
Class WFSummable (A : Type) `{Summable A} := mk_WF_sum {
  NoDup_sum_elements : NoDup (sum_elements :> list A)
}.

#[global] Arguments mk_WF_sum {_ _} _ : assert.

#[export] Instance SummableWF_fin {n} : WFSummable (fin n) :=
  mk_WF_sum (fin_elements_NoDup n).


#[export] Program Instance SummableWF_vec `{WFSummable A} {n} :
  WFSummable (vec A n) :=
  mk_WF_sum (vec_elements_NoDup _ n NoDup_sum_elements).

#[export] Program Instance SummableWF_bool : WFSummable bool.
Next Obligation.
  cbn.
  compute_done.
Qed.

(* FIXME: Move *)
Lemma NoDup_list_prod {A B} (l : list A) (l' : list B) :
  NoDup l -> NoDup l' -> NoDup (list_prod l l').
Proof.
  intros Hl Hl'.
  induction Hl; [constructor|].
  cbn.
  apply NoDup_app.
  split_and!.
  - now apply (NoDup_fmap _).
  - intros (a, b) (? & [= <- <-] & Hb)%elem_of_list_fmap.
    rewrite <- list_cprod_list_prod.
    rewrite elem_of_list_cprod.
    cbn; tauto.
  - easy.
Qed.

#[export] Program Instance SummableWF_prod `{WFSummable A, WFSummable B}
  : WFSummable (A * B).
Next Obligation.
  intros A SA [HA] B SB [HB].
  cbn.
  now apply NoDup_list_prod.
Qed.

#[export] Program Instance SummableWF_sum `{WFSummable A, WFSummable B}
  : WFSummable (A + B).
Next Obligation.
  intros A SA [HA] B SB [HB].
  cbn.
  apply NoDup_app; split_and!; cycle 1; [|now apply (NoDup_fmap _)..].
  intros ? ?%elem_of_list_fmap ?%elem_of_list_fmap.
  firstorder congruence.
Qed.

Class SummedElement `{Summable A} (a : A) : Prop := {
  element_summed : a ∈ sum_elements
}.

#[export] Program Instance SummedElement_fin {n} (i : fin n) :
  SummedElement i.
Next Obligation.
  intros.
  apply elem_of_list_In, fin_elements_in.
Qed.

#[export] Program Instance SummedElement_bool (b : bool) :
  SummedElement b.
Next Obligation.
  intros []; cbn; compute_done.
Qed.

(* FIXME: Move *)
Lemma vec_to_list_to_list {A n} (v : vec A n) :
  vec_to_list v = Vector.to_list v.
Proof.
  induction v; cbn; f_equal; easy.
Qed.

#[export] Program Instance SummedElement_vec `{Summable A}
  {n} (v : vec A n) (Hv : forall a, a ∈ vec_to_list v -> SummedElement a) :
  SummedElement v.
Next Obligation.
  intros A SA n v Hv.
  apply elem_of_list_In, vec_elements_in.
  rewrite Vector.to_list_Forall, Forall_forall.
  intros a Ha.
  rewrite <- vec_to_list_to_list in Ha.
  now apply elem_of_list_In, Hv.
Qed.

#[export] Program Instance SummedElement_sum_l `{Summable A, Summable B}
  (a : A) `{Ha : !SummedElement a} :
  SummedElement (@inl A B a).
Next Obligation.
  intros A SA B SB a [Ha].
  cbn.
  apply elem_of_app; left.
  now apply elem_of_list_fmap_1.
Qed.

#[export] Program Instance SummedElement_sum_r `{Summable A, Summable B}
  (b : B) `{Ha : !SummedElement b} :
  SummedElement (@inr A B b).
Next Obligation.
  intros A SA B SB b [Hb].
  cbn.
  apply elem_of_app; right.
  now apply elem_of_list_fmap_1.
Qed.

#[export] Program Instance SummedElement_prod `{Summable A, Summable B}
  (ab : A * B) `{Ha : !SummedElement ab.1, Hb : !SummedElement ab.2} :
  SummedElement ab.
Next Obligation.
  intros A SA B SB a [Ha] [Hb].
  cbn.
  rewrite <- list_cprod_list_prod.
  now apply elem_of_list_cprod.
Qed.


Section SummableWF_theory.

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

Lemma SummedElement_iff `{Summable A} (a : A) : SummedElement a <-> a ∈ sum_elements.
Proof.
  now split; [intros []|constructor].
Qed.

Lemma sum_of_unique' `{HA : WFSummable A} (f : A -> R) (a : A) `{Ha : !SummedElement a} :
  (forall b, SummedElement b -> a <> b -> f b == 0) ->
  ∑ b : A, f b == f a.
Proof.
  destruct HA as [HA].
  revert HA Ha.
  setoid_rewrite SummedElement_iff.
  unfold_sum_of.
  gen_sum_elem l.
  intros Hl Ha Hf.
  induction Hl as [|b l IHl]; [easy|].
  apply elem_of_cons in Ha as [<- | Ha].
  - cbn.
    rewrite Rlist_sum_zeros; [apply radd_0_r|].
    rewrite Forall_fmap, Forall_forall.
    cbn.
    intros b Hb.
    apply Hf; [now constructor|congruence].
  - cbn.
    rewrite Hf, radd_0_l by now constructor || congruence.
    apply IHHl; [easy|].
    intros ? ?; apply Hf; now constructor.
Qed.


End SummableWF_theory.