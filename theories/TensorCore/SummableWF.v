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
