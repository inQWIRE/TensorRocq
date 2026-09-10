From TensorRocq Require Import Aux Aux_stdpp Summable.Definitions Summable.Instances Algebra.
From stdpp Require Import vector fin fin_maps.
From stdpp Require Export list.

Class WFSummableOver (R A : Type)
  `{SR : SemiRing R rO rI radd rmul req}
  `{SRA : SummableOver R A, !LawfulSummableOver R A} := mk_WF_sum_over {
  sum_of_unique (f : A -> R) r
    (Hf : exists a, SummedElement a /\ req (f a) r /\ forall b, SummedElement b -> b <> a -> req (f b) rO) :
    req (sum_of f) r
}.

#[global] Arguments mk_WF_sum_over {_ _ _ _ _ _ _ _ _ _} _ : assert.


(* A Summable instance is WF if its list of elements is
  duplicate-free (hence a delta-tensor can be defined using
  an equality test) *)
Class WFSummable (A : Type) `{Summable A} := mk_WF_sum {
  NoDup_sum_elements : NoDup (sum_elements :> list A)
}.

#[global] Arguments mk_WF_sum {_ _} _ : assert.


Section summable.

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

#[global] Instance WFSummable_WFSummableOver (A : Type) `{Summable A}
  {WFA : WFSummable A} :
  WFSummableOver R A.
Proof.
  split.
  intros f r (a & Ha & Hfa & Hf).
  unfold SummedElement in Ha, Hf.
  cbn in Ha, Hf.
  destruct WFA as [WFA].
  revert WFA.
  unfold_sum_of.
  revert Ha Hf.
  gen_sum_elem l.
  intros Ha Hf Hl.
  induction Ha; apply NoDup_cons in Hl as [Hx Hl].
  - cbn.
    rewrite Hfa.
    rewrite Rlist_sum_zeros; [ring|].
    rewrite Forall_fmap, Forall_forall.
    intros b Hb.
    apply Hf; set_solver + Hb Hx.
  - cbn.
    rewrite Hf by now constructor || congruence.
    rewrite IHHa; [ring|..];
    auto using elem_of_list.
Qed.

End summable.

#[export] Instance SummableWF_fin {n} : WFSummable (fin n) :=
  mk_WF_sum (fin_elements_NoDup n).


#[export] Instance WFSummableOver_prop A {EqA : EqDecision A} :
  WFSummableOver Prop A.
Proof.
  split.
  unfold SummedElement.
  cbn.
  intros f r (a & _ & Hfa & Hf).
  rewrite sum_of_defn_abstract'; cbn.
  split; [|intros ?%Hfa; eauto].
  intros (b & Hb).
  destruct_decide (decide (b = a)); [now subst; firstorder|].
  firstorder.
Qed.

#[export] Instance SummedElement_prop {A} (a : A) : 
  SummedElement a.
Proof.
  done.
Qed.



Section summable.

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

#[export] Instance WFSummableOver_vec `{SummableOver R A}
  `{!LawfulSummableOver R A, !WFSummableOver R A} {n} :
  WFSummableOver R (vec A n).
Proof.
  split.
  intros f r (v & Hv & Hfv & Hf).
  unfold SummedElement in Hv, Hf.
  cbn in Hv, Hf.
  induction v; [done|].
  rewrite sum_of_vec_succ.
  apply sum_of_unique.
  exists h.
  cbn in Hv.
  apply Forall_cons in Hv as [Hh Hv].
  split_and!.
  - done.
  - apply IHv.
    + done.
    + done.
    + intros; apply Hf; [now constructor|].
      now intros ?%vcons_inj.
  - intros b Hb Hbh.
    apply sum_of_0'.
    intros w Hw.
    apply Hf; [now constructor|].
    now intros ?%vcons_inj.
Qed.


#[export] Program Instance SummableWF_bool : WFSummable bool.
Next Obligation.
  cbn.
  compute_done.
Qed.

#[export] Program Instance SummableWF_prod `{WFSummable A, WFSummable B}
  : @WFSummable (A * B) Summable_prod.
Next Obligation.
  intros A SA [HA] B SB [HB].
  cbn.
  now apply NoDup_list_prod.
Qed.

#[export] Program Instance SummableWF_sum `{WFSummable A, WFSummable B}
  : @WFSummable (A + B) Summable_sum.
Next Obligation.
  intros A SA [HA] B SB [HB].
  cbn.
  apply NoDup_app; split_and!; cycle 1; [|now apply (NoDup_fmap _)..].
  intros ? ?%elem_of_list_fmap ?%elem_of_list_fmap.
  firstorder congruence.
Qed.


Local Notation SummedElement := (SummedElement (R:=R)).

Lemma SummedElement_iff `{Summable A} (a : A) : SummedElement a <-> a ∈ sum_elements.
Proof.
  done.
Qed.

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

End summable.

#[export] Program Instance SummedElement_vec `{SummableOver R A}
  {n} (v : vec A n) (Hv : forall a, a ∈ vec_to_list v -> SummedElement a) :
  SummedElement v.
Next Obligation.
  intros A SA n v Hv.
  cbn.
  rewrite Forall_forall; done.
Qed.

#[export] Instance SummedElement_vcons `{SummableOver R A} (a : A) {n} (v : vec A n) :
  SummedElement a -> SummedElement v -> SummedElement (a ::: v).
Proof.
  now intros; constructor.
Qed.

#[export] Instance SummedElement_vnil `{SummableOver R A} :
  SummedElement ([#] :> vec A 0).
Proof.
  now apply SummedElement_vec.
Qed.



#[export] Program Instance SummedElement_sum_l
  `{SR : SemiRing R rO rI radd rmul req}
  `{SummableOver R A, SummableOver R B}
  (a : A) `{Ha : !SummedElement a} :
  SummedElement (R:=R) (@inl A B a).
Next Obligation.
  done.
Qed.

#[export] Program Instance SummedElement_sum_r
  `{SR : SemiRing R rO rI radd rmul req}
  `{SummableOver R A, SummableOver R B}
  (b : B) `{Ha : !SummedElement b} :
  SummedElement (R:=R) (@inr A B b).
Next Obligation.
  done.
Qed.

#[export] Program Instance SummedElement_prod `{SummableOver R A, SummableOver R B}
  (ab : A * B) `{Ha : !SummedElement ab.1, Hb : !SummedElement ab.2} :
  SummedElement ab.
Next Obligation.
  done.
Qed.


Lemma SummedElement_vec_iff `{SummableOver R A} {n} (v : vec A n) :
  SummedElement v <-> (forall a, a ∈@{list _} v -> SummedElement a).
Proof.
  apply Forall_forall.
Qed.

Lemma SummedElement_vec_app_iff `{SummableOver R A} {n m} (v : vec A n) (w : vec A m) :
  SummedElement (v +++ w) <-> SummedElement v /\ SummedElement w.
Proof.
  rewrite 3 SummedElement_vec_iff.
  setoid_rewrite elem_of_list_In.
  rewrite vec_to_list_app.
  setoid_rewrite in_app_iff.
  naive_solver.
Qed.

Lemma SummedElement_vec_iff_Forall `{SummableOver R A} {n} (v : vec A n) :
  SummedElement v <-> Forall SummedElement v.
Proof.
  done.
Qed.
#[export] Instance SummedElement_vsplitl `{SummableOver R A} {n m} (v : vec A (n + m)) :
  SummedElement v -> SummedElement (vsplitl v).
Proof.
  rewrite 2 SummedElement_vec_iff_Forall.
  rewrite <- (app_vsplit v), vec_to_list_app, Forall_app at 1.
  easy.
Qed.
#[export] Instance SummedElement_vsplitr `{SummableOver R A} {n m} (v : vec A (n + m)) :
  SummedElement v -> SummedElement (vsplitr v).
Proof.
  rewrite 2 SummedElement_vec_iff_Forall.
  rewrite <- (app_vsplit v), vec_to_list_app, Forall_app at 1.
  easy.
Qed.
#[export] Instance SummedElement_vec_app `{SummableOver R A} {n m}
  (v : vec A n) (w : vec A m) :
  SummedElement v -> SummedElement w -> SummedElement (v +++ w).
Proof.
  rewrite SummedElement_vec_app_iff.
  auto.
Qed.

Lemma make_vecs_map_SummedElements `{SA : SummableOver R A} {n m}
  (ins : vec _ n) (outs : vec _ m) (v w : vec A _) :
  SummedElement v -> SummedElement w ->
  map_Forall (λ _ a, SummedElement a)
  (make_vecs_map ins outs v w).
Proof.
  intros Hv Hw.
  unfold make_vecs_map.
  rewrite <- list_to_map_app.
  intros i a Hia%elem_of_list_to_map_2%(elem_of_list_fmap_1 snd).
  cbn in Hia.
  rewrite fmap_app, 2 vec_to_list_zip_with,
    2 snd_zip in Hia by now rewrite 2 length_vec_to_list.
  rewrite SummedElement_vec_iff in Hw.
  rewrite SummedElement_vec_iff in Hv.
  apply elem_of_app in Hia as []; auto.
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

Lemma sum_of_unique' `{SRA : SummableOver R A,
  LSRA : !LawfulSummableOver R A,
  WFA : !WFSummableOver R A} (f : A -> R) (a : A) `{Ha : !SummedElement a} :
  (forall b, SummedElement b -> a <> b -> f b == 0) ->
  ∑ b : A, f b == f a.
Proof.
  intros Hb.
  apply sum_of_unique.
  exists a.
  split_and!; done || auto.
Qed.


End SummableWF_theory.