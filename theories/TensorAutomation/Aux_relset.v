From stdpp Require Import relations sets.
Require Aux_pos. (* Hack to make universes work *)

#[export] Instance relation_elem_of {A B} : ElemOf (A * B) (A -> B -> Prop) :=
  fun ab R => R ab.1 ab.2.
#[export] Instance relation_empty {A B} : Empty (A -> B -> Prop) :=
  fun a b => False.
#[export] Instance relation_top {A B} : Top (A -> B -> Prop) :=
  fun a b => True.
#[export] Instance relation_singleton {A B} : Singleton (A * B) (A -> B -> Prop) :=
  fun ab => fun a b => (a, b) = ab.
#[export] Instance relation_union {A B} : Union (A -> B -> Prop) :=
  fun R R' => fun a b => R a b \/ R' a b.
#[export] Instance relation_intersection {A B} : Intersection (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ R' a b.
#[export] Instance relation_difference {A B} : Difference (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ ~ R' a b.

#[global] Arguments relation_elem_of {_ _} _ _ / : assert.
#[global] Arguments relation_empty {_ _} _ _ / : assert.
#[global] Arguments relation_top {_ _} _ _ / : assert.
#[global] Arguments relation_singleton {_ _} _ _ _ / : assert.
#[global] Arguments relation_union {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_intersection {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_difference {_ _} _ _ _ _ / : assert.




#[export] Program Instance relation_semi_set {A} : SemiSet (A * A) (relation A).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_set {A} : Set_ (A * A) (relation A).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_top_set {A} : TopSet (A * A) (relation A).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Instance rel_empty_symm {A} : @Symmetric A ∅.
Proof. easy. Qed.

#[export] Instance rel_empty_trans {A} : @Transitive A ∅.
Proof. easy. Qed.

#[export] Instance rel_top_equiv {A} : @Equivalence A ⊤.
Proof. easy. Qed.

Add Parametric Morphism {A} : elem_of with signature
  eq ==> (≡@{relation A}) ==> iff as rel_elem_of_equiv.
Proof.
  firstorder.
Qed.


Add Parametric Morphism {A} : elem_of with signature
  eq ==> (⊆@{relation A}) ==> impl as rel_elem_of_subseteq.
Proof.
  firstorder.
Qed.

Add Parametric Morphism {A} : subseteq with signature
  (⊆@{relation A}) --> (⊆@{relation A}) ==> impl as rel_subseteq_proper_subseteq.
Proof.
  firstorder.
Qed.

Add Parametric Morphism {A} : subseteq with signature
  (≡@{relation A}) ==> (≡@{relation A}) ==> iff as rel_subseteq_proper_equiv.
Proof.
  firstorder.
Qed.

Add Parametric Relation {A} : (relation A) equiv
  reflexivity proved by ltac:(hnf; firstorder)
  symmetry proved by ltac:(hnf; firstorder)
  transitivity proved by ltac:(hnf; firstorder)
  as relation_equivalence.

Add Parametric Relation {A} : (relation A) subseteq
  reflexivity proved by ltac:(hnf; firstorder)
  transitivity proved by ltac:(hnf; firstorder)
  as relation_subseteq_equiv.


#[export] Instance rel_union_refl {A} {R R' : relation A} :
  TCOr (Reflexive R) (Reflexive R') -> Reflexive (R ∪ R').
Proof.
  intros [HR|HR']; [left|right]; reflexivity.
Qed.

#[export] Instance rel_union_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∪ R').
Proof.
  unfold Symmetric.
  unfold union, relation_union.
  firstorder.
Qed.


#[export] Instance rel_intersection_refl {A} {R R' : relation A} :
  Reflexive R -> Reflexive R' -> Reflexive (R ∩ R').
Proof.
  intros; split; reflexivity.
Qed.

#[export] Instance rel_intersection_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∩ R').
Proof.
  unfold Symmetric.
  unfold intersection, relation_intersection.
  firstorder.
Qed.

#[export] Instance rel_intersection_trans {A} {R R' : relation A} :
  Transitive R -> Transitive R' -> Transitive (R ∩ R').
Proof.
  intros ? ?.
  intros ? ? ? [] []; split; etransitivity; eauto.
Qed.

#[export] Instance rel_intersection_equiv {A} {R R' : relation A} :
  Equivalence R -> Equivalence R' -> Equivalence (R ∩ R').
Proof.
  intros ? ?; split; apply _.
Qed.


#[export] Instance rel_difference_refl {A} {R R' : relation A} :
  Reflexive R -> Irreflexive R' -> Reflexive (R ∖ R').
Proof.
  intros HR HR'; split; [apply HR|apply HR'].
Qed.

#[export] Instance rel_difference_symm {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∖ R').
Proof.
  intros ? ?.
  intros a a' [HRa%symmetry HR'a%not_symmetry].
  now split.
Qed.

Section preimage.
Context {A B} (f : A -> B) (R : relation B).
Definition rel_preimage : relation A :=
  fun a b => R (f a) (f b).

#[export] Instance rel_preimage_refl : Reflexive R -> Reflexive rel_preimage.
Proof.
  intros ? ?; hnf; reflexivity.
Qed.

#[export] Instance rel_preimage_symm : Symmetric R -> Symmetric rel_preimage.
Proof.
  intros ? ? ? ?; hnf; symmetry; easy.
Qed.

#[export] Instance rel_preimage_trans : Transitive R -> Transitive rel_preimage.
Proof.
  unfold rel_preimage.
  intros ? ? ? ? ? ?; etransitivity; eauto.
Qed.

#[export] Instance rel_preimage_equiv : Equivalence R -> Equivalence rel_preimage.
Proof.
  intros ?; split; apply _.
Qed.

End preimage.


Lemma relation_subseteq_antisymm {A} (R1 R2 : relation A) :
  R1 ⊆ R2 -> R2 ⊆ R1 -> R1 ≡ R2.
Proof.
  firstorder.
Qed.

Lemma elem_of_relation {A} {RA : relation A} xy :
  xy ∈ RA <-> RA xy.1 xy.2.
Proof.
  done.
Qed.
Lemma elem_of_relation_pair {A} {RA : relation A} x y :
  (x, y) ∈ RA <-> RA x y.
Proof.
  done.
Qed.
Lemma relation_equiv_iff {A} {RA RA' : relation A} :
  RA ≡ RA' <-> forall a a', RA a a' <-> RA' a a'.
Proof.
  split; [|intros Heq xy; apply Heq].
  intros Heq a a'.
  apply (Heq (a, a')).
Qed.
Lemma relation_subseteq_iff {A} {RA RA' : relation A} :
  RA ⊆ RA' <-> subrelation RA RA'.
Proof.
  split; [|intros Heq xy; apply Heq].
  intros Heq a a'.
  apply (Heq (a, a')).
Qed.
Lemma rtc_prod_relation `{RA : relation A, RB : relation B} :
  rtc (prod_relation RA RB) ⊆ prod_relation (rtc RA) (rtc RB).
Proof.
  apply relation_subseteq_iff.
  intros [a b] [a' b'].
  intros Heq.
  induction Heq; [done|].
  etransitivity; [|eassumption].
  unfold prod_relation in *.
  split; now apply rtc_once.
Qed.

Lemma rel_union_subseteq_l {A} (R1 R2 : relation A) :
  R1 ⊆ R1 ∪ R2.
Proof.
  firstorder.
Qed.

Lemma rel_union_subseteq_r {A} (R1 R2 : relation A) :
  R2 ⊆ R1 ∪ R2.
Proof.
  firstorder.
Qed.

Definition rel_compose {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) :
  A -> C -> Prop :=
  fun a c => exists b, R1 a b /\ R2 b c.

#[export] Hint Unfold rel_compose : core.

Add Parametric Morphism {A B C} : (@rel_compose A B C) with signature
  equiv ==> equiv ==> equiv as rel_compose_equiv.
Proof.
  intros R1 R1' HR1 R2 R2' HR2.
  intros (a, c).
  unfold elem_of, relation_elem_of.
  cbn.
  split; intros [b ?]; exists b;
  now (split; [apply (HR1 (_, _))|apply (HR2 (_, _))]).
Qed.

Add Parametric Morphism {A B C} : (@rel_compose A B C) with signature
  subseteq ==> subseteq ==> subseteq as rel_compose_subseteq.
Proof.
  intros R1 R1' HR1 R2 R2' HR2.
  intros (a, c).
  unfold elem_of, relation_elem_of.
  cbn.
  intros [b []].
  exists b.
  split; [now apply (HR1 (_, _))|now apply (HR2 (_, _))].
Qed.

#[export] Instance subrelation_rel_compose_l {A} (R1 R2 : relation A) :
  Reflexive R2 -> subrelation R1 (rel_compose R1 R2).
Proof.
  intros HR2 a b Hab.
  now exists b.
Qed.

#[export] Instance subrelation_rel_compose_r {A} (R1 R2 : relation A) :
  Reflexive R1 -> subrelation R2 (rel_compose R1 R2).
Proof.
  intros HR2 a b Hab.
  now exists a.
Qed.


Lemma Transitive_iff_subseteq {A} (R : relation A) :
  Transitive R <-> rel_compose R R ⊆ R.
Proof.
  setoid_rewrite relation_subseteq_iff.
  firstorder.
Qed.

Lemma rel_compose_assoc {A B C D} R1 R2 R3 :
  @rel_compose A C D (@rel_compose A B C R1 R2) R3 ≡
  rel_compose R1 (rel_compose R2 R3).
Proof.
  firstorder.
Qed.

Lemma rel_compose_trans {A} (R1 R2 : relation A) :
  Transitive R1 -> Transitive R2 ->
  rel_compose R2 R1 ⊆ rel_compose R1 R2 ->
  Transitive (rel_compose R1 R2).
Proof.
  intros HR1%((Transitive_iff_subseteq _)) HR2%((Transitive_iff_subseteq _)) Hsubs.
  rewrite Transitive_iff_subseteq.
  rewrite rel_compose_assoc, <- (rel_compose_assoc R2).
  rewrite Hsubs.
  rewrite rel_compose_assoc.
  rewrite HR2.
  rewrite <- rel_compose_assoc.
  rewrite HR1.
  done.
Qed.




Lemma rtc_unfold {A} (R : relation A) :
  rtc R ≡ eq ∪ rel_compose R (rtc R).
Proof.
  apply relation_equiv_iff.
  intros a b.
  split.
  - intros []; [now left|right].
    eauto.
  - intros [<-|(c & Hac & Hcb)]; econstructor; eauto.
Qed.

Lemma rtc_unfold_once_l {A} (R : relation A) :
  rel_compose R (rtc R) ⊆ rtc R.
Proof.
  rewrite rtc_unfold at 2.
  apply rel_union_subseteq_r.
Qed.

Lemma rtc_compose_right {A} (R1 R2 : relation A) :
  rel_compose (rtc (rel_compose R1 R2)) R1 ≡
  rel_compose R1 (rtc (rel_compose R2 R1)).
Proof.
  apply relation_subseteq_antisymm; apply relation_subseteq_iff.
  - intros a d (c & Hac & Hcd).
    induction Hac as [|a b c Hab Hbc IHHac].
    + exists d.
      eauto using rtc.
    + destruct Hab as (a' & Haa' & Ha'b).
      exists a'; apply (conj Haa').
      destruct IHHac as (c' & Hbc' & Hc'd); [done|].
      eauto using rtc.
  - intros a d (b & Hab & Hbd).
    revert a Hab;
    induction Hbd as [|b c d Hbc Hcd IHHbd]; intros a Hab.
    + exists a.
      eauto using rtc.
    + destruct Hbc as (b' & Hbb' & Hb'c).
      destruct (IHHbd b') as (c' & Hbc' & Hc'd); [done|].
      exists c'; split; [|done].
      eauto using rtc.
Qed.

Lemma rtc_subseteq {A} (R1 R2 : relation A) : R1 ⊆ R2 ->
  rtc R1 ⊆ rtc R2.
Proof.
  intros HR%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a b Hab.
  induction Hab; eauto using rtc.
Qed.

Lemma rtc_subseteq_once {A} (R : relation A) :
  R ⊆ rtc R.
Proof.
  apply relation_subseteq_iff.
  intros a b Hab.
  now apply rtc_once.
Qed.

Lemma rtc_id {A} (R : relation A) : Reflexive R -> Transitive R ->
  rtc R ≡ R.
Proof.
  intros HR HT.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros a b Hab.
    induction Hab; eauto.
  - apply (rtc_subseteq_once).
Qed.

Lemma rtc_idemp {A} (R : relation A) :
  rtc (rtc R) ≡ rtc R.
Proof.
  apply rtc_id; apply _.
Qed.

Lemma rtc_union {A} (R1 R2 : relation A) :
  rtc (R1 ∪ R2) ≡ rel_compose (rtc R1) (rtc (rel_compose R2 (rtc R1))).
Proof.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros a c Hac.
    induction Hac as [|a b c Hab Hbc IHHac];[eauto using rtc|].
    destruct IHHac as (b' & Hbb' & Hcc').
    destruct Hab as [Hab|Hab].
    + exists b'; split; [|done].
      eauto using rtc.
    + exists a.
      split; [done|].
      eauto using rtc.
  - rewrite <- (rtc_idemp (R1 ∪ R2)).
    rewrite <- (rtc_unfold_once_l (rtc _)).
    f_equiv.
    + apply rtc_subseteq, rel_union_subseteq_l.
    + apply rtc_subseteq.
      rewrite <- (rtc_unfold_once_l (_ ∪ _)).
      f_equiv; [apply rel_union_subseteq_r|].
      apply rtc_subseteq, rel_union_subseteq_l.
Qed.

Lemma rtc_commutes_self {A} (R : relation A) :
  rel_compose R (rtc R) ≡ rel_compose (rtc R) R.
Proof.
  apply relation_equiv_iff.
  intros a c.
  split.
  - intros (b & Hab & Hbc).
    revert a Hab;
    induction Hbc as [|b b' c Hbb' Hb'c IH];
    intros a Hab.
    + eauto using rtc.
    + destruct (IH b) as (b'' & Hbb'' & Hb''c); [done|].
      eauto using rtc.
  - intros (b & Hab & Hbc).
    (* revert c Hbc; *)
    induction Hab as [|a a' b Haa' Ha'b IH].
      (* intros c Hbc. *)
    + eauto using rtc.
    + destruct IH as (b'' & Hbb'' & Hb''c); [done|].
      eauto using rtc.
Qed.


Lemma rtc_unfold_once_r {A} (R : relation A) :
  rel_compose (rtc R) R ⊆ rtc R.
Proof.
  rewrite <- rtc_commutes_self.
  apply rtc_unfold_once_l.
Qed.

(* Lemma rtc_induction {A} (R : relation A) (P : relation A -> Prop)
  `{HP : !Proper (equiv ==> iff) P}
  (Heq : P eq) (Hcomp : forall R', P R' -> P (rel_compose R R')) :
  P (rtc R).
Proof.
   *)

Lemma rtc_subseteq_ind_l {A} (R1 R2 : relation A) :
  rel_compose R1 R2 ⊆ R2 ->
  rel_compose (rtc R1) R2 ⊆ R2.
Proof.
  intros HR12%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a c (b & Hab & ?).
  induction Hab; [done|].
  eauto 7.
Qed.


Lemma rtc_subseteq_ind_r {A} (R1 R2 : relation A) :
  rel_compose R1 R2 ⊆ R1 ->
  rel_compose R1 (rtc R2) ⊆ R1.
Proof.
  intros HR12%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a c (b & ? & Hbc).
  induction Hbc; [done|].
  eauto 7.
Qed.

Lemma rtc_commute_subseteq_l {A} (R1 R2 : relation A) :
  rel_compose R1 R2 ⊆ rel_compose R2 R1 ->
  rel_compose (rtc R1) R2 ⊆ rel_compose R2 (rtc R1).
Proof.
  intros HR12%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a c (b & Hab & ?).
  induction Hab as [|a a' b Haa' Ha'b IH]; [eauto using rtc|].
  destruct (IH ltac:(auto)) as (b' & Ha'b' & Hb'c).
  specialize (HR12 a b' ltac:(eauto)) as (a'' & Ha''a & Ha''b').
  eauto using rtc.
Qed.


Lemma rtc_commute_subseteq_r {A} (R1 R2 : relation A) :
  rel_compose R1 R2 ⊆ rel_compose R2 R1 ->
  rel_compose R1 (rtc R2) ⊆ rel_compose (rtc R2) R1.
Proof.
  intros HR12%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a c (b & Hab & Hbc).
  revert a Hab;
  induction Hbc as [|b b' c Hbb' Hb'c IH]; [eauto using rtc|];
  intros a Hab.
  specialize (HR12 a b' ltac:(eauto)) as (a'' & Ha''a & Ha''b').
  destruct (IH a'' ltac:(auto)) as (?&?&?). eauto using rtc.
Qed.


Lemma rtc_compose_commut_rl {A} (R1 R2 : relation A) :
  rel_compose R2 R1 ⊆ rel_compose R1 R2 ->
  rtc (rel_compose R1 R2) ⊆ rel_compose (rtc R1) (rtc R2).
Proof.
  intros HR12.
  pose proof HR12 as H12%relation_subseteq_iff.
  apply relation_subseteq_iff.
  intros a c Hac.
  induction Hac as [|a b c Hab Hbc IH]; [eauto using rtc|].
  refine (proj1 (elem_of_relation_pair _ _) _).
  eapply rel_compose_subseteq; [apply rtc_unfold_once_l..|].
  rewrite rel_compose_assoc, <- (rel_compose_assoc (rtc R1)).
  eapply rel_compose_subseteq; [reflexivity|
  apply rel_compose_subseteq; [now apply rtc_commute_subseteq_r|reflexivity]|].
  rewrite <- 2 rel_compose_assoc, rel_compose_assoc.
  apply elem_of_relation_pair.
  eauto.
Qed.


#[export] Instance rtc_once_subrelation {A} (R : relation A) :
  subrelation R (rtc R).
Proof.
  refine rtc_once.
Qed.
#[export] Instance rel_union_subrelation_l {A} (R1 R1' R2 : relation A) :
  subrelation R1 R1' -> subrelation R1 (R1' ∪ R2) | 10.
Proof.
  firstorder.
Qed.
#[export] Instance rel_union_subrelation_r {A} (R1 R2 R2' : relation A) :
  subrelation R2 R2' -> subrelation R2 (R1 ∪ R2') | 10.
Proof.
  firstorder.
Qed.
#[export] Instance rel_union_subrelation_l' {A} (R1 R2 : relation A) :
  subrelation R1 (R1 ∪ R2).
Proof.
  firstorder.
Qed.
#[export] Instance rel_union_subrelation_r' {A} (R1 R2 : relation A) :
  subrelation R2 (R1 ∪ R2).
Proof.
  firstorder.
Qed.
#[export] Instance rtc_once_subrelation' {A} (R1 R2 : relation A) :
  subrelation R1 R2 ->
  subrelation R1 (rtc R2).
Proof.
  intros ->.
  apply _.
Qed.
Lemma subrel {A} {R1 R2 : relation A} `{H12 : !subrelation R1 R2} {x y} :
  R1 x y -> R2 x y.
Proof.
  firstorder.
Qed.
Lemma Reflexive_iff_subseteq {A} (R : relation A) :
  Reflexive R <-> eq ⊆@{relation A} R.
Proof.
  rewrite relation_subseteq_iff.
  split; [intros; now apply eq_subrelation|].
  firstorder.
Qed.
Lemma Symmetric_iff_subseteq {A} (R : relation A) :
  Symmetric R <-> R ⊆ flip R.
Proof.
  rewrite relation_subseteq_iff.
  unfold Symmetric.
  firstorder.
Qed.
Lemma Equivalence_iff_substeqs {A} (R : relation A) :
  Equivalence R <->
  eq ⊆@{relation A} R /\
  R ⊆ flip R /\
  rel_compose R R ⊆ R.
Proof.
  rewrite <- Reflexive_iff_subseteq, <- Symmetric_iff_subseteq,
    <- Transitive_iff_subseteq.
  split; [now intros []|].
  now constructor.
Qed.
Lemma Equivalence_equiv_proper {A} (R1 R2 : relation A) :
  R1 ≡ R2 -> Equivalence R1 <-> Equivalence R2.
Proof.
  intros Heq.
  assert (HR12 : R1 ⊆ R2) by now rewrite Heq.
  assert (HR21 : R2 ⊆ R1) by now rewrite Heq.
  clear Heq.
  rewrite relation_subseteq_iff in HR12.
  rewrite relation_subseteq_iff in HR21.
  intros; split; intros []; constructor;
  firstorder eauto.
Qed.

Lemma rtc_union_weaken {A} (R1 R2 : relation A) :
  rel_compose (rtc R1) (rtc R2) ⊆ rtc (R1 ∪ R2).
Proof.
  rewrite rtc_union.
  f_equiv.
  apply rtc_subseteq.
  apply relation_subseteq_iff.
  hnf; eauto using rtc.
Qed.

Lemma rel_union_subseteq {A} (R1 R2 R3 : relation A) : 
  R1 ∪ R2 ⊆ R3 <-> R1 ⊆ R3 /\ R2 ⊆ R3.
Proof.
  firstorder.
Qed.

Lemma rtc_union_commute {A} (R1 R2 : relation A) :
  rel_compose R2 R1 ⊆ rel_compose R1 R2 ->
  rtc (R1 ∪ R2) ≡ rel_compose (rtc R1) (rtc R2).
Proof.
  intros Hcomm.
  apply relation_subseteq_antisymm; [|apply rtc_union_weaken].
  rewrite <- (rtc_id (rel_compose _ _)); [|hnf; eauto using rtc|
  apply rel_compose_trans; [apply _..|]; 
  now apply rtc_commute_subseteq_l, rtc_commute_subseteq_r].
  apply rtc_subseteq.
  apply rel_union_subseteq; split; 
  apply relation_subseteq_iff; intros ? ? ?; eauto using rtc.
Qed.


Lemma rtc_proper {A B} (RA : relation A) (RB : relation B)
  (f : A -> B) : Proper (RA ==> RB) f -> Proper (rtc RA ==> rtc RB) f.
Proof.
  intros Hf.
  intros a b Hab.
  induction Hab; eauto using rtc.
Qed.
(* Lemma rtc_respectful {A B} (RA : relation A) (RB : relation B) :
  rtc (RA ==> RB)%signature ⊆ (rtc RA ==> rtc RB)%signature.
Proof.
  apply relation_subseteq_iff.
  intros f g. *)
Lemma rtc_proper2 {A B C} (RA : relation A) `{HRA : !Reflexive RA}
  (RB : relation B) `{HRB : !Reflexive RB} (RC : relation C)
  (f : A -> B -> C) : Proper (RA ==> RB ==> RC) f ->
    Proper (rtc RA ==> rtc RB ==> rtc RC) f.
Proof.
  intros Hf.
  intros a a' Ha b b' Hb.
  revert b b' Hb; induction Ha; intros b b' Hb;
    induction Hb; [reflexivity|..].
  - rewrite <- IHHb.
    apply rtc_once.
    apply Hf; done.
  - rewrite <- IHHa by reflexivity.
    apply rtc_once.
    apply Hf; done.
  - rewrite <- IHHb by done.
    apply rtc_once.
    apply Hf; done.
Qed.
Lemma rtc_proper2' {A B C} (RA : relation A)
  (RB : relation B) (RC : relation C)
  (f : A -> B -> C) : Proper (RA ==> eq ==> RC) f ->
    Proper (eq ==> RB ==> RC) f ->
    Proper (rtc RA ==> rtc RB ==> rtc RC) f.
Proof.
  intros HfA HfB.
  intros a a' Ha b b' Hb.
  revert b b' Hb; induction Ha; intros b b' Hb;
    induction Hb; [reflexivity|..].
  - rewrite <- IHHb.
    apply rtc_once.
    apply HfB; done.
  - rewrite <- IHHa by reflexivity.
    apply rtc_once.
    apply HfA; done.
  - rewrite <- IHHb by done.
    apply rtc_once.
    apply HfB; done.
Qed.
Lemma rtc_subrelation {A} (R1 R2 : relation A) :
  subrelation R1 R2 -> subrelation (rtc R1) (rtc R2).
Proof.
  rewrite <- 2 relation_subseteq_iff.
  apply rtc_subseteq.
Qed.
#[export] Instance rel_preimage_proper {A B} (f : A -> B) :
  Proper (equiv ==> equiv) (rel_preimage f).
Proof.
  hnf.
  intros RB RB'.
  rewrite relation_equiv_iff.
  firstorder.
Qed.
Lemma rel_compose_subseteq_trans {A} (R1 R2 R3 : relation A)
  `{HR3 : !Transitive R3} :
  R1 ⊆ R3 -> R2 ⊆ R3 -> rel_compose R1 R2 ⊆@{relation A} R3.
Proof.
  rewrite 3 relation_subseteq_iff.
  firstorder eauto.
Qed.
#[export] Instance respectful_equiv {A B} :
  Proper (equiv ==> equiv ==> equiv) (@respectful A B).
Proof.
  intros RA RA' HRA RB RB' HRB.
  rewrite @relation_equiv_iff in *.
  intros f g.
  unfold respectful.
  setoid_rewrite HRA.
  setoid_rewrite HRB.
  done.
Qed.
Lemma Proper_equiv_proper {A} : Proper (equiv ==> eq ==> iff) (@Proper A).
Proof.
  intros RA RA' HRA f _ <-.
  rewrite relation_equiv_iff in HRA.
  apply HRA.
Qed.
Lemma rel_union_proper_l {A B} (RA1 RA2 : relation A) (RB : relation B) f :
  Proper (RA1 ==> RB) f ->
  Proper (RA2 ==> RB) f ->
  Proper (RA1 ∪ RA2 ==> RB) f.
Proof.
  firstorder.
Qed.
Lemma rel_union_proper {A B} (RA1 RA2 : relation A) (RB1 RB2 : relation B) f :
  Proper (RA1 ==> RB1) f ->
  Proper (RA2 ==> RB2) f ->
  Proper (RA1 ∪ RA2 ==> RB1 ∪ RB2) f.
Proof.
  firstorder.
Qed.



Lemma rtc_rel_preimage_subseteq {A B} (f : A -> B) (R : relation B) :
  rtc (rel_preimage f R) ⊆ rel_preimage f (rtc R).
Proof.
  apply relation_subseteq_iff.
  intros x y Hxy.
  unfold rel_preimage.
  induction Hxy; eauto using rtc.
Qed.

Lemma rel_preimage_rtc {A B} (f : A -> B) `{Hf : !Inj eq eq f} (R : relation B) :
  (forall a b, R (f a) b -> exists a', f a' = b) ->
  rel_preimage f (rtc R) ≡ rtc (rel_preimage f R).
Proof.
  intros HRf.
  apply relation_subseteq_antisymm; [apply relation_subseteq_iff|apply rtc_rel_preimage_subseteq].
  intros x y.
  unfold rel_preimage at 1.
  intros Heq.
  remember (f x) as fx eqn:Hfx.
  remember (f y) as fy eqn:Hfy.
  revert x Hfx y Hfy.
  induction Heq as [|x y z Hxy Hyz IH].
  - intros a -> b ->%Hf.
    done.
  - intros a -> c ->.
    apply HRf in Hxy as Hb.
    destruct Hb as (b & <-).
    eauto using rtc.
Qed.

Lemma rel_preimage_union {A B} (f : A -> B) (R1 R2 : relation B) : 
  rel_preimage f (R1 ∪ R2) = rel_preimage f R1 ∪ rel_preimage f R2.
Proof.
  reflexivity.
Qed.

