(* Some auxiliary results and tactics, that should 
  really live somewhere else. *)

Require Import Setoid.

Lemma eq_reflexivity {A : Type} {RA : relation A} `{Reflexive A RA} x y : 
  x = y -> RA x y.
Proof.
  now intros ->.
Qed.




Lemma exists_sig {A} {P Q : A -> Prop} : 
  (exists x : sig P, Q (proj1_sig x)) <-> exists x, P x /\ Q x.
Proof.
  split.
  - intros ((x & p) & q).
    eauto.
  - intros (x & p & q).
    now exists (exist P x p).
Qed.

Lemma exists_sigT {A} {P : A -> Type} {Q : sigT P -> Prop}: 
  (exists x : sigT P, Q x) <-> exists x p, Q (@existT A P x p).
Proof.
  split.
  - intros ((x & p) & q).
    eauto.
  - intros (x & p & q).
    now exists (@existT A P x p).
Qed.

Lemma exists_and_sig {A} {P Q R : A -> Prop} : 
  (exists x : {a : A | P a /\ Q a}, R (proj1_sig x)) <-> 
    exists (x : {a : A | P a}), Q (proj1_sig x) /\ R (proj1_sig x).
Proof.
  rewrite exists_sig.
  setoid_rewrite and_assoc.
  now rewrite <- exists_sig.
Qed.

Lemma exists_sig2 {A} {P Q R : A -> Prop} : 
  (exists x : sig2 P Q, R ( proj1_sig (sig_of_sig2 x))) <-> 
    exists x, P x /\ Q x /\ R x.
Proof.
  split.
  - intros ([x p q] & r).
    eauto.
  - intros (x & p & q & r).
    now exists (exist2 _ _ x p q).
Qed.




Lemma exists_iff {A} (P Q : A -> Prop) : 
  (forall a, P a <-> Q a) -> (exists a, P a) <-> (exists a, Q a).
Proof. firstorder. Qed.

Lemma forall_iff {A} (P Q : A -> Prop) : 
  (forall a, P a <-> Q a) -> (forall a, P a) <-> (forall a, Q a).
Proof. firstorder. Qed.



Lemma and_is_True_r {P Q} : Q -> P /\ Q <-> P.
Proof. tauto. Qed.
Lemma and_is_True_l {P Q} : P -> P /\ Q <-> Q.
Proof. tauto. Qed.
Lemma and_or_distr_r {P Q R} : (P \/ Q) /\ R <-> P /\ R \/ Q /\ R.
Proof. tauto. Qed.
Lemma and_or_distr_l {P Q R} : P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof. tauto. Qed.
Lemma iff_True {P} : (P <-> True) <-> P.
Proof. tauto. Qed.
Lemma iff_True_1 {P} : P -> (P <-> True).
Proof. tauto. Qed.
Lemma iff_True_2 {P} : (P <-> True) -> P.
Proof. tauto. Qed.  



(* FIXME: Move *)
Tactic Notation "vm_eval" uconstr(pat) :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in *;
  vm_compute in Hx;
  subst x.

Tactic Notation "vm_eval" uconstr(pat) "in" 
  ne_hyp_list_sep(H, ",") :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in H;
  vm_compute in Hx;
  subst x.