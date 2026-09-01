From QuantumLib Require Import Complex.
Require Import QArith Qreals.

(* A computational subset of the complex numbers,
  where [(a,b,c,d)] represents [a + b * Ci + c / √2 + d * Ci / √2 ] *)
Inductive QC : Set :=
  | mkQC (a b c d : Q) : QC.

Definition QCred (q : QC) : QC :=
  let '(mkQC a b c d) := q in
  mkQC (Qred a) (Qred b) (Qred c) (Qred d).

Definition QC2C (q : QC) : C :=
  let '(mkQC a b c d) := q in
  (Q2R a + Q2R b / √ 2, Q2R c + Q2R d / √ 2)%R.

Definition Q2QC (q : Q) : QC :=
  mkQC q 0 0 0.

Definition QCeq : relation QC :=
  fun q q' =>
  let '(mkQC a b c d) := q in
  let '(mkQC a' b' c' d') := q' in
  Qeq a a' /\ Qeq b b' /\ Qeq c c' /\ Qeq d d'.

Definition QCeqb (q r : QC) : bool :=
  let '(mkQC a b c d) := q in
  let '(mkQC a' b' c' d') := r in
  Qeq_bool a a' && Qeq_bool b b' && Qeq_bool c c' && Qeq_bool d d'.

Definition QCplus (q q' : QC) : QC :=
  let '(mkQC a b c d) := q in
  let '(mkQC a' b' c' d') := q' in
  mkQC (a + a') (b + b') (c + c') (d + d').

Definition QCopp (q : QC) : QC :=
  let '(mkQC a b c d) := q in
  mkQC (-a) (-b) (-c) (-d).

Definition QCminus q r : QC := QCplus q (QCopp r).

Definition QCmult (q q' : QC) : QC :=
  let '(mkQC a b c d) := q in
  let '(mkQC a' b' c' d') := q' in
  QCred (mkQC
    (a * a' + b * b' / 2 - c * c' - d * d' / 2)
    (a * b' + b * a'     - c * d' - d * c')
    (a * c' + b * d' / 2 + c * a' + d * b' / 2)
    (a * d' + b * c'     + c * b' + d * a')).

Definition QCinv (q : QC) : QC :=
  let '(mkQC a b c d) := q in
  let q_den_terms := (a * a + b * b / 2 + c * c + d * d / 2)%Q in
  let root2_den_terms := (2 * a * b + 2 * c * d)%Q in
  let den_fact := (q_den_terms * q_den_terms - root2_den_terms * root2_den_terms / 2) in
  QCred (QCmult (mkQC a b (-c) (-d)) (
    mkQC (q_den_terms / den_fact) (-root2_den_terms / den_fact)
    0 0
  )).

Definition QCdiv (q r : QC) : QC := QCmult q (QCinv r).

Definition QCconj (q : QC) : QC :=
  let '(mkQC a b c d) := q in
  mkQC a b (-c) (-d).

Declare Scope QC_scope.
Delimit Scope QC_scope with QC.
Bind Scope QC_scope with QC.

(* Levels for these notations are inherited from existing definitions
  in other scopes *)
Notation "q == r" := (QCeq q r) : QC_scope.
Notation "q + r" := (QCplus q r) : QC_scope.
Notation "q - r" := (QCminus q r) : QC_scope.
Notation "q * r" := (QCmult q r) : QC_scope.
Notation "q / r" := (QCdiv q r) : QC_scope.
Notation "- q" := (QCopp q) : QC_scope.
Notation "/ q" := (QCinv q) : QC_scope.
Notation "q ^*" := (QCconj q) : QC_scope.

Open Scope QC_scope.

Lemma QCeq_refl q : q == q.
Proof.
  destruct q as [a b c d].
  repeat split.
Qed.

Lemma QCeq_sym q r : q == r -> r == q.
Proof.
  destruct q as [a b c d].
  destruct r as [a' b' c' d'].
  cbn.
  intros (? & ? & ? & ?);
  repeat split; now symmetry.
Qed.

Lemma QCeq_trans q r s : q == r -> r == s -> q == s.
Proof.
  destruct q as [a b c d].
  destruct r as [a' b' c' d'].
  destruct s as [a'' b'' c'' d''].
  cbn.
  intros (? & ? & ? & ?) (? & ? & ? & ?).
  repeat split; now etransitivity; eauto.
Qed.

Add Parametric Relation : QC QCeq
  reflexivity proved by QCeq_refl
  symmetry proved by QCeq_sym
  transitivity proved by QCeq_trans
  as QCeq_setoid.

Lemma Qeq_bool_spec q r : reflect (Qeq q r) (Qeq_bool q r).
Proof.
  apply iff_reflect; now rewrite Qeq_bool_iff.
Qed.

Lemma QCeqb_spec q r : reflect (q == r) (QCeqb q r).
Proof.
  destruct q as [a b c d], r as [a' b' c' d'].
  cbn.
  apply iff_reflect.
  rewrite 3!andb_true_iff, 4 Qeq_bool_iff.
  firstorder.
Qed.

#[export] Hint Resolve Qeq_bool_spec QCeqb_spec : bdestruct.

Lemma QCeqb_iff q r : QCeqb q r = true <-> q == r.
Proof.
  symmetry.
  apply reflect_iff, QCeqb_spec.
Qed.

Lemma QCeqb_eq q r : QCeqb q r = true -> q == r.
Proof.
  apply QCeqb_iff.
Qed.

Lemma QCred_correct qc : QCred qc == qc.
Proof.
  destruct qc; repeat split; apply Qred_correct.
Qed.

Add Parametric Morphism : QCred with signature
  QCeq ==> eq as QCred_mor.
Proof.
  intros [a b c d] [a' b' c' d'] (Ha & Hb & Hc & Hd).
  cbn.
  f_equal; now apply Qred_complete.
Qed.

Add Parametric Morphism : QCred with signature
  QCeq ==> QCeq as QCred_mor'.
Proof.
  intros ? ? ->; easy.
Qed.

Add Parametric Morphism : QC2C with signature
  QCeq ==> eq as QC2C_mor.
Proof.
  intros [a b c d] [a' b' c' d'] (Ha & Hb & Hc & Hd).
  cbn.
  now rewrite Ha, Hb, Hc, Hd.
Qed.

Add Parametric Morphism : mkQC with signature
  Qeq ==> Qeq ==> Qeq ==> Qeq ==> QCeq as mkQC_mor.
Proof.
  cbn.
  easy.
Qed.

Add Parametric Morphism : QCeqb with signature
  QCeq ==> QCeq ==> eq as QCeqb_mor.
Proof.
  intros x x' H y y' H'.
  apply Bool.eq_iff_eq_true.
  rewrite 2 QCeqb_iff.
  now rewrite H, H'.
Qed.

Add Parametric Morphism : QCplus with signature
  QCeq ==> QCeq ==> QCeq as QCplus_mor.
Proof.
  intros [] [] Heqs [] [] Heqs'.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCmult with signature
  QCeq ==> QCeq ==> QCeq as QCmult_mor.
Proof.
  intros [] [] Heqs [] [] Heqs'.
  unfold QCmult.
  f_equiv.
  cbn in *.
  repeat split; repeat f_equiv; easy.
Qed.

Add Parametric Morphism : QCopp with signature
  QCeq ==> QCeq as QCopp_mor.
Proof.
  intros [] [] Heqs.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCconj with signature
  QCeq ==> QCeq as QCconj_mor.
Proof.
  intros [] [] Heqs.
  cbn in *.
  repeat split; f_equiv; easy.
Qed.

Add Parametric Morphism : QCinv with signature
  QCeq ==> QCeq as QCinv_mor.
Proof.
  intros [] [] Heqs.
  unfold QCinv.
  destruct Heqs as (Ha & Hb & Hc & Hd).
  now rewrite Ha, Hb, Hc, Hd.
Qed.

Add Parametric Morphism : QCminus with signature
  QCeq ==> QCeq ==> QCeq as QCminus_mor.
Proof.
  intros ? ? H ? ? H'.
  unfold QCminus.
  now rewrite H, H'.
Qed.

Add Parametric Morphism : QCdiv with signature
  QCeq ==> QCeq ==> QCeq as QCdiv_mor.
Proof.
  intros ? ? H ? ? H'.
  unfold QCdiv.
  now rewrite H, H'.
Qed.

Coercion Q2QC : Q >-> QC.

Lemma QCeq_iff_QCminus_eq_0 q r : q == r <-> q - r == 0.
Proof.
  destruct q, r.
  cbn.
  lra.
Qed.

Section QC2C.

Local Open Scope C_scope.
Local Coercion QC2C : QC >-> C.

Lemma QC2C_plus q r : QC2C (q + r) = q + r.
Proof.
  destruct q, r.
  cbn.
  rewrite !Q2R_plus.
  lca.
Qed.

Lemma QC2C_QCred q : QC2C (QCred q) = QC2C q.
Proof.
  destruct q.
  cbn.
  now rewrite 4 Qred_correct.
Qed.

Lemma QC2C_mult q r : QC2C (q * r) = q * r.
Proof.
  destruct q, r.
  unfold QCmult.
  rewrite QC2C_QCred.
  cbn.
  rewrite !Q2R_minus, !Q2R_plus, !(Q2R_div _ 2), !Q2R_mult by lra.
  replace (Q2R 2) with (2%R) by lra.
  pose proof sqrt2_neq_0.
  apply c_proj_eq; cbn; R_field.
Qed.

Lemma QC2C_opp q : QC2C (- q) = - q.
Proof.
  destruct q.
  cbn.
  rewrite !Q2R_opp.
  lca.
Qed.

Lemma QC2C_minus q r : QC2C (q - r) = q - r.
Proof.
  unfold QCminus.
  rewrite QC2C_plus, QC2C_opp.
  reflexivity.
Qed.

Section Irrational.
Local Open Scope R_scope.
Local Lemma Q2R_0 : Q2R 0 = 0.
Proof. lra. Qed.
Local Lemma Q2R_0' q : (q == 0)%Q -> Q2R q = 0.
Proof. intros ->; apply Q2R_0. Qed.
Local Lemma Q2R_inv' q : Q2R (/q) = / Q2R q.
Proof.
  bdestruct (Qeq_bool q 0).
  - rewrite H.
    rewrite 2 Q2R_0' by reflexivity.
    now rewrite Rinv_0.
  - now apply Q2R_inv.
Qed.
Local Lemma Q2R_div' q r : Q2R (q / r) = Q2R q / Q2R r.
Proof.
  unfold Qdiv, Rdiv.
  now rewrite Q2R_mult, Q2R_inv'.
Qed.
Local Lemma Q2R_0_inv : forall q, Q2R q = 0%R -> Qeq q 0.
Proof.
  intros ?.
  rewrite <- RMicromega.Q2R_0.
  apply eqR_Qeq.
Qed.

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
Qed.

Local Lemma sqrt2_irrational'' q r : (Q2R q * √ 2 + Q2R r = 0%R <->
  q == 0 /\ r == 0)%R%Q.
Proof.
  split.
  - bdestruct (Qeq_bool q 0).
    1: {
      rewrite H, Q2R_0, Rmult_0_l, Rplus_0_l.
      now intros ->%Q2R_0_inv.
    }
    bdestruct (Qeq_bool r 0).
    1: {
      rewrite H0, Q2R_0, Rplus_0_r.
      intros Hprod%Rmult_integral.
      now destruct Hprod as [->%Q2R_0_inv | Hf%sqrt2_neq_0].
    }
    intros Heq.
    assert (Hsqrt2 : √ 2 = Q2R (- r / q)). 1: {
      rewrite Q2R_div', Q2R_opp.
      replace (Q2R r) with (- (Q2R q * √ 2)) by lra.
      field.
      now intros ?%Q2R_0_inv.
    }
    now apply sqrt2_irrational' in Hsqrt2.
  - intros [-> ->]; lra.
Qed.

(* Local Lemma sqrt2_irrational''' (a b : Q) :
  Q2R a * Q2R a * 2 + Q2R b * Q2R b = 0 <-> Qeq a 0 /\ Qeq b 0.
Proof.
  split; [|intros [-> ->]; lra].
  intros Heq.
  assert (Q2R a = 0) by nra.
  lra. *)

End Irrational.

Local Lemma Q2R_sqrt2_inj q r : (Q2R q + Q2R r / √2)%R = 0%R <->
  (q == 0 /\ r == 0)%Q.
Proof.
  split.
  - intros Hz.
    apply sqrt2_irrational''.
    replace (Q2R q) with (- Q2R r / √ 2)%R by lra.
    field.
    apply sqrt2_neq_0.
  - intros [-> ->].
    lra.
Qed.

Lemma eqC0_QCeq0 q : QC2C q = C0 -> q == 0.
Proof.
  intros Heq.
  pose proof Heq as Hfst%(f_equal fst).
  pose proof Heq as Hsnd%(f_equal snd).
  destruct q as [a b c d].
  cbn in Hfst, Hsnd.
  apply Q2R_sqrt2_inj in Hfst, Hsnd.
  cbn.
  easy.
Qed.

Lemma eqC_QCeq q r : QC2C q = QC2C r -> q == r.
Proof.
  intros HQCeq.
  apply QCeq_iff_QCminus_eq_0.
  apply eqC0_QCeq0.
  rewrite QC2C_minus.
  rewrite HQCeq.
  lca.
Qed.

Lemma QCneq_0_neq_C0 q : ~ (q == 0) -> QC2C q <> C0.
Proof.
  now intros Hne Heq%eqC0_QCeq0.
Qed.

Lemma QC2C_conj q : QC2C (q ^*) = q ^*.
Proof.
  destruct q.
  cbn.
  rewrite !Q2R_opp.
  lca.
Qed.

Lemma Cinv_alt (c : C) : / c = c ^* * RtoC (/ (fst c * fst c + snd c * snd c)).
Proof.
  unfold Cinv, Cmult, Cconj;
  cbn.
  rewrite 2!Rmult_1_r, 2!Rmult_0_r, Rplus_0_l, Rminus_0_r.
  reflexivity.
Qed.

Section Rops.

Lemma Rmult_plus_div_sqrt2 (a b c d : R) :
  ((a + b / √2) * (c + d / √ 2) = (a * c + b * d / 2) + (a * d + c * b) / √ 2)%R.
Proof.
  pose proof sqrt2_neq_0.
  R_field.
Qed.


Lemma Rplus_plus_div_sqrt2 (a b c d : R) :
  ((a + b / √2) + (c + d / √ 2) = (a + c) + (b + d) / √ 2)%R.
Proof.
  lra.
Qed.

Lemma sqrt_square_abs (r : R) : √ (r * r) = Rabs r.
Proof.
  unfold Rabs.
  destruct (Rcase_abs r) as [Hneg | Hnneg].
  - replace (r * r)%R with ((-r)*(-r))%R by lra.
    apply sqrt_square; lra.
  - apply sqrt_square; lra.
Qed.


Local Open Scope R_scope.
Lemma Rdiv_le_Rdiv_iff a b c d :
  0 < b -> 0 < d ->
  a / b <= c / d <-> a * d <= c * b.
Proof.
  intros Hb Hd.
  split.
  - intros Hdivs.
    replace (a * d) with (a / b * d * b) by (field; lra).
    apply Rmult_le_compat_r; [lra|].
    replace c with (c / d * d) by (field; lra).
    nra.
  - intros Hle.
    replace (a / b) with (a * d / b / d) by (field; lra).
    replace (c / d) with (c * b / b / d) by (field; lra).
    unfold Rdiv.
    apply Rmult_le_compat_r; [apply Rinv_0_lt_compat in Hd; lra|].
    apply Rmult_le_compat_r; [apply Rinv_0_lt_compat in Hb; lra|].
    lra.
Qed.

Lemma Q2R_le_iff q r : (Q2R q <= Q2R r)%R <-> (q <= r)%Q.
Proof.
  destruct q as [qnum qden], r as [rnum rden].
  unfold Qle.
  cbn.
  unfold Q2R.
  rewrite <- 2 Rdiv_unfold.
  cbn.
  rewrite Rdiv_le_Rdiv_iff by (apply IZR_lt; lia).
  rewrite <- 2 mult_IZR, IZR_le_iff.
  reflexivity.
Qed.

Lemma Q2R_lt_iff q r : (Q2R q < Q2R r)%R <-> (q < r)%Q.
Proof.
  split.
  - intros Hgt%Rlt_not_le.
    rewrite Q2R_le_iff in Hgt.
    lra.
  - intros Hgt%Qlt_not_le.
    apply Rnot_le_lt.
    now rewrite Q2R_le_iff.
Qed.

Lemma Qabs_pos q : Qle 0 q -> (Qabs.Qabs q == q)%Q.
Proof.
  intros Hq.
  refine (Qabs.Qabs_case q (fun x => x == q)%Q _ _); lra.
Qed.

Lemma Qabs_neg q : Qle q 0 -> (Qabs.Qabs q == - q)%Q.
Proof.
  intros Hq.
  refine (Qabs.Qabs_case q (fun x => x == - q)%Q _ _); lra.
Qed.

Lemma Qabs_0_iff q : (Qabs.Qabs q == 0 <-> q == 0)%Q.
Proof.
  refine (Qabs.Qabs_case q (fun x => x == 0 <-> q == 0)%Q _ _); lra.
Qed.

Lemma Qopp_0_iff q : (- q == 0 <-> q == 0)%Q.
Proof. lra. Qed.

Lemma Q2R_abs q : Q2R (Qabs.Qabs q) = Rabs (Q2R q).
Proof.
  unfold Rabs.
  destruct (Rcase_abs) as [Hneg | Hpos].
  - rewrite <- Q2R_opp.
    rewrite <- !Q2R_0, Q2R_lt_iff in Hneg.
    now rewrite Qabs_neg by lra.
  - apply Rge_le in Hpos.
    rewrite <- !Q2R_0, Q2R_le_iff in Hpos.
    now rewrite Qabs_pos by lra.
Qed.

Lemma Rinv_plus_div_sqrt2 (a b : Q) :
  (* (Q2R a + Q2R b / √ 2 <> 0)%R -> *)
  (/ (Q2R a + Q2R b / √2) = (Q2R a + (- Q2R b) / √ 2) *
    (/ (Q2R a * Q2R a - Q2R b * Q2R b / 2)))%R.
Proof.
  destruct (Req_dec (Q2R a + Q2R b / √ 2) 0) as [Hz | Hnz].
  - rewrite Hz, Rinv_0.
    apply Q2R_sqrt2_inj in Hz as [-> ->].
    lra.
  - R_field_simplify; [lra|].
    repeat split; [|apply sqrt2_neq_0|].
    + enough (Q2R a * Q2R a <> Q2R b * Q2R b / 2)%R by lra.
      intros Heq%(f_equal sqrt).
      rewrite sqrt_div, 2 sqrt_square_abs in Heq by nra.
      rewrite <- 2 Q2R_abs in Heq.
      assert (Heq' : Q2R (Qabs.Qabs a) + Q2R (-Qabs.Qabs b) / √2 = 0)
        by (rewrite Heq, Q2R_opp; lra).
      apply Q2R_sqrt2_inj in Heq'.
      rewrite Qopp_0_iff, 2 Qabs_0_iff in Heq'.
      rewrite Q2R_sqrt2_inj in Hnz.
      easy.
    + intros Heq%(f_equal (fun x => Rdiv x (√2))).
      rewrite Rdiv_0_l in Heq.
      apply Hnz.
      rewrite <- Heq.
      field.
      apply sqrt2_neq_0.
Qed.

Open Scope Q_scope.
Open Scope QC_scope.
Open Scope C_scope.

Lemma QC2C_inv q : QC2C (/ q) = / QC2C q.
Proof.
  bdestruct (QCeqb q 0).
  - rewrite H.
    rewrite (QCeqb_eq (/ 0) 0 eq_refl).
    replace (QC2C 0) with C0 by lca.
    now rewrite Cinv_0.
  - cbv delta [QCinv] beta.
    destruct q as [a b c d].
    set (q_den_terms := (a * a + b * b / 2 + c * c + d * d / 2)%Q).
    set (root2_den_terms := (2 * a * b + 2 * c * d)%Q).
    cbv zeta.
    set (den_fact := (q_den_terms * q_den_terms -
      root2_den_terms * root2_den_terms / 2)%Q).

    rewrite QC2C_QCred.

    rewrite QC2C_mult.
    rewrite Cinv_alt.
    f_equal.
    1: {
      rewrite <-QC2C_conj; reflexivity.
    }
    apply c_proj_eq; [|cbn; lra].
    cbn.
    rewrite 2 Rmult_plus_div_sqrt2.
    rewrite <- !Q2R_mult.
    replace 2%R with (Q2R 2) by lra.
    rewrite <- !Q2R_div', <- !Q2R_plus.
    replace (Q2R 2) with 2%R by lra.
    rewrite Rplus_plus_div_sqrt2, <- 2 Q2R_plus.
    rewrite Rinv_plus_div_sqrt2.
    transitivity ((Q2R q_den_terms + Q2R (- root2_den_terms) / √ 2) * / Q2R den_fact)%R.
    1: {
      rewrite 2 Rdiv_unfold, Rmult_plus_distr_r.
      rewrite !(Rmult_comm _ (/√2)), Rmult_assoc.
      rewrite 2 Q2R_div', Q2R_opp.
      lra.
    }
    f_equal.
    + f_equal; [|f_equal]; [f_equiv; unfold q_den_terms; lra|].
      rewrite <- Q2R_opp.
      f_equiv.
      unfold root2_den_terms.
      lra.
    + f_equal.
      rewrite <- 2 Q2R_mult.
      replace 2%R with (Q2R 2) by lra.
      rewrite <- Q2R_div', <- Q2R_minus.
      f_equiv.
      unfold den_fact, q_den_terms, root2_den_terms.
      field.
Qed.

Lemma QC2C_div q r : QC2C (q / r) = QC2C q / QC2C r.
Proof.
  unfold QCdiv.
  rewrite QC2C_mult, QC2C_inv; reflexivity.
Qed.

(* FIXME: Move *)
Lemma Q2QC_correct (q : Q) : QC2C (Q2QC q) = Q2R q.
Proof.
  lca.
Qed.


Definition Q2R' (q : Q) : option R :=
  let q' := Qred q in
  match Qnum q' with
  | Z0 => None
  | Zpos p =>
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with
    | true, true => (* q = 1 / 1 *) (1%R)
    | false, true => (* q = +p / 1 *) (IZR (Z.pos p))
    | true, false => (* q = 1 / _ *) (/ IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q'%R)
    end
  | Zneg p =>
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with
    | true, true => (* q = -1 / 1 *) (- 1%R)%R
    | false, true => (* q = -p / 1 *) (- IZR (Z.pos p))%R
    | true, false => (* q = -1 / _ *) (- / IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q')
    end
  end.

Hint Resolve Pos.eqb_spec Z.eqb_spec : bdestruct.

Lemma Q2R'_correct q :
  maybe (Q2R' q) 0%R = Q2R q.
Proof.
  rewrite <- (Qred_correct q) at 2.
  cbv delta [Q2R'] beta iota.
  generalize (Qred q); cbv zeta.
  clear q.
  intros q.
  destruct q as [num den].
  cbn.
  destruct num.
  - unfold Q2R. cbn; lra.
  - bdestruct (1 =? p)%positive;
    bdestruct (1 =? den)%positive;
    subst; unfold Q2R; cbn; lra.
  - bdestruct (1 =? p)%positive;
    bdestruct (1 =? den)%positive;
    subst; unfold Q2R; cbn; try lra.
    change (Z.neg p) with (- Z.pos p)%Z.
    rewrite opp_IZR.
    lra.
Qed.

Definition Q2C' (q : Q) : option C :=
  let q' := Qred q in
  match Qnum q' with
  | Z0 => None
  | Zpos p =>
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with
    | true, true => (* q = 1 / 1 *) (C1)
    | false, true => (* q = +p / 1 *) (IZR (Z.pos p))
    | true, false => (* q = 1 / _ *) Cinv (IZR (Z.pos (Qden q')))%R
    | false, false => (* general case *) (Q2R q'%R)
    end
  | Zneg p =>
    Some
    match Pos.eqb 1 p, Pos.eqb 1 (Qden q') with
    | true, true => (* q = -1 / 1 *) (Copp C1)
    | false, true => (* q = -p / 1 *) Copp (IZR (Z.pos p))%R
    | true, false => (* q = -1 / _ *) Copp (Cinv (IZR (Z.pos (Qden q')))%R)
    | false, false => (* general case *) (Q2R q')
    end
  end.

Hint Resolve Pos.eqb_spec Z.eqb_spec : bdestruct.

Lemma Q2C'_correct q :
  maybe (Q2C' q) C0 = Q2R q.
Proof.
  rewrite <- (Qred_correct q) at 2.
  cbv delta [Q2C'] beta iota.
  generalize (Qred q); cbv zeta.
  clear q.
  intros q.
  destruct q as [num den].
  cbn.
  destruct num.
  - unfold Q2R. cbn; lca.
  - bdestruct (1 =? p)%positive;
    bdestruct (1 =? den)%positive;
    subst; unfold Q2R; cbn; [|rewrite <- RtoC_inv|..]; lca.
  - bdestruct (1 =? p)%positive;
    bdestruct (1 =? den)%positive;
    subst; unfold Q2R; cbn; [|rewrite <- RtoC_inv, <- RtoC_opp|..]; try lca.
    change (Z.neg p) with (- Z.pos p)%Z.
    rewrite opp_IZR.
    lca.
Qed.

Definition omap {A B} (f : A -> B) (ma : option A) : option B :=
  match ma with
  | Some a => Some (f a)
  | None => None
  end.

Definition omap2 {A} (f : A -> A -> A) (ma ma' : option A) : option A :=
  match ma, ma' with
  | Some a, Some a' => Some (f a a')
  | Some a, None => Some a
  | None, Some a' => Some a'
  | None, None => None
  end.


Fixpoint ofold {A} (f : A -> A -> A) (mas : list (option A)) : option A :=
  match mas with
  | [] => None
  | ma :: mas => omap2 f ma (ofold f mas)
  end.

Definition QC2C' (q : QC) :=
  let '(mkQC a b c d) := q in
  let ma := (* omap RtoC *) (Q2C' a) in
  let mb := (* omap RtoC *) (Q2C' b) in
  let mc := (* omap RtoC *) (Q2C' c) in
  let md := (* omap RtoC *) (Q2C' d) in
  maybe (ofold Cplus [
    ma;
    omap (fun x => x / √2)%C mb;
    omap (fun x => x * Ci)%C mc;
    omap (fun x => x * Ci / √ 2)%C md
  ]) C0.

Lemma maybe_omap2 {A} (f : A -> A -> A) d :
  (forall a, f d a = a) -> (forall a, f a d = a) ->
  forall ma ma',
  maybe (omap2 f ma ma') d = f (maybe ma d) (maybe ma' d).
Proof.
  intros Hl Hr [a|] [a'|]; cbn; auto.
Qed.

Lemma maybe_omap {A B} d' (f : A -> B) d :
  (f d' = d) -> forall ma,
  maybe (omap f ma) d = f (maybe ma d').
Proof.
  intros Hd [a|]; cbn; auto.
Qed.

Lemma omap_omap {A B D} (f : A -> B) (g : B -> D) ma :
  omap g (omap f ma) = omap (fun x => g (f x)) ma.
Proof. now destruct ma. Qed.

Lemma QC2C'_correct q :
  QC2C' q = QC2C q.
Proof.
  destruct q as [a b c d].
  cbn.
  rewrite !(maybe_omap2 Cplus 0%R Cplus_0_l Cplus_0_r).
  (* rewrite !omap_omap. *)
  rewrite !(maybe_omap C0) by lca.
  rewrite !Q2C'_correct.
  cbn.
  pose proof sqrt2_neq_0.
  apply c_proj_eq; cbn; R_field.
Qed.


Lemma QC2C_inject_Z (z : Z) : 
  QC2C (inject_Z z) = IZR z.
Proof.
  cbn.
  unfold Q2R.
  lca.
Qed.

Lemma QC2C_Z (z : Z) : 
  QC2C (z # xH) = IZR z.
Proof.
  apply QC2C_inject_Z.
Qed.






Class ParseQC (q : QC) (c : C) := {
  parseqc : QC2C q = c
}.
Hint Mode ParseQC - ! : typeclass_instances.

Set Typeclasses Unique Instances.

#[export]
Instance parseQC_mk (qc : QC) :
  ParseQC qc qc.
Proof.
  constructor; easy.
Qed.

#[export]
Instance parseQC_mult q r c d :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q * r) (c * d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_mult, Hq, Hr.
Qed.

#[export]
Instance parseQC_div q r c d :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q / r) (c / d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_div, Hq, Hr.
Qed.

#[export]
Instance parseQC_plus q r c d :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q + r) (c + d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_plus, Hq, Hr.
Qed.

#[export]
Instance parseQC_minus q r c d :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q - r) (c - d).
Proof.
  intros [Hq] [Hr].
  constructor.
  now rewrite QC2C_minus, Hq, Hr.
Qed.

#[export]
Instance parseQC_opp q c :
  ParseQC q c -> ParseQC (-q) (-c).
Proof.
  intros [Hq].
  constructor.
  now rewrite QC2C_opp, Hq.
Qed.

#[export]
Instance parseQC_inv q c :
  ParseQC q c -> ParseQC (/ q) (/ c).
Proof.
  intros [Hq].
  constructor.
  now rewrite QC2C_inv, Hq.
Qed.


#[export]
Instance parseQC_0 :
  ParseQC (0) (C0).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_1 :
  ParseQC (1) (C1).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_2 :
  ParseQC (2) (C2).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_inv_sqrt2 :
  ParseQC (mkQC 0 1 0 0) (/√ 2).
Proof.
  constructor.
  rewrite <- RtoC_inv.
  lca.
Qed.

#[export]
Instance parseQC_Rinv_sqrt2 :
  ParseQC (mkQC 0 1 0 0) (Rinv (√ 2)).
Proof.
  constructor.
  lca.
Qed.

#[export]
Instance parseQC_1_div_sqrt2 :
  ParseQC (mkQC 0 1 0 0) (C1 / √ 2).
Proof.
  constructor.
  rewrite <- RtoC_div.
  lca.
Qed.

#[export]
Instance parseQC_sqrt2 :
  ParseQC (mkQC 0 2 0 0) (√ 2).
Proof.
  constructor.
  cbn.
  apply c_proj_eq; [|cbn; lra].
  cbn.
  rewrite Q2R_0.
  replace (Q2R 2) with (2%R) by lra.
  R_field_simplify; nonzero.
Qed.


#[export]
Instance parseQC_Ropp q (r : R) :
  ParseQC q r ->
  ParseQC (QCopp q) (Ropp r).
Proof.
  intros [Hq].
  constructor.
  rewrite QC2C_opp, Hq.
  lca.
Qed.

#[export]
Instance parseQC_Rmult q r (c d : R) :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q * r) (Rmult c d).
Proof.
  rewrite RtoC_mult.
  apply _.
Qed.

#[export]
Instance parseQC_Rdiv q r (c d : R) :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q / r) (Rdiv c d).
Proof.
  rewrite RtoC_div.
  apply _.
Qed.

#[export]
Instance parseQC_Rplus q r (c d : R) :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q + r) (Rplus c d).
Proof.
  rewrite RtoC_plus.
  apply _.
Qed.

#[export]
Instance parseQC_Rminus q r (c d : R) :
  ParseQC q c -> ParseQC r d ->
  ParseQC (q - r) (Rminus c d).
Proof.
  rewrite RtoC_minus.
  apply _.
Qed.

#[export]
Instance parseQC_Rinv q (c : R) :
  ParseQC q c -> ParseQC (/ q) (Rinv c).
Proof.
  rewrite RtoC_inv.
  apply _.
Qed.

#[export]
Instance parseQC_Ci : ParseQC (mkQC 0 0 1 0) Ci.
Proof.
  constructor.
  lca.
Qed.

#[export] Instance parseQC_Cpow n qc c :
  ParseQC qc c ->
  ParseQC (Nat.iter n (QCmult qc) 1) (c ^ n).
Proof.
  unfold Nat.iter. 
  intros Hqc.
  induction n; [apply _|].
  cbn; apply _.
Qed.

#[export] Instance parseQC_pow n qc (r : R) :
  ParseQC qc r ->
  ParseQC (Nat.iter n (QCmult qc) 1) (pow r n).
Proof.
  unfold Nat.iter. 
  intros Hqc.
  induction n; [apply _|].
  cbn. apply _.
Qed.


#[export]
Instance parseQC_IZR (z : Z) :
  ParseQC (z # xH) (IZR z).
Proof.
  constructor.
  cbn.
  unfold Q2R.
  lca.
Qed.

#[export]
Instance parseQC_INR (n : nat) :
  ParseQC (Z.of_nat n # xH) (INR n).
Proof.
  rewrite INR_IZR_INZ.
  apply _.
Qed.

#[export]
Instance parseQC_Q (q : Q) :
  ParseQC q (Q2R q).
Proof.
  constructor.
  lca.
Qed.


Unset Typeclasses Unique Instances.


Lemma solve_C_eq qc qc' c c' :
  ParseQC qc c -> ParseQC qc' c' ->
  QCeqb qc qc' = true ->
  c = c'.
Proof.
  intros [<-] [<-].
  now intros ->%QCeqb_eq.
Qed.




End Rops.
End QC2C.

Coercion QC2C : QC >-> C.

From TensorRocq Require Import Aux_stdpp.
From stdpp Require Import tactics.

Ltac solve_C_eq :=
  apply (solve_C_eq _ _ _ _ _ _); [vm_compute; reflexivity].

#[export] Instance QCinhab : Inhabited QC := populate (mkQC 0 0 0 0).


Definition QCexpPI4 (z : Z) : QC :=
  [mkQC 1 0 0 0; mkQC 0 1 0 1; mkQC 0 0 1 0;
    mkQC 0 (-1) 0 1; mkQC (-1) 0 0 0;
    mkQC 0 (-1) 0 (-1); mkQC 0 0 (-1) 0;
    mkQC 0 1 0 (-1)] !!! Z.to_nat (Z.modulo z 8).


Lemma QC2C_QCexpPI4 (z : Z) :
  QC2C (QCexpPI4 z) =
  Cexp (IZR z * PI / 4).
Proof.
  rewrite Cexp_mod_2PI_scaled.
  rewrite <- (Z2Nat.id (z mod (2 * 4))) by (apply numbers.Z.mod_pos; compute_done).
  rewrite <- INR_IZR_INZ.
  assert (Hz : (Z.to_nat (z mod (2 * 4)) < 8)%nat) by (
    enough ((z mod (2 * 4)) < 8)%Z by lia; apply Z.mod_pos_bound; compute_done).

  revert Hz.
  unfold QCexpPI4.
  change (2*4)%Z with 8%Z.
  generalize (Z.to_nat (z mod 8)) as n.
  intros [|[|[|[|[|[|[|[|]]]]]]]]; [..|lia];
  intros _; cbn -[QC2C].
  - rewrite Rmult_0_l, Rdiv_0_l, Cexp_0.
    solve_C_eq.
  - rewrite Rmult_1_l, Cexp_PI4.
    solve_C_eq.
  - replace (_ / 4)%R with (PI / 2)%R by lra.
    rewrite Cexp_PI2.
    solve_C_eq.
  - replace (_ / 4)%R with (3 * PI / 4)%R by lra.
    rewrite Cexp_3PI4.
    solve_C_eq.
  - replace (_ / 4)%R with (PI)%R by lra.
    rewrite Cexp_PI.
    solve_C_eq.
  - replace (_ / 4)%R with (5 * PI / 4)%R by lra.
    rewrite Cexp_5PI4.
    solve_C_eq.
  - replace (_ / 4)%R with (3 * PI / 2)%R by lra.
    rewrite Cexp_3PI2.
    solve_C_eq.
  - replace (_ / 4)%R with (7 * PI / 4)%R by lra.
    rewrite Cexp_7PI4.
    solve_C_eq.
Qed.

From TensorRocq Require Import Algebra.

Lemma QC_ring_theory : @ring_theory QC 0%Q 1%Q QCplus QCmult QCminus QCopp QCeq.
Proof.
  split; repeat intros []; simpl; split_and!; rewrite ?Qred_correct; field.
Qed.

Lemma QC_field_theory : @field_theory QC 0%Q 1%Q QCplus QCmult 
  QCminus QCopp QCdiv QCinv QCeq.
Proof.
  split.
  - apply QC_ring_theory.
  - intros [H_1_0 _]; contradict H_1_0; lra.
  - easy.
  - intros p Hp%QCneq_0_neq_C0.
    apply eqC_QCeq.
    rewrite QC2C_mult, QC2C_inv, QC2C_Z.
    C_field.
Qed.

Lemma QC_ring_theory_ext : ring_eq_ext QCplus QCmult QCopp QCeq.
Proof.
  split; apply _.
Qed.


Lemma QC_semi_ring_theory : @semi_ring_theory QC 0%Q 1%Q QCplus QCmult QCeq.
Proof.
  split; try apply QC_ring_theory.
  intros []; simpl; split_and!; rewrite ?Qred_correct; field.
Qed.

Lemma QC_sring_theory_ext : sring_eq_ext QCplus QCmult QCeq.
Proof.
  split; apply _.
Qed.

#[export] Instance QC_SemiRing : SemiRing QC 0%Q 1%Q QCplus QCmult QCeq := {
  RSRth := QC_semi_ring_theory;
  Req_ext := QC_sring_theory_ext;
  Req_equiv := (_ : Equivalence QCeq)
}.



From TensorRocqEx Require Import ZXCore.


#[export] Instance QC2C_SRH : SemiRingHomomorphism QC2C.
Proof.
  split; [apply _|
  intros; apply (solve_C_eq _ _ _ _ _ _), QCeqb_iff; done..].
Qed.


Add Field QC : QC_field_theory.





