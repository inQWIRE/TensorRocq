Require Export ZArith Lia Aux Aux_stdpp.
Require ZifyBool.
From stdpp Require Import prelude numbers list.
From stdpp Require gmap.

Open Scope positive_scope.
Open Scope list_scope.


Definition pos_to_nat_pred (p : positive) : nat :=
  pred (Pos.to_nat p).

#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.

Definition pos_add_N (p : positive) (n : N) : positive :=
  match n with
  | N0 => p
  | Npos q => Pos.add p q
  end.

Lemma pos_add_N_to_Z n p : (Zpos (pos_add_N p n) = Zpos p + Z.of_N n)%Z.
Proof.
  unfold pos_add_N; destruct n; lia.
Qed.


Definition pos_sub_N (p : positive) (n : N) : positive :=
  match n with
  | N0 => p
  | Npos q => Pos.sub p q
  end.

Lemma pos_sub_N_to_Z n p : N.lt n (Npos p) ->
  (Zpos (pos_sub_N p n) = Zpos p - Z.of_N n)%Z.
Proof.
  unfold pos_sub_N; destruct n; lia.
Qed.

(* FIXME: Move *)
#[global]
Program Instance Op_pos_to_nat_pred : ZifyClasses.UnOp pos_to_nat_pred :=
  { TUOp x := (x - 1)%Z }.
Next Obligation.
  cbn.
  unfold pos_to_nat_pred.
  intros; lia.
Qed.
Add Zify UnOp Op_pos_to_nat_pred.

#[global]
Program Instance Op_pos_add_N : ZifyClasses.BinOp pos_add_N :=
  { TBOp x y := (x + y)%Z }.
Next Obligation.
  cbn.
  intros.
  apply pos_add_N_to_Z.
Qed.
Add Zify BinOp Op_pos_add_N.

#[global]
Program Instance Op_pos_sub_N : ZifyClasses.BinOp pos_sub_N :=
  { TBOp x y := Z.max 1 (x - y)%Z }.
Next Obligation.
  cbn.
  intros.
  unfold pos_sub_N.
  destruct m; lia.
Qed.
Add Zify BinOp Op_pos_sub_N.


(* FIXME: Move *)
Section lengthN.

Local Open Scope N_scope.

Fixpoint lengthN {A} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: l => N.succ (lengthN l)
  end.
Lemma lengthN_correct {A} (l : list A) :
  N.to_nat (lengthN l) = length l.
Proof. induction l; cbn; lia. Qed.
Lemma lengthN_correct_rev {A} (l : list A) :
  lengthN l = N.of_nat (length l).
Proof. rewrite <- lengthN_correct; lia. Qed.
Lemma lengthN_app {A} (l l' : list A) :
  lengthN (l ++ l') = lengthN l + lengthN l'.
Proof.
  now rewrite 3 lengthN_correct_rev, length_app, Nat2N.inj_add.
Qed.

End lengthN.


Fixpoint pseq_aux (start : positive) (len : positive) : list positive :=
  match len with
  | 1 => [start]
  | p~0 =>
    pseq_aux start p ++ pseq_aux (Pos.add p start) p
  | p~1 =>
    start :: (pseq_aux (Pos.succ start) p)
    ++ pseq_aux (Pos.succ (Pos.add p start)) p
  end.

Definition pseq (start : positive) (len : N) : list positive :=
  match len with
  | N0 => []
  | Npos p => pseq_aux start p
  end.

Lemma lengthN_pseq_aux start len :
  lengthN (pseq_aux start len) = N.pos len.
Proof.
  revert start;
  induction len; intros start.
  - cbn.
    rewrite lengthN_app, 2 IHlen.
    lia.
  - cbn.
    rewrite lengthN_app, 2 IHlen.
    lia.
  - reflexivity.
Qed.

Lemma lengthN_pseq start len :
  lengthN (pseq start len) = len.
Proof.
  destruct len; [reflexivity|apply lengthN_pseq_aux].
Qed.

Lemma length_pseq_aux start len :
  length (pseq_aux start len) = Pos.to_nat len.
Proof.
  now rewrite <- lengthN_correct, lengthN_pseq_aux.
Qed.

Lemma length_pseq start len :
  length (pseq start len) = N.to_nat len.
Proof.
  now rewrite <- lengthN_correct, lengthN_pseq.
Qed.

Lemma elem_of_pseq_aux start len p :
  p ∈ pseq_aux start len <-> start <= p < start + len.
Proof.
  revert p start; induction len; intros p start; cbn.
  - rewrite elem_of_cons, elem_of_app, 2 IHlen.
    lia.
  - rewrite elem_of_app, 2 IHlen.
    lia.
  - rewrite elem_of_list_singleton.
    lia.
Qed.

Lemma elem_of_pseq start len p :
  p ∈ pseq start len <-> start <= p < pos_add_N start len.
Proof.
  destruct len; [|apply elem_of_pseq_aux].
  cbn.
  rewrite elem_of_nil.
  lia.
Qed.

Lemma NoDup_pseq_aux start len :
  NoDup (pseq_aux start len).
Proof.
  revert start; induction len; intros start; cbn.
  - rewrite NoDup_cons.
    split; [by rewrite not_elem_of_app, 2 elem_of_pseq_aux; lia|].
    apply NoDup_app.
    split_and!; trivial.
    intros p.
    by rewrite 2 elem_of_pseq_aux; lia.
  - apply NoDup_app.
    split_and!; trivial.
    intros p.
    by rewrite 2 elem_of_pseq_aux; lia.
  - apply NoDup_singleton.
Qed.

Lemma NoDup_pseq start len :
  NoDup (pseq start len).
Proof.
  destruct len; [constructor|apply NoDup_pseq_aux].
Qed.

Lemma lookup_pseq_aux start len n :
  pseq_aux start len !! n =
    if decide (n < Pos.to_nat len)%nat then
      Some (pos_add_N start (N.of_nat n))
    else None.
Proof.
  revert n start; induction len; intros n start; cbn.
  - destruct n; [now rewrite decide_True by lia|].
    cbn.
    setoid_rewrite lookup_app.
    rewrite IHlen.
    case_decide as Hsmall.
    + rewrite decide_True by lia.
      f_equal; lia.
    + rewrite IHlen.
      rewrite length_pseq_aux.
      case_decide as Hsm';
      [rewrite decide_True by lia|rewrite decide_False by lia];
      f_equal; lia.
  - setoid_rewrite lookup_app.
    rewrite IHlen.
    case_decide as Hsmall.
    + rewrite decide_True by lia.
      f_equal; lia.
    + rewrite IHlen.
      rewrite length_pseq_aux.
      case_decide as Hsm';
      [rewrite decide_True by lia|rewrite decide_False by lia];
      f_equal; lia.
  - rewrite list_lookup_singleton.
    destruct n; reflexivity.
Qed.


Lemma lookup_pseq start len n :
  pseq start len !! n =
    if decide (n < N.to_nat len)%nat then
      Some (pos_add_N start (N.of_nat n))
    else None.
Proof.
  destruct len; [now destruct n; reflexivity|].
  apply lookup_pseq_aux.
Qed.

Lemma lookup_pseq_1 len n :
  pseq 1 len !! n =
    if decide (n < N.to_nat len)%nat then
      Some (Pos.of_succ_nat n)
    else None.
Proof.
  rewrite lookup_pseq.
  case_decide; [|reflexivity].
  f_equal; lia.
Qed.

Lemma lookup_pseq_1_lt len n :
  (n < N.to_nat len)%nat ->
  pseq 1 len !! n =
    Some (Pos.of_succ_nat n).
Proof.
  rewrite lookup_pseq_1.
  intros; now apply decide_True.
Qed.

Lemma lookup_pseq_1_pos_lt (len : N) (p : positive) :
  (N.pos p <= len)%N ->
  pseq 1 len !! (p :>nat) =
    Some p.
Proof.
  intros Hp.
  rewrite lookup_pseq_1_lt by lia.
  f_equal; lia.
Qed.

Lemma elem_of_pseq_1 len p :
  p ∈ pseq 1 len <-> (p < N.succ_pos len).
Proof.
  rewrite elem_of_pseq; lia.
Qed.

(* FIXME: Move *)
Definition posperm (p : positive) (f : positive -> positive) : Prop :=
  f <$> pseq 1 (Pos.pred_N p) ≡ₚ pseq 1 (Pos.pred_N p).

Lemma posperm_inj n f :
  posperm n f ->
  (forall p q, p < n -> q < n -> f p = f q -> p = q).
Proof.
  intros Hf p q Hp Hq Hfpq.
  apply dec_stable; intros Hne.
  generalize (NoDup_pseq 1 (Pos.pred_N n)).
  rewrite <- Hf.
  intros Hij'.
  pose proof (fun i j x => NoDup_lookup _ i j x Hij') as Hij.
  specialize (Hij p q (f p)).
  rewrite 2 list_lookup_fmap in Hij.
  rewrite 2 lookup_pseq_1_pos_lt in Hij by lia.
  specialize (Hij eq_refl (f_equal Some (eq_sym Hfpq))).
  lia.
Qed.

Lemma posperm_surj n f :
  posperm n f ->
  forall p, p < n -> exists q, q < n /\ f q = p.
Proof.
  intros Hf p Hp.
  assert (Hpin : p ∈ pseq 1 (Pos.pred_N n)) by now rewrite elem_of_pseq; lia.
  rewrite <- Hf in Hpin.
  apply elem_of_list_fmap in Hpin as (q & Hfq & Hq%elem_of_pseq).
  exists q.
  split; [lia|easy].
Qed.

Lemma posperm_bounded n f :
  posperm n f ->
  forall p, p < n -> f p < n.
Proof.
  intros Hf p Hp.
  assert (Hpin : f p ∈ f <$> pseq 1 (Pos.pred_N n)) by
    now apply elem_of_list_fmap_1, elem_of_pseq; lia.
  rewrite Hf, elem_of_pseq in Hpin.
  lia.
Qed.


Lemma surj_inj_bounded_posperm n f :
  (forall p, p < n -> exists q, q < n /\ f q = p) ->
  (forall p q, p < n -> q < n -> f p = f q -> p = q) ->
  (forall p, p < n -> f p < n) ->
  posperm n f.
Proof.
  intros Hsurj Hinj Hbdd.
  apply NoDup_Permutation; [apply NoDup_fmap_2_strong| |];
  [|apply NoDup_pseq..|].
  - setoid_rewrite elem_of_pseq.
    intros ? ? ? ?; apply Hinj; lia.
  - intros p.
    rewrite elem_of_list_fmap.
    setoid_rewrite elem_of_pseq.
    replace (pos_add_N _ _) with n by lia.
    split.
    + intros (q & -> & Hq); specialize (Hbdd q); lia.
    + intros [_ Hp].
      destruct (Hsurj _ Hp) as (q & Hq & Hfq).
      exists q.
      split; [auto|lia].
Qed.

Lemma pos_lt_succ_case p q : p < Pos.succ q <-> p = q \/ p < q.
Proof.
  lia.
Qed.

Lemma NoDup_fmap_1_strong {A B} (f : A -> B) (l : list A) :
  NoDup (f <$> l) ->
  forall a b, a ∈ l -> b ∈ l -> f a = f b -> a = b.
Proof.
  rewrite NoDup_alt.
  intros Hdup a b
    (i & Ha)%elem_of_list_lookup (j & Hb)%elem_of_list_lookup Hfab.
  specialize (Hdup i j (f a)).
  rewrite 2 list_lookup_fmap in Hdup.
  tspecialize Hdup by now rewrite Ha.
  tspecialize Hdup by now rewrite Hb, Hfab.
  subst.
  congruence.
Qed.

Lemma NoDup_subseteq_same_length_Permutation {A} (l l' : list A) :
  NoDup l' -> l' ⊆ l -> length l' = length l ->
  l ≡ₚ l'.
Proof.
  intros Hl'; revert l;
  induction Hl' as [|a l' IHl']; [now intros []|].
  intros l Hl.
  specialize (Hl a ltac:(constructor)) as Hal.
  apply elem_of_list_split in Hal as (l1 & l2 & ->).
  specialize (IHHl' (l1 ++ l2)).
  tspecialize IHHl'.
  - intros b Hb.
    assert (b <> a) by congruence.
    specialize (Hl _ (elem_of_list_further _ _ _ Hb)).
    rewrite elem_of_app, elem_of_cons in Hl.
    rewrite elem_of_app.
    tauto.
  - simpl_list; cbn.
    intros Heq.
    rewrite <- IHHl' by now simpl_list; lia.
    solve_Permutation.
Qed.


Lemma surj_is_posperm n f :
  (forall p, p < n -> exists q, q < n /\ f q = p) ->
  posperm n f.
Proof.
  intros Hsurj.
  apply NoDup_subseteq_same_length_Permutation.
  - apply NoDup_pseq.
  - intros p Hp%elem_of_pseq.
    specialize (Hsurj p ltac:(lia)) as (q & Hq & Hfq).
    apply elem_of_list_lookup.
    exists q.
    rewrite list_lookup_fmap, lookup_pseq_1_pos_lt by lia.
    now subst p.
  - now rewrite length_fmap.
Qed.


Lemma pos_surj_is_inj_bounded n f :
  (forall p, p < n -> exists q, q < n /\ f q = p) ->
  (forall p q, p < n -> q < n -> f p = f q -> p = q) /\
  (forall p, p < n -> f p < n).
Proof.
  intros ?%surj_is_posperm.
  split; [now apply posperm_inj|now apply posperm_bounded].
Qed.

Lemma posperm_iff_surj n f :
  posperm n f <-> forall p, p < n -> exists q, q < n /\ f q = p.
Proof.
  split; [apply posperm_surj|apply surj_is_posperm].
Qed.

Lemma posperm_id n : posperm n id.
Proof.
  now hnf; rewrite list_fmap_id.
Qed.

Lemma posperm_compose n f g : posperm n f -> posperm n g ->
  posperm n (g ∘ f).
Proof.
  unfold posperm.
  intros Hf Hg.
  now rewrite list_fmap_compose, Hf, Hg.
Qed.

Definition posperm_inv n f (p : positive) : positive :=
  default p $ head (filter (λ q, f q = p) (pseq 1 (Pos.pred_N n))).

Lemma posperm_inv_spec n f p q : posperm n f -> p < n ->
  posperm_inv n f p = q <-> q < n /\ f q = p.
Proof.
  intros Hf Hp.
  unfold posperm_inv.
  pose proof Hf as Hfsurj.
  rewrite posperm_iff_surj in Hfsurj.
  specialize (Hfsurj _ Hp) as (q' & Hq' & Hfq').
  match goal with
  |- context [head ?l] =>
    pose proof (head_is_Some l).2 as Hne
  end.
  tspecialize Hne. 1:{
    intros Hfilt.
    pose proof (filter_nil_not_elem_of _ _ q' Hfilt Hfq') as Hq'nin.
    rewrite elem_of_pseq in Hq'nin.
    lia.
  }
  destruct Hne as [q'' Hq''].
  rewrite Hq''.
  apply head_Some_elem_of in Hq'' as
    [Hfq'' Hq''%elem_of_pseq]%elem_of_list_filter.
  cbn.
  split.
  - now intros <-; lia.
  - intros [Hq Hfqp].
    revert Hfq''; rewrite <- Hfqp.
    apply (posperm_inj _ _ Hf); lia.
Qed.


Lemma posperm_inv_linv n f p : posperm n f -> p < n ->
  posperm_inv n f (f p) = p.
Proof.
  intros Hf Hp.
  rewrite posperm_inv_spec by (easy || eapply posperm_bounded; eauto).
  easy.
Qed.

Lemma posperm_inv_bounded n f p : p < n -> posperm_inv n f p < n.
Proof.
  intros Hp.
  unfold posperm_inv.
  destruct (head _) eqn:Hhd; [|easy].
  cbn.
  apply head_Some_elem_of, elem_of_list_filter in Hhd as [_ ?%elem_of_pseq].
  lia.
Qed.

Lemma posperm_inv_rinv n f p : posperm n f -> p < n ->
  f (posperm_inv n f p) = p.
Proof.
  intros Hf Hp.
  now apply (posperm_inv_spec n f p); [easy..|].
Qed.

Lemma posperm_inv_posperm n f : posperm n f -> posperm n (posperm_inv n f).
Proof.
  intros Hf.
  apply surj_is_posperm.
  intros p Hp.
  exists (f p).
  split; [eapply posperm_bounded; eauto|auto using posperm_inv_linv].
Qed.

Definition make_pwf (n : positive) (f : positive -> positive) p :=
  if decide (n <= p) then p else f p.

Arguments make_pwf _ _ _/.


Lemma make_pwf_posperm_inj n f : posperm n f ->
  Inj eq eq (make_pwf n f).
Proof.
  intros Hf.
  specialize (posperm_inj _ _ Hf) as Hfinj.
  specialize (posperm_bounded _ _ Hf) as Hfbdd.
  intros p q.
  unfold make_pwf.
  case_decide as Hp; case_decide as Hq; [easy|..|apply Hfinj; lia].
  - pose proof (Hfbdd q); lia.
  - pose proof (Hfbdd p); lia.
Qed.




Lemma posperm_of_bounded_inj n f :
  (forall p, p < n -> f p < n) ->
  (forall p q, p < n -> q < n -> f p = f q -> p = q) ->
  posperm n f.
Proof.
  intros Hbdd Hinj.
  hnf.
  symmetry.
  apply NoDup_subseteq_same_length_Permutation.
  - apply NoDup_fmap_2_strong; [|apply NoDup_pseq].
    intros p q Hp%elem_of_pseq_1 Hq%elem_of_pseq_1.
    apply Hinj; lia.
  - intros _ (p & -> & Hp%elem_of_pseq_1)%elem_of_list_fmap.
    rewrite elem_of_pseq_1.
    specialize (Hbdd p); lia.
  - now rewrite length_fmap.
Qed.

Lemma posperm_of_bounded_linv n f g :
  (forall p, p < n -> f p < n) ->
  (forall p, p < n -> g (f p) = p) ->
  posperm n f.
Proof.
  intros Hbdd Hinj.
  apply posperm_of_bounded_inj; [apply Hbdd|].
  intros p q Hp Hq Heq%(f_equal g).
  now rewrite 2 Hinj in Heq.
Qed.

Lemma posperm_change_dims m {n f} : posperm m f -> n = m ->
  posperm n f.
Proof. now intros ? ->. Qed.

Definition pbig_swap (n m : N) (p : positive) :=
  if decide (Npos p <= m)%N then
    pos_add_N p n
  else
    pos_sub_N p m.

Lemma pbig_swap_posperm (n m : N) :
  posperm (N.succ_pos (n + m))%N (pbig_swap n m).
Proof.
  apply posperm_of_bounded_linv with
    (pbig_swap m n).
  - unfold pbig_swap.
    intros; case_decide; lia.
  - unfold pbig_swap.
    intros; repeat case_decide; lia.
Qed.

(* FIXME: Move *)
Notation lengthP l := (N.succ_pos (lengthN l)).


Lemma pbig_swap_posperm' nm (n m : N) :
  nm = N.succ_pos (n + m) ->
  posperm nm (pbig_swap n m).
Proof.
  intros ->; apply pbig_swap_posperm.
Qed.

Lemma posperm_ext n f g :
  (forall p, p < n -> f p = g p) ->
  posperm n f <-> posperm n g.
Proof.
  intros Hfg.
  unfold posperm.
  f_equiv.
  apply eq_reflexivity.
  apply list_fmap_ext; intros _ p Hp%elem_of_list_lookup_2%elem_of_pseq_1.
  apply Hfg; lia.
Qed.

Definition perm_posperm (ps : list positive) (p : positive) : positive :=
  ps !!! (p :> nat).

Lemma pseq_aux_to_seq start len :
  pseq_aux start len =
  Pos.of_succ_nat <$> seq start (Pos.to_nat len).
Proof.
  revert start; induction len; intros start.
  - cbn.
    replace (Pos.to_nat _) with (S (Pos.to_nat len + Pos.to_nat len)) by lia.
    cbn.
    rewrite seq_app.
    f_equal; [lia|].
    rewrite 2 IHlen, <- fmap_app.
    repeat first [lia | f_equal].
  - replace (Pos.to_nat _) with (Pos.to_nat len + Pos.to_nat len)%nat by lia.
    rewrite seq_app.
    cbn.
    rewrite 2 IHlen, <- fmap_app.
    repeat first [lia | f_equal].
  - change (Pos.to_nat 1) with 1%nat.
    cbn.
    f_equal; lia.
Qed.

Lemma pseq_to_seq start len :
  pseq start len =
  Pos.of_succ_nat <$> seq start (N.to_nat len).
Proof.
  destruct len; [reflexivity|apply pseq_aux_to_seq].
Qed.

Lemma perm_posperm_posperm n ps :
  ps ≡ₚ pseq 1 (Pos.pred_N n) -> posperm n (perm_posperm ps).
Proof.
  unfold posperm.
  intros Hps.
  rewrite <- Hps at 2.
  apply Permutation_length in Hps as Hlen.
  rewrite length_pseq in Hlen.
  apply eq_reflexivity.
  apply (list_eq_same_length _ _ _ eq_refl);
  [now rewrite length_fmap, length_pseq|].
  intros i x y Hi.
  rewrite list_lookup_fmap, lookup_pseq_1_lt by lia.
  cbn.
  unfold perm_posperm.
  rewrite list_lookup_total_alt.
  replace (pos_to_nat_pred _) with i by lia.
  destruct (ps !! i); cbn; congruence.
Qed.


(* Lemma perm_posperm_posperm_inv n ps :
  lengthP ps <= n ->
  posperm n (perm_posperm ps) -> ps ≡ₚ pseq 1 (Pos.pred_N n).
Proof.
  intros Hlen.
  unfold posperm.
  intros Hperm.
  assert (Hleneq : lengthP ps = n). 1:{
    enough (~ (lengthP ps < n))
  } *)


Lemma perm_posperm_posperm_iff n ps :
  lengthP ps = n ->
  posperm n (perm_posperm ps) <-> ps ≡ₚ pseq 1 (Pos.pred_N n).
Proof.
  intros Hlen.
  split; [|apply perm_posperm_posperm].
  unfold posperm.
  intros Hequiv.
  rewrite <- Hequiv.
  symmetry.
  (* apply Permutation_length in Hps as Hlen. *)
  (* rewrite length_pseq in Hlen. *)
  apply eq_reflexivity.
  rewrite lengthN_correct_rev in Hlen.
  apply (list_eq_same_length _ _ _ eq_refl);
  [rewrite length_fmap, length_pseq; lia|].
  intros i x y Hi.
  rewrite list_lookup_fmap, lookup_pseq_1_lt by lia.
  cbn.
  unfold perm_posperm.
  rewrite list_lookup_total_alt.
  replace (pos_to_nat_pred _) with i by lia.
  destruct (ps !! i); cbn; congruence.
Qed.

Lemma posperm_ind n (P : (positive -> positive) -> Prop)
  (Hresp : forall f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P f -> P g)
  (HPperm : forall ps, ps ≡ₚ pseq 1 (Pos.pred_N n) ->
    P (perm_posperm ps)) :
  forall f, posperm n f -> P f.
Proof.
  intros f Hf.
  specialize (HPperm _ Hf).
  revert HPperm.
  eenough (Hfun: _);
  [apply (fun Hp => Hresp _ _ Hp Hf Hfun)|].
  - revert Hf.
    apply posperm_ext, Hfun.
  - intros p Hp.
    cbn.
    unfold perm_posperm.
    erewrite list_lookup_total_fmap by now rewrite length_pseq; lia.
    f_equal.
    rewrite list_lookup_total_alt.
    rewrite lookup_pseq_1.
    rewrite decide_True by lia.
    cbn.
    lia.
Qed.




(* FIXME: Move *)
Lemma lengthN_reverse {A} (l : list A) :
  lengthN (reverse l) = lengthN l.
Proof.
  now rewrite lengthN_correct_rev, length_reverse, <- lengthN_correct_rev.
Qed.


(* FIXME: Move *)
Lemma default_is_Some_ext {B} (d d' : B) (mb mb' : option B) :
  is_Some mb -> is_Some mb' ->
  (forall b b', mb = Some b -> mb' = Some b' -> b = b') ->
  default d mb = default d' mb'.
Proof.
  intros [? ->] [? ->]; auto.
Qed.
Lemma pos_to_nat_pred_to_pos p :
  Pos.of_succ_nat (pos_to_nat_pred p) = p.
Proof. lia. Qed.

Notation posbdd n f :=
  (forall p : positive, Pos.lt p n -> Pos.lt (f p) n).

Definition ppermute_aux {A} (f : positive -> positive) (l : list A) : option (list A) :=
  join_list ((λ i, l !! (f i :> nat)) <$> pseq 1 (lengthN l)).

Definition ppermute {A} (f : positive -> positive) (l : list A) : list A :=
  default l (ppermute_aux f l).

Section ppermute.

Context {A : Type}.

Implicit Types l : list A.

Lemma length_ppermute f l : length (ppermute f l) = length l.
Proof.
  unfold ppermute, ppermute_aux.
  destruct (join_list _) as [jl|] eqn:Hjl; [|reflexivity].
  cbn.
  apply join_list_Some in Hjl.
  apply (f_equal length) in Hjl.
  now rewrite 2 length_fmap, length_pseq, lengthN_correct in Hjl.
Qed.

Lemma lengthN_ppermute f l : lengthN (ppermute f l) = lengthN l.
Proof.
  rewrite 2 lengthN_correct_rev, length_ppermute.
  reflexivity.
Qed.

Lemma ppermute_aux_is_Some_iff_bdd f l :
  is_Some (ppermute_aux f l) <->
  (forall p, p < lengthP l -> f p < lengthP l).
Proof.
  unfold ppermute_aux.
  rewrite join_list_is_Some.
  rewrite elem_of_list_fmap.
  split.
  - intros Hnone.
    pose proof (fun y Hy Hy' => Hnone (ex_intro _ y (conj (eq_sym Hy) Hy')))
      as Hin.
    intros p Hp.
    apply dec_stable; intros Hge.
    specialize (Hin p).
    rewrite lookup_ge_None, elem_of_pseq_1, <- lengthN_correct in Hin.
    lia.
  - intros Hbdd.
    intros (p & Hfp%eq_sym%lookup_ge_None & Hy%elem_of_pseq_1).
    rewrite <- lengthN_correct in Hfp.
    specialize (Hbdd p).
    lia.
Qed.


Lemma ppermute_aux_Some_lookup f l l' :
  ppermute_aux f l = Some l' ->
  forall i, (i < length l)%nat ->
  l' !! i = l !! (f (Pos.of_succ_nat i) :> nat).
Proof.
  intros Hjl.
  apply join_list_Some in Hjl.
  intros i Hi.
  specialize (f_equal (.!! i) Hjl).
  rewrite 2 list_lookup_fmap.
  rewrite lookup_pseq, lengthN_correct.
  rewrite decide_True by easy.
  cbn.
  replace (pos_to_nat_pred _) with (f (Pos.of_succ_nat i) :> nat) by
    repeat first [lia|f_equal].
  do 2 destruct (_ !! _); cbn; congruence.
Qed.


Lemma ppermute_aux_None_iff_not_bdd f l :
  ppermute_aux f l = None <->
  (exists p, p < lengthP l /\ lengthP l <= f p).
Proof.
  split.
  - rewrite eq_None_not_Some, ppermute_aux_is_Some_iff_bdd.
    setoid_rewrite <- elem_of_pseq_1.
    rewrite <- Forall_forall.
    intros Hex%not_Forall_Exists%Exists_exists; [|apply _].
    cbn in Hex.
    setoid_rewrite elem_of_pseq_1 in Hex.
    destruct Hex as (p & Hp & Hfp).
    exists p.
    rewrite elem_of_pseq_1.
    lia.
  - intros (p & Hp & Hfp).
    unfold ppermute.
    enough (ppermute_aux f l = None) as -> by easy.
    apply eq_None_not_Some.
    rewrite ppermute_aux_is_Some_iff_bdd.
    intros Hbdd.
    specialize (Hbdd p).
    lia.
Qed.




Lemma lookup_ppermute_alt_bdd f l :
  (forall p, p < N.succ_pos (lengthN l) -> f p < N.succ_pos (lengthN l)) ->
  forall i, (i < length l)%nat ->
  ppermute f l !! i = l !! (f (Pos.of_succ_nat i) :> nat).
Proof.
  intros [l' Hl']%ppermute_aux_is_Some_iff_bdd.
  unfold ppermute.
  rewrite Hl'.
  now apply ppermute_aux_Some_lookup.
Qed.


Lemma lookup_ppermute_alt_bdd_wf f l :
  (forall p, p < N.succ_pos (lengthN l) -> f p < N.succ_pos (lengthN l)) ->
  (forall p, N.succ_pos (lengthN l) <= p -> N.succ_pos (lengthN l) <= f p) ->
  forall i,
  ppermute f l !! i = l !! (f (Pos.of_succ_nat i) :> nat).
Proof.
  intros Hinj HWF i.
  destruct_decide (decide (i < length l)%nat) as Hi;
  [now apply lookup_ppermute_alt_bdd|].
  rewrite 2 lookup_ge_None_2.
  - reflexivity.
  - specialize (HWF (Pos.of_succ_nat i)); rewrite <- lengthN_correct in *; lia.
  - rewrite length_ppermute.
    lia.
Qed.

Lemma ppermute_not_bdd f l :
  (exists p, p < lengthP l /\ lengthP l <= f p) ->
  ppermute f l = l.
Proof.
  intros (p & Hp & Hfp).
  unfold ppermute.
  enough (ppermute_aux f l = None) as -> by easy.
  apply eq_None_not_Some.
  rewrite ppermute_aux_is_Some_iff_bdd.
  intros Hbdd.
  specialize (Hbdd p).
  lia.
Qed.


Lemma pp_bounded_case f l :
  {(forall p, p < lengthP l -> f p < lengthP l)} +
  {(exists p, p < lengthP l /\ lengthP l <= f p)}.
Proof.
  destruct (ppermute_aux f l) as [l'|] eqn:Hl'; [left | right].
  - apply mk_is_Some in Hl'.
    now rewrite ppermute_aux_is_Some_iff_bdd in Hl'.
  - apply ppermute_aux_None_iff_not_bdd in Hl'.
    easy.
Qed.

Lemma ppermute_case f l :
  {(forall p, p < lengthP l -> f p < lengthP l) /\
    is_Some (ppermute_aux f l)} +
  {(exists p, p < lengthP l /\ lengthP l <= f p) /\
    ppermute_aux f l = None}.
Proof.
  destruct (ppermute_aux f l) as [l'|] eqn:Hl'; [left | right].
  - split; [|easy].
    apply mk_is_Some in Hl'.
    now rewrite ppermute_aux_is_Some_iff_bdd in Hl'.
  - apply ppermute_aux_None_iff_not_bdd in Hl'.
    easy.
Qed.

Lemma ppermute_id l : ppermute id l = l.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl); [apply length_ppermute|].
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by easy.
  unfold id.
  replace (pos_to_nat_pred _) with i by lia.
  congruence.
Qed.


Lemma posbdd_compose n f g :
  posbdd n f -> posbdd n g ->
  posbdd n (f ∘ g).
Proof.
  unfold compose; auto.
Qed.

Lemma ppermute_compose l g f :
  posbdd (lengthP l) f -> posbdd (lengthP l) g ->
  ppermute g (ppermute f l) = ppermute (f ∘ g) l.
Proof.
  intros Hf Hg.
  pose proof (lengthN_correct l).
  apply (list_eq_same_length _ _ (length l)); [now rewrite !length_ppermute..|].
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by
    now rewrite ?lengthN_ppermute, ?length_ppermute.
  rewrite lookup_ppermute_alt_bdd by
    now easy + (pose proof (Hg (Pos.of_succ_nat i)); lia).
  rewrite lookup_ppermute_alt_bdd by
    now apply posbdd_compose + lia.
  cbn.
  rewrite pos_to_nat_pred_to_pos.
  congruence.
Qed.

Lemma ppermute_permutation l f : posperm (lengthP l) f ->
  ppermute f l ≡ₚ l.
Proof.
  intros Hf.
  specialize (posperm_bounded _ _ Hf) as Hfbdd.
  rewrite Permutation_inj.
  split; [apply length_ppermute|].
  pose proof (lengthN_correct l) as HlenNl.
  exists (fun n => make_pwf (lengthP l) f (Pos.of_succ_nat n)).
  split.
  - apply (compose_inj _ eq _ (make_pwf _ _ ∘ Pos.of_succ_nat) pos_to_nat_pred);
    [|hnf; lia].
    apply (compose_inj _ eq _ Pos.of_succ_nat (make_pwf _ _));
    [hnf; lia|].
    now apply make_pwf_posperm_inj.
  - intros i.
    apply option_eq.
    intros a.
    destruct_decide (decide (i < length l)%nat) as Hismall; unfold make_pwf.
    + rewrite decide_False by lia.
      now rewrite lookup_ppermute_alt_bdd by easy.
    + rewrite decide_True by (rewrite <- lengthN_correct in Hismall; lia).
      apply Nat.nlt_ge in Hismall.
      rewrite lookup_ge_None_2 by now rewrite length_ppermute.
      apply lookup_ge_None_2 in Hismall.
      replace (pos_to_nat_pred _) with i by lia.
      rewrite Hismall.
      easy.
Qed.

Lemma ppermute_ext f g l :
  (forall p, p < N.succ_pos (lengthN l) -> f p = g p) ->
  ppermute f l = ppermute g l.
Proof.
  intros Hfg.
  unfold ppermute.
  f_equal.
  unfold ppermute_aux.
  f_equal.
  apply list_fmap_ext; intros _ p Hq%elem_of_list_lookup_2%elem_of_pseq.
  do 2 f_equal; apply Hfg; lia.
Qed.

Lemma ppermute_id' f l :
  (forall p, p < N.succ_pos (lengthN l) -> f p = p) ->
  ppermute f l = l.
Proof.
  intros Hf.
  transitivity (ppermute id l); [now apply ppermute_ext|apply ppermute_id].
Qed.




Lemma ppermute_pbig_swap_app l r :
  ppermute (pbig_swap (lengthN l) (lengthN r)) (l ++ r) = r ++ l.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_ppermute, 2 length_app, Nat.add_comm|].
  intros i x y Hi.
  rewrite length_app in Hi.
  pose proof (lengthN_correct l).
  pose proof (lengthN_correct r).
  pose proof (pbig_swap_posperm (lengthN l) (lengthN r)) as Hperm.
  specialize (posperm_bounded _ _ Hperm) as Hbdd.
  rewrite lookup_ppermute_alt_bdd by (rewrite ?length_app;
    first [lia |
    apply posperm_bounded, pbig_swap_posperm'; rewrite lengthN_app; lia]).
  unfold pbig_swap.
  case_decide as Hismall.
  - rewrite lookup_app_r by lia.
    rewrite lookup_app_l by lia.
    replace (pos_to_nat_pred _ - _)%nat with i by lia.
    congruence.
  - rewrite lookup_app_l by lia.
    rewrite lookup_app_r by lia.
    replace (pos_to_nat_pred _)%nat with (i - length r)%nat by lia.
    congruence.
Qed.


(* FIXME: Move *)
Definition reflect_posperm (n : positive)
  (f : positive -> positive) (p : positive) :=
  Pos.sub n (f p).

Lemma sub_posperm n : posperm n (Pos.sub n).
Proof.
  apply posperm_of_bounded_linv with (Pos.sub n); lia.
Qed.

Lemma reflect_posperm_posperm n f : posperm n f ->
  posperm n (reflect_posperm n f).
Proof.
  intros Hf.
  apply (posperm_compose n f (Pos.sub n));
  easy + apply sub_posperm.
Qed.

Lemma reflect_posperm_bounded n f : posbdd n (reflect_posperm n f).
Proof.
  unfold reflect_posperm; lia.
Qed.



Lemma ppermute_reflect_posperm f l : posperm (lengthP l) f ->
  ppermute (reflect_posperm (lengthP l) f) l =
  ppermute f (reverse l).
Proof.
  intros Hf.
  pose proof (lengthN_correct l).
  apply list_eq_same_length with (length l);
  [now rewrite length_ppermute, ?length_reverse..|].
  intros i x y Hi.
  specialize (posperm_bounded _ _ Hf) as Hfbdd.
  rewrite lookup_ppermute_alt_bdd by now easy + apply reflect_posperm_bounded.
  rewrite lookup_ppermute_alt_bdd by
    now rewrite length_reverse + rewrite lengthN_reverse.
  specialize (Hfbdd (Pos.of_succ_nat i)).
  rewrite reverse_lookup by lia.
  unfold reflect_posperm.
  set (j := pos_to_nat_pred _).
  set (k := (_ - _)%nat).
  enough (j = k) by congruence.
  subst j k.
  lia.
Qed.

Lemma pseq_succ start len :
  pseq start (N.succ len) =
  start :: pseq (Pos.succ start) len.
Proof.
  rewrite 2 pseq_to_seq, N2Nat.inj_succ; cbn.
  repeat first [lia | f_equal].
Qed.

Lemma pseq_succ_start start len :
  pseq (Pos.succ start) len =
  Pos.succ <$> pseq start len.
Proof.
  rewrite 2 pseq_to_seq, <- list_fmap_compose.
  replace (pos_to_nat_pred _) with (S start) by lia.
  rewrite <- fmap_S_seq, <- list_fmap_compose.
  apply list_fmap_ext; intros; cbn; lia.
Qed.

Lemma ppermute_perm_posperm_cons_1 ps (x : A) l :
  length ps = length l -> xH ∉ ps ->
  ppermute (perm_posperm (xH :: ps)) (x :: l) =
  x :: ppermute (perm_posperm (Pos.pred <$> ps)) l.
Proof.
  intros Hlen Hps.
  unfold ppermute, ppermute_aux.
  cbn.
  rewrite pseq_succ.
  rewrite fmap_cons.
  unfold perm_posperm at 1.
  change (pos_to_nat_pred 1) with O.
  cbn [lookup_total list_lookup_total].
  change (pos_to_nat_pred 1) with O.
  cbn [lookup list_lookup].
  cbn.
  set (lhs := _ <$> _).
  set (rhs := _ <$> _).
  assert (Heq : lhs = rhs). 1:{
    subst lhs rhs.
    rewrite pseq_succ_start.
    rewrite <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ p Hp%elem_of_list_lookup_2%elem_of_pseq_1.
    cbn.
    replace (pos_to_nat_pred (Pos.succ p)) with (S p) by lia.
    cbn.
    (* generalize (pos_to_nat_pred p). *)
    unfold perm_posperm.
    setoid_rewrite list_lookup_total_alt.
    rewrite list_lookup_fmap.
    destruct (ps !! _) as [v|] eqn:Hlook.
    - apply elem_of_list_lookup_2 in Hlook as Hv.
      assert (v <> xH) by congruence.
      cbn.
      rewrite (lookup_cons_ne_0 ps) by lia.
      replace (pred _) with (p :> nat) by lia.
      rewrite Hlook.
      cbn.
      rewrite (lookup_cons_ne_0 l) by lia.
      f_equal; lia.
    - apply lookup_ge_None_1 in Hlook.
      rewrite lengthN_correct_rev in Hp.
      lia.
  }
  rewrite <- Heq.
  clear rhs Heq.
  destruct (join_list lhs); reflexivity.
Qed.


Lemma ppermute_perm_posperm_2_1_pseq (a b : A) l :
  ppermute (perm_posperm (2 :: 1 :: pseq 3 (lengthN l))) (a :: b :: l) =
  b :: a :: l.
Proof.
  unfold ppermute.
  replace (ppermute_aux _ _) with (Some (b :: a :: l)); [done|].
  symmetry.
  apply join_list_Some.
  apply (list_eq_same_length _ _ _ eq_refl);
  [now rewrite 2 length_fmap, length_pseq, lengthN_correct|].
  rewrite length_fmap.
  cbn.
  rewrite 2 pseq_succ.
  intros [|[|i]] x y Hi;
  cbn.
  - cbv.
    congruence.
  - cbv.
    congruence.
  - setoid_rewrite list_lookup_fmap.
    pose proof (lengthN_correct l).
    rewrite lookup_pseq, decide_True by lia.
    cbn.
    unfold perm_posperm.
    rewrite list_lookup_total_alt.
    replace (pos_to_nat_pred (pos_add_N _ _)) with
      (S (S i)) by lia.
    cbn.
    rewrite lookup_pseq, decide_True by lia.
    cbn.
    replace (pos_add_N _ _ :> nat) with (S (S i)) by lia.
    cbn.
    destruct (l !! i); cbn; congruence.
Qed.

Definition posperm_cons (f : positive -> positive) p : positive :=
  Pos.peano_rect _ 1 (λ p _, Pos.succ (f p)) p.

Lemma posperm_cons_posperm n f :
  posperm n f -> posperm (Pos.succ n) (posperm_cons f).
Proof.
  intros Hf.
  hnf.
  replace (Pos.pred_N _) with (N.succ (Pos.pred_N n)) by lia.
  rewrite pseq_succ, pseq_succ_start.
  rewrite fmap_cons.
  f_equiv.
  rewrite <- Hf at 2.
  rewrite <- 2 list_fmap_compose.
  apply eq_reflexivity, list_fmap_ext; intros _ ? _.
  cbn.
  unfold posperm_cons.
  now rewrite Pos.peano_rect_succ.
Qed.

Definition pos_swap p : positive :=
  match p with
  | 1 => 2
  | 2 => 1
  | _ => p
  end.

Definition Zswap (z : Z) : Z :=
  match z with
  | Zpos p => Zpos (pos_swap p)
  | _ => z
  end.


#[global]
Program Instance Op_pos_swap : ZifyClasses.UnOp pos_swap :=
  { TUOp z := Zswap z }.
Next Obligation.
  reflexivity.
Qed.
(* FIXME: Move *)
#[global]
Program Instance OpSpec_Zswap : ZifyClasses.UnOpSpec Zswap :=
  { UPred x y := (x = 1 /\ y = 2 \/ x = 2 /\ y = 1 \/
    (x <= 0 \/ x > 2) /\ y = x)%Z }.
Next Obligation.
  destruct x; cbn; [lia| |lia].
  refine (match p with
    | 1 => _
    | 2 => _
    | _ => _
    end); cbn; lia.
Qed.
Add Zify UnOp Op_pos_swap.
Add Zify UnOpSpec OpSpec_Zswap.

Lemma pos_swap_posperm n : 2 < n -> posperm n pos_swap.
Proof.
  intros Hn.
  apply posperm_of_bounded_inj; intros; lia.
Qed.


Lemma posperm_ind' (P : positive -> (positive -> positive) -> Prop)
  (Hresp : forall n f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P n f -> P n g)
  (HPperm : forall n ps, ps ≡ₚ pseq 1 (Pos.pred_N n) ->
    P n (perm_posperm ps)) :
  forall n f, posperm n f -> P n f.
Proof.
  intros n f Hf.
  specialize (HPperm n _ Hf).
  revert HPperm.
  eenough (Hfun: _);
  [apply (fun Hp => Hresp _ _ _ Hp Hf Hfun)|].
  - revert Hf.
    apply posperm_ext, Hfun.
  - intros p Hp.
    cbn.
    unfold perm_posperm.
    erewrite list_lookup_total_fmap by now rewrite length_pseq; lia.
    f_equal.
    rewrite list_lookup_total_alt.
    rewrite lookup_pseq_1.
    rewrite decide_True by lia.
    cbn.
    lia.
Qed.

Lemma perm_posperm_pseq_1 n :
  forall p, p < N.succ_pos n ->
  perm_posperm (pseq 1 n) p = p.
Proof.
  intros p Hp.
  unfold perm_posperm.
  rewrite list_lookup_total_alt.
  now rewrite lookup_pseq_1_pos_lt by lia.
Qed.

Lemma posperm_ind_fn_init (P : positive -> (positive -> positive) -> Prop)
  (Hresp : forall n f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P n f -> P n g)
  (Hid : forall n, P n id)
  (Hperm : forall n ps qs, ps ≡ₚ qs ->
    ps ≡ₚ pseq 1 (Pos.pred_N n) -> qs ≡ₚ pseq 1 (Pos.pred_N n) ->
      P n (perm_posperm ps) -> P n (perm_posperm qs)) :
  forall n f, posperm n f -> P n f.
Proof.
  apply posperm_ind'; [apply Hresp|].
  assert (Hseq : forall n, P n (perm_posperm (pseq 1 (Pos.pred_N n)))). 1: {
    intros n.
    generalize (Hid n).
    apply Hresp.
    - apply posperm_id.
    - apply perm_posperm_posperm; reflexivity.
    - intros; now rewrite perm_posperm_pseq_1 by lia.
  }
  intros n ps Hps.
  apply (Hperm _ (pseq 1 (Pos.pred_N n))); auto using Permutation_sym.
Qed.

Definition pshiftd (p : positive) (q : positive) : positive :=
  if decide (p < q) then Pos.pred q else q.
Definition pshiftu (p : positive) (q : positive) : positive :=
  if decide (p <= q) then Pos.succ q else q.
Definition Zshiftd (p : Z) (q : Z) : Z :=
  if decide (p < q)%Z then Z.pred q else q.
Definition Zshiftu (p : Z) (q : Z) : Z :=
  if decide (p <= q)%Z then Z.succ q else q.

#[global]
Program Instance Op_pshiftd : ZifyClasses.BinOp pshiftd :=
  { TBOp p q := Zshiftd p q }.
Next Obligation.
  cbn.
  unfold pshiftd, Zshiftd.
  intros; do 2 case_decide; try lia.
Qed.
(* FIXME: Move *)
#[global]
Program Instance OpSpec_Zshiftd : ZifyClasses.BinOpSpec Zshiftd :=
  { BPred p q y := (p < q /\ y = q - 1 \/ q <= p /\ y = q)%Z }.
Next Obligation.
  cbn.
  unfold Zshiftd.
  intros; case_decide; lia.
Qed.
#[global]
Program Instance Op_pshiftu : ZifyClasses.BinOp pshiftu :=
  { TBOp p q := Zshiftu p q }.
Next Obligation.
  cbn.
  unfold pshiftu, Zshiftu.
  intros; do 2 case_decide; try lia.
Qed.
(* FIXME: Move *)
#[global]
Program Instance OpSpec_Zshiftu : ZifyClasses.BinOpSpec Zshiftu :=
  { BPred p q y := (p <= q /\ y = q + 1 \/ q <= p /\ y = q)%Z }.
Next Obligation.
  cbn.
  unfold Zshiftu.
  intros; case_decide; lia.
Qed.
Add Zify BinOp Op_pshiftd.
Add Zify BinOp Op_pshiftu.
Add Zify BinOpSpec OpSpec_Zshiftd.
Add Zify BinOpSpec OpSpec_Zshiftu.
(* FIXME: This seems needed to make the pshiftd zify work - we get an extraneous
  (let s := decide (p < q) in _) in a hypothesis that breaks lia*)
Ltac Zify.zify_post_hook ::= cbv zeta in *.


Lemma pseq_len_ne_0 start len :
  len <> N0 ->
  pseq start len = start :: (pseq (Pos.succ start) (N.pred len)).
Proof.
  destruct len using N.peano_rect; [easy|].
  rewrite N.pred_succ, pseq_succ.
  easy.
Qed.

Lemma join_list_cons {B} (mx : option B) (l : list (option B)) :
  join_list (mx :: l) = x ← mx; (x ::.) <$> join_list l.
Proof.
  reflexivity.
Qed.

Lemma list_lookup_total_fmap_alt `{Inhabited B, Inhabited C} (f : B -> C)
  (l : list B) (i : nat) :
  f inhabitant = inhabitant ->
  (f <$> l) !!! i =@{C} f (l !!! i).
Proof.
  rewrite 2 list_lookup_total_alt.
  rewrite list_lookup_fmap.
  destruct (l !! i); easy.
Qed.

Lemma lookup_delete_pshiftd (p q : positive) l : q <> p ->
  delete (p:>nat) l !! (pshiftd p q :>nat) = l !! (q:>nat).
Proof.
  intros Hqp.
  unfold pshiftd.
  case_decide.
  - rewrite lookup_delete_ge by lia.
    f_equal; lia.
  - rewrite lookup_delete_lt by lia.
    reflexivity.
Qed.

Lemma ppermute_aux_perm_posperm_cons (p : positive) ps l :
  (p < length l)%nat -> p ∉ ps -> (length l <= S (length ps))%nat ->
  ppermute_aux (perm_posperm (p :: ps)) l =
  x ← l !! (p :> nat);
  (x ::.) <$> ppermute_aux (perm_posperm (pshiftd p <$> ps)) (delete (p:>nat) l).
Proof.
  intros Hlen Hps Hlens.
  unfold ppermute_aux.
  pose proof (lengthN_correct l) as HlenN.
  rewrite pseq_len_ne_0 by lia.
  rewrite fmap_cons, join_list_cons.
  (* change (perm_posperm _ 1) with p. *)
  apply option_bind_ext; [|reflexivity].
  intros x.
  do 2 f_equal.
  rewrite pseq_succ_start, <- list_fmap_compose.
  rewrite 2 lengthN_correct_rev, length_delete by now apply lookup_lt_is_Some; lia.
  rewrite <- lengthN_correct_rev.
  replace (N.of_nat _) with (N.pred (lengthN l)) by lia.
  apply list_fmap_ext.
  intros _ i Hi%elem_of_list_lookup_2%elem_of_pseq_1.
  cbn.
  unfold perm_posperm.
  rewrite list_lookup_total_fmap_alt by now cbn; lia.
  rewrite lookup_total_cons_ne_0 by lia.
  replace (pred _) with (i:>nat) by lia.
  rewrite lookup_delete_pshiftd; [easy|].
  enough (ps !!! (i:>nat) ∈ ps) by congruence.
  apply elem_of_list_lookup_total_2.
  lia.
Qed.


Definition posperm_swap (p q : positive) (k : positive) :=
  if decide (k = p) then q else if decide (k = q) then p else k.

Definition Zperm_swap (p q : Z) (k : Z) :=
  if decide (k = p) then q else if decide (k = q) then p else k.

(* TODO: Any way to make this work?
#[global]
Program Instance Op_posperm_swap p q : ZifyClasses.UnOp (posperm_swap p q) :=
  { TUOp k := Zperm_swap (Zpos p) (Zpos q) k }.
Next Obligation.
  cbn.
  unfold posperm_swap, Zperm_swap.
  intros; repeat case_decide; lia.
Qed.
(* FIXME: Move *)
#[global]
Program Instance OpSpec_Zperm_swap p q :
  ZifyClasses.UnOpSpec (Zperm_swap p q) :=
  { UPred k k' := (k = p /\ k' = q \/ k = q /\ k' = p \/
    k <> p /\ k <> q /\ k' = k)%Z }.
Next Obligation.
  cbn.
  unfold Zperm_swap.
  intros; repeat case_decide; lia.
Qed.
Add Zify UnOp Op_posperm_swap.
Add Zify BinOp Op_pshiftu.
Add Zify BinOpSpec OpSpec_Zshiftd. *)

Definition posperm_tl (f : positive -> positive) : positive -> positive :=
  λ k, Pos.pred (f (Pos.succ k)).

Lemma posperm_tl_posperm n f :
  posperm (Pos.succ n) f ->
  f 1 = 1 ->
  posperm n (posperm_tl f).
Proof.
  intros Hposperm Hf1.
  revert Hposperm.
  unfold posperm.
  replace (Pos.pred_N _) with (N.succ (Pos.pred_N n)) by lia.
  rewrite pseq_succ.
  rewrite fmap_cons, Hf1.
  intros Hequiv%Permutation_cons_inv%(fmap_Permutation Pos.pred).
  rewrite pseq_succ_start, <- 3 list_fmap_compose in Hequiv.
  rewrite Hequiv.
  apply eq_reflexivity, list_fmap_id'.
  cbn; lia.
Qed.


Lemma posperm_swap_invol p q k :
  posperm_swap p q (posperm_swap p q k) = k.
Proof.
  unfold posperm_swap at 2; repeat case_decide;
  unfold posperm_swap; repeat case_decide; lia.
Qed.


Lemma posperm_swap_comm p q k :
  posperm_swap p q k = posperm_swap q p k.
Proof.
  unfold posperm_swap; repeat case_decide; lia.
Qed.

Lemma posperm_swap_posperm p q n : p < n -> q < n ->
  posperm n (posperm_swap p q).
Proof.
  intros Hp Hq.
  apply posperm_of_bounded_linv with (posperm_swap p q).
  - intros i Hi.
    unfold posperm_swap; repeat case_decide; lia.
  - intros i Hi.
    apply posperm_swap_invol.
Qed.

(* TODO: Induction principle from binary swaps and composition,
  without using perm_posperm *)

Lemma posperm_ind_fn n (P : (positive -> positive) -> Prop)
  (Hresp : forall f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P f -> P g)
  (Hid : P id)
  (Hswap : forall f, posperm n f -> P f ->
    forall p q, p < n -> q < n -> (P (f ∘ posperm_swap p q))) :
  forall f, posperm n f -> P f.
Proof.
  destruct_decide (decide (n = 1)) as Hn0. 1:{
    subst.
    intros f Hf.
    revert Hid.
    apply Hresp; [auto using posperm_id..|].
    unfold id; lia.
  }
  (* Prove by inducting on the threshold above which f is the identity
    (i.e., insertion sort) *)
  enough (Hen : forall (z : nat) f,
    (forall p, p < pos_sub_N n (N.of_nat z) -> f p = p) -> posperm n f -> P f). 1:{
    intros f.
    apply (Hen n).
    lia.
  }

  intros z.
  induction z.
  - intros f Hfid Hf.
    revert Hid.
    apply Hresp; [auto using posperm_id..|].
    unfold id.
    now intros ? ?%Hfid.
  - intros f Hfid Hf.
    set (k := pos_sub_N n (S z)).
    remember (posperm_inv n f k) as fi eqn:Hfi.
    symmetry in Hfi.
    apply posperm_inv_spec in Hfi as Hfi'; [|easy + lia..].
    destruct Hfi' as [Hfi' Hf_fi].
    eapply (Hresp (f ∘ posperm_swap fi k ∘ posperm_swap fi k));
      [auto using posperm_compose, posperm_swap_posperm with lia|easy|
      intros; unfold compose; now rewrite posperm_swap_invol|].
    apply Hswap;
    [auto using posperm_compose, posperm_swap_posperm with lia| |lia..].
    apply IHz;
    [|auto using posperm_compose, posperm_swap_posperm with lia].
    intros p Hp.
    enough (Hkfi : k <= fi).
    + unfold posperm_swap; cbn.
      destruct_decide (decide (p = k)).
      * transitivity (f fi); [case_decide; congruence|].
        congruence.
      * rewrite decide_False by lia.
        apply Hfid; lia.
    + specialize (Hfid fi).
      lia.
Qed.

Lemma posperm_ind_fn_comp n (P : (positive -> positive) -> Prop)
  (Hresp : forall f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P f -> P g)
  (Hid : P id)
  (Hswap : forall p q, p < n -> q < n -> (P (posperm_swap p q)))
  (Hcomp : forall f g, posperm n f -> posperm n g ->
    P f -> P g -> P (g ∘ f)) :
  forall f, posperm n f -> P f.
Proof.
  intros f Hf.
  induction Hf using posperm_ind_fn;
  eauto using posperm_compose, posperm_swap_posperm with lia.
Qed.

Lemma posperm_ind_fn_comp' n (P : (positive -> positive) -> Prop)
  (Hresp : forall f g, posperm n f -> posperm n g ->
    (forall p, p < n -> f p = g p) -> P f -> P g)
  (Hid : P id)
  (Hswap : forall p q, p < q -> q < n -> (P (posperm_swap p q)))
  (Hcomp : forall f g, posperm n f -> posperm n g ->
    P f -> P g -> P (g ∘ f)) :
  forall f, posperm n f -> P f.
Proof.
  apply posperm_ind_fn_comp; [assumption..| |assumption].
  intros p q Hp Hq.
  destruct_decide (decide (p < q)) as Hpq; [|destruct_decide (decide (p = q))].
  - auto.
  - subst.
    revert Hid.
    apply Hresp; [auto using posperm_id, posperm_swap_posperm..|].
    intros; unfold id, posperm_swap; repeat case_decide; congruence.
  - generalize (Hswap q p ltac:(lia) Hp).
    apply Hresp; [auto using posperm_swap_posperm..|].
    intros; apply posperm_swap_comm.
Qed.

(* FIXME: Move *)
Lemma lengthP_cons x l : lengthP (x :: l) = Pos.succ (lengthP l).
Proof.
  cbn; lia.
Qed.

Lemma lengthP_app l l' : lengthP (l ++ l') = Pos.pred (lengthP l + lengthP l').
Proof.
  rewrite lengthN_app; lia.
Qed.

Lemma lengthP_ins l x l' : lengthP (l ++ x :: l') = lengthP l + lengthP l'.
Proof.
  rewrite lengthP_app, lengthP_cons; lia.
Qed.

Lemma ppermute_posperm_swap_swaps (x1 x2 : A) (l1 l2 l3 : list A) p q :
  p = lengthP l1 -> q = lengthP l1 + lengthP l2 ->
  ppermute (posperm_swap p q) (l1 ++ x1 :: l2 ++ x2 :: l3) =
  l1 ++ x2 :: l2 ++ x1 :: l3.
Proof.
  Local Ltac simplen :=
    rewrite ?length_ppermute;
    (repeat (rewrite ?length_app, ?lengthP_ins, ?lengthP_app; cbn)); cbn.
  pose proof (lengthN_correct l1).
  pose proof (lengthN_correct l2).
  pose proof (lengthN_correct l3).
  intros -> ->.
  apply (fun H => list_eq_same_length _ _ _ H eq_refl);
    [now simplen|].
  rewrite length_ppermute.
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by
    (assumption || apply posperm_bounded, posperm_swap_posperm; simplen; lia).
  unfold posperm_swap.
  case_decide as Hil1; [|case_decide as Hil2].
  - replace i with (length l1)%nat by lia.
    rewrite lookup_app_r, lookup_cons_ne_0, lookup_app_r by lia.
    replace (_ - _)%nat with O by lia.
    cbn.
    rewrite lookup_app_r, Nat.sub_diag by lia.
    cbn.
    congruence.
  - replace i with (length l1 + S (length l2))%nat by lia.
    rewrite lookup_app_r by lia.
    replace (_ - _)%nat with O by lia.
    cbn.
    rewrite lookup_app_r, lookup_cons_ne_0, lookup_app_r by lia.
    replace (_ - _)%nat with O by lia.
    cbn.
    congruence.
  - replace (pos_to_nat_pred _) with i by lia.
    destruct_decide (decide (i < length l1)%nat) as Hismall;
    [| rewrite 2 lookup_app_r by lia;
      rewrite 2 lookup_cons_ne_0 by lia;
      destruct_decide (decide (i < length l1 + S (length l2)))%nat as Himed].
    + rewrite 2 lookup_app_l by lia.
      congruence.
    + rewrite 2 lookup_app_l by lia.
      congruence.
    + rewrite 2 lookup_app_r, 2 lookup_cons_ne_0 by lia.
      congruence.
Qed.

Lemma ppermute_replicate f n (a : A) :
  ppermute f (replicate n a) = replicate n a.
Proof.
  (* unfold ppermute. *)
  destruct (ppermute_case f (replicate n a)) as [[Hfbdd Hsome] | [_ Hnone]];
  [|unfold ppermute; now rewrite Hnone].
  apply (list_eq_same_length _ _ _ eq_refl); [now rewrite length_ppermute|].
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by auto.
  rewrite 2 lookup_replicate.
  now intros [-> _] [-> _].
Qed.

(* FIXME: Move *)
Lemma and_from_l {P Q} :
  P /\ (P -> Q) -> P /\ Q.
Proof.
  tauto.
Qed.
Lemma pos_to_nat_pred_of_nat (i : nat) :
  pos_to_nat_pred (Pos.of_succ_nat i) = i.
Proof.
  lia.
Qed.

Lemma perm_exists_perm_posperm l l' :
  l ≡ₚ l' ->
  exists ps, ps ≡ₚ pseq 1 (lengthN l) /\
  ppermute (perm_posperm ps) l = l'.
Proof.
  intros Hperm.
  pose proof ((* Permutation_sym *) Hperm) as Hseq.
  apply perm_exists_perm_seq in Hseq as (idxs & Hidxs & Hl').
  exists (Pos.of_succ_nat <$> idxs).
  apply and_from_l;
  split; [now rewrite pseq_to_seq, lengthN_correct, Hidxs, Hperm|].
  intros Hidxs_perm.
  apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_ppermute, Hperm|].
  intros i x y Hi.
  apply Permutation_length in Hperm as Hlens.
  apply Permutation_length in Hidxs as Hlens'.
  rewrite length_seq in Hlens'.

  rewrite lookup_ppermute_alt_bdd by (lia ||
    apply posperm_bounded, perm_posperm_posperm;
    rewrite Hidxs_perm;
    f_equiv; lia).
  unfold perm_posperm.
  rewrite list_lookup_total_alt.
  rewrite list_lookup_fmap.
  rewrite pos_to_nat_pred_of_nat.
  destruct (idxs !! i) as [ii|] eqn:Hii;
  [|now apply lookup_ge_None in Hii; lia].
  cbn.
  rewrite pos_to_nat_pred_of_nat.
  intros Hlii Hl'ii.

  apply elem_of_enumerate in Hlii as Hii'.
  unfold enumerate in Hii'.
  rewrite Hl' in Hii'.
  apply elem_of_list_lookup_1 in Hii' as
    Hin.
  destruct Hin as (j & Hj).
  apply lookup_zip_Some in Hj as [Hj Hl'j].
  enough (i = j) by congruence.
  assert (Hdup : NoDup idxs) by now rewrite Hidxs; apply NoDup_seq.
  eapply NoDup_lookup; eauto.
Qed.


Lemma perm_exists_posperm l l' :
  l ≡ₚ l' ->
  exists f, posperm (lengthP l) f /\
  ppermute f l = l' /\
  forall i, i < lengthP l ->
  l !! (f i :> nat) = l' !! (i:>nat).
Proof.
  intros (ps & Hps & Hppermute)%perm_exists_perm_posperm.
  exists (perm_posperm ps).
  apply and_from_l, conj; [apply perm_posperm_posperm; now rewrite N.pos_pred_succ|].
  intros Hperm.
  split; [easy|].
  intros i Hi.
  apply (f_equal (.!! i:nat)) in Hppermute.
  rewrite lookup_ppermute_alt_bdd in Hppermute by
    first [now apply posperm_bounded|pose proof (lengthN_correct l); lia].
  now rewrite pos_to_nat_pred_to_pos in Hppermute.
Qed.


End ppermute.


Lemma posperm_imap_eq {A} f (l : list A) :
  posperm (lengthP l) f ->
  imap pair (ppermute f l) =
  ppermute f (zip ((λ n : nat, posperm_inv (lengthP l) f (Pos.of_succ_nat n) :> nat) <$> seq 0 (length l))
    l).
Proof.
  intros Hf.
  apply (list_eq_same_length _ _ (length l));
  [rewrite length_ppermute, length_zip, length_fmap, length_seq; lia
  |now rewrite length_imap, length_ppermute|].
  intros i (k, x) (k', x') Hi.
  rewrite list_lookup_imap.
  rewrite lookup_ppermute_alt_bdd by now easy + apply posperm_bounded.
  rewrite lookup_ppermute_alt_bdd; [|rewrite lengthN_correct_rev|];
  [|rewrite length_zip, length_fmap, length_seq, Nat.min_id..];
  [|now rewrite <- lengthN_correct_rev;
  apply posperm_bounded(* , posperm_inv_posperm *)|easy].
  rewrite lookup_zip_Some.
  rewrite list_lookup_fmap.
  rewrite fmap_Some.
  intros (? & Heq & [= -> <-]).
  pose proof (lengthN_correct l).
  rewrite lookup_seq_lt, Nat.add_0_l by
    (specialize ((posperm_bounded _ _ Hf) (Pos.of_succ_nat i)); lia).

  rewrite Heq.
  cbn.
  intros [[= <-] [= <-]].
  f_equal.
  rewrite pos_to_nat_pred_to_pos.
  rewrite posperm_inv_linv by now easy + lia.
  lia.
Qed.

Lemma ppermute_posperm_inv_linv {A} f (l : list A) :
  posperm (lengthP l) f ->
  ppermute (posperm_inv (lengthP l) f)
    (ppermute f l) = l.
Proof.
  intros Hf.
  apply (list_eq_same_length _ _ _ eq_refl); [now rewrite 2!length_ppermute|].
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by
    now rewrite ?lengthN_ppermute, ?length_ppermute;
      try apply posperm_bounded, posperm_inv_posperm.
  pose proof (lengthN_correct l).
  rewrite lookup_ppermute_alt_bdd by (now apply posperm_bounded || now
    specialize (posperm_bounded _ _ (posperm_inv_posperm _ _ Hf)
    (Pos.of_succ_nat i)); lia).
  rewrite pos_to_nat_pred_to_pos.
  rewrite posperm_inv_rinv by now easy + lia.
  rewrite pos_to_nat_pred_of_nat; congruence.
Qed.


Lemma ppermute_posperm_inv_rinv {A} f (l : list A) :
  posperm (lengthP l) f ->
  ppermute f
    (ppermute (posperm_inv (lengthP l) f) l) = l.
Proof.
  intros Hf.
  apply (list_eq_same_length _ _ _ eq_refl); [now rewrite 2!length_ppermute|].
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by
    now rewrite ?lengthN_ppermute, ?length_ppermute;
      try apply posperm_bounded.
  pose proof (lengthN_correct l).
  rewrite lookup_ppermute_alt_bdd by (now apply posperm_inv_bounded || now
    specialize (posperm_bounded _ _ Hf
    (Pos.of_succ_nat i)); lia).
  rewrite pos_to_nat_pred_to_pos.
  rewrite posperm_inv_linv by now easy + lia.
  rewrite pos_to_nat_pred_of_nat; congruence.
Qed.

Lemma posperm_inv_posperm_inv f n k : k < n ->
  posperm n f ->
  posperm_inv n (posperm_inv n f) k = f k.
Proof.
  intros Hk Hf.
  rewrite posperm_inv_spec by now easy + apply posperm_inv_posperm.
  split; [now apply posperm_bounded|].
  now apply posperm_inv_linv.
Qed.

Lemma posperm_imap_eq' {A} f (l : list A) :
  posperm (lengthP l) f ->
  imap pair l =
  ppermute (posperm_inv (lengthP l) f)
    (zip ((λ n : nat, f (Pos.of_succ_nat n) :> nat)
     <$> seq 0 (length l))
    (ppermute f l)).
Proof.
  intros Hf.
  apply posperm_inv_posperm in Hf as Hf'.
  rewrite <- (lengthN_ppermute f) in Hf'.
  apply posperm_imap_eq in Hf'.
  rewrite lengthN_ppermute, ppermute_posperm_inv_linv in Hf' by easy.
  rewrite Hf'.
  f_equal.
  rewrite length_ppermute.
  f_equal.
  pose proof (lengthN_correct l).
  apply list_fmap_ext; intros _ k Hk%elem_of_list_lookup_2%elem_of_seq.
  rewrite posperm_inv_posperm_inv by (easy + lia).
  reflexivity.
Qed.

Lemma ppermute_zip_with {A B C} f (p : A -> B -> C) (l : list A) (l' : list B) : 
  length l = length l' -> 
  ppermute f (zip_with p l l') = 
  zip_with p (ppermute f l) (ppermute f l').
Proof.
  intros Hl.
  destruct (ppermute_case f l) as [(Hbdd & Hsome) | (Hnbdd & Hnone)]. 2:{
    unfold ppermute.
    rewrite ((ppermute_aux_None_iff_not_bdd _ _).2) by 
      now rewrite lengthN_correct_rev, length_zip_with, <- Hl, 
        Nat.min_id, <- lengthN_correct_rev.
    rewrite ((ppermute_aux_None_iff_not_bdd _ _).2) by easy.
    rewrite ((ppermute_aux_None_iff_not_bdd _ _).2) by
      now rewrite lengthN_correct_rev, <- Hl, <- lengthN_correct_rev.
    reflexivity.
  }
  apply (fun H => list_eq_same_length _ _ _ H eq_refl); 
    [now rewrite length_ppermute, ?length_zip_with, ?length_ppermute|].
  rewrite length_ppermute, length_zip_with, <- Hl, Nat.min_id.
  intros i x y Hi.
  rewrite lookup_ppermute_alt_bdd by 
    now rewrite ?lengthN_correct_rev, length_zip_with, <- Hl, 
        Nat.min_id, <- ?lengthN_correct_rev.
  rewrite lookup_zip_with_Some.
  rewrite lookup_zip_with.
  rewrite lookup_ppermute_alt_bdd by 
    now rewrite ?lengthN_correct_rev, <- Hl, <- ?lengthN_correct_rev.
  rewrite lookup_ppermute_alt_bdd by easy.
  intros (? & ? & -> & -> & ->).
  cbn.
  congruence.
Qed.


Lemma zip_with_ppermute_r {A B C} f (p : A -> B -> C) (l : list A) (l' : list B) : 
  posperm (lengthP l) f ->
  length l = length l' -> 
  zip_with p l (ppermute f l') = 
  ppermute f (zip_with p (ppermute (posperm_inv (lengthP l) f) l) l').
Proof.
  intros Hf Hl.
  rewrite ppermute_zip_with by now rewrite length_ppermute.
  now rewrite ppermute_posperm_inv_rinv.
Qed.

Lemma lengthN_eq {A B} (l : list A) (l' : list B) : 
  lengthN l = lengthN l' <-> length l = length l'.
Proof.
  rewrite 2 lengthN_correct_rev; lia.
Qed.

Lemma zip_with_ppermute_l {A B C} f (p : A -> B -> C) (l : list A) (l' : list B) : 
  posperm (lengthP l) f ->
  length l = length l' -> 
  zip_with p (ppermute f l) l' = 
  ppermute f (zip_with p l (ppermute (posperm_inv (lengthP l) f) l')).
Proof.
  intros Hf Hl.
  apply lengthN_eq in Hl as Hl'.
  rewrite ppermute_zip_with by now rewrite length_ppermute.
  rewrite Hl'.
  now rewrite ppermute_posperm_inv_rinv by now rewrite <- Hl'.
Qed.


Lemma zip_with_ppermute_r_permutation {A B C} f (p : A -> B -> C) (l : list A) (l' : list B) : 
  posperm (lengthP l) f ->
  length l = length l' -> 
  zip_with p l (ppermute f l') ≡ₚ
  zip_with p (ppermute (posperm_inv (lengthP l) f) l) l'.
Proof.
  intros Hf Hl.
  rewrite zip_with_ppermute_r by easy.
  apply ppermute_permutation.
  rewrite lengthN_correct_rev, length_zip_with, length_ppermute, <- Hl, 
    Nat.min_id, <- lengthN_correct_rev.
  easy.
Qed.


Lemma zip_with_ppermute_l_permutation {A B C} f (p : A -> B -> C) (l : list A) (l' : list B) : 
  posperm (lengthP l) f ->
  length l = length l' -> 
  zip_with p (ppermute f l) l' ≡ₚ
  zip_with p l (ppermute (posperm_inv (lengthP l) f) l').
Proof.
  intros Hf Hl.
  rewrite zip_with_ppermute_l by easy.
  apply ppermute_permutation.
  rewrite lengthN_correct_rev, length_zip_with, length_ppermute, <- Hl, 
    Nat.min_id, <- lengthN_correct_rev.
  easy.
Qed.



Definition bcons (b : bool) (p : positive) : positive :=
  match b with
  | true => xI p
  | false => xO p
  end.

#[global]
Program Instance Op_bcons : ZifyClasses.BinOp
  (T1:=bool) bcons := {
  TBOp b p := (2 * p + Z.b2z b)%Z;
}.
Next Obligation.
  cbn.
  intros [] ?; cbn; lia.
Qed.

Add Zify BinOp Op_bcons.

#[export] Instance bcons_inj2 : Inj2 (=) (=) (=) bcons.
Proof.
  hnf.
  lia.
Qed.



Lemma lengthN_fmap {A B} (f : A -> B) (l : list A) :
  lengthN (f <$> l) = lengthN l.
Proof.
  apply lengthN_eq, length_fmap.
Qed.
Lemma ppermute_fmap {A B} p (f : A -> B) (l : list A) :
  ppermute p (f <$> l) = f <$> ppermute p l.
Proof.
  destruct (ppermute_case p l) as [(Hbdd & Hsome) | (Hndbb & Hnone)].
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap, 2 length_ppermute, length_fmap|].
    intros i x y.
    rewrite length_fmap, length_ppermute.
    intros Hi.
    rewrite lookup_ppermute_alt_bdd by now rewrite ?lengthN_fmap, ?length_fmap.
    rewrite 2 list_lookup_fmap.
    rewrite lookup_ppermute_alt_bdd by easy.
    congruence.
  - now rewrite 2 ppermute_not_bdd by now rewrite ?lengthN_fmap.
Qed.

Import gmap pmap.

(* Combine input and output maps to get the local variable map *)
Definition gmaps_to_Pmap {A}
  (minput : gmap nat A) (moutput : gmap nat A) : Pmap A :=
  (kmap (bcons false ∘ Pos.of_succ_nat) minput ∪
      kmap (bcons true ∘ Pos.of_succ_nat) moutput).




Lemma lookup_gmaps_to_Pmap {A} (mi mo : gmap nat A) p :
  gmaps_to_Pmap mi mo !! p =
  match p with
  | xH => None
  | p~0 => mi !! (p:>nat)
  | p~1 => mo !! (p:>nat)
  end.
Proof.
  unfold gmaps_to_Pmap.
  rewrite lookup_union.
  destruct p.
  - rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite option_union_left_id.
    replace p~1 with ((bcons true ∘ Pos.of_succ_nat) p) by now cbn; lia.
    rewrite lookup_kmap by apply _.
    reflexivity.
  - replace p~0 with ((bcons false ∘ Pos.of_succ_nat) p) by now cbn; lia.
    rewrite lookup_kmap by apply _.
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite option_union_right_id.
    reflexivity.
  - rewrite 2 (lookup_kmap_None _ _ _).2 by now cbn; lia.
    reflexivity.
Qed.