From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
Import Props stdpp.vector.

From TensorRocqEx Require Import BaseInstances NonZXAux.
From TensorRocqEx Require Import QC.
From TensorRocqEx Require Import MatrixAux TensorHom.



Import base QArith.

Local Open Scope QC_scope.

Definition QCinvsqrt2_pow (n : nat) :=
  let nmod2 := n `mod` 2 in
  let ndiv2 := n `div` 2 in
  let denom : positive := (Nat.iter ndiv2 xO xH) in
  if decide (nmod2 = O) then
    mkQC (Zpos xH # denom) 0 0 0
  else
    mkQC 0 (Zpos xH # denom) 0 0.


Lemma invsqrt2_pow_alt n :
  ((/ √ 2) ^ n = / 2 ^ (n / 2) * (if decide (n `mod` 2 = O) then 1 else / √ 2))%C.
Proof.
  rewrite (Nat.div_mod_eq n 2) at 1.
  rewrite Cpow_add_r.
  f_equal.
  - rewrite Cpow_mult.
    rewrite <- Cpow_inv.
    f_equal.
    rewrite QC2C_Z.
    cbn.
    C_field.
  - assert (Hn : lt (n mod 2) 2) by (apply Nat.mod_upper_bound; lia).
    destruct (n mod 2) as [|n'].
    + rewrite decide_True by done.
      rewrite QC2C_Z.
      done.
    + rewrite decide_False by lia.
      replace n' with O by lia.
      now rewrite Cpow_1_r.
Qed.

Lemma Qpow_half (n : nat) : ((/ 2 ^ n) == 1 # Pos.of_succ_nat (2 ^ n - 1))%Q.
Proof.
  change 2%Q with (inject_Z 2).
  rewrite <- Qpower.Zpower_Qpower by lia.
  unfold Qinv.
  cbn.
  replace ((BinInt.Z.pow 2 (BinInt.Z.of_nat n))) with (Zpos (Pos.of_nat (BinInt.Z.to_nat (2 ^ n)))).
  2:{
    enough (BinInt.Z.lt 0 $ BinInt.Z.pow 2 (BinInt.Z.of_nat n)) by lia.
    apply BinInt.Z.pow_pos_nonneg; lia.
  }
  f_equal.
  cbn.
  f_equal.
  rewrite Z2Nat.inj_pow by lia.
  change (BinInt.Z.to_nat 2) with 2%nat.
  rewrite Nat2Z.id.
  enough (0 < 2 ^ n)%nat by lia.
  now apply pow_positive.
Qed.

Lemma Qmk_1_iter_xO_xH n : (1 # Nat.iter n xO xH ==
  1 / 2 ^ n)%Q.
Proof.
  unfold Qdiv.
  rewrite Qmult_1_l.
  rewrite Qpow_half.
  f_equal.
  cbn.
  rewrite Zpos_P_of_succ_nat.
  rewrite <- Nat2Z.inj_succ.
  replace (S (2 ^ n - 1))%nat with (2 ^ n)%nat by
    (enough (0 < 2 ^ n)%nat by lia;
    now apply pow_positive).
  unfold Nat.iter.
  induction n; [done|].
  cbn -[Nat.mul].
  rewrite Nat2Z.inj_mul.
  rewrite IHn.
  done.
Qed.

Lemma Q2R_Z (z : BinInt.Z) : Q2R (z # xH) = IZR z.
Proof.
  unfold Q2R.
  cbn.
  rewrite Rinv_1, Rmult_1_r.
  done.
Qed.

Lemma QC2C_QCinvsqrt2_pow n :
  (QC2C (QCinvsqrt2_pow n) = (/ √ 2) ^ n)%C.
Proof.
  rewrite invsqrt2_pow_alt.
  unfold QCinvsqrt2_pow.
  case_decide.
  - cbn -[Nat.iter Nat.div].
    rewrite (Qreals.Qeq_eqR _ _ (Qmk_1_iter_xO_xH _)).
    rewrite !Q2R_Z.
    rewrite QC.Q2R_div', Q2R_Z.
    rewrite RMicromega.Q2RpowerRZ by lia.
    rewrite Rdiv_1_l.
    rewrite Rdiv_0_l, !Rplus_0_r.
    rewrite Cmult_1_r.
    change (?x, 0%R) with (RtoC x).
    rewrite RtoC_pow.
    rewrite RtoC_inv.
    f_equal.
    f_equal.
    rewrite pow_powerRZ.
    rewrite Q2R_Z.
    done.
  - cbn -[Nat.iter Nat.div].
    rewrite (Qreals.Qeq_eqR _ _ (Qmk_1_iter_xO_xH _)).
    rewrite !Q2R_Z.
    rewrite QC.Q2R_div', Q2R_Z.
    rewrite RMicromega.Q2RpowerRZ by lia.
    rewrite Rdiv_1_l.
    rewrite Rdiv_0_l, !Rplus_0_r, !Rplus_0_l.
    change (?x, 0%R) with (RtoC x).
    rewrite RtoC_pow.
    rewrite RtoC_div.
    unfold Cdiv.
    f_equal.
    rewrite RtoC_inv.
    f_equal.
    f_equal.
    rewrite pow_powerRZ.
    rewrite Q2R_Z.
    done.
Qed.





Definition QZXCVERT := option (bool * BinInt.Z + QC).


Definition Qzsp {n m : nat} (phase: BinInt.Z) : Tensor (R:=QC) n m bool :=
  fun bs cs =>
    (if allb false bs && allb false cs then 1%Q else 0%Q) +
    (if allb true bs && allb true cs then QCexpPI4 phase else 0%QC).

#[global] Arguments Qzsp {_ _} _ _ _ / : assert.

Definition Qxsp {n m : nat}
  (phase : BinInt.Z) : @Tensor QC n m bool :=
  fun bs cs =>
  QCinvsqrt2_pow (n + m) * (1 +
    QCexpPI4
    (if ZXCore.parity (bs +++ cs)
      then (4 + phase) else phase)).

#[global] Arguments Qxsp {_ _} _ _ _ / : assert.

Definition Qh : @Tensor QC 1 1 bool :=
  fun bl br =>
  QCinvsqrt2_pow 1 * (if vhd bl && vhd br then -1 else 1).

#[global] Arguments Qh _ _ / : assert.


Definition Qh_stack {n : nat} : @Tensor QC n n bool :=
  fun v w =>
  if (vec_dot v w) then
    - QCinvsqrt2_pow n
  else
    QCinvsqrt2_pow n.

#[global] Arguments Qh_stack {_} _ _ / : assert.


Lemma QCinvsqrt2_pow_S n :
  QCinvsqrt2_pow (S n) == QCinvsqrt2_pow 1 * QCinvsqrt2_pow n.
Proof.
  apply eqC_QCeq.
  rewrite QC2C_mult, 3 QC2C_QCinvsqrt2_pow.
  rewrite Cpow_1_r; done.
Qed.

Lemma Qh_stack_S n : @Qh_stack (S n) ≡ stack_tensor Qh Qh_stack.
Proof.
  intros v w _ _.
  inv_vec v; intros vh v.
  inv_vec w; intros wh w.
  cbn -[QCinvsqrt2_pow].
  rewrite xorb_if.
  destruct (vh && wh).
  - destruct (Rlist_sum _).
    + rewrite QCinvsqrt2_pow_S.
      apply eqC_QCeq.
      rewrite 3 QC2C_mult, QC2C_Z, QC2C_opp.
      lca.
    + rewrite QCinvsqrt2_pow_S.
      apply eqC_QCeq.
      rewrite QC2C_opp, 3 QC2C_mult, QC2C_Z.
      lca.
  - destruct (Rlist_sum _).
    + rewrite QCinvsqrt2_pow_S.
      apply eqC_QCeq.
      rewrite QC2C_opp, 3 QC2C_mult, QC2C_Z, QC2C_opp.
      lca.
    + rewrite QCinvsqrt2_pow_S.
      apply eqC_QCeq.
      rewrite 3 QC2C_mult, QC2C_Z.
      lca.
Qed.

Lemma Qh_stack_0 : @Qh_stack 0 ≡ delta_tensor.
Proof.
  intros v w _ _.
  inv_all_vec_fin.
  cbn.
  rewrite decide_True by done.
  apply eqC_QCeq.
  rewrite QC2C_QCinvsqrt2_pow.
  rewrite QC2C_Z.
  done.
Qed.



Lemma Qzsp_correct n m alpha :
  tensor_apply_hom QC2C (@Qzsp n m alpha) ≡
  zsp (IZR alpha * PI / 4).
Proof.
  intros v w _ _.
  cbn.
  unfold zsp.
  rewrite QC2C_plus.
  rewrite !(if_dist _ _ _ QC2C).
  rewrite 2 QC2C_Z, QC2C_QCexpPI4.
  done.
Qed.

Lemma Qxsp_correct n m alpha :
  tensor_apply_hom QC2C (@Qxsp n m alpha) ≡
  xsp (IZR alpha * PI / 4).
Proof.
  intros v w _ _.
  cbn -[QCplus].
  unfold xsp.
  rewrite QC2C_mult, QC2C_QCinvsqrt2_pow, QC2C_plus, QC2C_Z, QC2C_QCexpPI4.
  unfold Cdiv.
  rewrite Cmult_1_l.
  f_equal.
  f_equal.
  f_equal.
  destruct (_ :> bool); [|done].
  rewrite plus_IZR.
  R_field.
Qed.

Lemma Qh_stack_1_correct :
  tensor_apply_hom QC2C (@Qh_stack 1) ≡
  h_stack.
Proof.
  intros v w _ _.
  inv_all_vec_fin.
  cbn.
  rewrite (if_dist _ _ _ QC2C).
  rewrite QC2C_opp, QC2C_QCinvsqrt2_pow, Cpow_1_r.
  rewrite xorb_false_r, Cmult_1_r.
  unfold h.
  destruct (_ && _); lca.
Qed.

Lemma Qh_correct :
  tensor_apply_hom QC2C Qh ≡
  h_stack.
Proof.
  intros v w _ _.
  inv_all_vec_fin.
  cbn.
  rewrite QC2C_mult.
  rewrite (if_dist _ _ _ QC2C), 2 QC2C_Z.
  rewrite QC2C_QCinvsqrt2_pow, Cpow_1_r.
  rewrite Cmult_1_r.
  unfold h.
  destruct (_ && _); lca.
Qed.

Lemma Qh_stack_correct n :
  tensor_apply_hom QC2C (@Qh_stack n) ≡
  h_stack.
Proof.
  induction n.
  - rewrite Qh_stack_0.
    rewrite (tensor_apply_hom_delta _).
    intros v w _ _.
    cbn.
    inv_all_vec_fin.
    now rewrite decide_True by done.
  - rewrite Qh_stack_S.
    rewrite (tensor_apply_hom_stack_tensor _ (n:=1) (m:=1)).
    erewrite stack_tensor_mor; [|apply Qh_correct|apply IHn].
    intros v w _ _.
    inv_all_vec_fin; cbn.
    lca.
Qed.



#[export] Existing Instances eqm_setoid Zopp_eqm Zmult_eqm Zminus_eqm Zplus_eqm.


#[export] Instance QCexpPI4_proper : Proper (eqm 8 ==> eq) (QCexpPI4).
Proof.
  intros x y Hxy.
  unfold QCexpPI4.
  f_equal.
  now rewrite Hxy.
Qed.

#[export] Instance Qzsp_proper n m : Proper (eqm 8 ==> (≡)) (@Qzsp n m).
Proof.
  intros x y Hxy v w _ _.
  cbn.
  rewrite Hxy.
  done.
Qed.

#[export] Instance Qxsp_proper n m : Proper (eqm 8 ==> (≡)) (@Qxsp n m).
Proof.
  intros x y Hxy v w _ _.
  cbn -[QCplus].
  f_equiv.
  f_equiv.
  destruct (_ :> bool); now rewrite Hxy.
Qed.



#[export] Instance QZXCVERT_inhab : Inhabited QZXCVERT := populate None.

(* We define the natural equivalence relation on [ZXCVERT], with phases
  taken mod [2*PI], and show it is in fact an equivalence relation. *)
#[export] Instance QZXCVERT_equiv : Equiv QZXCVERT :=
  option_Forall2 (sum_relation (prod_relation eq
    (eqm 8)) QCeq).

#[export] Instance QZXCVERT_equiv_equivalence : Equivalence (≡@{QZXCVERT}).
Proof. apply _. Qed.

Definition QZXCCALC_tensor (x : QZXCVERT) : @DimensionlessTensor QC bool :=
  match x with
  | None => fun n m => (tensor_to_dimensionless (@Qh_stack n)) n m
  | Some (inl (false, r))  => fun n m => @Qzsp n m r
  | Some (inl (true, r)) => fun n m => @Qxsp n m r
  | Some (inr c) => fun n m v w => c
  end.


#[global] Arguments ZXCCALC_tensor !_ /.

(* We show this tensor interpretation respects our equivalence relation;
  this is basically just applying instances from [ZXCore.v]. *)
#[export] Instance QZXCCALC_tensor_proper :
  Proper ((≡) ==> (≡)) QZXCCALC_tensor.
Proof.
  intros x x' Heq.
  induction Heq as [x y Heq|]; [|done..].
  induction Heq as [ [ [] x] [c y] [ [= <-] Heq]|? ? Heq]; cbn in *; intros n m.
  - now rewrite <- Heq.
  - now rewrite <- Heq.
  - intros ????; done.
Qed.


#[export] Instance QZXCCALC : TensorLike QC bool QZXCVERT := {
  interpretTensor := QZXCCALC_tensor;
}.

Definition QZXDVERT := WithDiagrams QZXCVERT (fun n m => @Tensor QC n m bool).

#[export] Instance QC_bool_tensor_like :
  StrictTensorLike QC bool (fun n m => @Tensor QC n m bool) := {
  strictInterpretTensor n m t := t
}.

#[export] Instance QZXDCALC : TensorLike QC bool QZXDVERT := _.


Definition QZXC2ZXC : QZXCVERT -> ZXCVERT :=
  fmap (M:=option) (sum_map (prod_map Datatypes.id (λ z, IZR z * PI / 4)%R) QC2C).

(* FIXME: Move *)
Section Zfact.

Local Open Scope Z_scope.

Lemma Zmod_0_r a : a mod 0 = a.
Proof.
  destruct a; done.
Qed.

Lemma Zdiv_0_r a : a / 0 = 0.
Proof.
  destruct a; done.
Qed.

Lemma Zdiv_mod_eq a b : a = b * (a / b) + a mod b.
Proof.
  destruct_decide (decide (b = 0)).
  - subst.
    rewrite Zmod_0_r, Zdiv_0_r; lia.
  - now apply BinInt.Z.div_mod.
Qed.

Lemma Zmod_add a b c : (a + b * c) mod c = a mod c.
Proof.
  destruct_decide (decide (c = 0)).
  - subst.
    rewrite 2 Zmod_0_r; lia.
  - now apply BinInt.Z.mod_add.
Qed.

Lemma eqm_spec N a b :
  eqm N a b <-> exists z, a = z * N + b.
Proof.
  split.
  - intros [= Hab].
    exists (a / N - b / N).
    pose proof (Zdiv_mod_eq a N).
    pose proof (Zdiv_mod_eq b N).
    lia.
  - intros [z ->].
    hnf.
    rewrite BinInt.Z.add_comm.
    rewrite Zmod_add.
    done.
Qed.

End Zfact.

#[export] Instance QZXC2ZXC_proper : Proper ((≡) ==> (≡)) QZXC2ZXC.
Proof.
  apply option_fmap_proper.
  apply sum_map_proper; [|apply _].
  apply prod_map_proper; [apply _|].
  intros x y [z ->]%eqm_spec.
  exists z.
  rewrite plus_IZR, mult_IZR.
  lra.
Qed.

Definition zx_of_QC_tensor {n m} (t : Tensor n m bool) : ZX n m :=
  zx_of_matrix (matrix_of_tensor (tensor_apply_hom QC2C t)).

Definition QZXD2ZXD : QZXDVERT -> ZXDVERT :=
  sum_map QZXC2ZXC (fun '(existT (n, m) t) =>
    existT (n,m) (zx_of_QC_tensor t)).

#[export] Instance QZXD2ZXD_proper : Proper ((≡) ==> (≡)) QZXD2ZXD.
Proof.
  apply sum_map_proper; [apply _|].
  intros bt bt' Heq.
  induction Heq.
  constructor.
  unfold zx_of_QC_tensor.
  f_equiv.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  now f_equiv.
Qed.

Import ProQuote.

Section Quote_R_div_PI4.

Local Open Scope R_scope.

Class Quote_R_div_PI4 (z : BinInt.Z) (r : R) :=
  quote_R_div_PI4 : IZR z * PI / 4 =[mod 2 * PI] r.

Lemma mk_quote_R_div_PI4_0_simp z r rsimp :
  Rsimpl_modeq_2PI r rsimp ->
  Quote_R_div_PI4 z rsimp ->
  Quote_R_div_PI4 z r.
Proof.
  intros Hrsimp Hz.
  unfold Quote_R_div_PI4 in *.
  rewrite Hz.
  symmetry.
  exact Hrsimp.
Qed.



Lemma quote_R_div_PI4_0 r :
  r = 0 ->
  Quote_R_div_PI4 0 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_1 r :
  r = PI / 4 ->
  Quote_R_div_PI4 1 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_2 r :
  r = PI / 2 ->
  Quote_R_div_PI4 2 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_3 r :
  r = 3 * PI / 4 ->
  Quote_R_div_PI4 3 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_4 r :
  r = PI ->
  Quote_R_div_PI4 4 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_5 r :
  r = 5 * PI / 4 ->
  Quote_R_div_PI4 5 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_6 r :
  r = 3 * PI / 2 ->
  Quote_R_div_PI4 6 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

Lemma quote_R_div_PI4_7 r :
  r = 7 * PI / 4 ->
  Quote_R_div_PI4 7 r.
Proof.
  intros ->.
  unfold Quote_R_div_PI4.
  apply Aux.eq_reflexivity.
  lra.
Qed.

End Quote_R_div_PI4.

Ltac quote_R_div_PI4_tac :=
  let r := lazymatch goal with |- (Quote_R_div_PI4 _ ?r) => constr:(r) end in
  lazymatch r with
  | 0%R => apply quote_R_div_PI4_0; lra
  | (PI / 4)%R => apply quote_R_div_PI4_1; lra
  | (PI / 2)%R => apply quote_R_div_PI4_2; lra
  | (3 * PI / 4)%R => apply quote_R_div_PI4_3; lra
  | PI => apply quote_R_div_PI4_4; lra
  | (5 * PI / 4)%R => apply quote_R_div_PI4_5; lra
  | (3 * PI / 2)%R => apply quote_R_div_PI4_6; lra
  | (7 * PI / 4)%R => apply quote_R_div_PI4_7; lra
  | _ =>
    apply (mk_quote_R_div_PI4_0_simp _ _ _ _);
    let rsimp := lazymatch goal with |- (Quote_R_div_PI4 _ ?rsimp) => constr:(rsimp) end in
    lazymatch rsimp with
    | 0%R => apply quote_R_div_PI4_0; lra
    | (PI / 4)%R => apply quote_R_div_PI4_1; lra
    | (PI / 2)%R => apply quote_R_div_PI4_2; lra
    | (3 * PI / 4)%R => apply quote_R_div_PI4_3; lra
    | PI => apply quote_R_div_PI4_4; lra
    | (5 * PI / 4)%R => apply quote_R_div_PI4_5; lra
    | (3 * PI / 2)%R => apply quote_R_div_PI4_6; lra
    | (7 * PI / 4)%R => apply quote_R_div_PI4_7; lra
    end
  end.

#[export] Hint Extern 0 (Quote_R_div_PI4 _ _) =>
  quote_R_div_PI4_tac : typeclass_instances.


Lemma PI_neq_0 : PI <> 0%R.
Proof.
  pose proof PI2_1; lra.
Qed.


Class GeneratorQuote {T T'} {EqT' : Equiv T'}
  (f : T -> T') (t : T) (t' : T') := {
  generatorQuote : f t ≡ t'
}.

Section PRO_quote.

Context {Struct : Mor nat} {T : Type}
  {EqS : ∀ n m, Equiv (Struct n m)}
  {T'} {EqT' : Equiv T'}
  (f : T -> T').

Local Notation PRO_quote := (@PRO_quote Struct T EqS T' EqT' f _ _).

Lemma PRO_quote_id n :
  PRO_quote (Pid n) (Pid n).
Proof.
  unfold PRO_quote.
  constructor.
Qed.

Lemma PRO_quote_struct `{∀ n m, @Reflexive (Struct n m) base.equiv}
  n m (s : Struct n m) :
  PRO_quote [str s] [str s].
Proof.
  unfold PRO_quote.
  now constructor.
Qed.

Lemma PRO_quote_compose
  {n m o} (dp p : PRO Struct _ n m) (dq q : PRO Struct _ m o) :
  PRO_quote dp p ->
  PRO_quote dq q ->
  PRO_quote (dp ;; dq) (p ;; q).
Proof.
  unfold PRO_quote.
  cbn.
  now constructor.
Qed.

Lemma PRO_quote_stack
  {n m n' m'} (dp p : PRO Struct _ n m) (dq q : PRO Struct _ n' m') :
  PRO_quote dp p ->
  PRO_quote dq q ->
  PRO_quote (dp * dq) (p * q).
Proof.
  unfold PRO_quote.
  cbn.
  now constructor.
Qed.

Lemma PRO_quote_gen
  n m t t' :
  GeneratorQuote f t t' ->
  PRO_quote [gen t n m] [gen t' n m].
Proof.
  unfold PRO_quote.
  cbn.
  intros [].
  now constructor.
Qed.

End PRO_quote.

Ltac simplify_PRO_quote_tac :=
  let f := lazymatch goal with |- PRO_quote ?f _ _ => constr:(f) end in
  let rec go :=
    let rhs := lazymatch goal with |- PRO_quote _ _ ?rhs => constr:(rhs) end in
    lazymatch rhs with
    | Pcompose ?pl ?pr =>
      eapply (PRO_quote_compose f _ pl _ pr);
      go
    | Pstack ?pl ?pr =>
      eapply (PRO_quote_stack f _ pl _ pr);
      go
    | Pid _ =>
      apply (PRO_quote_id f)
    | Pstruct ?n ?m ?s =>
      apply (PRO_quote_struct f n m s)
    | Pgen ?n ?m ?t =>
      eapply (PRO_quote_gen f n m)
    | _ =>
      let rhs' := eval hnf in rhs in
      tryif constr_eq rhs rhs' then fail
      else
        lazymatch goal with |- ?P _ => change (P rhs') end;
        go
    end
  in go.

#[export] Hint Extern 1 (PRO_quote _ _ _) =>
  simplify_PRO_quote_tac : typeclass_instances.

Set Typeclasses Unique Instances.

#[export] Instance quote_QZXD_l qv v :
  GeneratorQuote QZXC2ZXC qv v ->
  GeneratorQuote QZXD2ZXD (inl qv) (inl v).
Proof.
  intros [Hqv]; constructor.
  cbn.
  now constructor.
Qed.

#[export] Instance quote_QZXC_H :
  GeneratorQuote QZXC2ZXC None None.
Proof.
  split; easy.
Qed.

#[export] Instance quote_QZXC_spider b z r :
  Quote_R_div_PI4 z r ->
  GeneratorQuote QZXC2ZXC
    (Some (inl (b, z))) (Some (inl (b, r))).
Proof.
  intros Hzr.
  constructor.
  cbn.
  repeat constructor || done.
Qed.

#[export] Instance quote_QZXC_const qc c :
  ParseQC qc c ->
  GeneratorQuote QZXC2ZXC
    (Some (inr qc)) (Some (inr c)).
Proof.
  intros [Hzr].
  constructor.
  cbn.
  repeat constructor || done.
Qed.

#[export] Instance quote_QZXD_bundled {n m} t (zx : ZX n m) :
  GeneratorQuote zx_of_QC_tensor t zx ->
  GeneratorQuote QZXD2ZXD (inr (bundleDiagram t)) (inr (bundleDiagram zx)).
Proof.
  intros [Ht].
  split.
  cbn.
  do 2 constructor.
  apply Ht.
Qed.

#[export] Instance quote_QZXD_bundled' {n m} t (zx : ZX n m) :
  GeneratorQuote zx_of_QC_tensor t zx ->
  GeneratorQuote QZXD2ZXD (inr (existT (n,m) t)) (inr (existT (n,m) zx)).
Proof.
  intros [Ht].
  split.
  cbn.
  do 2 constructor.
  apply Ht.
Qed.



Lemma mk_quote_zx_mat {n m} t (zx : ZX n m) :
  tensor_apply_hom QC2C t ≡ tensor_of_matrix (ZX_semantics zx) ->
  GeneratorQuote zx_of_QC_tensor t zx.
Proof.
  intros Ht.
  constructor.
  hnf.
  unfold zx_of_QC_tensor.
  rewrite zx_of_matrix_semantics by auto_wf.
  prep_matrix_equivalence.
  apply tensor_of_matrix_inj'.
  rewrite tensor_of_matrix_of_tensor.
  done.
Qed.

#[export] Instance quote_zx_mat_transpose {n m} t (zx : ZX n m) :
  GeneratorQuote zx_of_QC_tensor t zx ->
  GeneratorQuote zx_of_QC_tensor (fun v w => t w v) (zx ⊤).
Proof.
  intros [Hzx].
  constructor.
  hnf.
  rewrite semantics_transpose_comm.
  prep_matrix_equivalence.
  rewrite <- Hzx.
  unfold zx_of_QC_tensor.
  rewrite 2 zx_of_matrix_semantics by auto_wf.
  unfold matrix_of_tensor.
  rewrite 2 make_WF_equiv.
  done.
Qed.

#[export] Instance quote_zx_mat_triangle :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => if vhd w || ¬ vhd v then 1%QC else 0%QC) zx_triangle.
Proof.
  apply mk_quote_zx_mat.
  rewrite zx_triangle_semantics_alt.
  apply tensor_equiv_alt; repeat constructor; cbn -[QC2C];
  rewrite QC2C_Z; done.
Qed.

#[export] Instance quote_zx_mat_triangle_left :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => if vhd v || ¬ vhd w then 1%QC else 0%QC) zx_triangle_left.
Proof.
  pose proof quote_zx_mat_triangle as Hq.
  apply quote_zx_mat_transpose in Hq.
  exact Hq.
Qed.

#[export] Instance quote_zx_mat_state_0 :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => if vhd w then 0%QC else 1%QC) state_0.
Proof.
  apply mk_quote_zx_mat.
  rewrite state_0_semantics.
  apply tensor_equiv_alt; repeat constructor; cbn -[QC2C];
  rewrite QC2C_Z; done.
Qed.

#[export] Instance quote_zx_mat_state_1 :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => if vhd w then 1%QC else 0%QC) state_1.
Proof.
  apply mk_quote_zx_mat.
  rewrite state_1_semantics.
  apply tensor_equiv_alt; repeat constructor; cbn -[QC2C];
  rewrite QC2C_Z; done.
Qed.

#[export] Instance quote_zx_mat_state_b b :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => if eqb b (vhd w) then 1%QC else 0%QC) (state_b b).
Proof.
  apply mk_quote_zx_mat.
  rewrite state_b_semantics.
  apply tensor_equiv_alt; repeat constructor; destruct b; cbn -[QC2C];
  rewrite QC2C_Z; done.
Qed.

#[export] Instance quote_zx_mat_state_plus :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => mkQC 0 1 0 0) state_plus.
Proof.
  apply mk_quote_zx_mat.
  rewrite state_plus_semantics.
  apply tensor_equiv_alt; repeat constructor; cbn -[QC2C];
  unfold tensor_of_matrix, xbasis_plus; solve_C_eq.
Qed.

#[export] Instance quote_zx_mat_state_minus :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => mkQC 0 (if vhd w then -1 else 1) 0 0) state_minus.
Proof.
  apply mk_quote_zx_mat.
  rewrite state_minus_semantics.
  apply tensor_equiv_alt; repeat constructor; cbn -[QC2C];
  unfold tensor_of_matrix, xbasis_minus, Mplus, scale; cbn -[QC2C];
  solve_C_eq.
Qed.

#[export] Instance quote_zx_mat_uniform_state n :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => 1%QC) (uniform_state n).
Proof.
  apply mk_quote_zx_mat.
  rewrite uniform_state_semantics.
  rewrite make_WF_equiv.
  intros v w _ _.
  cbn -[QC2C].
  rewrite QC2C_Z.
  done.
Qed.

#[export] Instance quote_zx_mat_zero n m :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => 0%QC) (@zx_zero n m).
Proof.
  apply mk_quote_zx_mat.
  rewrite zx_zero_semantics.
  intros v w _ _.
  cbn -[QC2C].
  rewrite QC2C_Z.
  done.
Qed.

#[export] Instance quote_zx_mat_invsqrt2 :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => mkQC 0 1 0 0) (zx_invsqrt2).
Proof.
  apply mk_quote_zx_mat.
  rewrite zx_invsqrt2_semantics.
  intros v w _ _.
  inv_all_vec_fin.
  rewrite <- RtoC_inv.
  lca.
Qed.

#[export] Instance quote_zx_mat_two :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => mkQC 2 0 0 0) (zx_two).
Proof.
  apply mk_quote_zx_mat.
  rewrite zx_two_defn.
  intros v w _ _.
  inv_all_vec_fin.
  cbn.
  rewrite Cexp_0.
  lca.
Qed.

#[export] Instance quote_zx_mat_sqrt2 :
  GeneratorQuote zx_of_QC_tensor
    (fun v w => mkQC 0 2 0 0) (zx_sqrt2).
Proof.
  apply mk_quote_zx_mat.
  rewrite zx_sqrt2_semantics.
  intros v w _ _.
  inv_all_vec_fin.
  unfold tensor_of_matrix, scale.
  cbn.
  rewrite 2 Q2R_Z.
  rewrite Rdiv_0_l, 2 Rplus_0_l.
  change (?x, _) with (RtoC x).
  rewrite RtoC_div.
  C_field.
Qed.



From TensorRocqEx Require Import ZXrwsymm.

Import ZXsymm.

#[export] Instance QCeq_dec : RelDecision QCeq.
refine (fun r s => cast_if (bool_dec (QCeqb r s) true));
abstract(now rewrite <- QCeqb_iff; congruence).
Defined.

#[export] Instance QCtensor_dec n m : RelDecision (≡@{@Tensor QC n m bool}) :=
  tensor_equiv_dec QCeq_dec.

#[export] Instance QZXD2ZXD_TLH : TensorLikeHom' QC2C bool QZXD2ZXD.
Proof.
  split.
  - apply _.
  - apply _.
  - intros t n m.
    destruct t as [v|bd].
    + destruct v as [[([], z) | qc]|]; cbn.
      * now rewrite Qxsp_correct.
      * now rewrite Qzsp_correct.
      * done.
      * rewrite (tensor_apply_hom_tensor_to_dimensionless _).
        apply tensor_to_dimensionless_mor.
        now rewrite Qh_stack_correct.
    + induction bd as [(n', m') t].
      cbn -[unbundleDiagram].
      unfold unbundleDiagram.
      destruct (nat_pair_eq_dec_eval _ _) as [e|e];
        [|intros v w _ _; cbn -[QC2C]; solve_C_eq].
      cbn.
      injection e.
      intros <- <-.
      rewrite (proof_irrel e eq_refl).
      cbn [eq_rect_r eq_rect eq_sym].
      apply matrix_of_tensor_inj.
      rewrite ZX_tensor_semantics_correct.
      unfold zx_of_QC_tensor.
      rewrite zx_of_matrix_semantics by auto_wf.
      done.
Qed.


Ltac zxsolve_mid :=
  eapply (PRO_semantics_eq_by_quote QC2C bool _ QZXD2ZXD (TLH:=QZXD2ZXD_TLH)).

Ltac zxsolve :=
  zxsbypro;
  zxsolve_mid;
  [apply _..|];
  compute_done.




Module JPV.

(* Import ZXsymm ZXauto ZXfrob. *)

Local Open Scope C_scope.

Lemma zx_triangle_left_defn : zx_triangle_left = zx_triangle ⊤.
Proof. reflexivity. Qed.

Lemma zx_triangle_defn : zx_triangle = X 1 1 (PI / 2) ⟷ Z 1 1 (PI / 4) ⟷ (Z 0 1 (PI / 4) ↕ — ⟷ X 2 1 0)
⟷ (Z 1 2 0 ⟷ (— ↕ (X 1 2 0 ⟷ (Z 1 0 (- PI / 4) ↕ Z 1 0 (- PI / 4))))).
Proof. reflexivity. Qed.


Lemma cup_is_controlized :
  is_controlized ⊂
  cupcap_controlizer.
Proof.
  unfold is_controlized, is_controlled_state.
  split; zxsolve.
Qed.

Lemma box_is_controlized :
  is_controlized □
  box_controlizer.
Proof.
  unfold is_controlized, is_controlled_state.
  split; zxsolve.
Qed.

Lemma X_1_2_is_controlized :
  is_controlized (X 1 2 0)
  X_1_2_controlizer.
Proof.
  unfold is_controlized, is_controlled_state.
  split; zxsolve.
Qed.

Lemma JPV'_27 : Z 1 2 0 ⟷ (◁ ↕ —) ⟷ X 2 1 0 ∝= / √2 .* ◁.
Proof.
  zxsolve.
Qed.

Lemma X_0_0_PI_zero : X 0 0 PI ∝= zx_zero.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_17 : (— ↕ X 0 2 PI) ⟷ ((Z 2 1 0 ⟷ ▷) ↕ ◁) ⟷ (Z 2 1 0) ∝=
  /√ 2 .* (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  zxsolve.
Qed.

Lemma JPV_2_4_a : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 1 0 ⟷ X 1 0 0) ∝= ⦰.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_4_b : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 3 0 ⟷ X 3 0 0) ↕ Z 0 0 0 ∝= ⦰.
Proof.
  zxsolve.
Qed.


(* Lemma JPV_2_5 α β : (Z 0 1 PI ⟷ X 1 0 α) ↕ (Z 0 1 PI ⟷ X 1 0 β) ∝=
  (Z 0 1 PI ⟷ X 1 0 (α + β)) ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  apply transpose_diagrams_eq.
  cbn.
  apply const_of_zx_inj.
  rewrite 2 const_of_zx_stack.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite 3 const_of_zx_X_0_1_Z_1_0_gen.
  rewrite 5 (Cexp_add).
  rewrite Cexp_PI.
  C_field.
  lca.
Qed. *)

Lemma JPV_2_6 : Z 1 1 PI ⟷ X 1 2 0 ∝= X 1 2 0 ⟷ (Z 1 1 PI ↕ Z 1 1 PI).
Proof.
  zxsolve.
Qed.


(* FIXME: Move *)
Lemma fold_state_0 : X 0 1 0 ∝= √2 .* state_0.
Proof.
  zxsolve.
Qed.
Lemma fold_state_1 : X 0 1 PI ∝= √2 .* state_1.
Proof.
  zxsolve.
Qed.


Lemma JPV_2_7 : X 0 1 0 ⟷ zx_triangle ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  zxsolve.
Qed.

Lemma JPV_2_8 : X 0 1 0 ⟷ zx_triangle_left ∝= X 0 1 0.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_9 : X 0 1 PI ⟷ zx_triangle ∝= X 0 1 PI.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_10 : X 0 1 PI ⟷ zx_triangle_left ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  zxsolve.
Qed.

Lemma JPV_2_11 : X 1 1 PI ⟷ zx_triangle_left ∝= zx_triangle ⟷ X 1 1 PI.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_12 : Z 1 2 0 ⟷ (zx_triangle_left ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —) ∝=
  Z 1 2 0 ⟷ (X 1 2 0 ↕ zx_triangle_left) ⟷ (— ↕ Z 2 1 0).
Proof.
  zxsolve.
Qed.



Lemma JPV_2_13 : Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ (zx_triangle ⟷ zx_triangle)) ∝=
  zx_triangle ⟷ Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ —).
Proof.
  zxsolve.
Qed.

(* FIXME: Move *)
Lemma triangle_left_transpose : zx_triangle_left ⊤ = zx_triangle.
Proof.
  rewrite zx_triangle_left_defn.
  apply transpose_involutive_eq.
Qed.
Lemma zx_invsqrt2_defn' : zx_invsqrt2 ∝= Z 0 3 0 ⟷ X 3 0 0.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_14 : (Z 0 1 0 ⟷ zx_triangle) ↕
  (Z 0 1 0 ⟷ zx_triangle_left) ⟷ Z 2 1 0 ∝= Z 0 0 0 ↕ Z 0 1 0.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_15 : Z 1 2 0 ⟷ (□ ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝=
  (Z 0 3 0 ⟷ X 3 0 0) ↕
  zx_triangle_left ⟷ Z 1 1 PI.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_16 : Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝= —.
Proof.
  zxsolve.
Qed.

Local Open Scope C_scope.
Import Complex.

(* FIXME: Move *)
Lemma const_of_zx_zero : const_of_zx zx_zero = 0.
Proof.
  unfold const_of_zx.
  rewrite zx_zero_semantics.
  done.
Qed.
Lemma zx_of_const_0 : zx_of_const 0 ∝= zx_zero.
Proof.
  zxsolve.
Qed.
Lemma Z_2_1_0_states_b b c :
  state_b b ↕ state_b c ⟷ Z 2 1 0 ∝=
  (if eqb b c then state_b b else zx_zero).
Proof.
  destruct b, c; zxsolve.
Qed.


Lemma JPV_2_17' : Z 1 2 0 ⟷ (zx_triangle ↕ (X 1 1 PI ⟷ zx_triangle_left)) ⟷ Z 2 1 0 ∝=
  (X 0 3 0 ⟷ Z 3 0 0) ↕ (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  zxsolve.
Qed.

Lemma JPV_2_18_a : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 PI ⟷ zx_triangle_left) ↕
  zx_triangle_left) ⟷ Z 2 1 0) ∝=
  zx_triangle_left ↕ zx_triangle_left ⟷ Z 2 1 0.
Proof.
  zxsbypro.
  zxsolve_mid; [apply _..|].
  apply tensor_equiv_alt.
  Import Aux.
  vm_eval (sum_elements).
  constructor; [|admit].
  constructor; [|admit].
  vm_eval (PRO_semantics _ _ _).
  zxsolve.
Qed.

Lemma JPV_2_18_b : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 0 ⟷ zx_triangle) ↕
  zx_triangle) ⟷ Z 2 1 0) ∝=
  zx_triangle ↕ zx_triangle ⟷ Z 2 1 0.
Proof.
  zxsolve.
Qed.

(* FIXME: Remove when in VyZX: *)


Definition wrap_otl {n m o} (zx : ZX (n + m) o) : ZX m (n + o) :=
  n_cap n ↕ n_wire m ⟷
    cast _ _ (eq_sym (Nat.add_assoc _ _ _)) eq_refl (n_wire n ↕ zx).

Definition wrap_otr {n m o} (zx : ZX n (m + o)) : ZX (m + n) o :=
  cast _ _ eq_refl (eq_sym (Nat.add_assoc _ _ _)) (n_wire m ↕ zx)
  ⟷ (n_cup m ↕ n_wire o).

Definition wrap_ubl {n m o} (zx : ZX (n + m) o) : ZX n (o + m) :=
  cast _ _ (eq_sym (Nat.add_0_r _))
    (eq_sym (Nat.add_assoc _ _ _)) (n_wire n ↕ n_cap m) ⟷
    (zx ↕ n_wire m).

Definition wrap_ubr {n m o} (zx : ZX n (m + o)) : ZX (n + o) m :=
  (zx ↕ n_wire o) ⟷
    cast _ _ (eq_sym (Nat.add_assoc _ _ _))
      (eq_sym (Nat.add_0_r _)) (n_wire m ↕ n_cup o).
Import Setoid.

Add Parametric Morphism {n m o} : (@wrap_otl n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_otl_mor.
Proof.
  unfold wrap_otl.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_otr n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_otr_mor.
Proof.
  unfold wrap_otr.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_ubl n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_ubl_mor.
Proof.
  unfold wrap_ubl.
  now intros ? ? ->.
Qed.

Add Parametric Morphism {n m o} : (@wrap_ubr n m o) with signature
  proportional_by_1 ==> proportional_by_1 as wrap_ubr_mor.
Proof.
  unfold wrap_ubr.
  now intros ? ? ->.
Qed.


Global Arguments wrap_otl : simpl never.
Global Arguments wrap_otr : simpl never.
Global Arguments wrap_ubl : simpl never.
Global Arguments wrap_ubr : simpl never.

Import CastRules.

Lemma cast_compose_mid_distribute {n n' m o o' : nat}
  (m' : nat) (prfm : m' = m) (zx0 : ZX n m) (zx1 : ZX m o)
  prfn prfo :
  cast n' o' prfn prfo (zx0 ⟷ zx1) =
  cast n' m' prfn prfm zx0 ⟷ cast m' o' prfm prfo zx1.
Proof.
  subst.
  reflexivity.
Qed.


From TensorRocqEx Require Import ZXsrwsymm ZXsrwauto.
Import ZXmsymm.
  Import SizedProQuote.
  Import SizedRewriting SizedProLike.
  Import SizedPropsGraphs PropsGraphs.
Import ZXauto ZXmauto.

Import BWQuote.

Typeclasses Opaque n_cap n_cup.

Lemma wrap_otl_otr {n m o} (zx : ZX n (m + o)) :
  wrap_otl (wrap_otr zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  zxpacat.
Qed.

Lemma wrap_otr_otl {n m o} (zx : ZX (n + m) o) :
  wrap_otr (wrap_otl zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  zxpacat.
Qed.



Lemma wrap_ubl_ubr {n m o} (zx : ZX n (m + o)) :
  wrap_ubl (wrap_ubr zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  zxpacat.
Qed.


Lemma wrap_ubr_ubl {n m o} (zx : ZX (n + m) o) :
  wrap_ubr (wrap_ubl zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  zxpacat.
Qed.


Lemma wrap_over_top_left {n m o} (zx zx' : ZX (n + m) o) :
  wrap_otl zx ∝= wrap_otl zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_otr_mor.
  now rewrite 2 wrap_otr_otl in Hzx.
Qed.

Lemma wrap_over_top_right {n m o} zx zx' :
  wrap_otr zx ∝= @wrap_otr n m o zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_otl_mor.
  now rewrite 2 wrap_otl_otr in Hzx.
Qed.

Lemma wrap_under_bottom_left {n m o} (zx zx' : ZX (n + m) o) :
  wrap_ubl zx ∝= wrap_ubl zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_ubr_mor.
  now rewrite 2 wrap_ubr_ubl in Hzx.
Qed.

Lemma wrap_under_bottom_right {n m o} zx zx' :
  wrap_ubr zx ∝= @wrap_ubr n m o zx' ->
	zx ∝= zx'.
Proof.
  intros Hzx%wrap_ubl_mor.
  now rewrite 2 wrap_ubl_ubr in Hzx.
Qed.


Lemma wrap_otl_compose {n m o p} (zx0 : ZX (n + m) o) (zx1 : ZX o p) :
  wrap_otl (zx0 ⟷ zx1) ∝= wrap_otl zx0 ⟷ (n_wire n ↕ zx1).
Proof.
  unfold wrap_otl.
  rewrite stack_nwire_distribute_l, <- cast_compose_l_eq_mid.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_otr_compose {n m o p} (zx0 : ZX n m) (zx1 : ZX m (o + p)) :
  wrap_otr (zx0 ⟷ zx1) ∝= (n_wire o ↕ zx0) ⟷ wrap_otr zx1.
Proof.
  unfold wrap_otr.
  rewrite stack_nwire_distribute_l, <- cast_compose_r_eq_mid.
  rewrite compose_assoc.
  reflexivity.
Qed.


Lemma wrap_ubl_compose {n m o p} (zx0 : ZX (n + m) o) (zx1 : ZX o p) :
  wrap_ubl (zx0 ⟷ zx1) ∝= wrap_ubl zx0 ⟷ (zx1 ↕ n_wire m).
Proof.
  unfold wrap_ubl.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_ubr_compose {n m o p} (zx0 : ZX n m) (zx1 : ZX m (o + p)) :
  wrap_ubr (zx0 ⟷ zx1) ∝= (zx0 ↕ n_wire p) ⟷ wrap_ubr zx1.
Proof.
  unfold wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  reflexivity.
Qed.

Lemma wrap_otl_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_otl (zx0 ↕ zx1) ∝=
  cast o _ eq_refl (Nat.add_assoc _ _ _) (proc_to_state zx0 ↕ zx1).
Proof.
  unfold wrap_otl, proc_to_state.
  zxpacat.
Qed.

Lemma wrap_otr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_otr (zx0 ↕ zx1) ∝=
  cast _ _ (Nat.add_assoc _ _ _) eq_refl ((n_wire m ↕ zx0 ⟷ n_cup m) ↕ zx1).
Proof.
  unfold wrap_otr.
  zxpacat.
Qed.


Lemma wrap_ubl_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubl (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_0_r _)) (eq_sym (Nat.add_assoc _ _ _))
    (zx0 ↕ (n_cap o ⟷ (zx1 ↕ n_wire o))).
Proof.
  unfold wrap_ubl.
  zxpacat.
Qed.

Lemma wrap_ubr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubr (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_0_r _))
    (zx0 ↕ (zx1 ↕ n_wire p ⟷ n_cup p)).
Proof.
  unfold wrap_ubr.
  zxpacat.
Qed.



Lemma wrap_otl_transpose {n m o} zx :
	(@wrap_otl n m o zx) ⊤ ∝= wrap_otr (zx ⊤).
Proof.
	unfold wrap_otl, wrap_otr.
  rewrite 2 transpose_to_big_yank_l.
  zxpacat.
Qed.

Lemma wrap_otr_transpose {n m o} zx :
	(@wrap_otr n m o zx) ⊤ ∝= wrap_otl (zx ⊤).
Proof.
	apply transpose_diagrams_eq.
	rewrite wrap_otl_transpose.
	now rewrite 2!transpose_involutive.
Qed.

Lemma wrap_ubl_transpose {n m o} zx :
	(@wrap_ubl n m o zx) ⊤ ∝= wrap_ubr (zx ⊤).
Proof.
	unfold wrap_ubl, wrap_ubr.
  rewrite 2 transpose_to_big_yank_l.
  zxpacat.
Qed.

Lemma wrap_ubr_transpose {n m o} zx :
	(@wrap_ubr n m o zx) ⊤ ∝= wrap_ubl (zx ⊤).
Proof.
	apply transpose_diagrams_eq.
	rewrite wrap_ubl_transpose.
	now rewrite 2!transpose_involutive.
Qed.

#[export] Hint Rewrite
  @wrap_otl_transpose @wrap_otr_transpose
  @wrap_otl_transpose @wrap_otr_transpose : transpose_db.


Lemma wrap_otl_colorswap {n m o} zx :
	⊙ (@wrap_otl n m o zx) ∝= wrap_otl (⊙ zx).
Proof.
	unfold wrap_otl.
	cbn [color_swap].
	rewrite n_cap_colorswap, cast_colorswap.
	cbn [color_swap].
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_otr_colorswap {n m o} zx :
	⊙ (@wrap_otr n m o zx) ∝= wrap_otr (⊙ zx).
Proof.
	unfold wrap_otr.
	cbn [color_swap].
	rewrite n_cup_colorswap, cast_colorswap.
	cbn [color_swap].
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_ubl_colorswap {n m o} zx :
	⊙ (@wrap_ubl n m o zx) ∝= wrap_ubl (⊙ zx).
Proof.
	unfold wrap_ubl.
	cbn [color_swap].
	rewrite cast_colorswap.
	cbn [color_swap].
	rewrite n_cap_colorswap.
	now rewrite !n_wire_colorswap.
Qed.

Lemma wrap_ubr_colorswap {n m o} zx :
	⊙ (@wrap_ubr n m o zx) ∝= wrap_ubr (⊙ zx).
Proof.
	unfold wrap_ubr.
	cbn [color_swap].
	rewrite cast_colorswap.
	cbn [color_swap].
	rewrite n_cup_colorswap.
	now rewrite !n_wire_colorswap.
Qed.

#[export] Hint Rewrite
  @wrap_otl_colorswap @wrap_otr_colorswap
  @wrap_otl_colorswap @wrap_otr_colorswap : colorswap_db.


(* FIXME: Move *)
Lemma zx_of_const_transpose c : (zx_of_const c) ⊤ ∝= zx_of_const c.
Proof.
  prep_matrix_equivalence; rewrite semantics_transpose_comm; now by_cell.
Qed.
Lemma fold_state_plus : Z 0 1 0 ∝= √ 2 .* state_plus.
Proof.
  zxsolve.
Qed.
Lemma fold_state_minus : Z 0 1 PI ∝= √ 2 .* state_minus.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_19 : (— ↕ (Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left))) ⟷
  (X 2 1 PI ↕ —) ⟷ Z 2 1 0 ∝=
  ((Z 1 2 0 ⟷ (zx_triangle_left ↕ zx_triangle)) ↕ —) ⟷
  (— ↕ X 2 1 PI) ⟷ Z 2 1 0.
Proof.
  zxsolve.
Qed.

(* FIXME: Move *)
Lemma zx_invsqrt2_to_const :
  zx_invsqrt2 ∝= zx_of_const (/ √ 2).
Proof.
  zxsolve.
Qed.

Lemma JPV_2_20 : (Z 0 1 0 ⟷ X 1 0 0) ↕ (Z 1 2 0 ⟷ (— ↕ zx_triangle_left) ⟷ X 2 1 0) ∝=
  zx_triangle_left.
Proof.
  zxsolve.
Qed.

(* FIXME: Move *)
Lemma triangle_state_plus : state_plus ⟷ zx_triangle ∝= state_plus .+ / √ 2 .* state_1.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_semantics.
  rewrite zx_plus_semantics, zx_scale_semantics.
  rewrite state_plus_semantics, state_1_semantics.
  by_cell; lca.
Qed.

Lemma triangle_state_minus : state_minus ⟷ zx_triangle ∝= / √ 2 .* state_0.
Proof.
  zxsolve.
Qed.

Lemma left_triangle_state_plus : state_plus ⟷ zx_triangle_left ∝= state_plus .+ / √ 2 .* state_0.
Proof.
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_left_semantics.
  rewrite zx_plus_semantics, zx_scale_semantics.
  rewrite state_plus_semantics, state_0_semantics.
  by_cell; lca.
Qed.

Lemma left_triangle_state_minus : state_minus ⟷ zx_triangle_left ∝= - / √ 2 .* state_1.
Proof.
  zxsolve.
Qed.

Lemma JPV_2_21 : zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI
  ∝= Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left.
Proof.
  zxsolve.
Qed.

(* FIXME: Unstateable! Lemma JPV_2_22 : ... *)

Lemma JPV_2_23 β : X 0 1 PI ⟷ zx_triangle_left ⟷ Z 1 2 PI ⟷
  (zx_triangle_left ↕ X 1 2 β) ⟷ ((Z 2 1 PI ⟷ X 1 0 0) ↕ —) ∝=
  (Z 0 1 0 ⟷ X 1 0 0) ↕ (Z 0 1 PI ⟷ X 1 1 β).
Proof.
  zxsrw JPV_2_10.
  zxsrw (gadget_is_scaled_empty (Z 0 1 0 ⟷ X 1 0 0)).
  zxsrw (gadget_is_scaled_empty (Z 0 1 0 ⟷ X 1 0 0)).
  f_equiv.
  pose proof (f_equiv transpose (to_gadget (X_state_copy 0 2 PI eq_refl eq_refl))) as Hrw.
  rewrite Rmult_0_l, Cexp_0, Cexp_PI in Hrw.
  cbn in Hrw.
  rewrite zx_of_const_transpose in Hrw.
  zxsrw Hrw.
  clear Hrw.
  zxsrw (@Z_spider_1_1_fusion 0 2 0 PI).
  pose proof (f_equiv transpose JPV_2_7) as Hrw.
  cbn in Hrw.
  rewrite triangle_transpose in Hrw.
  zxsrw Hrw.
  clear Hrw.
  zxsrw (dominated_X_spider_fusion_top_left 0 0 1 1 0 β).
  zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 0 0 PI).
  zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_of_const_mult'.
  replace (Cmult _ _) with C1 by (autorewrite with RtoC_db; C_field; lca).
  rewrite <- zx_scale_defn, zx_scale_1_l.
  zxscat.
Qed.



Lemma JPV_2_24 β : Z 1 2 0 ⟷ ((zx_triangle ⟷ X 1 1 β) ↕ (zx_triangle_left ⟷ X 1 1 β))
  ⟷ (— ↕ Z 1 2 0) ⟷ (X 2 1 PI ↕ —) ∝=
  Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left)
  ⟷ (— ↕ Z 1 2 0) ⟷ (X 2 1 PI ↕ X 1 1 β).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  do 2 zxsrw (Z_1_2_state_b 0 b).
  do 2 zxsrw (triangle_state_b b).
  do 2 zxsrw (left_triangle_state_b b).
  f_equiv.
  destruct b.
  - zxsrw (to_gadget (Z_state_copy' false 1 β eq_refl eq_refl)).
    rewrite zx_of_const_1' by (cbn; C_field; lca).
    zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    zxaclean_lhs.
    zxsrw <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxarw_rhs <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxsrw (@X_1_n_state_1 1 β).
    zxsrw (@X_spider_1_1_fusion 0 2 (PI + β) PI).
    zxsrw (@X_1_n_state_1 2 PI).
    f_equiv.
    rewrite <- (X_proc_to_state 1 1 β).
    unfold proc_to_state.
    zxacat.
  - zxsrw (to_gadget (Z_state_copy' false 1 β eq_refl eq_refl)).
    rewrite zx_of_const_1' by (cbn; C_field; lca).
    zxsrw (@X_1_n_state_0 1 β).
    zxarw_lhs <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxsrw (to_gadget (Z_state_copy' false 2 PI eq_refl eq_refl)).
    rewrite <- zx_of_const_mult'.
    rewrite (f_equal zx_of_const (y:=/ C2)) by (cbn; C_field).
    zxsrw (dominated_Z_spider_fusion_top_right 0 0 1 0 0 0).
    zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 1 0 0).
    zxsrw (Z_1_2_state_0 0).
    zxarw_rhs <- (X_wrap_under_bot_left 1 1 PI eq_refl eq_refl).
    zxsrw (to_gadget (Z_state_copy' false 2 PI eq_refl eq_refl)).
    symmetry.
    rewrite (f_equal zx_of_const (y:=/√2)) by
      (cbn; C_field; lca).
    zxsrw (dominated_Z_spider_fusion_top_right 0 0 1 0 0 0).
    zxsrw (Z_1_n_state0 0 0).
    zxsrw (@X_1_n_state_0 1 β).
    rewrite <- zx_of_const_mult'.
    rewrite (f_equal zx_of_const (y:=/ C2)) by C_field.
    zxscat.
Qed.

(* FIXME: Move *)
Lemma to_const (zx : ZX 0 0) : zx ∝= zx_of_const (const_of_zx zx).
Proof.
  apply const_of_zx_inj.
  now rewrite const_of_zx_of_const.
Qed.

Lemma Z_2_1_states_b b c α :
  state_b b ↕ state_b c ⟷ Z 2 1 α ∝=
  (if eqb b c then (if b then Cexp α else C1) .* state_b b else zx_zero).
Proof.
  rewrite <- (Rplus_0_l α), <- Z_spider_1_1_fusion.
  rewrite <- compose_assoc.
  rewrite (Z_2_1_0_states_b b c).
  destruct (eqb b c); [|now rewrite compose_0_l].
  rewrite (Z_1_n_state_b b 1 α).
  rewrite Rplus_0_l, n_stack_1, 2 cast_id_eq.
  done.
Qed.


Lemma JPV_2_25 :
  (X 1 1 PI ⟷ Z 1 2 0) ↕
  (X 0 1 0 ⟷ Z 1 2 PI) ⟷
  (— ↕ (zx_triangle_left ↕ zx_triangle ⟷ Z 2 2 PI) ↕ —) ⟷
  (X 2 1 0 ↕ X 2 1 0) ⟷ ⨉ ∝=
  - C1 .*
  (Z 1 2 PI) ↕
  (X 0 1 PI ⟷ Z 1 2 PI) ⟷
  (— ↕ (zx_triangle ↕ zx_triangle_left ⟷ Z 2 2 PI) ↕ —) ⟷
  (X 2 1 0 ↕ X 2 1 0).
Proof.
  zxsolve.
Qed.


Fixpoint JPV_2_22_lhs_aux n : ZX (1 + (1 + n)) 1 :=
  match n with
  | 0 => Z (1 + 1) 1 0
  | S n =>
    — ↕ ((Z (1 + 1) 1 0 ⟷ zx_triangle_left) ↕ n_wire n) ⟷ JPV_2_22_lhs_aux n
  end.



Lemma JPV_2_22_aux :
  ⊂ ⟷ (◁ ↕ —) ⟷ Z 2 1 0 ∝= Z 0 1 0.
Proof.
  zxsolve.
Qed.


(* @nocheck name *)
(* Conventional name *)
Lemma completeness_BW :
	◁ ⟷ Z 1 1 PI ⟷ ▷ ∝= ▷ ⟷ X 1 1 PI.
Proof.
  zxsbypro.
  zxsolve_mid; [apply _..|].
  apply tensor_equiv_alt.
  Import Aux.
  vm_eval (sum_elements).
  apply Forall_cons.
  split; [|admit].
  apply Forall_cons.
  split; [|admit].
  vm_eval (PRO_semantics _ _ _).

  remember QCeq as f.
  vm_compute.
  zxsolve.
Qed.

Ring_polynom.Pol

Lemma JPV_2_22 n :
  Z 0 1 0 ↕ Z 0 1 0 ↕ n_wire n ⟷ JPV_2_22_lhs_aux n ∝=
  (⊂ ⟷ (zx_triangle_left ↕ —)) ↕ n_wire n ⟷ JPV_2_22_lhs_aux n.
Proof.
  assert (n = 2) as -> by admit.
  cbn.
  zxsolve.
  induction n.
  - cbn.
    zxfclean.
    zxsrw JPV_2_22_aux.
    done.
  - cbn -[n_wire].

    zxpsrw_rhs JPV_2_22_aux.

  assert (n = 1)%nat as -> by admit.
  cbn.
  zxsclean.
  zxfclean. *)


(* Lemma JPV_2_26 *)

End JPV.
(* Goal True.
eassert (Quote_R_div_PI4 _ ((- PI / 12 * -6 + /4 * - 4 * PI * / - 4))).
apply _.
field_simplify (((- PI / 12 * -6 + /4 * - 4 * PI * / - 4) / PI))%R; [|apply PI_neq_0..].
apply _.


ring_simplify (3 * PI / 4)%R. rsimpl_modeq_2PI_tac. *)
