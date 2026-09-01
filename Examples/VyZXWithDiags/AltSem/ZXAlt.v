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

(* FIXME: Move *)
Lemma xorb_if {A} (a a' : A) (b b' : bool) :
  (if xorb b b' then a else a') =
  if b then if b' then a' else a else if b' then a else a'.
Proof.
  destruct b, b'; done.
Qed.

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
    rewrite (tensor_apply_hom_stack _ (n:=1) (m:=1)).
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
#[export] Instance sum_map_proper `{RA : relation A, RA' : relation A',
  RB : relation B, RB' : relation B'} (f : A -> B) (f' : A' -> B')
  {Hf : Proper (RA ==> RB) f} {Hf' : Proper (RA' ==> RB') f'} :
  Proper (sum_relation RA RA' ==> sum_relation RB RB') (sum_map f f').
Proof.
  intros a b Hab.
  induction Hab; cbn; constructor; now f_equiv.
Qed.

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
    | Pcompose _ _ =>
      apply (PRO_quote_compose f);
      go
    | Pstack _ _ =>
      apply (PRO_quote_stack f);
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





(* Goal True.
eassert (Quote_R_div_PI4 _ ((- PI / 12 * -6 + /4 * - 4 * PI * / - 4))).
apply _.
field_simplify (((- PI / 12 * -6 + /4 * - 4 * PI * / - 4) / PI))%R; [|apply PI_neq_0..].
apply _.


ring_simplify (3 * PI / 4)%R. rsimpl_modeq_2PI_tac. *)
