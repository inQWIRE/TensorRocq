From TensorRocq Require Export Tensor.
From TensorRocq Require Import Aux_stdpp. 
From TensorRocqEx Require Export ZXCore.
From VyZX Require Export CoreData.
Require Export QlibInterface.
From stdpp Require Import vector. 

Local Open Scope C_scope.

Lemma Z_semantics_alt n m α i j : 
  Z_semantics n m α i j = 
  (if (i =? 0) && (j =? 0) then C1 else C0) + 
  (if (i =? 2 ^ m - 1) && (j =? 2 ^ n - 1) then Cexp α else C0).
Proof.
  unfold Z_semantics.
  destruct i; [destruct j; [destruct n; [destruct m|]|]|].
  - reflexivity.
  - pose proof (pow_positive 2 m ltac:(easy)).
    cbn [Nat.pow].
    replace_bool_lia (0 =? 2 * 2 ^ m - 1) false.
    lca.
  - pose proof (pow_positive 2 n ltac:(easy)).
    cbn [Nat.pow].
    replace_bool_lia (0 =? 2 * 2 ^ n - 1) false.
    rewrite andb_false_r.
    lca.
  - rewrite andb_false_r, Cplus_0_l.
    reflexivity.
  - rewrite andb_false_l, Cplus_0_l.
    reflexivity.
Qed.

(* FIXME: Move *)
Lemma allb_iff_eq_const {n} (v : Vector.t bool n) b : 
  allb b v = true <-> v = Vector.const b n.
Proof.
  induction v.
  - simpl.
    split; reflexivity.
  - simpl.
    rewrite andb_true_iff.
    rewrite Bool.eqb_true_iff, IHv.
    split; [intros []; congruence|intros ?%Vector.cons_inj; easy].
Qed.

(* FIXME: Move *) 
Lemma rev_const {A n} (a : A) :
  Vector.rev (Vector.const a n) = Vector.const a n.
Proof.
  apply Vector.to_list_inj.
  rewrite Vector.to_list_rev, Vector.to_list_const.
  rewrite rev_repeat.
  reflexivity.
Qed.

Lemma allb_rev {n} (v : Vector.t bool n) b : 
  allb b (Vector.rev v) = allb b v.
Proof.
  apply Bool.eq_iff_eq_true.
  rewrite 2!allb_iff_eq_const.
  split.
  - intros H%(f_equal Vector.rev).
    rewrite Vector.rev_rev, rev_const in H.
    auto.
  - intros ->.
    rewrite rev_const.
    reflexivity.
Qed.

Lemma vlookup_eq_nth {A n} (v : vec A n) i : 
  v !!! i = Vector.nth v i.
Proof.
  revert i; induction v; [apply fin_0_inv|apply fin_S_inv; [done|]].
  intros i.
  apply IHv.
Qed.

Lemma allb_false_nat_to_bits n i : (i < 2 ^ n)%nat -> 
  allb false (nat_to_bits n i) = (i =? 0).
Proof.
  intros Hi.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite allb_iff_eq_const.
  split.
  - intros Heq.
    apply Nat.bits_inj.
    intros k.
    rewrite Nat.bits_0.
    bdestruct (k <? n).
    + assert (Hk : (n - S k < n)%nat) by lia.
      apply (f_equal (.!!! (Fin.of_nat_lt Hk))) in Heq.
      rewrite nth_nat_to_bits in Heq.
      rewrite fin.fin_to_nat_to_fin in Heq.
      rewrite vlookup_eq_nth, Vector.const_nth in Heq.
      rewrite <- Heq.
      f_equal; lia.
    + replace i with (i mod 2 ^ n) by (apply Nat.mod_small; auto).
      rewrite Nat.mod_pow2_bits_high by easy.
      reflexivity.
  - intros ->.
    apply vec_eq.
    intros p.
    rewrite nth_nat_to_bits, vlookup_eq_nth, Vector.const_nth.
    apply Nat.bits_0.
Qed.

(* FIXME: Move *)
Lemma testbit_pow_2_sub_1 n k : 
  Nat.testbit (2 ^ n - 1) k = (k <? n).
Proof.
  revert k.
  induction n.
  - apply Nat.bits_0.
  - intros [|k].
    + cbn -[Nat.pow].
      rewrite Nat.odd_sub by (apply pow_positive; lia).
      rewrite Nat.odd_pow by easy.
      reflexivity.
    + cbn [Nat.testbit].
      rewrite Nat.div2_div.
      change (?x = _) with (x = (k <? n)).
      rewrite <- IHn.
      f_equal.
      cbn [Nat.pow].
      rewrite Nat.mul_comm.
      rewrite div_sub by easy.
      rewrite Nat.sub_0_r.
      reflexivity.
Qed.


Lemma allb_true_nat_to_bits n i : (i < 2 ^ n)%nat -> 
  allb true (nat_to_bits n i) = (i =? 2 ^ n - 1).
Proof.
  intros Hi.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite allb_iff_eq_const.
  split.
  - intros Heq.
    apply (f_equal vec_to_list) in Heq.
    rewrite nat_to_bits_to_list in Heq by easy.
    rewrite vec_to_list_to_list, Vector.to_list_const in Heq.
    apply (f_equal reverse) in Heq.
    rewrite reverse_involutive, <- rev_reverse, rev_repeat in Heq.
    apply (f_equal binlist_to_nat) in Heq.
    rewrite nat_to_binlist_inverse in Heq.
    rewrite Heq.
    apply binlist_to_nat_true.
  - intros ->.
    apply vec_eq; intros p.
    rewrite nth_nat_to_bits.
    rewrite testbit_pow_2_sub_1.
    rewrite vlookup_eq_nth, Vector.const_nth.
    apply Nat.ltb_lt.
    rewrite <- fin_to_nat_rev.
    apply fin.fin_to_nat_lt.
Qed.


Lemma matrix_of_Z_tensor n m α : 
  matrix_of_tensor (@zsp n m α) = 
  Z_semantics n m α.
Proof.
  prep_matrix_equivalence.
  unfold matrix_of_tensor, zsp.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  unfold zsp.
  rewrite Z_semantics_alt.
  f_equal.
  - apply f_equal_if; [|reflexivity..].
    rewrite 2!allb_false_nat_to_bits by easy.
    apply andb_comm.
  - apply f_equal_if; [|reflexivity..].
    rewrite 2!allb_true_nat_to_bits by easy.
    apply andb_comm.
Qed.



Lemma xsp_decomp n m α : 
  @xsp n m α ≡ compose_tensor (compose_tensor h_stack (zsp α)) h_stack.
Proof.
  intros v w Hv Hw.
  rewrite xsp_colorswap.
  cbn.
  unfold xsp_by_h, bihadamard.
  rewrite sum_of_comm.
  apply sum_of_ext; intros ds.
  now rewrite sum_of_distr_l.
Qed.


Lemma matrix_of_X_tensor n m α : 
  matrix_of_tensor (@xsp n m α) = 
  X_semantics n m α.
Proof.
  prep_matrix_equivalence.
  rewrite xsp_decomp.
  rewrite 2 matrix_of_tensor_compose, 2 matrix_of_tensor_h_stack, 
    matrix_of_Z_tensor, <- Mmult_assoc.
  reflexivity.
Qed.



Fixpoint ZX_tensor_semantics {n m} (zx : ZX n m) : @Tensor C n m bool :=
  match zx with 
  | ⦰ => delta_tensor
  | ⊂ => cup_tensor (n:=1)
  | ⊃ => cap_tensor (n:=1)
  | ⨉ => swap_tensor (n:=1) (m:=1)
  | — => delta_tensor
  | □ => h_stack
  | X n m α => xsp α
  | Z n m α => zsp α
  | zx0 ↕ zx1 => stack_tensor (ZX_tensor_semantics zx0) (ZX_tensor_semantics zx1)
  | zx0 ⟷ zx1 => compose_tensor (ZX_tensor_semantics zx0) (ZX_tensor_semantics zx1)
  end.




Lemma ZX_tensor_semantics_correct {n m} (zx : ZX n m) :
  matrix_of_tensor (ZX_tensor_semantics zx) = ZX_semantics zx.
Proof.
  induction zx.
  - cbn.
    now rewrite matrix_of_tensor_delta.
  - apply matrix_of_tensor_cup.
  - apply matrix_of_tensor_cap.
  - apply matrix_of_tensor_swap.
  - apply matrix_of_tensor_delta.
  - apply matrix_of_tensor_H.
  - apply matrix_of_X_tensor.
  - apply matrix_of_Z_tensor.
  - cbn.
    rewrite matrix_of_tensor_stack.
    congruence.
  - cbn.
    rewrite matrix_of_tensor_compose.
    congruence.
Qed.

