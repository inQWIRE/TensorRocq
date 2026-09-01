From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.

From TensorRocqEx Require Import VyZXExample_withdiags.


Import ZXsymm ZXauto ZXfrob.


Import ZXmsymm.
  Import SizedProQuote.
  Import SizedRewriting SizedProLike.
  Import SizedPropsGraphs PropsGraphs.

Import BW.

Import ComposeRules.

Open Scope nat_scope.

Ltac visualize_flag ::= fail.


From TensorRocqEx Require Export NonZXAux.
Import prf_notations.
Import ComposeRules.

Open Scope nat_scope.

Import ZXsymm ZXauto ZXfrob.




Lemma gadget_transpose (zx : ZX 0 0) : transpose zx ∝= zx.
Proof.
  prep_matrix_equivalence.
  rewrite semantics_transpose_comm.
  by_cell; done.
Qed.


Lemma gadget_colorswap (zx : ZX 0 0) : ⊙ zx ∝= zx.
Proof.
  rewrite colorswap_is_bihadamard.
  cbn.
  now rewrite compose_empty_r, compose_empty_l.
Qed.

Lemma transpose_to_big_yank_l {n m} (zx : ZX n m) :
  zx ⊤ ∝= (n_cap n ⟷ (n_wire n ↕ zx)) ↕ n_wire m ⟷
    cast _ _ add_assoc' add_0_r' (n_wire n ↕ n_cup m).
Proof.
  rewrite n_cap_pullthrough_bot.
  rewrite stack_nwire_distribute_r.
  rewrite compose_assoc.
  rewrite stack_assoc_fwd, cast_compose_eq_mid_join.
  rewrite n_wire_stack, <- stack_split_diag, (stack_split_antidiag (zx ⊤)).
  rewrite stack_empty_r_fwd, (cast_compose_r _ _ _ (zx ⊤)), cast_contract_eq'.
  rewrite cast_compose_distribute, cast_id, cast_contract_eq'.
  rewrite <- compose_assoc.
  rewrite big_yank_l, nwire_removal_l.
  done.
Qed.

Lemma transpose_to_big_yank_r {n m} (zx : ZX n m) :
  zx ⊤ ∝= cast _ _ add_0_r' add_assoc' (n_wire m ↕ n_cap n)
  ⟷ (((n_wire m ↕ zx) ⟷ n_cup m) ↕ n_wire n).
Proof.
  apply transpose_diagrams_eq.
  autorewrite with transpose_db.
  cbn [transpose].
  rewrite cast_transpose.
  cbn [transpose].
  rewrite 2 n_wire_transpose, n_cap_transpose, n_cup_transpose.
  rewrite <- transpose_to_big_yank_l.
  done.
Qed.





(* FIXME: Move *)
Lemma zx_scale_sqrt2_alt {n m} (zx : ZX n m) :
  √ 2 .* zx ∝= (Z 0 1 0 ⟷ X 1 0 0) ↕ zx.
Proof.
  rewrite gadget_is_scaled_empty.
  rewrite zx_scale_stack_distr_l, stack_empty_l.
  f_equiv.
  cbn.
  unfold kron, I; simpl.
  rewrite Cexp_0.
  C_field; lca.
Qed.

(* FIXME: Move *)
Lemma Z_state_copy' (b : bool) n a prfn prfm :
  Z 0 1 (if b then PI else 0) ⟷ X 1 n a ∝[
    (/ √2 ^ S n) * (if b then C2 * Cexp a else C2)
  ] cast _ _ prfn prfm (n ⇑ Z 0 1 (if b then PI else 0)).
Proof.
  destruct b.
  - specialize (Z_state_copy 1 n a prfn prfm) as Hrw.
    rewrite Rmult_1_l, Cexp_PI in Hrw.
    replace (_ + _)%C with (C2 * Cexp a)%C in Hrw by lca.
    rewrite RtoC_inv, <- RtoC_pow in Hrw.
    done.
  - specialize (Z_state_copy 0 n a prfn prfm) as Hrw.
    rewrite Rmult_0_l, Cexp_0 in Hrw.
    refine (eq_rect _ (λ c, _ ∝[c] _) Hrw _ _).
    rewrite RtoC_inv, <- RtoC_pow.
    lca.
Qed.

Lemma X_state_copy' (b : bool) n a prfn prfm :
  X 0 1 (if b then PI else 0) ⟷ Z 1 n a ∝[
    (/ √2 ^ S n) * (if b then C2 * Cexp a else C2)
  ] cast _ _ prfn prfm (n ⇑ X 0 1 (if b then PI else 0)).
Proof.
  colorswap_of (Z_state_copy' b n a prfn prfm).
Qed.

Lemma Z_state_copy'' (b : bool) n a prfn prfm :
  Z 0 1 (if b then PI else 0) ⟷ X 1 n a ∝[
    match n with
    | O => if b then √ 2 * Cexp a else √ 2
    | S O => if b then Cexp a else C1
    | S (S n) =>
      if b then (/ √2 ^ (S n)) * Cexp a else (/ √ 2 ^ S n)
    end%C
  ] cast _ _ prfn prfm (n ⇑ Z 0 1 (if b then PI else 0)).
Proof.
  specialize (Z_state_copy' b n a prfn prfm) as Hrw.
  refine (eq_rect _ (λ c, _ ∝[c] _) Hrw _ _).
  destruct n; [destruct b; cbn; C_field; lca|].
  destruct n; [destruct b; cbn; C_field; lca|].
  destruct b; cbn; C_field; lca.
Qed.

Lemma X_state_copy'' (b : bool) n a prfn prfm :
  X 0 1 (if b then PI else 0) ⟷ Z 1 n a ∝[
    match n with
    | O => if b then √ 2 * Cexp a else √ 2
    | S O => if b then Cexp a else C1
    | S (S n) =>
      if b then (/ √2 ^ (S n)) * Cexp a else (/ √ 2 ^ S n)
    end
  ] cast _ _ prfn prfm (n ⇑ X 0 1 (if b then PI else 0)).
Proof.
  colorswap_of (Z_state_copy'' b n a prfn prfm).
Qed.

(* FIXME: Move *)
#[export] Instance const_of_zx_inj : Inj proportional_by_1 eq const_of_zx.
Proof.
  intros zx zx' Heq.
  rewrite gadget_is_scaled_empty, Heq, <- gadget_is_scaled_empty.
  done.
Qed.

(* FIXME: Move*)
Lemma const_of_zx_of_const c : const_of_zx (zx_of_const c) = c.
Proof.
  unfold const_of_zx.
  rewrite zx_of_const_semantics.
  lca.
Qed.

Lemma const_of_zx_scale c zx : const_of_zx (c .* zx) = Cmult c (const_of_zx zx).
Proof.
  unfold const_of_zx.
  rewrite zx_scale_semantics.
  done.
Qed.

Lemma zx_of_const_1 : zx_of_const C1 ∝= ⦰.
Proof.
  rewrite gadget_is_scaled_empty.
  apply zx_scale_eq_1_l.
  now rewrite const_of_zx_of_const.
Qed.

Lemma zx_of_const_1' c : c = C1 -> zx_of_const c ∝= ⦰.
Proof.
  intros ->.
  apply zx_of_const_1.
Qed.

Lemma zx_of_const_invsqrt2 : zx_of_const (/ √ 2) ∝= zx_invsqrt2.
Proof.
  apply (inj const_of_zx).
  rewrite const_of_zx_of_const, const_of_zx_invsqrt2.
  done.
Qed.


Lemma const_of_zx_sqrt2 : const_of_zx zx_sqrt2 = √ 2.
Proof.
  unfold const_of_zx.
  rewrite zx_sqrt2_semantics.
  lca.
Qed.

Lemma zx_of_const_sqrt2 : zx_of_const (√ 2) ∝= zx_sqrt2.
Proof.
  apply (inj const_of_zx).
  rewrite const_of_zx_of_const, const_of_zx_sqrt2.
  done.
Qed.

Lemma zx_sqrt2_defn'_XZ : zx_sqrt2 ∝= X 0 1 0 ⟷ Z 1 0 0.
Proof.
  apply (inj const_of_zx).
  rewrite const_of_zx_sqrt2.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  done.
Qed.

Lemma zx_sqrt2_defn'_ZX : zx_sqrt2 ∝= Z 0 1 0 ⟷ X 1 0 0.
Proof.
  apply (inj const_of_zx).
  rewrite const_of_zx_sqrt2.
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  done.
Qed.




Lemma zx_mul_S_r_stack n m k prf1 prf3 prf4 :
  zx_mul_S_r (n + m) k ⟷ cast _ _ prf1 eq_refl (zx_mid_comm n m (n * k) (m * k)) ∝=
  cast _ _ prf3 prf4 (zx_mul_S_r n k ↕ zx_mul_S_r m k).
Proof.
  prop_perm_eq_nosimpl.
  eapply eq_of_WF_perm_eq; [auto_perm..|].
  cbn [perm_of_zx].
  rewrite 2 perm_of_zx_cast.
  cbn [perm_of_zx].
  rewrite perm_of_zx_mid_comm.
  rewrite (perm_of_zx_mul_S_r n k).
  rewrite (perm_of_zx_mul_S_r m k).
  rewrite perm_of_zx_mul_S_r.
  rewrite Nat.mul_add_distr_r.
  intros i Hi.
  cbn - [Nat.mul].
  rewrite stack_perms_defn by lia.
  bdestruct_one.
  2:{
    bdestruct_one; [lia|].
    rewrite Nat.sub_add by lia.
    rewrite stack_perms_defn by lia.
    bdestruct_one; [lia|].
    bdestruct_one; [lia|].
    transitivity ((i - (n + m)) `div` k + (i - (n + m)) + 1).
    1:{
      pose proof (Nat.div_mod_eq (i - (n + m)) k).
      lia.
    }
    transitivity ((i - n * S k - m) `div` k + (i - (n * S k) - m) + 1 + n * S k).
    2:{
      pose proof (Nat.div_mod_eq (i - (n * S k) - m) k).
      lia.
    }
    replace (i - n * S k - m) with (i - (n + m) - n * k) by lia.
    rewrite div_sub_r.
    enough ((i - (n + m)) / k >= n) by lia.
    apply Nat.div_le_lower_bound; lia.
  }
  rewrite stack_perms_defn by lia.
  bdestruct_one.
  1:{
    bdestruct_one; [|lia].
    rewrite stack_perms_left by lia.
    bdestruct_one; [|lia].
    done.
  }
  rewrite big_swap_perm_defn by lia.
  bdestruct_one.
  2:{
    bdestruct_one; [|lia].
    rewrite stack_perms_right by lia.
    bdestruct_one; [lia|].
    pose proof (Nat.div_mod_eq (i - n * S k - m) k).
    lia.
  }
  bdestruct_one; [lia|].
  rewrite stack_perms_left by lia.
  bdestruct_one; [lia|].
  replace (i - n + m + n - (n + m)) with (i - n) by lia.
  done.
Qed.


Lemma zx_mul_comm_1_l n : zx_mul_comm 1 n ∝= cast _ _ mul_1_l mul_1_r (n_wire n).
Proof.
  prop_perm_eq.
  rewrite perm_of_zx_mul_comm.
  eq_by_WF_perm_eq (1 * n).
  rewrite kron_comm_perm_defn.
  intros i Hi.
  rewrite Nat.mod_1_r, Nat.div_1_r.
  lia.
Qed.

Lemma zx_mul_comm_1_r n : zx_mul_comm n 1 ∝= cast _ _ mul_1_r mul_1_l (n_wire n).
Proof.
  prop_perm_eq.
  rewrite perm_of_zx_mul_comm.
  eq_by_WF_perm_eq (n * 1).
  rewrite kron_comm_perm_defn.
  intros i Hi.
  rewrite Nat.mod_small, Nat.div_small by lia.
  lia.
Qed.


Lemma zx_mid_comm_1 : zx_mid_comm 1 1 1 1 ∝= — ↕ ⨉ ↕ —.
Proof.
  prop_perm_eq_nosimpl.
  eq_by_WF_perm_eq 4.
  rewrite perm_of_zx_mid_comm.
  by_perm_cell; reflexivity.
Qed.


Lemma zx_mul_comm_add_2 k l :
  zx_mul_comm (k + l) 2 ∝=
  cast _ _ mul_add_distr_r twice_double (zx_mul_comm k 2 ↕ zx_mul_comm l 2 ⟷
  cast _ _ (f_equal2 Nat.add twice_double twice_double) eq_refl
    (zx_mid_comm k k l l)).
Proof.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  rewrite perm_of_zx_mul_comm.
  rewrite perm_of_zx_cast.
  cbn [perm_of_zx].
  rewrite perm_of_zx_cast.
  rewrite perm_of_zx_mid_comm.
  rewrite 2 perm_of_zx_mul_comm.
  intros i Hi.
  rewrite kron_comm_perm_defn by lia.
  cbn.
  rewrite (stack_perms_defn _ _ _ _ i) by lia.
  bdestruct_one.
  2:{
    rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff i _ 1 H).2) by lia.
    rewrite Nat.sub_add by lia.
    rewrite stack_perms_right by lia.
    rewrite kron_comm_perm_defn by lia.
    rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff (i - _) _ 1 H).2) by lia.
    lia.
  }
  rewrite (stack_perms_defn _ _ _ _ i) by lia.
  bdestruct_one.
  1:{
    rewrite stack_perms_left, kron_comm_perm_defn by lia.
    rewrite 2 Nat.mod_small, 2 Nat.div_small by lia.
    lia.
  }
  rewrite big_swap_perm_defn by lia.
  bdestruct_one.
  - rewrite Nat.sub_add by lia.
    rewrite stack_perms_right, kron_comm_perm_defn by lia.
    rewrite 2 Nat.mod_small, 2 Nat.div_small by lia.
    lia.
  - rewrite stack_perms_left, kron_comm_perm_defn by lia.
    rewrite 2 mod_n_to_2n by lia.
    rewrite 2 (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
    lia.
Qed.




(* FIXME: Move / find? *)
Lemma n_stack_1_n_stack1 k (zx : ZX 1 1) : k ⇑ zx = _ ↑ zx.
Proof.
  induction k; cbn; congruence.
Qed.

Lemma n_stack1_n_stack k (zx : ZX 1 1) : k ↑ zx ∝= cast _ _ (eq_sym (Nat.mul_1_r k)) (eq_sym (Nat.mul_1_r k)) (k ⇑ zx).
Proof.
  rewrite n_stack_1_n_stack1.
  rewrite cast_n_stack1.
  done.
Qed.

Lemma n_stack_n_wire k n : k ⇑ n_wire n ∝= n_wire _.
Proof.
  induction k; [done|].
  cbn.
  rewrite IHk.
  rewrite n_wire_stack.
  done.
Qed.


(* FIXME: Move *)
Lemma n_stack_zxperm k {n m} (zx : ZX n m) : ZXperm zx ->
  ZXperm (n_stack k zx).
Proof.
  induction k; cbn; auto_zxperm.
Qed.
#[export] Hint Resolve n_stack_zxperm : zxperm_db.

Lemma perm_of_zx_n_stack_perm_eq k {n m} (zx : ZX n m) :
  perm_eq (k * n) (perm_of_zx (k ⇑ zx))
    (tensor_perms k n idn (perm_of_zx zx)).
Proof.
  induction k; [easy|].
  cbn -[Nat.mul].
  rewrite IHk.
  rewrite 2 tensor_perms_defn.
  rewrite stack_perms_defn.
  intros i Hi.
  bdestruct_one.
  - rewrite Nat.div_small, Nat.mod_small by lia.
    lia.
  - replace (i - n) with (i - 1 * n) by lia.
    rewrite div_sub_r.
    rewrite sub_mul_mod by lia.
    enough (i / n >= 1) by nia.
    apply Nat.div_le_lower_bound; lia.
Qed.


Lemma perm_of_zx_n_stack k {n m} (zx : ZX n m) : ZXperm zx ->
  perm_of_zx (k ⇑ zx) = tensor_perms k n idn (perm_of_zx zx).
Proof.
  intros Hzx.
  eq_by_WF_perm_eq (k * n).
  apply perm_of_zx_n_stack_perm_eq.
Qed.

Lemma n_stack1_zxperm_natural {n m} (zxp : ZX n m) (zx : ZX 1 1) :
  ZXperm zxp ->
  zxp ⟷ m ↑ zx ∝= n ↑ zx ⟷ zxp.
Proof.
  intros Hzxp.
  induction Hzxp.
  - zxscat.
  - zxscat.
  - cbn; zxscat.
  - rewrite 2 nstack1_split.
    zxpsrw IHHzxp1.
    zxpsrw IHHzxp2.
    zxpscat.
  - zxpsrw IHHzxp2.
    zxpsrw IHHzxp1.
    zxpscat.
Qed.


Lemma n_stack_scale k (c : C) {n m} (zx : ZX n m) :
  n_stack k (c .* zx) ∝= (c ^ k) .* n_stack k zx.
Proof.
  induction k.
  - cbn.
    rewrite zx_scale_1_l; done.
  - cbn.
    distribute_zxscale.
    f_equiv.
    C_field.
Qed.



#[export] Instance ZX_copy_proper k n m :
  Proper (proportional_by_1 ==> proportional_by_1)
    (@ZX_copy k n m).
Proof.
  intros zx zx' Hzx.
  unfold ZX_copy.
  f_equiv.
  f_equiv.
  f_equiv.
  done.
Qed.

Lemma ZX_copy_0 {n m} (zx : ZX n m) : ZX_copy 0 zx ∝= cast _ _ mul_0_r mul_0_r ⦰.
Proof.
  unfold ZX_copy.
  rewrite zx_mul_comm_0_r, zx_mul_comm_0_l.
  rewrite n_wire_removal_l', n_wire_removal_r', cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma n_stack_to_ZX_copy k {n m} (zx : ZX n m) :
  n_stack k zx ∝= zx_mul_comm _ _ ⟷ ZX_copy k zx ⟷ zx_mul_comm _ _.
Proof.
  unfold ZX_copy.
  zxpsrw (zx_mul_comm_cancel k n).
  zxpsrw (zx_mul_comm_cancel k m).
  done.
Qed.

Lemma ZX_copy_n_wire k n :
  ZX_copy k (n_wire n) ∝= n_wire _.
Proof.
  unfold ZX_copy.
  rewrite n_stack_n_wire, nwire_removal_r.
  rewrite zx_mul_comm_cancel.
  done.
Qed.

Lemma ZX_copy_wire k :
  ZX_copy k — ∝= n_wire _.
Proof.
  rewrite wire_to_n_wire, ZX_copy_n_wire.
  done.
Qed.

Lemma ZX_copy_compose k {n m o} (zx : ZX n m) (zx' : ZX m o) :
  ZX_copy k (zx ⟷ zx') ∝= ZX_copy k zx ⟷ ZX_copy k zx'.
Proof.
  unfold ZX_copy.
  zxpsrw (zx_mul_comm_cancel k m).
  rewrite n_stack_compose.
  zxpscat.
Qed.

Lemma ZX_copy_stack k {n m o p} (zx : ZX n m) (zx' : ZX o p) :
  ZX_copy k (zx ↕ zx') ∝= cast _ _ (Nat.mul_add_distr_r _ _ _)
    (Nat.mul_add_distr_r _ _ _) (ZX_copy k zx ↕ ZX_copy k zx').
Proof.
  unfold ZX_copy.
  induction k.
  - rewrite empty_zxperm_empty by auto_zxperm.
    symmetry.
    rewrite empty_zxperm_empty by auto_zxperm.
    cast_irrelevance.
    Unshelve.
    all: lia.
  - cbn.
    rewrite zx_mul_comm_S_l.
    rewrite <- compose_assoc.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite IHk.
    rewrite nwire_removal_l, nwire_removal_r.
    rewrite <- 2 zx_mul_comm_S_r.
    rewrite cast_stack_r_fwd.

    rewrite <- (nwire_removal_r (_ ↕ _)).
    rewrite <- (zxperm_transpose_right_inverse (zx_mid_comm _ _ _ _)) by auto_zxperm.
    rewrite zx_mid_comm_transpose.
    rewrite <- (compose_assoc _ (zx_mid_comm _ _ _ _)).
    rewrite zx_mid_comm_commutes_r.
    rewrite <- (nwire_removal_r zx), <- (nwire_removal_r zx') at 1.
    rewrite 2 stack_compose_distr.
    rewrite <- (nwire_removal_l zx), <- (nwire_removal_l zx') at 1.
    rewrite 6 stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite (compose_assoc _ _ (zx_mid_comm _ _ _ _)).
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite cast_id_eq.
    rewrite <- 2 compose_assoc.
    rewrite compose_assoc.
    f_equiv; [f_equiv|].
    + rewrite 2 zx_mul_comm_S_r.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite <- compose_assoc.
      f_equiv.
      apply zx_mul_S_r_stack.
    + rewrite 2 zx_mul_comm_S_l.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite compose_assoc.
      f_equiv.
      apply transpose_diagrams_eq.
      cbn [transpose].
      rewrite transpose_involutive_eq.
      rewrite 2 cast_transpose.
      cbn [transpose].
      rewrite 2 transpose_involutive_eq.
      rewrite zx_mid_comm_transpose.
      apply zx_mul_S_r_stack.
Qed.


(* FIXME: *)
Lemma ZX_copy_stack_back k {n m o p} (zx : ZX n m) (zx' : ZX o p) :
  ZX_copy k zx ↕ ZX_copy k zx' ∝= cast _ _ (eq_sym (Nat.mul_add_distr_r _ _ _))
    (eq_sym (Nat.mul_add_distr_r _ _ _)) (ZX_copy k (zx ↕ zx')).
Proof.
  rewrite ZX_copy_stack, cast_contract_eq', cast_id.
  done.
Qed.

Lemma ZX_copy_cap k : ZX_copy k ⊃ ∝=
  cast _ _ twice_double eq_refl (n_cup k).
Proof.
  rewrite n_cup_to_n_stacked_caps.
  unfold n_stacked_caps.
  unfold ZX_copy.
  rewrite zx_mul_comm_0_r.
  rewrite n_wire_removal_r'.
  rewrite cast_compose_r, cast_contract_eq'.
  rewrite cast_zx_of_perm_natural_r.
  rewrite 2 cast_compose_distribute, cast_contract_eq'.
  f_equiv; [|cast_irrelevance].
  rewrite cast_zx_of_perm_natural_l.
  rewrite zx_of_perm_kron_comm_perm, cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_copy_transpose k {n m} (zx : ZX n m) :
  (ZX_copy k zx) ⊤ ∝= ZX_copy k (zx ⊤).
Proof.
  unfold ZX_copy.
  cbn.
  rewrite 2 zx_mul_comm_transpose.
  rewrite nstack_transpose.
  rewrite compose_assoc.
  done.
Qed.

Lemma ZX_copy_colorswap k {n m} (zx : ZX n m) :
  ⊙ (ZX_copy k zx) ∝= ZX_copy k (⊙ zx).
Proof.
  unfold ZX_copy.
  cbn.
  rewrite nstack_colorswap.
  rewrite 2 (zxperm_colorswap_eq (zx_mul_comm _ _)) by auto_zxperm.
  done.
Qed.

#[export] Hint Rewrite ZX_copy_transpose : transpose_db.

Lemma ZX_copy_cup k : ZX_copy k ⊂ ∝= cast _ _ eq_refl twice_double (n_cap k).
Proof.
  apply transpose_diagrams_eq.
  rewrite cast_transpose, n_cap_transpose, ZX_copy_transpose.
  exact (ZX_copy_cap k).
Qed.

Lemma ZX_copy_swap k : ZX_copy k ⨉ ∝= cast _ _ twice_double twice_double (zx_comm k k).
Proof.
  unfold ZX_copy.
  prop_perm_eq_nosimpl.
  eq_by_WF_perm_eq (2 * k).
  cbn [perm_of_zx].
  rewrite perm_of_zx_cast, 2 perm_of_zx_mul_comm, perm_of_zx_comm.
  rewrite perm_of_zx_n_stack by auto_zxperm.
  rewrite Combinators.compose_assoc.
  rewrite tensor_perms_kron_comm_perm_natural by auto_perm.
  cbn [perm_of_zx].
  rewrite <- Combinators.compose_assoc.
  rewrite kron_comm_perm_pseudo_invol, compose_idn_l.
  now rewrite tensor_perms_swap_idn.
Qed.

Lemma ZX_copy_1_1 k (zx : ZX 1 1) : ZX_copy k zx ∝= _ ↑ zx.
Proof.
  unfold ZX_copy.
  rewrite n_stack_1_n_stack1.
  rewrite n_stack1_zxperm_natural by auto_zxperm.
  rewrite compose_assoc.
  rewrite zx_mul_comm_cancel.
  zxpscat.
Qed.

Lemma ZX_copy_scale k (c : C) {n m} (zx : ZX n m) :
  ZX_copy k (c .* zx) ∝= c ^ k .* ZX_copy k zx.
Proof.
  unfold ZX_copy.
  rewrite n_stack_scale.
  distribute_zxscale.
  done.
Qed.


Lemma ZX_copy_1_2_add k l (zx : ZX 1 2) :
  ZX_copy (k + l) zx ∝=
  cast _ _ mul_add_distr_l (f_equal (Nat.add _) add_0_r) (ZX_copy k zx ↕ ZX_copy l zx ⟷
    cast _ _ (eq_sym (f_equal2 Nat.add (Nat.double_twice _) (Nat.double_twice _))) eq_refl (zx_mid_comm k k l l)).
Proof.
  unfold ZX_copy.
  rewrite 2 stack_compose_distr.
  rewrite 3 zx_mul_comm_1_l, n_wire_removal_l'.
  auto_cast_eqn rewrite <- cast_stack_distribute, n_wire_stack, n_wire_removal_l'.
  auto_cast_eqn rewrite nstack_split.
  rewrite cast_contract_eq'.
  rewrite zx_mul_comm_add_2.
  symmetry.
  rewrite compose_assoc, cast_compose_distribute.
  apply compose_simplify_casted_abs; [lia|intros ?..].
  - rewrite 2 cast_contract_eq'.
    cast_irrelevance.
  - rewrite cast_contract_eq'.
    zxpscat.
    (* rewrite cast_contract_eq'.
    cast_irrelevance.
    f_equiv.
    cast_irrelevance. *)
Qed.

Lemma ZX_copy_2_1_add k l (zx : ZX 2 1) :
  ZX_copy (k + l) zx ∝=
  cast _ _ (f_equal (Nat.add _) add_0_r) mul_add_distr_l (
  cast _ _ eq_refl (eq_sym (f_equal2 Nat.add (Nat.double_twice _) (Nat.double_twice _))) (zx_mid_comm k l k l) ⟷
  (ZX_copy k zx ↕ ZX_copy l zx)).
Proof.
  apply transpose_diagrams_eq.
  rewrite ZX_copy_transpose.
  rewrite ZX_copy_1_2_add.
  rewrite cast_transpose.
  cbn [transpose].
  rewrite cast_transpose, 2 ZX_copy_transpose, zx_mid_comm_transpose.
  done.
Qed.

Lemma ZX_copy_cast k {n m n' m'} (zx : ZX n m) (Hn : n' = n) (Hm : m' = m) :
  ZX_copy k (cast _ _ Hn Hm zx) ∝= cast _ _
    (f_equal (λ a, a*k) Hn) (f_equal (λ a, a*k) Hm) (ZX_copy k zx).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.


Fixpoint ZX_copy' k {n m} (zx : ZX n m) : ZX (n * k) (m * k) :=
  match zx with
  | ⦰ => ⦰
  | — => n_wire _
  | □ => n_stack1 _ □
  | ⨉ => cast _ _ twice_double twice_double (zx_comm k k)
  | ⊂ => cast _ _ eq_refl twice_double (n_cap k)
  | ⊃ => cast _ _ twice_double eq_refl (n_cup k)
  | X n m α => ZX_copy k (X n m α)
  | Z n m α => ZX_copy k (Z n m α)
  | zx ⟷ zx' => ZX_copy' k zx ⟷ ZX_copy' k zx'
  | zx ↕ zx' => cast _ _ (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _)
    (ZX_copy' k zx ↕ ZX_copy' k zx')
  end.



Lemma ZX_copy'_correct k {n m} (zx : ZX n m) :
  ZX_copy' k zx ∝= ZX_copy k zx.
Proof.
  induction zx.
  - rewrite (ZX_copy_n_wire k 0).
    done.
  - rewrite ZX_copy_cup.
    done.
  - rewrite ZX_copy_cap.
    done.
  - rewrite ZX_copy_swap.
    done.
  - rewrite ZX_copy_wire.
    done.
  - rewrite ZX_copy_1_1.
    done.
  - done.
  - done.
  - rewrite ZX_copy_stack.
    cbn.
    now do 2 f_equiv.
  - rewrite ZX_copy_compose.
    cbn.
    now f_equiv.
Qed.










Lemma ZX_bcopy_prf {k} {n : btree unit} :
  btree_size (λ _, k) n = bsize n * k.
Proof.
  induction n; cbn; lia.
Qed.

Definition ZX_bcopy (k : nat) (n m : btree unit) (zx : ZX (bsize n) (bsize m)) :
  ZX (btree_size (λ _, k) n) (btree_size (λ _, k) m) :=
  cast _ _ ZX_bcopy_prf ZX_bcopy_prf (ZX_copy k zx).


#[export] Instance ZX_bcopy_proper k n m :
  Proper (proportional_by_1 ==> proportional_by_1) (@ZX_bcopy k n m).
Proof.
  intros zx zx' Hzx.
  unfold ZX_bcopy.
  f_equiv.
  now f_equiv.
Qed.


Lemma ZX_bcopy_0 n m (zx : ZX (bsize n) (bsize m)) : ZX_bcopy 0 n m zx ∝=
  cast _ _ (eq_trans ZX_bcopy_prf mul_0_r) (eq_trans ZX_bcopy_prf mul_0_r) ⦰.
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_0.
  rewrite cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_bcopy_1 {n m : btree unit} (zx : ZX (bsize n) (bsize m)) :
  ZX_bcopy 1 _ _ zx ∝= cast _ _ btree_size_const_1 btree_size_const_1 zx.
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_1.
  rewrite cast_contract_eq'.
  cast_irrelevance.
Qed.


Lemma ZX_bcopy_scale k c n m zx :
  ZX_bcopy k n m (c .* zx) ∝= c ^ k .* ZX_bcopy k n m zx.
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_scale, zx_scale_cast.
  done.
Qed.

Lemma ZX_bcopy_compose k {n m o : btree unit} (zx : ZX (bsize n) (bsize m))
  (zx' : ZX (bsize m) (bsize o)) :
  ZX_bcopy k n o (zx ⟷ zx') ∝=
  ZX_bcopy k n m zx ⟷ ZX_bcopy k m o zx'.
Proof.
  unfold ZX_bcopy.
  rewrite cast_compose_eq_mid_join.
  rewrite ZX_copy_compose.
  done.
Qed.

Lemma ZX_bcopy_stack k {n m o p : btree unit} (zx : ZX (bsize n) (bsize m))
  (zx' : ZX (bsize o) (bsize p)) :
  ZX_bcopy k (n + o) (m + p) (zx ↕ zx') ∝=
  ZX_bcopy k n m zx ↕ ZX_bcopy k o p zx'.
Proof.
  unfold ZX_bcopy.
  etransitivity.
  eapply (f_equiv (cast _ _ _ _)).
  apply ZX_copy_stack.
  rewrite cast_contract_eq'.
  rewrite cast_stack_l_fwd, cast_stack_r_fwd, cast_contract_eq'.
  cast_irrelevance.
Qed.


Lemma ZX_bcopy_n_wire k (n : btree unit) :
  ZX_bcopy k n n (n_wire _) ∝=
  n_wire _.
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_n_wire.
  rewrite cast_n_wire.
  done.
Qed.



(* FIXME: Move *)
Lemma ZX_bcopy_colorswap k n m zx :
  ⊙ (ZX_bcopy k n m zx) ∝= ZX_bcopy k n m (⊙ zx).
Proof.
  unfold ZX_bcopy.
  rewrite cast_colorswap.
  rewrite ZX_copy_colorswap.
  done.
Qed.

Lemma ZX_bcopy_transpose k n m zx :
  (ZX_bcopy k n m zx) ⊤ ∝= ZX_bcopy k m n (zx ⊤).
Proof.
  unfold ZX_bcopy.
  rewrite cast_transpose, ZX_copy_transpose.
  done.
Qed.

Lemma ZX_bcopy_1_2_add k l (zx : ZX 1 2) :
  ZX_bcopy (k + l) (!()) (!() + !()) zx ∝=
  ZX_bcopy k (!()) (!() + !()) zx ↕
  ZX_bcopy l (!()) (!() + !()) zx ⟷ zx_mid_comm _ _ _ _.
Proof.
  unfold ZX_bcopy.
  cbn.
  rewrite ZX_copy_1_2_add.
  rewrite cast_contract_eq'.
  auto_cast_eqn rewrite <- cast_stack_distribute.
  rewrite cast_compose_r, cast_contract_eq'.
  rewrite cast_compose_distribute, cast_id, cast_contract_eq'.
  f_equiv.
  cast_irrelevance.
Qed.

Lemma ZX_bcopy_2_1_add k l (zx : ZX 2 1) :
  ZX_bcopy (k + l) (!() + !()) (!()) zx ∝=
  zx_mid_comm _ _ _ _ ⟷ (ZX_bcopy k (!() + !()) (!()) zx ↕
  ZX_bcopy l (!() + !()) (!()) zx).
Proof.
  apply transpose_diagrams_eq.
  cbn -[btree_size].
  rewrite 3 ZX_bcopy_transpose, zx_mid_comm_transpose.
  apply ZX_bcopy_1_2_add.
Qed.


Lemma ZX_bcopy_to_zx_mid_comm n :
  ZX_bcopy n ((!() + !()) + (!() + !())) ((!() + !()) + (!() + !()))
    (— ↕ ⨉ ↕ —) ∝= zx_mid_comm n n n n.
Proof.
  unfold ZX_bcopy.
  unfold ZX_copy.
  (* rewrite <- zx_mid_comm_1. *)
  apply prop_eq_of_perm_eq; [auto_zxperm|cbn; auto_zxperm|].
  cbn -[zx_mul_comm Nat.mul].
  rewrite perm_of_zx_cast, perm_of_zx_mid_comm.
  cbn [perm_of_zx].
  rewrite 2 perm_of_zx_mul_comm, perm_of_zx_n_stack by auto_zxperm.
  erewrite <- perm_of_zx_proper_eq; [..|apply zx_mid_comm_1]; [|apply (zx_mid_comm_zxperm 1 1 1 1)|auto_zxperm].
  rewrite (perm_of_zx_mid_comm 1 1 1 1 : @perm_of_zx 4 4 _ = _).
  rewrite Combinators.compose_assoc.
  rewrite tensor_perms_kron_comm_perm_natural by auto_perm.
  rewrite <- Combinators.compose_assoc.
  rewrite kron_comm_perm_pseudo_invol, compose_idn_l.
  intros i Hi.
  rewrite stack_perms_defn, tensor_perms_defn by lia.
  bdestruct_one.
  2:{
    rewrite (Nat.div_mod_eq i n) at 3.
    rewrite (fun H => (Kronecker.div_eq_iff i n 3 H).2) by lia.
    cbn.
    lia.
  }
  symmetry.
  rewrite stack_perms_defn by lia.
  bdestruct_one.
  1:{
    rewrite Nat.div_small, Nat.mod_small by lia.
    done.
  }
  rewrite big_swap_perm_defn by lia.
  bdestruct_one.
  - rewrite (Nat.div_mod_eq i n) at 1.
    rewrite (fun H => (Kronecker.div_eq_iff i n 1 H).2) by lia.
    cbn.
    lia.
  - rewrite (Nat.div_mod_eq i n) at 1.
    rewrite (fun H => (Kronecker.div_eq_iff i n 2 H).2) by lia.
    cbn.
    lia.
Qed.

Lemma ZX_bcopy_cast_l k n n' (p : bpath n n') m zx :
  ZX_bcopy k n m zx ∝= cast _ _ (btree_size_eq_path p) eq_refl
    (ZX_bcopy k n' m (cast _ _ (eq_sym (bsize_eq_path p)) eq_refl zx)).
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_cast.
  rewrite 2 cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_bcopy_cast_r k n m m' (p : bpath m m') zx :
  ZX_bcopy k n m zx ∝= cast _ _ eq_refl (btree_size_eq_path p)
    (ZX_bcopy k n m' (cast _ _ eq_refl (eq_sym (bsize_eq_path p)) zx)).
Proof.
  unfold ZX_bcopy.
  rewrite ZX_copy_cast.
  rewrite 2 cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_bcopy_1_1 k (zx : ZX 1 1) :
  ZX_bcopy k (!()) (!()) zx ∝= k ↑ zx.
Proof.
  unfold ZX_bcopy.
  cbn.
  rewrite ZX_copy_le_1 by lia.
  rewrite n_stack_1_n_stack1.
  rewrite cast_contract_eq'.
  rewrite cast_n_stack1.
  done.
Qed.

Lemma ZX_bcopy_1_0_add k l (zx : ZX 1 0) :
  ZX_bcopy (k + l) (!()) 0 zx ∝=
  ZX_bcopy k (!()) 0 zx ↕ ZX_bcopy l (!()) 0 zx.
Proof.
  unfold ZX_bcopy.
  cbn.
  rewrite 3 ZX_copy_le_1 by lia.
  auto_cast_eqn rewrite nstack_split, <- 2 cast_stack_distribute.
  rewrite 3 cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_bcopy_0_1_add k l (zx : ZX 0 1) :
  ZX_bcopy (k + l) 0 (!()) zx ∝=
  ZX_bcopy k 0 (!()) zx ↕ ZX_bcopy l 0 (!()) zx.
Proof.
  unfold ZX_bcopy.
  cbn.
  rewrite 3 ZX_copy_le_1 by lia.
  auto_cast_eqn rewrite nstack_split, <- 2 cast_stack_distribute.
  rewrite 3 cast_contract_eq'.
  cast_irrelevance.
Qed.









Import fin vector.

(* FIXME: Move *)
Lemma vlookup_vtl {A n} (v : vec A (S n)) (i : fin n) :
  vtl v !!! i = v !!! (FS i).
Proof.
  inv_vec v; done.
Qed.







Fixpoint n_stackv {A} {n m} (f : A -> ZX n m) {k} : forall (v : vec A k),
  ZX (k * n) (k * m) :=
  match k with
  | 0 => fun _ => ⦰
  | S k => fun v =>
    f (vhd v) ↕ n_stackv f (vtl v)
  end.

Lemma n_stackv_ext_eq {A B} {n m} (f : A -> ZX n m) (g : B -> ZX n m) {k} (v : vec A k) w :
  (forall i, f (v !!! i) ∝= g (w !!! i)) ->
  n_stackv f v ∝= n_stackv g w.
Proof.
  induction k; [done|].
  intros Hvw.
  cbn.
  f_equiv; [rewrite <- 2 vlookup_0_vhd; exact (Hvw 0%fin)|].
  apply IHk.
  intros i.
  rewrite 2 vlookup_vtl.
  auto.
Qed.

Lemma n_stackv_vmap {A B} {n m} (g : B -> ZX n m) f {k} (v : vec A k) :
  n_stackv g (vmap f v) = n_stackv (g ∘ f) v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma n_stackv_vapp {A} {n m} (f : A -> ZX n m) {k l} (v : vec A k) (w : vec A l) :
  n_stackv f (v +++ w) ∝= cast _ _
    (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _) (n_stackv f v ↕ n_stackv f w).
Proof.
  induction v.
  - rewrite cast_id.
    cbn.
    rewrite stack_empty_l.
    done.
  - cbn.
    rewrite IHv.
    rewrite cast_stack_r_fwd, stack_assoc_back_fwd, cast_contract_eq'.
    cast_irrelevance.
Qed.


Lemma n_stackv_scale {A n m} (c : C) (f : A -> ZX n m) {k} (v : vec A k) :
  n_stackv (λ a, c .* f a) v ∝= (c ^ k) .* n_stackv f v.
Proof.
  induction v.
  - cbn.
    by distribute_zxscale.
  - cbn.
    rewrite IHv.
    distribute_zxscale.
    apply zx_scale_simplify_eq; [C_field|done].
Qed.

(* Lemma n_stackv_stack {A} {n m n' m'} (f : A -> ZX n m) (f' : A -> ZX n' m')
  {k} (v : vec A k) :
  n_stackv (λ a, f a ↕ f' a) v ∝= cast _ _
    (Nat.mul_add_distr_l _ _ _) (Nat.mul_add_distr_l _ _ _)
    (n_stackv f v ↕ n_stackv f' v). *)


Lemma n_stackv_compose {A} {n m o} (f : A -> ZX n m) (g : A -> ZX m o)
  {k} (v : vec A k) :
  n_stackv (λ a, f a ⟷ g a) v ∝=
    n_stackv f v ⟷ n_stackv g v.
Proof.
  induction v; [zxscat|].
  cbn.
  rewrite <- stack_compose_distr, IHv.
  done.
Qed.

Lemma n_stackv_compose_back {A B} {n m o} (f : A -> ZX n m) (g : B -> ZX m o)
  {k} (v : vec A k) w :
  n_stackv f v ⟷ n_stackv g w ∝=
  n_stackv (λ ab, f ab.1 ⟷ g ab.2) (vzip v w).
Proof.
  rewrite n_stackv_compose.
  f_equiv; apply n_stackv_ext_eq; intros i; rewrite vlookup_zip_with; done.
Qed.

Lemma n_stackv_const {A} {n m} (zx : ZX n m) {k} (v : vec A k) :
  n_stackv (λ _, zx) v = n_stack k zx.
Proof.
  induction k; [done|].
  cbn.
  f_equal; auto.
Qed.

Lemma n_stackv_const' {A} {n m} (zx : ZX n m) (f : A -> ZX n m) {k} (v : vec A k) :
  (forall i, f (v !!! i) ∝= zx) ->
  n_stackv f v ∝= n_stack k zx.
Proof.
  induction k; [done|].
  cbn.
  intros Hv.
  rewrite <- vlookup_0_vhd, Hv.
  f_equiv.
  apply IHk.
  intros i.
  rewrite vlookup_vtl.
  done.
Qed.

Lemma n_stackv_vcons {A n m} (f : A -> ZX n m) b {k} (v : vec A k) :
  n_stackv f (b ::: v) = f b ↕ n_stackv f v.
Proof.
  done.
Qed.

Lemma n_stackv_vnil {A n m} (f : A -> ZX n m) (v : vec A 0) :
  n_stackv f v = ⦰.
Proof.
  done.
Qed.



Fixpoint n_stackv1 {A} (f : A -> ZX 1 1) {k} : forall (v : vec A k),
  ZX k k :=
  match k with
  | 0 => fun _ => ⦰
  | S k => fun v =>
    f (vhd v) ↕ n_stackv1 f (vtl v)
  end.



Lemma n_stackv1_vcons {A} (f : A -> ZX 1 1) b {k} (v : vec A k) :
  n_stackv1 f (b ::: v) = f b ↕ n_stackv1 f v.
Proof.
  done.
Qed.

Lemma n_stackv1_vnil {A} (f : A -> ZX 1 1) (v : vec A 0) :
  n_stackv1 f v = ⦰.
Proof.
  done.
Qed.


Lemma n_stackv1_ext_eq {A} (f g : A -> ZX 1 1) {k} (v w : vec A k) :
  (forall i, f (v !!! i) ∝= g (w !!! i)) ->
  n_stackv1 f v ∝= n_stackv1 g w.
Proof.
  induction k; [done|].
  intros Hvw.
  cbn.
  f_equiv; [rewrite <- 2 vlookup_0_vhd; exact (Hvw 0%fin)|].
  apply IHk.
  intros i.
  rewrite 2 vlookup_vtl.
  auto.
Qed.

Lemma n_stackv1_vmap {A B} (g : B -> ZX 1 1) f {k} (v : vec A k) :
  n_stackv1 g (vmap f v) = n_stackv1 (g ∘ f) v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma n_stackv1_vapp {A} (f : A -> ZX 1 1) {k l} (v : vec A k) (w : vec A l) :
  n_stackv1 f (v +++ w) ∝= n_stackv1 f v ↕ n_stackv1 f w.
Proof.
  induction v.
  - cbn.
    rewrite stack_empty_l.
    done.
  - cbn.
    rewrite IHv.
    rewrite stack_assoc_back_fwd, cast_id.
    done.
Qed.


Lemma n_stackv1_compose {A} (f g : A -> ZX 1 1)
  {k} (v : vec A k) :
  n_stackv1 (λ a, f a ⟷ g a) v ∝=
    n_stackv1 f v ⟷ n_stackv1 g v.
Proof.
  induction v; [now rewrite compose_empty_r|].
  cbn.
  rewrite IHv, stack_compose_distr.
  done.
Qed.

Lemma n_stackv1_const {A} (zx : ZX 1 1) {k} (v : vec A k) :
  n_stackv1 (λ _, zx) v = n_stack1 k zx.
Proof.
  induction k; [done|].
  cbn.
  f_equal; auto.
Qed.

Lemma n_stackv1_const' {A} (zx : ZX 1 1) (f : A -> ZX 1 1) {k} (v : vec A k) :
  (forall i, f (v !!! i) ∝= zx) ->
  n_stackv1 f v ∝= n_stack1 k zx.
Proof.
  induction k; [done|].
  cbn.
  intros Hv.
  rewrite <- vlookup_0_vhd, Hv.
  f_equiv.
  apply IHk.
  intros i.
  rewrite vlookup_vtl.
  done.
Qed.


Lemma n_stackv1_scale {A} (c : C) (f : A -> ZX 1 1) {k} (v : vec A k) :
  n_stackv1 (λ a, c .* f a) v ∝= (c ^ k) .* n_stackv1 f v.
Proof.
  induction v.
  - cbn.
    by distribute_zxscale.
  - cbn.
    rewrite IHv.
    distribute_zxscale.
    apply zx_scale_simplify_eq; [C_field|done].
Qed.

Lemma n_stackv1_to_n_stackv {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  n_stackv1 f v ∝= cast _ _ mul_1_r' mul_1_r' (n_stackv f v).
Proof.
  induction v.
  - cbn; now rewrite cast_id.
  - cbn.
    rewrite IHv, cast_stack_r_fwd.
    cast_irrelevance.
Qed.

Lemma n_stackv_to_n_stackv1 {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  n_stackv f v ∝= cast _ _ mul_1_r mul_1_r (n_stackv1 f v).
Proof.
  rewrite n_stackv1_to_n_stackv, cast_contract_eq', cast_id.
  done.
Qed.

Lemma n_stackv_colorswap {A} {n m} (f : A -> ZX n m) {k} (v : vec A k) :
  ⊙ (n_stackv f v) = n_stackv (λ a, ⊙ (f a)) v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma n_stackv_transpose {A} {n m} (f : A -> ZX n m) {k} (v : vec A k) :
  (n_stackv f v) ⊤ = n_stackv (λ a, (f a) ⊤) v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma n_stackv1_colorswap {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  ⊙ (n_stackv1 f v) = n_stackv1 (λ a, ⊙ (f a)) v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma n_stackv1_transpose {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  (n_stackv1 f v) ⊤ = n_stackv1 (λ a, (f a) ⊤) v.
Proof.
  induction v; cbn; congruence.
Qed.




Definition ZX_vcopy {A} {n m} (f : A -> ZX n m) {k} (v : vec A k) :
  ZX (n * k) (m * k) :=
  zx_mul_comm _ _ ⟷ n_stackv f v ⟷ zx_mul_comm _ _.


Local Notation "'[gen'  t ']'" := (Pgen _ _ t).

(* FIXME: Move *)
Arguments n_stackv {_} {_ _} _ {!_} (!_) / : assert.
Typeclasses Opaque n_stackv.

(* FIXME: Move *)
Import GeneratorNotations.

Lemma add_comm_mid {n m o p} : n + m + (o + p) = n + o + (m + p).
Proof.
  lia.
Qed.

Lemma zx_mul_S_r_stack_back n m k :
  zx_mul_S_r (n + m) k ∝=
  cast _ _ mul_add_distr_r (f_equiv (Nat.add _) mul_add_distr_r) ((zx_mul_S_r n k ↕ zx_mul_S_r m k) ⟷
    cast _ _ eq_refl eq_refl (zx_mid_comm n (n * k) m (m * k))).
Proof.
  pose proof (zx_mul_S_r_stack n m k) as Hrw.
  do 3 specialize (Hrw ltac:(lia)).
  rewrite compose_zxperm_r_eq in Hrw by auto_zxperm.
  rewrite Hrw.
  rewrite cast_transpose, zx_mid_comm_transpose.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite 2 cast_compose_distribute.
  f_equiv; [cast_irrelevance|].
  rewrite 2 cast_contract_eq'; cast_irrelevance.
Qed.

Lemma cast_n_wire_add_l {n m o} (Hn : n + m = n + o) :
  cast _ _ Hn eq_refl (n_wire _) ∝=
  n_wire n ↕ cast _ _ (proj1 (Nat.add_cancel_l _ _ _) Hn) eq_refl (n_wire _).
Proof.
  rewrite cast_stack_r_fwd.
  cast_irrelevance.
  rewrite n_wire_stack.
  done.
Qed.

Lemma cast_n_wire_add_r {n m o} (Hn : m + n = o + n) :
  cast _ _ Hn eq_refl (n_wire _) ∝=
  cast _ _ (proj1 (Nat.add_cancel_r _ _ _) Hn) eq_refl (n_wire _) ↕ n_wire n.
Proof.
  rewrite cast_stack_l_fwd.
  cast_irrelevance.
  rewrite n_wire_stack.
  done.
Qed.

(* FIXME: Move, and improve *)
Ltac reassert lem :=
  let T := type of lem in
  assert T.

Lemma zx_cast_n_wire_compose {n m o} (Hn : n = m) (Hm : m = o) : 
  cast _ _ Hn eq_refl (n_wire _) ⟷ cast _ _ Hm eq_refl (n_wire _) ∝=
  cast _ _ (eq_trans Hn Hm) eq_refl (n_wire _).
Proof.
  subst.
  rewrite n_wire_removal_l', cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma n_stackv_stack {A} {n m n' m'} (f : A -> ZX n m) (f' : A -> ZX n' m')
  {k} (v : vec A k) :
  n_stackv (λ a, f a ↕ f' a) v ∝=
  zx_mul_comm k (n + n') ⟷ cast _ _ mul_add_distr_r eq_refl (zx_mul_comm n k ↕ zx_mul_comm n' k) ⟷
  (n_stackv f v ↕ n_stackv f' v) ⟷
  cast _ _ eq_refl mul_add_distr_r (zx_mul_comm k m ↕ zx_mul_comm k m') ⟷ zx_mul_comm (m + m') k.
Proof.
  induction v.
  - auto_cast_eqn rewrite empty_zxperm_empty by auto_zxperm.
    symmetry.
    auto_cast_eqn rewrite empty_zxperm_empty by auto_zxperm.
    zxpscat.
  - cbn -[cast].
    rewrite zx_mul_comm_S_l.
    rewrite IHv.
    rewrite 2 zx_mul_S_r_stack_back.
    rewrite cast_transpose.
    cbn [transpose].
    rewrite cast_transpose, zx_mid_comm_transpose.
    rewrite cast_compose_l_eq_mid, cast_contract_eq'.
    rewrite 3 cast_compose_r_eq_mid, cast_contract_eq'.
    symmetry.
    rewrite (cast_compose_r _ _ (n_wire _ ↕ _)).
    rewrite cast_compose_eq_mid_join.
    rewrite <- compose_assoc.
    rewrite cast_compose_eq_mid_join.
    rewrite 2 zx_mul_comm_S_l.
    zxpsrw (zxperm_transpose_left_inverse (zx_mul_S_r n n0 ↕ zx_mul_S_r n' n0) 
      ltac:(auto_zxperm)).
    zxpsrw (zxperm_transpose_left_inverse (zx_mul_S_r m n0 ↕ zx_mul_S_r m' n0) 
      ltac:(auto_zxperm)).
    unfold zx_mid_comm.
    rewrite 2 cast_contract_eq'.
    zxpscat.
Qed.


Lemma ZX_vcopy_stack {A} {n m n' m'} (f : A -> ZX n m) (f' : A -> ZX n' m')
  {k} (v : vec A k) :
  ZX_vcopy (λ a, f a ↕ f' a) v ∝= cast _ _
    (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _)
    (ZX_vcopy f v ↕ ZX_vcopy f' v).
Proof.
  unfold ZX_vcopy.
  induction v.
  - rewrite empty_zxperm_empty by auto_zxperm.
    symmetry.
    rewrite empty_zxperm_empty by auto_zxperm.
    cast_irrelevance.
    Unshelve.
    all: lia.
  - cbn.
    rewrite zx_mul_comm_S_l.
    rewrite <- compose_assoc.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite IHv.
    rewrite nwire_removal_l, nwire_removal_r.
    rewrite <- 2 zx_mul_comm_S_r.
    rewrite cast_stack_r_fwd.

    rewrite <- (nwire_removal_r (_ ↕ _)).
    rewrite <- (zxperm_transpose_right_inverse (zx_mid_comm _ _ _ _)) by auto_zxperm.
    rewrite zx_mid_comm_transpose.
    rewrite <- (compose_assoc _ (zx_mid_comm _ _ _ _)).
    rewrite zx_mid_comm_commutes_r.
    rewrite <- (nwire_removal_r (f _)), <- (nwire_removal_r (f' _)) at 1.
    rewrite 2 stack_compose_distr.
    rewrite <- (nwire_removal_l (f _)), <- (nwire_removal_l (f' _)) at 1.
    rewrite 6 stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite (compose_assoc _ _ (zx_mid_comm _ _ _ _)).
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite cast_id_eq.
    rewrite <- 2 compose_assoc.
    rewrite compose_assoc.
    f_equiv; [f_equiv|].
    + rewrite 2 zx_mul_comm_S_r.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite <- compose_assoc.
      f_equiv.
      apply zx_mul_S_r_stack.
    + rewrite 2 zx_mul_comm_S_l.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite compose_assoc.
      f_equiv.
      apply transpose_diagrams_eq.
      cbn [transpose].
      rewrite transpose_involutive_eq.
      rewrite 2 cast_transpose.
      cbn [transpose].
      rewrite 2 transpose_involutive_eq.
      rewrite zx_mid_comm_transpose.
      apply zx_mul_S_r_stack.
Qed.




(* Lemma ZX_vcopy_stack {A} {n m n' m'} (f : A -> ZX n m) (f' : A -> ZX n' m')
  {k} (v : vec A k) :
  ZX_vcopy (λ a, f a ↕ f' a) v ∝= cast _ _
    (Nat.mul_add_distr_r _ _ _) (Nat.mul_add_distr_r _ _ _)
    (ZX_vcopy f v ↕ ZX_vcopy f' v).
Proof.
  unfold ZX_vcopy.
  induction v.
  - auto_cast_eqn rewrite empty_zxperm_empty by auto_zxperm.
    symmetry.
    auto_cast_eqn rewrite empty_zxperm_empty by auto_zxperm.
    zxpscat.
  - cbn.
    rewrite zx_mul_comm_S_l.
    zxpsrw IHv.
    rewrite <- 2 zx_mul_comm_S_r.
    reassert IHv.
    zxsbypro.
    zxpsrw IHv.
    rewrite zx_mul_S_r_stack_back.

    rewrite cast_n_wire_add_l.



    zxsbypro.
    let T := type of IHv in
    assert T.
    zxsbypro.
    zxsrw IHv.
    rewrite <- compose_assoc.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite (compose_assoc _ (_ ↕ _) (_ ↕ _)), <- stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite IHv.
    rewrite nwire_removal_l, nwire_removal_r.
    rewrite <- 2 zx_mul_comm_S_r.
    rewrite cast_stack_r_fwd.

    rewrite <- (nwire_removal_r (_ ↕ _)).
    rewrite <- (zxperm_transpose_right_inverse (zx_mid_comm _ _ _ _)) by auto_zxperm.
    rewrite zx_mid_comm_transpose.
    rewrite <- (compose_assoc _ (zx_mid_comm _ _ _ _)).
    rewrite zx_mid_comm_commutes_r.
    rewrite <- (nwire_removal_r (f _)), <- (nwire_removal_r (f' _)) at 1.
    rewrite 2 stack_compose_distr.
    rewrite <- (nwire_removal_l (f _)), <- (nwire_removal_l (f' _)) at 1.
    rewrite 6 stack_compose_distr.
    rewrite <- 2 compose_assoc.
    rewrite (compose_assoc _ _ (zx_mid_comm _ _ _ _)).
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite 2 cast_compose_distribute.
    symmetry.
    rewrite cast_id_eq.
    rewrite <- 2 compose_assoc.
    rewrite compose_assoc.
    f_equiv; [f_equiv|].
    + rewrite 2 zx_mul_comm_S_r.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite <- compose_assoc.
      f_equiv.
      apply zx_mul_S_r_stack.
    + rewrite 2 zx_mul_comm_S_l.
      rewrite stack_compose_distr.
      rewrite 2 cast_compose_distribute.
      rewrite compose_assoc.
      f_equiv.
      apply transpose_diagrams_eq.
      cbn [transpose].
      rewrite transpose_involutive_eq.
      rewrite 2 cast_transpose.
      cbn [transpose].
      rewrite 2 transpose_involutive_eq.
      rewrite zx_mid_comm_transpose.
      apply zx_mul_S_r_stack.
Qed. *)


Lemma ZX_vcopy_compose {A} {n m o} (f : A -> ZX n m) (g : A -> ZX m o)
  {k} (v : vec A k) :
  ZX_vcopy (λ a, f a ⟷ g a) v ∝=
    (ZX_vcopy f v ⟷ ZX_vcopy g v).
Proof.
  unfold ZX_vcopy.
  rewrite n_stackv_compose.
  zxpsrw (zx_mul_comm_cancel k m).
  zxpscat.
Qed.

Lemma ZX_vcopy_const {A} {n m} (zx : ZX n m)
  {k} (v : vec A k) :
  ZX_vcopy (λ _, zx) v ∝= ZX_copy k zx.
Proof.
  unfold ZX_vcopy.
  rewrite n_stackv_const.
  done.
Qed.

Lemma ZX_vcopy_1_1 {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  ZX_vcopy f v ∝= cast _ _ mul_1_l mul_1_l (n_stackv1 f v).
Proof.
  unfold ZX_vcopy.
  rewrite zx_mul_comm_1_l, n_wire_removal_l', zx_mul_comm_1_r, n_wire_removal_r',
    n_stackv_to_n_stackv1, 2 cast_contract_eq'.
  cast_irrelevance.
Qed.





Definition ZX_bvcopy {A} {n m : btree unit} (f : A -> ZX (bsize n) (bsize m))
  {k} (v : vec A k) :
  ZX (btree_size (λ _, k) n) (btree_size (λ _, k) m) :=
  cast _ _ ZX_bcopy_prf ZX_bcopy_prf (ZX_vcopy f v).


Lemma ZX_bvcopy_compose {A} n m o k (f : A -> ZX _ _) (g : A -> ZX _ _) (v : vec A k) :
  ZX_bvcopy (λ a, f a ⟷ g a) v ∝=
    ZX_bvcopy (n:=n) (m:=m) f v ⟷ ZX_bvcopy (m:=o) g v.
Proof.
  unfold ZX_bvcopy.
  rewrite cast_compose_eq_mid_join.
  cast_irrelevance.
  rewrite ZX_vcopy_compose.
  done.
Qed.

Lemma ZX_bvcopy_stack {A} n m o p k (f : A -> ZX _ _) (g : A -> ZX _ _) (v : vec A k) :
  ZX_bvcopy (n:=n+o) (m:=m+p) (λ a, f a ↕ g a) v ∝=
    ZX_bvcopy (n:=n) (m:=m) f v ↕ ZX_bvcopy (n:=o) (m:=p) g v.
Proof.
  unfold ZX_bvcopy.
  rewrite cast_stack_r_fwd, cast_stack_l_fwd, cast_contract_eq'.
  cbn.
  rewrite ZX_vcopy_stack, cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma ZX_bvcopy_1_1 {A} (f : A -> ZX 1 1) {k} (v : vec A k) :
  @ZX_bvcopy _ (!()) (!()) f _ v ∝= n_stackv1 f v.
Proof.
  unfold ZX_bvcopy.
  rewrite ZX_vcopy_1_1, cast_contract_eq', cast_id.
  done.
Qed.



Lemma ZX_bvcopy_vmap {A B} {n m} (g : B -> ZX (bsize n) (bsize m)) f {k} (v : vec A k) :
  ZX_bvcopy g (vmap f v) = ZX_bvcopy (g ∘ f) v.
Proof.
  unfold ZX_bvcopy, ZX_vcopy.
  rewrite n_stackv_vmap.
  done.
Qed.

Lemma ZX_bvcopy_ext_eq {A B} n m k (f : A -> ZX (bsize n) (bsize m))
  (g : B -> ZX (bsize n) (bsize m)) (v w : vec _ k) :
  (forall i, f (v !!! i) ∝= g (w !!! i)) ->
  ZX_bvcopy f v ∝= ZX_bvcopy g w.
Proof.
  intros Hvw.
  rewrite (vec_to_vmap_lookup_vfinseq v).
  rewrite (vec_to_vmap_lookup_vfinseq w).
  rewrite 2 ZX_bvcopy_vmap.
  unfold ZX_bvcopy.
  f_equiv.
  unfold ZX_vcopy.
  do 2 f_equiv.
  apply n_stackv_ext_eq.
  intros i.
  cbn.
  rewrite lookup_vfinseq.
  done.
Qed.


Lemma ZX_bvcopy_compose_back {A B} n m o k (f : A -> ZX _ _) (g : B -> ZX _ _) (v : vec A k) w :
  ZX_bvcopy (n:=n) (m:=m) f v ⟷ ZX_bvcopy (m:=o) g w ∝=
    ZX_bvcopy (λ ab, f ab.1 ⟷ g ab.2) (vzip v w).
Proof.
  rewrite ZX_bvcopy_compose.
  f_equiv; apply ZX_bvcopy_ext_eq; intros i; rewrite vlookup_zip_with; done.
Qed.

Lemma ZX_bvcopy_const {A} n m zx {k} (v : vec A k) :
  ZX_bvcopy (λ _, zx) v = ZX_bcopy k n m zx.
Proof.
  unfold ZX_bvcopy, ZX_bcopy.
  cast_irrelevance.
  unfold ZX_vcopy, ZX_copy.
  do 2 f_equal.
  rewrite n_stackv_const.
  done.
Qed.



Lemma ZX_bvcopy_const' {A} n m zx (f : A -> ZX _ _) {k} (v : vec A k) :
  (forall i, f (v !!! i) ∝= zx) ->
  ZX_bvcopy f v ∝= ZX_bcopy k n m zx.
Proof.
  intros Hv.
  unfold ZX_bvcopy, ZX_bcopy.
  cast_irrelevance.
  unfold ZX_vcopy, ZX_copy.
  do 2 f_equiv.
  rewrite (n_stackv_const' zx); done.
Qed.


Lemma ZX_bvcopy_colorswap {A} n m k (f : A -> ZX (bsize n) (bsize m)) (v : vec A k) :
  ⊙ (ZX_bvcopy f v) = ZX_bvcopy (λ a, ⊙ (f a)) v.
Proof.
  unfold ZX_bvcopy.
  rewrite cast_colorswap.
  cast_irrelevance.
  unfold ZX_vcopy.
  cbn.
  rewrite 2 (zxperm_colorswap_eq (zx_mul_comm _ _)) by auto_zxperm.
  rewrite n_stackv_colorswap.
  done.
Qed.

Lemma ZX_bvcopy_transpose {A} n m k (f : A -> ZX (bsize n) (bsize m)) (v : vec A k) :
  (ZX_bvcopy f v) ⊤ ∝= ZX_bvcopy (λ a, (f a) ⊤) v.
Proof.
  unfold ZX_bvcopy.
  rewrite cast_transpose.
  cast_irrelevance.
  unfold ZX_vcopy.
  cbn.
  rewrite 2 zx_mul_comm_transpose, n_stackv_transpose, compose_assoc.
  done.
Qed.




