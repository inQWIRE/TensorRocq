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







Module prf_notations.

(* FIXME: Move *)
Notation mul_1_r := (Nat.mul_1_r _).
Notation mul_1_r' := (eq_sym (Nat.mul_1_r _)).
Notation mul_1_l := (Nat.mul_1_l _).
Notation mul_1_l' := (eq_sym (Nat.mul_1_l _)).

(* FIXME: Move  *)
Notation mul_add_distr_l := (Nat.mul_add_distr_l _ _ _).
Notation mul_add_distr_l' := (eq_sym (Nat.mul_add_distr_l _ _ _)).
Notation mul_add_distr_r := (Nat.mul_add_distr_r _ _ _).
Notation mul_add_distr_r' := (eq_sym (Nat.mul_add_distr_r _ _ _)).

(* FIXME: Move *)
Notation mul_0_r := (Nat.mul_0_r _).
Notation mul_0_r' := (eq_sym (Nat.mul_0_r _)).
Notation mul_0_l := (Nat.mul_0_l _).
Notation mul_0_l' := (eq_sym (Nat.mul_0_l _)).
Notation add_0_r := (Nat.add_0_r _).
Notation add_0_r' := (eq_sym (Nat.add_0_r _)).
Notation add_0_l := (Nat.add_0_l _).
Notation add_0_l' := (eq_sym (Nat.add_0_l _)).

Notation add_assoc := (Nat.add_assoc _ _ _).
Notation add_assoc' := (eq_sym (Nat.add_assoc _ _ _)).
Notation mul_assoc := (Nat.mul_assoc _ _ _).
Notation mul_assoc' := (eq_sym (Nat.mul_assoc _ _ _)).

Notation add_comm := (Nat.add_comm _ _).
Notation add_comm' := (eq_sym (Nat.add_comm _ _)).

Notation mul_comm := (Nat.mul_comm _ _).
Notation mul_comm' := (eq_sym (Nat.mul_comm _ _)).

Notation twice_double := (eq_sym (Nat.double_twice _) : 2 * _ = _ + _).
Notation twice_double_r := (eq_sym (Nat.double_twice _) : _ * 2 = _ + _).

Notation double_twice := ((Nat.double_twice _) : _ + _ = 2 * _).
Notation double_twice_r := ((Nat.double_twice _) : _ + _ = _ * 2).


End prf_notations.

Import prf_notations.



(* FIXME: Move *)
Lemma div_sub_r a b c : (a - b * c) / c = a / c - b.
Proof.
  destruct_decide (decide (a <= b * c)) as Habc.
  - replace (a - _) with 0 by lia.
    rewrite Nat.Div0.div_0_l.
    symmetry.
    enough (a / c <= b) by lia.
    apply Nat.Div0.div_le_upper_bound.
    lia.
  - replace (a / c) with (((a - b * c) + b * c) / c) by (f_equal; lia).
    destruct_decide (decide (c = 0)); [subst; now rewrite 2 Nat.div_0_r; lia|].
    rewrite Nat.div_add by done.
    lia.
Qed.

(* FIXME: Move, and use! *)
Lemma show_div_eq c a b : b * c <= a < b * S c ->
  a / b = c.
Proof.
  intros Heq; apply Kronecker.div_eq_iff; lia.
Qed.
  

Lemma tensor_perms_swap_idn k : tensor_perms 2 k swap_2_perm idn = big_swap_perm k k.
Proof.
  eq_by_WF_perm_eq (k + k).
  rewrite big_swap_perm_defn.
  intros i Hi.
  rewrite tensor_perms_defn by lia.
  bdestruct_one.
  - rewrite Nat.mod_small, Nat.div_small by lia.
    cbn; lia.
  - replace (i / k) with 1.
    + cbn.
      rewrite mod_n_to_2n by lia.
      lia.
    + symmetry.
      apply Kronecker.div_eq_iff; lia.
Qed.





(* FIXME: Move??? *)
Lemma Cpow_inv c n :
  ((/ c) ^ n = / c ^ n)%C.
Proof.
  induction n; [lca|].
  cbn.
  rewrite Cinv_mult_distr.
  rewrite IHn.
  done.
Qed.
Lemma Cpow_1_r c : (c ^ 1 = c)%C.
Proof.
  lca.
Qed.




Lemma btree_size_const_1 {A} {n : btree A} :
  btree_size (λ _, 1) n = bsize n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma bsize_eq_path {A n n'} (p : @bpath A n n') : bsize n = bsize n'.
Proof.
  rewrite <- 2 btree_size_const_1.
  apply btree_size_eq_path.
  done.
Qed.




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
  - zxscat.
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
  rewrite compose_assoc, cast_compose_r.
  rewrite compose_empty_r, cast_contract_eq'.
  rewrite cast_compose_distribute, cast_contract_eq'.
  apply compose_simplify_casted_abs; [lia|intros ?..].
  - rewrite cast_contract_eq'.
    rewrite cast_zx_of_perm_natural_l.
    rewrite zx_of_perm_kron_comm_perm, cast_contract_eq', cast_id.
    done.
  - rewrite cast_contract_eq'.
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
    cast_irrelevance.
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















































From TensorRocq Require Import Matrix.


Lemma vtl_mx_vblock {n n' m} (A : Matrix bool (S (S n)) (S m)) (B : Matrix bool (S n') (S m)) :
  vtl (mx_vblock A B) = mx_vblock (vtl A) B.
Proof.
  inv_vec A; done.
Qed.




#[export] Instance bool_leibniz : LeibnizEquiv bool.
Proof.
  intros ? ?; easy.
Qed.
#[export] Instance vec_equiv {A} `{Equiv A} {n} : Equiv (vec A n) := vec_rel equiv.
#[export] Instance vec_leibniz `{LeibnizEquiv A} {n} : LeibnizEquiv (vec A n).
Proof.
  intros v w Hvw.
  apply vec_eq.
  unfold equiv, vec_equiv in Hvw.
  rewrite vec_rel_lookup in Hvw.
  intros i.
  apply leibniz_equiv, Hvw.
Qed.


Lemma cast_matrix_alt {n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix bool n m) :
  cast_matrix Hn Hm A = Vector.cast (vmap (λ v, Vector.cast v Hm) A) Hn.
Proof.
  subst.
  rewrite cast_matrix_id, Aux_stdpp_base.cast_id.
  rewrite vmap_id' by now intros; rewrite Aux_stdpp_base.cast_id.
  done.
Qed.


Lemma mx_vblock_nil_r {n m} (A : Matrix bool n m) :
  mx_vblock A [#] = cast_matrix add_0_r' eq_refl A.
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_vblock.
  induction i using fin_add_inv; [|inv_all_vec_fin].
  rewrite fin_sum_case_L.
  cbn.
  rewrite mlookup_cast.
  rewrite fcast_id.
  f_equal.
  apply fin_to_nat_inj.
  now rewrite fin_to_nat_cast, fin_to_nat_L.
Qed.

Lemma mx_hblock_cons {R n m m'} vA A vB B :
  @mx_hblock R (S n) m m' (vA ::: A) (vB ::: B) =
  (vA +++ vB) ::: mx_hblock A B.
Proof.
  done.
Qed.

Lemma mx_hblock_nil_l {n m'} (A : Matrix bool n 0) (B : Matrix bool n m') :
  mx_hblock A B = B.
Proof.
  apply vec_eq.
  intros i.
  unfold mx_hblock.
  rewrite vlookup_zip_with.
  cbn.
  unfold Matrix in *.
  induction (A !!! i) using vec_0_inv.
  done.
Qed.

Lemma mx_hblock_nil_r {n m} (A : Matrix bool n m) (B : Matrix bool n 0) :
  mx_hblock A B = cast_matrix eq_refl add_0_r' A.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_hblock, mlookup_cast.
  induction j using fin_add_inv; [|inv_all_vec_fin].
  rewrite fin_sum_case_L.
  cbn.
  f_equal; apply fin_to_nat_inj; now rewrite fin_to_nat_cast, ?fin_to_nat_L.
Qed.


(* FIXME: Move *)
Lemma mx_transpose_involutive {R n m} : Cancel eq (@mx_transpose R n m) mx_transpose.
Proof.
  intros A.
  apply mx_eq.
  intros i j.
  now rewrite 2 mlookup_transpose.
Qed.
Lemma mx_transpose_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_transpose (mx_vblock A B) = mx_hblock (mx_transpose A) (mx_transpose B).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_hblock, mlookup_transpose, mlookup_vblock.
  destruct (fin_sum_case j); cbn; now rewrite mlookup_transpose.
Qed.
Lemma mx_transpose_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_transpose (mx_hblock A B) = mx_vblock (mx_transpose A) (mx_transpose B).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_vblock, mlookup_transpose, mlookup_hblock.
  destruct (fin_sum_case i); cbn; now rewrite mlookup_transpose.
Qed.
Definition mx_splitl {R n m m'} (A : Matrix R n (m + m')) :=
  vmap vsplitl A.
Definition mx_splitr {R n m m'} (A : Matrix R n (m + m')) :=
  vmap vsplitr A.
Lemma mx_hblock_split {R n m m'} (A : Matrix R n (m + m')) :
  mx_hblock (mx_splitl A) (mx_splitr A) = A.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_zip_with, 2 vlookup_map.
  apply app_vsplit.
Qed.
Lemma mx_splitl_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_splitl (mx_hblock A B) = A.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_map, vlookup_zip_with.
  apply vsplitl_app.
Qed.
Lemma mx_splitr_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_splitr (mx_hblock A B) = B.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_map, vlookup_zip_with.
  apply vsplitr_app.
Qed.
Definition mx_splitu {R n n' m} (A : Matrix R (n + n') m) :=
  vsplitl A.
Definition mx_splitd {R n n' m} (A : Matrix R (n + n') m) :=
  vsplitr A.
Lemma mx_vblock_split {R n n' m} (A : Matrix R (n + n') m) :
  mx_vblock (mx_splitu A) (mx_splitd A) = A.
Proof.
  apply app_vsplit.
Qed.
Lemma mx_splitu_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_splitu (mx_vblock A B) = A.
Proof.
  apply vsplitl_app.
Qed.
Lemma mx_splitd_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_splitd (mx_vblock A B) = B.
Proof.
  apply vsplitr_app.
Qed.


Lemma matrix_nonempty_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HProw : forall m (A : Matrix R 1 m), P _ _ A)
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n as [|[|n]]; [now auto..|].
  induction A as [vA A] using vec_S_inv.
  change (vA ::: A) with (mx_vblock [#vA] A).
  apply (HPvblock 1 (S n) _ [#vA] A); [lia..|apply IHn|apply IHn]; lia.
Qed.

Lemma matrix_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HProw : forall m (A : Matrix R 1 m), P _ _ A)
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  induction n; [auto|].
  induction A as [vA A] using vec_S_inv.
  change (vA ::: A) with (mx_vblock [#vA] A).
  change (S n) with (1 + n).
  apply HPvblock; [auto|].
  auto.
Qed.




Lemma matrix_nonempty_hblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HPcol : forall n (A : Matrix R n 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct n; [now auto|].
  induction m as [m IHm] using lt_wf_ind.
  destruct m as [|[|m]]; [now auto..|].
  rewrite <- (@mx_hblock_split _ _ 1 (S m) A).
  change (S (S m)) with (1 + S m).
  apply HPhblock; [lia..|apply IHm|apply IHm]; lia.
Qed.

Lemma matrix_hblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HPcol : forall n (A : Matrix R n 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  induction m; [auto|].
  rewrite <- (@mx_hblock_split _ _ 1 m A).
  change (S m) with (1 + m).
  apply HPhblock; [auto|].
  auto.
Qed.


Lemma matrix_nonempty_hblock_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HP_1_1 : forall (A : Matrix R 1 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B))
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct n; [now auto|].
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m; [auto|].
    change (S (S m)) with (1 + S m) in *.
    rewrite <- (mx_hblock_split A).
    apply HPhblock; [lia..|auto|auto].
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A).
    apply HPvblock; [lia..|apply IHn|apply IHn]; lia.
Qed.


(* FIXME: Move *)
Definition mx_zip_with {R R' R''} (f : R -> R' -> R'')
  {n m} (A : Matrix R n m) (B : Matrix R' n m) : Matrix R'' n m :=
  vzip_with (vzip_with f) A B.

Lemma mlookup_zip_with {R R' R''} (f : R -> R' -> R'')
  {n m} (A : Matrix R n m) (B : Matrix R' n m) i j :
  mx_zip_with f A B i j = f (A i j) (B i j).
Proof.
  unfold mx_zip_with, mx_to_fun, Matrix.
  now rewrite 2 vlookup_zip_with.
Qed.

#[export] Instance mx_zip_with_mor {R R' R''}
  `{Equiv R, Equiv R', Equiv R''} (f : R -> R' -> R'')
  {Hf : Proper (equiv ==> equiv ==> equiv) f}
  {n m} : Proper (equiv ==> equiv ==> equiv) (mx_zip_with f (n:=n) (m:=m)).
Proof.
  intros A A' HA B B' HB.
  apply mx_equiv.
  intros i j.
  rewrite 2 mlookup_zip_with.
  f_equiv; now apply mx_equiv.
Qed.


Definition mx_plus {R} `{SR : SemiRing R rO rI radd rmul req}
  {n m} (A B : Matrix R n m) := mx_zip_with radd A B.

Definition mx_vec_prod {R} `{SR : SemiRing R rO rI radd rmul req}
  {n m} (A : Matrix R n m) (v : vec R m) : vec R n :=
  vmap (vec_dot v) A.

Section mx_plus.


Local Open Scope Matrix_scope.


Context {R} `{SR : SemiRing R rO rI radd rmul req}.



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


Lemma mlookup_plus {n m} (A B : Matrix R n m) i j :
  mx_plus A B i j = A i j + B i j.
Proof.
  apply mlookup_zip_with.
Qed.

#[export] Instance mx_plus_mor
  {n m} : Proper (equiv ==> equiv ==> equiv) (mx_plus (n:=n) (m:=m)).
Proof.
  apply mx_zip_with_mor, _.
Qed.

(* TODO: Refactor these to be mx_zip_with lemmas *)
Lemma mx_plus_hblock {n m m'} (A A' : Matrix R n m) (B B' : Matrix R n m') :
  mx_plus (mx_hblock A B) (mx_hblock A' B') =
  mx_hblock (mx_plus A A') (mx_plus B B').
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_hblock.
  induction j as [j|j] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn; now rewrite mlookup_plus.
  - rewrite fin_sum_case_R; cbn; now rewrite mlookup_plus.
Qed.
Lemma mx_plus_vblock {n n' m} (A A' : Matrix R n m) (B B' : Matrix R n' m) :
  mx_plus (mx_vblock A B) (mx_vblock A' B') =
  mx_vblock (mx_plus A A') (mx_plus B B').
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_vblock.
  induction i as [i|i] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn; now rewrite mlookup_plus.
  - rewrite fin_sum_case_R; cbn; now rewrite mlookup_plus.
Qed.

Lemma mx_row_hblock {n m m'}
  (A : Matrix R n m) (B : Matrix R n m') i :
  mx_row (mx_hblock A B) i = mx_row A i +++ mx_row B i.
Proof.
  unfold mx_row, mx_hblock, Matrix.
  rewrite vlookup_zip_with.
  done.
Qed.

Lemma mx_col_vblock {n n' m}
  (A : Matrix R n m) (B : Matrix R n' m) i :
  mx_col (mx_vblock A B) i = mx_col A i +++ mx_col B i.
Proof.
  unfold mx_col, mx_vblock, Matrix.
  rewrite Vector.map_append.
  done.
Qed.

Lemma compose_matrix_hblock_vblock {n m m' o}
  (A : Matrix R n m) (B : Matrix R m o)
  (C : Matrix R n m') (D : Matrix R m' o) :
  compose_matrix (mx_hblock A C) (mx_vblock B D) ≡
  mx_plus (compose_matrix A B) (compose_matrix C D).
Proof.
  apply mx_equiv.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_compose.
  rewrite mx_row_hblock, mx_col_vblock.
  rewrite vec_dot_app.
  done.
Qed.

Lemma mx_row_vblock {n n' m}
  (A : Matrix R n m) (B : Matrix R n' m) i :
  mx_row (mx_vblock A B) i =
  sum_rect (λ _, _) (mx_row A) (mx_row B) (fin_sum_case i).
Proof.
  unfold mx_row, mx_vblock, Matrix.
  rewrite lookup_vapp.
  done.
Qed.

Lemma mx_col_hblock {n m m'}
  (A : Matrix R n m) (B : Matrix R n m') i :
  mx_col (mx_hblock A B) i =
  sum_rect (λ _, _) (mx_col A) (mx_col B) (fin_sum_case i).
Proof.
  unfold mx_col, mx_hblock, Matrix.
  apply vec_eq; intros j.
  rewrite vlookup_map, vlookup_zip_with.
  rewrite lookup_vapp.
  destruct (fin_sum_case i); cbn; now rewrite vlookup_map.
Qed.

Lemma compose_matrix_vblock_l {n n' m o}
  (A : Matrix R n m) (B : Matrix R n' m)
  (C : Matrix R m o) :
  compose_matrix (mx_vblock A B) C =
  mx_vblock (compose_matrix A C) (compose_matrix B C).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_compose, mlookup_vblock.
  rewrite mx_row_vblock.
  induction i as [i|i] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn -[vec_dot].
    now rewrite mlookup_compose.
  - rewrite fin_sum_case_R; cbn -[vec_dot].
    now rewrite mlookup_compose.
Qed.


Lemma compose_matrix_hblock_r {n m o o'}
  (A : Matrix R n m) (B : Matrix R m o)
  (C : Matrix R m o') :
  compose_matrix A (mx_hblock B C) =
  mx_hblock (compose_matrix A B) (compose_matrix A C).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_compose, mlookup_hblock.
  rewrite mx_col_hblock.
  induction j as [j|j] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn -[vec_dot].
    now rewrite mlookup_compose.
  - rewrite fin_sum_case_R; cbn -[vec_dot].
    now rewrite mlookup_compose.
Qed.

Lemma compose_matrix_0_mid {n o} (A : Matrix R n 0) (B : Matrix R 0 o) :
  compose_matrix A B = const_matrix 0.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_compose', mlookup_const.
  rewrite sum_of_fin_0.
  done.
Qed.



End mx_plus.



Lemma matrix_double_nonempty_hblock_vblock_ind {R}
  (P : forall n m, Matrix R n m -> Matrix R n m -> Prop)
  (HPnil_l : forall m (A B : Matrix R 0 m), P _ _ A B)
  (HPnil_r : forall n (A B : Matrix R n 0), P _ _ A B)
  (HP_1_1 : forall (A B : Matrix R 1 1), P _ _ A B)
  (HPhblock : forall n m m' (A A' : Matrix R n m) (B B' : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A A' -> P _ _ B B' -> P _ _ (mx_hblock A B) (mx_hblock A' B'))
  (HPvblock : forall n n' m (A A' : Matrix R n m) (B B' : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A A' -> P _ _ B B' -> P _ _ (mx_vblock A B) (mx_vblock A' B')) :
  forall n m A B, P n m A B.
Proof.
  intros n m A B.
  destruct n; [now auto|].
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m; [auto|].
    change (S (S m)) with (1 + S m) in *.
    rewrite <- (mx_hblock_split A), <- (mx_hblock_split B).
    apply HPhblock; [lia..|auto|auto].
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A), <- (mx_vblock_split B).
    apply HPvblock; [lia..|apply IHn|apply IHn]; lia.
Qed.


Lemma matrix_composable_double_nonempty_hblock_vblock_ind {R}
  (P : forall n m o, Matrix R n m -> Matrix R m o -> Prop)
  (HPnil_l : forall m o (A : Matrix R 0 m) (B : Matrix R m o), P _ _ _ A B)
  (HPnil_c : forall n o (A : Matrix R n 0) (B : Matrix R 0 o), P _ _ _ A B)
  (HPnil_r : forall n m (A : Matrix R n m) (B : Matrix R m 0), P _ _ _ A B)
  (HP_1_1 : forall (A B : Matrix R 1 1), P _ _ _ A B)
  (HP_l : forall n n' m o (A : Matrix R n m) (A' : Matrix R n' m) (B : Matrix R m o),
    n <> 0 -> n' <> 0 -> m <> 0 -> o <> 0 ->
    P _ _ _ A B -> P _ _ _ A' B ->
    P _ _ _ (mx_vblock A A') B)
  (HP_r : forall n m o o' (A : Matrix R n m) (B : Matrix R m o) (B' : Matrix R m o'),
    n <> 0 -> m <> 0 -> o <> 0 -> o' <> 0 ->
    P _ _ _ A B -> P _ _ _ A B' ->
    P _ _ _ A (mx_hblock B B'))
  (HP_c : forall n m m' o (A : Matrix R n m) (A' : Matrix R n m')
    (B : Matrix R m o) (B' : Matrix R m' o),
    n <> 0 -> m <> 0 -> m' <> 0 -> o <> 0 ->
    P _ _ _ A B -> P _ _ _ A' B' ->
    P _ _ _ (mx_hblock A A') (mx_vblock B B')) :
  forall n m o A B, P n m o A B.
Proof.
  intros n m o A B.
  destruct n; [now auto|].
  destruct m; [now auto|].
  destruct o; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m as [m IHm] using lt_wf_ind.
    destruct m.
    + clear IHm.
      induction o; [auto|].
      change (S (S o)) with (1 + S o) in *.
      rewrite <- mx_hblock_split.
      auto.
    + change (S (S m)) with (1 + S m) in *.
      rewrite <- (mx_vblock_split B), <- (mx_hblock_split A).
      apply HP_c; [lia..| |auto].
      apply IHm.
      lia.
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A).
    apply HP_l; [lia..| |auto].
    apply IHn.
    lia.
Qed.

Lemma const_matrix_alt {R} {n m} (r : R) :
  @const_matrix R n m r = Vector.const (Vector.const r _) _.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_const.
  unfold mx_to_fun, Matrix.
  rewrite 2 vlookup_const.
  done.
Qed.


Section mx_vec_prod.


Local Open Scope Matrix_scope.


Context {R} `{SR : SemiRing R rO rI radd rmul req}.



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

Lemma mx_vec_prod_0 {n} (A : Matrix R n 0) (v : vec R 0) :
  (mx_vec_prod A v) = (fun_to_vec (λ _, 0)).
Proof.
  apply vec_eq.
  intros i.
  unfold mx_vec_prod.
  rewrite vlookup_map, lookup_fun_to_vec.
  rewrite vec_dot_to_sum_of, sum_of_fin_0.
  done.
Qed.

Lemma mx_vec_prod_hblock_app {n m o} (A : Matrix R n m) (B : Matrix R n o)
  v w :
  vec_rel equiv (mx_vec_prod (mx_hblock A B) (v +++ w))
  (vzip_with radd (mx_vec_prod A v) (mx_vec_prod B w)).
Proof.
  apply vec_rel_lookup.
  intros i.
  unfold mx_vec_prod, mx_hblock.
  rewrite vlookup_zip_with, 3 vlookup_map, vlookup_zip_with.
  rewrite vec_dot_app.
  done.
Qed.

Lemma mx_vec_prod_vblock {n m o} (A : Matrix R n o) (B : Matrix R m o)
  v :
  mx_vec_prod (mx_vblock A B) v =
  (mx_vec_prod A v) +++ (mx_vec_prod B v).
Proof.
  apply Vector.map_append.
Qed.

End mx_vec_prod.












Definition b2zx (b : bool) : ZX 1 1 :=
  if b then — else zx_invsqrt2 ↕ (Z 1 0 0 ⟷ X 0 1 0).

Definition b2zx' (b : bool) : ZX 1 1 :=
  if b then — else Z 1 0 0 ⟷ X 0 1 0.


Lemma b2zx'_to_b2zx b : (√ 2 ^ Nat.b2n b) .* b2zx' b ∝= √ 2 .* b2zx b.
Proof.
  destruct b; cbn.
  - rewrite Cmult_1_r.
    done.
  - rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_assoc, zx_scale_eq_1_l by C_field.
    now rewrite stack_empty_l.
Qed.

Lemma b2zx_compose b c :
  b2zx b ⟷ b2zx c ∝= b2zx (b && c).
Proof.
  destruct b.
  - cbn.
    rewrite wire_removal_l.
    now destruct c.
  - cbn.
    destruct c.
    + cbn.
      now rewrite wire_removal_r.
    + cbn.
      zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
      rewrite const_of_zx_X_0_1_0_Z_1_0_0.
      rewrite (gadget_is_scaled_empty zx_invsqrt2).
      rewrite const_of_zx_invsqrt2.
      rewrite zx_of_const_to_scaled_empty.
      distribute_zxscale.
      apply zx_scale_simplify_eq; [C_field|].
      zxscat.
Qed.

Lemma b2zx_plus b c :
  Z 1 2 0 ⟷ (b2zx b ↕ b2zx c) ⟷ X 2 1 0 ∝=
  / √ 2 .* b2zx (b ⊕ c).
Proof.
  destruct b, c; cbn.
  - zxsrw (to_gadget hopf_rule_Z_X).
    rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    rewrite zx_of_const_to_scaled_empty.
    distribute_zxscale.
    rewrite zx_scale_assoc.
    apply zx_scale_simplify_eq; [C_field|zxscat].
  - rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_r, zx_scale_compose_distr_r, zx_scale_compose_distr_l.
    apply zx_scale_simplify_eq; [done|].
    zxfrw box_compose.
    rewrite box_compose.
    done.
  - rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    distribute_zxscale.
    rewrite zx_scale_stack_distr_l, zx_scale_compose_distr_r, zx_scale_compose_distr_l.
    apply zx_scale_simplify_eq; [done|].
    zxfrw box_compose.
    rewrite box_compose.
    done.
  - zxsrw <- (@X_add_l 0 0 1 0 0 0).
    rewrite (gadget_is_scaled_empty zx_invsqrt2), const_of_zx_invsqrt2.
    rewrite 2 Rplus_0_r.
    zxfcat.
Qed.

Fixpoint zx_binmat_aux_r {n} : forall (A : vec bool (S n)), ZX (S n) 1 :=
  match n with
  | 0 => fun A => b2zx (vhd A)
  | S n =>
    fun A =>
    (Z 0 1 0 ⟷ X 1 0 0) ↕ (b2zx (vhd A) ↕ zx_binmat_aux_r (vtl A) ⟷ X 2 1 0)
  end.

Fixpoint zx_binmat_aux_l {m n} : forall (A : Matrix bool (S m) (S n)), ZX (S n) (S m) :=
  match m with
  | 0 => fun A => zx_binmat_aux_r (vhd A)
  | S m =>
    fun A =>
    ZX_bcopy (S n) (!()) (!() + !()) (Z 1 2 0) ⟷
     (zx_binmat_aux_r (vhd A) ↕ zx_binmat_aux_l (vtl A))
  end.



Definition zx_binmat {m n} (A : Matrix bool m n) : ZX n m :=
  match n, m, A with
  | 0, 0, _ => ⦰
  | 0, S m, _ => (* TODO: What goes here? Any phase tricks? *)
    ZX_bcopy (S m) 0 (!()) (zx_invsqrt2 ↕ X 0 1 0)
  | S n, 0, _ =>
    ZX_bcopy (S n) (!()) 0 (Z 1 0 0)
  | S n, S m, A => zx_binmat_aux_l A
  end.


Definition mx_weight {m n} (A : Matrix bool m n) : nat :=
  sum_list_with (sum_list_with Nat.b2n ∘ vec_to_list) (vec_to_list A).


Definition mx_biadj {m n} (A : Matrix bool m n) : ZX (m * n) (m * n) :=
  n_stackv (λ row, cast _ _ mul_1_r' mul_1_r' (n_stackv b2zx' row)) A.

Lemma mx_biadj_alt {m n} (A : Matrix bool m n) :
  mx_biadj A ∝=
  cast _ _ mul_1_r' mul_1_r' $ n_stackv b2zx' (vjoin A).
Proof.
  induction A; [zxscat|].
  cbn.
  rewrite n_stackv_vapp.
  rewrite cast_contract_eq'.
  auto_cast_eqn rewrite cast_stack_distribute.
  f_equiv; [cast_irrelevance|].
  rewrite IHA.
  cast_irrelevance.
Qed.


Lemma mx_biadj_0_r {m} (A : vec (vec bool 0) m) :
  mx_biadj A ∝= cast _ _ (Nat.mul_0_r _) (Nat.mul_0_r _) ⦰.
Proof.
  induction A; [zxscat|].
  cbn.
  rewrite IHA.
  rewrite cast_id, stack_empty_l.
  cast_irrelevance.
Qed.



Lemma zx_binmat_alt_aux_l {m n} (A : vec (vec bool (S n)) (S m)) :
  zx_binmat_aux_l A ∝=
  (√2 ^ mx_weight A / √ 2 ^ S m) .*
  cast _ _ mul_1_r' mul_1_r'
  (S n ⇑ Z 1 (S m) 0 ⟷ zx_mul_comm _ _ ⟷
    mx_biadj A ⟷
      S m ⇑ X (S n) 1 0).
Proof.
  induction m as [[|m] IHm] using lt_wf_ind.
  - clear IHm.
    cbn [zx_binmat_aux_l].
    inv_vec A.
    intros A.
    cbn [vhd Vector.caseS].
    rewrite zx_mul_comm_1_r.
    rewrite cast_compose_r, nwire_removal_r, cast_contract_eq'.
    rewrite n_stack_1.
    rewrite mx_biadj_alt.
    rewrite compose_assoc.
    rewrite Z_is_wire.
    rewrite wire_to_n_wire, n_stack_n_wire.
    rewrite cast_compose_l, nwire_removal_l, 2 cast_contract_eq'.
    rewrite cast_X.
    rewrite cast_compose_l, cast_X, cast_contract_eq'.
    cbn [vjoin].
    rewrite (n_stackv_vapp b2zx' A [#]).
    change (n_stackv _ [#]) with ⦰.
    rewrite stack_empty_r_fwd, cast_contract_eq'.
    rewrite cast_compose_l, cast_X, cast_contract_eq'.
    induction n.
    + rewrite X_is_wire, wire_removal_r.
      cbn.
      inv_all_vec_fin.
      cbn.
      rewrite stack_empty_r_fwd, 2 cast_id.
      destruct x; cbn.
      * now rewrite zx_scale_eq_1_l by C_field.
      * rewrite Cmult_1_r.
        rewrite gadget_is_scaled_empty.
        rewrite zx_scale_stack_distr_l.
        rewrite stack_empty_l.
        rewrite const_of_zx_invsqrt2.
        f_equiv.
        C_field.
    + cbn [zx_binmat_aux_r].
      induction A as [h A] using vec_S_inv.
      cbn [vhd vtl Vector.caseS].
      rewrite IHn.
      clear IHn.
      rewrite <- zx_scale_sqrt2_alt.
      distribute_zxscale.
      rewrite n_stackv_vcons.
      rewrite cast_compose_distribute, cast_X.
      rewrite <- (nwire_removal_r (b2zx _)), stack_compose_distr, compose_assoc.
      rewrite (dominated_X_spider_fusion_bot_right (S n * 1) 0 1 1 0 0).
      rewrite cast_compose_distribute, cast_X.
      rewrite <- 2 zx_scale_compose_distr_l.
      rewrite Rplus_0_r.
      f_equiv; [|done].
      symmetry.
      change (S (S n) * 1) with (1 + S n * 1).
      change (S (S n)) with (1 + S n).
      auto_cast_eqn rewrite (@cast_stack_distribute 1 1 1 1).
      rewrite cast_id.
      rewrite <- 2 zx_scale_stack_distr_l.
      f_equiv; [|cast_irrelevance].
      unfold Cdiv.
      rewrite Cmult_assoc.
      rewrite 2 (Cmult_comm _ (/ _)).
      rewrite <- 2 zx_scale_assoc.
      f_equiv.
      cbn.
      rewrite 2 Nat.add_0_r, Cpow_add_r.
      rewrite 2 (Cmult_comm _ (√ 2 ^ sum_list_with _ _)).
      rewrite <- 2 zx_scale_assoc.
      f_equiv.
      rewrite b2zx'_to_b2zx.
      done.
  - cbn [zx_binmat_aux_l].
    induction A as [v A] using vec_S_inv.
    cbn [vhd vtl Vector.caseS].
    rewrite (IHm 0 ltac:(lia) [#v]).
    rewrite IHm by lia.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_r.
    apply zx_scale_simplify_eq.
    1:{
      cbn.
      rewrite Nat.add_0_r.
      rewrite Cpow_add_r.
      unfold mx_weight.
      C_field.
    }
    rewrite 2 (n_stack_to_ZX_copy _ (Z _ _ _)).
    rewrite zx_mul_comm_1_r.
    rewrite 2 n_wire_removal_l'.

    rewrite !cast_compose_distribute, !cast_contract_eq', !cast_id_eq.
    rewrite !stack_compose_distr.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, cast_contract_eq'.
    rewrite ZX_copy_stack_back, cast_contract_eq'.
    unfold ZX_bcopy.
    rewrite <- !compose_assoc.
    rewrite cast_compose_eq_mid_join.
    rewrite <- ZX_copy_compose.
    rewrite <- Z_add_r, 2 Rplus_0_r.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    2:{
      rewrite cast_stack_r_fwd, cast_contract_eq'.
      cbn -[cast].
      rewrite stack_empty_r_fwd, cast_stack_l_fwd, cast_contract_eq'.
      cast_irrelevance.
    }
    rewrite cast_compose_distribute, cast_id.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    2:{
      unfold mx_biadj.
      rewrite 2 n_stackv_vcons, n_stackv_vnil, stack_empty_r_fwd, 2 cast_contract_eq'.
      rewrite 2 cast_stack_l_fwd, cast_contract_eq'.
      cast_irrelevance.
    }
    rewrite compose_assoc, cast_compose_distribute, cast_contract_eq'.

    unfold ZX_copy.
    cbn [bsize btree_size].
    rewrite zx_mul_comm_1_l.
    rewrite n_wire_removal_l'.
    rewrite cast_compose_distribute, cast_contract_eq', compose_assoc.
    f_equiv; [cast_irrelevance|].
    rewrite <- stack_compose_distr.
    rewrite n_wire_removal_l', cast_contract_eq', cast_n_wire.
    rewrite zx_mul_comm_cancel.
    rewrite n_wire_stack.
    rewrite nwire_removal_r.
    cast_irrelevance.
Qed.


Lemma zx_binmat_alt {m n} (A : vec (vec bool n) m) :
  zx_binmat A ∝=
  (√2 ^ mx_weight A / √ 2 ^ m) .*
  cast _ _ mul_1_r' mul_1_r'
  (n ⇑ Z 1 m 0 ⟷ zx_mul_comm _ _ ⟷
    mx_biadj A ⟷
      m ⇑ X n 1 0).
Proof.
  induction m.
  - cbn.
    rewrite cast_compose_r, 3 compose_empty_r, 2 cast_contract_eq'.
    inv_vec A.
    cbn.
    rewrite Cdiv_1_r, zx_scale_1_l.
    destruct n.
    + cbn.
      zxscat.
    + cbn -[n_stack].
      unfold ZX_bcopy.
      cbn -[n_stack].
      unfold ZX_copy.
      rewrite zx_mul_comm_0_r, cast_compose_r, compose_empty_r, 2 cast_contract_eq'.
      rewrite zx_mul_comm_1_l, cast_compose_l, nwire_removal_l, 2 cast_contract_eq'.
      cast_irrelevance.
  - destruct n.
    + cbn [zx_binmat].
      replace (mx_weight A) with 0. 2:{
        unfold mx_weight.
        symmetry.
        induction A; cbn; inv_all_vec_fin; cbn; lia.
      }
      rewrite mx_biadj_0_r.
      rewrite zx_mul_comm_0_l.
      change (0 ⇑ _) with ⦰.
      rewrite compose_empty_l.
      rewrite cast_compose_eq_mid_join, compose_empty_l.
      rewrite cast_compose_l, compose_empty_l, 2 cast_contract_eq'.
      change (_ ^ 0)%C with C1.
      unfold Cdiv; rewrite Cmult_1_l.
      rewrite <- Cpow_inv.
      rewrite <- zx_scale_cast.
      generalize (S m) as m'.
      clear.
      intros m.
      unfold ZX_bcopy.
      cbn.
      unfold ZX_copy.
      rewrite zx_mul_comm_0_l, zx_mul_comm_1_r.
      rewrite cast_compose_l, compose_empty_l, cast_compose_r,
        nwire_removal_r, 4 cast_contract_eq'.
      cast_irrelevance.
      induction m.
      * cbn.
        rewrite zx_scale_1_l.
        done.
      * cbn.
        rewrite IHm.
        rewrite (gadget_is_scaled_empty zx_invsqrt2).
        rewrite const_of_zx_invsqrt2.
        rewrite 2 zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc.
        rewrite stack_empty_l.
        done.
    + apply zx_binmat_alt_aux_l.
Qed.




Lemma zx_binmat_cast {n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix bool n m) :
  zx_binmat (cast_matrix Hn Hm A) =
  cast _ _ (eq_sym Hm) (eq_sym Hn) (zx_binmat A).
Proof.
  subst.
  rewrite cast_matrix_id, cast_id_eq.
  done.
Qed.

Lemma zx_binmat_0_l n A : @zx_binmat 0 n A ∝= ZX_bcopy n (!()) 0 (Z 1 0 0).
Proof.
  destruct n.
  - cbn.
    rewrite ZX_bcopy_0, cast_id.
    done.
  - cbn.
    done.
Qed.

Lemma zx_binmat_0_r m A : @zx_binmat m 0 A ∝= ZX_bcopy m 0 (!()) (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  destruct m.
  - cbn.
    rewrite ZX_bcopy_0, cast_id.
    done.
  - cbn.
    done.
Qed.


Lemma zx_binmat_aux_l_vblock {n n' m} (A : Matrix bool (S n) (S m)) (B : Matrix bool (S n') (S m)) :
  zx_binmat_aux_l (mx_vblock A B) ∝=
  ZX_bcopy (S m) (!()) (!() + !()) (Z 1 2 0) ⟷
  (zx_binmat_aux_l A ↕ zx_binmat_aux_l B).
Proof.
  induction n; [inv_vec A; done|].
  cbn [zx_binmat_aux_l].
  rewrite vtl_mx_vblock.
  rewrite IHn.
  rewrite <- (nwire_removal_l (zx_binmat_aux_r _)).
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  rewrite <- (ZX_bcopy_n_wire (S m) (!())).
  rewrite <- (@ZX_bcopy_stack (S m) (!()) (!()) (!()) (!() + !())).
  rewrite <- (@ZX_bcopy_compose (S m) (!()) (!() + !()) (!() + (!() + !()))).
  rewrite <- (nwire_removal_l (zx_binmat_aux_l B)) at 2.
  rewrite stack_compose_distr.
  rewrite <- compose_assoc.
  rewrite <- (ZX_bcopy_n_wire (S m) (!())).
  rewrite <- (@ZX_bcopy_stack (S m) (!()) (!() + !()) (!()) (!())).
  rewrite <- (@ZX_bcopy_compose (S m) (!()) (!() + !()) ((!() + !()) + !())).
  rewrite (stack_assoc_fwd (zx_binmat_aux_r (vhd A)) (zx_binmat_aux_l (vtl A)) (zx_binmat_aux_l B)).
  rewrite cast_compose_r, cast_compose_distribute, 2 cast_id.
  f_equiv; [|now inv_vec A].
  unfold ZX_bcopy.
  rewrite cast_contract_eq'.
  cast_irrelevance.
  f_equiv.
  zxfcat.
Qed.

Lemma zx_binmat_vblock {n n' m} (A : Matrix bool n m) (B : Matrix bool n' m) :
  zx_binmat (mx_vblock A B) ∝=
  ZX_bcopy m (!()) (!() + !()) (Z 1 2 0) ⟷
  (zx_binmat A ↕ zx_binmat B).
Proof.
  destruct n'. 1:{
    inv_vec B.
    rewrite mx_vblock_nil_r.
    rewrite zx_binmat_cast.
    rewrite <- nwire_removal_l.
    rewrite stack_split_antidiag, <- compose_assoc.
    apply compose_simplify_casted_abs; [lia|intros..];
    [|rewrite stack_empty_r_fwd, cast_contract_eq'; cast_irrelevance].
    clear.
    rewrite (proof_irrel _ add_0_r').
    clear Hm'.
    rewrite zx_binmat_0_l.
    rewrite <- (ZX_bcopy_n_wire m (!())).
    rewrite <- (@ZX_bcopy_stack m (!()) (!()) (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (!() + 0)).
    rewrite ZX_bcopy_n_wire.
    unfold ZX_bcopy.
    rewrite cast_contract_eq'.
    rewrite ZX_copy_1_1.
    rewrite (ltac:(zxfcat) : Z 1 2 0 ⟷ (n_wire 1 ↕ Z 1 0 0) ∝= —).
    symmetry.
    fold (n_wire (1 * m)).
    rewrite cast_n_wire.
    done.
  }
  destruct n.
  1:{
    inv_vec A.
    change (mx_vblock _ B) with B.
    rewrite zx_binmat_0_l.
    rewrite stack_split_diag, <- compose_assoc.
    rewrite <- (ZX_bcopy_n_wire m (!())).
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) (!()) ).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + !())).
    rewrite stack_empty_l.
    rewrite (ltac:(zxfcat) : Z 1 2 0 ⟷ (Z 1 0 0 ↕ n_wire 1) ∝= n_wire 1).
    unfold ZX_bcopy.
    rewrite ZX_copy_n_wire, cast_n_wire.
    rewrite nwire_removal_l.
    done.
  }
  destruct m.
  - unfold Matrix in A, B.
    rewrite 3 zx_binmat_0_r.
    unfold ZX_bcopy.
    rewrite 3 (ZX_copy_le_1 _ (zx_invsqrt2 ↕ X 0 1 0)) by lia.
    cbn -[n_stack Nat.add].
    rewrite 3 cast_contract_eq'.
    auto_cast_eqn rewrite <- cast_stack_distribute.
    auto_cast_eqn rewrite nstack_split, cast_contract_eq'.
    rewrite ZX_copy_0.
    rewrite cast_contract_eq', n_wire_removal_l', cast_contract_eq'.
    cast_irrelevance.
  - apply zx_binmat_aux_l_vblock.
Qed.



Lemma zx_binmat_aux_r_app {m m'} (vA : vec bool (S m)) (vB : vec bool (S m')) :
  zx_binmat_aux_r (vA +++ vB) ∝=
  zx_binmat_aux_r vA ↕ zx_binmat_aux_r vB ⟷
  ((√ 2) .* X 2 1 0).
Proof.
  induction m.
  - inv_vec vA; intros h.
    cbn.
    rewrite gadget_is_scaled_empty, <- const_of_zx_colorswap.
    simpl.
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    distribute_zxscale.
    apply zx_scale_simplify_eq; [lca|].
    (* FIXME: zxpscat doesn't work here!!! *)
    rewrite stack_empty_l.
    done.
  - induction vA as [a vA] using vec_S_inv.
    cbn.

    rewrite gadget_is_scaled_empty, <- const_of_zx_colorswap.
    simpl.
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite IHm.
    rewrite 2 zx_scale_compose_distr_r, 3 zx_scale_stack_distr_l,
      zx_scale_stack_distr_r, 2 stack_empty_l, 2 zx_scale_compose_distr_l.
    rewrite 2 zx_scale_assoc.
    apply zx_scale_simplify_eq; [cbn; C_field|].
    rewrite stack_push_br.
    rewrite stack_push_tr.
    rewrite (stack_assoc_back_fwd (b2zx a) (zx_binmat_aux_r vA) (zx_binmat_aux_r vB)).
    rewrite 2 compose_assoc.
    apply compose_simplify_casted_abs; [lia|intros ?..].
    + cast_irrelevance.
    + rewrite cast_id.
      apply colorswap_diagrams_eq.
      cbn.
      zxfcat.
Qed.


Lemma zx_binmat_aux_l_hblock {n m m'} (A : Matrix bool (S n) (S m)) (B : Matrix bool (S n) (S m')) :
  zx_binmat_aux_l (mx_hblock A B) ∝=
  zx_binmat_aux_l A ↕ zx_binmat_aux_l B ⟷
  ((√ 2 ^ S n) .* ZX_bcopy (S n) (!() + !()) (!()) (X 2 1 0)).
Proof.
  fold Nat.add.
  induction n.
  1:{
    inv_vec A; intros vA.
    inv_vec B; intros vB.
    cbn.
    rewrite zx_binmat_aux_r_app.
    rewrite ZX_bcopy_1, cast_id.
    rewrite Cmult_1_r.
    done.
  }

  induction A as [vA A] using vec_S_inv.
  induction B as [vB B] using vec_S_inv.
  rewrite mx_hblock_cons.
  cbn [zx_binmat_aux_l].
  cbn.
  rewrite IHn.
  rewrite zx_binmat_aux_r_app.
  rewrite stack_compose_distr.
  rewrite stack_compose_distr.
  rewrite (stack_mid_comm (zx_binmat_aux_r vA) (zx_binmat_aux_r vB) (zx_binmat_aux_l A) (zx_binmat_aux_l B)).
  rewrite <- 3 compose_assoc, compose_assoc.
  change (S (?x + S ?y)) with (S x + S y).
  f_equiv; [f_equiv; [|done]|].
  - change (S (?x + S ?y)) with (S x + S y).
    unfold ZX_bcopy.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, cast_contract_eq'.
    auto_cast_eqn rewrite cast_compose_l, cast_backwards_eq.
    symmetry.
    rewrite cast_contract_eq'.
    cbn [bsize].
    unfold ZX_copy.
    rewrite 3 zx_mul_comm_1_l.
    rewrite 3 n_wire_removal_l'.
    rewrite 4 cast_compose_l.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, 3 cast_contract_eq'.
    rewrite stack_compose_distr.
    auto_cast_eqn rewrite nstack_split.
    rewrite compose_assoc, cast_compose_distribute, cast_contract_eq'.
    rewrite 2 cast_compose_distribute.
    apply compose_simplify_casted_abs; [lia|intros ?..];
    [rewrite cast_contract_eq'; cast_irrelevance|].
    rewrite 3 cast_contract_eq'.
    rewrite cast_stack_l_fwd, cast_stack_r_fwd, 2 cast_contract_eq'.

    apply prop_eq_of_perm_eq; [auto_zxperm..|].
    cbn [perm_of_zx].
    rewrite 3 perm_of_zx_cast.
    cbn [perm_of_zx].
    rewrite perm_of_zx_mid_comm, 3 perm_of_zx_mul_comm.
    intros i Hi.
    cbn -[Nat.add].
    rewrite stack_perms_defn by lia.
    bdestruct_one.
    2:{
      rewrite stack_perms_right by lia.
      rewrite Nat.sub_add by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite mod_n_to_2n by lia.
      rewrite (fun H => (Kronecker.div_eq_iff i _ 1 H).2) by lia.
      rewrite mod_n_to_2n by lia.
      rewrite (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      lia.
    }
    rewrite stack_perms_defn by lia.
    bdestruct_one.
    1:{
      rewrite stack_perms_left by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite 2 Nat.mod_small, 2 Nat.div_small by lia.
      lia.
    }
    rewrite big_swap_perm_defn by lia.
    bdestruct_one.
    1:{
      rewrite stack_perms_left by lia.
      rewrite 2 kron_comm_perm_defn by lia.
      rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      rewrite mod_n_to_2n, (fun H => (Kronecker.div_eq_iff _ _ 1 H).2) by lia.
      lia.
    }
    rewrite stack_perms_right by lia.
    rewrite 2 kron_comm_perm_defn by lia.
    rewrite Nat.mod_small, Nat.div_small by lia.
    rewrite Nat.mod_small, Nat.div_small by lia.
    lia.
  - unfold ZX_bcopy.
    rewrite zx_scale_stack_distr_r, zx_scale_stack_distr_l,
       zx_scale_assoc, zx_scale_compose_distr_r.
    apply zx_scale_simplify_eq; [cbn; C_field|].
    rewrite cast_stack_r_fwd, cast_compose_r.
    cbn -[cast Nat.add].
    symmetry.
    auto_cast_eqn rewrite cast_backwards_eq.
    rewrite cast_contract_eq'.
    rewrite cast_compose_distribute, cast_id.
    unfold ZX_copy.
    rewrite 2 zx_mul_comm_1_r.
    rewrite 2 n_wire_removal_r'.
    rewrite cast_stack_r_fwd, cast_compose_eq_mid_join.
    rewrite stack_push_bl.
    rewrite <- compose_assoc.
    auto_cast_eqn rewrite cast_backwards_eq, cast_contract_eq'.
    rewrite cast_compose_distribute, cast_id.
    f_equiv; [|done].

    apply prop_eq_of_perm_eq; [auto_zxperm..|].
    cbn [perm_of_zx].
    rewrite 2 perm_of_zx_cast, perm_of_n_wire.
    rewrite perm_of_zx_mid_comm, 2 perm_of_zx_mul_comm.
    replace (1 + S n + (1 + S n)) with (2 * S (S n)) by lia.
    rewrite kron_comm_perm_2_n_succ_alt.
    rewrite Nat.add_comm.
    rewrite <- stack_perms_assoc.
    cbn.
    rewrite Nat.add_0_r, Nat.add_1_r.
    done.
  Unshelve.
    cbn; lia.
Qed.





Lemma zx_binmat_hblock {n m m'} (A : Matrix bool n m) (B : Matrix bool n m') :
  zx_binmat (mx_hblock A B) ∝=
  (√ 2 ^ n) .* (zx_binmat A ↕ zx_binmat B ⟷
  ZX_bcopy n (!() + !()) (!()) (X 2 1 0)).
Proof.
  destruct m'. 1:{
    rewrite zx_binmat_0_r.
    rewrite <- zx_scale_compose_distr_l, <- zx_scale_stack_distr_r.
    rewrite mx_hblock_nil_r.
    rewrite zx_binmat_cast.

    rewrite stack_split_diag, compose_assoc.
    rewrite <- nwire_removal_r.
    apply compose_simplify_casted_abs; [lia|intros..];
    [rewrite stack_empty_r_fwd, cast_contract_eq'; cast_irrelevance|].
    clear.
    rewrite (proof_irrel _ add_0_r').
    clear Hm'.
    rewrite <- (ZX_bcopy_n_wire n (!())).
    distribute_zxscale.
    rewrite <- (@ZX_bcopy_stack n (!()) (!()) 0 (!())).
    rewrite zx_scale_cast.
    rewrite <- (@ZX_bcopy_compose n (!() + 0) (!() + !()) (!())).
    assert (Hrw : n_wire 1 ↕ (zx_invsqrt2 ↕ X 0 1 0) ⟷ X 2 1 0 ∝= zx_invsqrt2 ↕ n_wire 1).
    1:{
      apply colorswap_diagrams_eq.
      simpl.
      zxfcat.
    }
    rewrite Hrw.
    clear Hrw.
    rewrite ZX_bcopy_n_wire.
    cbn.
    unfold ZX_bcopy.
    rewrite cast_contract_eq'.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite (ZX_copy_stack n zx_invsqrt2 —).
    rewrite ZX_copy_le_1 by lia.
    rewrite n_stack_gadget_to_scalar, const_of_zx_invsqrt2.
    rewrite cast_contract_eq', ZX_copy_wire.
    rewrite cast_stack_l_fwd.
    rewrite zx_scale_stack_distr_l, n_wire_stack, cast_contract_eq'.
    rewrite zx_scale_cast, cast_n_wire.
    rewrite zx_scale_assoc, zx_scale_eq_1_l; [done|].
    rewrite <- Cpow_mul_l, Cinv_r by nonzero.
    rewrite Cpow_1_l.
    done.
  }
  destruct m.
  1:{
    rewrite mx_hblock_nil_l.
    rewrite zx_binmat_0_r.
    rewrite <- nwire_removal_r at 1.
    rewrite stack_split_antidiag, compose_assoc, stack_empty_l.
    rewrite <- zx_scale_compose_distr_r.
    f_equiv.
    rewrite <- (ZX_bcopy_n_wire n (!())).
    rewrite <- (@ZX_bcopy_stack n 0 (!()) (!()) (!()) ).
    rewrite <- (@ZX_bcopy_compose n (0 + !()) (!() + !()) (!())).

    assert (Hrw : (zx_invsqrt2 ↕ X 0 1 0) ↕ n_wire 1 ⟷ X 2 1 0 ∝= zx_invsqrt2 ↕ n_wire 1).
    1:{
      apply colorswap_diagrams_eq.
      simpl.
      zxfcat.
    }
    rewrite Hrw.
    clear Hrw.
    rewrite ZX_bcopy_n_wire.
    cbn.
    unfold ZX_bcopy.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite (ZX_copy_stack n zx_invsqrt2 —).
    rewrite ZX_copy_le_1 by lia.
    rewrite n_stack_gadget_to_scalar, const_of_zx_invsqrt2.
    rewrite cast_contract_eq', ZX_copy_wire.
    rewrite cast_stack_l_fwd.
    rewrite zx_scale_stack_distr_l, n_wire_stack, cast_contract_eq'.
    rewrite zx_scale_cast, cast_n_wire.
    rewrite zx_scale_assoc, zx_scale_eq_1_l; [done|].
    rewrite <- Cpow_mul_l, Cinv_r by nonzero.
    rewrite Cpow_1_l.
    done.
  }
  destruct n.
  - unfold Matrix in A, B.
    cbn.
    rewrite zx_scale_1_l, ZX_bcopy_0, n_wire_removal_r', cast_id.
    unfold ZX_bcopy.
    rewrite 3 (ZX_copy_le_1) by (cbn; lia).
    cbn -[n_stack].
    change (S (?x + S ?y)) with (S x + S y).
    auto_cast_eqn rewrite nstack_split, 2 cast_contract_eq'.
    change 0 with (0 + 0).
    rewrite cast_stack_distribute.
    rewrite 2 cast_contract_eq'.
    done.
  - rewrite <- zx_scale_compose_distr_r.
    apply zx_binmat_aux_l_hblock.
Qed.





Lemma b2zx_copy b : b2zx b ⟷ Z 1 2 0 ∝= Z 1 2 0 ⟷ (b2zx b ↕ b2zx b).
Proof.
  destruct b; cbn.
  - zxscat.
  - zxsrw (to_gadget (X_state_copy'' false 2 0 eq_refl eq_refl)).
    cbn.
    rewrite Cmult_1_r, zx_of_const_invsqrt2.
    zxfcat.
Qed.













Lemma zx_binmat_copy {n m} (A : Matrix bool n m) :
  zx_binmat A ⟷ ZX_bcopy n (!()) (!() + !()) (Z 1 2 0) ∝=
  ZX_bcopy m (!()) (!() + !()) (Z 1 2 0) ⟷ (zx_binmat A ↕ zx_binmat A).
Proof.
  induction n, m, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite ZX_bcopy_0, cast_id, nwire_removal_r.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    unfold ZX_bcopy.
    cast_irrelevance.
    f_equiv.
    zxfcat.
  - rewrite zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) (!() + !())).
    rewrite <- (@ZX_bcopy_stack n 0 (!()) 0 (!())).
    rewrite ZX_bcopy_0, cast_id, nwire_removal_l.
    unfold ZX_bcopy.
    cast_irrelevance.
    f_equiv.
    zxsrw (to_gadget (X_state_copy'' false 2 0 eq_refl eq_refl)).
    cbn.
    rewrite Cmult_1_r, zx_of_const_invsqrt2.
    zxscat.
  - hnf in A.
    inv_all_vec_fin.
    cbn.
    rewrite ZX_bcopy_1, cast_id.
    apply b2zx_copy.
  - rewrite zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) (!() + !())).
    rewrite (to_gadget bi_algebra_rule_Z_X).
    rewrite <- zx_scale_defn.
    rewrite ZX_bcopy_scale.
    rewrite zx_scale_compose_distr_r.
    unfold bi_alg_Z_X.
    rewrite compose_assoc.
    rewrite (@ZX_bcopy_compose n _ ((!() + !()) + (!() + !()))).
    rewrite ZX_bcopy_stack.
    rewrite <- compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite IHA1, IHA2.
    rewrite (@ZX_bcopy_compose n _ ((!() + !()) + (!() + !()))).
    rewrite ZX_bcopy_to_zx_mid_comm.
    rewrite stack_compose_distr.
    rewrite <- compose_assoc.

    rewrite (compose_assoc _ (zx_binmat A1 ↕ zx_binmat A1 ↕ (zx_binmat A2 ↕ zx_binmat A2))).
    rewrite zx_mid_comm_commutes_r.
    rewrite ZX_bcopy_stack.
    rewrite 2 compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- compose_assoc.
    setoid_rewrite <- ZX_bcopy_1_2_add.
    distribute_zxscale.
    done.
  - rewrite zx_binmat_vblock.
    rewrite ZX_bcopy_1_2_add.
    rewrite compose_assoc.
    cbn.
    rewrite <- (compose_assoc (_ ↕ _)), <- stack_compose_distr.
    rewrite IHA1, IHA2, 2 stack_compose_distr.
    rewrite compose_assoc.
    rewrite (zx_mid_comm_commutes_r (zx_binmat A1) (zx_binmat A1) (zx_binmat A2) (zx_binmat A2)).
    rewrite <- ! compose_assoc.
    rewrite <- 2 (@ZX_bcopy_stack m (!()) (!() + !()) (!()) (!() + !())).
    rewrite <- 2 (@ZX_bcopy_compose m (!()) (!() + !()) ((!() + !()) + (!() + !()))).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_compose m (!()) ((!() + !()) + (!() + !())) ((!() + !()) + (!() + !()))).
    f_equiv.
    f_equiv.
    zxfcat.
Qed.







Lemma b2zx_erase b : b2zx b ⟷ Z 1 0 0 ∝= Z 1 0 0.
Proof.
  destruct b; [zxscat|].
  cbn.
  zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_of_const_invsqrt2.
  rewrite <- zx_of_const_mult', Cinv_r, zx_of_const_1; [zxscat|nonzero].
Qed.

Lemma zx_binmat_erase {n m} (A : Matrix bool n m) :
  zx_binmat A ⟷ ZX_bcopy n (!()) 0 (Z 1 0 0) ∝=
  ZX_bcopy m (!()) 0 (Z 1 0 0).
Proof.
  induction n, m, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite ZX_bcopy_0, cast_id, nwire_removal_r.
    done.
  - rewrite zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) 0).
    rewrite ZX_bcopy_0, cast_id.
    rewrite pull_out_top, compose_assoc.
    rewrite (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_of_const_to_scaled_empty.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite <- zx_of_const_mult', Cinv_l, zx_of_const_1 by nonzero.
    rewrite ZX_bcopy_n_wire.
    done.
  - hnf in A.
    inv_all_vec_fin.
    cbn.
    rewrite ZX_bcopy_1, cast_id.
    apply b2zx_erase.
  - rewrite zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l, compose_assoc.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) 0).
    rewrite <- zx_scale_compose_distr_r.
    rewrite <- (ZX_bcopy_scale n _ (!() + !()) 0).
    assert (Hrw : √ 2 .* (X 2 1 0 ⟷ Z 1 0 0) ∝= Z 1 0 0 ↕ Z 1 0 0); [|revert Hrw; intros ->].
    1:{
      apply transpose_diagrams_eq.
      rewrite zx_scale_transpose.
      cbn.
      rewrite (to_gadget (Z_state_copy'' false 2 0 eq_refl eq_refl)).
      rewrite zx_scale_defn.
      zxaclean_lhs.
      rewrite <- zx_of_const_mult'.
      rewrite zx_of_const_1' by (cbn; C_field).
      zxscat.
    }
    rewrite (ZX_bcopy_cast_r _ _ _ _ (@bluniti _ 0)).
    rewrite cast_compose_r_eq_mid.
    rewrite 2 cast_id.
    rewrite ZX_bcopy_stack.
    cbn.
    rewrite <- (@stack_compose_distr _ _ 0 _ _ 0).
    rewrite IHA1, IHA2.
    rewrite ZX_bcopy_1_0_add.
    done.
  - rewrite zx_binmat_vblock.
    rewrite ZX_bcopy_1_0_add.
    rewrite compose_assoc.
    cbn.
    rewrite <- (@stack_compose_distr _ _ 0 _ _ 0).
    rewrite IHA1, IHA2.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    zxfcat.
Qed.





Lemma b2zx_hadamard b : b2zx b ⟷ □ ∝= □ ⟷ transpose (b2zx b).
Proof.
  destruct b; [zxscat|].
  cbn.
  rewrite gadget_transpose.
  rewrite <- (colorswap_involutive (Z 1 0 0 ⟷ X 0 1 0)), colorswap_is_bihadamard.
  cbn.
  zxsrw box_compose.
  zxscat.
Qed.

Lemma zx_binmat_hadamard {m n} (A : Matrix bool m n) :
  √2 ^ m .* zx_binmat A ⟷ m ↑ □ ∝= √2 ^ n .* n ↑ □ ⟷ (zx_binmat (mx_transpose A)) ⊤.
Proof.
  induction m, n, A using matrix_nonempty_hblock_vblock_ind.
  - rewrite zx_binmat_0_l.
    rewrite zx_binmat_0_r.
    rewrite (ZX_bcopy_transpose m 0 (!())).
    cbn.
    rewrite gadget_transpose.
    rewrite zx_scale_1_l, zx_scale_compose_distr_l.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose m (!()) (!()) 0).
    rewrite <- (@ZX_bcopy_scale m _ (!()) 0).
    rewrite compose_empty_r.
    f_equiv.
    change (X 1 0 0) with (⊙ (Z 1 0 0)).
    rewrite colorswap_is_bihadamard.
    cbn.
    zxsrw box_compose.
    rewrite <- zx_of_const_invsqrt2, <- zx_of_const_mult', Cinv_l, zx_of_const_1, stack_empty_l by nonzero.
    done.
  - rewrite zx_binmat_0_l.
    rewrite zx_binmat_0_r.
    rewrite (ZX_bcopy_transpose n (!()) 0).
    cbn.
    rewrite zx_scale_1_l, zx_scale_compose_distr_l.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose n 0 (!()) (!())).
    rewrite <- (@ZX_bcopy_scale n _ 0 (!())).
    rewrite compose_empty_l.
    f_equiv.
    change (X 0 1 0) with (⊙ (Z 0 1 0)).
    rewrite colorswap_is_bihadamard.
    cbn.
    zxsrw box_compose.
    rewrite <- zx_of_const_invsqrt2, <- zx_of_const_mult', Cinv_l, zx_of_const_1, stack_empty_l by nonzero.
    done.
  - hnf in A.
    inv_all_vec_fin.
    rewrite nstack1_1, Cpow_1_r.
    cbn.
    rewrite 2 zx_scale_compose_distr_l, b2zx_hadamard.
    done.
  - rewrite zx_binmat_hblock.
    rewrite 3 zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose n (!() + !()) (!()) (!())).
    rewrite X_to_Z, 3 compose_assoc, nstack1_1, box_compose, wire_removal_r.
    rewrite (@ZX_bcopy_compose n _ (!() + !())).
    cbn.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite ZX_bcopy_stack, ZX_bcopy_1_1.
    rewrite <- compose_assoc, <- stack_compose_distr.
    rewrite <- 2 zx_scale_compose_distr_l, <- zx_scale_stack_distr_l,
      <- zx_scale_compose_distr_l, <- zx_scale_stack_distr_r, <- zx_scale_compose_distr_l.
    rewrite IHA1, IHA2.
    rewrite mx_transpose_hblock.
    rewrite zx_binmat_vblock.
    cbn.
    rewrite (ZX_bcopy_transpose n (! ()) (!() + !())).
    cbn.
    rewrite nstack1_split.
    rewrite <- compose_assoc, <- stack_compose_distr.
    distribute_zxscale.
    rewrite Cmult_comm, <- Cpow_add_r.
    done.

  - rewrite zx_binmat_vblock, Cpow_add_r.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc, <- zx_scale_compose_distr_r, nstack1_split.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_r, <- zx_scale_stack_distr_l.
    rewrite <- 2 zx_scale_compose_distr_l.
    rewrite IHA1, IHA2.
    distribute_zxscale.
    rewrite stack_compose_distr.
    rewrite <- compose_assoc.
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_stack m (!()) (!()) (!()) (!())).
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (!() + !())).

    rewrite Z_to_X, nstack1_1.
    cbn.
    rewrite stack_empty_r_fwd, cast_id.
    rewrite compose_assoc, <- (stack_compose_distr Box Box Box Box), box_compose.
    rewrite wire_to_n_wire, n_wire_stack, nwire_removal_r.
    rewrite mx_transpose_vblock.
    rewrite zx_binmat_hblock.
    rewrite zx_scale_transpose.
    cbn.
    rewrite (ZX_bcopy_transpose m (!() + !()) (! ())).
    cbn.
    distribute_zxscale.
    f_equiv.
    rewrite <- compose_assoc.
    rewrite <- (@ZX_bcopy_compose m (!()) (!()) (!() + !())).
    done.
Qed.

Lemma zx_binmat_colorswap {m n} (A : Matrix bool m n) :
  ⊙ (zx_binmat A) ∝=
    √ 2 ^ n / √ 2 ^ m .* (zx_binmat (mx_transpose A)) ⊤.
Proof.
  rewrite colorswap_is_bihadamard.
  pose proof (zx_binmat_hadamard A) as Hrw.
  rewrite zx_scale_compose_distr_l in Hrw.
  rewrite zx_scale_eq_l in Hrw by nonzero.
  rewrite Hrw.
  distribute_zxscale.
  rewrite <- compose_assoc.
  rewrite <- n_stack1_compose, box_compose, nwire_removal_l.
  f_equiv.
  C_field.
Qed.


Lemma zx_binmat_cocopy {m n} (A : Matrix bool m n) :
  √2 ^ n .* (ZX_bcopy n (!()+!()) (!()) (X 2 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ m .* (zx_binmat A ↕ zx_binmat A ⟷ ZX_bcopy m (!()+!()) (!()) (X 2 1 0)).
Proof.
  apply colorswap_diagrams_eq.
  rewrite 2 zx_scale_colorswap.
  cbn [color_swap].
  rewrite ZX_bcopy_colorswap.
  rewrite (ZX_bcopy_colorswap m (!()+!()) (!())).
  cbn.
  rewrite zx_binmat_colorswap.
  distribute_zxscale.
  apply transpose_diagrams_eq.
  rewrite 2 zx_scale_transpose.
  cbn.
  rewrite transpose_involutive.
  rewrite (ZX_bcopy_transpose n (!()+!()) (!())), (ZX_bcopy_transpose m (!()+!()) (!())).
  cbn.
  rewrite zx_binmat_copy.
  f_equiv; [|done].
  C_field.
Qed.


Lemma zx_binmat_coerase {m n} (A : Matrix bool m n) :
  √2 ^ m .* (ZX_bcopy n 0 (!()) (X 0 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ n .* (ZX_bcopy m 0 (!()) (X 0 1 0)).
Proof.
  apply colorswap_diagrams_eq.
  rewrite 2 zx_scale_colorswap.
  cbn [color_swap].
  rewrite (ZX_bcopy_colorswap n 0 (!())).
  rewrite (ZX_bcopy_colorswap m 0 (!())).
  cbn.
  rewrite zx_binmat_colorswap.
  distribute_zxscale.
  apply transpose_diagrams_eq.
  rewrite 2 zx_scale_transpose.
  cbn.
  rewrite transpose_involutive.
  rewrite (ZX_bcopy_transpose n 0 (!())).
  rewrite (ZX_bcopy_transpose m 0 (!())).
  cbn.
  rewrite zx_binmat_erase.
  f_equiv.
  C_field.
Qed.


Lemma zx_binmat_cocopy' {m n} (A : Matrix bool m n) :
  (ZX_bcopy n (!()+!()) (!()) (X 2 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ m / √2 ^ n .* (zx_binmat A ↕ zx_binmat A ⟷ ZX_bcopy m (!()+!()) (!()) (X 2 1 0)).
Proof.
  unfold Cdiv.
  rewrite Cmult_comm, <- zx_scale_assoc.
  rewrite <- zx_scale_eq_l by nonzero.
  apply zx_binmat_cocopy.
Qed.


Lemma zx_binmat_coerase' {m n} (A : Matrix bool m n) :
  (ZX_bcopy n 0 (!()) (X 0 1 0) ⟷ zx_binmat A) ∝=
  √2 ^ n / √2 ^ m .* (ZX_bcopy m 0 (!()) (X 0 1 0)).
Proof.
  unfold Cdiv.
  rewrite Cmult_comm, <- zx_scale_assoc.
  rewrite <- zx_scale_eq_l by nonzero.
  apply zx_binmat_coerase.
Qed.



Lemma b2zx_plus' b c :
  √2 .* (Z 1 2 0 ⟷ (b2zx b ↕ b2zx c) ⟷ X 2 1 0) ∝=
  b2zx (b ⊕ c).
Proof.
  rewrite b2zx_plus, zx_scale_assoc, Cinv_r, zx_scale_1_l by nonzero.
  done.
Qed.


Lemma zx_binmat_plus {m n} (A B : Matrix bool m n) :
  √2 ^ m .* (ZX_bcopy n (!()) (!() + !()) (Z 1 2 0) ⟷
    (zx_binmat A ↕ zx_binmat B) ⟷ ZX_bcopy m (!() + !()) (!()) (X 2 1 0)) ∝=
  zx_binmat (mx_plus A B).
Proof.
  revert m n A B.
  (* FIXME: Debug... *)
  apply matrix_double_nonempty_hblock_vblock_ind; intros *.
  - rewrite 3 zx_binmat_0_l.
    rewrite <- (@ZX_bcopy_stack m (!()) 0 (!()) 0).
    cbn.
    rewrite ZX_bcopy_0, cast_id, compose_empty_r, zx_scale_1_l.
    rewrite <- (@ZX_bcopy_compose m (!()) (!() + !()) (0 + 0)).
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    zxfcat.
  - rewrite 3 zx_binmat_0_r.
    rewrite <- (@ZX_bcopy_stack n 0 (!()) 0 (!())).
    cbn.
    rewrite ZX_bcopy_0, cast_id, compose_empty_l.
    rewrite <- (@ZX_bcopy_compose n (0 + 0) (!() + !()) (!())).
    rewrite (ZX_bcopy_cast_l _ _ _ blunit), 2 cast_id.
    rewrite <- (@ZX_bcopy_scale n _ 0 (!())).
    f_equiv.
    apply colorswap_diagrams_eq.
    rewrite zx_scale_colorswap.
    cbn.
    rewrite gadget_colorswap.
    cbn.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_scale_defn.
    distribute_zxscale.
    rewrite zx_scale_compose_distr_l, zx_scale_assoc.
    apply zx_scale_simplify_eq; [C_field|zxfcat].
  - hnf in A, B.
    inv_all_vec_fin.
    cbn.
    rewrite 2 ZX_bcopy_1, 2 cast_id, Cmult_1_r.
    rewrite b2zx_plus'.
    done.
  - intros Hn Hm Hm' IHA IHB.
    rewrite 2 zx_binmat_hblock.
    rewrite zx_scale_stack_distr_l, zx_scale_stack_distr_r, zx_scale_assoc,
      zx_scale_compose_distr_r, zx_scale_compose_distr_l, zx_scale_assoc.
    rewrite stack_compose_distr.
    rewrite ZX_bcopy_1_2_add.
    rewrite <- compose_assoc.
    cbn.
    rewrite (compose_assoc _ (zx_mid_comm _ _ _ _)).
    rewrite <- zx_mid_comm_commutes_r, <- compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite 2 compose_assoc, <- (compose_assoc (zx_mid_comm _ _ _ _)).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_stack n (!()+!()) (!()) (!()+!()) (!())).
    rewrite <- (@ZX_bcopy_compose n ((!()+!())+(!()+!()))
      ((!()+!())+(!()+!())) (!()+!())).
    rewrite <- (@ZX_bcopy_compose n ((!()+!())+(!()+!())) (!()+!()) (!())).
    assert (Hrw : — ↕ ⨉ ↕ — ⟷ (X 2 1 0 ↕ X 2 1 0) ⟷ X 2 1 0 ∝=
      (X 2 1 0 ↕ X 2 1 0) ⟷ X 2 1 0) by (apply colorswap_diagrams_eq; cbn; zxfcat).
    rewrite Hrw.
    rewrite (@ZX_bcopy_compose n _ (!()+!())).
    rewrite ZX_bcopy_stack.
    rewrite <- compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite <- zx_scale_assoc, <- zx_scale_compose_distr_l.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_l, <- zx_scale_stack_distr_r.
    rewrite IHA, IHB.
    rewrite mx_plus_hblock.
    rewrite zx_binmat_hblock.
    done.
  - intros Hn Hn' Hm IHA IHB.
    rewrite 2 zx_binmat_vblock.
    rewrite stack_compose_distr.
    cbn.
    rewrite stack_mid_comm, <- 3 compose_assoc.
    rewrite <- (@ZX_bcopy_stack m (!()) (!()+!()) (!()) (!()+!())).
    rewrite <- (@ZX_bcopy_compose m (!()) (!()+!()) ((!()+!())+(!()+!()))).
    rewrite <- ZX_bcopy_to_zx_mid_comm.
    rewrite <- (@ZX_bcopy_compose m (!()) ((!()+!())+(!()+!())) ((!()+!())+(!()+!()))).
    assert (Hrw : Z 1 2 0 ⟷ (Z 1 2 0 ↕ Z 1 2 0) ⟷ (— ↕ ⨉ ↕ —) ∝=
      Z 1 2 0 ⟷ (Z 1 2 0 ↕ Z 1 2 0)) by zxfcat.
    rewrite Hrw.
    rewrite (@ZX_bcopy_compose m _ (!()+!())).
    rewrite ZX_bcopy_stack.
    rewrite 2 compose_assoc.
    rewrite ZX_bcopy_2_1_add, <- (compose_assoc (zx_mid_comm _ _ _ _)).
    rewrite <- zx_mid_comm_transpose, zxperm_transpose_left_inverse, nwire_removal_l by auto_zxperm.
    rewrite <- stack_compose_distr, compose_assoc.
    cbn.
    rewrite <- stack_compose_distr, <- 2 compose_assoc.
    rewrite <- zx_scale_compose_distr_r, Cpow_add_r, Cmult_comm.
    rewrite <- zx_scale_assoc, <- zx_scale_stack_distr_l, <- zx_scale_stack_distr_r.
    rewrite IHA, IHB.
    rewrite mx_plus_vblock.
    rewrite zx_binmat_vblock.
    done.
Qed.

Lemma b2zx_compose' b c :
  b2zx b ⟷ b2zx c ∝= b2zx (c && b).
Proof.
  rewrite b2zx_compose, andb_comm.
  done.
Qed.



Lemma zx_binmat_aux_r_const_false n : zx_binmat_aux_r (Vector.const false (S n)) ∝=
  ZX_bcopy (S n) (! ()) 0 (Z 1 0 0) ⟷ (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  induction n.
  + cbn.
    rewrite ZX_bcopy_1, cast_id.
    zxscat.
  + cbn [zx_binmat_aux_r].
    rewrite IHn.
    cbn.
    rewrite <- zx_of_const_invsqrt2, <- 2zx_scale_defn.
    distribute_zxscale.
    rewrite (stack_compose_distr (Z 1 0 0)).
    rewrite zx_scale_compose_distr_l, compose_assoc.
    rewrite <- X_add_l, 2 Rplus_0_l.
    rewrite <- zx_sqrt2_defn'_ZX.
    rewrite <- zx_of_const_sqrt2.
    rewrite <- zx_scale_defn.
    distribute_zxscale.
    rewrite Cmult_assoc, Cinv_r, Cmult_1_l by nonzero.
    do 2 f_equiv; [|done].
    unfold ZX_bcopy.
    rewrite cast_stack_r_fwd.
    cbn.
    rewrite 2 ZX_copy_le_1 by lia.
    rewrite cast_stack_r_fwd.
    rewrite 2 cast_contract_eq'.
    cast_irrelevance.
Qed.

Lemma zx_binmat_const_false n m :
  zx_binmat (const_matrix false) ∝= ZX_bcopy n (! ()) 0 (Z 1 0 0)
    ⟷ ZX_bcopy m 0 (! ()) (zx_invsqrt2 ↕ X 0 1 0).
Proof.
  rewrite const_matrix_alt.
  cbn.

  destruct n. 1:{
    rewrite zx_binmat_0_r, ZX_bcopy_0, cast_id, compose_empty_l.
    done.
  }
  destruct m. 1:{
    rewrite zx_binmat_0_l, ZX_bcopy_0, cast_id, compose_empty_r.
    done.
  }
  cbn [zx_binmat].
  induction m.
  - cbn [zx_binmat_aux_l].
    rewrite zx_binmat_aux_r_const_false, ZX_bcopy_1, cast_id.
    done.
  - cbn [zx_binmat_aux_l].
    rewrite IHm.
    rewrite zx_binmat_aux_r_const_false.
    rewrite stack_compose_distr, <- compose_assoc.
    rewrite <- (@ZX_bcopy_stack (S n) (!()) 0 (!()) 0).
    rewrite <- (@ZX_bcopy_compose (S n) (!()) (!()+!()) (0+0)).
    rewrite <- (@Z_add_r 1 0 0), 2 Rplus_0_l.
    rewrite (ZX_bcopy_cast_r _ _ _ _ blunit), 2 cast_id.
    f_equiv.
    unfold ZX_bcopy.
    rewrite cast_stack_r_fwd.
    cast_irrelevance.
    cbn.
    rewrite 2 ZX_copy_le_1 by lia.
    rewrite cast_stack_r_fwd.
    cast_irrelevance.
Qed.

#[export] Instance zx_binmat_proper n m : Proper (equiv ==> eq) (@zx_binmat n m).
Proof.
  intros A A' HA.
  f_equal.
  apply mx_eq.
  rewrite mx_equiv in HA.
  done.
Qed.

Lemma zx_binmat_compose {k m n} (A : Matrix bool m n) (C : Matrix bool k m) :
  zx_binmat A ⟷ zx_binmat C ∝= zx_binmat (compose_matrix C A).
Proof.
  induction k, m, n, C, A using matrix_composable_double_nonempty_hblock_vblock_ind.
  - rewrite 2 zx_binmat_0_l.
    clear.
    rewrite zx_binmat_erase.
    done.
  - rewrite compose_matrix_0_mid.
    rewrite zx_binmat_0_l, zx_binmat_0_r.
    setoid_rewrite zx_binmat_const_false.
    done.
  - rewrite 2 zx_binmat_0_r.
    rewrite <- zx_of_const_invsqrt2.
    rewrite <- zx_scale_defn.
    rewrite 2 ZX_bcopy_scale, zx_scale_compose_distr_l.
    rewrite 2 Cpow_inv.
    rewrite <- zx_scale_eq_l by nonzero.
    rewrite zx_scale_assoc, Cmult_comm, <- zx_scale_assoc.
    rewrite <- zx_scale_eq_r by nonzero.
    apply zx_binmat_coerase.
  - unfold Matrix in *.
    inv_all_vec_fin.
    cbn.
    rewrite b2zx_compose', xorb_false_r.
    done.
  - rewrite compose_matrix_vblock_l, 2 zx_binmat_vblock.
    rewrite <- compose_assoc.
    rewrite zx_binmat_copy.
    rewrite compose_assoc.
    cbn.
    rewrite <- stack_compose_distr.
    rewrite IHA1, IHA2.
    done.
  - rewrite compose_matrix_hblock_r, 2 zx_binmat_hblock.
    rewrite zx_scale_compose_distr_l.
    rewrite compose_assoc.
    rewrite <- zx_scale_compose_distr_r.
    rewrite (zx_binmat_cocopy A1).
    rewrite zx_scale_compose_distr_r, <- compose_assoc, <- stack_compose_distr.
    rewrite IHA1, IHA2.
    done.
  - rewrite zx_binmat_vblock, zx_binmat_hblock, compose_matrix_hblock_vblock.
    rewrite <- zx_binmat_plus.
    rewrite zx_scale_compose_distr_r.
    f_equiv.
    rewrite <- compose_assoc.
    f_equiv.
    rewrite compose_assoc.
    f_equiv.
    cbn.
    rewrite <- stack_compose_distr, IHA1, IHA2.
    done.
Qed.














(* Lemma ZX_bvcopy_compose_gen {A B} {n m o} (f : A -> ZX n m) (g : B -> ZX m o) *)















Definition X_pi_wire (b : bool) : ZX 1 1 :=
  X 1 1 (if b then PI else 0).

Lemma Z_state_0_erase α :
  Z 0 1 0 ⟷ X 1 1 α ∝= Z 0 1 0.
Proof.
  rewrite (to_gadget (Z_state_copy'' false 1 α eq_refl eq_refl)).
  rewrite zx_of_const_1.
  zxscat.
Qed.

Lemma Z_state_0_coerase α :
  X 1 1 α ⟷ Z 1 0 0 ∝= Z 1 0 0.
Proof.
  transpose_of (Z_state_0_erase α).
Qed.

Lemma X_state_0_erase α :
  X 0 1 0 ⟷ Z 1 1 α ∝= X 0 1 0.
Proof.
  colorswap_of (Z_state_0_erase α).
Qed.

Lemma X_state_0_coerase α :
  Z 1 1 α ⟷ X 1 0 0 ∝= X 1 0 0.
Proof.
  transpose_of (X_state_0_erase α).
Qed.


Lemma X_pi_wire_b2zx b c :
  X_pi_wire b ⟷ b2zx c ∝=
  b2zx c ⟷ X_pi_wire (b && c).
Proof.
  destruct b, c; unfold X_pi_wire; cbn.
  - rewrite wire_removal_l, wire_removal_r.
    done.
  - rewrite X_is_wire, wire_removal_r.
    zxsrw (Z_state_0_coerase PI).
    zxscat.
  - rewrite wire_removal_l, wire_removal_r.
    done.
  - rewrite X_is_wire.
    rewrite wire_removal_l, wire_removal_r.
    done.
Qed.

Lemma X_pi_wire_plus b c :
  X_pi_wire b ↕ X_pi_wire c ⟷ X 2 1 0 ∝=
  X 2 1 0 ⟷ X_pi_wire (b ⊕ c).
Proof.
  unfold X_pi_wire.
  rewrite <- X_add_l, X_spider_1_1_fusion.
  rewrite Rplus_0_l, Rplus_0_r.
  destruct b, c; [|f_equiv; cbn; lra..].
  apply X_eq_2_PI.
  lra.
Qed.

Definition Z_pi_wire (b : bool) : ZX 1 1 :=
  Z 1 1 (if b then PI else 0).

Lemma zx_binmat_red_pi_action {m n} (A : Matrix bool m n) (v : vec bool n) :
  n_stackv1 X_pi_wire v ⟷ zx_binmat A ∝= zx_binmat A ⟷ n_stackv1 X_pi_wire (mx_vec_prod A v).
Proof.
  induction n as [[|[|n]] IHn] using lt_wf_ind.
  - rewrite zx_binmat_0_r.
    cbn.
    rewrite compose_empty_l.
    rewrite mx_vec_prod_0.
    rewrite (n_stackv1_const' (X 1 1 0)). 2:{
      intros i.
      rewrite lookup_fun_to_vec.
      done.
    }
    rewrite <- ZX_bcopy_1_1.
    rewrite <- (@ZX_bcopy_compose m 0 (!()) (!())).
    rewrite X_is_wire, wire_removal_r.
    done.
  - clear IHn.
    induction m as [[|[|m]] IHm] using lt_wf_ind.
    + rewrite zx_binmat_0_l.
      rewrite ZX_bcopy_1, cast_id.
      cbn.
      rewrite compose_empty_r.
      rewrite stack_empty_r_fwd, cast_id.
      unfold X_pi_wire.
      apply transpose_diagrams_eq.
      cbn.
      rewrite (to_gadget (Z_state_copy'' false 1 (if (vhd v) then PI else 0) eq_refl eq_refl)).
      rewrite cast_id, zx_of_const_1.
      zxscat.
    + unfold Matrix in *.
      clear.
      inv_all_vec_fin.
      cbn.
      rewrite 2 stack_empty_r_fwd, 2 cast_id, xorb_false_r.
      rewrite X_pi_wire_b2zx.
      done.
    + change (S (S m)) with (1 + S m) in *.
      rewrite <- (mx_vblock_split A).
      rewrite zx_binmat_vblock.
      rewrite mx_vec_prod_vblock, n_stackv1_vapp.
      rewrite compose_assoc.
      cbn [btree_fold].
      rewrite <- stack_compose_distr.
      rewrite <- 2 IHm by lia.
      rewrite stack_compose_distr.
      rewrite <- 2 compose_assoc.
      f_equiv.
      rewrite ZX_bcopy_1, cast_id.
      clear.
      inv_vec v.
      intros []; unfold X_pi_wire; cbn; rewrite stack_empty_r_fwd, cast_id.
      * rewrite (X_pi_copy _ eq_refl eq_refl).
        cbn.
        rewrite stack_empty_r_fwd, cast_id.
        done.
      * rewrite X_is_wire.
        zxscat.
  - change (S (S n)) with (1 + S n) in *.
    induction v as [vl vr] using vec_add_inv.
    rewrite <- (mx_hblock_split A).
    pose proof (mx_vec_prod_hblock_app (mx_splitl A) (mx_splitr A) vl vr) as Hrw.
    pose proof (leibniz_equiv_iff (A:=vec bool m)) as Hleib.
    apply Hleib in Hrw.
    rewrite Hrw.
    rewrite zx_binmat_hblock.
    fold (vec_equiv (A:=bool) (n:=1 + S n)) in Hrw.
    rewrite zx_scale_compose_distr_r.
    rewrite n_stackv1_vapp.
    rewrite <- compose_assoc.
    rewrite <- stack_compose_distr.
    rewrite 2 IHn by lia.
    cbn [btree_fold].
    distribute_zxscale.
    f_equiv.
    rewrite stack_compose_distr, 2 compose_assoc.
    f_equiv.
    rewrite <- 3 ZX_bvcopy_1_1.
    rewrite (vec_to_vmap_lookup_vfinseq (mx_vec_prod _ vl)).
    rewrite (vec_to_vmap_lookup_vfinseq (mx_vec_prod _ vr)).
    rewrite 2 ZX_bvcopy_vmap.
    rewrite <- (ZX_bvcopy_stack (!()) (!()) (!()) (!()) m).
    rewrite vzip_with_map.
    rewrite vzip_with_diag, ZX_bvcopy_vmap.
    erewrite <- (@ZX_bvcopy_const (fin m)) at 1.
    rewrite <- (ZX_bvcopy_compose (!()+!()) (!()+!()) (!()) m).
    erewrite <- (@ZX_bvcopy_const (fin m)) at 1.
    rewrite <- (ZX_bvcopy_compose (!()+!()) (!()) (!()) m).
    apply (ZX_bvcopy_ext_eq (!()+!()) (!()) m).
    intros i.
    cbn.
    rewrite lookup_vfinseq.
    rewrite X_pi_wire_plus.
    done.
Qed.


Lemma zx_binmat_green_pi_action {m n} (A : Matrix bool m n) (v : vec bool m) :
  zx_binmat A ⟷ n_stackv1 Z_pi_wire v ∝= 
  n_stackv1 Z_pi_wire (mx_vec_prod (mx_transpose A) v) ⟷ zx_binmat A.
Proof.
  apply colorswap_diagrams_eq, transpose_diagrams_eq.
  cbn.
  rewrite 2 n_stackv1_colorswap, 2 n_stackv1_transpose.
  rewrite zx_binmat_colorswap.
  rewrite zx_scale_transpose, transpose_involutive.
  distribute_zxscale.
  unfold Z_pi_wire.
  cbn.
  rewrite zx_binmat_red_pi_action.
  done.
Qed.
  




(* Lemma mx_biadj_vblock {n n' m} (A : Matrix bool n m) (B : Matrix bool n' m) :
  mx_biadj (mx_vblock A B) ∝=
  cast _ _ mul_add_distr_r mul_add_distr_r (mx_biadj A ↕ mx_biadj B).

Notation BinMatrix m n := (vec (vec bool n) m).

Declare Scope binmatrix_scope.
Delimit Scope binmatrix_scope with binmatrix.
Bind Scope binmatrix_scope with BinMatrix.

Definition binmx_vblock

Lemma zx_binmat_vapp {m m' n} (A : BinMatrix ) *)







Module JPV.

Import ZXsymm ZXauto ZXfrob.

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
  unfold cupcap_controlizer.
  split.
  - unfold is_controlled_state.
    zxsrw (Z_1_2_state_0 0).
    zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    zxsrw left_triangle_state_0.
    zxsrw (Z_1_n_state0 0 0).
    zxsrw (triangle_state_0).
    pose proof (Z_state_copy 0 2 PI eq_refl eq_refl) as Hcopy.
    rewrite Rmult_0_l in Hcopy.
    zxsrw (to_gadget Hcopy).
    rewrite Cexp_0, Cexp_PI.
    replace ((C1 + C1) * (C1 - (-1)%R) + C2 * (-1)%R)%C with C2 by lca.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxscat|].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    cbn.
    autorewrite with RtoC_db.
    C_field.
  - (* rewrite <- compose_assoc. *)
    zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_to_scaled_empty, zx_scale_1_l.
    zxsrw left_triangle_state_1.
    zxsrw (@Z_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    rewrite (gadget_is_scaled_empty (Z 0 0 0)).
    rewrite const_of_zx_Z_gen.
    rewrite Cexp_0.
    zxsrw triangle_state_1.
    zxsrw (@X_1_n_state_1 2 PI).
    zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite X_eq_2_PI by lra.
    rewrite <- ! zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxacat|].
    cbn.
    C_field; lca.
Time Qed.

Lemma JPV'_27 : Z 1 2 0 ⟷ (◁ ↕ —) ⟷ X 2 1 0 ∝= / √2 .* ◁.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  destruct b; cbn.
  - zxsrw (Z_1_2_state_1 0).
    zxsrw left_triangle_state_1.
    zxsrw (X_zxperm_absorbtion_left 2 2 1 0 ⨉ ltac:(auto_zxperm)).
    zxsrw left_triangle_state_1.
    rewrite state_1_defn.
    zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 0 1 PI 0 eq_refl eq_refl).
    pose proof (Z_state_copy 0 1 PI eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l in Hrw.
    rewrite Rplus_0_r.
    zxsrw (to_gadget Hrw).
    clear Hrw.
    rewrite <- !zx_of_const_mult'.
    f_equiv.
    f_equiv.
    rewrite Cexp_0, Cexp_PI.
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
  - zxsrw (Z_1_2_state_0 0).
    zxsrw left_triangle_state_0.
    zxsrw left_triangle_state_0.
    rewrite state_0_defn.
    (* zxsrw (X_zxperm_absorbtion_left 2 2 1 0 ⨉ ltac:(auto_zxperm)). *)
    zxsrw <- (@X_add_l 0 0 1 0 0 0).
    rewrite 2 Rplus_0_r.
    zxscat.
Qed.

Lemma X_0_0_PI_zero : X 0 0 PI ∝= zx_zero.
Proof.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_gen.
  rewrite Cexp_PI.
  replace (C1 + (-1)%R) with C0 by lca.
  apply zx_scale_0_l.
Qed.

Import ComposeRules.
Lemma JPV_2_17 : (— ↕ X 0 2 PI) ⟷ ((Z 2 1 0 ⟷ ▷) ↕ ◁) ⟷ (Z 2 1 0) ∝=
  /√ 2 .* (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros br.
  apply transpose_diagrams_eq.
  cbn.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros bl.
  rewrite left_triangle_transpose, triangle_transpose.
  rewrite zx_scale_transpose.
  cbn.
  destruct bl, br.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite left_triangle_state_1, triangle_state_1.
    rewrite Z_spider_1_1_fusion, Rplus_0_r.
    pose proof (X_wrap_over_top_right 1 0 PI) as Hrw.
    rewrite cap_Z in Hrw.
    rewrite state_1_defn at 2 4.
    rewrite !zx_scale_transpose.
    zxsrw <- Hrw.
    zxsrw <- state_0_defn.
    zxsrw (@X_1_n_state_0 0 PI).
    zxsrw (@X_1_n_state_1 1 PI).
    zxsrw (@X_spider_1_1_fusion 0 0 (PI + PI) PI).
    rewrite (X_Rmodeq_2PI _ PI) by (exists (1 : BinInt.Z); lra).
    rewrite X_0_0_PI_zero.
    rewrite ?zx_scale_0_l.
    rewrite ?compose_0_l, ?stack_0_l.
    done.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_1.
    rewrite Cexp_0, zx_scale_1_l.
    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite left_triangle_state_1, triangle_state_1.
    rewrite Z_spider_1_1_fusion, Rplus_0_r.
    pose proof (X_wrap_over_top_right 1 0 PI) as Hrw.
    rewrite cap_Z in Hrw.
    rewrite state_0_defn at 1 2.
    rewrite !zx_scale_transpose.
    zxsrw <- Hrw.
    rewrite state_1_defn.
    zxsrw (@X_spider_1_1_fusion 0 1 PI PI).

    rewrite (X_eq_2_PI 0 1 (PI + PI)) by lra.
    zxsrw (@X_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    zxsrw (to_gadget (X_state_pi_copy 0 eq_refl eq_refl)).
    zxsrw (@X_spider_1_1_fusion 0 0 0 0).
    rewrite Rplus_0_r.
    rewrite (gadget_is_scaled_empty (X 0 0 0)).
    rewrite const_of_zx_X_gen.
    rewrite Cexp_0.
    replace (C1 + C1) with C2 by lca.
    etransitivity; [apply gadget_is_scaled_empty|etransitivity; [|symmetry; apply gadget_is_scaled_empty] ].
    f_equiv.
    rewrite ? const_of_zx_compose, ?const_of_zx_stack.
    rewrite ? const_of_zx_of_const.
    rewrite const_of_zx_scale.
    cbn.
    autorewrite with RtoC_db.
    C_field.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_0.

    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite triangle_state_0, left_triangle_state_0.
    rewrite Z_1_2_state_0.
    rewrite state_1_defn at 1 2.
    rewrite !zx_scale_transpose.
    cbn.
    rewrite state_0_defn.
    zxsrw (@X_spider_1_1_fusion 0 0 0 PI).
    zxsrw (@X_spider_1_1_fusion 0 0 0 PI).
    rewrite Rplus_0_l.
    now rewrite X_0_0_PI_zero, ?compose_0_l, ?stack_0_l.
  - cbn.
    rewrite <- !compose_assoc.
    rewrite Z_1_2_state_0.

    rewrite <- (@stack_compose_distr 0 1 2 0 1 1).
    rewrite <- !compose_assoc.
    rewrite triangle_state_0, left_triangle_state_0.
    rewrite Z_1_2_state_0.
    rewrite state_0_defn at 3 5.
    rewrite !zx_scale_transpose.
    cbn.
    rewrite state_0_defn at 1 2.
    zxsrw (X_spider_fusion_top_left_bot_right 0 0 1 0 0 0 PI eq_refl eq_refl).
    pose proof (Z_state_copy 0 0 PI eq_refl eq_refl) as Hrw.
    rewrite Rplus_0_l.
    rewrite Rmult_0_l in Hrw.
    zxsrw (to_gadget Hrw).
    zxsrw (Z_1_n_state0 0 0).
    rewrite <- ! zx_of_const_mult'.
    f_equiv.
    f_equiv.
    rewrite Cexp_PI, Cexp_0.
    cbn.
    autorewrite with RtoC_db.
    C_field.
    lca.
Qed.

Lemma JPV_2_4_a : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 1 0 ⟷ X 1 0 0) ∝= ⦰.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_stack.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_invsqrt2_defn.
  rewrite const_of_zx_invsqrt2.
  etransitivity; [|apply zx_scale_1_l].
  f_equiv.
  C_field.
Qed.

Lemma JPV_2_4_b : (Z 0 3 0 ⟷ X 3 0 0) ↕ (Z 0 3 0 ⟷ X 3 0 0) ↕ Z 0 0 0 ∝= ⦰.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite <- zx_invsqrt2_defn.
  rewrite gadget_is_scaled_empty.
  rewrite 2 const_of_zx_stack.
  rewrite const_of_zx_Z_0.
  rewrite const_of_zx_invsqrt2.
  etransitivity; [|apply zx_scale_1_l].
  f_equiv.
  C_field.
Qed.


Lemma JPV_2_5 α β : (Z 0 1 PI ⟷ X 1 0 α) ↕ (Z 0 1 PI ⟷ X 1 0 β) ∝=
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
Qed.

#[export] Instance ZXDVERT_inhab : Inhabited ZXDVERT := _.

Lemma JPV_2_6 : Z 1 1 PI ⟷ X 1 2 0 ∝= X 1 2 0 ⟷ (Z 1 1 PI ↕ Z 1 1 PI).
Proof.
  pose proof (Z_copy 2 1 eq_refl eq_refl) as Hrw.
  rewrite Rmult_1_l in Hrw.
  rewrite Hrw.
  zxscat.
Qed.


(* FIXME: Move *)
Lemma fold_state_0 : X 0 1 0 ∝= √2 .* state_0.
Proof.
  rewrite state_0_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.
Lemma fold_state_1 : X 0 1 PI ∝= √2 .* state_1.
Proof.
  rewrite state_1_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.


Lemma JPV_2_7 : X 0 1 0 ⟷ zx_triangle ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  rewrite fold_state_0.
  zxsrw triangle_state_0.
  rewrite (gadget_is_scaled_empty (_ ⟷ _)).
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  zxscat.
Qed.

Lemma JPV_2_8 : X 0 1 0 ⟷ zx_triangle_left ∝= X 0 1 0.
Proof.
  rewrite fold_state_0.
  zxsrw left_triangle_state_0.
  zxscat.
Qed.

Lemma JPV_2_9 : X 0 1 PI ⟷ zx_triangle ∝= X 0 1 PI.
Proof.
  rewrite fold_state_1.
  zxsrw triangle_state_1.
  zxscat.
Qed.

Lemma JPV_2_10 : X 0 1 PI ⟷ zx_triangle_left ∝= Z 0 1 0 ↕ (Z 0 1 0 ⟷ X 1 0 0).
Proof.
  rewrite fold_state_1.
  zxsrw left_triangle_state_1.
  rewrite (gadget_is_scaled_empty (_ ⟷ _)).
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  zxscat.
Qed.

Lemma JPV_2_11 : X 1 1 PI ⟷ zx_triangle_left ∝= zx_triangle ⟷ X 1 1 PI.
Proof.
  prep_matrix_equivalence.
  rewrite 2 zx_compose_spec.
  pose proof not_semantics as Hrw.
  rewrite not_defn in Hrw.
  rewrite Hrw.
  rewrite zx_triangle_semantics.
  rewrite zx_triangle_left_semantics.
  by_cell; lca.
Qed.

Lemma JPV_2_12 : Z 1 2 0 ⟷ (zx_triangle_left ↕ X 1 2 0) ⟷ (Z 2 1 0 ↕ —) ∝=
  Z 1 2 0 ⟷ (X 1 2 0 ↕ zx_triangle_left) ⟷ (— ↕ Z 2 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same.
  rewrite zx_of_const_1, 2 stack_empty_l.
  zxsrw (@X_1_n_state_b 2 0 b).
  zxsrw (@X_1_n_state_b 2 0 b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - rewrite Rplus_0_r.
    zxfcat.
  - zxsrw_rhs (@Z_self_swap_absorbtion_left_base 1 0).
    rewrite <- cap_X.
    zxfcat.
Qed.



Lemma JPV_2_13 : Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ (zx_triangle ⟷ zx_triangle)) ∝=
  zx_triangle ⟷ Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 0 0) ↕ —).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (left_triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  rewrite Cexp_0, Tauto.if_same.
  rewrite zx_of_const_1, stack_empty_l.
  destruct b.
  - zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_1, stack_empty_l.
    zxsrw left_triangle_state_1.
    zxsrw triangle_state_1.
    zxscat.
  - zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
    rewrite Rplus_0_r.
    rewrite <- cap_Z.
    zxarw_rhs (cup_pullthrough_top (zx_triangle_left ⟷ Z 1 0 0) —).
    zxsrw_rhs <- (eq_reflexivity (RA:=proportional_by_1)  _ _ zx_triangle_defn).
    zxsrw (Z_1_n_state0 0 0).
    zxscat.
Qed.

(* FIXME: Move *)
Lemma triangle_left_transpose : zx_triangle_left ⊤ = zx_triangle.
Proof.
  rewrite zx_triangle_left_defn.
  apply transpose_involutive_eq.
Qed.
Lemma zx_invsqrt2_defn' : zx_invsqrt2 ∝= Z 0 3 0 ⟷ X 3 0 0.
Proof.
  symmetry.
  rewrite gadget_is_scaled_empty.
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite <- zx_invsqrt2_defn.
  rewrite <- gadget_is_scaled_empty.
  done.
Qed.

Lemma JPV_2_14 : (Z 0 1 0 ⟷ zx_triangle) ↕
  (Z 0 1 0 ⟷ zx_triangle_left) ⟷ Z 2 1 0 ∝= Z 0 0 0 ↕ Z 0 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose, triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_n_state_b b 0 0).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - zxsrw (Z_1_n_state_b true 0 0).
    rewrite Cexp_0, zx_of_const_1.
    zxfcat.
  - zxsrw (Z_1_n_state_b false 0 0).
    rewrite zx_of_const_1.
    zxfcat.
Qed.

Lemma JPV_2_15 : Z 1 2 0 ⟷ (□ ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝=
  (Z 0 3 0 ⟷ X 3 0 0) ↕
  zx_triangle_left ⟷ Z 1 1 PI.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw <- zx_invsqrt2_defn'.
  rewrite gadget_is_scaled_empty, const_of_zx_invsqrt2.
  destruct b.
  - cbn.
    zxsrw box_state_1.
    rewrite state_minus_defn.
    zxfcat.
  - cbn.
    zxsrw box_state_0.
    rewrite state_plus_defn.
    zxsrw (Z_1_n_state0 1 PI).
    rewrite state_0_defn.
    zxfcat.
Qed.

Lemma JPV_2_16 : Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left) ⟷ Z 2 1 0 ∝= —.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b; zxfcat.
Qed.

(* FIXME: Move *)
Lemma const_of_zx_zero : const_of_zx zx_zero = 0.
Proof.
  unfold const_of_zx.
  rewrite zx_zero_semantics.
  done.
Qed.
Lemma zx_of_const_0 : zx_of_const 0 ∝= zx_zero.
Proof.
  apply const_of_zx_inj.
  rewrite const_of_zx_of_const, const_of_zx_zero.
  done.
Qed.
Lemma Z_2_1_0_states_b b c :
  state_b b ↕ state_b c ⟷ Z 2 1 0 ∝=
  (if eqb b c then state_b b else zx_zero).
Proof.
  apply transpose_diagrams_eq.
  cbn [transpose].
  apply prop_eq_by_eq_on_state_b_1_n.
  intros d.
  zxsrw (Z_1_n_state_b d 2 0).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  zxsrw (state_b_state_b_transpose d c).
  zxsrw (state_b_state_b_transpose d b).
  rewrite <- zx_of_const_mult'.
  rewrite <- RtoC_mult, b2R_mult.
  replace (_ && _) with (eqb b c && eqb d b) by (unfold eqb; Btauto.btauto).
  destruct (eqb b c); [|cbn; rewrite zx_zero_transpose, zx_of_const_0, compose_0_r; done].
  rewrite state_b_state_b_transpose.
  rewrite gadget_is_scaled_empty, const_of_zx_of_const.
  done.
Qed.


Lemma JPV_2_17' : Z 1 2 0 ⟷ (zx_triangle ↕ (X 1 1 PI ⟷ zx_triangle_left)) ⟷ Z 2 1 0 ∝=
  (X 0 3 0 ⟷ Z 3 0 0) ↕ (X 1 0 0 ⟷ Z 0 1 0).
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, stack_empty_l.
  rewrite <- not_defn.
  zxsrw (not_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (left_triangle_state_b (¬ b)).
  zxsrw (@X_1_n_state_b 0 0 b).
  rewrite Rplus_0_r.
  destruct b.
  - cbn.
    rewrite X_0_0_PI_zero.
    rewrite compose_0_l, stack_0_l.
    pose proof (Z_2_1_0_states_b true false) as Hrw.
    cbn in Hrw.
    rewrite <- Hrw.
    zxscat.
  - cbn.
    zxsrw <- (Aux.eq_reflexivity _ _ zx_invsqrt2_defn :> _ ∝= _).
    rewrite gadget_is_scaled_empty.
    rewrite 2 const_of_zx_compose, const_of_zx_invsqrt2, const_of_zx_of_const.
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_Z_0.
    rewrite zx_scale_eq_1_l by C_field.
    zxfcat.
Qed.

Lemma JPV_2_18_a : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 PI ⟷ zx_triangle_left) ↕
  zx_triangle_left) ⟷ Z 2 1 0) ∝=
  zx_triangle_left ↕ zx_triangle_left ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_left_transpose.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  zxsrw (triangle_state_b b).
  destruct b.
  - zxsrw (@X_1_n_state_1 2 PI).
    rewrite X_eq_2_PI by lra.
    rewrite <- cap_X.
    zxsrw <- (Z_wrap_over_top_right 1 1 0).
    zxsrw (Z_1_2_state_1 0).
    rewrite <- !zx_of_const_mult'.
    rewrite Cexp_0.
    rewrite zx_of_const_1' by C_field.
    zxscat.
  - pose proof (Z_state_copy 0 2 PI eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l, Cexp_0, Cexp_PI in Hrw.
    zxsrw (to_gadget Hrw).
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxfcat|].
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
Qed.

Lemma JPV_2_18_b : (Z 0 1 0 ⟷ X 1 0 0) ↕
  ((— ↕ Z 1 2 0) ⟷ ((X 2 1 0 ⟷ zx_triangle) ↕
  zx_triangle) ⟷ Z 2 1 0) ∝=
  zx_triangle ↕ zx_triangle ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose.
  rewrite gadget_is_scaled_empty.
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  destruct b.
  - pose proof (Z_state_copy 0 2 0 eq_refl eq_refl) as Hrw.
    rewrite Rmult_0_l, Cexp_0 in Hrw.
    zxsrw (to_gadget Hrw).
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1'; [zxfcat|].
    cbn.
    autorewrite with RtoC_db.
    C_field; lca.
  - zxsrw (@X_1_n_state_0 2 0).
    rewrite <- cap_X.
    zxsrw <- (Z_wrap_over_top_right 1 1 0).
    zxsrw (Z_1_2_state_0 0).
    rewrite <- !zx_of_const_mult'.
    rewrite zx_of_const_1' by C_field.
    zxscat.
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

Lemma wrap_otl_otr {n m o} (zx : ZX n (m + o)) :
  wrap_otl (wrap_otr zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r_fwd, stack_assoc_back_fwd, cast_contract_eq', n_wire_stack.

  unshelve erewrite (cast_compose_mid_distribute (m + m + (m + o))); [lia|].
  rewrite <- compose_assoc.
  rewrite cast_contract_eq'.
  rewrite cast_id.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_l, nwire_removal_r.
  rewrite push_out_top.
  rewrite <- (nwire_removal_r zx) at 2.
  rewrite compose_assoc.
  Morphisms.f_equiv.
  rewrite <- n_wire_stack.
  rewrite stack_assoc_back_fwd.
  rewrite (stack_assoc_back_fwd (n_wire m) (n_cup m) (n_wire o)).
  rewrite cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_l, <- stack_nwire_distribute_r.
  rewrite <- cast_stack_l.
  Morphisms.f_equiv.
  rewrite cast_id.
  apply big_yank_l.
  Unshelve.
  all: lia.
Qed.

Lemma wrap_otr_otl {n m o} (zx : ZX (n + m) o) :
  wrap_otr (wrap_otl zx) ∝= zx.
Proof.
  unfold wrap_otl, wrap_otr.
  rewrite stack_nwire_distribute_l.
  rewrite cast_stack_r_fwd, stack_assoc_back_fwd, cast_contract_eq', n_wire_stack.
  unshelve erewrite (cast_compose_mid_distribute (n + n + (n + m))); [lia|].
  rewrite compose_assoc.
  rewrite cast_contract_eq'.
  rewrite cast_id.
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_l, nwire_removal_r.
  rewrite pull_out_top.
  rewrite <- (nwire_removal_l zx) at 2.
  rewrite <- compose_assoc.
  Morphisms.f_equiv.
  rewrite <- n_wire_stack.
  rewrite stack_assoc_back_fwd.
  rewrite (stack_assoc_back_fwd (n_wire n) (n_cap n) (n_wire m)).
  rewrite cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  cbn [Nat.add].
  rewrite <- cast_stack_l, <- stack_nwire_distribute_r.
  rewrite <- cast_stack_l.
  Morphisms.f_equiv.

  rewrite big_yank_r.
  rewrite cast_contract_eq', cast_id.
  reflexivity.
  Unshelve.
  all: lia.
Qed.



Lemma wrap_ubl_ubr {n m o} (zx : ZX n (m + o)) :
  wrap_ubl (wrap_ubr zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite cast_stack_l_fwd, stack_assoc_fwd, n_wire_stack.
  rewrite <- compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
  unshelve erewrite push_out_bot, (cast_compose_mid_distribute (m + o)); [lia..|].
  rewrite cast_contract_eq', cast_id.
  rewrite compose_assoc.
  rewrite <- (nwire_removal_r zx) at 2.
  Morphisms.f_equiv.

  rewrite <- n_wire_stack.
  rewrite 2 stack_assoc_fwd.
  rewrite 2 cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_r, <- stack_nwire_distribute_l.
  rewrite <- cast_stack_r.
  Morphisms.f_equiv.
  rewrite big_yank_r.
  rewrite cast_contract_eq', cast_id.
  reflexivity.
  Unshelve.
  all: lia.
Qed.


Lemma wrap_ubr_ubl {n m o} (zx : ZX (n + m) o) :
  wrap_ubr (wrap_ubl zx) ∝= zx.
Proof.
  unfold wrap_ubl, wrap_ubr.
  rewrite stack_nwire_distribute_r.
  rewrite cast_stack_l_fwd, (stack_assoc_fwd zx), n_wire_stack.

  rewrite compose_assoc.
  rewrite cast_compose_eq_mid_join.
  rewrite <- stack_compose_distr, nwire_removal_l, nwire_removal_r.
  unshelve erewrite pull_out_bot, (cast_compose_mid_distribute (n + m)); [lia..|].
  rewrite cast_contract_eq', cast_id.
  rewrite <- compose_assoc.
  rewrite <- (nwire_removal_l zx) at 2.
  Morphisms.f_equiv.

  rewrite <- n_wire_stack.
  rewrite 2 stack_assoc_fwd.
  rewrite 2 cast_contract_eq'.
  rewrite cast_compose_l, cast_contract_eq'.
  rewrite <- cast_stack_r, <- stack_nwire_distribute_l.
  rewrite <- cast_stack_r.
  Morphisms.f_equiv.
  rewrite big_yank_l.
  rewrite cast_id.
  reflexivity.
  Unshelve.
  all: lia.
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
  rewrite stack_assoc_back_fwd, cast_contract_eq'.
  rewrite cast_compose_r_eq_mid.
  rewrite <- stack_compose_distr.
  cast_irrelevance.
  now rewrite nwire_removal_l.
Qed.

Lemma wrap_otr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_otr (zx0 ↕ zx1) ∝=
  cast _ _ (Nat.add_assoc _ _ _) eq_refl ((n_wire m ↕ zx0 ⟷ n_cup m) ↕ zx1).
Proof.
  unfold wrap_otr.
  rewrite stack_assoc_back_fwd, cast_contract_eq'.
  rewrite cast_compose_l_eq_mid.
  rewrite <- stack_compose_distr.
  cast_irrelevance.
  now rewrite nwire_removal_r.
Qed.


Lemma wrap_ubl_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubl (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_0_r _)) (eq_sym (Nat.add_assoc _ _ _))
    (zx0 ↕ (n_cap o ⟷ (zx1 ↕ n_wire o))).
Proof.
  unfold wrap_ubl.
  rewrite stack_assoc_fwd.
  rewrite cast_compose_eq_mid_join.
  cast_irrelevance.
  now rewrite <- stack_compose_distr, nwire_removal_l.
Qed.

Lemma wrap_ubr_stack {n m o p} (zx0 : ZX n m) (zx1 : ZX o p) :
  wrap_ubr (zx0 ↕ zx1) ∝=
  cast _ _ (eq_sym (Nat.add_assoc _ _ _)) (eq_sym (Nat.add_0_r _))
    (zx0 ↕ (zx1 ↕ n_wire p ⟷ n_cup p)).
Proof.
  unfold wrap_ubr.
  rewrite stack_assoc_fwd, cast_compose_eq_mid_join.
  cast_irrelevance.
  rewrite <- stack_compose_distr, nwire_removal_r.
  reflexivity.
Qed.



Lemma wrap_otl_transpose {n m o} zx :
	(@wrap_otl n m o zx) ⊤ ∝= wrap_otr (zx ⊤).
Proof.
	unfold wrap_otl, wrap_otr.
	cbn [transpose].
	rewrite n_cap_transpose, cast_transpose.
	cbn [transpose].
	now rewrite !n_wire_transpose.
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
	cbn [transpose].
	rewrite cast_transpose.
	cbn [transpose].
	rewrite n_cap_transpose.
	now rewrite !n_wire_transpose.
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
  rewrite state_plus_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.
Lemma fold_state_minus : Z 0 1 PI ∝= √ 2 .* state_minus.
Proof.
  rewrite state_minus_defn, zx_scale_assoc.
  rewrite zx_scale_eq_1_l by C_field.
  done.
Qed.

Lemma JPV_2_19 : (— ↕ (Z 1 2 0 ⟷ (zx_triangle ↕ zx_triangle_left))) ⟷
  (X 2 1 PI ↕ —) ⟷ Z 2 1 0 ∝=
  ((Z 1 2 0 ⟷ (zx_triangle_left ↕ zx_triangle)) ↕ —) ⟷
  (— ↕ X 2 1 PI) ⟷ Z 2 1 0.
Proof.
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_transpose, triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1, 2 stack_empty_l.
  zxsrw (triangle_state_b b).
  zxsrw (@X_1_n_state_b 2 PI b).
  zxsrw (@X_1_n_state_b 2 PI b).
  zxsrw (triangle_state_b b).
  apply (@wrap_over_top_right 0 1 1).
  unfold wrap_otr.
  zxsrw <- (X_wrap_over_top_left 0 1 (if b then (PI + PI)%R else PI)).
  zxaclean_rhs.
  destruct b.
  - rewrite X_eq_2_PI by lra.
    rewrite (X_eq_2_PI 0 2) by lra.
    rewrite <- cap_X.
    apply transpose_diagrams_eq.
    cbn [transpose].
    autorewrite with transpose_db.
    rewrite (zx_comm_transpose 2 1).
    rewrite ?zx_of_const_transpose.
    apply prop_eq_by_eq_on_state_b_1_n.
    intros b.
    zxsrw (Z_1_2_state_b 0 b).
    zxaclean_rhs.
    zxsrw_rhs (cup_pullthrough_top (state_1 ⊤) —).
    rewrite transpose_involutive.
    zxfclean_rhs.
    zxsrw (Z_1_2_state_1 0).
    rewrite Cexp_0, zx_of_const_1.
    zxsrw triangle_state_1.
    zxsrw (cap_pullthrough_top state_1 (state_b b)).
    zxsrw_rhs (state_b_state_b_transpose b true).
    zxsrw (state_b_state_b_transpose b true).
    rewrite <- !zx_of_const_mult'.
    zxsrw (triangle_state_b b).
    destruct b; [rewrite Cmult_1_r; done|].
    cbn.
    rewrite 2 Cmult_0_l, zx_of_const_0, ? stack_0_l.
    done.
  - rewrite X_0_2_PI_to_cup_not.
    apply transpose_diagrams_eq.
    cbn [transpose].
    autorewrite with transpose_db.
    rewrite (zx_comm_transpose 2 1).
    rewrite ?zx_of_const_transpose.
    apply prop_eq_by_eq_on_state_b_1_n.
    intros b.
    zxsrw (Z_1_2_state_b 0 b).
    zxaclean_rhs.
    rewrite <- not_defn.
    zxarw (not_state_b b).
    zxfclean_rhs.
    zxarw (cap_pullthrough_top (state_b (¬ b)) —).
    zxarw <- (n_cap_pullthrough_bot (state_b (¬ b))).
    rewrite (cup_pullthrough_top_1 zx_triangle —).
    rewrite triangle_transpose.
    zxaclean_rhs.
    rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
    rewrite (left_triangle_state_b (¬ b)).
    zxsrw (triangle_state_b b).
    f_equiv.
    zxsrw (Z_1_n_state_b b 0 0).
    rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
    destruct b.
    + cbn.
      rewrite not_state_1.
      zxscat.
    + cbn.
      rewrite fold_state_plus.
      zxsrw not_state_plus.
      zxscat.
Qed.

(* FIXME: Move *)
Lemma zx_invsqrt2_to_const :
  zx_invsqrt2 ∝= zx_of_const (/ √ 2).
Proof.
  apply const_of_zx_inj.
  rewrite const_of_zx_invsqrt2, const_of_zx_of_const.
  done.
Qed.

Lemma JPV_2_20 : (Z 0 1 0 ⟷ X 1 0 0) ↕ (Z 1 2 0 ⟷ (— ↕ zx_triangle_left) ⟷ X 2 1 0) ∝=
  zx_triangle_left.
Proof.
  rewrite gadget_is_scaled_empty.
  rewrite <- const_of_zx_colorswap.
  cbn [color_swap].
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_2_state_b 0 b).
  rewrite Cexp_0, Tauto.if_same, zx_of_const_1.
  zxsrw (left_triangle_state_b b).
  zxsrw (left_triangle_state_b b).
  rewrite state_b_defn'.
  zxsrw (dominated_X_spider_fusion_top_right 0 0 1 1 (if b then PI else 0) 0).
  rewrite Rplus_0_r.
  rewrite zx_invsqrt2_to_const, <- zx_of_const_mult'.
  rewrite zx_of_const_1' by C_field.
  destruct b.
  - rewrite <- not_defn, fold_state_plus.
    zxsrw not_state_plus.
    zxscat.
  - zxsrw (@X_1_n_state_0 1 0).
    rewrite state_0_defn.
    zxscat.
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
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_semantics.
  rewrite zx_scale_semantics.
  rewrite state_minus_semantics, state_0_semantics.
  by_cell; lca.
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
  prep_matrix_equivalence.
  rewrite zx_compose_spec.
  rewrite zx_triangle_left_semantics.
  rewrite zx_scale_semantics.
  rewrite state_minus_semantics, state_1_semantics.
  by_cell; lca.
Qed.


Lemma JPV_2_21 : zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI
  ∝= Z 1 1 PI ⟷ zx_triangle_left ⟷ Z 1 1 PI ⟷ zx_triangle_left.
Proof.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (left_triangle_state_b b).
  zxsrw (Z_1_n_state_b b 1 PI).
  rewrite Cexp_PI.
  zxsrw (left_triangle_state_b b).
  destruct b.
  - zxsrw (@Z_spider_1_1_fusion 0 1 0 PI).
    zxsrw (@Z_spider_1_1_fusion 0 1 0 PI).
    rewrite Rplus_0_l.
    rewrite fold_state_minus.
    zxsrw left_triangle_state_minus.
    zxsrw (Z_1_n_state1 1 PI).
    zxsrw left_triangle_state_minus.
    rewrite <- !zx_of_const_mult'.
    do 2 f_equiv.
    rewrite Cexp_PI.
    lca.
  - zxsrw (Z_1_n_state0 1 PI).
    zxsrw (Z_1_n_state0 1 PI).
    zxsrw left_triangle_state_0.
    zxsrw left_triangle_state_0.
    zxsrw (Z_1_n_state0 1 PI).
    rewrite zx_of_const_1.
    zxscat.
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
  rewrite Rplus_0_l.
  pose proof (f_equiv transpose JPV_2_7) as Hrw.
  cbn in Hrw.
  rewrite triangle_transpose in Hrw.
  zxsrw Hrw.
  clear Hrw.
  zxsrw (dominated_X_spider_fusion_top_left 0 0 1 1 0 β).
  zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 0 0 PI).
  rewrite 2 Rplus_0_l.
  zxsrw (gadget_is_scaled_empty (X 0 1 0 ⟷ Z 1 0 0)).
  rewrite const_of_zx_X_0_1_0_Z_1_0_0.
  rewrite <- zx_of_const_mult'.
  rewrite zx_of_const_1' by (autorewrite with RtoC_db; C_field; lca).
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
    rewrite Rplus_0_r.
    zxaclean_lhs.
    zxsrw <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxarw_rhs <- (X_wrap_under_bot_left  1 1 PI eq_refl eq_refl).
    zxsrw (@X_1_n_state_1 1 β).
    zxsrw (@X_spider_1_1_fusion 0 2 (PI + β) PI).
    rewrite (X_Rmodeq_2PI _ β) by (exists (1 : BinInt.Z); lra).
    zxsrw (@X_1_n_state_1 2 PI).
    rewrite (X_eq_2_PI _ _ (_ + _)) by lra.
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
    rewrite Rplus_0_r.
    zxsrw (dominated_Z_spider_fusion_top_left 0 0 1 1 0 0).
    rewrite Rplus_0_r.
    zxsrw (Z_1_2_state_0 0).
    zxarw_rhs <- (X_wrap_under_bot_left 1 1 PI eq_refl eq_refl).
    zxsrw (to_gadget (Z_state_copy' false 2 PI eq_refl eq_refl)).
    symmetry.
    rewrite (f_equal zx_of_const (y:=/√2)) by
      (cbn; C_field; lca).
    zxsrw (dominated_Z_spider_fusion_top_right 0 0 1 0 0 0).
    rewrite Rplus_0_r.
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
  transitivity (X 1 1 PI ⟷ Z 1 2 0 ⟷ ((zx_triangle_left ⟷ Z 1 2 PI) ↕ —) ⟷
    (— ↕ X 2 1 0)). 1:{
    zxsrw (to_gadget (X_state_copy'' false 2 PI eq_refl eq_refl)).
    zxsrw JPV_2_7.
    zxsrw (to_const (Z 0 1 0 ⟷ X 1 0 0)).
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1' by (C_field; lca).
    zxsrw (dominated_Z_spider_fusion_bot_right 0 0 1 2 0 PI).
    rewrite Rplus_0_l.
    zxsrw (dominated_X_spider_fusion_bot_right 0 0 1 1 0 0).
    rewrite Rplus_0_r.
    rewrite X_0_is_wire.
    zxfcat.
  }
  transitivity (Z 1 2 PI ⟷ (— ↕ (zx_triangle ⟷ Z 1 2 PI)) ⟷
    (X 2 1 0 ↕ X 1 1 PI)). 2:{
    zxsrw (to_gadget (X_state_copy'' true 2 PI eq_refl eq_refl)).
    zxsrw JPV_2_10.
    zxsrw (to_const (Z 0 1 0 ⟷ X 1 0 0)).
    rewrite <- const_of_zx_colorswap.
    cbn [color_swap].
    rewrite const_of_zx_X_0_1_0_Z_1_0_0.
    rewrite <- zx_of_const_mult'.
    rewrite Cexp_PI'.
    zxsrw (dominated_Z_spider_fusion_bot_right 0 0 1 2 0 PI).
    rewrite Rplus_0_l.
    zxsrw (dominated_X_spider_fusion_bot_right 0 0 1 1 PI 0).
    rewrite Rplus_0_r.
    rewrite <- zx_of_const_mult'.
    rewrite zx_of_const_1' by (C_field; lca).
    zxscat.
  }
  transitivity (Z 1 2 0 ⟷ (— ↕ (zx_triangle ⟷ Z 1 2 0)) ⟷
    ((X 2 1 0 ⟷ Z 1 1 PI) ↕ X 1 1 PI)). 2:{
    symmetry.
    rewrite <- (Rplus_0_r PI).
    rewrite <- (@dominated_Z_spider_fusion_top_left 1 0 1 1).
    rewrite Rplus_0_r.
    cbn.
    rewrite (X_wrap_over_top_left 1 1 0) at 1.
    zxsrw JPV_2_6.

    zxsrw (dominated_Z_spider_fusion_top_right 1 0 1 0 PI 0).
    zxsrw (dominated_Z_spider_fusion_bot_right 1 0 1 0 PI (PI + 0)).
    rewrite (Z_eq_2_PI 2 0 (PI + _)) by lra.
    zxsrw <- (X_wrap_over_top_left 1 1 0).
    zxscat.
  }
  transitivity (X 1 1 PI ⟷ Z 1 2 0 ⟷
    (— ↕ (zx_triangle_left ⟷ Z 1 2 0)) ⟷
    ((X 2 1 0 ⟷ Z 1 1 PI) ↕ —)). 2:{
    symmetry.
    rewrite (Z_wrap_over_top_right 1 1 0) at 2.

    pose proof JPV_2_6 as Hrw.
    apply (f_equiv (color_swap ∘ transpose)%prg) in Hrw.
    cbn in Hrw.
    zxsrw Hrw.
    clear Hrw.
    zxsrw <- JPV_2_11.

    zxsrw (cup_pullthrough_bot_1 (X 1 1 PI) —).
    zxsrw (dominated_X_spider_fusion_bot_right 1 0 1 1 PI 0).
    zxsrw <- (dominated_X_spider_fusion_top_right 1 0 1 1 PI 0).
    zxsrw <- (f_equiv color_swap JPV_2_6).
    zxfcat.
  }
  zxsrw notc_is_notc_r.
  zxsrw <- JPV_2_12.
  zxsrw <- cnot_is_cnot_r.
  zxfcat.
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
  apply transpose_diagrams_eq.
  cbn.
  rewrite triangle_left_transpose.
  apply prop_eq_by_eq_on_state_b_1_n.
  intros b.
  zxsrw (Z_1_n_state_b b 2 0).
  rewrite Cexp_0.
  rewrite zx_of_const_1' by now destruct b.
  zxsrw (triangle_state_b b).
  zxarw (cap_pullthrough_bot (state_b b) —).
  rewrite <- gadget_transpose.
  cbn.
  rewrite transpose_involutive_eq.
  zxsrw (Z_1_n_state_b b 0 0).
  rewrite Cexp_0.
  rewrite zx_of_const_1' by now destruct b.


  destruct b.
  - cbn.
    rewrite (state_b_state_b_transpose true true).
    cbn.
    rewrite zx_scale_1_l.
    done.
  - cbn.
    zxsrw (Z_1_n_state0 0 0).
    done.
Qed.



Lemma JPV_2_22 n :
  Z 0 1 0 ↕ Z 0 1 0 ↕ n_wire n ⟷ JPV_2_22_lhs_aux n ∝=
  (⊂ ⟷ (zx_triangle_left ↕ —)) ↕ n_wire n ⟷ JPV_2_22_lhs_aux n.
Proof.
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
  zxfclean.


(* Lemma JPV_2_26 *)