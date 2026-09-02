From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.












(* Print Instances LawfulStructGraphable. *)














Lemma n_wire_removal_l' {n n' n'' m} (zx : ZX n'' m) prfn' prfn'' :
  cast n' n'' prfn' prfn'' (n_wire n) ⟷ zx ∝= cast _ _ (eq_trans_r prfn' prfn'') eq_refl zx.
Proof.
  subst.
  rewrite 2 CastRules.cast_id.
  now rewrite nwire_removal_l.
Qed.

Lemma n_wire_removal_r' {n m m' m''} (zx : ZX n m') prfm' prfm'' :
  zx ⟷ cast m' m'' prfm' prfm'' (n_wire m) ∝= cast _ _ eq_refl (eq_trans_r prfm'' prfm') zx.
Proof.
  subst.
  rewrite 2 CastRules.cast_id.
  now rewrite nwire_removal_r.
Qed.


(* FIXME: Move *)
Lemma zx_of_const_mult' (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ⟷ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm, compose_empty_r.
  done.
Qed.


(* FIXME: Move *)
Lemma empty_zxperm_empty {n m} (Hn : n = O) (Hm : m = O)
  (zx : ZX n m) : ZXperm zx ->
  zx ∝= cast n m Hn Hm ⦰.
Proof.
  intros Hzx.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  subst.
  easy.
Qed.


Fixpoint zx_mul_S_r n m : ZX (n * S m) (n + n * m) :=
  match n with
  | 0 => ⦰
  | S n =>
    n_wire (S m) ↕ zx_mul_S_r n m ⟷ zx_mid_comm 1 m n (n * m)
  end.

Fixpoint zx_mul_comm n m : ZX (n * m) (m * n) :=
  match m with
  | 0 => cast _ _ (Nat.mul_0_r n) eq_refl ⦰
  | S m =>
    zx_mul_S_r n m ⟷
    (n_wire n ↕ zx_mul_comm n m)
  end.

Lemma zx_mul_S_r_zxperm n m : ZXperm (zx_mul_S_r n m).
Proof.
  induction n; cbn -[Nat.add]; [auto_zxperm|].
  constructor; [auto_zxperm|].
  apply (zx_mid_comm_zxperm 1).
Qed.

#[export] Hint Resolve zx_mul_S_r_zxperm : zxperm_db.

Lemma zx_mul_comm_zxperm n m : ZXperm (zx_mul_comm n m).
Proof.
  induction m; cbn; auto_zxperm.
Qed.

#[export] Hint Resolve zx_mul_comm_zxperm : zxperm_db.


Lemma perm_of_zx_mul_S_r n m : perm_eq (n * S m)
  (perm_of_zx (zx_mul_S_r n m))
  (λ i, if i <? n then (S m) * i else
    let i' := i - n in
    S m * (i' / m) + S (i' mod m))%nat.
Proof.

  induction n; [hnf; lia|].
  cbn -[Nat.div Nat.modulo Nat.add n_wire].
  rewrite IHn.
  rewrite perm_of_n_wire.
  rewrite (perm_of_zx_mid_comm 1 m n).
  rewrite stack_perms_defn.
  rewrite (Nat.add_comm m n).
  rewrite big_swap_perm_defn.
  rewrite (Nat.add_comm n m).
  rewrite (stack_perms_defn _ _ idn).
  intros i Hi.
  unfold compose.
  rewrite stack_perms_defn by lia.
  bdestruct (i <? 1 + m + n).
  - bdestruct (i <? 1). 1:{
      replace i with O by lia.
      rewrite 2 Nat.Div0.mod_0_l.
      bdestructΩ'.
    }
    bdestruct (i - 1 <? n).
    + bdestruct_one; [lia|].
      bdestruct_one; [|lia].
      bdestruct_one; [|lia].
      nia.
    + bdestruct_one; [|lia].
      bdestruct_one; [lia|].
      rewrite Nat.div_small by lia.
      rewrite Nat.mod_small by lia.
      lia.
  - bdestruct_one; [lia|].
    bdestruct_one; [lia|].
    bdestruct_one; [lia|].
    rewrite Nat.sub_add by lia.
    replace (i - S n)%nat with (1 * m + (i - S n - m))%nat by lia.
    rewrite Nat.div_add_l by lia.
    rewrite mod_add_l by lia.
    replace (i - S m - n)%nat with (i - S n - m)%nat by lia.
    lia.
Qed.


Lemma perm_of_zx_mul_comm n m : (perm_of_zx (zx_mul_comm n m)) =
  (kron_comm_perm n m).
Proof.
  eq_by_WF_perm_eq (n * m)%nat.
  induction m.
  - intros i Hi; lia.
  - cbn.
    rewrite perm_of_zx_mul_S_r.
    rewrite IHm, perm_of_n_wire.
    rewrite 2 kron_comm_perm_defn.
    intros i Hi.
    unfold stack_perms, compose.
    bdestruct (i <? n + n * m); [|lia].
    bdestruct (i <? n).
    + bdestruct_one; [|lia].
      rewrite Nat.mod_small, Nat.div_small; lia.
    + bdestruct_one; [lia|].
      rewrite Nat.add_sub.
      rewrite Nat.div_add_l by lia.
      rewrite mod_add_l.
      rewrite (Nat.div_small (_ / _)), (Nat.mod_small (_ / _)) by
        (apply Nat.div_lt_upper_bound; lia).
      rewrite div_sub_one_r.
      replace (i - n)%nat with (i - 1 * n)%nat by lia.
      rewrite sub_mul_mod by lia.
      assert (i / n <> 0)%nat by (rewrite Nat.div_small_iff; lia).
      lia.
Qed.



Import vector.

(* FIXME: Move *)
Lemma tensor_of_matrix_inj' {n m} (A B : Matrix (2^m) (2^n)) :
  tensor_of_matrix A ≡ tensor_of_matrix B ->
  A ≡ B.
Proof.
  intros HAB.
  rewrite <- matrix_of_tensor_of_matrix.
  rewrite HAB.
  rewrite matrix_of_tensor_of_matrix.
  reflexivity.
Qed.

#[export] Instance nat_fun_to_fin_perm_proper n m :
  Proper (perm_eq n ==> equiv) (nat_fun_to_fin_perm n m).
Proof.
  intros f f' Hf.
  unfold nat_fun_to_fin_perm.
  f_equiv.
  f_equiv.
  f_equiv.
  intros i.
  now rewrite Hf by apply fin_to_nat_lt.
Qed.




Fixpoint fin_perm_of_zx {n m} (zx : ZX n m) : option (fin n -> fin m) :=
  match zx with
  | ⦰ => Some (λ i, i)
  | — => Some (λ i, i)
  | ⨉ => Some (@fin_add_comm 1 1)
  | zx ↕ zx' =>
    omap2 fin_perm_stack (fin_perm_of_zx zx) (fin_perm_of_zx zx')
  | zx ⟷ zx' =>
    omap2 (λ f g i, g (f i)) (fin_perm_of_zx zx) (fin_perm_of_zx zx')
  | ⊂ | ⊃ | Z _ _ _ | X _ _ _ | Box => None
  end.

Lemma fin_perm_of_zx_is_Some {n m} (zx : ZX n m) :
  is_Some (fin_perm_of_zx zx) <-> ZXperm zx.
Proof.
  split.
  - induction zx; cbn; try solve [intros [_ [=]]]; [auto_zxperm..| |].
    + rewrite omap2_is_Some.
      intros []; auto_zxperm.
    + rewrite omap2_is_Some.
      intros []; auto_zxperm.
  - intros Hzx.
    induction Hzx; [done..| |].
    + cbn.
      rewrite omap2_is_Some; done.
    + cbn.
      rewrite omap2_is_Some; done.
Qed.

Lemma ZX_tensor_semantics_zxperm_aux {n m} (zx : ZX n m)
  : forall (H : is_Some (fin_perm_of_zx zx)),
  ZX_tensor_semantics zx ≡
  perm_tensor (is_Some_proj H).
Proof.
  intros H.
  apply fin_perm_of_zx_is_Some in H as Hzx.
  revert H.
  induction Hzx; intros ?.
  - cbn.
    now rewrite perm_tensor_id' by done.
  - cbn.
    now rewrite perm_tensor_id' by done.
  - cbn.
    rewrite swap_tensor_perm_tensor.
    done.
  - cbn -[fin_perm_of_zx].
    apply fin_perm_of_zx_is_Some in Hzx1, Hzx2.
    erewrite stack_tensor_mor by (unshelve eauto; eauto).
    destruct (fin_perm_of_zx (zx0 ↕ zx1)) as [p_p|] eqn:Hp_p; [|now destruct H as [_ [=]]].
    cbn.
    cbn in Hp_p.
    apply omap2_Some in Hp_p as (p & p' & Hp & Hp' & <-).
    revert Hzx1 Hzx2.
    rewrite Hp, Hp'.
    intros ? ?.
    cbn.
    rewrite perm_tensor_stack.
    done.
  - cbn -[fin_perm_of_zx].
    apply fin_perm_of_zx_is_Some in Hzx1, Hzx2.
    erewrite compose_tensor_mor by (unshelve eauto; eauto).
    destruct (fin_perm_of_zx (zx0 ⟷ zx1)) as [p_p|] eqn:Hp_p; [|now destruct H as [_ [=]]].
    cbn.
    cbn in Hp_p.
    apply omap2_Some in Hp_p as (p & p' & Hp & Hp' & <-).
    revert Hzx1 Hzx2.
    rewrite Hp, Hp'.
    intros ? ?.
    cbn.
    rewrite perm_tensor_compose.
    done.
Qed.


Lemma fin_perm_of_n_wire n : fin_perm_of_zx (n_wire n) ≡ Some (λ i, i).
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  cbn.
  f_equiv.
  rewrite fin_perm_stack_id.
  done.
Qed.


Lemma fin_perm_of_zx_cast {n m n' m'} (Hn : n' = n) (Hm : m' = m)
  (zx : ZX n m) : fin_perm_of_zx (cast _ _ Hn Hm zx) =
    cast_fin_perm (eq_sym Hn) (eq_sym Hm) <$> fin_perm_of_zx zx.
Proof.
  subst.
  rewrite cast_id_eq.
  destruct (fin_perm_of_zx zx); [|done].
  cbn.
  now rewrite cast_fin_perm_refl.
Qed.


Lemma nat_fun_to_fin_perm_of_perm_bounded (n m : nat) (f : nat -> nat)
  (Hf : forall i, i < n -> f i < m) :
  nat_fun_to_fin_perm n m f =
  Some (fun_to_vec (λ i, nat_to_fin (Hf i (fin_to_nat_lt i)))!!!.).
Proof.
  unfold nat_fun_to_fin_perm.
  rewrite fmap_Some.
  exists (fun_to_vec (λ i, nat_to_fin (Hf i (fin_to_nat_lt i)))).
  split; [|done].
  apply vec_join_Some.
  apply vec_eq.
  intros i.
  rewrite vlookup_map, 2 lookup_fun_to_vec.
  rewrite <- nat_to_ofin_fin.
  now rewrite fin_to_nat_to_fin.
Qed.


Lemma nat_fun_to_fin_perm_stack_perms_bounded_square
  (n m : nat) (f : nat -> nat) (g : nat -> nat) :
  perm_bounded n f -> perm_bounded m g ->
  nat_fun_to_fin_perm (n + m) (n + m) (stack_perms n m f g) ≡
  omap2 fin_perm_stack (nat_fun_to_fin_perm n n f) (nat_fun_to_fin_perm m m g).
Proof.
  intros Hf Hg.
  rewrite (nat_fun_to_fin_perm_of_perm_bounded n n f Hf).
  rewrite (nat_fun_to_fin_perm_of_perm_bounded m m g Hg).
  cbn.
  assert (Hfg : perm_bounded (n + m) (stack_perms n m f g)) by auto_perm.
  rewrite (nat_fun_to_fin_perm_of_perm_bounded _ _ _ Hfg).
  f_equiv.
  intros i.
  rewrite fun_to_vec_plus.
  induction i using fin_add_inv.
  - rewrite lookup_vapp_L, fin_perm_stack_L.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_L, 2 fin_to_nat_to_fin, fin_to_nat_L.
    unfold stack_perms.
    pose proof (fin_to_nat_lt i).
    bdestruct_one; [|lia].
    done.
  - rewrite lookup_vapp_R, fin_perm_stack_R.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_R, 2 fin_to_nat_to_fin, fin_to_nat_R.
    unfold stack_perms.
    pose proof (fin_to_nat_lt i).
    bdestructΩ'.
    rewrite add_sub'.
    lia.
Qed.

Lemma nat_fun_to_fin_perm_compose_bounded_square
  (n : nat) (f : nat -> nat) (g : nat -> nat) :
  perm_bounded n f -> perm_bounded n g ->
  nat_fun_to_fin_perm n n (g ∘ f) ≡
  omap2 (λ f g, λ i, g (f i))
    (nat_fun_to_fin_perm n n f) (nat_fun_to_fin_perm n n g).
Proof.
  intros Hf Hg.
  rewrite (nat_fun_to_fin_perm_of_perm_bounded n n f Hf).
  rewrite (nat_fun_to_fin_perm_of_perm_bounded n n g Hg).
  cbn.
  assert (Hfg : perm_bounded n (g ∘ f)) by auto_perm.
  rewrite (nat_fun_to_fin_perm_of_perm_bounded _ _ _ Hfg).
  f_equiv.
  intros i.
  rewrite 3 lookup_fun_to_vec.
  apply fin_to_nat_inj.
  rewrite 3 fin_to_nat_to_fin.
  done.
Qed.

Import finite.

Lemma fin_inj_to_nat_inj_permutation {n m}
  (f : fin n -> fin m) {Hf : Inj eq eq f} (Hnm : n = m) :
  permutation n (fin_inj_to_nat_inj f).
Proof.
  subst m.
  apply permutation_iff_surjective.
  intros i Hi.
  apply finite_inj_surj in Hf as Hf'; [|done].
  specialize (Hf' (nat_to_fin Hi)) as (j & Hj).
  exists j.
  split; [apply fin_to_nat_lt|].
  now rewrite fin_inj_to_nat_inj_fin, Hj, fin_to_nat_to_fin.
Qed.

#[export] Hint Resolve fin_inj_to_nat_inj_permutation : perm_db.

Lemma fin_inj_to_nat_inj_perm_bounded {n m}
  (f : fin n -> fin m) (Hnm : m <= n) :
  perm_bounded n (fin_inj_to_nat_inj f).
Proof.
  intros i Hi.
  rewrite <- (fin_to_nat_to_fin _ _ Hi).
  rewrite fin_inj_to_nat_inj_fin.
  pose proof (fin_to_nat_lt (f (nat_to_fin Hi))).
  lia.
Qed.

#[export] Hint Resolve fin_inj_to_nat_inj_perm_bounded : perm_bounded_db.


Lemma perm_inv_fin_inj_to_nat_inj {n}
  (f : fin n -> fin n) {Hf : Inj eq eq f} :
  perm_eq n (perm_inv n (fin_inj_to_nat_inj f)) (fin_inj_to_nat_inj (fin_perm_inv f)).
Proof.
  refine (nat_lt_ind _ _).
  intros i.
  rewrite fin_inj_to_nat_inj_fin.
  apply perm_inv_eq_iff; [auto_perm|apply fin_to_nat_lt..|].
  rewrite fin_inj_to_nat_inj_fin.
  rewrite (fin_perm_inv_rinv f Hf).
  done.
Qed.



Lemma matrix_of_tensor_perm_tensor {n m}
  (f : fin n -> fin m) {Hf : Inj eq eq f} (Hnm : n = m) :
  matrix_of_tensor (perm_tensor f) =
  perm_to_matrix n (perm_inv n $ fin_inj_to_nat_inj f).
Proof.
  subst m.
  prep_matrix_equivalence.
  rewrite (perm_inv_fin_inj_to_nat_inj f).
  unfold matrix_of_tensor.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  unfold matrix_of_tensor.
  unfold perm_to_matrix.
  unfold perm_mat.
  rewrite qubit_perm_to_nat_perm_defn by done.
  bdestruct (i <? 2 ^ n); [|lia].
  bdestruct (j <? 2 ^ n); [|lia].
  rewrite 2 andb_true_r.
  cbn.
  rewrite decide_bool_decide.
  apply f_equal_if; [|done..].
  apply Bool.eq_iff_eq_true.
  rewrite bool_decide_eq_true, Nat.eqb_eq.
  rewrite <- (nat_to_bits_inj n) by first [done|apply funbool_to_nat_bound].
  split.
  - intros Hjeq.
    apply vec_eq.
    intros b.
    rewrite 2 nth_nat_to_bits.
    rewrite testbit_funbool_to_nat.
    pose proof (fin_to_nat_lt b).
    bdestruct_one; [|lia].
    rewrite sub_S_sub_S by done.
    cbn.
    rewrite fin_inj_to_nat_inj_fin.
    rewrite nat_to_funbool_eq'.
    pose proof (fin_to_nat_lt (fin_perm_inv f b)).
    bdestruct_one; [|lia].
    apply (f_equal (.!!!fin_perm_inv f b)) in Hjeq.
    rewrite nth_nat_to_bits in Hjeq.
    rewrite Hjeq.
    rewrite lookup_permute_vec.
    cbn.
    rewrite nth_nat_to_bits.
    rewrite (fin_perm_inv_rinv f Hf).
    done.
  - intros Hieq.
    apply vec_eq.
    intros b.
    pose proof (fin_to_nat_lt b).
    rewrite nth_nat_to_bits.
    rewrite lookup_permute_vec.
    cbn.
    rewrite nth_nat_to_bits.
    apply (f_equal (.!!!f b)) in Hieq.
    rewrite nth_nat_to_bits in Hieq.
    rewrite Hieq.
    rewrite nth_nat_to_bits.
    rewrite testbit_funbool_to_nat.
    bdestruct_one; [|lia].
    rewrite sub_S_sub_S by (apply fin_to_nat_lt).
    cbn.
    rewrite fin_inj_to_nat_inj_fin, (fin_perm_inv_linv f Hf).
    rewrite nat_to_funbool_eq'.
    bdestruct_one; lia.
Qed.




Import Aux.

Lemma fin_perm_of_zx_by_perm_of_zx {n m} (zx : ZX n m) (Hzx : ZXperm zx) :
  fin_perm_of_zx zx ≡ nat_fun_to_fin_perm n m (perm_inv n $ perm_of_zx zx).
Proof.
  induction Hzx using zxperm_square_induction.
  - cbn.
    f_equiv.
    intros i; inv_all_vec_fin.
  - cbn.
    vm_eval (nat_to_ofin 1 0).
    cbn.
    f_equiv.
    intros i; inv_all_vec_fin; done.
  - cbn.
    vm_eval (nat_to_ofin _ _).
    vm_eval (nat_to_ofin _ _).
    cbn.
    f_equiv.
    intros i; inv_all_vec_fin; done.
  - cbn.
    rewrite perm_inv_stack_perms by auto_perm.
    rewrite nat_fun_to_fin_perm_stack_perms_bounded_square by auto_perm.
    f_equiv; done.
  - cbn.
    rewrite perm_inv_compose by auto_perm.
    rewrite nat_fun_to_fin_perm_compose_bounded_square by auto_perm.
    f_equiv; done.
Qed.


Lemma fin_perm_of_zx_comm n m : fin_perm_of_zx (zx_comm n m) ≡ Some fin_add_comm.
Proof.
  rewrite fin_perm_of_zx_by_perm_of_zx by auto_zxperm.
  assert (Hbnd : forall i, i < n + m ->
    perm_inv (n + m) (perm_of_zx (zx_comm n m)) i < m + n). 1:{
    intros i Hi.
    rewrite (Nat.add_comm m n).
    auto_perm.
  }
  rewrite (nat_fun_to_fin_perm_of_perm_bounded _ _ _ Hbnd).
  f_equiv.
  intros i.
  rewrite lookup_fun_to_vec.
  apply fin_to_nat_inj.
  rewrite fin_to_nat_to_fin.
  rewrite perm_of_zx_comm.
  pose proof (fin_to_nat_lt i).
  rewrite (Nat.add_comm n m) at 1.
  rewrite big_swap_perm_inv by lia.
  induction i as [i|i] using fin_add_inv; pose proof (fin_to_nat_lt i).
  - rewrite fin_add_comm_L, fin_to_nat_L, fin_to_nat_R.
    rewrite big_swap_perm_left; lia.
  - rewrite fin_add_comm_R, fin_to_nat_R, fin_to_nat_L.
    rewrite big_swap_perm_right; lia.
Qed.

Lemma fin_perm_of_zx_mid_comm n m o p
  : fin_perm_of_zx (zx_mid_comm n m o p) ≡ Some fin_mid_comm.
Proof.
  unfold zx_mid_comm.
  rewrite fin_perm_of_zx_cast.
  cbn.
  rewrite 2 fin_perm_of_n_wire, fin_perm_of_zx_comm.
  cbn.
  f_equiv.
  intros i.
  unfold fin_mid_comm.
  cbn.
  rewrite cast_fin_perm_apply.
  induction i as [i|i] using fin_add_inv;
  induction i as [i|i] using fin_add_inv;
  rewrite 1?fin_sum_case_L, 1?fin_sum_case_R;
  cbn;
  rewrite 1?fin_sum_case_L, 1?fin_sum_case_R;
  cbn.
  - replace (Fin.cast (finL _) _) with (finL (finL i) :> fin (n + (m + o) + p)).
    2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, 4 fin_to_nat_L.
      done.
    }
    rewrite 2 fin_perm_stack_L.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, 4 fin_to_nat_L.
    done.
  - replace (Fin.cast (finL _) _) with (finL (finR (finL i)) :> fin (n + (m + o) + p)).
    2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, 2 fin_to_nat_L, 2 fin_to_nat_R, fin_to_nat_L.
      done.
    }
    rewrite fin_perm_stack_L, fin_perm_stack_R, fin_add_comm_L.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, fin_to_nat_L, 3 fin_to_nat_R, fin_to_nat_L.
    lia.
  - replace (Fin.cast (finR _) _) with (finL (finR (finR i)) :> fin (n + (m + o) + p)).
    2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, fin_to_nat_L, 3 fin_to_nat_R, fin_to_nat_L.
      lia.
    }
    rewrite fin_perm_stack_L, fin_perm_stack_R, fin_add_comm_R.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, 2 fin_to_nat_L, 2 fin_to_nat_R, fin_to_nat_L.
    lia.
  - replace (Fin.cast (finR _) _) with (finR i :> fin (n + (m + o) + p)).
    2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, 3 fin_to_nat_R.
      lia.
    }
    rewrite fin_perm_stack_R.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, 3 fin_to_nat_R.
    lia.
Qed.



Lemma fin_perm_of_zx_mul_S_r {n m} :
  fin_perm_of_zx (zx_mul_S_r n m) ≡ Some fin_perm_mul_S_r.
Proof.
  induction n.
  - cbn.
    f_equiv.
    intros i.
    inv_all_vec_fin.
  - cbn -[Nat.add Nat.mul n_wire].
    rewrite IHn.
    rewrite fin_perm_of_n_wire.
    cbn -[Nat.add Nat.mul].
    rewrite (fin_perm_of_zx_mid_comm 1 m n (n * m)).
    cbn -[Nat.add Nat.mul].
    f_equiv.
    intros i.
    induction i as [il ir] using fin_mul_ind.
    unfold fin_perm_mul_S_r at 2.
    rewrite fin_split_prod.

    induction il as [|il] using fin_S_inv.
    1:{
      cbn -[finR].
      rewrite fin_perm_stack_L.
      unfold fin_mid_comm.
      cbn.

      induction ir as [|ir] using fin_S_inv; [done|].
      cbn.
      rewrite fin_sum_case_L.
      done.
    }
    cbn -[finR].
    rewrite fin_perm_stack_R.
    unfold fin_perm_mul_S_r.
    rewrite fin_split_prod.
    induction ir as [|ir] using fin_S_inv.
    1:{
      cbn -[finR].
      unfold fin_mid_comm.
      cbn -[finR fin_sum_case].
      rewrite fin_sum_case_R.
      cbn -[finR fin_sum_case].
      rewrite fin_sum_case_L.
      done.
    }
    cbn -[finR].
    unfold fin_mid_comm.
    cbn -[finR fin_sum_case].
    rewrite fin_sum_case_R.
    cbn -[finR fin_sum_case].
    rewrite fin_sum_case_R.
    done.
Qed.


Lemma fin_perm_of_zx_mul_comm {n m} :
  fin_perm_of_zx (zx_mul_comm n m) ≡ Some fin_prod_comm.
Proof.
  induction m.
  - cbn.
    rewrite fin_perm_of_zx_cast.
    cbn.
    f_equiv.
    intros i.
    exfalso.
    revert i.
    rewrite Nat.mul_0_r.
    intros; inv_all_vec_fin.
  - cbn.
    rewrite fin_perm_of_zx_mul_S_r, fin_perm_of_n_wire, IHm.
    cbn.
    f_equiv.
    intros i.
    induction i as [il ir] using fin_mul_ind.
    rewrite fin_prod_comm_prod.
    unfold fin_perm_mul_S_r.
    rewrite fin_split_prod.
    induction ir as [|ir] using fin_S_inv; cbn.
    + apply fin_perm_stack_L.
    + now rewrite fin_perm_stack_R, fin_prod_comm_prod.
Qed.



Lemma ZX_tensor_semantics_by_fin_perm_of_zx {n m} (zx : ZX n m) p :
  fin_perm_of_zx zx ≡ Some p ->
  ZX_tensor_semantics zx ≡ perm_tensor p.
Proof.
  intros Hp.
  apply (f_equiv is_Some) in Hp as Hp'.
  pose proof (Hp'.2) as Hp''.
  tspecialize Hp'' by trivial.
  rewrite (ZX_tensor_semantics_zxperm_aux _ Hp'').
  f_equiv.
  clear Hp'.
  revert Hp Hp''.
  destruct (fin_perm_of_zx zx); [|easy].
  cbn.
  intros Htp%(inj Some).
  done.
Qed.



Lemma ZX_tensor_semantics_n_stack k {n m} (zx : ZX n m) :
  ZX_tensor_semantics (k ⇑ zx) ≡ n_stack_tensor k (ZX_tensor_semantics zx).
Proof.
  induction k; cbn.
  - intros v w; inv_all_vec_fin; done.
  - apply stack_tensor_mor, IHk; done.
Qed.

Definition ZX_copy k {n m} (zx : ZX n m) : ZX (n * k) (m * k) :=
  zx_mul_comm n k ⟷ n_stack k zx ⟷ zx_mul_comm k m.

Lemma ZX_tensor_semantics_ZX_copy k {n m} (zx : ZX n m) :
  ZX_tensor_semantics (ZX_copy k zx) ≡
  copy_tensor k (ZX_tensor_semantics zx).
Proof.
  cbn.
  pose proof (ZX_tensor_semantics_by_fin_perm_of_zx _ _
    (@fin_perm_of_zx_mul_comm n k)) as Hl.
  pose proof (ZX_tensor_semantics_by_fin_perm_of_zx _ _
    (@fin_perm_of_zx_mul_comm k m)) as Hr.
  erewrite compose_tensor_mor; [|
    apply compose_tensor_mor;
    [apply Hl|apply ZX_tensor_semantics_n_stack]|apply Hr].
  rewrite copy_tensor_alt.
  rewrite (compose_perm_tensor_r _ _) by lia.
  erewrite permute_tensor_mor; [|done..|
  apply (compose_perm_tensor_l (Nat.mul_comm _ _) _)].
  rewrite permute_tensor_compose.
  rewrite compose_id_left, compose_id_right.
  apply permute_tensor_mor; [|done..].
  rewrite fin_perm_inv_cast_fin_prod_comm.
  done.
Qed.


Lemma n_cup_alt_ZX_copy n :
  n_cup n ∝= cast (n + n) _ (Nat.double_twice n) eq_refl (ZX_copy n ⊃).
Proof.
  unfold ZX_copy.
  rewrite (empty_zxperm_empty (Nat.mul_0_r n) eq_refl) by auto_zxperm.
  rewrite cast_compose_r, compose_empty_r, 2 cast_contract_eq'.
  induction n;
  [unfold n_cup; cbn; apply prop_eq_of_perm_eq; [auto_zxperm..|easy]|].
  rewrite n_cup_grow_l.
  rewrite IHn.
  clear IHn.
  rewrite cast_stack_r_fwd.
  rewrite <- (nwire_removal_l ⊃) at 1.
  rewrite (stack_compose_distr (n_wire 2) ⊃ (zx_mul_comm 2 n) (n ⇑ ⊃)).
  rewrite 2 cast_compose_distribute.
  rewrite <- ComposeRules.compose_assoc.
  f_equiv; [|cast_irrelevance].
  cbn [zx_mul_comm].
  rewrite cast_compose_r.
  rewrite 2 cast_compose_distribute.
  f_equiv; [|cast_irrelevance].
  rewrite cast_contract_eq'.
  unshelve rewrite cast_backwards_eq, cast_contract_eq';
  [reflexivity|apply (f_equal (Nat.add 2) (Nat.double_twice n))|].
  unfold proportional_by_1.
  rewrite <- 2 ZX_tensor_semantics_correct.
  prep_matrix_equivalence.
  apply matrix_of_tensor_of_equiv.
  erewrite ZX_tensor_semantics_by_fin_perm_of_zx.
  2:{
    rewrite fin_perm_of_zx_cast, fin_perm_of_zx_mul_S_r.
    cbn -[Nat.add Nat.mul].
    done.
  }
  erewrite ZX_tensor_semantics_by_fin_perm_of_zx.
  2:{
    apply fin_perm_of_zx_mid_comm.
  }
  f_equiv.
  intros i.
  remember (eq_sym _) as prfl eqn:Hprfl.
  clear Hprfl.
  remember (eq_sym _) as prfr eqn:Hprfr.
  clear Hprfr.
  rewrite cast_fin_perm_apply.
  unfold fin_mid_comm.
  cbn -[Nat.add Nat.mul].
  induction i as [i|i] using fin_add_inv.
  - replace (Fin.cast (finL i) (eq_sym prfl))
      with (fin_prod (0 :> fin 2) i). 2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, fin_to_nat_L, fin_to_nat_prod.
      done.
    }
    rewrite fin_sum_case_L.
    cbn -[Nat.add Nat.mul fin_prod].
    unfold fin_perm_mul_S_r.
    rewrite fin_split_prod.
    induction i as [|i] using fin_S_inv; [done|].
    cbn.
    do 2 f_equal.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, 2 fin_to_nat_L.
    done.
  - replace (Fin.cast (finR i) (eq_sym prfl))
      with (fin_prod (1 :> fin 2) i). 2:{
      apply fin_to_nat_inj.
      rewrite fin_to_nat_cast, fin_to_nat_R, fin_to_nat_prod.
      cbn.
      lia.
    }
    rewrite fin_sum_case_R.
    cbn -[Nat.add Nat.mul fin_prod].
    unfold fin_perm_mul_S_r.
    rewrite fin_split_prod.
    induction i as [|i] using fin_S_inv; [done|].
    cbn.
    do 2 f_equal.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast, 2 fin_to_nat_R, fin_to_nat_L.
    done.
Qed.




Lemma allb_forallb b {n} (v : vec bool n) :
  allb b v = forallb (eqb b) v.
Proof.
  induction v; cbn; f_equal; done.
Qed.

Lemma ZX_tensor_semantics_Z_delta_spider n m :
  ZX_tensor_semantics (Z n m 0) ≡
  delta_spider_tensor.
Proof.
  cbn.
  intros v w _ _.
  cbn.
  rewrite sum_of_bool_defn.
  unfold zsp.
  rewrite Cexp_0.
  f_equal; rewrite decide_bool_decide; (apply f_equal_if; [|done..]);
  apply (inj Is_true);
  rewrite bool_decide_spec, andb_True, 2 allb_forallb, 2 forallb_True,
  vec_to_list_app, Forall_app;
  f_equiv; apply Forall_iff; now intros [].
Qed.




Lemma Z_Rmodeq_2PI {n m} α α' : α =[mod 2 * PI] α' ->
  Z n m α ∝= Z n m α'.
Proof.
  intros Hα.
  prep_matrix_equivalence.
  apply tensor_of_matrix_inj'.
  rewrite <- 2 ZX_tensor_semantics_correct.
  rewrite 2 tensor_of_matrix_of_tensor.
  cbn.
  now f_equiv.
Qed.

Lemma X_Rmodeq_2PI {n m} α α' : α =[mod 2 * PI] α' ->
  X n m α ∝= X n m α'.
Proof.
  intros Hα.
  colorswap_of (@Z_Rmodeq_2PI n m α α' Hα).
Qed.


(* FIXME: Move!!! *)
Lemma cast_n_wire_l {n m o}
  (Hm : m = n) (Ho : o = n) :
  cast _ _ Hm Ho (n_wire n) =
  cast _ _ eq_refl (eq_trans Ho (eq_sym Hm)) (n_wire m).
Proof.
  subst; now rewrite 2 cast_id_eq.
Qed.
Lemma cast_n_wire_r {n m o}
  (Hm : m = n) (Ho : o = n) :
  cast _ _ Hm Ho (n_wire n) =
  cast _ _ (eq_trans Hm (eq_sym Ho)) eq_refl (n_wire o).
Proof.
  subst; now rewrite 2 cast_id_eq.
Qed.



Lemma Z_push_out_phase_gadget n m α : Z n m α ∝= Z n (S m) 0 ⟷ (Z 1 0 α ↕ n_wire m).
Proof.
  rewrite (dominated_Z_spider_fusion_top_left 0 0 m n).
  now rewrite Rplus_0_r.
Qed.

Lemma Z_push_out_phase_gadget' n m α β : Z n m (α + β) ∝=
  Z n (S m) β ⟷ (Z 1 0 α ↕ n_wire m).
Proof.
  rewrite (dominated_Z_spider_fusion_top_left 0 0 m n).
  done.
Qed.

Lemma PRO_to_ZX_cast `{ProLike Struct T ZX}
  {n m n' m'} (Hn : n = n') (Hm : m = m') (p : PRO Struct T n m) :
  PRO_to_diagram (cast_PRO Hn Hm p) =
  cast _ _ (eq_sym Hn) (eq_sym Hm) <$> PRO_to_diagram p.
Proof.
  subst.
  rewrite cast_PRO_id.
  destruct (PRO_to_diagram _); [|done].
  done.
Qed.

Lemma zx_mul_comm_n_1 n : zx_mul_comm n 1 ∝=
  cast _ _ (Nat.mul_1_r n) (Nat.mul_1_l n) (n_wire n).
Proof.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  rewrite perm_of_zx_mul_comm.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite kron_comm_perm_defn.
  intros i Hi.
  rewrite Nat.mod_small, Nat.div_small; lia.
Qed.

Lemma zx_mul_comm_1_n n : zx_mul_comm 1 n ∝=
  cast _ _ (Nat.mul_1_l n) (Nat.mul_1_r n) (n_wire n).
Proof.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  rewrite perm_of_zx_mul_comm.
  rewrite perm_of_zx_cast, perm_of_n_wire.
  rewrite kron_comm_perm_defn.
  intros i Hi.
  rewrite Nat.mod_1_r, Nat.div_1_r.
  lia.
Qed.

Lemma ZX_copy_1 {n m} (zx : ZX n m) :
  ZX_copy 1 zx ∝= cast _ _ (Nat.mul_1_r n) (Nat.mul_1_r m) zx.
Proof.
  unfold ZX_copy.
  rewrite zx_mul_comm_1_n, zx_mul_comm_n_1.
  rewrite n_stack_1.
  rewrite 2 cast_compose_eq_mid_join, nwire_removal_l, nwire_removal_r.
  cast_irrelevance.
Qed.


Lemma zx_mul_comm_0_l n : zx_mul_comm 0 n ∝= cast _ _ eq_refl (Nat.mul_0_r _) ⦰.
Proof.
  apply empty_zxperm_empty.
  auto_zxperm.
Qed.

Lemma zx_mul_comm_0_r n : zx_mul_comm n 0 ∝= cast _ _ (Nat.mul_0_r _) eq_refl ⦰.
Proof.
  apply empty_zxperm_empty.
  auto_zxperm.
Qed.
Lemma zx_of_perm_kron_comm_perm n m :
  zx_of_perm (n * m) (kron_comm_perm n m) ∝=
  cast _ _ eq_refl (Nat.mul_comm _ _) (zx_mul_comm n m).
Proof.
  prop_perm_eq_nosimpl.
  eq_by_WF_perm_eq (n * m).
  rewrite perm_of_zx_of_perm_eq, perm_of_zx_cast by auto_perm.
  rewrite perm_of_zx_mul_comm.
  done.
Qed.



Lemma zx_mul_comm_transpose n m : (zx_mul_comm n m) ⊤ ∝= zx_mul_comm m n.
Proof.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  rewrite perm_of_zx_transpose by auto_zxperm.
  rewrite 2 perm_of_zx_mul_comm.
  rewrite kron_comm_perm_inv'.
  done.
Qed.

Lemma zx_mul_comm_cancel n m : zx_mul_comm n m ⟷ zx_mul_comm m n ∝= n_wire _.
Proof.
  rewrite <- (zx_mul_comm_transpose n m).
  apply zxperm_transpose_right_inverse; auto_zxperm.
Qed.

Lemma zx_mul_comm_S_r n m : zx_mul_comm n (S m) ∝=
  zx_mul_S_r n m ⟷ (n_wire n ↕ zx_mul_comm n m).
Proof.
  done.
Qed.

Lemma zx_mul_comm_S_l n m : zx_mul_comm (S n) m ∝=
  n_wire m ↕ zx_mul_comm n m ⟷ (zx_mul_S_r m n) ⊤.
Proof.
  apply transpose_diagrams_eq.
  rewrite zx_mul_comm_transpose.
  cbn.
  rewrite transpose_involutive, n_wire_transpose, zx_mul_comm_transpose.
  done.
Qed.

Lemma zx_mul_comm_le_1_l n m : n ≤ 1 -> zx_mul_comm n m ∝= cast _ _ eq_refl (Nat.mul_comm _ _) (n_wire _).
Proof.
  intros Hn.
  assert (n = 0 \/ n = 1) as [-> | ->] by lia.
  - cbn -[cast].
    rewrite zx_mul_comm_0_l.
    cast_irrelevance.
  - rewrite zx_mul_comm_1_n.
    auto_cast_eqn rewrite cast_backwards_eq, cast_contract_eq', cast_n_wire.
    done.
Qed.

Lemma zx_mul_comm_le_1_r n m : m ≤ 1 -> zx_mul_comm n m ∝= cast _ _ (Nat.mul_comm _ _) eq_refl  (n_wire _).
Proof.
  intros Hm.
  apply transpose_diagrams_eq.
  rewrite zx_mul_comm_transpose, cast_transpose, n_wire_transpose.
  rewrite zx_mul_comm_le_1_l by done.
  done.
Qed.

Lemma ZX_copy_le_1 k {n m} (zx : ZX n m) : n <= 1 -> m <= 1 -> ZX_copy k zx ∝=
  cast _ _ (Nat.mul_comm _ _) (Nat.mul_comm _ _) (k ⇑ zx).
Proof.
  unfold ZX_copy.
  intros Hn Hm.
  rewrite zx_mul_comm_le_1_l by done.
  rewrite zx_mul_comm_le_1_r by done.
  rewrite n_wire_removal_l'.
  rewrite n_wire_removal_r', cast_contract_eq'.
  cast_irrelevance.
Qed.


Lemma const_of_zx_colorswap zx : const_of_zx (color_swap zx) = const_of_zx zx.
Proof.
  rewrite colorswap_is_bihadamard.
  cbn -[const_of_zx].
  rewrite compose_empty_r, compose_empty_l.
  done.
Qed.

Lemma stack_push_tl {n m o n' m'} (zx : ZX n m) (zx' : ZX m o) (zx'' : ZX n' m') :
  (zx ⟷ zx') ↕ zx'' ∝= zx ↕ n_wire _ ⟷ (zx' ↕ zx'').
Proof.
  rewrite <- stack_compose_distr, nwire_removal_l.
  done.
Qed.

Lemma stack_push_tr {n m o n' m'} (zx : ZX n m) (zx' : ZX m o) (zx'' : ZX n' m') :
  (zx ⟷ zx') ↕ zx'' ∝= (zx ↕ zx'') ⟷ (zx' ↕ n_wire _).
Proof.
  rewrite <- stack_compose_distr, nwire_removal_r.
  done.
Qed.

Lemma stack_push_bl {n m n' m' o'} (zx : ZX n m) (zx' : ZX n' m') (zx'' : ZX m' o') :
  zx ↕ (zx' ⟷ zx'') ∝= n_wire _ ↕ zx' ⟷ (zx ↕ zx'').
Proof.
  rewrite <- stack_compose_distr, nwire_removal_l.
  done.
Qed.

Lemma stack_push_br {n m n' m' o'} (zx : ZX n m) (zx' : ZX n' m') (zx'' : ZX m' o') :
  zx ↕ (zx' ⟷ zx'') ∝= (zx ↕ zx') ⟷ (n_wire _ ↕ zx'').
Proof.
  rewrite <- stack_compose_distr, nwire_removal_r.
  done.
Qed.

Lemma stack_mid_comm {n0 m0 n1 m1 n2 m2 n3 m3}
  (zx0 : ZX n0 m0) (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) (zx3 : ZX n3 m3) :
  (zx0 ↕ zx1) ↕ (zx2 ↕ zx3) ∝= zx_mid_comm _ _ _ _
    ⟷ ((zx0 ↕ zx2) ↕ (zx1 ↕ zx3)) ⟷ zx_mid_comm _ _ _ _.
Proof.
  rewrite ComposeRules.compose_assoc, zx_mid_comm_commutes_r.
  rewrite <- ComposeRules.compose_assoc, <- zx_mid_comm_transpose, zxperm_transpose_left_inverse by auto_zxperm.
  rewrite nwire_removal_l.
  done.
Qed.


Lemma n_stack_gadget_to_scalar k (zx : ZX 0 0) :
  k ⇑ zx ∝= const_of_zx zx ^ k .* n_wire _.
Proof.
  induction k; [cbn; rewrite zx_scale_1_l; done|].
  cbn.
  rewrite IHk, (gadget_is_scaled_empty zx) at 1.
  distribute_zxscale.
  apply zx_scale_simplify_eq.
  - C_field.
  - apply stack_empty_l.
Qed.