From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.

(* First, we must define the data assocated to generators. In our case,
  we use [option (bool * R + C)] with [None] being the hadamard box,
  [Some (inl (false, α))] being a Z spider with phase [α],
  [Some (inl (true, α))] being a X spider with phase [α], and
  [Some (inr c)] being a constant gadget with value [c]. *)
Definition ZXCVERT := option (bool * R + C).

(* We must show the type of generators is nonempty *)
#[export] Instance ZXCVERT_inhab : Inhabited ZXCVERT := populate None.

(* We define the natural equivalence relation on [ZXCVERT], with phases
  taken mod [2*PI], and show it is in fact an equivalence relation. *)
#[export] Instance ZXCVERT_equiv : Equiv ZXCVERT :=
  option_Forall2 (sum_relation (prod_relation eq (Rmodeq (2*PI))) eq).

#[export] Instance ZXCVERT_equiv_equivalence : Equivalence (≡@{ZXCVERT}).
Proof. apply _. Qed.

(* We give an interpretation of our generators as dimensionless tensors (to [C]),
  using the definitions in [ZXCore.v] *)
Definition ZXCCALC_tensor (x : ZXCVERT) : DimensionlessTensor bool :=
  match x with
  | None => fun n m => (tensor_to_dimensionless (@h_stack n)) n m
  | Some (inl (false, r))  => fun n m => @zsp n m r
  | Some (inl (true, r)) => fun n m => @xsp n m r
  | Some (inr c) => fun n m v w => c
  end.

#[global] Arguments ZXCCALC_tensor !_ /.

(* We show this tensor interpretation respects our equivalence relation;
  this is basically just applying instances from [ZXCore.v]. *)
#[export] Instance ZXCCALC_tensor_proper :
  Proper ((≡) ==> (≡)) ZXCCALC_tensor.
Proof.
  intros x x' Heq.
  induction Heq as [x y Heq|]; [|done..].
  induction Heq as [ [ [] x] [c y] [ [= <-] Heq]|? ? <-]; [..|done];
  cbn;
  intros n m;
  now rewrite Heq.
Qed.

(* Then, we give the [TensorLike] instance defining the tensor associated
  to a [ZXCVERT]. *)
#[export] Instance ZXCCALC : TensorLike C bool ZXCVERT := {
  interpretTensor := ZXCCALC_tensor;
}.


(* We declare the equivalence relation assocaited to ZX-diagrams *)
#[local] Instance ZX_equiv {n m} : Equiv (ZX n m) := proportional_by_1.

#[program] Instance ZX_tensorlike : StrictTensorLike C bool ZX := {
  strictInterpretTensor n m zx := ZX_tensor_semantics zx;
}.
Next Obligation.
  intros n m zx zx' Hzx.
  apply matrix_of_tensor_inj.
  rewrite 2 ZX_tensor_semantics_correct.
  now rewrite Hzx.
Qed.

Definition ZXCVERT_to_ZX
  n m (c : ZXCVERT) : option (ZX n m) :=
  match c with
  | None => match decide (n = m) with
    | left Heq => Some (cast _ _ Heq eq_refl (n_stack1 m Box))
    | right _ => None
    end
  | Some (inl (true, r)) => Some (X n m r)
  | Some (inl (false, r)) => Some (Z n m r)
  | Some (inr c) => match n, m with
    | 0, 0 => Some (zx_of_const c)
    | _, _ => None
    end
  end.

#[export] Instance ZX_tensorable : TensorableDiagram ZXCVERT ZX :=
  ZXCVERT_to_ZX.

#[export] Instance ZX_compositional : Compositional ZX := {
  Did n := n_wire n;
  Dcompose _ _ _ zx zx' := zx ⟷ zx';
  Dstack _ _ _ _ zx zx' := zx ↕ zx';
}.

Definition Monoidal_to_ZX {n m} (p : Monoidal n m) : ZX n m :=
  cast n m (Monoidal_eq p) eq_refl (n_wire _).

Definition Symmetry_to_ZX {n m} (p : Symmetry n m) : ZX n m :=
  match p with
  | Swap n m => zx_comm n m
  end.


Definition SymmetricG_to_ZX {n m} (p : SymmetricG n m) : ZX n m :=
  match p with
  | inl p => Monoidal_to_ZX p
  | inr p => Symmetry_to_ZX p
  end.

Definition Autonomy_to_ZX {n m} (p : Autonomy n m) : ZX n m :=
  match p with
  | Cap 0 => ⦰
  | Cap 1 => ⊃
  | Cap n => n_cup n
  | Cup 0 => ⦰
  | Cup 1 => ⊂
  | Cup n => n_cap n
  end.

Definition Autonomous_to_ZX {n m} (p : Autonomous n m) : ZX n m :=
  match p with
  | inl p => SymmetricG_to_ZX p
  | inr p => Autonomy_to_ZX p
  end.

#[export] Instance ZX_Monoidal_structable : StructableDiagram Monoidal ZX :=
  fun _ _ => Monoidal_to_ZX.

#[export] Instance ZX_Symmetry_structable : StructableDiagram Symmetry ZX :=
  fun _ _ => Symmetry_to_ZX.

#[export] Instance ZX_Autonomy_structable : StructableDiagram Autonomy ZX :=
  fun _ _ => Autonomy_to_ZX.

#[export] Instance ZX_SymmetricG_structable : StructableDiagram SymmetricG ZX :=
  fun _ _ => SymmetricG_to_ZX.

#[export] Instance ZX_Autonomous_structable : StructableDiagram Autonomous ZX :=
  fun _ _ => Autonomous_to_ZX.

Local Instance ZX_abstract_symmetricG : AbstractProLike SymmetricG ZX := {}.

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
(*
Lemma zx_mul_comm_S_l n m : zx_mul_comm (S n) m ∝= K.

Lemma zx_mul_comm_transpose n m : ((zx_mul_comm n m) ⊤)%ZX ∝= zx_mul_comm m n.
Proof. *)



Lemma Monoidal_to_ZX_zxperm
  {n m} (p : Monoidal n m) : ZXperm (Monoidal_to_ZX p).
Proof.
  unfold Monoidal_to_ZX.
  auto_zxperm.
Qed.

Lemma Symmetry_to_ZX_zxperm
  {n m} (p : Symmetry n m) : ZXperm (Symmetry_to_ZX p).
Proof.
  induction p; cbn;
  auto_zxperm.
Qed.

#[export] Hint Resolve Monoidal_to_ZX_zxperm Symmetry_to_ZX_zxperm : zxperm_db.

Lemma zx_symmetricG_SPRO_to_diagram_zxperm
  {n m} (p : SPRO SymmetricG n m) : ZXperm (SPRO_to_diagram p).
Proof.
  induction p; cbn; [auto_zxperm..| |done].
  induction s; cbn; auto_zxperm.
Qed.

#[export] Hint Resolve zx_symmetricG_SPRO_to_diagram_zxperm : zxperm_db.


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


Lemma fin_perm_inv_cast_eq_of_cancel {n m} (Hnm : n = m) (f : fin n -> fin m)
  {Hf : Inj eq eq f} (fi : fin m -> fin n) :
  Cancel eq f fi ->
  fin_perm_inv_cast Hnm f ≡ fi.
Proof.
  subst.
  intros Hffi.
  rewrite fin_perm_inv_cast_id.
  intros i.
  apply (fin_perm_inv_spec f).
  apply Hffi.
Qed.

Lemma fin_perm_inv_cast_fin_prod_comm {n m} (Hnm : n * m = m * n) :
  fin_perm_inv_cast Hnm fin_prod_comm ≡ fin_prod_comm.
Proof.
  apply fin_perm_inv_cast_eq_of_cancel; apply _.
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

(* FIXME: Move *)
Lemma empty_zxperm_empty {n m} (Hn : n = 0) (Hm : m = 0)
  (zx : ZX n m) : ZXperm zx ->
  zx ∝= cast n m Hn Hm ⦰.
Proof.
  intros Hzx.
  apply prop_eq_of_perm_eq; [auto_zxperm..|].
  subst.
  easy.
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

Definition Frobenial_to_ZX {n m} (p : Frobenial n m) : ZX n m :=
  match p with
  | Delta0 => Z 0 0 0
  | Delta1 n m => Z n m 0
  | Delta k n m => ZX_copy k (Z n m 0)
  end.

Definition Frobenius_to_ZX {n m} (p : Frobenius n m) : ZX n m :=
  match p with
  | inl p => Autonomous_to_ZX p
  | inr p => Frobenial_to_ZX p
  end.

#[export] Instance ZX_Frobenial_structable : StructableDiagram Frobenial ZX :=
  fun _ _ => Frobenial_to_ZX.

#[export] Instance ZX_Frobenius_structable : StructableDiagram Frobenius ZX :=
  fun _ _ => Frobenius_to_ZX.

#[export] Instance ZX_SymmetricG_ProLike : ProLike SymmetricG ZXCVERT ZX := {
  PL_tensD := ZX_tensorable
}.

#[export] Instance ZX_Autonomous_ProLike : ProLike Autonomous ZXCVERT ZX := {
  PL_tensD := ZX_tensorable
}.

#[export] Instance ZX_Frobenius_ProLike : ProLike Frobenius ZXCVERT ZX := {
  PL_tensD := ZX_tensorable
}.

(* FIXME: Move *)
#[export] Instance morunion_leibniz {A} {Struct Struct' : Mor A}
  `{EqStruct : forall n m, Equiv (Struct n m),
    LeibStruct : forall n m, LeibnizEquiv (Struct n m)}
  `{EqStruct' : forall n m, Equiv (Struct' n m),
    LeibStruct' : forall n m, LeibnizEquiv (Struct' n m)} :
    forall n m, LeibnizEquiv (MorUnion Struct Struct' n m).
Proof.
  intros n m p p' Hp.
  induction Hp as [? ? Hp|? ? Hp]; apply leibniz_equiv in Hp; congruence.
Qed.

#[export] Instance Monoidal_leibniz n m : LeibnizEquiv (Monoidal n m).
Proof.
  easy.
Qed.

#[export] Instance Symmetry_leibniz n m : LeibnizEquiv (Symmetry n m).
Proof.
  easy.
Qed.

#[export] Instance Autonomy_leibniz n m : LeibnizEquiv (Autonomy n m).
Proof.
  easy.
Qed.

#[export] Instance Frobenial_leibniz n m : LeibnizEquiv (Frobenial n m).
Proof.
  easy.
Qed.




(* Print Instances LawfulStructGraphable. *)
(* FIXME: Move *)
#[export] Instance proper_from_symemtricg {n m} `{Reflexive T RT}
  (f : SymmetricG n m -> T) :
  Proper (equiv ==> RT) f.
Proof.
  intros s s' <-%leibniz_equiv.
  done.
Qed.
#[export] Instance proper_from_autonomous {n m} `{Reflexive T RT}
  (f : Autonomous n m -> T) :
  Proper (equiv ==> RT) f.
Proof.
  intros s s' <-%leibniz_equiv.
  done.
Qed.
#[export] Instance proper_from_frobenius {n m} `{Reflexive T RT}
  (f : Frobenius n m -> T) :
  Proper (equiv ==> RT) f.
Proof.
  intros s s' <-%leibniz_equiv.
  done.
Qed.

#[export, program] Instance ZX_Monoidal_lawstructable :
  LawfulStructableDiagram C bool Monoidal ZX.
Next Obligation.
  intros n m sm.
  cbn.
  unfold ofStruct, ZX_Monoidal_structable; cbn.
  unfold Monoidal_to_ZX.
  etransitivity; [|symmetry; apply (Monoidal_semantics sm)].
  destruct (Monoidal_eq sm).
  cbn.
  rewrite perm_tensor_id' by now intros; apply fcast_id.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct.
  now rewrite n_wire_semantics, matrix_of_tensor_delta.
Qed.

#[export, program] Instance ZX_Symmetry_lawstructable :
  LawfulStructableDiagram C bool Symmetry ZX.
Next Obligation.
  intros n m ss.
  cbn.
  induction ss as [n m].
  cbn.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct.
  rewrite <- tensor_of_matrix_kron_comm.
  rewrite matrix_of_tensor_of_matrix.
  now rewrite zx_comm_semantics.
Qed.

#[export, program] Instance ZX_Autonomy_lawstructable :
  LawfulStructableDiagram C bool Autonomy ZX.
Next Obligation.
  intros n m sa.
  induction sa as [[|[|n]]|[|[|n]]]; cbn -[n_cup n_cap].
  - intros v w.
    inv_all_vec_fin.
    done.
  - done.
  - unfold n_cap.
    apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    rewrite semantics_transpose_comm.
    apply tensor_of_matrix_inj'.
    rewrite tensor_of_matrix_transpose.
    intros v w Hv Hw.
    etransitivity; [apply (tensor_of_matrix_n_cup_semantics (S (S n)) w v); done|].
    rewrite tensor_of_matrix_of_tensor.
    done.
  - intros v w.
    inv_all_vec_fin.
    done.
  - done.
  - apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    apply tensor_of_matrix_inj'.
    etransitivity; [apply (tensor_of_matrix_n_cup_semantics (S (S n)))|].
    rewrite tensor_of_matrix_of_tensor.
    done.
Qed.

#[export, program] Instance ZX_Frobenial_lawstructable :
  LawfulStructableDiagram C bool Frobenial ZX.
Next Obligation.
  intros n m s.
  induction s as [|n m|k n m];
  [now cbn; try rewrite <- ZX_tensor_semantics_Z_delta_spider..|].
  cbn -[ZX_copy].
  rewrite ZX_tensor_semantics_ZX_copy.
  unfold delta_spider_tensor_bundled.
  apply copy_tensor_mor.
  apply ZX_tensor_semantics_Z_delta_spider.
Qed.

#[export, program] Instance ZX_SymmetricG_lawstructable :
  LawfulStructableDiagram C bool SymmetricG ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
Qed.

#[export, program] Instance ZX_Autonomous_lawstructable :
  LawfulStructableDiagram C bool Autonomous ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
Qed.

#[export, program] Instance ZX_Frobenius_lawstructable :
  LawfulStructableDiagram C bool Frobenius ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
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

#[program] Instance ZX_lawtensorable
  : LawfulTensorableDiagram C bool (TensT := ZXCCALC)
    ZXCVERT ZX (StructD := ZX_tensorable).
Next Obligation.
  intros n m zxc zxc' Heq.
  induction Heq as [z_c z_c' Heq|]; [|done].
  induction Heq as [z z' Heq|c c' <-]; [|done].
  destruct z as [is_x r], z' as [is_x' r'].
  destruct Heq as [[= <-] Heq].
  cbn.
  destruct is_x; f_equiv; [apply X_Rmodeq_2PI|apply Z_Rmodeq_2PI]; done.
Qed.
Next Obligation.
  intros n m [[([], r)|c]|] d.
  - cbn.
    intros [= <-].
    done.
  - cbn.
    intros [= <-].
    done.
  - cbn.
    case_match; [|done].
    case_match; [|done].
    intros [= <-].
    subst.
    apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    rewrite zx_of_const_semantics.
    intros v w Hv Hw.
    cbn in *.
    replace v with 0 by lia.
    replace w with 0 by lia.
    unfold scale.
    cbn.
    apply Cmult_1_r.
  - cbn.
    unfold ZXCCALC_tensor.
    case_decide; [|done].
    subst m.
    rewrite cast_id_eq.
    intros [= <-].
    unfold ZXCCALC_tensor.
    cbn.
    apply matrix_of_tensor_inj.
    rewrite tensor_to_dimensionless_refl.
    rewrite matrix_of_tensor_h_stack.
    rewrite ZX_tensor_semantics_correct.
    rewrite n_stack1_semantics.
    done.
Qed.

#[program] Instance ZX_lawcompositional : LawfulCompositional C bool ZX.
Next Obligation.
  intros n.
  cbn.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct, n_wire_semantics, matrix_of_tensor_delta.
  done.
Qed.
Next Obligation.
  done.
Qed.
Next Obligation.
  done.
Qed.
Next Obligation.
  intros n m zx zx' Hzx.
  prep_matrix_equivalence.
  apply tensor_of_matrix_inj'.
  rewrite <- 2 ZX_tensor_semantics_correct.
  rewrite 2 tensor_of_matrix_of_tensor.
  apply Hzx.
Qed.
(*
#[export] Instance ZX_lawpro phases consts :
  LawfulProLike C bool Frobenius ZXCVERT ZX
    (ProD:=ZX_ProLike phases consts)
    (TensT := ZXCCALC phases consts):= {}. *)


#[export] Instance ZX_SymmetricG_lawpro :
  LawfulProLike C bool SymmetricG ZXCVERT ZX
    (ProD:=ZX_SymmetricG_ProLike)
    (TensT := ZXCCALC):= {}.


#[export] Instance ZX_Autonomous_lawpro :
  LawfulProLike C bool Autonomous ZXCVERT ZX
    (ProD:=ZX_Autonomous_ProLike)
    (TensT := ZXCCALC):= {}.

#[export] Instance ZX_Frobenius_lawpro :
  LawfulProLike C bool Frobenius ZXCVERT ZX
    (ProD:=ZX_Frobenius_ProLike)
    (TensT := ZXCCALC):= {}.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)

Module GeneratorNotations.

Notation "'const' a" := (Some (inr a)) (a at level 9, only printing, at level 1).

Notation "'Z' a" := (Some (inl (false, a))) (a at level 9, only printing, at level 1).
Notation "'Z'" := (Some (inl (false, IZR 0))) (only printing, at level 1).

Notation "'X' a" := (Some (inl (true, a))) (a at level 9, only printing, at level 1).
Notation "'X'" := (Some (inl (true, IZR 0))) (only printing, at level 1).

Notation "'H'" := ((None :> ZXCVERT)) (only printing, at level 1).

End GeneratorNotations.

(* FIXME: Move *)
Lemma zx_of_const_mult' (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ⟷ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm, compose_empty_r.
  done.
Qed.




Module ZXsymm.

Export GeneratorNotations.

Section ZXquote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_SymmetricG_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_quote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_quote_symm_n_wire n : Quote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_symm_wire : Quote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_empty : Quote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_symm_zx_comm n m : Quote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_symm_swap : Quote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.


Lemma zx_quote_symm_cup : Quote ⊂ (Pgen 0 2 (Some (inl (false, 0%R)))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

Lemma zx_quote_symm_cap : Quote ⊃ (Pgen 2 0 (Some (inl (false, 0%R)))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.


#[export] Instance zx_quote_symm_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_symm_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_quote_symm_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_quote_symm_Z n m α : Quote (Z n m α) (Pgen n m (Some (inl (false, α)))) | 1.
Proof.
  constructor; done.
Qed.

#[export] Instance zx_quote_symm_X n m α : Quote (X n m α) (Pgen n m (Some (inl (true, α)))) | 1.
Proof.
  constructor; done.
Qed.

#[export] Instance zx_quote_symm_Z_wire :
  Quote (Z 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite Z_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_X_wire :
  Quote (X 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite X_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_H : Quote (Box) (Pgen 1 1 None).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_quote_symm_const c : Quote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_symm_scale c {n m} (zx : ZX n m) ap :
  Quote zx ap -> Quote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_quote_symm_stack 0 0); apply _.
Qed.

End ZXquote_symm.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramQuote ⊂ _) =>
  exact (zx_quote_symm_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote ⊃ _) =>
  exact (zx_quote_symm_cap) : typeclass_instances.

(*
#[export] Hint Extern 0 (DiagramQuote (n_cup ?n) _) =>
  exact (zx_quote_symm_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (n_cap ?n) _) =>
  exact (zx_quote_symm_cup n) : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (?zx ↕ ?zx') _) =>
  notypeclasses refine (zx_quote_symm_stack zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (?zx ⟷ ?zx') _) =>
  notypeclasses refine (zx_quote_symm_compose zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_quote_symm_scale c n m val _ _): typeclass_instances.

#[export] Hint Extern 10 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (?val) _) =>
  progress first [unfold val|simpl] : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (zx_comm ?n ?m) _) =>
  exact (zx_quote_symm_zx_comm n m) : typeclass_instances.





Section ZXdenote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Denote := (DiagramDenote (ProD:=ZX_SymmetricG_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_denote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_denote_symm_n_wire n : Denote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_symm_wire : Denote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_denote_symm_empty : Denote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_symm_zx_comm n m : Denote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_symm_swap : Denote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.

(* Lemma zx_denote_symm_n_cap n : Denote (n_cup n) (Pcap n).
Proof.
  constructor.
  cbn -[n_cup].
  rewrite <- (tensor_of_matrix_of_tensor (ZX_tensor_semantics _)).
  rewrite ZX_tensor_semantics_correct.
  apply tensor_of_matrix_n_cup_semantics.
Qed.

Lemma zx_denote_symm_n_cup n : Denote (n_cap n) (Acup n).
Proof.
  constructor.
  cbn -[n_cap].
  rewrite <- (tensor_of_matrix_of_tensor (ZX_tensor_semantics _)).
  rewrite ZX_tensor_semantics_correct.
  unfold n_cap.
  rewrite semantics_transpose_comm.
  rewrite tensor_of_matrix_transpose.
  intros v w Hv Hw.
  rewrite tensor_of_matrix_n_cup_semantics by done.
  done.
Qed. *)


Lemma zx_denote_symm_cup : Denote ⊂ (Pgen 0 2 (Some (inl (false, 0%R)))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

Lemma zx_denote_symm_cap : Denote ⊃ (Pgen 2 0 (Some (inl (false, 0%R)))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.


#[export] Instance zx_denote_symm_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_denote_symm_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_denote_symm_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Denote zx ap ->
  Denote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_denote_symm_Z n m α : Denote (Z n m α) (Pgen n m (Some (inl (false, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_symm_X n m α : Denote (X n m α) (Pgen n m (Some (inl (true, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_symm_H : Denote (Box) (Pgen 1 1 None).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_denote_symm_const c : Denote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_symm_scale c {n m} (zx : ZX n m) ap :
  Denote zx ap -> Denote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_denote_symm_stack 0 0); apply _.
Qed.

End ZXdenote_symm.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pgen 0 2 (Some (inl (false, 0%R))))) =>
  exact (zx_denote_symm_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pgen 2 0 (Some (inl (false, 0%R))))) =>
  exact (zx_denote_symm_cap) : typeclass_instances.

(*
#[export] Hint Extern 0 (DiagramDenote (n_cup ?n) _) =>
  exact (zx_denote_symm_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (n_cap ?n) _) =>
  exact (zx_denote_symm_cup n) : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pstack ?p ?p')) =>
  notypeclasses refine (zx_denote_symm_stack _ _ p p' _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pcompose ?p ?p')) =>
  notypeclasses refine (zx_denote_symm_compose _ _ p p' _ _) : typeclass_instances.

(* #[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike)
  (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_denote_symm_scale c n m val _ _): typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pswap 1 1)) =>
  exact (zx_denote_symm_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pswap ?n ?m)) =>
  exact (zx_denote_symm_zx_comm n m) : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ ([str inr (Swap 1 1)])) =>
  exact (zx_denote_symm_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ ([str inr (Swap ?n ?m)])) =>
  exact (zx_denote_symm_zx_comm n m) : typeclass_instances.

Ltac setup_zxsrw_lhs lem match_number :=
  etransitivity; [
    (
    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_monog_quote_rewrite_correct
          _ _ _ _ _  (ZX_SymmetricG_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end))|].


Ltac zxsviz :=
  SizedProQuote.prop_visualize_goal ZX_SymmetricG_ProLike.

Ltac zxsviz_lhs :=
  SizedProQuote.prop_visualize_lhs ZX_SymmetricG_ProLike.

Ltac zxsviz_rhs :=
  SizedProQuote.prop_visualize_rhs ZX_SymmetricG_ProLike.

(* Redefine this to enable/disable printing after rewriting *)
Ltac zxsrw_visualize_after :=
  zxsviz.

Ltac zxsrw_lhs lem match_number :=

  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_monog_quote_rewrite_correct
          _ _ _ _ _  (ZX_SymmetricG_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _ _ _ _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _ _ _) as Hrw;
    (do 3 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxsrw_rhs lem match_number :=
  symmetry;
  zxsrw_lhs lem match_number;
  symmetry.

Ltac zxsrw lem match_number :=
  zxsrw_lhs lem match_number || zxsrw_rhs lem match_number.


Tactic Notation "zxsrw_lhs" uconstr(lem) "at" constr(n) :=
  zxsrw_lhs lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw_lhs" uconstr(lem) :=
  zxsrw_lhs lem at O.

Tactic Notation "zxsrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw_lhs (symmetry lem) at n.

Tactic Notation "zxsrw_lhs" "<-" uconstr(lem) :=
  zxsrw_lhs (symmetry lem).

Tactic Notation "zxsrw_rhs" uconstr(lem) "at" constr(n) :=
  zxsrw_rhs lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw_rhs" uconstr(lem) :=
  zxsrw_rhs lem at O.

Tactic Notation "zxsrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw_rhs (symmetry lem) at n.

Tactic Notation "zxsrw_rhs" "<-" uconstr(lem) :=
  zxsrw_rhs (symmetry lem).

Tactic Notation "zxsrw" uconstr(lem) "at" constr(n) :=
  zxsrw lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw" uconstr(lem) :=
  zxsrw lem at O.

Tactic Notation "zxsrw" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw (symmetry lem) at n.

Tactic Notation "zxsrw" "<-" uconstr(lem) :=
  zxsrw (symmetry lem).

  (* Redefine this to enable/disable printing after cleaning *)
Ltac zxsclean_visualize_after :=
  zxsviz.

Ltac zxsclean_lhs_aux :=
  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (LawfulProLike_PRO_monog_quote_clean_correct
          _ _ _ _ _  (ZX_SymmetricG_lawpro)
          (interp_discrete_hg_inhab lv) tgt) as Hrw
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "simplified term could not be extracted from graph! Please report this error. "
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxsclean_lhs :=
  zxsclean_lhs_aux;
  zxsclean_visualize_after.

Ltac zxsclean_rhs :=
  symmetry; zxsclean_lhs_aux; symmetry;
  zxsclean_visualize_after.

Ltac zxsclean := zxsclean_lhs_aux; zxsclean_rhs.

Ltac zxscat_visualize_before :=
  zxsviz.

Ltac zxscat :=
  zxscat_visualize_before;
  (unshelve

  (
  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  evar (l : list ZXCVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    specialize (LawfulProLike_PRO_quote_test_correct
        _ _ _ _ _  (ZX_SymmetricG_lawpro)
        (interp_discrete_hg_inhab lv) lhs rhs) as Hrw
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  (tryif timeout 3 (specialize (Hrw _ _ _ _)) then idtac else
    fail "Timed out trying to quote goal! Have you declared all necessary instances?");
  epose proof (Hrw _ _) as Hrw;
  (do 2 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
  tspecialize Hrw;
  [vm_compute;
  lazymatch goal with
  | |- true = true => reflexivity
  | |- false = true => fail "terms are not isomorphic! (as hypergraphs)"
  end
  | ];
  apply Hrw)); exact nil.





Module Examples.




Theorem hopf_rule_Z_X :
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  apply prop_by_iff_zx_scale.
  split; [|intros ?%(f_equal fst); cbn in *; lra].
  zxsviz.
  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r_fwd.
  rewrite cast_id_eq.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  replace (0%R) with (0 + 0)%R by lra.
  zxsrw <- (@Z_spider_1_1_fusion 0 2 0 0).
  rewrite <- X_spider_1_1_fusion.
  replace (0 + 0)%R with 0%R by lra.
  zxsrw (to_gadget (proportional_by_sym bi_algebra_rule_Z_X)).

  unshelve (rewrite (X_wrap_under_bot_right 1)); [lia..|].



  (* zxsclean_lhs. *)
  (* rewrite cup_Z. *)


  zxsrw_lhs (to_gadget Z_state_0_copy 2 eq_refl eq_refl).

  rewrite <- Z_0_is_wire at 1.
  zxsrw (symmetry (@Z_add_l 0 1 0 0 0 0)).
  rewrite 2 Rplus_0_r.
  zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
  rewrite Rplus_0_r.
  zxsrw (cup_pullthrough_top (X 1 0 0) —).
  rewrite <- zx_of_const_mult'.
  replace (zx_of_const _)%C with (zx_of_const (/ C2))%C 
    by (apply (f_equal zx_of_const); cbn; autorewrite with RtoC_db; C_field).
  zxscat.
Qed.


Theorem hopf_rule_Z_X_vert n m top bot α β prf :
  Z n (top + 2) α ↕ n_wire bot ⟷
  cast _ _ prf eq_refl
    (n_wire top ↕ X (2 + bot) m β) ∝[/ C2] Z n top α ↕ X bot m β.
Proof.
  Admitted.

Theorem bi_algebra_rule_X_over_Z :
  X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ ⨉
  ⟷ (X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0) ∝[/ (√2)%R]
  Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0).
Proof.
  zxsymmetry.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].

  rewrite (Z_wrap_over_top_right).
  rewrite (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl).

  zxsrw_lhs (to_gadget bi_algebra_rule_X_Z).

  assert (Hrw1 : X 1 2 0 ∝= — ↕ ⊂ ⟷ (— ↕ X 1 2 0 ↕ —) ⟷ (⊃ ↕ n_wire 2)). 1:{
    rewrite cup_X, cap_X.
    zxsrw (dominated_X_spider_fusion_top_left 2 0 1 0 0 0).
    rewrite Rplus_0_l.
    zxsrw (X_spider_fusion_bot_left_top_right 1 0 2 0 0 0 0 eq_refl eq_refl).
    now rewrite Rplus_0_l.
  }
  (* rewrite <- cap_Z, <- cup_Z. *)
  assert (Hrw2 : Z 2 1 0 ∝= (n_wire 2 ↕ ⊂) ⟷ (— ↕ Z 2 1 0 ↕ —) ⟷ (⊃ ↕ —)). 1:{
    zxsrw (Z_spider_fusion_bot_left_top_right 1 0 1 0 1 0 0 eq_refl eq_refl).
    rewrite Rplus_0_l.
    zxsrw_rhs (Z_spider_fusion_bot_left_top_right 1 0 1 1 0 0 0 eq_refl eq_refl).
    now rewrite Rplus_0_l.
  }
  rewrite Hrw1 at 1.
  rewrite Hrw2 at 2.
  Fail zxscat.
Admitted.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  rewrite notc_is_swapp_cnot.
  zxscat.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxscat.
Qed.

Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split. 2:{
    apply nonzero_div_nonzero, Cmult_neq_0; nonzero.
  }

  rewrite cnot_is_swapp_notc at 2.
  rewrite notc_is_notc_r.
  zxsrw (to_gadget bi_algebra_rule_X_over_Z).

  zxsrw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxsrw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxsrw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxsrw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr.
  zxscat.
Qed.

End Examples.

End ZXsymm.







Module ZXauto.

Export GeneratorNotations.

Section ZXquote_auto.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_Autonomous_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_quote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_quote_auto_n_wire n : Quote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_auto_wire : Quote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_quote_auto_empty : Quote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_auto_zx_comm n m : Quote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_auto_swap : Quote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.


Lemma zx_quote_auto_n_cap n : Quote (n_cup n) (Pcap n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcap].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv].
  - now rewrite n_cup_0_empty.
  - now rewrite n_cup_1_cup.
  - done.
Qed.

Lemma zx_quote_auto_n_cup n : Quote (n_cap n) (Pcup n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcup].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv n_cap].
  - now rewrite n_cap_0_empty.
  - now rewrite n_cap_1_cap.
  - done.
Qed.


Lemma zx_quote_auto_cup : Quote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_quote_auto_cap : Quote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_auto_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_auto_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_quote_auto_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_quote_auto_Z n m α :
  Quote (Z n m α) (Pgen n m (Some (inl (false, α)))) | 1.
Proof.
  constructor; done.
Qed.

#[export] Instance zx_quote_auto_X n m α :
  Quote (X n m α) (Pgen n m (Some (inl (true, α)))) | 1.
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_auto_Z_cup :
  Quote (Z 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

#[export] Instance zx_quote_auto_Z_cap :
  Quote (Z 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.

#[export] Instance zx_quote_auto_X_cup :
  Quote (X 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_X.
  done.
Qed.

#[export] Instance zx_quote_auto_X_cap :
  Quote (X 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_X.
  done.
Qed.

#[export] Instance zx_quote_auto_Z_wire :
  Quote (Z 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite Z_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_auto_X_wire :
  Quote (X 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite X_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_auto_H : Quote (Box) (Pgen 1 1 None).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_quote_auto_const c : Quote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_auto_scale c {n m} (zx : ZX n m) ap :
  Quote zx ap -> Quote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_quote_auto_stack 0 0); apply _.
Qed.

End ZXquote_auto.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) ⊂ _) =>
  exact (zx_quote_auto_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) ⊃ _) =>
  exact (zx_quote_auto_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (n_cup ?n) _) =>
  exact (zx_quote_auto_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (n_cap ?n) _) =>
  exact (zx_quote_auto_n_cup n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (?zx ↕ ?zx') _) =>
  notypeclasses refine (zx_quote_auto_stack zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (?zx ⟷ ?zx') _) =>
  notypeclasses refine (zx_quote_auto_compose zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_quote_auto_scale c n m val _ _): typeclass_instances.

#[export] Hint Extern 10 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (?val) _) =>
  progress first [unfold val|simpl] : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Autonomous_ProLike) (zx_comm ?n ?m) _) =>
  exact (zx_quote_auto_zx_comm n m) : typeclass_instances.





Section ZXdenote_auto.

Local Set Typeclasses Unique Instances.

Local Notation Denote := (DiagramDenote (ProD:=ZX_Autonomous_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_denote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_denote_auto_n_wire n : Denote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_auto_wire : Denote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_denote_auto_empty : Denote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_auto_zx_comm n m : Denote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_auto_swap : Denote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.

Lemma zx_denote_auto_n_cap n : Denote (n_cup n) (Pcap n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_auto_n_cap.
Qed.

Lemma zx_denote_auto_n_cup n : Denote (n_cap n) (Pcup n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_auto_n_cup.
Qed.


Lemma zx_denote_auto_cup : Denote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_denote_auto_cap : Denote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_auto_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_denote_auto_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_denote_auto_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Denote zx ap ->
  Denote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_denote_auto_Z n m α : Denote (Z n m α) (Pgen n m (Some (inl (false, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_auto_X n m α : Denote (X n m α) (Pgen n m (Some (inl (true, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_auto_H : Denote (Box) (Pgen 1 1 None).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_denote_auto_const c : Denote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_auto_scale c {n m} (zx : ZX n m) ap :
  Denote zx ap -> Denote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_denote_auto_stack 0 0); apply _.
Qed.

End ZXdenote_auto.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pcup 1)) =>
  exact (zx_denote_auto_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pcap 1)) =>
  exact (zx_denote_auto_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inr (Cup 1)])) =>
  exact (zx_denote_auto_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inr (Cap 1)])) =>
  exact (zx_denote_auto_cap) : typeclass_instances.


#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pcup ?n)) =>
  exact (zx_denote_auto_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pcap ?n)) =>
  exact (zx_denote_auto_n_cap n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inr (Cup ?n)])) =>
  exact (zx_denote_auto_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inr (Cap ?n)])) =>
  exact (zx_denote_auto_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pstack ?p ?p')) =>
  notypeclasses refine (zx_denote_auto_stack _ _ p p' _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pcompose ?p ?p')) =>
  notypeclasses refine (zx_denote_auto_compose _ _ p p' _ _) : typeclass_instances.

(* #[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike)
  (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_denote_auto_scale c n m val _ _): typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pswap 1 1)) =>
  exact (zx_denote_auto_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ (Pswap ?n ?m)) =>
  exact (zx_denote_auto_zx_comm n m) : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inl (inr (Swap 1 1))])) =>
  exact (zx_denote_auto_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Autonomous_ProLike) _ ([str inl (inr (Swap ?n ?m))])) =>
  exact (zx_denote_auto_zx_comm n m) : typeclass_instances.



Ltac zxaviz :=
  SizedProQuote.aprop_visualize_goal ZX_Autonomous_ProLike.

Ltac zxaviz_lhs :=
  SizedProQuote.aprop_visualize_lhs ZX_Autonomous_ProLike.

Ltac zxaviz_rhs :=
  SizedProQuote.aprop_visualize_rhs ZX_Autonomous_ProLike.

Ltac zxarw_visualize_after :=
  zxaviz.

Ltac setup_zxarw_lhs lem match_number quotient_number :=
  etransitivity; [
    (
    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_bimonog_quote_rewrite_correct
          _ _ _ _ _  (ZX_Autonomous_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end))|].

Ltac zxarw_lhs lem match_number quotient_number :=

  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_bimonog_quote_rewrite_correct
          _ _ _ _ _  (ZX_Autonomous_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _ _ _ _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _ _ _) as Hrw;
    (do 3 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxarw_rhs lem match_number quotient_number :=
  symmetry;
  zxarw_lhs lem match_number quotient_number;
  symmetry.

Ltac zxarw lem match_number quotient_number :=
  zxarw_lhs lem match_number quotient_number || zxarw_rhs lem match_number quotient_number.


Tactic Notation "zxarw_lhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw_lhs lem n q;
  zxarw_visualize_after.

Tactic Notation "zxarw_lhs" uconstr(lem) "at" constr(n) :=
  zxarw_lhs lem at n quotient O.

Tactic Notation "zxarw_lhs" uconstr(lem) :=
  zxarw_lhs lem at O.

Tactic Notation "zxarw_lhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw_lhs (symmetry lem) at n quotient q.

Tactic Notation "zxarw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxarw_lhs (symmetry lem) at n.

Tactic Notation "zxarw_lhs" "<-" uconstr(lem) :=
  zxarw_lhs (symmetry lem).


Tactic Notation "zxarw_rhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw_rhs lem n q;
  zxarw_visualize_after.

Tactic Notation "zxarw_rhs" uconstr(lem) "at" constr(n) :=
  zxarw_rhs lem at n quotient O.

Tactic Notation "zxarw_rhs" uconstr(lem) :=
  zxarw_rhs lem at O.

Tactic Notation "zxarw_rhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw_rhs (symmetry lem) at n quotient q.

Tactic Notation "zxarw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxarw_rhs (symmetry lem) at n.

Tactic Notation "zxarw_rhs" "<-" uconstr(lem) :=
  zxarw_rhs (symmetry lem).


Tactic Notation "zxarw" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw lem n q;
  zxarw_visualize_after.

Tactic Notation "zxarw" uconstr(lem) "at" constr(n) :=
  zxarw lem at n quotient O.

Tactic Notation "zxarw" uconstr(lem) :=
  zxarw lem at O.

Tactic Notation "zxarw" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxarw (symmetry lem) at n quotient q.

Tactic Notation "zxarw" "<-" uconstr(lem) "at" constr(n) :=
  zxarw (symmetry lem) at n.

Tactic Notation "zxarw" "<-" uconstr(lem) :=
  zxarw (symmetry lem).


Ltac zxaclean_visualize_after :=
  zxaviz.


Ltac zxaclean_lhs_aux :=
  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (LawfulProLike_PRO_bimonog_quote_clean_correct
          _ _ _ _ _  (ZX_Autonomous_lawpro)
          (interp_discrete_hg_inhab lv) tgt) as Hrw
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "simplified term could not be extracted from graph! Please report this error. "
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxaclean_lhs :=
  zxaclean_lhs_aux;
  zxaclean_visualize_after.


Ltac zxaclean_rhs :=
  symmetry; zxaclean_lhs_aux; symmetry;
  zxaclean_visualize_after.

Ltac zxaclean := zxaclean_lhs_aux; zxaclean_rhs.

Ltac zxacat_visualize_before :=
  zxaviz.

Ltac zxacat :=
  zxacat_visualize_before;
  (unshelve

  (
  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  evar (l : list ZXCVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    specialize (LawfulProLike_PRO_quote_test_correct
        _ _ _ _ _  (ZX_Autonomous_lawpro)
        (interp_discrete_hg_inhab lv) lhs rhs) as Hrw
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  (tryif timeout 3 (specialize (Hrw _ _ _ _)) then idtac else
    fail "Timed out trying to quote goal! Have you declared all necessary instances?");
  epose proof (Hrw _ _) as Hrw;
  (do 2 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
  tspecialize Hrw;
  [vm_compute;
  lazymatch goal with
  | |- true = true => reflexivity
  | |- false = true => fail "terms are not isomorphic! (as hypergraphs)"
  end
  | ];
  apply Hrw)); exact nil.


Module Examples.




Theorem hopf_rule_Z_X :
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  apply prop_by_iff_zx_scale.
  split; [|intros ?%(f_equal fst); cbn in *; lra].
  zxaviz.
  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r_fwd.
  rewrite cast_id_eq.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  replace (0%R) with (0 + 0)%R by lra.
  zxarw_lhs (symmetry (@Z_spider_1_1_fusion 0 2 0 0)).

  rewrite <- X_spider_1_1_fusion.
  replace (0 + 0)%R with 0%R by lra.

  zxarw_lhs (to_gadget (proportional_by_sym bi_algebra_rule_Z_X)).


  unshelve (rewrite (X_wrap_under_bot_right 1)); [lia..|].




  (* zxaclean_lhs. *)
  (* rewrite cup_Z. *)


  zxarw_lhs (to_gadget Z_state_0_copy 2 eq_refl eq_refl).

  rewrite <- Z_0_is_wire at 1.
  zxarw (symmetry (@Z_add_l 0 1 0 0 0 0)) at 1.
  rewrite 2 Rplus_0_r.
  zxarw (@Z_spider_1_1_fusion 0 2 0 0).
  rewrite Rplus_0_r.
  zxarw (cup_pullthrough_top (X 1 0 0) —).
  rewrite 2 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  replace (_ * / √ 2)%C with (/ C2)%C
    by (cbn; autorewrite with RtoC_db; C_field).
  zxacat.
Qed.


Theorem hopf_rule_Z_X_vert n m top bot α β prf :
  Z n (top + 2) α ↕ n_wire bot ⟷
  cast _ _ prf eq_refl
    (n_wire top ↕ X (2 + bot) m β) ∝[/ C2] Z n top α ↕ X bot m β.
Proof.
  Admitted.

Theorem bi_algebra_rule_X_over_Z :
  X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ ⨉
  ⟷ (X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0) ∝[/ (√2)%R]
  Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0).
Proof.
  zxsymmetry.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].

  rewrite (Z_wrap_over_top_right).
  rewrite (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl).

  zxarw_lhs (to_gadget bi_algebra_rule_X_Z).

  assert (Hrw1 : X 1 2 0 ∝= — ↕ ⊂ ⟷ (— ↕ X 1 2 0 ↕ —) ⟷ (⊃ ↕ n_wire 2)). 1:{
    rewrite cup_X, cap_X.
    zxarw_rhs (dominated_X_spider_fusion_top_left 2 0 1 0 0 0).
    rewrite Rplus_0_l.
    zxarw (X_spider_fusion_bot_left_top_right 1 0 2 0 0 0 0 eq_refl eq_refl) at 0.
    now rewrite Rplus_0_l.
  }
  (* rewrite <- cap_Z, <- cup_Z. *)
  assert (Hrw2 : Z 2 1 0 ∝= (n_wire 2 ↕ ⊂) ⟷ (— ↕ Z 2 1 0 ↕ —) ⟷ (⊃ ↕ —)). 1:{
    zxarw_rhs (Z_spider_fusion_bot_left_top_right 1 0 1 0 1 0 0 eq_refl eq_refl).
    rewrite Rplus_0_l.
    zxarw_rhs (Z_spider_fusion_bot_left_top_right 1 0 1 1 0 0 0 eq_refl eq_refl).
    now rewrite Rplus_0_l.
  }
  rewrite Hrw1 at 2.
  rewrite Hrw2 at 2.
  zxacat.
Qed.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  rewrite notc_is_swapp_cnot.
  zxacat.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxacat.
Qed.

Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split. 2:{
    apply nonzero_div_nonzero, Cmult_neq_0; nonzero.
  }

  rewrite cnot_is_swapp_notc at 2.
  rewrite notc_is_notc_r.
  zxarw (to_gadget bi_algebra_rule_X_over_Z).

  zxarw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxarw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxarw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxarw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr.
  zxacat.
Qed.

End Examples.

End ZXauto.











Module ZXfrob.

Section ZXquote_frob.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_Frobenius_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_quote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_quote_frob_n_wire n : Quote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_frob_wire : Quote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_quote_frob_empty : Quote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_frob_zx_comm n m : Quote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_frob_swap : Quote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.


Lemma zx_quote_frob_n_cap n : Quote (n_cup n) (Pcap n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcap].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv].
  - now rewrite n_cup_0_empty.
  - now rewrite n_cup_1_cup.
  - done.
Qed.

Lemma zx_quote_frob_n_cup n : Quote (n_cap n) (Pcup n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcup].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv n_cap].
  - now rewrite n_cap_0_empty.
  - now rewrite n_cap_1_cap.
  - done.
Qed.


Lemma zx_quote_frob_cup : Quote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_quote_frob_cap : Quote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_frob_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_frob_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_quote_frob_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
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


Lemma PRO_to_diagram_Pdelta_1 n m : n + m <> O ->
  PRO_to_diagram (Pdelta 1 n m) ≡ Some (Z _ _ 0).
Proof.
  cbn.
  intros Hnm.
  f_equiv.
  rewrite ZX_copy_1.
  rewrite cast_Z.
  done.
Qed.

Lemma PRO_to_diagram_Pdelta1 n m :
  PRO_to_diagram (Pdelta1 n m) ≡ Some (Z _ _ 0).
Proof.
  done.
Qed.

Lemma zx_quote_frob_Z_0 n m : Quote (Z n m 0) (Pdelta1 n m).
Proof.
  constructor.
  now apply PRO_to_diagram_Pdelta1.
Qed.

Lemma zx_quote_frob_Z_add (n m : nat) α β d d' :
  Quote (Z 1 0 β) d -> Quote (Z 1 0 α) d' ->
  Quote (Z n m (α + β))
  (Pdelta1 n (S (S m)) ;; d * d' * Pid m).
Proof.
  intros Hd Hd'.
  rewrite Z_push_out_phase_gadget'.
  rewrite (Z_push_out_phase_gadget n).
  rewrite ComposeRules.compose_assoc.
  rewrite <- (pull_out_top (Z 1 0 β)).
  rewrite (stack_assoc_back_fwd (Z 1 0 β) (Z 1 0 α)), cast_id_eq.
  apply zx_quote_frob_compose.
  - apply zx_quote_frob_Z_0.
  - apply (@zx_quote_frob_stack (1 + 1) (0 + 0) m m); typeclasses eauto.
Qed.

Lemma zx_quote_frob_Z_phase α :
  Quote (Z 1 0 α) ([gen (Some (inl (false, α))) 1 0]).
Proof.
  done.
Qed.

Lemma zx_quote_frob_Z n m α : DiagramQuote (Z n m α)
  (Pdelta1 n (S m) ;; [gen (Some (inl (false, α))) 1 0] * Pid m).
Proof.
  rewrite Z_push_out_phase_gadget.
  pose proof zx_quote_frob_Z_phase.
  pose proof zx_quote_frob_Z_0.
  change (S m) with (1 + m).
  eauto with zarith typeclass_instances.
Qed.

#[export] Instance zx_quote_frob_h_stack n : Quote (n_stack1 n Box)
  ([gen None n n]) | 1.
Proof.
  constructor.
  cbn.
  case_decide; [|done].
  rewrite cast_id_eq.
  done.
Qed.

#[export] Instance zx_quote_frob_h : Quote Box
  ([gen None 1 1]).
Proof.
  rewrite <- nstack1_1.
  apply _.
Qed.

Lemma zx_quote_frob_X n m α d :
  Quote (n_stack1 n Box ⟷ (Z n m α ⟷ n_stack1 m Box))
    d -> Quote (X n m α) d.
Proof.
  apply DiagramQuote_proper_equiv, reflexivity.
  rewrite <- colorswap_is_bihadamard.
  done.
Qed.











#[export] Instance zx_quote_frob_Z_cup :
  Quote (Z 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

#[export] Instance zx_quote_frob_Z_cap :
  Quote (Z 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.
(*
#[export] Instance zx_quote_frob_X_cup :
  Quote (X 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_X.
  done.
Qed.

#[export] Instance zx_quote_frob_X_cap :
  Quote (X 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_X.
  done.
Qed. *)

#[export] Instance zx_quote_frob_Z_wire :
  Quote (Z 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite Z_0_is_wire, <- wire_to_n_wire.
Qed.

(* #[export] Instance zx_quote_frob_X_wire :
  Quote (X 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite X_0_is_wire, <- wire_to_n_wire.
Qed. *)


#[export] Instance zx_quote_frob_const c : Quote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_frob_scale c {n m} (zx : ZX n m) ap :
  Quote zx ap -> Quote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_quote_frob_stack 0 0); apply _.
Qed.

Lemma zx_quote_frob_Z_gen n m α :
  Quote (Z n m α) (Pdelta1 n (S m) ;; Pgen 1 0 (Some (inl (false, α))) * Pid m).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite <- Z_push_out_phase_gadget.
  done.
Qed.

End ZXquote_frob.


Ltac zx_quote_frob_Z_tac_step :=
  match goal with
  | |- DiagramQuote (Z ?n ?m (?alpha + ?beta)) _ =>
    notypeclasses refine (zx_quote_frob_Z_add n m alpha beta _ _ _ _)
  | |- DiagramQuote (Z ?n ?m 0) _ =>
    notypeclasses refine (zx_quote_frob_Z_0 n m _); lia
  | |- DiagramQuote (Z 1 0 ?alpha)_  =>
    notypeclasses refine (zx_quote_frob_Z_phase alpha)
  | |- DiagramQuote (Z ?n ?m ?alpha) _ =>
    exact (zx_quote_frob_Z n m alpha)
  end.

Ltac zx_quote_frob_Z_tac := zx_quote_frob_Z_tac_step; repeat zx_quote_frob_Z_tac_step.

(*
#[export] Hint Extern 0 (DiagramQuote (Z ?n ?m ?alpha) _) =>
  solve [zx_quote_frob_Z_tac|let _ := match goal with
    |- ?G => idtac "FAIL ON" G end in idtac] : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (Z ?n ?m 0) _) =>
  exact (zx_quote_frob_Z_0 n m) : typeclass_instances.


#[export] Hint Extern 1 (DiagramQuote (Z ?n ?m ?alpha) _) =>
  exact (zx_quote_frob_Z_gen n m alpha) : typeclass_instances.

#[export] Hint Extern 3 (DiagramQuote (X ?n ?m ?α) _) =>
  notypeclasses refine (zx_quote_frob_X n m α _ _);
  cbn : typeclass_instances.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) ⊂ _) =>
  exact (zx_quote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) ⊃ _) =>
  exact (zx_quote_frob_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (n_cup ?n) _) =>
  exact (zx_quote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (n_cap ?n) _) =>
  exact (zx_quote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (?zx ↕ ?zx') _) =>
  notypeclasses refine (zx_quote_frob_stack zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (?zx ⟷ ?zx') _) =>
  notypeclasses refine (zx_quote_frob_compose zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_quote_frob_scale c n m val _ _): typeclass_instances.

#[export] Hint Extern 10 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (?val) _) =>
  progress first [unfold val|simpl] : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_Frobenius_ProLike) (zx_comm ?n ?m) _) =>
  exact (zx_quote_frob_zx_comm n m) : typeclass_instances.





Section ZXdenote_frob.

Local Set Typeclasses Unique Instances.

Local Notation Denote := (DiagramDenote (ProD:=ZX_Frobenius_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_denote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_denote_frob_n_wire n : Denote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_frob_wire : Denote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_denote_frob_empty : Denote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_frob_zx_comm n m : Denote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_frob_swap : Denote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.

Lemma zx_denote_frob_n_cap n : Denote (n_cup n) (Pcap n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_frob_n_cap.
Qed.

Lemma zx_denote_frob_n_cup n : Denote (n_cap n) (Pcup n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_frob_n_cup.
Qed.


Lemma zx_denote_frob_cup : Denote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_denote_frob_cap : Denote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_frob_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_denote_frob_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_denote_frob_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Denote zx ap ->
  Denote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_denote_frob_Z n m α : Denote (Z n m α) (Pgen n m (Some (inl (false, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_frob_X n m α : Denote (X n m α) (Pgen n m (Some (inl (true, α)))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_frob_H : Denote (Box) (Pgen 1 1 None).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_denote_frob_const c : Denote (zx_of_const c) (Pgen 0 0 (Some (inr c))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_frob_scale c {n m} (zx : ZX n m) ap :
  Denote zx ap -> Denote (zx_scale c zx) (Pgen 0 0 (Some (inr c)) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_denote_frob_stack 0 0); apply _.
Qed.


Lemma zx_denote_frob_Pdelta_1 n m : n + m <> O ->
  Denote (Z (n * 1) (m * 1) 0)
  (Pstruct _ _ (inr (Delta 1 n m))).
Proof.
  constructor.
  rewrite PRO_to_diagram_Pdelta_1 by done.
  done.
Qed.

Lemma zx_denote_frob_Pdelta_0 :
  Denote (Z 0 0 0)
  (Pstruct _ _ (inr (Delta 1 0 0))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite ZX_copy_1, cast_id_eq.
  done.
Qed.

Lemma zx_denote_frob_Pdelta1 n m : Denote (Z n m 0) (Pdelta1 n m).
Proof.
  constructor; done.
Qed.

End ZXdenote_frob.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcup 1)) =>
  exact (zx_denote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcap 1)) =>
  exact (zx_denote_frob_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cup 1))])) =>
  exact (zx_denote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cap 1))])) =>
  exact (zx_denote_frob_cap) : typeclass_instances.


#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcup ?n)) =>
  exact (zx_denote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcap ?n)) =>
  exact (zx_denote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cup ?n))])) =>
  exact (zx_denote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cap ?n))])) =>
  exact (zx_denote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pstack ?p ?p')) =>
  notypeclasses refine (zx_denote_frob_stack _ _ p p' _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcompose ?p ?p')) =>
  notypeclasses refine (zx_denote_frob_compose _ _ p p' _ _) : typeclass_instances.

(* #[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike)
  (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_denote_frob_scale c n m val _ _): typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pswap 1 1)) =>
  exact (zx_denote_frob_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pswap ?n ?m)) =>
  exact (zx_denote_frob_zx_comm n m) : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inl (inr (Swap 1 1)))])) =>
  exact (zx_denote_frob_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inl (inr (Swap ?n ?m)))])) =>
  exact (zx_denote_frob_zx_comm n m) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta 1 ?n ?m)])) =>
  let H := fresh in
  tryif assert (H : n + m <> O) by lia then
    exact (zx_denote_frob_Pdelta_1 n m H)
  else fail : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta 1 0 0)])) =>
  exact zx_denote_frob_Pdelta_0 : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta1 ?n ?m)])) =>
  exact (zx_denote_frob_Pdelta1 n m) : typeclass_instances.


Ltac setup_zxfrw_lhs lem match_number quotient_number :=
  etransitivity; [
    (
    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_frobenius_quote_rewrite_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end))|].

Ltac zxfrw_lhs lem match_number quotient_number :=

  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_frobenius_quote_rewrite_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _ _ _ _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _ _ _) as Hrw;
    (do 3 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxfrw_rhs lem match_number quotient_number :=
  symmetry;
  zxfrw_lhs lem match_number quotient_number;
  symmetry.

Ltac zxfrw lem match_number quotient_number :=
  zxfrw_lhs lem match_number quotient_number || zxfrw_rhs lem match_number quotient_number.


Tactic Notation "zxfrw_lhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_lhs lem n q.

Tactic Notation "zxfrw_lhs" uconstr(lem) "at" constr(n) :=
  zxfrw_lhs lem at n quotient O.

Tactic Notation "zxfrw_lhs" uconstr(lem) :=
  zxfrw_lhs lem at O.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_lhs (symmetry lem) at n quotient q.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw_lhs (symmetry lem) at n.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) :=
  zxfrw_lhs (symmetry lem).


Tactic Notation "zxfrw_rhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_rhs lem n q.

Tactic Notation "zxfrw_rhs" uconstr(lem) "at" constr(n) :=
  zxfrw_rhs lem at n quotient O.

Tactic Notation "zxfrw_rhs" uconstr(lem) :=
  zxfrw_rhs lem at O.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_rhs (symmetry lem) at n quotient q.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw_rhs (symmetry lem) at n.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) :=
  zxfrw_rhs (symmetry lem).


Tactic Notation "zxfrw" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw lem n q.

Tactic Notation "zxfrw" uconstr(lem) "at" constr(n) :=
  zxfrw lem at n quotient O.

Tactic Notation "zxfrw" uconstr(lem) :=
  zxfrw lem at O.

Tactic Notation "zxfrw" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw (symmetry lem) at n quotient q.

Tactic Notation "zxfrw" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw (symmetry lem) at n.

Tactic Notation "zxfrw" "<-" uconstr(lem) :=
  zxfrw (symmetry lem).


Ltac zxfmrw_lhs rwe :=
  (* let rwe := constr:(![rw {box_compose}]) in *)

  etransitivity; [
    (unshelve
    (
    etransitivity;
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    specialize (LawfulProLike_PRO_frobenius_quote_multi_rewrite_correct
      (ZX_Frobenius_lawpro)
      (interp_discrete_hg_inhab lv)) as Hrw;
    epose proof (Hrw rwe _ _ _) as Hrw;
    (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac else
      fail "Timed out trying to quote the rewrite rule!");

    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (Hrw _ _ tgt)
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) ||
      fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw; [
      vm_compute;
      lazymatch goal with
      | |- ?R (inl _) (inl _) => reflexivity
      | |- ?R (inr ?e) _ => fail
        "rewriting failed, with the following error: " e
      end
      | ];
      (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

      (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Timed out trying to denote result! Have you declared all necessary instances?");

      apply Hrw)); exact nil|].

Ltac zxfmrw_rhs rwe :=
  symmetry;
  zxfmrw_lhs rwe;
  symmetry.

Ltac zxfmrw rwe :=
  zxfmrw_lhs rwe + zxfmrw_rhs rwe.


Tactic Notation "zxfmrw_lhs" uconstr(rwe) :=
  zxfmrw_lhs rwe.

Tactic Notation "zxfmrw_rhs" uconstr(rwe) :=
  zxfmrw_rhs rwe.

Tactic Notation "zxfmrw" uconstr(rwe) :=
  zxfmrw rwe.


Ltac zxfclean_lhs :=
  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (LawfulProLike_PRO_frobenius_quote_clean_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
          (interp_discrete_hg_inhab lv) tgt) as Hrw
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "simplified term could not be extracted from graph! Please report this error. "
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxfclean_rhs :=
  symmetry; zxfclean_lhs; symmetry.

Ltac zxfclean := zxfclean_lhs; zxfclean_rhs.

Ltac zxfcat :=
  (unshelve

  (
  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  evar (l : list ZXCVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    specialize (LawfulProLike_PRO_quote_test_correct
        _ _ _ _ _  (ZX_Frobenius_lawpro)
        (interp_discrete_hg_inhab lv) lhs rhs) as Hrw
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  (tryif timeout 3 (specialize (Hrw _ _ _ _)) then idtac else
    fail "Timed out trying to quote goal! Have you declared all necessary instances?");
  epose proof (Hrw _ _) as Hrw;
  (do 2 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
  tspecialize Hrw;
  [vm_compute;
  lazymatch goal with
  | |- true = true => reflexivity
  | |- false = true => fail "terms are not isomorphic! (as hypergraphs)"
  end
  | ];
  apply Hrw)); exact nil.


Module Examples.


Lemma bi_algebra_rule_X_Z_gen n n' m m' α α' β β' :
  Z (n + n') 1 (α + α') ⟷ X 1 (m + m') (β + β') ∝[√ 2]
  (Z n 1 α ↕ Z n' 1 α') ⟷ (
    (X 1 2 0 ↕ X 1 2 0 ⟷ (— ↕ ⨉ ↕ —) ⟷ (Z 2 1 0 ↕ Z 2 1 0))
  ) ⟷ (X 1 m β ↕ X 1 m' β').
Proof.
  rewrite <- (Rplus_0_r α).
  rewrite Z_add_l.
  rewrite <- (Rplus_0_r β).
  rewrite X_add_r.
  rewrite ComposeRules.compose_assoc, <- (ComposeRules.compose_assoc (Z 2 1 0)).
  zxrewrite bi_algebra_rule_X_Z.
  zxrefl.
  rewrite 2 Rplus_0_r.
  rewrite <- !ComposeRules.compose_assoc.
  f_equiv.
  rewrite !ComposeRules.compose_assoc.
  f_equiv.
  rewrite <- !ComposeRules.compose_assoc.
  done.
Qed.

Lemma bi_algebra_rule_Z_X_gen n n' m m' α α' β β' :
  X (n + n') 1 (α + α') ⟷ Z 1 (m + m') (β + β') ∝[√ 2]
  (X n 1 α ↕ X n' 1 α') ⟷ (
    (Z 1 2 0 ↕ Z 1 2 0 ⟷ (— ↕ ⨉ ↕ —) ⟷ (X 2 1 0 ↕ X 2 1 0))
  ) ⟷ (Z 1 m β ↕ Z 1 m' β').
Proof.
  colorswap_of (bi_algebra_rule_X_Z_gen n n' m m' α α' β β').
Qed.


Lemma zx_of_const_mult' (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ⟷ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxfcat.
Qed.

Import ZXsymm ZXauto.

Lemma box_to_transpose : □ ∝= (⊂ ⟷ (— ↕ □)) ↕ — ⟷ (— ↕ ⊃).
Proof.
  rewrite cup_pullthrough_bot_1.
  zxfcat.
Qed.

Theorem hopf_rule_Z_X :
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  apply prop_by_iff_zx_scale.
  split; [|intros ?%(f_equal fst); cbn in *; lra].


  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r_fwd.
  rewrite cast_id_eq.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  rewrite <- (Rplus_0_l 0).
  zxsclean_lhs.
  rewrite <- X_spider_1_1_fusion, <- Z_spider_1_1_fusion.
  rewrite Rplus_0_l.
  zxfrw_lhs (to_gadget (proportional_by_sym bi_algebra_rule_Z_X)) at 0.
  zxfrw_lhs (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl) at 1.
  zxfrw_lhs (to_gadget Z_state_0_copy 2 eq_refl eq_refl).
  cbn.
  rewrite <- zx_of_const_mult'.
  replace (_ * / √ 2)%C with (/ C2)%C by (autorewrite with RtoC_db; C_field).
  rewrite box_to_transpose.
  zxfcat.
Qed.


Theorem hopf_rule_Z_X_vert n m top bot α β prf :
  Z n (top + 2) α ↕ n_wire bot ⟷
  cast _ _ prf eq_refl
    (n_wire top ↕ X (2 + bot) m β) ∝[/ C2] Z n top α ↕ X bot m β.
Proof.
  Admitted.

Theorem bi_algebra_rule_X_over_Z :
  X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ ⨉
  ⟷ (X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0) ∝[/ (√2)%R]
  Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0).
Proof.
  zxsymmetry.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].

  rewrite (Z_wrap_over_top_right).
  rewrite (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl).
  zxsrw_lhs (to_gadget bi_algebra_rule_X_Z).


  assert (Hrw1 : X 1 2 0 ∝= — ↕ ⊂ ⟷ (— ↕ X 1 2 0 ↕ —) ⟷ (⊃ ↕ n_wire 2)). 1:{
    rewrite cup_X, cap_X.
    zxfrw_rhs box_compose.
    zxfrw_rhs box_compose.
    zxfcat.
  }
  rewrite Hrw1 at 2.
  zxfcat.
Qed.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  zxfcat.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxfcat.
Qed.

Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split. 2:{
    apply nonzero_div_nonzero, Cmult_neq_0; nonzero.
  }

  rewrite cnot_is_swapp_notc at 2.
  rewrite notc_is_notc_r.
  zxfrw (to_gadget bi_algebra_rule_X_over_Z).

  zxfrw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  (* rewrite Rplus_0_l. *)
  zxfrw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxfrw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxfrw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr.
  zxfrw box_compose.
  zxfcat.
Qed.

End Examples.

End ZXfrob.























From TensorRocq Require Import BW BWSized SizedProps PropsGraphs SizedPropsGraphs SizedProLike SizedRewriting SizedProQuote.

Open Scope nat_scope.

Definition ZX_tensor_is_Some (asgn : Pmap nat) (n m : btree positive) (t : ZXCVERT) : bool :=
  match t with
  | None => (* H-box stack *) bool_decide (n =@{list positive} m) (* Conservative, but sufficient *)
  | Some (inr _) => (* Constant; need there to be no args *) (bool_decide (n ++ m = []) |||
    default false (l ← join_list ((asgn !!.) <$> (n ++ m)); Some $ forallb (Nat.eqb 0) l))%lazy
  | Some (inl _) => true
  end.

#[export] Instance ZX_sized_ofTensor_testable : SizedOfTensorSomeTestable ZXCVERT ZX :=
  ZX_tensor_is_Some.

#[export, program] Instance ZX_lawful_sized_ofTensor_testable : LawfulSizedOfTensorSomeTestable ZXCVERT ZX.
Next Obligation.
  intros concr n m t fN Hsome HfN.
  destruct t as [[[isX phase] | c]|]; [destruct isX; done|..]; cbn in Hsome.
  - destruct (bool_decide (_ = [])) eqn:Hsome'.
    + apply bool_decide_eq_true in Hsome'.
      assert (Hnm : n =@{list _} [] /\ m =@{list _} []) by now apply app_nil in Hsome'.
      rewrite (btree_size_ext (n:=n) (m:=0)) by apply Hnm.
      rewrite (btree_size_ext (n:=m) (m:=0)) by apply Hnm.
      done.
    + enough (btree_size fN (n + m) = 0) as Hnm by
      (cbn in Hnm; apply Nat.eq_add_0 in Hnm as [-> ->]; done).
      rewrite <- sum_list_with_btree_elems.
      destruct (_ ≫= _) as [b|] eqn:Hb; [|done].
      apply id in Hsome as [= ->].
      apply bind_Some in Hb as (zeros & Hnm & Hzeros).
      apply join_list_Some in Hnm.
      apply (inj Some) in Hzeros.
      apply Is_true_true, forallb_True in Hzeros.
      remember (length zeros) as k eqn:Hk.
      apply (f_equal length) in Hnm as Hk'.
      rewrite 2 length_fmap in Hk'.
      assert (zeros = replicate k 0) as ?; [|rewrite <- Hk' in Hk; subst zeros].
      1:{
        subst k.
        rewrite <- fmap_const.
        symmetry.
        rewrite Forall_forall in Hzeros.
        apply list_fmap_id'.
        intros a Ha%Hzeros; now destruct a.
      }
      apply list_eq_Forall2 in Hnm.
      rewrite Forall2_fmap in Hnm.
      subst k.
      rewrite <- fmap_const in Hnm.
      rewrite Forall2_fmap_r in Hnm.
      cbn.
      revert Hnm.
      clear Hsome' Hk' Hzeros.
      induction (n ++ m) as [|p nm IHnm]; [done|].
      intros [Hp Hnm]%Forall2_cons.
      cbn in Hp.
      cbn.
      apply Nat.eq_add_0.
      split; [|auto].
      apply HfN in Hp.
      done.
  - apply bool_decide_eq_true in Hsome.
    rewrite (btree_size_ext Hsome).
    cbn.
    case_decide; done.
Qed.

Notation SizedProLike' MS S T D :=
    (SizedProLike (N:=positive) MS S T D).


#[export] Instance ZX_SymmetricG_SizedProLike : SizedProLike' MSymmetric SymmetricG ZXCVERT ZX := {}.

#[export] Instance ZX_Autonomous_SizedProLike : SizedProLike' MAutonomous Autonomous ZXCVERT ZX := {}.

#[export] Instance ZX_Frobenius_SizedProLike : SizedProLike' MFrobenius Frobenius ZXCVERT ZX := {}.




Module ZXmsymm.

Section ZXquote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_SymmetricG_ProLike)).

Lemma btree_size_eq_path {N} {f : N -> nat} {a b : btree N} (p : bpath a b) :
  btree_size f a = btree_size f b.
Proof.
  rewrite <- 2 sum_list_with_btree_elems.
  f_equal.
  now apply btree_elems_bpath in p.
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

Lemma zx_quote_symm_cast_nwire_bpath_aux (f : positive -> nat)
  (a b : btree positive)
  (p : bpath a b) :
  Quote (cast _ _
  (btree_size_eq_path p) eq_refl (n_wire (btree_size f b)))
  ((MPRO_to_PRO f (gbpath_to_MPRO p))).
Proof.
  induction p.
  - rewrite cast_id_eq.
    cbn.
    done.
  - cbn.
    constructor.
    cbn.
    f_equiv.
    cast_irrelevance.
  - cbn.
    rewrite <- n_wire_stack.
    rewrite cast_stack_distribute.
    exact (quote_stack _ _ _ _ IHp1 IHp2).
  - erewrite cast_simplify_eq by reflexivity.
    rewrite <- (cast_n_wire_r (n:=btree_size f b)).

    rewrite <- (nwire_removal_l (n_wire _)).
    rewrite cast_compose_distribute.
    cbn -[cast].
    unshelve refine (quote_compose _ _ _ _ IHp1 _).
    rewrite cast_n_wire_r.
    eapply DiagramQuote_proper_equiv, IHp2; [cast_irrelevance|done].
  Unshelve.
    symmetry; apply btree_size_eq_path; assumption.
Qed.


Lemma zx_quote_symm_cast_nwire_bpath (f : positive -> nat)
  (a b : btree positive)
  (Hab : a =@{list _} b)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n)) (MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Hab))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|apply zx_quote_symm_cast_nwire_bpath_aux].
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_bpath (f : positive -> nat)
  (a b a' b' : btree positive)
  (Ha : a =@{list _} a') (Hb : b' =@{list _} b)
  (zx : ZX (btree_size f a') (btree_size f b')) p
  (Hasize : btree_size f a = btree_size f a')
  (Hbsize : btree_size f b = btree_size f b') :
  Quote zx p ->
  Quote (cast _ _ Hasize Hbsize zx) (MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Ha)) ;;
    p ;; MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Hb)))%pro.
Proof.
  intros Hzx.
  rewrite <- (nwire_removal_l zx).
  rewrite cast_compose_distribute.
  rapply @quote_compose;
  [apply zx_quote_symm_cast_nwire_bpath|].
  rewrite <- (nwire_removal_r zx).
  rewrite cast_compose_distribute.
  rapply @quote_compose.
  apply zx_quote_symm_cast_nwire_bpath.
Qed.




End ZXquote_symm.

Module QuoteCast.

Import Ltac2.
Import ConstrExtra.

Ltac2 solve_zx_symm_quote_cast () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m ?n' ?m' ?hn ?hm ?zx) _] =>
    let (cs, bn) := parse_nat_btree_to_pos [] n in
    let (cs, bn') := parse_nat_btree_to_pos cs n' in
    let (cs, bm) := parse_nat_btree_to_pos cs m in
    let (cs, bm') := parse_nat_btree_to_pos cs m' in
    let cbn := CC.to_btree_typed 'positive CC.to_pos bn in
    let cbm := CC.to_btree_typed 'positive CC.to_pos bm in
    let cbn' := CC.to_btree_typed 'positive CC.to_pos bn' in
    let cbm' := CC.to_btree_typed 'positive CC.to_pos bm' in
    let ccs := CC.mk_list_typed 'nat cs in
    let prf := '(zx_quote_symm_cast_bpath (interp_discrete_hg_inhab $ccs)
      $cbn $cbm $cbn' $cbm' eq_refl eq_refl $zx _ $hn $hm) in
    refine '(id $prf _)
  end.

End QuoteCast.

#[export] Hint Extern 0 (DiagramQuote (ProD:=ZX_SymmetricG_ProLike)
  (cast _ _ _ _ _) _) =>
  ltac2:(QuoteCast.solve_zx_symm_quote_cast()) : typeclass_instances.




Import ZXsymm.

Definition zxpscat_lemma := LawfulMProLike_MPRO_quote_test_correct (T':=positive) (MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro.

Definition zxpsrw_lhs_lemma := LawfulProLike_MPRO_monog_quote_rewrite_correct (T':=positive) (@MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro.

Ltac zxpscat :=

  let Hrw := fresh "Hrw" in
  time? "zxpscat setup tactic" specialize (zxpscat_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXCVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));
  lazymatch goal with
  | |- ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  time? "zxpscat quote to PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));
  time? "zxpscat quote to positive PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)
  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  time? "zxpscat quote to MPRO" (epose proof (Hrw _ _ _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error."));
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpscat refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxspcat) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpscat compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxspcat) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxspcat) Unexpected additional goal! Please report this unexpected error."..].


Ltac zxpsrw_lhs lem match_number :=

  let Hrw := fresh "Hrw" in
  time? "zxpsrw_lhs setup tactic" specialize (zxpsrw_lhs_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXCVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));

  let lemT := type of lem in
  lazymatch lemT with
  | ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | _ =>
    fail "cannot recognize lemma (type) as the application of a relation: " lemT
  end;


  lazymatch goal with
  | |- ?R ?dtgt _ =>
    specialize (Hrw _ _ dtgt)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;

  specialize (Hrw match_number);
  specialize (Hrw lem);

  epose proof (Hrw _ _ _) as Hrw;

  time? "zxpsrw_lhs quote lem to PRO" (
  do 2 (tryif timeout 2 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote lemma! Have you declared all necessary instances?"));
  time? "zxpsrw_lhs quote goal to PRO" (
  do 1 (tryif timeout 2 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));

  time? "zxpsrw_lhs quote to positive PRO" (epose proof (Hrw _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)

  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  epose proof (Hrw _ _ _ _   _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.");

  specialize_with_concr_asgn_list Hrw lnv;
  time? "zxpsrw_lhs prove correctness of concrete assignment" (
    tryif (timeout 1 (tspecialize Hrw by compute_done)) then idtac
    else fail "Failed to prove concrete assignment map correct! Please report this unexpected error");

  epose proof (Hrw _) as Hrw;
  time? "zxpsrw_lhs compute rewrite" (tspecialize Hrw; [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ]);

  time? "zxpsrw_lhs MPRO to PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting resulting sized MPRO as a PRO! Please report this unexpected error."));

  time? "zxpsrw_lhs denote from positive PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac else
    fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this."));

  time? "zxpsrw_lhs denote PRO to goal" (epose proof (Hrw _) as Hrw;
  (tryif timeout 10 (tspecialize Hrw by typeclasses eauto) then idtac else
    fail "Timed out trying to denote result! Have you declared all necessary instances?"));
  close_evar_ended_list le; close_evar_ended_list ln;
  subst le ln;
  etransitivity; [apply Hrw|clear Hrw].


Ltac zxpsrw_rhs lem match_number :=
  symmetry;
  zxpsrw_lhs lem match_number;
  symmetry.

Ltac zxpsrw lem match_number :=
  zxpsrw_lhs lem match_number || zxpsrw_rhs lem match_number.


Tactic Notation "zxpsrw_lhs" uconstr(lem) "at" constr(n) :=
  zxpsrw_lhs lem n.

Tactic Notation "zxpsrw_lhs" uconstr(lem) :=
  zxpsrw_lhs lem at O.

Tactic Notation "zxpsrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw_lhs (symmetry lem) at n.

Tactic Notation "zxpsrw_lhs" "<-" uconstr(lem) :=
  zxpsrw_lhs (symmetry lem).

Tactic Notation "zxpsrw_rhs" uconstr(lem) "at" constr(n) :=
  zxpsrw_rhs lem n.

Tactic Notation "zxpsrw_rhs" uconstr(lem) :=
  zxpsrw_rhs lem at O.

Tactic Notation "zxpsrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw_rhs (symmetry lem) at n.

Tactic Notation "zxpsrw_rhs" "<-" uconstr(lem) :=
  zxpsrw_rhs (symmetry lem).

Tactic Notation "zxpsrw" uconstr(lem) "at" constr(n) :=
  zxpsrw lem n.

Tactic Notation "zxpsrw" uconstr(lem) :=
  zxpsrw lem at O.

Tactic Notation "zxpsrw" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw (symmetry lem) at n.

Tactic Notation "zxpsrw" "<-" uconstr(lem) :=
  zxpsrw (symmetry lem).





Lemma parametric_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m o β ⟷ Z o p γ ∝=
  Z n m α ⟷ (X m o β ⟷ Z o p γ).
Proof.
  zxpscat.
Qed.


Lemma parametric_stack_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m (o + n + m) β ⟷ (Z o p γ ↕ Z n p γ ↕ Z m p γ) ⟷
    X _ n α ∝=
  Z n m α ⟷ X m (o + (n + m)) β ⟷ (Z o p γ ↕ (Z n p γ ↕ Z m p γ)) ⟷
    X _ n α.
Proof.
  (* Ltac enable_timing ::= idtac. *)
  (* idtac "--------------------------------------". *)

  Time zxpscat.
Qed.

Lemma Z_absolute_fusion' {n m o} (α β : R) : m <> O ->
  Z n m α ⟷ Z m o β ∝= Z n o (α + β).
Proof.
  destruct m; [done|intros _].
  apply Z_absolute_fusion.
Qed.

(* FIXME: Add quote instances too *)
#[export] Instance zx_denote_symm_monoidal {n m} (s : Monoidal n m) :
  DiagramDenote (ProD:=ZX_SymmetricG_ProLike)
    (cast _ _ (Monoidal_eq s) eq_refl (n_wire m))
    [str monoidal_inl s].
Proof.
  constructor; done.
Qed.


Lemma Z_absolute_fusion : forall {n m o} α β,
	(Z n (S m) α ⟷ Z (S m) o β) ∝=
	Z n o (α + β).
Proof.
  intros. (* Figure 19a *)
  induction m.
  - apply Z_spider_1_1_fusion.
  - rewrite grow_Z_top_right, grow_Z_top_left.
    zxpsrw (Z_1_2_1_fusion 0 0).
    rewrite Rplus_0_l.
    zxpsrw IHm.
    zxpscat.
Qed.



Lemma parametric_rewriting_example {n m o p : nat} {α β γ : R} : m <> 0 -> n <> 0 ->
  Z n (p + (m + n)) α ⟷ (n_wire p ↕ (Z m n α ↕ Z n m β)) ⟷
  (n_wire p ↕ zx_comm _ _) ⟷ (n_wire p ↕ (Z m n α ↕ Z n m α)) ⟷
  Z (p + (n + m)) p 0 ∝= Z _ _ 0.
Proof.
  intros Hm Hn.


  (* TODO: Investigate parameter matching like this:
  epose (lem := @Z_absolute_fusion' _ n _ _ _ Hn).
  let lemT := type of lem in
  match lemT with
  | ?R ?lhs _ =>
    eassert (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) lhs _)
  end.
  Hint Mode DiagramQuote + + + + - - ! - : typeclass_instances.
  typeclasses eauto.

  TODO: Or maybe we should parse the target term directly using the known
  composition and stacking? In either case, we need to end up with a list
  of _sized_ generators, from which we can try all matches I guess? With
  a warning that that'll be slow? *)



  (* TODO: etc... let lem := lem *)
  zxpsrw_lhs (@Z_absolute_fusion' m n m α α Hn).
  zxpsrw_lhs (@Z_absolute_fusion' m n m α α Hn).

  set (lem := @Z_absolute_fusion' m n m α α Hn).
  set (match_number := 0) in n.

  rewrite ?cast_id_eq.
  Print Grammar tactic.
  cleanup_permlike. )); exact nil|].
    vm_compute.

  }
  tspecialize Hrw. 1:{
    compute_done.
    apply (bool_decide_unpack _).
    close_evar_ended_list ln.
    vm_compute.
    apply bool_decide_eq_true.
    compute_done.
  }
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.").
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.").
  tspecialize Hrw.


  ltac2:(mk_MPRO_PRO_quote_SymmetricG()).
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.").
  time? "zxpsrw_lhs quote to MPRO" (
  do 3 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.")).
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpsrw_lhs refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxpsrw_lhs) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpsrw_lhs compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxpsrw_lhs) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxpsrw_lhs) Unexpected additional goal! Please report this unexpected error."..].


  From TensorRocq Require Import .
  typeclasses eauto.

  epose proof

  tspecialize Hrw.
  typeclasses eauto.
  epose proof (Hrw _ _  _ _ )


Lemma parametric_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m o β ⟷ Z o p γ ∝=
  Z n m α ⟷ (X m o β ⟷ Z o p γ).
Proof.

  specialize (LawfulProLike_MPRO_monog_quote_rewrite_correct (T':=positive) (@MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro) as Hrw.
  let le := fresh "l" in evar (le : list ZXCVERT);
  let l := eval unfold l in le in
  specialize (Hrw (interp_discrete_hg_inhab l)).
  epose proof (Hrw _ _ )


Section Quote.

#[export]



