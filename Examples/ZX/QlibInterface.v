From QuantumLib Require Import Modulus Quantum.
Require Import QuantumLib.Bits.
Require Import Tensor ZXCore.

Require Import Aux_stdpp.
Import vector.

Lemma vmap_fun_to_vec {A B} {n} (f : fin n -> A) (g : A -> B) :
  vmap g (fun_to_vec f) = fun_to_vec (g ∘ f).
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_map, 2 lookup_fun_to_vec.
  done.
Qed.

Lemma vmap_seq_fun_to_vec {A} (f : nat -> A) start len :
  vmap f (vseq start len) = fun_to_vec (fun i => f (start + i)).
Proof.
  rewrite vseq_fun_to_vec, vmap_fun_to_vec.
  done.
Qed.

#[export] Instance vec_rev_invol {A n} : Involutive eq (@Vector.rev A n).
Proof.
  hnf; intros;
  apply Vector.rev_rev.
Qed.

#[export] Instance vec_rev_inj {A n} : Inj eq eq (@Vector.rev A n).
Proof.
  apply cancel_inj.
Qed.

#[export] Instance vec_rev_surj {A n} : Surj eq (@Vector.rev A n).
Proof.
  apply cancel_surj.
Qed.


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





Lemma rev_cast {A n m} (v : Vector.t A m) (H : m = n) :
  Vector.rev (Vector.cast v H) = Vector.cast (Vector.rev v) H.
Proof.
  subst.
  now rewrite 2!cast_id.
Qed.

Lemma rev_append {A n m} (v : Vector.t A m) (u : Vector.t A n) :
  Vector.rev (v +++ u) =
  Vector.cast (Vector.rev u +++ Vector.rev v) (Nat.add_comm _ _).
Proof.
  apply vec_to_list_inj2.
  rewrite vec_to_list_cast, vec_to_list_app,
    3 vec_to_list_rev, vec_to_list_app.
  apply reverse_app.
Qed.


Lemma cast_cast {A n m o} (v : Vector.t A o) (H : o = m) (H' : m = n) :
  Vector.cast (Vector.cast v H) H' = Vector.cast v (eq_trans H H').
Proof.
  subst.
  now rewrite 3!cast_id.
Qed.






Definition nat_to_bits (len : nat) (n : nat) : Vector.t bool len :=
  fun_to_vec (fun i => Nat.testbit n (len - S i)).

Lemma nat_to_bits_alt len n :
  nat_to_bits len n =
  vmap (Nat.testbit n) (Vector.rev (vseq 0 len)).
Proof.
  apply vec_eq.
  intros i.
  unfold nat_to_bits.
  rewrite lookup_fun_to_vec, vlookup_map, vlookup_rev, vlookup_seq.
  rewrite fin_to_nat_rev.
  done.
Qed.

Lemma cast_nat_to_bits {n m i} (H : m = n) :
  Vector.cast (nat_to_bits m i) H = nat_to_bits n i.
Proof.
  subst.
  now rewrite cast_id.
Qed.



Definition bits_to_nat {len} (v : Vector.t bool len) :=
  funbool_to_nat len (λ i, default false ((vec_to_list v) !! i)).


Open Scope nat_scope.


Lemma nat_to_bits_to_list (len : nat) n : n < 2 ^ len ->
  vec_to_list (nat_to_bits len n) = reverse (nat_to_binlist len n).
Proof.
  intros Hn.
  rewrite nat_to_bits_alt.
  rewrite Vector.map_rev, vec_to_list_rev.
  f_equal.

  rewrite vec_to_list_map, vec_to_list_seq.
  apply nth_ext with (d:= false) (d':=false).
  - rewrite length_map, length_seq.
    rewrite nat_to_binlist_length; easy.
  - intros k Hk.
    rewrite map_nth_small with (dnew := 0) by
      (now rewrite length_map in Hk).
    rewrite length_map, length_seq in Hk.
    rewrite seq_nth by auto.
    rewrite nth_nat_to_binlist.
    reflexivity.
Qed.


Lemma nth_nat_to_bits_gen start len n p :
  (Vector.map (Nat.testbit n) (vseq start len)) !!! p =
  Nat.testbit (n / 2 ^ start) (fin.fin_to_nat p).
Proof.
  revert start.
  induction p; intros start.
  - simpl.
    rewrite Nat.testbit_odd.
    rewrite Nat.shiftr_div_pow2.
    reflexivity.
  - cbn.
    rewrite IHp.
    rewrite Nat.div2_div, Nat.Div0.div_div.
    rewrite Nat.mul_comm.
    reflexivity.
Qed.

Lemma nth_nat_to_bits len n p :
  (nat_to_bits len n) !!! p =
  Nat.testbit n (len - S (fin_to_nat p)).
Proof.
  rewrite nat_to_bits_alt.
  rewrite <- fin_to_nat_rev.
  rewrite <- (Nat.div_1_r n) at 2.
  rewrite <- (nth_nat_to_bits_gen 0).
  rewrite 2 vlookup_map.
  f_equal.
  apply vlookup_rev.
Qed.

Lemma nat_to_bits_eq_of_mod len n :
  nat_to_bits len n = nat_to_bits len (n mod 2 ^ len).
Proof.
  apply vec_eq.
  intros p.
  rewrite 2!nth_nat_to_bits.
  rewrite testbit_mod_pow2.
  pose proof (fin.fin_to_nat_lt p).
  bdestruct_one; [reflexivity|lia].
Qed.


Lemma nat_to_bits_succ_alt len n :
  nat_to_bits (S len) n =
  Vector.shiftin (Nat.odd n) $ nat_to_bits len (n / 2).
Proof.
  rewrite 2 nat_to_bits_alt.
  apply (inj Vector.rev).
  rewrite Vector.map_rev, Vector.rev_rev,
    Vector.rev_shiftin, <- Vector.map_rev, Vector.rev_rev.
  cbn -[Nat.div].
  f_equal.
  apply vec_eq; intros p.
  rewrite 2 vlookup_map, 2 vlookup_seq.
  cbn -[Nat.div].
  now rewrite Nat.div2_div.
Qed.

Lemma nat_to_bits_succ len n :
  nat_to_bits (S len) n =
  Nat.odd (n / 2 ^ len) ::: nat_to_bits len n.
Proof.
  cbn -[Nat.div].
  f_equal.
  rewrite Nat.testbit_odd, Nat.sub_0_r.
  now rewrite Nat.shiftr_div_pow2.
Qed.



Lemma nat_to_bits_plus l1 l2 n :
  nat_to_bits (l1 + l2) n =
  nat_to_bits l1 (n / 2 ^ l2) +++
    nat_to_bits l2 n.
Proof.
  revert n;
  induction l1; intros n; [done|].
  cbn [Nat.add].
  rewrite 2 nat_to_bits_succ.
  cbn [Vector.append].
  f_equal; [|done].
  rewrite Nat.Div0.div_div.
  now rewrite Nat.add_comm, Nat.pow_add_r.
Qed.





Lemma nat_to_bits_to_nat (len : nat) n :
  n < 2 ^ len ->
  bits_to_nat (nat_to_bits len n) = n.
Proof.
  intros Hn.
  apply Nat.bits_inj.
  unfold bits_to_nat.
  intros k.
  rewrite testbit_funbool_to_nat.
  bdestruct_one.
  2: {
    replace n with (n mod (2 ^ len)) by
      now rewrite Nat.mod_small by easy.
    rewrite Nat.mod_pow2_bits_high; easy.
  }
  rewrite lookup_vec_to_list.
  case_guard; [cbn|lia].
  rewrite nth_nat_to_bits.
  f_equal.
  rewrite fin_to_nat_to_fin; lia.
Qed.

Lemma nat_to_bits_inj (len : nat) n m :
  n < 2 ^ len -> m < 2 ^ len ->
  nat_to_bits len n = nat_to_bits len m <-> n = m.
Proof.
  intros Hn Hm.
  split; [|now intros ->].
  intros Hnm%(f_equal bits_to_nat).
  now rewrite 2!nat_to_bits_to_nat in Hnm by auto.
Qed.


Lemma testbit_bits_to_nat {len} (v : vec bool len) i :
  Nat.testbit (bits_to_nat v) i =
  default false ((vec_to_list (Vector.rev v)) !! i).
Proof.
  unfold bits_to_nat.
  rewrite testbit_funbool_to_nat.
  rewrite 2 lookup_vec_to_list.
  bdestruct_one; repeat case_guard; try lia || done.
  cbn.
  rewrite vlookup_rev.
  f_equal.
  apply fin_to_nat_inj.
  now rewrite fin_to_nat_rev, 2 fin_to_nat_to_fin.
Qed.



Lemma bits_to_nat_to_bits {len} (v : Vector.t bool len) :
  nat_to_bits len (bits_to_nat v) = v.
Proof.
  apply vec_eq; intros i.
  rewrite nth_nat_to_bits.
  rewrite testbit_bits_to_nat.
  rewrite <- fin_to_nat_rev.
  rewrite lookup_vec_to_list_fin.
  cbn.
  now rewrite <- vlookup_rev, (involutive _).
Qed.





#[export] Instance matrix_equiv {n m} : Equiv (Matrix n m) :=
  mat_equiv.

Lemma csum_vec_eq_bigsum_rev {n} f :
  ∑ v : vec bool n, f v =
  Σ (fun i => f (Vector.rev (nat_to_bits n i))) (2 ^ n).
Proof.
  induction n.
  - cbn.
    rewrite sum_of_vec_0, Vector.rev_nil.
    symmetry; apply Cplus_0_l.
  - rewrite sum_of_vec_succ, sum_of_bool_defn.
    rewrite 2!IHn.
    etransitivity; [symmetry; refine (big_sum_plus (G:=C) _ _ _)|].
    change (2 ^ (S n)) with (2 * 2 ^ n).
    rewrite big_sum_product_div_mod_split.
    apply big_sum_eq_bounded.
    intros k Hk.
    simpl.
    rewrite Cplus_0_l.
    rewrite 2!nat_to_bits_succ_alt, 2 Vector.rev_shiftin.
    rewrite Nat.odd_mul, andb_false_r.
    rewrite Nat.odd_succ, Nat.even_mul, orb_true_r.
    rewrite Nat.div_mul by easy.
    replace (S (k * 2) / 2) with ((k * 2 + 1) / 2) by (f_equal; lia).
    rewrite Nat.div_add_l by easy.
    rewrite Nat.add_0_r.
    reflexivity.
Qed.


Lemma bigsum_eq_csum_rev {n} f :
  Σ f (2 ^ n) =
  ∑ v : vec bool n, f (bits_to_nat (Vector.rev v)).
Proof.
  rewrite csum_vec_eq_bigsum_rev.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite Vector.rev_rev.
  now rewrite nat_to_bits_to_nat by easy.
Qed.

Lemma bigsum_eq_csum {n} f :
  Σ f (2 ^ n) =
  ∑ v : vec bool n, f (bits_to_nat v).
Proof.
  rewrite bigsum_eq_csum_rev.
  symmetry.
  now rewrite sum_of_vec_rev.
Qed.


Lemma csum_vec_eq_bigsum {n} f :
  ∑ v : vec bool n, f v =
  Σ (fun i => f (nat_to_bits n i)) (2 ^ n).
Proof.
  rewrite bigsum_eq_csum.
  now setoid_rewrite bits_to_nat_to_bits.
Qed.


Definition matrix_of_tensor {n m : nat} (t : Tensor n m bool) :
  Matrix (2^m) (2^n) :=
  make_WF (fun i j =>
    t (nat_to_bits n j) (nat_to_bits m i)).

Definition tensor_of_matrix {n m : nat} (A : Matrix (2^m) (2^n)) :
  Tensor n m bool :=
  fun i j => A (bits_to_nat j) (bits_to_nat i).

Lemma WF_matrix_of_tensor {n m} (t : Tensor n m bool) :
  WF_Matrix (matrix_of_tensor t).
Proof. apply WF_make_WF. Qed.

#[export] Hint Resolve WF_matrix_of_tensor : wf_db.

Add Parametric Morphism {n m} : (@tensor_of_matrix n m) with signature
  mat_equiv ==> equiv as tensor_of_matrix_eq_of_mat_equiv.
Proof.
  intros A B HAB.
  intros v w _ _.
  unfold tensor_of_matrix.
  apply HAB; apply funbool_to_nat_bound.
Qed.


Add Parametric Morphism {n m} : (@matrix_of_tensor n m) with signature
  equiv ==> mat_equiv as matrix_of_tensor_of_equiv.
Proof.
  intros A B HAB.
  intros v w _ _.
  unfold matrix_of_tensor.
  unfold make_WF.
  bdestruct_one; [|done].
  bdestruct_one; [|done].
  cbn.
  apply HAB; apply _.
Qed.


Lemma matrix_of_tensor_of_matrix {n m} (A : Matrix (2^n) (2^m)) :
  matrix_of_tensor (tensor_of_matrix A) ≡ A.
Proof.
  unfold matrix_of_tensor, tensor_of_matrix.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  now rewrite 2!nat_to_bits_to_nat by auto.
Qed.

Lemma tensor_of_matrix_of_tensor {n m} (t : Tensor n m bool) :
  tensor_of_matrix (matrix_of_tensor t) = t.
Proof.
  unfold matrix_of_tensor, tensor_of_matrix.
  prep_matrix_equality.
  rewrite make_WF_equiv by apply funbool_to_nat_bound.
  now rewrite 2!bits_to_nat_to_bits.
Qed.

Lemma tensor_of_matrix_inj {n m} (A B : Matrix (2^m) (2^n)) :
  tensor_of_matrix A = tensor_of_matrix B ->
  A ≡ B.
Proof.
  intros HAB%(f_equal matrix_of_tensor).
  rewrite <- matrix_of_tensor_of_matrix.
  rewrite HAB.
  rewrite matrix_of_tensor_of_matrix.
  reflexivity.
Qed.

Lemma matrix_of_tensor_inj {n m} (t s : Tensor n m bool) :
  matrix_of_tensor t ≡ matrix_of_tensor s ->
  t ≡ s.
Proof.
  intros HAB.
  rewrite <- tensor_of_matrix_of_tensor.
  rewrite <- HAB.
  rewrite tensor_of_matrix_of_tensor.
  reflexivity.
Qed.

Lemma matrix_of_tensor_compose {n m o} (t : Tensor n m bool) (s : Tensor m o bool) :
  matrix_of_tensor (compose_tensor t s) =
  matrix_of_tensor s × matrix_of_tensor t.
Proof.
  prep_matrix_equivalence.
  intros i k Hi Hk.
  unfold Mmult, matrix_of_tensor.
  unfold make_WF.
  bdestruct_one; [|lia].
  bdestruct_one; [|lia].
  simpl.
  rewrite csum_vec_eq_bigsum.
  apply big_sum_eq_bounded.
  intros j Hj.
  bdestruct_one; [|lia].
  simpl.
  apply Cmult_comm.
Qed.

Lemma matrix_of_tensor_stack {n0 m0 n1 m1}
  (t : Tensor n0 m0 bool) (s : Tensor n1 m1 bool) :
  matrix_of_tensor (stack_tensor t s) =
  matrix_of_tensor t ⊗ matrix_of_tensor s.
Proof.
  prep_matrix_equivalence.
  intros i k Hi Hk.
  unfold stack_tensor, matrix_of_tensor, kron.
  rewrite 3!make_WF_equiv by show_moddy_lt.
  rewrite <- (cast_nat_to_bits (Nat.add_comm n1 n0)),
    <- (cast_nat_to_bits (Nat.add_comm m1 m0)).
  rewrite 2 cast_nat_to_bits.
  rewrite 2 nat_to_bits_plus.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  f_equal.
  f_equal; apply nat_to_bits_eq_of_mod.
Qed.


Lemma matrix_of_tensor_delta n :
  matrix_of_tensor (delta_tensor) = I (2 ^ n).
Proof.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  unfold matrix_of_tensor, delta_tensor.
  rewrite make_WF_equiv by easy.
  rewrite decide_bool_decide.
  apply f_equal_if; [|easy..].
  replace_bool_lia (i <? 2 ^ n) true.
  rewrite andb_true_r.
  apply Bool.eq_iff_eq_true.
  rewrite Nat.eqb_eq.
  rewrite bool_decide_eq_true.
  rewrite nat_to_bits_inj by easy.
  easy.
Qed.


Lemma matrix_of_tensor_swap :
  matrix_of_tensor (swap_tensor (n:=1)(m:=1)) = swap.
Proof.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.


Lemma matrix_of_tensor_cap :
  matrix_of_tensor (cap_tensor (n:=1)) = list2D_to_matrix [[C1; C0; C0; C1]].
Proof.
  apply mat_equiv_eq;
    [auto_wf | apply show_WF_list2D_to_matrix; reflexivity |].
  by_cell; reflexivity.
Qed.

Lemma matrix_of_tensor_cup :
  matrix_of_tensor (cup_tensor (n:=1)) = list2D_to_matrix [[C1]; [C0]; [C0]; [C1]].
Proof.
  apply mat_equiv_eq;
    [auto_wf | apply show_WF_list2D_to_matrix; reflexivity |].
  by_cell; reflexivity.
Qed.

(* FIXME: Move *)
#[global] Arguments h !_ !_ /.

Lemma matrix_of_tensor_H :
  matrix_of_tensor (h_stack (n:=1)) = hadamard.
Proof.
  prep_matrix_equivalence.
  by_cell; cbn -[Cmult]; lca.
Qed.

Lemma matrix_of_tensor_stack_tensors_1 n (t : Tensor 1 1 bool) :
  @matrix_of_tensor n n (stack_n_tensor_1 t) =
  kron_n n (matrix_of_tensor t).
Proof.
  prep_matrix_equivalence.
  induction n; [by_cell; reflexivity|].
  rewrite kron_n_assoc by auto_wf.
  rewrite stack_n_tensor_1_succ.
  rewrite (@matrix_of_tensor_stack 1 1).
  rewrite IHn.
  reflexivity.
Qed.

Lemma stack_tensor_h_stack n m : 
  stack_tensor (@h_stack n) (@h_stack m) ≡ h_stack.
Proof.
  intros v w Hv Hw.
  cbn.
  now rewrite h_stack_mul, 2 app_vsplit.
Qed.

Lemma stack_n_tensor_1_h n :
  stack_n_tensor_1 h_stack ≡ h_stack (n:=n).
Proof.
  induction n; [now do 2 refine (vec_0_inv _ _)|].
  rewrite stack_n_tensor_1_succ.
  erewrite stack_tensor_mor by first [eassumption|reflexivity].
  now rewrite stack_tensor_h_stack.
Qed.

Lemma matrix_of_tensor_h_stack n :
  matrix_of_tensor (h_stack (n:=n)) = kron_n n hadamard.
Proof.
  prep_matrix_equivalence.
  rewrite <- stack_n_tensor_1_h.
  rewrite matrix_of_tensor_stack_tensors_1.
  f_equiv.
  apply matrix_of_tensor_H.
Qed.