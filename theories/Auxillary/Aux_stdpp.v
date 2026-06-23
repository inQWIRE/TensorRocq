(* Extra bits for stdpp *)
Require Combinators.
Require Import SetoidList SetoidPermutation.
From stdpp Require Import decidable.
From TensorRocq Require Import Aux.

From stdpp Require Import prelude functions.

From stdpp Require Import sorting.

From stdpp Require Import strings fin_maps gmultiset pmap gmap hlist.
From stdpp Require Import pretty finite.

From TensorRocq Require Export Aux_stdpp_base.



Definition permute_vec {A n m} (f : fin n -> fin m) (v : vec A m) : vec A n :=
  fun_to_vec (λ i, v !!! f i).

Lemma lookup_permute_vec {A n m} (f : fin n -> fin m) (v : vec A m) i :
  permute_vec f v !!! i = v !!! f i.
Proof.
  unfold permute_vec.
  rewrite lookup_fun_to_vec.
  done.
Qed.

Lemma permute_vec_compose {A n m o} (g : fin m -> fin o) (f : fin n -> fin m)
  (v : vec A o) :
  permute_vec f (permute_vec g v) = permute_vec (g ∘ f) v.
Proof.
  apply vec_eq.
  intros i.
  now rewrite 3 lookup_permute_vec.
Qed.

Lemma permute_vec_id {A n}
  (v : vec A n) :
  permute_vec id v = v.
Proof.
  apply vec_eq.
  intros i.
  now rewrite lookup_permute_vec.
Qed.

#[export] Instance permute_vec_ext {A n m} :
  Proper (pointwise_relation _ eq ==> eq ==> eq) (@permute_vec A n m).
Proof.
  intros f g Hfg v _ <-.
  apply vec_eq; intros i.
  rewrite 2 lookup_permute_vec, Hfg.
  done.
Qed.

Lemma permute_vec_id' {A n}
  f (v : vec A n) :
  (forall i, f i = i) ->
  permute_vec f v = v.
Proof.
  intros Hf.
  rewrite <- (permute_vec_id v) at 2.
  apply permute_vec_ext, reflexivity.
  exact Hf.
Qed.

#[export] Instance permute_vec_cancel {A n m} (f : fin n -> fin m) g :
  Cancel eq g f -> Cancel eq (permute_vec (A:=A) f) (permute_vec g).
Proof.
  intros Hfg v.
  rewrite permute_vec_compose.
  apply permute_vec_id'.
  apply Hfg.
Qed.

Lemma permute_vec_perm {A n m} (f : fin n -> fin m) {Hf : Inj eq eq f}
  (Hnm : n = m) (v : vec A m) :
  permute_vec f v ≡ₚ v.
Proof.
  subst m.
  apply Permutation_lookup.
  split; [now rewrite 2 length_vec_to_list|].
  exists (fin_inj_to_nat_inj f).
  split; [apply _|].
  intros i.
  rewrite 2 lookup_vec_to_list.
  unfold fin_inj_to_nat_inj.
  unfold guard.
  case_decide as Hi; [|cbn; case_decide; [lia|done]].
  cbn.
  pose proof (fin_to_nat_lt (f (nat_to_fin Hi))).
  case_decide; [|done].
  cbn.
  f_equal.
  rewrite lookup_permute_vec.
  f_equal.
  now rewrite nat_to_fin_to_nat.
Qed.

Lemma fin_mul_ind {n m} (P : fin (n * m) -> Type)
  (HP : forall i j, P (fin_prod i j)) : forall i, P i.
Proof.
  intros i.
  rewrite <- fin_prod_split, uncurry_alt.
  auto.
Qed.

Definition fin_prod_comm {n m} (i : fin (n * m)) : fin (m * n) :=
  uncurry fin_prod (prod_swap (fin_split i)).

Lemma fin_prod_comm_prod {n m} (i : fin n) (j : fin m) : fin_prod_comm (fin_prod i j) = fin_prod j i.
Proof.
  unfold fin_prod_comm.
  rewrite fin_split_prod.
  done.
Qed.

#[export] Instance fin_prod_comm_invol {n m} : Cancel eq (@fin_prod_comm n m) fin_prod_comm.
Proof.
  refine (fin_mul_ind _ _).
  intros i j.
  now rewrite 2 fin_prod_comm_prod.
Qed.

#[export] Instance fin_prod_comm_inj {n m} : Inj eq eq (@fin_prod_comm n m) := cancel_inj.


Fixpoint vfinseq n : vec (fin n) n :=
  match n with
  | 0 => [#]
  | S n => 0%fin ::: vmap FS (vfinseq n)
  end.

Lemma vec_to_list_vfinseq n : vec_to_list (vfinseq n) = fin_enum n.
Proof.
  induction n; cbn; f_equal; rewrite vec_to_list_map; f_equal; done.
Qed.

Lemma seq_0_to_vfinseq n :
  seq 0 n = fin_to_nat <$> (vec_to_list $ vfinseq n).
Proof.
  induction n; [done|].
  cbn.
  rewrite <- fmap_S_seq.
  rewrite IHn, vec_to_list_map.
  rewrite <- 2 list_fmap_compose.
  done.
Qed.

Lemma lookup_vfinseq n i : vfinseq n !!! i = i.
Proof.
  induction i; [done|].
  cbn.
  now rewrite vlookup_map, IHi.
Qed.

Lemma vzip_with_to_vmap_l {n} {A B C} (f : A -> C) (v : vec A n) (w : vec B n) :
  vzip_with (λ a _, f a) v w = vmap f v.
Proof.
  induction n; inv_all_vec_fin; cbn; congruence.
Qed.

Lemma vzip_with_to_vmap_r {n} {A B C} (f : B -> C) (v : vec A n) (w : vec B n) :
  vzip_with (λ _ b, f b) v w = vmap f w.
Proof.
  induction n; inv_all_vec_fin; cbn; congruence.
Qed.

Lemma vzip_with_diag {n} {A B} (f : A -> A -> B) (v : vec A n) :
  vzip_with f v v =
  vmap (λ a, f a a) v.
Proof.
  induction v; cbn; congruence.
Qed.

(* FIXME: Move *)
Fixpoint vjoin {A} {n m} (v : vec (vec A n) m) : vec A (m * n) :=
  match v with
  | [#] => [#]
  | u ::: v => u +++ vjoin v
  end.

Fixpoint vunjoin {A} {n m} : forall (v : vec A (m * n)), vec (vec A n) m  :=
  match m with
  | 0 => fun _ => [#]
  | S m => fun v =>
    vsplitl v ::: vunjoin (vsplitr v)
  end.

Fixpoint vjoin' {A} {n m} : forall (v : vec (vec A n) m), vec A (n * m) :=
  match n with
  | 0 => fun v => [#]
  | S n => fun v =>
    (vmap vhd v) +++ vjoin' (vmap vtl v)
  end.

Fixpoint vunjoin' {A} {n m} : forall (v : vec A (n * m)), vec (vec A n) m  :=
  match n with
  | 0 => fun _ => fun_to_vec (λ _, [#])
  | S n => fun v =>
    Vector.map2 (λ a u, a ::: u) (vsplitl v) (vunjoin' $ vsplitr v)
  end.

#[export] Instance vjoin_unjoin {A n m} :
  Cancel eq (@vjoin A n m) vunjoin.
Proof.
  hnf.
  induction m; [intros; inv_all_vec_fin; done|].
  cbn.
  intros v.
  induction v using vec_add_inv.
  rewrite vsplitl_app, vsplitr_app.
  rewrite IHm.
  done.
Qed.

#[export] Instance vjoin'_unjoin' {A n m} :
  Cancel eq (@vjoin' A n m) vunjoin'.
Proof.
  hnf.
  induction n; [intros; inv_all_vec_fin; done|].
  cbn.
  intros v.
  induction v using vec_add_inv.
  rewrite vsplitl_app, vsplitr_app.
  rewrite 2 vmap_zip_with.
  cbn.
  rewrite vzip_with_to_vmap_l, vzip_with_to_vmap_r, 2 Vector.map_id, IHn.
  done.
Qed.


#[export] Instance vunjoin_join {A n m} :
  Cancel eq vunjoin (@vjoin A n m).
Proof.
  hnf.
  intros v.
  induction v; [done|].
  cbn.
  rewrite vsplitl_app, vsplitr_app.
  congruence.
Qed.

Lemma vjoin'_nil {A n} : @vjoin' A n 0 [#] = Vector.cast [#] (eq_sym (Nat.mul_0_r n)).
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  f_equal.
  apply proof_irrel.
Qed.

Lemma vunjoin'_nil {A n} v : @vunjoin' A n 0 v = [#].
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  done.
Qed.

#[export] Instance vunjoin'_join' {A n m} :
  Cancel eq vunjoin' (@vjoin' A n m).
Proof.
  hnf.
  induction n.
  - intros v.
    cbn.
    induction v; cbn in *; unfold compose; inv_all_vec_fin; congruence.
  - intros v.
    cbn.
    rewrite vsplitl_app, vsplitr_app.
    rewrite IHn.
    rewrite vzip_with_map.
    rewrite vzip_with_diag.
    apply vmap_id'.
    intros; now rewrite <- Vector.eta.
Qed.

Lemma lookup_vjoin {A n m} (v : vec (vec A n) m) i :
  vjoin v !!! i = v !!! (fin_split i).1 !!! (fin_split i).2.
Proof.
  revert i; induction v; [intros ?; inv_all_vec_fin|refine (fin_mul_ind _ _)].
  intros i j.
  inv_all_vec_fin.
  - cbn.
    rewrite lookup_vapp_L.
    rewrite fin_sum_case_L.
    done.
  - cbn.
    rewrite lookup_vapp_R, fin_sum_case_R.
    rewrite IHv.
    done.
Qed.

Lemma vlookup_0_vhd {A n} (v : vec A (S n)) : v !!! 0%fin = vhd v.
Proof.
  now inv_all_vec_fin.
Qed.

Lemma lookup_vtl {A n} (v : vec A (S n)) i :
  vtl v !!! i = v !!! FS i.
Proof.
  now inv_all_vec_fin.
Qed.

Lemma lookup_vjoin' {A n m} (v : vec (vec A n) m) i :
  vjoin' v !!! i = v !!! (fin_split i).2 !!! (fin_split i).1.
Proof.
  revert v i; induction n; [intros ?; apply fin_0_inv|].
  intros v.
  refine (fin_mul_ind _ _).
  intros i j.
  inv_all_vec_fin.
  - cbn.
    rewrite lookup_vapp_L.
    rewrite fin_sum_case_L.
    rewrite vlookup_map.
    cbn.
    rewrite vlookup_0_vhd.
    done.
  - cbn.
    rewrite lookup_vapp_R, fin_sum_case_R.
    rewrite IHn.
    rewrite vlookup_map, lookup_vtl.
    done.
Qed.

Lemma lookup_vunjoin {A n m} (v : vec A (n * m)) i j :
  vunjoin v !!! i !!! j = v !!! fin_prod i j.
Proof.
  rewrite <- vjoin_unjoin.
  rewrite lookup_vjoin, vjoin_unjoin.
  rewrite fin_split_prod.
  done.
Qed.

Lemma lookup_vunjoin' {A n m} (v : vec A (n * m)) i j :
  vunjoin' v !!! i !!! j = v !!! fin_prod j i.
Proof.
  rewrite <- vjoin'_unjoin'.
  rewrite lookup_vjoin', vjoin'_unjoin'.
  rewrite fin_split_prod.
  done.
Qed.



Lemma vjoin_to_vjoin' {A n m} (v : vec (vec A n) m) :
  vjoin v = permute_vec fin_prod_comm (vjoin' v).
Proof.
  apply vec_eq.
  intros i.
  induction i using fin_mul_ind.
  rewrite lookup_vjoin, lookup_permute_vec,
    lookup_vjoin', fin_prod_comm_prod, 2 fin_split_prod.
  done.
Qed.

Lemma vjoin'_to_vjoin {A n m} (v : vec (vec A n) m) :
  vjoin' v = permute_vec fin_prod_comm (vjoin v).
Proof.
  rewrite vjoin_to_vjoin'.
  now rewrite (permute_vec_cancel _ _ _).
Qed.


Lemma vunjoin_to_vunjoin' {A n m} (v : vec A (n * m)) :
  vunjoin v = vunjoin' (permute_vec fin_prod_comm v).
Proof.
  apply vec_eq.
  intros i.
  apply vec_eq.
  intros j.
  rewrite lookup_vunjoin, lookup_vunjoin', lookup_permute_vec, fin_prod_comm_prod.
  done.
Qed.

Lemma vunjoin'_to_vunjoin {A n m} (v : vec A (n * m)) :
  vunjoin' v = vunjoin (permute_vec fin_prod_comm v).
Proof.
  rewrite vunjoin_to_vunjoin'.
  now rewrite (permute_vec_cancel _ _ _).
Qed.