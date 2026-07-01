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



Lemma div_sub_one_r n m :
  ((n - m) / m = n / m - 1)%nat.
Proof.
  destruct_decide (decide (n < m)).
  - replace (n - m)%nat with O by lia.
    rewrite Nat.Div0.div_0_l, Nat.div_small; lia.
  - replace (n / m)%nat with ((1 * m + (n - m)) / m)%nat by (f_equal; lia).
    destruct m.
    + rewrite 2 Nat.div_0_r; done.
    + rewrite Nat.div_add_l by lia.
      lia.
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

Lemma vlookup_eq_nth {A n} (v : vec A n) i :
  v !!! i = Vector.nth v i.
Proof.
  revert i; induction v; [apply fin_0_inv|apply fin_S_inv; [done|]].
  intros i.
  apply IHv.
Qed.

Lemma vlookup_const {A n} (a : A) (i : fin n) :
  Vector.const a n !!! i = a.
Proof.
  now rewrite vlookup_eq_nth, Vector.const_nth.
Qed.



(* FIXME: Move, replace in Aux_stdpp_base *)

#[export] Instance omap2_Proper {A B C}
  `{RA : relation A, RB : relation B, RC : relation C}
  (f : A -> B -> C) {Hf : Proper (RA ==> RB ==> RC) f} :
  Proper (option_Forall2 RA ==> option_Forall2 RB ==> option_Forall2 RC) (omap2 f).
Proof.
  intros ma ma' Hma mb mb' Hmb.
  induction Hma as [a a' Ha|]; [|constructor].
  induction Hmb as [b b' Hb|]; [|constructor].
  constructor.
  now f_equiv.
Qed.
#[export] Instance omap2_Proper_equiv {A B C}
  `{RA : Equiv A, RB : Equiv B, RC : Equiv C}
  (f : A -> B -> C) {Hf : Proper (equiv ==> equiv ==> equiv) f} :
  Proper (equiv ==> equiv ==> equiv) (omap2 f).
Proof.
  apply omap2_Proper, Hf.
Qed.

Import stdpp.fin.

(* FIXME: Move *)
(* Record finperm n m := {
  finperm_vec : vec (fin m) n
}.

Definition finperm_fun {n m} (f : finperm n m) : fin n -> fin m :=
  (f.(finperm_vec n m) !!!.).
 *)
Notation id := Datatypes.id.


#[export] Instance fin_perm_equiv {n m} : Equiv (fin n -> fin m) :=
  pointwise_relation (fin n) eq.

Definition fin_add_comm {n m} (i : fin (n + m)) : fin (m + n) :=
  match fin_sum_case i with
  | inl i => Fin.R _ i
  | inr i => Fin.L _ i
  end.

Definition fin_perm_stack {n m n' m'} (f : fin n -> fin m) (g : fin n' -> fin m') :
  fin (n + n') -> fin (m + m') :=
  fun i =>
  match fin_sum_case i with
  | inl i => Fin.L _ (f i)
  | inr i => Fin.R _ (g i)
  end.

Lemma fin_perm_stack_L {n m n' m'} (f : fin n -> fin m) (g : fin n' -> fin m')
  i : fin_perm_stack f g (Fin.L _ i) = Fin.L _ (f i).
Proof.
  unfold fin_perm_stack.
  rewrite fin_sum_case_L.
  done.
Qed.

Lemma fin_perm_stack_R {n m n' m'} (f : fin n -> fin m) (g : fin n' -> fin m')
  i : fin_perm_stack f g (Fin.R _ i) = Fin.R _ (g i).
Proof.
  unfold fin_perm_stack.
  rewrite fin_sum_case_R.
  done.
Qed.

Definition fin_perm_assoc {n m o} (i : fin (n + m + o)) : fin (n + (m + o)) :=
  match fin_sum_case i with
  | inl i => match fin_sum_case i with
    | inl i => Fin.L _ i
    | inr i => Fin.R _ (Fin.L _ i)
    end
  | inr i => Fin.R _ (Fin.R _ i)
  end.

Definition fin_perm_invassoc {n m o} (i : fin (n + (m + o))) : fin (n + m + o) :=
  match fin_sum_case i with
  | inl i => Fin.L _ (Fin.L _ i)
  | inr i =>
    match fin_sum_case i with
    | inl i => Fin.L _ (Fin.R _ i)
    | inr i => Fin.R _ i
    end
  end.

#[export] Instance fin_perm_stack_proper {n m n' m'} :
  Proper (equiv ==> equiv ==> equiv) (@fin_perm_stack n m n' m').
Proof.
  intros f f' Hf g g' Hg.
  intros i.
  induction i as [i|i] using fin_add_inv.
  - rewrite 2 fin_perm_stack_L, Hf.
    done.
  - rewrite 2 fin_perm_stack_R, Hg.
    done.
Qed.


#[export] Instance fin_compose_proper_gen {n m o} :
  Proper (equiv ==> equiv ==> equiv)
    (λ (g : fin m -> fin o) (f : fin n -> fin m), λ i, g (f i)).
Proof.
  intros f f' Hf g g' Hg.
  intros i.
  cbn.
  now rewrite Hf, Hg.
Qed.

#[export] Instance fin_inv_compose_proper_gen {n m o} :
  Proper (equiv ==> equiv ==> equiv)
    (λ (f : fin n -> fin m) (g : fin m -> fin o), λ i, g (f i)).
Proof.
  intros f f' Hf g g' Hg.
  intros i.
  cbn.
  now rewrite Hf, Hg.
Qed.

#[export] Instance fin_compose_proper {n m o} :
  Proper (equiv ==> equiv ==> equiv) (@compose (fin n) (fin m) (fin o)).
Proof.
  apply _.
Qed.


Definition fin_perm_mul_S_r {n m} (i : fin (n * S m)) : fin (n + n * m) :=
  let '(il, ir) := fin_split i in
  fin_S_inv (λ _, fin (n + n * m)) (Fin.L _ il)
    (λ ir', Fin.R _ (fin_prod il ir')) ir.

Lemma fin_prod_comm_S_r {n m} : @fin_prod_comm n (S m) ≡
  fin_perm_stack id (@fin_prod_comm n m) ∘ fin_perm_mul_S_r.
Proof.
  intros i.
  induction i as [il ir] using fin_mul_ind.
  cbn.
  rewrite fin_prod_comm_prod.
  unfold fin_perm_mul_S_r.
  rewrite fin_split_prod.
  induction ir as [|ir'] using fin_S_inv.
  - cbn.
    rewrite fin_perm_stack_L.
    done.
  - cbn.
    rewrite fin_perm_stack_R, fin_prod_comm_prod.
    done.
Qed.

Definition fin_perm_invmul_S_r {n m} (i : fin (n + n * m)) : fin (n * S m) :=
  match fin_sum_case i with
  | inl i => fin_prod i 0
  | inr i =>
    let '(il, ir') := fin_split i in
    fin_prod il (FS ir')
  end.

Lemma fin_prod_comm_S_l {n m} : @fin_prod_comm (S n) m ≡
  fin_perm_invmul_S_r ∘ fin_perm_stack id (@fin_prod_comm n m).
Proof.
  intros i.
  induction i as [il ir] using fin_mul_ind.
  cbn.
  rewrite fin_prod_comm_prod.
  induction il as [|il'] using fin_S_inv.
  - cbn.
    rewrite fin_perm_stack_L.
    unfold fin_perm_invmul_S_r.
    rewrite fin_sum_case_L.
    done.
  - cbn.
    rewrite fin_perm_stack_R.
    unfold fin_perm_invmul_S_r.
    rewrite fin_sum_case_R, fin_prod_comm_prod, fin_split_prod.
    done.
Qed.

Lemma fin_perm_stack_id {n m} : @fin_perm_stack n n m m (λ i, i) (λ i, i) ≡
  (λ i, i).
Proof.
  intros i.
  induction i using fin_add_inv.
  - now rewrite fin_perm_stack_L.
  - now rewrite fin_perm_stack_R.
Qed.


Definition cast_fin_perm {n n' m m'}
  (Hn : n = n') (Hm : m = m') (f : fin n -> fin m) : fin n' -> fin m' :=
  match Nat.eq_dec n n' with
  | right HFn => False_rect _ (HFn Hn)
  | left Hn' =>
    match Nat.eq_dec m m' with
    | right HFm => False_rect _ (HFm Hm)
    | left Hm' =>
      match Hn', Hm' with
      | eq_refl, eq_refl => f
      end
    end
  end.

Lemma cast_fin_perm_refl {n m}
  (Hn : n = n) (Hm : m = m) (f : fin n -> fin m) :
  cast_fin_perm Hn Hm f = f.
Proof.
  unfold cast_fin_perm.
  case_match; [|done].
  case_match; [|done].
  rewrite 2 (proof_irrel _ eq_refl).
  done.
Qed.

Lemma cast_fin_perm_apply {n m n' m'}
  (Hn : n = n') (Hm : m = m') (f : fin n -> fin m) i :
  cast_fin_perm Hn Hm f i = Fin.cast (f (Fin.cast i (eq_sym Hn))) Hm.
Proof.
  subst.
  rewrite cast_fin_perm_refl.
  now rewrite 2 fcast_id.
Qed.



#[export] Instance cast_fin_perm_proper {n n' m m'}
  (Hn : n = n') (Hm : m = m') : Proper ((≡) ==> (≡)) (cast_fin_perm Hn Hm).
Proof.
  intros f f' Hf.
  subst.
  rewrite 2 cast_fin_perm_refl.
  done.
Qed.

Notation finL := (Fin.L _).
Notation finR := (Fin.R _).

Class FinCases (n : nat) (T : Type) := mk_FinCases {
  fin_cases : fin n -> T;
  fin_cases_rev : T -> fin n;
}.

#[global] Arguments mk_FinCases {_ _} _ _ : assert.
#[global] Arguments fin_cases {_ _} {_} / _ : assert.
#[global] Arguments fin_cases_rev {_ _} {_} / _ : assert.


#[export] Instance fin_cases_refl n : FinCases n (fin n) | 100 :=
  mk_FinCases (fun i => i) (fun i => i).

#[export] Instance fin_cases_succ `{FinCases n T} : FinCases (S n) (option T) :=
  mk_FinCases (fin_S_inv (λ _, option T) None (Some ∘ fin_cases)) (from_option (FS ∘ fin_cases_rev) 0%fin).

#[export] Instance fin_cases_add `{FinCases n Tn, FinCases m Tm} :
  FinCases (n + m) (Tn + Tm) :=
  mk_FinCases (sum_map fin_cases fin_cases ∘ fin_sum_case)
    (sum_rect _ (finL ∘ fin_cases_rev) (finR ∘ fin_cases_rev)).

#[export] Instance fin_cases_prod `{FinCases n Tn, FinCases m Tm} :
  FinCases (n * m) (Tn * Tm) :=
  mk_FinCases (prod_map fin_cases fin_cases ∘ fin_split)
    (uncurry fin_prod ∘ prod_map (fin_cases_rev) (fin_cases_rev)).

Definition fin_mid_comm {n m o p} (i : fin ((n + m) + (o + p))) :
  fin ((n + o) + (m + p)) :=
  match fin_cases i with
  | inl (inl i) => finL (finL i)
  | inl (inr i) => finR (finL i)
  | inr (inl i) => finL (finR i)
  | inr (inr i) => finR (finR i)
  end.

Fixpoint vec_join {A n} (v : vec (option A) n) : option (vec A n) :=
  match v with
  | [#] => Some [#]
  | h ::: v => h ≫= λ h, (h :::.) <$> vec_join v
  end.

Lemma vec_join_Some {A n} (v : vec (option A) n) u :
  vec_join v = Some u <-> v = vmap Some u.
Proof.
  revert u; induction v; intros u.
  - inv_all_vec_fin.
    done.
  - cbn.
    inv_all_vec_fin.
    cbn.
    split.
    + rewrite bind_Some.
      intros (x' & -> & (u' & ->%IHv & [<- ->]%vcons_inj)%fmap_Some).
      done.
    + intros [-> ->]%vcons_inj.
      cbn.
      erewrite (IHv _).2 by done.
      done.
Qed.

Definition nat_to_ofin (n i : nat) : option (fin n) :=
  (@nat_to_fin i n) <$> guard (i < n)%nat.

Lemma nat_to_ofin_fin {n} (i : fin n) : nat_to_ofin n i = Some i.
Proof.
  unfold nat_to_ofin.
  pose proof (fin_to_nat_lt i).
  case_guard; [|done].
  cbn.
  f_equal.
  apply nat_to_fin_to_nat.
Qed.

Definition nat_fun_to_fin_perm (n m : nat) (f : nat -> nat) : option (fin n -> fin m) :=
  (λ v, (v!!!.)) <$> vec_join (fun_to_vec (n:=n) (λ i, nat_to_ofin m (f i))).

Lemma nat_lt_ind {n} (P : forall i : nat, Prop)
  (HP : forall (i : fin n), P i) : forall i, i < n -> P i.
Proof.
  intros i Hi.
  rewrite <- (fin_to_nat_to_fin _ _ Hi).
  auto.
Qed.



Lemma fin_add_comm_L {n m} i : @fin_add_comm n m (finL i) = finR i.
Proof.
  unfold fin_add_comm.
  now rewrite fin_sum_case_L.
Qed.

Lemma fin_add_comm_R {n m} i : @fin_add_comm n m (finR i) = finL i.
Proof.
  unfold fin_add_comm.
  now rewrite fin_sum_case_R.
Qed.


(* FIXME: Move *)
Definition fin_perm_inv_cast {n m} (Hnm : n = m) (f : fin n -> fin m) :
  fin m -> fin n :=
  cast_fin_perm Hnm eq_refl (fin_perm_inv (cast_fin_perm eq_refl (eq_sym Hnm) f)).

Lemma fin_perm_inv_cast_id {n} (Hn : n = n) (f : fin n -> fin n) :
  fin_perm_inv_cast Hn f = fin_perm_inv f.
Proof.
  unfold fin_perm_inv_cast.
  rewrite 2 cast_fin_perm_refl.
  done.
Qed.


Fixpoint list_split {A} (P : A -> Prop) {HP : forall a, Decision (P a)}
  (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | a :: l =>
    let '(lP, lNP) := list_split P l in
    if decide (P a) then (a :: lP, lNP) else (lP, a :: lNP)
  end.



Notation "x '←@{' M '}' y ; z" := (mbind (M:=M%type) (λ x : _, z) y)
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x '←@{' M '}' y ; z" := (mbind (M:=M%type) (λ x : _, z) y)
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "x '←@{' M ; b '}' y ; z" := (mbind (M:=M%type) (λ x : b%type, z) y)
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x '←@{' M ; b '}' y ; z" := (mbind (M:=M%type) (λ x : b%type, z) y)
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.


Infix "'<$>@{' M '}'" := (fmap (M:=M%type)) (at level 61, left associativity, only parsing) : stdpp_scope.

(* FIXME: Move *)
Notation "m ≫=@{ M } f" := (mbind (M:=M%type) f m) (at level 60, right associativity, only parsing) : stdpp_scope.

Notation "m ≫=@{ M ; b } f" := (mbind (M:=M%type) (A:=b%type) f m) (at level 60, right associativity, only parsing) : stdpp_scope.



Import stdpp.list.

Lemma decide_ext' {P Q} `{Decision P, Decision Q}
  {A} {R : relation A} {x y x' y' : A} :
  (P <-> Q) ->
  (P -> Q -> R x x') -> (~ P -> ~ Q -> R y y') ->
  R (if decide P then x else y) (if decide Q then x' else y').
Proof.
  do 2 case_decide;
  naive_solver.
Qed.

Lemma lookup_kmap_None_1 `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) {Hf : Inj eq eq f} {A} (m : M1 A) (j : K2) :
  (forall i, j = f i -> m !! i = None) -> (kmap f m :> M2 A) !! j = None.
Proof.
  now rewrite lookup_kmap_None.
Qed.


Lemma lookup_kmap_None_1' `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) {Hf : Inj eq eq f} {A} (m : M1 A) (j : K2) :
  (forall i, f i <> j) -> (kmap f m :> M2 A) !! j = None.
Proof.
  intros Hi; apply (lookup_kmap_None_1 f); now intros ? []%symmetry%Hi.
Qed.




Definition list_index `{EqDecision A} (x : A) : list A -> option nat :=
  fix go l :=
  match l with
  | [] => None
  | a :: l =>
    if decide (x = a) then Some 0 else S <$> go l
  end.

Section list_index.


Context `{EqDecision A}.
Implicit Type l : list A.


Lemma list_index_eq_find (x : A) l :
  list_index x l = fst <$> list_find (eq x) l.
Proof.
  induction l; [done|].
  cbn.
  case_decide; [done|].
  rewrite IHl.
  now destruct (list_find _ _).
Qed.

Lemma list_index_is_Some x l :
  is_Some (list_index x l) <-> x ∈ l.
Proof.
  rewrite list_index_eq_find.
  rewrite fmap_is_Some.
  split; [|intros Hx; apply (list_find_elem_of _ _ x Hx eq_refl)].
  now intros [[] (?%elem_of_list_lookup_2 & <- & _)%list_find_Some].
Qed.

Lemma list_index_Some x l i :
  list_index x l = Some i <->
  l !! i = Some x /\ forall j y, l !! j = Some y -> j < i -> x <> y.
Proof.
  rewrite list_index_eq_find.
  rewrite fmap_Some, exists_pair.
  setoid_rewrite list_find_Some.
  naive_solver.
Qed.

Lemma list_index_None x l :
  list_index x l = None <-> x ∉ l.
Proof.
  rewrite <- list_index_is_Some.
  now rewrite eq_None_not_Some.
Qed.

Lemma list_index_None_1 x l :
  list_index x l = None -> x ∉ l.
Proof.
  now rewrite list_index_None.
Qed.

Lemma list_index_None_2 x l :
  x ∉ l -> list_index x l = None.
Proof.
  now rewrite list_index_None.
Qed.


Lemma list_index_Some_NoDup x l i :
  NoDup l ->
  list_index x l = Some i <-> l !! i = Some x.
Proof.
  intros Hdup.
  rewrite list_index_Some.
  rewrite <- (and_True (l !! i = Some x)) at 2.
  apply and_iff_from_l; [reflexivity|intros Hli _].
  apply iff_True_1.
  intros j y Hlj Hji ->.
  enough (i = j) by lia.
  revert Hli Hlj.
  now apply NoDup_lookup.
Qed.

Lemma list_index_inj x y l i :
  list_index x l = Some i -> list_index y l = Some i -> x = y.
Proof.
  rewrite 2 list_index_Some.
  intros [] [].
  congruence.
Qed.

Lemma list_index_lt x l i :
  list_index x l = Some i -> i < length l.
Proof.
  now intros [?%lookup_lt_Some _]%list_index_Some.
Qed.

Lemma list_index_app x l l' :
  list_index x (l ++ l') =
  list_index x l ∪ (Nat.add (length l) <$> list_index x l').
Proof.
  induction l; [cbn; now destruct (list_index _ _)|].
  cbn.
  case_decide; [now rewrite union_Some_l|].
  rewrite IHl.
  unfold union, option_union, union_with, option_union_with.
  repeat (destruct (list_index _ _)); reflexivity.
Qed.

Lemma list_index_fmap_gen `{EqDecision B} (f : A -> B) x l :
  list_index x (f <$> l) = fst <$> list_find (λ y, x = f y) l.
Proof.
  induction l; [done|].
  cbn.
  case_decide; [done|].
  rewrite IHl.
  now destruct (list_find _ _).
Qed.

Lemma list_index_fmap `{EqDecision B} (f : A -> B) {Hf : Inj eq eq f} x l :
  list_index (f x) (f <$> l) = list_index x l.
Proof.
  induction l; [done|].
  cbn.
  apply decide_ext'; [|intros; now f_equal..].
  apply (inj_iff f).
Qed.

Lemma list_index_fmap' `{EqDecision B} (x : A) (f : A -> B) {Hf : Inj eq eq f} y l :
  y = f x -> list_index y (f <$> l) = list_index x l.
Proof.
  intros ->.
  apply (list_index_fmap f).
Qed.

End list_index.

Lemma list_lookup_omap_all_is_Some `(f : A -> option B) (l : list A) (i : nat)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l !! i = l !! i ≫= f.
Proof.
  rewrite <- Forall_forall in Hf.
  revert i;
  induction Hf; [now intros []|intros i].
  cbn.
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  destruct i; [cbn; now rewrite Hfx|].
  cbn.
  apply IHHf.
Qed.

Lemma length_omap_all_is_Some `(f : A -> option B) (l : list A)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  length (omap f l) = length l.
Proof.
  rewrite <- Forall_forall in Hf.
  induction Hf; [done|cbn].
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  cbn.
  f_equal; apply IHHf.
Qed.

Lemma omap_all_is_Some_default `(f : A -> option B) (l : list A) (g : A -> B)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l = (λ i, default (g i) (f i)) <$> l.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl).
  - now rewrite length_fmap; apply length_omap_all_is_Some.
  - intros i x y.
    rewrite length_fmap.
    intros Hi.
    rewrite list_lookup_omap_all_is_Some by easy.
    rewrite list_lookup_fmap.
    destruct (l !! i) as [li|]; [|easy].
    cbn.
    destruct (f li); [|easy].
    cbn; congruence.
Qed.


Lemma nat_to_ofin_S_S n i : nat_to_ofin (S n) (S i) = FS <$> nat_to_ofin n i.
Proof.
  unfold nat_to_ofin.
  apply (inj (fmap fin_to_nat)).
  do 2 case_guard; [|exfalso; lia..|]; [|done].
  cbn.
  now rewrite 2 fin_to_nat_to_fin.
Qed.



Definition vec_find {A} (P : A -> Prop) {HP : forall a, Decision (P a)}
  : forall {n} (v : vec A n), option (fin n * A) :=
  fix go n v :=
  match v with
  | [#] => None
  | a ::: v =>
    if decide (P a) then Some (0%fin, a) else
      prod_map FS id <$> go _ v
  end.


Fixpoint vec_index `{EqDecision A} (a : A) {n} (v : vec A n) : option (fin n) :=
  match v with
  | [#] => None
  | a' ::: v =>
    if decide (a = a') then Some 0%fin else
      FS <$> vec_index a v
  end.

Lemma fin_to_nat_vec_index `{EqDecision A} (a : A) {n} (v : vec A n) :
  fin_to_nat <$> (vec_index a v) = list_index a v.
Proof.
  induction n; inv_all_vec_fin; [done|].
  cbn.
  case_decide; [done|].
  rewrite <- IHn.
  now destruct (vec_index _ _).
Qed.

Lemma vec_index_to_list_index `{EqDecision A} (a : A) {n} (v : vec A n) :
  vec_index a v = list_index a v ≫= nat_to_ofin n.
Proof.
  rewrite <- fin_to_nat_vec_index.
  destruct (vec_index _ _) as [i|]; [|done].
  cbn.
  rewrite nat_to_ofin_fin.
  done.
Qed.



(* FIXME: Move *)
Lemma vmap_vzip_with {A B C D} (f : C -> D) (g : A -> B -> C) {n}
  (v w : vec _ n) :
  vmap f (vzip_with g v w) = vzip_with (λ a b, f (g a b)) v w.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.
Lemma fst_vzip {A} {n} (v w : vec A n) :
  vmap fst (vzip_with pair v w) = v.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.
Lemma snd_vzip {A} {n} (v w : vec A n) :
  vmap snd (vzip_with pair v w) = w.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.


(* FIXME: Move *)
Fixpoint vimap {A B} {n} : forall (f : fin n -> A -> B) (v : vec A n), vec B n :=
  match n with
  | 0 => fun _ _ => [#]
  | S n =>
    fun f v => (f 0%fin (vhd v)) ::: vimap (λ i, f (FS i)) (vtl v)
  end.

Lemma vlookup_imap {A B} {n} (f : fin n -> A -> B) (v : vec A n) (i : fin n) :
  vimap f v !!! i = f i (v !!! i).
Proof.
  induction n; inv_all_vec_fin; cbn; [done|].
  apply IHn.
Qed.

Lemma vimap_ext {A B} {n} f g (v : vec A n) :
  (forall i, f i (v !!! i) = g i (v !!! i)) ->
  vimap f v =@{vec B n} vimap g v.
Proof.
  intros Hfg.
  induction n; inv_all_vec_fin; cbn; [done|].
  f_equal; [apply Hfg|].
  apply IHn; intros; apply Hfg.
Qed.

Notation vmap_map := (Vector.map_map _ _ _).

Lemma vimap_to_vfinseq {A B} {n} (f : fin n -> B) (v : vec A n) :
  vimap (λ i _, f i) v = vmap f (vfinseq n).
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_map, vlookup_imap, lookup_vfinseq.
  done.
Qed.

Lemma vimap_to_vmap {A B} (f : A -> B) {n} (v : vec A n) :
  vimap (λ _, f) v = vmap f v.
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_map, vlookup_imap.
  done.
Qed.

Lemma vimap_vmap {A B C} {n} (f : fin n -> B -> C) (g : A -> B) v :
  vimap f (vmap g v) = vimap (λ i a, f i (g a)) v.
Proof.
  apply vec_eq; intros i.
  rewrite 2 vlookup_imap, vlookup_map.
  done.
Qed.

Lemma vmap_vimap {A B C} (g : B -> C) {n} (f : fin n -> A -> B) v :
  vmap g (vimap f v) = vimap (λ i a, g (f i a)) v.
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_map, 2 vlookup_imap.
  done.
Qed.

Lemma vec_to_vmap_lookup_vfinseq {A n} (v : vec A n) :
  v = vmap (v!!!.) (vfinseq n).
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_map, lookup_vfinseq.
  done.
Qed.

Lemma vimap_vfinseq {A} {n} (f : fin n -> fin n -> A) :
  vimap f (vfinseq n) = vmap (λ i, f i i) (vfinseq n).
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_imap, vlookup_map, lookup_vfinseq.
  done.
Qed.

Lemma vimap_to_vmap_vfinseq_lookup {A B} {n} (f : fin n -> A -> B) v :
  vimap f v = vmap (λ i, f i (v !!! i)) (vfinseq n).
Proof.
  rewrite (vec_to_vmap_lookup_vfinseq v), vimap_vmap at 1.
  rewrite vimap_vfinseq.
  done.
Qed.

(* Lemma vimap_vzip_with {A B C D} {n} (f : fin n -> C -> D) (g : A -> B -> C) *)

Lemma vec_prod_eta {A B n} (v : vec (A * B) n) :
  v = vzip (vmap fst v) (vmap snd v).
Proof.
  apply vec_eq; intros i.
  rewrite vlookup_zip_with, 2 vlookup_map.
  apply surjective_pairing.
Qed.

Fixpoint vcount {A} (P : A -> Prop) {HP : forall a, Decision (P a)}
  {n} (v : vec A n) : nat :=
  match v with
  | [#] => 0
  | a ::: v =>
    if decide (P a) then S (vcount P v) else vcount P v
  end.

(* Fixpoint vfilter {A} (P : A -> Prop) {HP : forall a, Decision (P a)}
  {n} (v : vec A n) : vec A (vcount P ) *)




Lemma gmap_map_insert `{Countable A} (m : gmap A A) (a b : A) :
  pointwise_relation A eq (gmap_map (<[a := b]> m))
    (<[a := b]> (gmap_map m)).
Proof.
  intros c.
  rewrite fn_lookup_insert_case.
  unfold gmap_map.
  rewrite lookup_insert_case.
  now case_decide.
Qed.


Lemma gmap_map_empty `{Countable A} :
  pointwise_relation A eq (gmap_map (∅ :> gmap A A))
    id.
Proof.
  intros c.
  unfold gmap_map.
  now rewrite lookup_empty.
Qed.

Lemma list_filter_all {A} {P : A -> Prop} `{HP : forall a, Decision (P a)}
  (l : list A) :
  (forall a, a ∈ l -> P a) ->
  filter P l = l.
Proof.
  rewrite <- Forall_forall.
  intros Hl.
  induction Hl; [reflexivity|].
  cbn.
  rewrite decide_True by easy.
  f_equal.
  apply IHHl.
Qed.

Lemma list_filter_none {A} {P : A -> Prop} `{HP : forall a, Decision (P a)}
  (l : list A) :
  (forall a, a ∈ l -> ~ P a) ->
  filter P l = [].
Proof.
  rewrite <- Forall_forall.
  intros Hl.
  induction Hl; [reflexivity|].
  cbn.
  rewrite decide_False by easy.
  apply IHHl.
Qed.

Lemma NoDup_perm_filter_out `{EqDecision A} (l : list A) (a : A) :
  NoDup l -> a ∈ l ->
  l ≡ₚ a :: filter (.≠ a) l.
Proof.
  intros Hl Ha.
  apply elem_of_list_split in Ha as Hspl.
  destruct Hspl as (l1 & l2 & ->).
  rewrite <- Permutation_middle in Hl |- *.
  f_equiv.
  apply NoDup_cons in Hl as [Hal Hdup].
  cbn.
  rewrite decide_False by easy.
  symmetry.
  apply eq_reflexivity.
  apply list_filter_all.
  congruence.
Qed.

(* FIXME: Move *)
Lemma filter_nil_iff {A} (P : A -> Prop) {HP : forall x, Decision (P x)}
  (l : list A) : filter P l = [] <-> (forall x, x ∈ l -> ~ P x).
Proof.
  split; [|now eauto using list_filter_none].
  unfold not.
  intros;
  eapply filter_nil_not_elem_of; eauto.
Qed.

Lemma vtake_vmap {A B} (f : A -> B) {n} (i : fin n) (v : vec A n) :
  vtake i (vmap f v) = vmap f (vtake i v).
Proof.
  induction i; inv_all_vec_fin; cbn; f_equal; done.
Qed.

Lemma filter_fmap_prod_map_id_r {A B C} (P : C -> Prop) {HP : forall x, Decision (P x)}
  (f : A -> B) (l : list (A * C)) :
  filter (λ i, P i.2) (prod_map f id <$> l) =
  prod_map f id <$> filter (λ i, P i.2) l.
Proof.
  induction l; [done|].
  cbn; simpl.
  case_decide; cbn; f_equal; done.
Qed.

Lemma list_filter_ext_lookup {A} (P Q : A -> Prop)
  {HP : forall x, Decision (P x)} {HQ : forall x, Decision (Q x)}
  (l l' : list A) :
  Forall2 (λ x y, (P x <-> Q y) /\ (P x -> Q y -> x = y)) l l' ->
  filter P l = filter Q l'.
Proof.
  intros Hl.
  induction Hl; [done|].
  destruct_and!.
  cbn.
  apply decide_ext'; [done|now intros; f_equal; auto|..].
  intros; done.
Qed.