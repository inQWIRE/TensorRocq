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