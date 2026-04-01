From TensorRocq Require Import Tensor TensorGraph.
From QuantumLib Require Export Complex.
From TensorRocqEx Require Import Rmodeq ZXCore. 
Open Scope nat_scope.

(* FIXME: Move somewhere else *)
Add Parametric Morphism : Cexp with signature
  Rmodeq (2 * PI) ==> eq as Cexp_modeq_2PI.
Proof.
  unfold Cexp.
  intros ? ? Heq.
  f_equal;
  now rewrite Heq.
Qed.

Add Parametric Morphism n m : (@zsp n m) with signature
  Rmodeq (2 * PI) ==> equiv as zsp_modeq_2PI.
Proof.
  intros r r' Heq v w Hv Hw.
  unfold zsp.
  erewrite Cexp_modeq_2PI by apply Heq.
  done.
Qed.

Add Parametric Morphism n m : (@xsp n m) with signature
  Rmodeq (2 * PI) ==> equiv as xsp_modeq_2PI.
Proof.
  intros r r' Heq v w Hv Hw.
  unfold xsp.
  f_equal.
  f_equal.
  apply Cexp_modeq_2PI; case_match; now rewrite Heq.
Qed.

Notation "'ZXG'" := (CospanHyperGraph (bool * R)) (at level 0).

(* Check ZXG. *)
Definition h_stack' : @DimensionlessTensor C bool :=
  fun n m v w =>
  default C0 (uncurry h_stack ∘ Vector.splitat ((n+m)/2) <$>
  vec_cast_opt (v +++ w) ((n + m)/2 + (n+m)/2)).

Lemma h_stack'_refl n : h_stack' n n ≡ h_stack.
Proof.
  intros v w Hv Hw.
  unfold h_stack'.
  replace ((n + n) / 2) with n by (symmetry;
    etransitivity; [|apply (Nat.div_mul _ 2); lia];
    f_equal; lia).
  rewrite vec_cast_opt_refl.
  cbn.
  now rewrite Vector.splitat_append.
Qed.

Definition h_stack1' : @DimensionlessTensor C bool :=
  fun n m v w =>
  default C0 (uncurry h_stack ∘ Vector.splitat 1 <$>
  vec_cast_opt (v +++ w) (1 + 1)).

Lemma h_stack1'_11 : h_stack1' 1 1 ≡ h_stack.
Proof.
  exact (h_stack'_refl 1).
Qed.

Lemma h_stack1'_ne n m : n + m <> 2 ->
  h_stack1' n m ≡ const_tensor C0.
Proof.
  intros Hnm v w Hv Hw.
  unfold h_stack1'.
  now rewrite vec_cast_opt_ne by done.
Qed.

Lemma h_stack1'_ne_gen n m v w : n + m <> 2 ->
  h_stack1' n m v w = C0.
Proof.
  intros Hnm.
  unfold h_stack1'.
  now rewrite vec_cast_opt_ne by done.
Qed.

Lemma h_stack1'_spec {n m} (H : n + m = 2) (v : vec bool n) (w : vec bool m) : 
  h_stack1' n m v w =
  h ((v+++w)!!!Fin.cast 0 (eq_sym H))
    ((v+++w)!!!Fin.cast 1 (eq_sym H)).
Proof.
  unfold h_stack1'.
  generalize (v +++ w) as vw.
  clear v w.
  rewrite H.
  cbn.
  intros vw.
  induction vw as [v w'] using vec_S_inv.
  induction w' as [w ?] using vec_S_inv.
  apply Cmult_1_r.
Qed.

Require Import QlibInterface.

Lemma vlookup_lookup_total `{Inhabited A} {n} (v : vec A n) (i : fin n) :
  v !!! i = vec_to_list v !!! (i:>nat).
Proof.
  rewrite list_lookup_total_alt.
  now rewrite lookup_vec_to_list_fin.
Qed.




Definition ZXVERT := option (bool * R).

#[export] Instance ZXVERT_equiv : Equiv ZXVERT :=
  option_Forall2 (prod_relation eq (Rmodeq (2*PI))).


#[export] Instance ZXVERT_equiv_equivalence : Equivalence (≡@{ZXVERT}).
Proof. apply _. Qed.

Definition ZXCALC_tensor (x : ZXVERT) : DimensionlessTensor bool :=
  match x with
  | None => h_stack1'
  | Some (false, r)  => fun n m => @zsp n m r
  | Some (true, r) => fun n m => @xsp n m r
  end.

#[global] Arguments ZXCALC_tensor !_ /.

#[export] Instance ZXCALC_tensor_proper : 
  Proper ((≡) ==> (≡)) ZXCALC_tensor.
Proof.
  intros x x' Heq.
  induction Heq as [[[] r] [_ r'] [[= <-] Heq]|]; [cbn; intros n m..|done];
  cbn in Heq;
  now rewrite Heq.
Qed.

#[export] Instance ZXCALC : TensorLike C bool ZXVERT := {
  interpretTensor := ZXCALC_tensor;
}.

Lemma allb_forallb {n} b (v : vec bool n) :
  allb b v = forallb (eqb b) v.
Proof.
  induction v; [reflexivity|].
  cbn.
  now rewrite IHv.
Qed.

Add Parametric Morphism {A} : (@forallb A) with signature
  pointwise_relation A eq ==> (≡ₚ) ==> eq as forallb_Permutation.
Proof.
  intros P Q HPQ l l' Hl.
  apply Bool.eq_iff_eq_true.
  rewrite 2 forallb_forall.
  setoid_rewrite HPQ.
  rewrite <- 2 List.Forall_forall.
  now rewrite Hl.
Qed.



Lemma parity_perm {n m} (v : vec bool n) (w : vec bool m) :
  v ≡ₚ w ->
  parity v = parity w.
Proof.
  intros Hperm.
  apply Permutation_length in Hperm as Hnm.
  rewrite 2 length_vec_to_list in Hnm.
  subst m.
  unfold parity.
  rewrite 2 Vector.to_list_fold_left.
  rewrite 2 fold_symmetric by now intros; Btauto.btauto.
  apply (foldr_permutation_proper _ _).
  - solve_proper.
  - intros; Btauto.btauto.
  - now rewrite <- 2 vec_to_list_to_list.
Qed.


Lemma zsp_allb_app {n m n' m'} r v w v' w' :
  allb false (v +++ w) = allb false (v' +++ w') ->
  allb true (v +++ w) = allb true (v' +++ w') ->
  @zsp n m r v w = @zsp n' m' r v' w'.
Proof.
  intros Hfalse Htrue.
  unfold zsp.
  rewrite ! allb_forallb, <- ! forallb_app, <- ! vec_to_list_app,
    <- ! allb_forallb.
  now rewrite Hfalse, Htrue.
Qed.




(* TODO: Rework these and put them in TensorGraph *)

(* Definition relabel_vertex {T} (n m : nat) (tg : TensorGraph T) : TensorGraph T :=
  let '(mk_tg verts edges) := tg in
  let verts' :=
    match lookup n verts with
    | Some t => <[m := t]> (delete n verts)
    | None => verts
    end in
  let relabel_idx i := if i =? n then m else i in
  let edges' := (fun e : (nat * nat) =>
    let (s, d) := e in (relabel_idx s, relabel_idx d)) <$> edges in
  mk_cohg verts' edges'.


Definition has_edge (n m : nat) (es : list edge) : Prop :=
  (n, m) ∈ es \/ (m, n) ∈ es.

Definition connected {T} (n m : nat) (tg : TensorGraph T) : Prop :=
  is_key tg.1 n /\ is_key tg.1 m /\ has_edge n m tg.2.

Definition remove_vertex {T} (n : nat) (tg : TensorGraph T) : TensorGraph T :=
  let '(mk_cohg verts edges) := tg in
  let verts' := delete n verts in
  let edges' :=
    filter (fun e : (nat * nat) => let (s, d) := e in negb ((s =? n) || (d =? n))) edges in
  mk_cohg verts' edges'.

Definition remove_edge {T} (n m : nat) (tg : TensorGraph T) : TensorGraph T:=
  let '(mk_cohg verts edges) := tg in
  let edges' := filter (fun e : (nat * nat) => let (s, d) := e in ((s =? n) && (d =? m) || (s =? m) && (d =? n))) edges in
  mk_cohg verts edges'.

Definition successors {T} (n : nat) (tg : TensorGraph T) : list nat :=
  map snd (filter (fun e => fst e =? n) (snd tg)).

Definition predecessors {T}(n : nat) (tg : TensorGraph T) : list nat :=
  map fst (filter (fun e => snd e =? n) (snd tg)).

Fixpoint add_edges {T} (es : list (nat * nat))
  (tg : TensorGraph T) :=
  match es with
  | [] => tg
  | e :: es' => add_edge e (add_edges es' tg)
  end.


Definition rotation (n : nat) (zxg : ZXG) : option R :=
  snd <$> (zxg.1 !! n).

Definition vertex_type (n : nat) (zxg : ZXG) : option bool :=
  fst <$> (zxg.1 !! n).

Definition hopf (n m : nat) (zxg : ZXG) : ZXG :=
  remove_edge n m (remove_edge n m zxg).

Definition option_eqb_bool (a : option bool) (b : option bool) : bool :=
  match a with
  | Some x => match b with
              | Some y => eqb x y
              | None => false
              end
  | None => false
  end.

Definition fuse (n m : nat) (zxg : ZXG) : ZXG :=
  let preds' := (fun l => (l, n)) <$> predecessors m zxg in
  let succs' := (fun r => (n, r)) <$> successors m zxg in
  let preds'' := (fun l => (l, n)) <$> predecessors n zxg in
  let succs'' := (fun r => (n, r)) <$> successors n zxg in
  let rot_n : option R := rotation n zxg in
  let rot_m : option R := rotation m zxg in
  if option_eqb_bool (vertex_type n zxg) (vertex_type m zxg) then
    match rot_n with
    | Some r1 =>
      match rot_m with
      | Some r2 => add_vertex n (true, (r1 + r2)%R)
        (add_edges (preds' ++ preds'' ++ succs' ++ succs'') (remove_vertex n (remove_vertex m zxg)))
      | None => zxg
      end
    | None => zxg
    end
    else
      zxg. *)
