Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp Aux_pos.

Require Import TensorExprDBSyntax.

(* Axiomatized rules for tensor expressions, which we will show are
  tensor-preserving *)

Local Open Scope positive_scope.
Local Open Scope list_scope.


(* FIXME: Move *)
Definition pos_swap (p : positive) : positive :=
  match p with | 1 => 2 | 2 => 1 | _ => p end%positive.

Inductive teq (eqs : list tensorequation) :
    typecontext -> tensorexpr -> tensorexpr -> Prop :=
  | teq_refl ctx te : teq eqs ctx te te

  | teq_comm ctx te te' : teq eqs ctx (te * te') (te' * te)
  | teq_assoc ctx te te' te'' : teq eqs ctx (te * (te' * te'')) (te * te' * te'')
  | teq_one_r ctx te : teq eqs ctx (te * 1) te

  | teq_prod_ext ctx tel tel' ter ter' :
    teq eqs ctx tel tel' -> teq eqs ctx ter ter' ->
    teq eqs ctx (tel * ter) (tel' * ter')
  | teq_tsum_ext ctx ty te te' : teq eqs (tc_cons_type ty ctx) te te' ->
    teq eqs ctx (tsum ty te) (tsum ty te')
  | teq_tsum_comm ctx ty ty' te : teq eqs ctx (tsum ty (tsum ty' te))
    (tsum ty' (tsum ty (relabel_te (relabel_rels pos_swap) te)))
  | teq_tsum_distr_l ctx ty tbody te :
    teq eqs ctx ((∑' ty, tbody) * te)
      (∑' ty, tbody * relabel_te (relabel_rels Pos.succ) te)

  | teq_hyp ctx tys lhs rhs (substs : Pmap var) : mk_teq lhs rhs tys ∈ eqs ->
    (forall l, l ∈ te_local_varset lhs ∪ te_local_varset rhs ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
      teq eqs ctx (te_substl (λ l, default (loc l) (substs !! l)) lhs)
        (te_substl (λ l, default (loc l) (substs !! l)) rhs)


  | teq_symm ctx te te' : teq eqs ctx te te' -> teq eqs ctx te' te
  | teq_trans ctx te te' te'' : teq eqs ctx te te' -> teq eqs ctx te' te'' ->
      teq eqs ctx te te''

  | teq_ill_typed ctx te te' : ~ well_typed ctx te -> ~ well_typed ctx te' ->
      teq eqs ctx te te'.


Add Parametric Relation eqs ctx : tensorexpr (teq eqs ctx)
  reflexivity proved by (teq_refl _ _)
  symmetry proved by (teq_symm _ _)
  transitivity proved by (teq_trans _ _)
  as teq_setoid.

Add Parametric Morphism eqs ctx : tproduct with signature
  teq eqs ctx ==> teq eqs ctx ==> teq eqs ctx as tproduct_mor.
Proof.
  auto using teq_prod_ext.
Qed.

Add Parametric Morphism eqs ctx ty : (tsum ty) with signature
  teq eqs (tc_cons_type ty ctx) ==> teq eqs ctx as tsum_mor.
Proof.
  auto using teq_tsum_ext.
Qed.

Create HintDb teq_db discriminated.

#[export] Hint Constructors teq : teq_db.
#[export] Hint Resolve tproduct_mor tsum_mor : teq_db.

Lemma teq_perm_indep_fwd eqs eqs' : eqs ≡ₚ eqs' -> forall ctx te te',
  teq eqs ctx te te' -> teq eqs' ctx te te'.
Proof.
  intros Hperm ctx te te' Heq.
  induction Heq; [now eauto with teq_db..| | | |];
    [|now eauto with teq_db..].
  eapply teq_hyp; eauto.
  now rewrite <- Hperm.
Qed.


Lemma teq_perm_indep eqs eqs' : eqs ≡ₚ eqs' -> forall ctx te te',
  teq eqs ctx te te' <-> teq eqs' ctx te te'.
Proof.
  split; eauto using teq_perm_indep_fwd, Permutation_sym.
Qed.

(* Add Parametric Morphism : teq *)

(* TODO: Improve printing here *)
Notation " ![ σ ; Γ ] ⊢ te = te' " :=
  (teq σ Γ te%te te'%te) (at level 100, te at level 69, te' at level 70).

Lemma teq_one_l eqs ctx te : ![ eqs; ctx ] ⊢ 1 * te = te.
Proof.
  rewrite teq_comm.
  apply teq_one_r.
Qed.

Lemma teq_tsum_distr_r eqs ctx ty tbody te :
    ![ eqs; ctx ] ⊢ (te * ∑' ty, tbody) =
      (∑' ty, relabel_te (relabel_rels Pos.succ) te * tbody).
Proof.
  rewrite teq_comm, teq_tsum_distr_l, teq_comm.
  reflexivity.
Qed.





Lemma teq_wt eqs ctx te te' :
  Forall (fun '(mk_teq lhs rhs tyl) =>
    well_typed (tc_eqn_with_locals ctx tyl) lhs /\
    well_typed (tc_eqn_with_locals ctx tyl) rhs) eqs ->
    ![ eqs; ctx] ⊢ te = te' -> well_typed ctx te <->
  well_typed ctx te'.
Proof.
  intros Heqs Heq.
  induction Heq; cbn.
  - easy.
  - easy.
  - easy.
  - easy.
  - naive_solver.
  - auto.
  - split; [apply relabel_te_swap_wt|].
    intros Heq%relabel_te_swap_wt.
    rewrite relabel_te_compose in Heq.
    erewrite relabel_te_ext, relabel_te_id in Heq; [|
      now intros [r| |]; [destruct r as [|[]|]|reflexivity..]].
    easy.
  - now rewrite <- relabel_te_cons_wt.
  - rewrite Forall_forall in Heqs.
    specialize (Heqs _ ltac:(eassumption)) as [Hlhs Hrhs].
    split; intros _; eapply te_substl_wt; set_solver.
  - symmetry; auto.
  - naive_solver.
  - naive_solver.
Qed.



(* 
Notation "'∑s'  tys ,  abs" :=
    (tensorexpr_of_tensorlist_aux tys abs)
    (at level 60, only printing) : tensorexpr_scope.

Lemma teq_relabel_rels_aux ctx eqs (neword : list Idx) tys tys' abs :
  neword ≡ₚ Pos.of_succ_nat <$> seq 0 (length tys') -> (* TODO: replace with length condition *)
  imap (λ i a, (Pos.of_succ_nat i, a)) tys ≡ₚ
    zip neword tys' ->
  ![ctx; eqs] ⊢ mk_tl tys abs =
    mk_tl tys'
      (relabel_abs (relabel_rels
        (λ r, default r (neword !! pos_to_nat_pred r))) <$> abs).
Proof.
  intros Hneword Htys.
  cbn.
  assert (Hlens : length tys' = length tys). 1:{
    apply Permutation_length in Hneword, Htys.
    rewrite length_fmap, length_seq in Hneword.
    rewrite length_imap, length_zip in Htys.
    lia.
  }
  rewrite Hlens in Hneword.
  revert Hneword.
  remember (Pos.of_succ_nat <$> seq 0 (length tys)) as oldord eqn:Holdord.
  intros Hneword.
  revert tys tys' Hlens Htys Holdord;
  induction Hneword;
  intros tys tys' Hlens Htys Holdord.
  - destruct tys; [|easy].
    destruct tys'; [|easy].
    cbn.
    apply eq_reflexivity.
    do 2 f_equal; symmetry.
    apply list_fmap_id'.
    intros ((fabs, low), up) _.
    apply relabel_abs_id'.
    intros []; [|reflexivity..].
    cbn.
    now rewrite lookup_nil.
  - destruct tys as [|ty tys]; [easy|].
    destruct tys' as [|ty' tys']; [easy|].
    cbn in Hlens.
    apply (inj S) in Hlens.
    cbn in Holdord.
    revert Holdord.
    intros [= -> Hl'].

    destruct tys'; [|easy].


Lemma teq_hyp' eqs ctx tys lhs rhs (substs : Pmap var) :
  mk_teq lhs rhs tys ∈ eqs ->
  (forall l, l ∈ te_local_varset lhs ∪ te_local_varset rhs ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
      teq eqs ctx (te_substl (λ l, default (loc l) (substs !! l)) lhs)
        (te_substl (λ l, default (loc l) (substs !! l)) rhs).

map_is_subtyped_iff_restriction_is_typed

Definition teqeq eqs ctx (teeq : tensorequation) : Prop :=
  teq eqs *)

