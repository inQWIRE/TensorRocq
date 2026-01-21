(* Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp.

Require Import TensorExprDBSyntax.

(* Axiomatized rules for tensor expressions, which we will show are 
  tensor-preserving *)

Notation vartypecontext := (Pmap Ty).
Notation abstypecontext := (gmap Idx (list Ty)).

Record typecontext := mk_tc {
  tc_ma : abstypecontext;
  tc_mg : vartypecontext;
  tc_ml : vartypecontext;
  tc_mr : list Ty;
}.

Definition tc_cons_type (ty : Ty) (tc : typecontext) : typecontext :=
  mk_tc (tc.(tc_ma)) (tc.(tc_mg)) (tc.(tc_ml)) (ty :: tc.(tc_mr)).

Definition tc_get_var (tc : typecontext) (v : var) : option Ty :=
  get_var (tc.(tc_mg)) (tc.(tc_ml)) (tc.(tc_mr)) v.

Declare Scope tensorexpr_scope.
Delimit Scope tensorexpr_scope with te.
Bind Scope tensorexpr_scope with tensorexpr.

Declare Custom Entry args_print.

Declare Custom Entry var_print.

Notation " '#' r " := (rel r) (in custom var_print at level 1).
Notation " 'L@' l " := (loc l) (in custom var_print at level 1).
Notation " 'G@' g " := (glob g) (in custom var_print at level 1).

Notation " '()' " := (@nil var) (in custom args_print at level 0).
Notation " '(' x ,  .. ,  y ')'" := 
  (cons x .. (cons y nil) ..)
  (in custom args_print at level 0, x custom var_print at level 1, 
    y custom var_print at level 1).


Notation "te  *  te'" := (tproduct te%te te'%te) : tensorexpr_scope.
Notation "1" := (tone) (at level 1) : tensorexpr_scope.
Notation "∑'  ty ,  te" := (tsum ty%nat te%te) 
  (at level 45, right associativity) : tensorexpr_scope.
Notation "'!{' f '}'  low  up" :=
  (tabstract f low up) (at level 10, 
    low custom args_print at level 0, 
    up custom args_print at level 0) : tensorexpr_scope.

Fixpoint well_typed (tc : typecontext) (te : tensorexpr) : Prop :=
  match te with 
  | tone => True
  | tabstract f low up =>
    (fmap Some) <$> tc.(tc_ma) !! f = Some ((tc_get_var tc) <$> (low ++ up))
  | tproduct te te' => 
    well_typed tc te /\ well_typed tc te'
  | tsum ty te => well_typed (tc_cons_type ty tc) te
  end.

Fixpoint is_well_typed (ta : abstypecontext) 
  (tg tl : vartypecontext) (tr : list Ty) (te : tensorexpr) : bool :=
  match te with 
  | tone => true
  | tabstract f low up =>
    bool_decide ((fmap Some) <$> ta !! f = Some ((get_var tg tl tr) <$> (low ++ up)))
  | tproduct te te' => is_well_typed ta tg tl tr te && is_well_typed ta tg tl tr te'
  | tsum ty te => is_well_typed ta tg tl (ty :: tr) te
  end.

Lemma is_well_typed_correct tc te : 
  is_well_typed (tc.(tc_ma)) (tc.(tc_mg)) (tc.(tc_ml)) (tc.(tc_mr)) te <-> 
  well_typed tc te.
Proof.
  destruct tc as [ta tg tl tr]; cbn.
  revert tr; induction te; intros tr; cbn.
  - easy.
  - apply bool_decide_spec.
  - now rewrite andb_True, IHte1, IHte2.
  - apply IHte.
Qed.

Lemma is_well_typed_correct_alt tc te : 
  if (is_well_typed (tc.(tc_ma)) (tc.(tc_mg)) (tc.(tc_ml)) (tc.(tc_mr)) te)
  then well_typed tc te else ¬ well_typed tc te.
Proof.
  specialize (is_well_typed_correct tc te).
  destruct (is_well_typed _ _ _ _ _); cbn; naive_solver.
Qed.

#[global] Instance well_typed_dec tc te : Decision (well_typed tc te) :=
  match is_well_typed (tc.(tc_ma)) (tc.(tc_mg)) (tc.(tc_ml)) (tc.(tc_mr)) te
    as b return ((if b return Prop then _ else _) -> _) with
  | true => left
  | false => right
  end (is_well_typed_correct_alt tc te).



Inductive teq (eqs : list tensorequation) : 
    typecontext -> Pmap Ty -> tensorexpr -> tensorexpr -> Prop :=
  | teq_refl ctx tyl te : teq eqs ctx tyl te te

  | teq_comm ctx tyl te te' : teq eqs ctx tyl (te * te') (te' * te)
  | teq_assoc ctx te te' te'' : teq eqs ctx (te * (te' * te'')) (te * te' * te'')
  | teq_one_r ctx te : teq eqs ctx (te * 1) te
  
  | teq_prod_ext ctx tel tel' ter ter' : 
    teq eqs ctx tel tel' -> teq eqs ctx ter ter' -> 
    teq eqs ctx (tel * ter) (tel' * ter')
  | teq_tsum_ext ctx ty te te' : teq eqs (tc_cons_type ty ctx) te te' -> 
    teq eqs ctx (tsum ty te) (tsum ty te')
  | teq_tsum_comm ctx ty ty' te : teq eqs ctx (tsum ty (tsum ty' te))
    (tsum ty' (tsum ty (relabel_te (relabel_rels 
      (fun p => match p with | 1 => 2 | 2 => 1 | _ => p end%positive)) te)))
  | teq_tsum_distr_l ctx ty tbody te : 
    teq eqs ctx ((∑' ty, tbody) * te) 
      (∑' ty, tbody * relabel_te (relabel_rels Pos.succ) te)
  
  | teq_hyp ctx tys lhs rhs (substs : Pmap var) : mk_teq lhs rhs tys ∈ eqs ->
    map_is_typed (tc_get_var ctx) (Some <$> tys) substs ->
      teq eqs ctx (te_substl (λ l, default (loc l) (substs !! l)) lhs) 
        (te_substl (λ l, default (loc l) (substs !! l)) rhs)
  
  
  | teq_symm ctx te te' : teq eqs ctx te te' -> teq eqs ctx te' te
  | teq_trans ctx te te' te'' : teq eqs ctx te te' -> teq eqs ctx te' te'' -> 
      teq eqs ctx te te''
  
  | teq_ill_typed ctx te te' : ~ well_typed ctx te -> ~ well_typed ctx te -> 
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
Notation " σ ; Γ ⊢ te = te' " :=
  (teq σ Γ te%te te'%te) (at level 100, te at level 69, te' at level 70).

Lemma teq_one_l eqs ctx te : eqs; ctx ⊢ 1 * te = te.
Proof.
  rewrite teq_comm.
  apply teq_one_r.
Qed.

Lemma teq_tsum_distr_r eqs ctx ty tbody te : 
    eqs; ctx ⊢ (te * ∑' ty, tbody) =
      (∑' ty, relabel_te (relabel_rels Pos.succ) te * tbody).
Proof.
  rewrite teq_comm, teq_tsum_distr_l, teq_comm.
  reflexivity.
Qed.


Definition tleq 
 *)
