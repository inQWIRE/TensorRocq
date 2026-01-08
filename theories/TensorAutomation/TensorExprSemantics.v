Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

Require Import Aux_stdpp.

Require Import TensorExprSyntax.


Section TensorExprSemantics.


Import Relation_Definitions.

Import Setoid.

Context `{SR : SemiRing R rO rI radd rmul req}.

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


Context (V : Ty -> Type).
Context `{Vsum : forall n, Summable (V n)}.

Existing Instance Vsum.

Fixpoint V_n_args (args : list Ty) (A : Type) : Type :=
  match args with 
  | [] => A
  | n :: args => V n -> V_n_args args A
  end.

(* A bundled function with its argument types *)
Definition Vfunc := {args : list Ty & V_n_args args R}.

Definition Vval := {n : Ty & V n}.

Definition Vval_get (n : Ty) (v : Vval) : option (V n) :=
  match v with 
  | existT n' val => 
    match decide (n = n') with 
    | left H => Some (eq_rect_r V val H)
    | right _ => None
    end
  end.

Definition Vconst (f : Vfunc) : option R :=
  match f with 
  | existT [] c => Some c
  | existT _ _ => None
  end.

Definition Vapply (f : Vfunc) (v : Vval) : option Vfunc :=
  match f with 
  | existT (n :: args) f => 
      (fun v => existT (P:=fun a => V_n_args a R) args (f v)) <$> (Vval_get n v)
  | existT [] _ => None
  end.

Fixpoint Vapplys (f : Vfunc) (vs : list Vval) : option R :=
  match vs with 
  | [] => Vconst f
  | v :: vs => 
      f ← Vapply f v;
      Vapplys f vs
  end.




Definition varcontext := gmap Idx Vval.

Definition vartypecontext := gmap Idx Ty.

Definition vartype_of_var_context (vars : varcontext) : vartypecontext :=
  projT1 <$> vars.

Definition abscontext := gmap string Vfunc.

Definition abstypecontext := gmap string (list Ty).

Definition abstype_of_abs_context (abs : abscontext) : abstypecontext :=
  projT1 <$> abs.

Coercion vartype_of_var_context : varcontext >-> vartypecontext.
Coercion abstype_of_abs_context : abscontext >-> abstypecontext.


Definition mk_Vval {n} (v : V n) : Vval := existT n v.

Definition mk_Vfunc args (f : V_n_args args R) : Vfunc := existT args f.

(* TODO: Extract (and remove?) *)
Fixpoint well_typed (abs : abstypecontext) (types : vartypecontext) 
  (te : tensorexpr) : bool :=
  match te with 
  | tone => true
  | tabstract absidx lower upper =>
    match abs !! absidx with 
    | None => false
    | Some args => bool_decide (Some <$> args = ((types !!.) <$> (lower ++ upper)))
    end
  | tproduct l r => well_typed abs types l && well_typed abs types r
  | tsum var ty summand => 
    well_typed abs (<[var := ty]> types) summand
  end.


Fixpoint semantics (abs : abscontext) (vars : varcontext) 
  (te : tensorexpr) : option R :=
  match te with 
  | tone => Some rI
  | tabstract absidx lower upper =>
      args ← join_list ((vars !!.) <$> (lower ++ upper));
      fval ← abs !! absidx;
      Vapplys fval args
  | tproduct l r => 
      lval ← semantics abs vars l;
      rval ← semantics abs vars r;
      Some (rmul lval rval)
  | tsum v n summand =>
      Some (sum_of (fun x : V n => 
        default rO (semantics abs (<[v := mk_Vval x]> vars) summand)))
  end.

Definition abstract_semantics (abs : abscontext) (vars : varcontext)
  (absidx : Idx) (lower : list Idx) (upper : list Idx) : R :=
  default rO (args ← join_list ((vars !!.) <$> (lower ++ upper));
      fval ← abs !! absidx;
      Vapplys fval args).


Lemma abstract_semantics_ext abs vars abs' vars' 
  idx lower upper idx' lower' upper' :
  abs !! idx = abs' !! idx' -> 
  (vars !!.) <$> (lower ++ upper) = (vars' !!.) <$> (lower' ++ upper') ->
  abstract_semantics abs vars idx lower upper = 
  abstract_semantics abs' vars' idx' lower' upper'.
Proof.
  intros Hidx Hargs.
  unfold abstract_semantics.
  now rewrite Hidx, Hargs.
Qed.

Fixpoint total_semantics (abs : abscontext) (vars : varcontext) (te : tensorexpr) : R :=
  match te with 
  | tone => rI
  | tabstract absidx lower upper =>
      abstract_semantics abs vars absidx lower upper
  | tproduct l r => 
      rmul (total_semantics abs vars l) (total_semantics abs vars r)
  | tsum v n summand => 
      sum_of (fun x : V n => 
        total_semantics abs (<[v := mk_Vval x]> vars) summand)
  end.


Definition tl_total_semantics abs vars (tl : tensorlist) : R :=
  total_semantics abs vars (tensorexpr_of_tensorlist tl).

Definition teq : relation tensorexpr :=
  fun te1 te2 => forall abs vars, 
  total_semantics abs vars te1 == total_semantics abs vars te2.


Lemma Vconst_is_Some (f : Vfunc) : is_Some (Vconst f) <-> projT1 f = [].
Proof.
  unfold Vconst.
  destruct f as [args f].
  cbn.
  destruct args; split; easy || now intros ?%is_Some_None.
Qed.

Lemma Vval_get_is_Some n (v : Vval) : is_Some (Vval_get n v) <-> 
  projT1 v = n.
Proof.
  unfold Vval_get.
  destruct v as [n' v].
  cbn.
  case_decide; try subst; try easy;
  split; [now intros ?%is_Some_None|congruence].
Qed.

Arguments Vval_get : simpl never.

Lemma Vapply_is_Some f v : is_Some (Vapply f v) <->
  head (projT1 f) = Some (projT1 v).
Proof.
  unfold Vapply.
  destruct f as [args f], v as [n v].
  cbn.
  destruct args; [split; cbn; easy || now intros ?%is_Some_None|].
  rewrite fmap_is_Some, Vval_get_is_Some.
  cbn.
  firstorder congruence.
Qed.

Lemma Vapplys_is_Some f vs : is_Some (Vapplys f vs) <-> 
  projT1 f = projT1 <$> vs.
Proof.
  destruct f as [args f].
  cbn.
  revert f vs; induction args as [|arg args IHargs]; intros f vs.
  - destruct vs; split; now try intros ?%is_Some_None.
  - destruct vs; [split; now try intros ?%is_Some_None|].
    cbn.
    rewrite option_fmap_bind.
    unfold compose.
    rewrite bind_is_Some, Vval_get_is_Some.
    setoid_rewrite IHargs.
    split.
    + intros [Hproj Hargs].
      rewrite <- Hproj.
      apply Vval_get_is_Some in Hproj.
      destruct Hproj as [? ?].
      f_equal; eauto.
    + now intros [= Harg Hargs].
Qed.

Lemma wt_abstract_is_Some (vars : varcontext) (abs : abscontext) absidx lower upper :
  well_typed abs vars (tabstract absidx lower upper) = true ->
  is_Some (semantics abs vars (tabstract absidx lower upper)).
Proof.
  cbn.
  unfold abstype_of_abs_context, vartype_of_var_context.
  setoid_rewrite lookup_fmap.
  fold Vval Vfunc abscontext varcontext.
  destruct (abs !! absidx) as [f|] eqn:Hfeq; [|easy].
  cbn.
  rewrite bool_decide_eq_true.
  generalize (lower ++ upper) as args.
  clear lower upper.
  intros args.
  intros Hfargs.
  rewrite bind_is_Some.
  split.
  - rewrite join_list_is_Some.
    rewrite elem_of_list_fmap.
    intros (var & Hvar%eq_sym & Hvar_args).
    apply elem_of_list_lookup_1 in Hvar_args as Hvar'.
    destruct Hvar' as [i Hi].
    apply (f_equal (.!! i)) in Hfargs as Hfi.
    revert Hfi.
    rewrite 2 list_lookup_fmap, Hi.
    cbn.
    setoid_rewrite lookup_fmap.
    setoid_rewrite Hvar.
    cbn.
    destruct (projT1 f !! i) as [fi|] eqn:Hfi; [easy|].
    assert (Hi' : is_Some (args !! i)) by now rewrite Hi.
    assert (Hfi' : ~ is_Some (projT1 f !! i)) by now rewrite Hfi; intros ?%is_Some_None.
    rewrite lookup_lt_is_Some in Hi'.
    setoid_rewrite lookup_lt_is_Some in Hfi'.
    specialize (f_equal length Hfargs).
    simpl_list.
    lia.
  - intros argvs.
    rewrite join_list_Some.
    intros Hargvs.
    rewrite Vapplys_is_Some.
    eapply list_eq_same_length; [|reflexivity|].
    1: {
      specialize (f_equal length Hfargs).
      specialize (f_equal length Hargvs).
      simpl_list.
      now intros ->.
    }
    intros i fi argin Hi Hfi.
    rewrite list_lookup_fmap.
    rewrite fmap_Some.
    intros (argvi & Hargvi & ->).
    apply (f_equal (.!! i)) in Hargvs as Hargi.
    rewrite 2 list_lookup_fmap in Hargi.
    setoid_rewrite Hargvi in Hargi.
    cbn in Hargi.
    apply fmap_Some in Hargi as (argi & Hargi & Hvars_argi).
    apply (f_equal (.!! i)) in Hfargs as Hfi'.
    rewrite 2 list_lookup_fmap in Hfi'.
    rewrite Hfi in Hfi'.
    rewrite Hargi in Hfi'.
    cbn in Hfi'.
    apply (inj Some) in Hfi'.
    setoid_rewrite lookup_fmap in Hfi'.
    setoid_rewrite <- Hvars_argi in Hfi'.
    cbn in Hfi'.
    congruence.
Qed.

Lemma wt_semantics_is_Some (vars : varcontext) (abs : abscontext) te : 
  well_typed abs vars te = true ->
  is_Some (semantics abs vars te).
Proof.
  revert vars; induction te; intros vars.
  - easy.
  - apply wt_abstract_is_Some.
  - cbn.
    rewrite andb_true_iff.
    intros [Hl%IHte1 Hr%IHte2].
    destruct Hl as [? ->].
    destruct Hr as [? ->].
    easy.
  - now destruct reg.
Qed.


Lemma total_semantics_spec abs vars te : 
  total_semantics abs vars te == default rO (semantics abs vars te).
Proof.
  revert vars; induction te; intros vars; [reflexivity|reflexivity|cbn..].
  - rewrite IHte1, IHte2.
    destruct (semantics abs vars te1) as [tv1|],
      (semantics abs vars te2) as [tv2|]; cbn; ring. 
  - apply sum_of_ext.
    intros x.
    apply IHte.
Qed.

Lemma teq_refl : Reflexive teq.
Proof. easy. Qed.

Lemma teq_symm : Symmetric teq.
Proof. easy. Qed.

Lemma teq_trans : Transitive teq.
Proof. 
  unfold teq. 
  pose proof (Req_equivalence.(Equivalence_Transitive)) as ?. 
  eauto.
Qed.

#[global]
Add Parametric Relation : tensorexpr teq
  reflexivity proved by teq_refl
  symmetry proved by teq_symm
  transitivity proved by teq_trans
  as teq_setoid.

Infix "=t=" := teq (at level 70).


Add Parametric Morphism : tproduct with signature
  teq ==> teq ==> teq as tproduct_mor.
Proof.
  intros l l' Hl r r' Hr abs vars.
  cbn.
  f_equiv; [apply Hl|apply Hr].
Qed.

Add Parametric Morphism var ty : (tsum var ty) with signature
  teq ==> teq as tsum_mor.
Proof.
  intros smd smd' Hsmd abs vars.
  cbn.
  f_equiv; intros x.
  apply Hsmd.
Qed.

Lemma tproduct_tone_l te : teq (tproduct tone te) te.
Proof.
  intros abs vars; cbn; ring.
Qed.

Lemma tproduct_tone_r te : teq (tproduct te tone) te.
Proof.
  intros abs vars; cbn; ring.
Qed.

Lemma tproduct_assoc te1 te2 te3 : 
  teq (tproduct te1 (tproduct te2 te3))
  (tproduct (tproduct te1 te2) te3).
Proof.
  intros abs vars; cbn; ring.
Qed.

Lemma tproduct_comm te1 te2 : 
  teq (tproduct te1 te2)
    (tproduct te2 te1).
Proof.
  intros abs vars; cbn; ring.
Qed.


Add Parametric Morphism : tproducts with signature
  Permutation ==> teq as tproducts_perm_mor.
Proof.
  intros tes tes' Hperm.
  induction Hperm; [reflexivity|..|etransitivity; eauto].
  - cbn; now f_equiv.
  - cbn.
    rewrite 2 tproduct_assoc.
    f_equiv.
    apply tproduct_comm.
Qed.


Add Parametric Relation : tensorlist tensorlist_perm_eq 
  reflexivity proved by ltac:(split; reflexivity)
  symmetry proved by ltac:(unfold tensorlist_perm_eq; split; now symmetry)
  transitivity proved by ltac:(unfold tensorlist_perm_eq; intros ???[][];
     split; etransitivity; eauto)
  as tensorlist_perm_eq_setoid.

Add Parametric Morphism : abstracts_vars with signature
  Permutation ==> eq as abstracts_vars_perm_mor.
Proof.
  unfold abstracts_vars.
  now intros ? ? ->.
Qed.

Add Parametric Morphism : tl_free_varset with signature
  tensorlist_perm_eq ==> eq as tl_free_varset_perm_mor.
Proof.
  intros tl tl' [Hsums Habs].
  unfold tl_free_varset.
  now rewrite Hsums, Habs.
Qed.

Add Parametric Morphism : tl_bound_varset with signature
  tensorlist_perm_eq ==> eq as tl_bound_varset_perm_mor.
Proof.
  intros tl tl' [Hsums Habs].
  unfold tl_bound_varset.
  now rewrite Hsums.
Qed.

Add Parametric Morphism : tl_varset with signature
  tensorlist_perm_eq ==> eq as tl_varset_perm_mor.
Proof.
  intros tl tl' [Hsums Habs].
  unfold tl_varset.
  now rewrite Hsums, Habs.
Qed.



Lemma total_semantics_absset_indep abs abs' vars
  te :
  (forall a, a ∈ te_absset te -> abs !! a = abs' !! a) ->
  total_semantics abs vars te == total_semantics abs' vars te.
Proof.
  revert vars; induction te; cbn; intros var Habs.
  - easy.
  - unfold abstract_semantics; now rewrite Habs by now clear; set_solver.
  - f_equiv; [apply IHte1 | apply IHte2]; intros ? Hmem; apply Habs;
    clear -Hmem; set_solver.
  - apply sum_of_ext; intros x.
    apply IHte.
    easy.
Qed.

Lemma total_semantics_free_varset_indep abs vars vars' te :
  (forall v, v ∈ te_free_varset te -> vars !! v = vars' !! v) -> 
  total_semantics abs vars te == total_semantics abs vars' te.
Proof.
  revert vars vars'; induction te; intros vars vars' Hvar.
  - reflexivity.
  - cbn in *.
    (* setoid_rewrite elem_of_singleton in Habs. *)
    setoid_rewrite elem_of_list_to_set in Hvar.
    unfold abstract_semantics.
    f_equiv.
    do 2 f_equal.
    apply map_ext_in.
    intros a Ha%elem_of_list_In%Hvar.
    now destruct a.
  - cbn in *.
    f_equiv;
    [apply IHte1 | apply IHte2]; 
    intros; apply Hvar;
    [now apply elem_of_union_l | now apply elem_of_union_r].
  - cbn in *.
    apply sum_of_ext.
    intros x.
    apply IHte.
    intros v Hv.
    destruct_decide (decide (v = reg)) as Htveq.
    + subst.
      cbn.
      now simpl_map.
    + specialize (Hvar v ltac:(set_solver)).
      cbn.
      setoid_rewrite lookup_insert_ne; [|easy..].
      easy.
Qed.

Lemma te_relabel_semantics abs vars vars' f te : 
  (forall v, v ∈ te_varset te -> vars !! v = vars' !! (f v)) -> 
  (forall v v', v ∈ te_varset te -> v' ∈ te_varset te ->
    f v = f v' -> v = v') ->
  (* (forall tv, tv ∈ te_varset te -> (f tv).1 = tv.1) ->  *)
  total_semantics abs vars' (relabel_te f te) ==
  total_semantics abs vars te.
Proof. 
  revert vars vars'; induction te; intros vars vars' Hvar Hfinj.
  - reflexivity.
  - cbn in *.
    (* setoid_rewrite elem_of_singleton in Habs. *)
    setoid_rewrite elem_of_list_to_set in Hvar.
    unfold abstract_semantics.
    f_equiv.
    do 2 f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext.
    intros i a Ha%elem_of_list_lookup_2%Hvar.
    cbn; now rewrite Ha.
  - cbn in *.
    f_equiv;
    (apply IHte1 || apply IHte2);
    intros; (apply Hvar || apply Hfinj);
    now (assumption + apply elem_of_union_l + apply elem_of_union_r).
  - cbn in *.
    apply sum_of_ext.
    intros x.
    apply IHte; [|intros ? ? Hm1 Hm2; apply Hfinj; clear -Hm1 Hm2; set_solver].
    intros v Hv.
    destruct_decide (decide (reg = v)) as Hvreg.
    + subst.
      now setoid_rewrite lookup_insert.
    + setoid_rewrite lookup_insert_ne; [apply Hvar; clear -Hv; set_solver|easy|].
      intros Hfeq; apply Hvreg.
      revert Hfeq.
      apply Hfinj; clear -Hv; set_solver.
Qed.


Lemma te_relabel_bound_aux_semantics abs vars vars' f te bound :
  (forall v, v ∈ bound -> vars !! v = vars' !! (f v)) -> 
  (forall v, v ∈ te_varset te ∖ bound -> vars !! v = vars' !! v) -> 
  (forall v v', v ∈ bound ∪ te_bound_varset te -> v' ∈ bound ∪ te_bound_varset te ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ te_bound_varset te -> f v ∉ te_varset te ∖ ({[v]} ∪ bound)) ->
  (* (forall tv, tv ∈ te_varset te ∖  -> (f tv).1 = tv.1) ->  *)
  total_semantics abs vars' (relabel_bound_aux f bound te) ==
  total_semantics abs vars te.
Proof.
  revert bound vars vars'; induction te; intros bound vars vars' 
    Hbound Hfree Hfinj Hffree.
  - reflexivity.
  - cbn in *.
    unfold abstract_semantics.
    f_equiv.
    do 2 f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext.
    intros i a Ha%elem_of_list_lookup_2. 
    cbn. 
    unfold relabel_bound_Idx.
    case_decide as Habound; [symmetry; now apply Hbound|].
    specialize (Hfree a). 
    rewrite elem_of_difference, elem_of_list_to_set in Hfree.
    now specialize (Hfree ltac:(auto)).
  - cbn in *.
    f_equiv;
    (apply IHte1 || apply IHte2);
    intros; try (apply Hbound || apply Hfree || apply Hfinj); 
    try first [assumption | now apply elem_of_union_l | now apply elem_of_union_r];
    clear Hbound Hfree Hfinj IHte1 IHte2; set_solver.
  - cbn in *.
    apply sum_of_ext.
    intros x.
    apply IHte.
    + intros v Hv.
      destruct_decide (decide (reg = v)) as Hvreg; 
      [subst; now setoid_rewrite lookup_insert|].
      rewrite elem_of_union, elem_of_singleton in Hv.
      assert (Hvbound : v ∈ bound) by naive_solver.
      setoid_rewrite lookup_insert_ne; [apply Hbound; clear -Hvbound; set_solver|easy|].
      intros Hfeq; apply Hvreg.
      revert Hfeq.
      apply Hfinj; clear -Hvbound; set_solver.
    + intros v [Hv [Hvnreg%not_elem_of_singleton Hvnbound]%not_elem_of_union]%elem_of_difference.
      setoid_rewrite lookup_insert_ne; [|easy|].
      * apply Hfree; clear -Hv Hvnbound; set_solver.
      * intros <-.
        specialize (Hffree reg).
        specialize (Hffree ltac:(set_solver)).
        set_solver.
    + set_solver.
    + set_solver.
Qed.

Lemma te_relabel_bound_semantics abs vars f te : 
  (forall v v', v ∈ te_bound_varset te -> v' ∈ te_bound_varset te ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ te_bound_varset te -> f v ∉ te_varset te ∖ {[v]}) ->
  total_semantics abs vars (relabel_bound f te) ==
  total_semantics abs vars te.
Proof.
  intros Hfinj Hffree.
  apply te_relabel_bound_aux_semantics.
  - set_solver.
  - easy.
  - set_solver.
  - set_solver.
Qed.

Lemma relabel_bound_correct f te : 
  (forall v v', v ∈ te_bound_varset te -> v' ∈ te_bound_varset te ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ te_bound_varset te -> f v ∉ te_varset te ∖ {[v]}) ->
  teq (relabel_bound f te) te.
Proof.
  intros Hinj Hfree abs vars.
  now apply te_relabel_bound_semantics.
Qed.



Lemma te_base_alpha_equiv_one vold vnew te :
  vnew ∉ te_varset te ∖ {[vold]} ->
  teq (relabel_bound (fun x => if decide (x = vold) then vnew else x) te)
  te.
Proof.
  intros Hvnew.
  pose proof (te_bound_varset_subseteq te) as Hsub.
  apply relabel_bound_correct; intros; repeat case_decide; subst; 
    congruence || set_solver.
Qed.


Lemma tsum_distr_l_free_in var ty smd te : 
  var ∉ te_free_varset te ->
  teq (tproduct (tsum var ty smd) te)
    (tsum var ty (tproduct smd te)).
Proof.
  intros Hvar abs vars.
  cbn.
  rewrite sum_of_distr_l.
  apply sum_of_ext; intros x.
  f_equiv.
  apply total_semantics_free_varset_indep.
  intros v Hv.
  now setoid_rewrite lookup_insert_ne; [|congruence].
Qed.

Lemma tsum_distr_r_free_in var ty smd te : 
  var ∉ te_free_varset te ->
  teq (tproduct te (tsum var ty smd))
    (tsum var ty (tproduct te smd)).
Proof.
  intros Hvar.
  rewrite tproduct_comm, (tproduct_comm te smd).
  now apply tsum_distr_l_free_in.
Qed.






Lemma tl_total_semantics_sumless_abs_app abs vars labs rabs : 
  tl_total_semantics abs vars (mk_tl [] (labs ++ rabs)) == 
  tl_total_semantics abs vars (mk_tl [] labs) * tl_total_semantics abs vars (mk_tl [] rabs).
Proof.
  cbn.
  induction labs as [|[[idx lower] upper] labs IHlabs]; [cbn; ring|].
  cbn.
  rewrite IHlabs.
  ring.
Qed.


Lemma mk_tl_sumless_app_r labs rabs : mk_tl [] (labs ++ rabs) =t= 
  tproduct (mk_tl [] labs) (mk_tl [] rabs).
Proof.
  intros ? ?; apply tl_total_semantics_sumless_abs_app.
Qed.

Lemma tl_cons_sum_teq ty var tl : 
  tl_cons_sum ty var tl =t= tsum var ty tl.
Proof.
  reflexivity.
Qed.

(* Definition  *)

Lemma tsum_var_change var var' ty te :
  var' ∉ te_varset te ∖ {[var]} ->
  (* te_relabel_bound_semantics *)
  tsum var ty te =t= tsum var' ty 
  (relabel_te (relabel_var var var') te).
Proof.
  intros Hvar'.
  rewrite <- (te_base_alpha_equiv_one var var') by (cbn; set_solver).
  cbn.
  rewrite union_empty_r_L.
  rewrite decide_True by easy.
  intros abs vars.
  cbn.
  apply sum_of_ext; intros x.
  transitivity (total_semantics abs (<[var:=mk_Vval x]> vars) te); [|symmetry].
  - apply te_relabel_bound_aux_semantics.
    + intros ? ->%elem_of_singleton.
      rewrite decide_True by easy.
      now setoid_rewrite lookup_insert.
    + intros v [Hv Hvnvar%not_elem_of_singleton]%elem_of_difference.
      setoid_rewrite lookup_insert_ne; try easy.
      intros <-.
      set_solver.
    + intros v v' Hv Hv'.
      pose proof (te_bound_varset_subseteq te).
      case_decide as Hvvar; case_decide as Hvvar'; set_solver.
    + intros v Hv.
      case_decide as Hvvar; set_solver.
  - apply te_relabel_semantics.
    + intros v Hv.
      unfold relabel_var.
      case_decide as Hvvar.
      * subst. now setoid_rewrite lookup_insert.
      * setoid_rewrite lookup_insert_ne; try easy.
        set_solver.
    + intros v v' Hv Hv'.
      unfold relabel_var. 
      case_decide as Hvvar; case_decide as Hvvar'; set_solver.
Qed.


Lemma elem_of_te_varset_relabel f te var : 
  var ∈ te_varset (relabel_te f te) ↔
  exists var', var' ∈ te_varset te /\ f var' = var.
Proof.
  induction te.
  - cbn.
    set_solver.
  - cbn.
    set_solver.
  - cbn.
    rewrite elem_of_union.
    rewrite IHte1, IHte2.
    clear IHte1 IHte2.
    set_solver.
  - cbn.
    rewrite elem_of_union.
    rewrite IHte.
    clear IHte.
    set_solver.
Qed.


Lemma tl_times_aux_base_r_correct avoid labs rsums rabs len_rsums prf : 
  abstracts_vars labs ⊆ avoid ->
  tl_varset (mk_tl rsums rabs) ⊆ avoid -> 
  tl_times_aux_base_r avoid labs rsums rabs len_rsums prf =t=
  tproduct (mk_tl [] labs) (mk_tl rsums rabs).
Proof.
  cbn.
  revert avoid labs rabs rsums prf;
  induction len_rsums as [|len_rsums IHrsums];
  intros avoid labs rabs rsums prf.
  - destruct rsums as [|]; [|easy].
    intros _ _. 
    cbn in prf. 
    cbn [ tl_times_aux_base_r ].
    now rewrite mk_tl_sumless_app_r.
  - destruct rsums as [|[ty var] rsums]; [easy|].
    intros Hav_l Hav_r.
    cbn in prf.
    cbn [ tl_times_aux_base_r tensorexpr_of_tensorlist_aux ].
    rewrite tl_cons_sum_teq.
    rewrite (tsum_var_change var (fresh_var var avoid)).
    2:{
      rewrite fold_tensorexpr_of_tensorlist_aux.
      rewrite <- tl_varset_correct.
      apply (not_elem_of_weaken _ _ _ (fresh_var_fresh var avoid)).
      clear -Hav_r.
      cbn in *; set_solver.
    }
    rewrite tsum_distr_r_free_in.
    2:{
      rewrite <- abstract_vars_correct.
      revert Hav_l.
      apply not_elem_of_weaken, fresh_var_fresh.
    }
    rewrite IHrsums.
    2: {
      rewrite Hav_l.
      apply union_subseteq_l.
    }
    2: {
      rewrite tl_varset_correct.
      rewrite relabel_one_in_correct.
      rewrite tl_varset_correct in Hav_r.
      cbn in *.
      intros x.
      rewrite elem_of_te_varset_relabel.
      intros (v & Hv & <-).
      unfold relabel_var.
      case_decide; subst; [|set_solver +Hav_r Hv].
      destruct_decide (decide (fresh_var var avoid = var)) as Hfr; 
      set_solver +Hav_r Hv Hfr.
    }
    rewrite fold_tensorexpr_of_tensorlist_aux.
    now rewrite relabel_one_in_correct.
Qed.


Lemma tl_times_aux_l_correct avoid lsums labs rsums rabs len_lsums prf : 
  tl_varset (mk_tl lsums labs) ⊆ avoid ->
  tl_varset (mk_tl rsums rabs) ⊆ avoid -> 
  tl_times_aux_l avoid lsums labs rsums rabs len_lsums prf =t=
  tproduct (mk_tl lsums labs) (mk_tl rsums rabs).
Proof.
  cbn.
  revert avoid lsums labs rabs rsums prf;
  induction len_lsums as [|len_lsums IHlsums];
  intros avoid lsums labs rabs rsums prf.
  - destruct lsums as [|]; [|easy].
    intros Hl Hr.
    apply tl_times_aux_base_r_correct; [|easy].
    unfold tl_varset in Hl. 
    cbn -[abstracts_vars] in Hl.
    now rewrite union_empty_r_L in Hl.
  - destruct lsums as [|[ty var] lsums]; [easy|].
    intros Hav_l Hav_r.
    cbn in prf.
    cbn [ tl_times_aux_l tensorexpr_of_tensorlist_aux ].
    rewrite tl_cons_sum_teq.
    rewrite (tsum_var_change var (fresh_var var avoid)).
    2:{
      rewrite fold_tensorexpr_of_tensorlist_aux.
      rewrite <- tl_varset_correct.
      apply (not_elem_of_weaken _ _ _ (fresh_var_fresh var avoid)).
      clear -Hav_l.
      cbn in *; set_solver.
    }
    rewrite tsum_distr_l_free_in.
    2:{
      rewrite tl_varset_correct in Hav_r.
      specialize (te_free_varset_subseteq (mk_tl rsums rabs)).
      apply not_elem_of_weaken.
      revert Hav_r.
      apply not_elem_of_weaken, fresh_var_fresh.
    }
    rewrite IHlsums.
    2: {
      rewrite tl_varset_correct.
      rewrite relabel_one_in_correct.
      rewrite tl_varset_correct in Hav_l.
      cbn in *.
      intros x.
      rewrite elem_of_te_varset_relabel.
      intros (v & Hv & <-).
      unfold relabel_var.
      case_decide; subst; [|set_solver +Hav_l Hv].
      destruct_decide (decide (fresh_var var avoid = var)) as Hfr; 
      set_solver +Hav_l Hv Hfr.
    }
    2: {
      rewrite Hav_r.
      apply union_subseteq_l.
    }
    rewrite fold_tensorexpr_of_tensorlist_aux.
    now rewrite relabel_one_in_correct.
Qed.



Lemma tl_times_aux_correct avoid lsums labs rsums rabs : 
  tl_varset (mk_tl lsums labs) ⊆ avoid ->
  tl_varset (mk_tl rsums rabs) ⊆ avoid -> 
  tl_times_aux avoid lsums labs rsums rabs =t=
  tproduct (mk_tl lsums labs)
    ((mk_tl rsums rabs)).
Proof.
  intros Hav_l Hav_r.
  now apply tl_times_aux_l_correct.
Qed.

Lemma tl_times_correct l r : 
  tl_times l r =t= tproduct l r.
Proof.
  apply tl_times_aux_correct.
  - apply union_subseteq_l.
  - apply union_subseteq_r.
Qed.



Lemma tensorlist_of_tensorexpr_correct te : 
  tensorlist_of_tensorexpr te =t= te.
Proof.
  induction te.
  - reflexivity.
  - cbn.
    now rewrite tproduct_tone_r.
  - cbn.
    now rewrite tl_times_correct, IHte1, IHte2.
  - cbn.
    f_equiv.
    apply IHte.
Qed.


Lemma tsum_comm var ty var' ty' te :
  (var = var' -> ty = ty') ->
  tsum var ty (tsum var' ty' te) =t=
  tsum var' ty' (tsum var ty te).
Proof.
  destruct_decide (decide (var = var')) as Hvars.
  1:{ 
    subst.
    now intros ->.
  }
  intros _.
  intros abs vars.
  cbn.
  rewrite sum_of_comm.
  apply sum_of_ext; intros x.
  apply sum_of_ext; intros y.
  f_equiv.
  now apply insert_commute.
Qed.

(* TODO: General relabeling function taking bound context.
  Also, can there be a framework for knowing the used context? *)

Lemma tensorlist_sums_perm_NoDup_eq sums sums' abs : 
  NoDup sums.*2 -> sums ≡ₚ sums' -> 
  mk_tl sums abs =t= mk_tl sums' abs.
Proof.
  cbn. 
  intros Hsums Heq.
  induction Heq.
  - reflexivity.
  - cbn in *.
    destruct x.
    f_equiv.
    apply IHHeq.
    now rewrite NoDup_cons in Hsums.
  - cbn.
    destruct x, y.
    apply tsum_comm.
    cbn in Hsums.
    rewrite NoDup_cons, not_elem_of_cons in Hsums.
    destruct Hsums as [[? _] _].
    easy.
  - rewrite IHHeq1, IHHeq2; [easy| |easy].
    now rewrite <- Heq1.
Qed.


Lemma te_relabel_one_until_binder_semantics abs vars vars' var var' te : 
  (vars' !! var' = vars !! var) ->
  (forall a, a ≠ var -> a ≠ var' -> vars' !! a = vars !! a) ->
  var' ∉ te_varset te ∖ {[var]} ->
  total_semantics abs vars' (relabel_one_until_binder var var' te) ==
  total_semantics abs vars te.
Proof.
  revert vars vars'; induction te; intros vars vars' Hvar Hvars Hvar'.
  - reflexivity.
  - cbn in *.
    unfold abstract_semantics.
    f_equiv.
    do 2 f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ a Ha%elem_of_list_lookup_2. 
    cbn.
    unfold relabel_var.
    case_decide; [now subst|].
    apply Hvars; set_solver. 
  - cbn in *.
    f_equiv;
    (apply IHte1 || apply IHte2); set_solver.
  - cbn.
    case_decide as Hreg; [subst|]; cbn.
    apply sum_of_ext.
    intros x.
    + apply total_semantics_free_varset_indep.
      intros v Hv. 
      destruct_decide (decide (var = v)); [subst; now setoid_rewrite lookup_insert|].
      setoid_rewrite lookup_insert_ne; [|easy..].
      apply Hvars; try easy.
      clear IHte.
      apply te_free_varset_subseteq in Hv.
      cbn in Hvar'.
      set_solver.
    + apply sum_of_ext; intros x.
      apply IHte.
      3: now clear -Hvar'; cbn in *; set_solver.
      * setoid_rewrite lookup_insert_ne; [auto| |easy].
        now clear -Hvar' Hreg; cbn in *; set_solver.
      * intros a Havar Havar'.
        destruct_decide (decide (reg = a)); [subst; now setoid_rewrite lookup_insert|].
        setoid_rewrite lookup_insert_ne; [|easy..].
        auto.
Qed.

Lemma tsum_relabel_one_until_binder var var' ty te : 
  var' ∉ te_varset te ∖ {[var]} -> 
  tsum var' ty (relabel_one_until_binder var var' te) =t=
  tsum var ty te.
Proof.
  intros Hvar' abs vars.
  cbn.
  apply sum_of_ext; intros x.
  apply te_relabel_one_until_binder_semantics.
  - now setoid_rewrite lookup_insert.
  - intros; now setoid_rewrite lookup_insert_ne.
  - easy.
Qed.


Lemma tsum_overwrite_irrel var var' ty ty' te : 
  var' ∉ te_free_varset te -> 
  tsum var ty (tsum var ty' te) =t=
  tsum var' ty (tsum var ty' te).
Proof.
  intros Hvar' abs vars.
  cbn.
  apply sum_of_ext; intros x.
  apply sum_of_ext; intros y.
  setoid_rewrite insert_insert.
  apply total_semantics_free_varset_indep.
  setoid_rewrite lookup_insert_case.
  intros v Hv.
  case_decide; [easy|].
  setoid_rewrite lookup_insert_ne; [easy|set_solver].
Qed.











Lemma make_sums_free_correct_helper ty var var' sums abs : 
  var ∈ sums.*2 -> var' ∉ abstracts_vars abs ∪ list_to_set sums.*2 ->
  mk_tl ((ty, var) :: sums) abs =t= mk_tl ((ty, var') :: sums) abs.
Proof.
  induction sums as [|[ty' v] sums IHsums]; [easy|].
  cbn.
  rewrite elem_of_cons.
  destruct_decide (decide (var = v)) as Hvar.
  - subst v.
    intros _ Hvar'.
    apply tsum_overwrite_irrel.
    rewrite fold_tensorexpr_of_tensorlist_aux, <- tl_free_varset_correct.
    unfold tl_free_varset.
    cbn -[abstracts_vars].
    set_solver.
  - intros [|Hvarin] Hvar'; [easy|].
    rewrite 2(tsum_comm _ _ v) by (easy || set_solver).
    f_equiv.
    apply IHsums; [easy|].
    set_solver.
Qed.

Lemma make_sums_free_correct avoid sums abs : 
  tl_varset (mk_tl sums abs) ⊆ avoid -> 
  mk_tl (make_sums_free avoid sums) abs =t= mk_tl sums abs.
Proof.
  intros Hav.
  induction sums as [|[ty var] sums IHsums]; [easy|].
  cbn [make_sums_free].
  case_decide as Hvar.
  2: {
    cbn.
    f_equiv.
    apply IHsums; cbn in *; clear -Hav; set_solver.
  }
  rewrite <- (make_sums_free_correct_helper ty var
    (fresh_var _ _)).
  - cbn.
    f_equiv.
    apply IHsums; cbn in *; clear -Hav; set_solver.
  - now rewrite elem_of_list_to_set in Hvar.
  - apply (not_elem_of_weaken _ _ _ (fresh_var_fresh _ _)).
    set_solver +Hav.
Qed. 

Lemma tl_dedup_sums_correct tl : 
  tl_dedup_sums tl =t= tl.
Proof.
  now apply make_sums_free_correct.
Qed.




Lemma tensorlist_abs_perm_eq sums abs abs' : 
  abs ≡ₚ abs' -> 
  mk_tl sums abs =t= mk_tl sums abs'.
Proof.
  intros Habs.
  induction sums; [|cbn; case_match; f_equiv; assumption].
  cbn.
  now rewrite Habs.
Qed.


Lemma tensorlist_perm_eq_correct tl tl' : 
  NoDup tl.(tl_sums).*2 ->
  tensorlist_perm_eq tl tl' -> tl =t= tl'.
Proof.
  intros Hsums [Hsumsp Habsp].
  destruct tl as [sums abs], tl' as [sums' abs'].
  cbn -[tensorexpr_of_tensorlist] in *.
  transitivity (mk_tl sums abs').
  - now apply tensorlist_abs_perm_eq.
  - now apply tensorlist_sums_perm_NoDup_eq.
Qed.


Lemma tl_relabel_tl_bound_aux_semantics abs vars vars' f bound tl :
  (forall v, v ∈ bound ∖ tl_bound_varset tl -> vars !! v = vars' !! (f v)) -> 
  (forall v, v ∈ tl_free_varset tl ∖ bound -> vars !! v = vars' !! v) -> 
  (forall v v', v ∈ bound ∪ tl_bound_varset tl -> v' ∈ bound ∪ tl_bound_varset tl ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ bound ∪ tl_bound_varset tl -> f v ∉ tl_free_varset tl ∖ bound) ->
  tl_bound_varset tl ⊆ bound ->
  (* (forall tv, tv ∈ tl_varset tl ∖  -> (f tv).1 = tv.1) ->  *)
  total_semantics abs vars' (mk_tl (prod_map id f <$> tl_sums tl)
    (relabel_abs (relabel_bound_Idx f bound) <$> tl_abstracts tl)) ==
  total_semantics abs vars tl.
Proof.
  rename abs into cabs.
  rename vars into cvars.
  rename vars' into cvars'.
  destruct tl as [sums abs].
  cbn.
  revert bound cvars cvars'; 
  induction sums as [|[ty var] sums IHsums]; 
  intros bound cvars cvars' Hbound Hfree Hfinj Hffree.
  - cbn in *.
    intros _.
    induction abs as [|[[idx lower] upper] abs IHabs]; [easy|].
    cbn.
    f_equiv.
    2: {
      apply IHabs.
      - intros v Hv.
        apply Hfree.
        clear -Hv.
        unfold tl_free_varset in *.
        cbn in *.
        set_solver.
      - intros v Hv%Hffree.
        clear -Hv.
        unfold tl_free_varset in *.
        cbn in *.
        set_solver.
    }
    erewrite abstract_semantics_ext; [reflexivity..|].
    rewrite <- fmap_app, <- list_fmap_compose.
    apply map_ext_in.
    intros v Hv.
    symmetry.
    cbn.
    unfold relabel_bound_Idx.
    case_decide as Hvbd.
    + apply Hbound; set_solver.
    + apply Hfree.
      unfold tl_free_varset.
      cbn.
      clear -Hv Hvbd.
      apply elem_of_list_In in Hv.
      set_solver.
  - cbn.
    intros Hsubs.
    apply sum_of_ext; intros x.
    apply IHsums.
    + intros v Hv.
      setoid_rewrite lookup_insert_case.
      case_decide as Hvvar.
      * subst.
        now rewrite decide_True by easy.
      * rewrite decide_False; [apply Hbound; clear -Hv Hvvar; set_solver|].
        intros Hfeq; apply Hvvar.
        revert Hfeq.
        apply Hfinj; cbn; clear -Hv; set_solver.
    + intros v Hv.
      setoid_rewrite lookup_insert_case.
      assert (Hvvar : var ≠ v) by (clear -Hsubs Hv; set_solver).
      rewrite decide_False by easy.
      rewrite decide_False; [apply Hfree; clear -Hvvar Hv; 
      unfold tl_free_varset in *; cbn; set_solver|].
      specialize (Hffree var ltac:(clear; set_solver)).
      clear -Hffree Hvvar Hsubs Hv.
      unfold tl_free_varset in *; cbn in *; set_solver.
    + clear -Hfinj; intros ? ? ? ?; apply Hfinj; clear Hfinj; set_solver.
    + clear -Hffree Hsubs; intros v Hv.
      specialize (Hffree v ltac:(clear -Hv; set_solver)).
      clear Hv.
      unfold tl_free_varset in *.
      cbn in *.
      set_solver.
    + clear -Hsubs.
      set_solver.
Qed.


Lemma tl_relabel_bound_semantics abs vars f tl : 
  (forall v v', v ∈ tl_bound_varset tl -> v' ∈ tl_bound_varset tl ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ tl_bound_varset tl -> f v ∉ tl_free_varset tl) ->
  total_semantics abs vars (relabel_bound f tl) ==
  total_semantics abs vars tl.
Proof.
  intros Hfinj Hffree.
  rewrite <- relabel_tl_bound_correct.
  apply tl_relabel_tl_bound_aux_semantics.
  - clear; set_solver.
  - reflexivity.
  - clear -Hfinj; intros ? ? ? ?; apply Hfinj; clear Hfinj; set_solver.
  - intros v.
    specialize (Hffree v).
    specialize (tl_varset_bound_free_disjoint tl).
    set_solver +Hffree.
  - reflexivity.
Qed.

Lemma relabel_tl_bound_correct_teq f tl : 
  (forall v v', v ∈ tl_bound_varset tl -> v' ∈ tl_bound_varset tl ->
    f v = f v' -> v = v') ->
  (forall v, v ∈ tl_bound_varset tl -> f v ∉ tl_free_varset tl) ->
  (* NoDup tl.(tl_sums).*2 -> *)
  teq (relabel_tl_bound f tl) tl.
Proof.
  intros Hfinj Hffree abs vars.
  rewrite relabel_tl_bound_correct.
  now apply tl_relabel_bound_semantics.
Qed.

Lemma tensorlist_teq_sufficient_condition_aux_1 (tl tl' : tensorlist) f : 
    (forall v v', v ∈ tl_bound_varset (tl_dedup_sums tl') -> 
      v' ∈ tl_bound_varset (tl_dedup_sums tl') -> f v = f v' -> v = v') ->
    (forall v, v ∈ tl_bound_varset (tl_dedup_sums tl') -> 
      f v ∉ tl_free_varset (tl_dedup_sums tl')) ->
    tensorlist_perm_eq (tl_dedup_sums tl)
      (relabel_tl_bound f (tl_dedup_sums tl')) ->
  tl =t= tl'.
Proof.
  intros Hfinj Hffree Heq.
  apply tensorlist_perm_eq_correct in Heq; [|now apply tl_dedup_sums_NoDup_vars].
  rewrite relabel_tl_bound_correct_teq in Heq by easy.
  now rewrite 2 tl_dedup_sums_correct in Heq.
Qed.





Lemma tensorlist_teq_sufficient_condition_aux_2_conditions 
  (tl tl' : tensorlist) f : 
  tl_free_varset tl = tl_free_varset tl' -> 
    tensorlist_perm_eq (tl_dedup_sums tl)
      (relabel_tl_bound f (tl_dedup_sums tl')) ->
  
  (forall v v', v ∈ tl_bound_varset (tl_dedup_sums tl') -> 
    v' ∈ tl_bound_varset (tl_dedup_sums tl') -> f v = f v' -> v = v') /\
  (forall v, v ∈ tl_bound_varset (tl_dedup_sums tl') -> 
    f v ∉ tl_free_varset (tl_dedup_sums tl')).
Proof.
  intros Hfrees Hpermeq.
  pose proof Hpermeq as [Hsumsp Habsp].
  cbn -[tl_dedup_sums] in Hsumsp.
  pose proof (tl_dedup_sums_NoDup_vars tl) as Hdup.
  rewrite Hsumsp in Hdup.
  split.
  - intros v v'.
    unfold tl_bound_varset.
    rewrite 2 elem_of_list_to_set.
    apply NoDup_fmap_iff.
    now rewrite snds_prod_map in Hdup.
  - intros v.
    unfold tl_bound_varset.
    rewrite elem_of_list_to_set.
    intros Hv.
    apply (elem_of_list_fmap_1 f) in Hv as Hfv.
    rewrite <- (snds_prod_map id) in Hfv.
    rewrite <- Hsumsp in Hfv.
    rewrite tl_free_varset_tl_dedup_sums.
    rewrite <- Hfrees.
    rewrite <- (elem_of_list_to_set (C:=gset Idx)), fold_tl_bound_varset in Hfv.
    apply tl_varset_bound_free_disjoint in Hfv.
    rewrite tl_free_varset_tl_dedup_sums in Hfv.
    easy.
Qed.


Lemma tensorlist_teq_sufficient_condition_aux_2 (tl tl' : tensorlist) f : 
  tl_free_varset tl = tl_free_varset tl' -> 
    tensorlist_perm_eq (tl_dedup_sums tl)
      (relabel_tl_bound f (tl_dedup_sums tl')) ->
  tl =t= tl'.
Proof.
  intros Hfrees Hpermeq.
  apply tensorlist_teq_sufficient_condition_aux_2_conditions in Hpermeq
    as Hconds; [|easy].
  now apply (tensorlist_teq_sufficient_condition_aux_1 tl tl' f).
Qed.


Lemma tensorlist_teq_sufficient_condition (tl tl' : tensorlist) : 
  tl_free_varset tl = tl_free_varset tl' ->
  (exists f : Idx -> Idx, 
    tensorlist_perm_eq (tl_dedup_sums tl)
      (relabel_tl_bound f (tl_dedup_sums tl'))) ->
  tl =t= tl'.
Proof.
  intros ? []; eauto using tensorlist_teq_sufficient_condition_aux_2.
Qed.










Lemma tl_cons_sum_relabel_one_until_binder var var' ty te : 
  var' ∉ te_varset te ∖ {[var]} -> 
  tsum var' ty (relabel_one_until_binder var var' te) =t=
  tsum var ty te.
Proof.
  intros Hvar' abs vars.
  cbn.
  apply sum_of_ext; intros x.
  apply te_relabel_one_until_binder_semantics.
  - now setoid_rewrite lookup_insert.
  - intros; now setoid_rewrite lookup_insert_ne.
  - easy.
Qed.

Lemma tl_sum_unused_irrelevant_base tl ty v v' : 
  v ∉ tl_used_varset tl -> v' ∉ tl_used_varset tl ->
  tl_cons_sum ty v tl =t= tl_cons_sum ty v' tl.
Proof.
  intros Hv Hv'.
  intros abs vars.
  cbn.
  apply sum_of_ext; intros x.
  apply total_semantics_free_varset_indep.
  fold (tensorexpr_of_tensorlist tl).
  intros v'' Hv''.
  rewrite <- tl_free_varset_correct in Hv''.
  assert (tl_free_varset tl ⊆ tl_used_varset tl) by now clear; set_solver.
  setoid_rewrite lookup_insert_ne; [easy|..]; intros ->; set_solver.
Qed.


Lemma tl_unused_to_front_of_NoDup tl : NoDup tl.(tl_sums).*2 ->
  mk_tl (tl_unused_bound_vars tl ++ 
    tl_used_bound_vars tl) tl.(tl_abstracts) =t= tl.
Proof.
  intros Hdup.
  symmetry.
  apply tensorlist_perm_eq_correct; [easy|].
  split; [|reflexivity].
  cbn.
  unfold tl_unused_bound_vars, tl_used_bound_vars.
  now rewrite filter_neg_with_Permutation.
Qed.




Lemma tl_app_sums_Permutation_NoDup tl sums sums' :
  sums ≡ₚ sums' -> NoDup sums.*2 ->
  (* Forall (.∉ tl_used_varset tl) (sums.*2) -> *)
  tl_app_sums sums tl =t= tl_app_sums sums' tl.
Proof.
  intros Hperm.
  induction Hperm;
  repeat match goal with 
    | x : Ty * Idx |- _ => 
      let ty := fresh "ty" in 
      let var := fresh "var" in 
      destruct x as [ty var]
   end.
  - reflexivity.
  - cbn.
    intros Hdup%NoDup_cons.
    f_equiv.
    now apply IHHperm.
  - cbn.
    intros [[Hne _]%not_elem_of_cons _]%NoDup_cons.
    now apply tsum_comm.
  - intros Hdup.
    pose proof Hdup as Hdup'.
    rewrite Hperm1 in Hdup'.
    etransitivity; eauto.
Qed.


Lemma tl_cons_sum_mor {ty : Ty} {var : Idx} {tl tl' : tensorlist} :
  tl =t= tl' -> tl_cons_sum ty var tl =t= tl_cons_sum ty var tl'.
Proof.
  cbn.
  now intros ->.
Qed.

Lemma tl_app_sums_mor {sums} {tl tl' : tensorlist} :
  tl =t= tl' -> tl_app_sums sums tl =t= tl_app_sums sums tl'.
Proof.
  induction sums as [|[ty var] sums IHsums]; 
  [easy|now intros ?%IHsums; apply tl_cons_sum_mor].
Qed.

Lemma tl_app_sums_Permutation tl sums sums' :
  sums ≡ₚ sums' ->
  Forall (.∉ tl_used_varset tl) (sums.*2) ->
  tl_app_sums sums tl =t= tl_app_sums sums' tl.
Proof.
  intros Hperm.
  induction Hperm;
  repeat match goal with 
    | x : Ty * Idx |- _ => 
      let ty := fresh "ty" in 
      let var := fresh "var" in 
      destruct x as [ty var]
   end.
  - reflexivity.
  - cbn.
    intros Hall.
    decompose_Forall_hyps.
    f_equiv.
    now apply IHHperm.
  - intros Hall.
    decompose_Forall_hyps.
    destruct_decide (decide (var = var0)) as Htyeq.
    2: {
      now apply tsum_comm.
    }
    subst var0.
    pose proof (is_fresh ({[var]} ∪ tl_used_varset tl)) as Hvar'.
    set (var' := fresh ({[var]} ∪ tl_used_varset tl)) in *.
    rewrite (tl_sum_unused_irrelevant_base _ _ var var') by 
      (cbn; rewrite tl_app_sums_eq_app; set_solver).
    transitivity (tl_cons_sum ty0 var (tl_cons_sum ty var' (tl_app_sums l tl)));
    [apply tsum_comm; intros ->; set_solver|].
    apply tl_cons_sum_mor.
    apply tl_sum_unused_irrelevant_base;
    rewrite tl_used_varset_tl_app_sums; easy || set_solver.
  - intros Hall.
    pose proof Hall as Hall'.
    rewrite Hperm1 in Hall'.
    etransitivity; eauto.
Qed.






Lemma tl_unused_at_front_indep tl sums sums' : (* NoDup tl.(tl_sums).*2 -> *)
  NoDup sums.*2 ->
  sums.*1 ≡ₚ sums'.*1 ->
  Forall (.∉ tl_used_varset tl) (sums.*2) -> 
  Forall (.∉ tl_used_varset tl) (sums'.*2) ->
  tl_app_sums sums tl =t= tl_app_sums sums' tl.
Proof.
  intros Hdup.
  intros (sumsp & Hsums_p & Hsums')%fmap_Permuation_iff_exists.
  intros Hall Hall'.
  rewrite (tl_app_sums_Permutation _ _ _ Hsums_p) by easy.
  rewrite Hsums_p in Hdup, Hall.
  clear sums Hsums_p.
  revert sums' Hsums' Hall';
  induction sumsp as [|[ty var] sumsp IHsumsp].
  - intros _ ->%eq_sym%fmap_nil_inv; reflexivity.
  - intros [|[ty' var'] sums']; [easy|].
    cbn [fmap list_fmap fst].
    intros [= <- Hsums'] Hall'.
    cbn in Hdup, Hall, Hall'.
    apply NoDup_cons in Hdup as [Hvarnp Hdup].
    apply Forall_cons in Hall as [Hvar Hall].
    apply Forall_cons in Hall' as [Hvar' Hall'].
    cbn [ tl_app_sums ].
    rewrite (tl_sum_unused_irrelevant_base _ _ _ var') by 
      (rewrite tl_used_varset_tl_app_sums; set_solver).
    apply tl_cons_sum_mor.
    now apply IHsumsp.
Qed.

Lemma tl_unused_at_front_indep' tl tl' sums sums' : (* NoDup tl.(tl_sums).*2 -> *)
  NoDup sums.*2 ->
  sums.*1 ≡ₚ sums'.*1 ->
  Forall (.∉ tl_used_varset tl) (sums.*2) -> 
  Forall (.∉ tl_used_varset tl') (sums'.*2) ->
  tl =t= tl' ->
  tl_app_sums sums tl =t= tl_app_sums sums' tl'.
Proof.
  intros Hdup.
  intros (sumsp & Hsums_p & Hsums')%fmap_Permuation_iff_exists.
  intros Hall Hall' Heq.
  rewrite (tl_app_sums_Permutation _ _ _ Hsums_p) by easy.
  rewrite Hsums_p in Hdup, Hall.
  clear sums Hsums_p.
  revert sums' Hsums' Hall';
  induction sumsp as [|[ty var] sumsp IHsumsp].
  - intros _ ->%eq_sym%fmap_nil_inv _; apply Heq.
  - intros [|[ty' var'] sums']; [easy|].
    cbn [fmap list_fmap fst].
    intros [= <- Hsums'] Hall'.
    cbn in Hdup, Hall, Hall'.
    apply NoDup_cons in Hdup as [Hvarnp Hdup].
    apply Forall_cons in Hall as [Hvar Hall].
    apply Forall_cons in Hall' as [Hvar' Hall'].
    cbn [ tl_app_sums ].
    pose proof (is_fresh (tl_used_varset tl ∪ tl_used_varset tl')) as Hvar''.
    set (var'' := fresh (tl_used_varset tl ∪ tl_used_varset tl')) in *.
    rewrite (tl_sum_unused_irrelevant_base _ _ var var'') by
      (rewrite tl_used_varset_tl_app_sums; set_solver).
    rewrite (tl_sum_unused_irrelevant_base _ _ var' var'') by
      (rewrite tl_used_varset_tl_app_sums; set_solver).
    apply tl_cons_sum_mor.
    now apply IHsumsp.
Qed.




Lemma tl_sum_irrelevant_to_cons_unused ty var tl : 
  var ∉ tl_used_varset tl -> 
  tl_cons_sum ty var tl =t= tl_cons_unused_sum ty tl.
Proof.
  intros Hvar.
  apply tl_sum_unused_irrelevant_base; easy + apply is_fresh.
Qed.

Lemma tl_cons_unused_sum_alt ty tl avoid : 
  tl_used_varset tl ⊆ avoid -> 
  tl_cons_sum ty (fresh avoid) tl =t= tl_cons_unused_sum ty tl.
Proof.
  intros Hunused.
  apply tl_sum_irrelevant_to_cons_unused.
  revert Hunused.
  apply not_elem_of_weaken, is_fresh.
Qed.

Lemma tl_cons_unused_sum_mor ty (tl tl' : tensorlist) : tl =t= tl' -> 
  tl_cons_unused_sum ty tl =t= tl_cons_unused_sum ty tl'.
Proof.
  set (avoid := tl_used_varset tl ∪ tl_used_varset tl').
  intros Heq.
  rewrite <- 2 (tl_cons_unused_sum_alt _ _ avoid) by 
    first [apply union_subseteq_l | apply union_subseteq_r].
  now apply tl_cons_sum_mor.
Qed.

Lemma tl_app_unused_sums_mor tys (tl tl' : tensorlist) : tl =t= tl' -> 
  tl_app_unused_sums tys tl =t= tl_app_unused_sums tys tl'.
Proof.
  intros Heq.
  induction tys; [assumption|now apply tl_cons_unused_sum_mor].
Qed.











Lemma match_tensorlist_correct_aux_map_conditions tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl -> 
  map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' -> 
  size (dom m) = size (map_img m :> gset Idx) ->
  tl_free_varset tl = tl_free_varset tl' -> 
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  (tl_unused_bound_vars tl).*1 ≡ₚ (tl_unused_bound_vars tl').*1 ->
  relabel_abs (relabel_bound_Idx (gmap_map m) (tl_bound_varset tl)) <$>
	tl_abstracts tl ≡ₚ tl_abstracts tl' ->
  tl =t= tl'.
Proof.
  intros Hdup Hdup' Hdom Himg Hinj Hfrees Htypes Hunused Hmabs.
  pose proof Hinj as Hsize.
  rewrite map_dom_img_eq_card_iff_inj in Hinj.
  rewrite <- (tl_unused_to_front_of_NoDup _ Hdup).
  rewrite <- (tl_unused_to_front_of_NoDup _ Hdup').
  rewrite 2 mk_tl_app_sums_aux, <- 2 tl_app_sums_eq_fold.
  assert (NoDup (tl_used_bound_vars tl).*2) as Hudup by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup; apply Hdup).
  assert (NoDup (tl_used_bound_vars tl').*2) as Hudup' by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup'; apply Hdup').
  assert (NoDup (tl_unused_bound_vars tl).*2) as Huudup by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup; apply Hdup).
  assert (NoDup (tl_unused_bound_vars tl').*2) as Huudup' by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup'; apply Hdup').
  apply tl_unused_at_front_indep';
  [assumption|assumption|
    apply Forall_forall; now intros ? 
    Hdiff%elem_of_vars_tl_unused_bound_vars
      %elem_of_difference..|].
  rewrite <- (relabel_tl_bound_correct_teq (gmap_map m)).
  - unfold relabel_tl_bound.
    cbn -[tensorexpr_of_tensorlist].
    rewrite list_to_set_vars_tl_used_bound_vars.
    assert (NoDup (prod_map id (gmap_map m) <$> tl_used_bound_vars tl).*2) as Hndm
      by now apply match_tensorlist_correct_aux_map_NoDup_prod_map.
    apply tensorlist_perm_eq_correct; [easy|].
    split.
    + cbn.
      now apply match_tensorlist_correct_aux_map_used_bound.
    + cbn.
      rewrite <- Hmabs.
      erewrite list_fmap_ext; [reflexivity|].
      intros _ [[abs low] up] Habs%elem_of_list_lookup_2.
      apply relabel_abs_ext.
      cbn.
      apply list_fmap_ext.
      intros _ v Hv%elem_of_list_lookup_2.
      unfold relabel_bound_Idx.
      apply decide_ext.
      enough (v ∈ tl_used_varset tl) by (rewrite elem_of_intersection; tauto).
      apply elem_of_tl_used_varset'.
      eauto.
  - apply gmap_map_inj_on; [easy|]. 
    cbn.
    now rewrite list_to_set_vars_tl_used_bound_vars, Hdom.
  - intros v.
    cbn.
    rewrite list_to_set_vars_tl_used_bound_vars.
    rewrite <- Hdom.
    intros [mv Hmv]%elem_of_dom.
    rewrite (gmap_map_correct _ _ _ Hmv).
    apply (elem_of_map_img_2 (SA:=gset Idx)) in Hmv as Hmvimg.
    rewrite Himg in Hmvimg.
    rewrite tl_free_varset_tl_used_bound_vars, Hfrees.
    apply elem_of_intersection in Hmvimg as [Hmvbound _].
    now apply tl_varset_bound_free_disjoint in Hmvbound.
Qed.




Lemma match_tensorlist_correct_aux_map_conditions' tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  match_tensorlist tl tl' = Some m ->
  (* dom m = tl_bound_varset tl ∩ tl_used_varset tl ->  *)
  (* map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' ->  *)
  NoDup (map_to_list m).*2 ->
  (* size (dom m) = size (map_img m :> gset Idx) -> *)
  (* tl_free_varset tl = tl_free_varset tl' ->  *)
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  tl.(tl_sums).*1 ≡ₚ tl'.(tl_sums).*1 ->
  (* (tl_unused_bound_vars tl).*1 ≡ₚ (tl_unused_bound_vars tl').*1 -> *)
  (* relabel_abs (relabel_bound_Idx (gmap_map m) (tl_bound_varset tl)) <$>
	tl_abstracts tl ≡ₚ tl_abstracts tl' -> *)
  tl =t= tl'.
Proof.
  intros Hdup Hdup' Heq.
  apply mk_is_Some in Heq as Hsome.
  apply match_tensorlist_spec_aux_dom in Heq as Hdom.
  apply match_tensorlist_spec_aux_img in Heq as Himg.
  intros Hsize.
  rewrite <- (map_dom_img_eq_card_iff_NoDup (SA:=gset Idx)) in Hsize.
  apply match_tensorlist_spec_aux_free in Hsome as Hfrees.
  intros Htypes Hunused.
  apply match_tensorlist_spec_aux_2 in Heq as Hmabs.
  apply (match_tensorlist_correct_aux_map_unused tl tl' m) in Hunused; 
    [|easy..].
  now apply (match_tensorlist_correct_aux_map_conditions _ _ m).
Qed.


Lemma match_tensorlist_correct_aux_map_conditions_length tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  match_tensorlist tl tl' = Some m ->
  (* dom m = tl_bound_varset tl ∩ tl_used_varset tl ->  *)
  (* map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' ->  *)
  (* size (dom m) = size (map_img m :> gset Idx) -> *)
  (* tl_free_varset tl = tl_free_varset tl' ->  *)
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  tl.(tl_sums).*1 ≡ₚ tl'.(tl_sums).*1 ->
  length (tl_used_bound_vars tl) = length (tl_used_bound_vars tl') ->
  (* (tl_unused_bound_vars tl).*1 ≡ₚ (tl_unused_bound_vars tl').*1 -> *)
  (* relabel_abs (relabel_bound_Idx (gmap_map m) (tl_bound_varset tl)) <$>
	tl_abstracts tl ≡ₚ tl_abstracts tl' -> *)
  tl =t= tl'.
Proof.
  intros Hdup Hdup' Heq.
  apply mk_is_Some in Heq as Hsome.
  apply match_tensorlist_spec_aux_dom in Heq as Hdom.
  apply match_tensorlist_spec_aux_img in Heq as Himg.
  intros Htypes Hperm Hlen.
  apply (match_tensorlist_correct_aux_map_inj tl tl' m) in Hlen; [|easy..].
  apply match_tensorlist_spec_aux_free in Hsome as Hfrees.
  apply match_tensorlist_spec_aux_2 in Heq as Hmabs.
  apply (match_tensorlist_correct_aux_map_unused tl tl' m) in Hperm; [|easy..].
  now apply (match_tensorlist_correct_aux_map_conditions _ _ m).
Qed.


Lemma tl_dedup_sums_inj tl tl' : 
  tl_dedup_sums tl =t= tl_dedup_sums tl' -> 
  tl =t= tl'.
Proof. 
  now rewrite 2 tl_dedup_sums_correct. 
Qed.




Lemma tensorlist_eqb_correct tl tl' :
  tensorlist_eqb tl tl' = true -> 
  tl =t= tl'.
Proof.
  intros Htl.
  apply Is_true_true in Htl as Htl'.
  apply tensorlist_eqb_spec_aux_1 in Htl' as
    (Htys & Hunused & Hsome).
  revert Hsome.
  destruct (match_tensorlist _ _) as [m|] eqn:Hm;
    [|by intros ?%is_Some_None].
  cbn -[ tl_type_map ].
  rewrite guard_is_Some.
  intros Htypes.
  apply tl_dedup_sums_inj.
  apply (match_tensorlist_correct_aux_map_conditions' _ _ m);
  [apply tl_dedup_sums_NoDup_vars|apply tl_dedup_sums_NoDup_vars|try easy..].
  - apply (map_dom_img_eq_card_iff_NoDup (SA:=gset Idx)).
    apply (match_tensorlist_correct_aux_map_inj (tl_dedup_sums tl)
      (tl_dedup_sums tl'));
    [apply tl_dedup_sums_NoDup_vars|apply tl_dedup_sums_NoDup_vars|
    now apply match_tensorlist_spec_aux_dom in Hm|
    now apply match_tensorlist_spec_aux_img in Hm|].
    specialize (Permutation_length Htys).
    rewrite <- (tl_dedup_sums_types tl), <- (tl_dedup_sums_types tl').
    rewrite 2 length_fmap.
    rewrite 2 tl_sums_used_unused_decomp.
    simpl_list.
    rewrite Hunused.
    lia.
  - by rewrite 2 tl_dedup_sums_types.
Qed.

Lemma tensorlist_eqb_correct_apply abs vars tl tl' :
  tensorlist_eqb tl tl' = true ->
  total_semantics abs vars tl ==
  total_semantics abs vars tl'.
Proof.
  intros Heq%tensorlist_eqb_correct.
  apply Heq.
Qed.

Lemma tensorexpr_eqb_correct_apply abs vars te te' : 
  tensorlist_eqb (tensorlist_of_tensorexpr te)
    (tensorlist_of_tensorexpr te') = true ->
  total_semantics abs vars te ==
  total_semantics abs vars te'.
Proof.
  intros Heq%tensorlist_eqb_correct.
  rewrite 2 tensorlist_of_tensorexpr_correct in Heq.
  apply Heq.
Qed.

End TensorExprSemantics.