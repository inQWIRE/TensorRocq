Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

Require Import Aux_stdpp.



Section TensorExpr. 

(* A parameter giving the types for registers *)
Definition Ty := nat.
Definition Idx := string.


(* Some auxiliary functions *)

Definition fresh_var (var : Idx) (avoid : gset Idx) : Idx :=
  if decide (var ∈ avoid) then fresh avoid else var.

Lemma fresh_var_fresh var avoid : 
  fresh_var var avoid ∉ avoid.
Proof.
  unfold fresh_var.
  case_decide.
  - apply is_fresh.
  - assumption.
Qed.

Lemma fresh_var_id var avoid : var ∉ avoid -> 
  fresh_var var avoid = var.
Proof.
  unfold fresh_var.
  intros HF.
  by apply decide_False.
Qed.

Definition relabel_var (old new : Idx) : Idx -> Idx :=
  fun x => if decide (x = old) then new else x.





Inductive tensorexpr :=
  | tone : tensorexpr  
  | tabstract (absidx : Idx) (lower : list Idx) (upper : list Idx)
  | tproduct (l r : tensorexpr)
  | tsum (reg : Idx) (ty : Ty) (summand : tensorexpr).


Definition tabstract' (abs : Idx * list Idx * list Idx) : tensorexpr :=
  let '(abs, lower, upper) := abs in tabstract abs lower upper.

Fixpoint tproducts (tes : list tensorexpr) : tensorexpr :=
  match tes with
  | [] => tone
  | te :: tes => tproduct te (tproducts tes)
  end.

Fixpoint relabel_te (f : Idx -> Idx) (te : tensorexpr) : tensorexpr :=
  match te with 
  | tone => tone
  | tabstract absidx lower upper => tabstract absidx (f <$> lower) (f <$> upper)
  | tproduct l r => tproduct (relabel_te f l) (relabel_te f r)
  | tsum reg ty summand => 
    tsum (f reg) ty (relabel_te f summand)
  end.

Definition relabel_bound_Idx (f : Idx -> Idx) (bound : gset Idx)
  (tv : Idx) : Idx :=
  if decide (tv ∈ bound) then f tv else tv.

Fixpoint relabel_bound_aux (f : Idx -> Idx) (bound : gset Idx) 
  (te : tensorexpr) : tensorexpr :=
  match te with 
  | tone => tone
  | tabstract absidx lower upper => 
      let f' := relabel_bound_Idx f bound in 
      tabstract absidx (f' <$> lower) (f' <$> upper)
  | tproduct l r => 
      tproduct (relabel_bound_aux f bound l) (relabel_bound_aux f bound r)
  | tsum reg ty summand => 
      tsum (* (relabel_bound_Idx f bound reg) *) (f reg) ty 
        (relabel_bound_aux f ({[reg]} ∪ bound) summand)
  end.

Definition relabel_bound (f : Idx -> Idx) (te : tensorexpr) :=
  relabel_bound_aux f ∅ te.

Fixpoint relabel_one_until_binder (var var' : Idx) (te : tensorexpr) :=
  match te with 
  | tone => tone
  | tabstract idx lower upper => 
    tabstract idx (relabel_var var var' <$> lower)
      (relabel_var var var' <$> upper)
  | tproduct l r => 
    tproduct (relabel_one_until_binder var var' l) 
      (relabel_one_until_binder var var' r)
  | tsum reg ty smd => 
    if decide (reg = var) then tsum reg ty smd 
      else tsum reg ty (relabel_one_until_binder var var' smd)
  end.


Fixpoint te_varset (te : tensorexpr) : gset Idx :=
  match te with 
  | tone => ∅
  | tabstract _ lower upper => list_to_set (lower ++ upper)
  | tproduct l r => te_varset l ∪ te_varset r
  | tsum reg ty summand => 
    {[ reg ]} ∪ te_varset summand
  end.

Fixpoint te_free_varset (te : tensorexpr) : gset Idx :=
  match te with 
  | tone => ∅
  | tabstract _ lower upper => list_to_set (lower ++ upper)
  | tproduct l r => te_free_varset l ∪ te_free_varset r
  | tsum reg ty summand => 
    te_free_varset summand ∖ {[ reg ]}
  end.

Fixpoint te_bound_varset (te : tensorexpr) : gset Idx :=
  match te with 
  | tone => ∅
  | tabstract _ lower upper => ∅
  | tproduct l r => te_bound_varset l ∪ te_bound_varset r
  | tsum reg ty summand => 
      {[ reg ]} ∪ te_bound_varset summand
  end.

Fixpoint te_absset (te : tensorexpr) : gset Idx :=
  match te with 
  | tone => ∅
  | tabstract idx _ _ => {[ idx ]}
  | tproduct l r => te_absset l ∪ te_absset r
  | tsum reg ty summand => 
    te_absset summand
  end.


Lemma te_varset_bound_free_decomp te : 
  te_varset te = te_bound_varset te ∪ te_free_varset te.
Proof.
  induction te; cbn in *; [set_solver..|rewrite IHte].
  unfold_leibniz.
  apply set_subseteq_antisymm; [|set_solver].
  apply union_subseteq; split; [set_solver|].
  apply union_subseteq; split; [set_solver|].
  intros x Hx.
  destruct_decide (decide (x = reg)).
  + subst; set_solver.
  + set_solver.
Qed.





Record tensorlist := mk_tl {
  tl_sums : list (Ty * Idx);
  tl_abstracts : list (Idx * list Idx * list Idx)
}.

Lemma tl_ext tl tl' : 
  tl.(tl_sums) = tl'.(tl_sums) -> 
  tl.(tl_abstracts) = tl'.(tl_abstracts) -> 
  tl = tl'.
Proof.
  destruct tl, tl'; cbn; congruence.
Qed.

Definition tl_cons_sum ty var (tl : tensorlist) : tensorlist :=
  mk_tl ((ty, var) :: tl.(tl_sums)) (tl.(tl_abstracts)).

Fixpoint tl_app_sums sums tl :=
  match sums with 
  | [] => tl
  | (ty, var) :: sums => tl_cons_sum ty var (tl_app_sums sums tl)
  end.

Fixpoint tensorexpr_of_tensorlist_aux sums abs : tensorexpr :=
  match sums with 
  | [] => tproducts (tabstract' <$> abs)
  | (ty, var) :: sums => tsum var ty (tensorexpr_of_tensorlist_aux sums abs)
  end.

Definition tensorexpr_of_tensorlist (tl : tensorlist) : tensorexpr :=
  tensorexpr_of_tensorlist_aux (tl.(tl_sums)) (tl.(tl_abstracts)).

Coercion tensorexpr_of_tensorlist : tensorlist >-> tensorexpr.


Definition tlone : tensorlist := mk_tl [] [].

Lemma tlone_correct : tlone =@{tensorexpr} tone.
Proof.
  reflexivity.
Qed.


Definition tensorlist_perm_eq (tl tl' : tensorlist) :=
  tl.(tl_sums) ≡ₚ tl'.(tl_sums) /\
  tl.(tl_abstracts) ≡ₚ tl'.(tl_abstracts).


(* Variable sets for [tensorlist]s *)

Definition abstracts_vars (abs : list (Idx * list Idx * list Idx)) : gset Idx :=
  list_to_set (concat ((fun '(_, lower, upper) => lower ++ upper) 
    <$> abs)).

Definition tl_free_varset (tl : tensorlist) : gset Idx :=
  (abstracts_vars tl.(tl_abstracts)) ∖ list_to_set (tl.(tl_sums).*2).

Definition tl_varset (tl : tensorlist) : gset Idx :=
  (abstracts_vars tl.(tl_abstracts)) ∪ list_to_set (tl.(tl_sums).*2).

Definition tl_bound_varset (tl : tensorlist) : gset Idx :=
  list_to_set tl.(tl_sums).*2.

Definition tl_used_varset (tl : tensorlist) : gset Idx :=
  abstracts_vars tl.(tl_abstracts).

Definition tl_used_bound_vars tl : list (Ty * Idx) :=
  filter (λ x, x.2 ∈ tl_used_varset tl) tl.(tl_sums).

Definition tl_unused_bound_vars tl : list (Ty * Idx) :=
  filter (λ x, x.2 ∉ tl_used_varset tl) tl.(tl_sums).






Definition tl_cons_unused_sum ty (tl : tensorlist) : tensorlist :=
  tl_cons_sum ty (fresh (tl_used_varset tl)) tl.

Fixpoint tl_app_unused_sums (tys : list Ty) (tl : tensorlist) : tensorlist :=
  match tys with 
  | [] => tl
  | ty :: tys => tl_cons_unused_sum ty (tl_app_unused_sums tys tl)
  end.



Definition tl_type_map (tl : tensorlist) : gmap Idx Ty :=
  list_to_map (prod_swap <$> reverse tl.(tl_sums)).
  
(** Relabeling in [tensorlist]s *)

Definition relabel_one_in_sums (old new : Idx) (sums : list (Ty * Idx)) : 
  list (Ty * Idx) :=
  (prod_map id (relabel_var old new)) <$> sums.

Lemma length_relabel_one_in_sums old new sums : 
  length (relabel_one_in_sums old new sums) = length sums.
Proof.
  apply length_fmap.
Qed.

Definition relabel_one_in_abs (old new : Idx) 
  (abs : list (Idx * list Idx * list Idx)) : 
  list (Idx * list Idx * list Idx) :=
  (prod_map (prod_map id (fmap (FMap:=list_fmap) (relabel_var old new))) 
    (fmap (FMap:=list_fmap) (relabel_var old new))) <$> abs.


Definition relabel_abs (f : Idx -> Idx) (abs : Idx * list Idx * list Idx) :=
  let '(idx, lower, upper) := abs in 
  (idx, f <$> lower, f <$> upper).

Definition relabel_tl_bound (f : Idx -> Idx) (tl : tensorlist) : tensorlist :=
  let bound := tl_bound_varset tl in 
  mk_tl (prod_map id f <$> tl.(tl_sums))
    (relabel_abs (relabel_bound_Idx f bound) <$> tl.(tl_abstracts)).



Fixpoint make_sums_free avoid (sums : list (Ty * Idx)) : list (Ty * Idx) :=
  match sums with 
  | [] => []
  | (ty, var) :: sums' => 
    let free_sums' := make_sums_free avoid sums' in 
    let used := list_to_set (free_sums'.*2) in 
    let var' := if decide (var ∈ used) then fresh_var var (avoid ∪ used) else var in 
    (ty, var') :: free_sums'
  end.

Definition tl_dedup_sums (tl : tensorlist) : tensorlist :=
  mk_tl (make_sums_free (tl_varset tl) (tl.(tl_sums))) (tl.(tl_abstracts)).


Fixpoint make_sums_free' (avoid : gset Idx) (sums : list (Ty * Idx)) : 
  list (Ty * Idx) * gset Idx :=
  match sums with 
  | [] => ([], ∅)
  | (ty, var) :: sums' =>
    let '(free_sums', used) := make_sums_free' avoid sums' in 
    let var' :=
      if decide (var ∈ used) then fresh_var var (avoid ∪ used) 
        else var in 
    ((ty, var') :: free_sums', {[var']} ∪ used)
  end.

Definition tl_dedup_sums' (tl : tensorlist) : tensorlist :=
  mk_tl (make_sums_free' (tl_varset tl) tl.(tl_sums)).1 tl.(tl_abstracts).




Fixpoint tl_times_aux_base_r (avoid : gset Idx)
  (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) 
  len_rsums : length rsums = len_rsums -> 
  tensorlist
  (* list (Ty * Idx) * list (Idx * list Idx * list Idx) *) := 
  match rsums with 
  | [] => fun _ => mk_tl [] (labs ++ rabs)
  | (ty, var) :: rsums' => 
    match len_rsums with 
    | 0 => fun prf => False_rect _ (Nat.neq_succ_0 (length rsums') prf)
    | S len_rsums => 
      fun prf => 
      let var' := fresh_var var avoid in 
      (* let rsums'' := relabel_one_in_sums var var' rsums' in  *)
      let rabs' := relabel_one_in_abs var var' rabs in
      tl_cons_sum ty var' (tl_times_aux_base_r (avoid ∪ ({[var']} ∖ {[var]})) labs 
        (relabel_one_in_sums var var' rsums') rabs'
        (len_rsums) 
        (eq_trans (length_relabel_one_in_sums var var' rsums')
          (Nat.succ_inj (length rsums') _ prf))) 
    end
  end.


Fixpoint tl_times_aux_l (avoid : gset Idx)
  (lsums : list (Ty * Idx)) (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) 
  len_lsums {struct len_lsums} : length lsums = len_lsums -> 
  tensorlist
  (* list (nat * Idx) * list (Idx * list Idx * list Idx) *) :=
  match lsums with 
  | [] => fun _ =>
    tl_times_aux_base_r avoid labs rsums rabs (length rsums) eq_refl
  | (ty, var) :: lsums' => 
    match len_lsums with 
    | 0 => fun prf => False_rect _ (Nat.neq_succ_0 (length lsums') prf)
    | S len_lsums => 
      fun prf => 
      let var' := fresh_var var avoid in 
      (* let rsums'' := relabel_one_in_sums var var' rsums' in  *)
      let labs' := relabel_one_in_abs var var' labs in
      tl_cons_sum ty var' (tl_times_aux_l (avoid ∪ ({[var']} ∖ {[var]})) 
        (relabel_one_in_sums var var' lsums') labs' rsums rabs
        (len_lsums) 
        (eq_trans (length_relabel_one_in_sums var var' lsums')
          (Nat.succ_inj (length lsums') _ prf)))
    end
  end.

Definition tl_times_aux (avoid : gset Idx)
  (lsums : list (Ty * Idx)) (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) :
  tensorlist :=
  tl_times_aux_l avoid lsums labs rsums rabs (length lsums) eq_refl.

Definition tl_times (l r : tensorlist) : tensorlist :=
  let avoid := (tl_varset l) ∪ (tl_varset r) in
  tl_times_aux avoid (l.(tl_sums)) (l.(tl_abstracts))
    (r.(tl_sums)) (r.(tl_abstracts)).

(** Converting a [tensorexpr] to a [tensorlist] *)

Fixpoint tensorlist_of_tensorexpr (te : tensorexpr) : tensorlist :=
  match te with 
  | tone => tlone
  | tabstract idx lower upper => mk_tl [] [(idx, lower, upper)]
  | tproduct l r => tl_times (tensorlist_of_tensorexpr l) (tensorlist_of_tensorexpr r)
  | tsum var ty smd => 
    tl_cons_sum ty var (tensorlist_of_tensorexpr smd)
  end.



(* Matching on [tensorlist]s *)


Fixpoint extend_map_of_abstract_pair (lbound rbound : gset Idx)
  (m : gmap Idx Idx) (l r : list Idx) : option (gmap Idx Idx) :=
  match l, r with 
  | [], [] => Some m
  | hl :: l, hr :: r => 
    if decide (hl ∉ lbound) then 
      if decide (hl = hr /\ hr ∉ rbound) then 
        extend_map_of_abstract_pair lbound rbound m l r
      else None
    else
      if decide (hr ∉ rbound) then None else
      match m !! hl with 
      | Some mhl => 
        if decide (mhl = hr) then 
          extend_map_of_abstract_pair lbound rbound m l r
        else None
      | None => 
        extend_map_of_abstract_pair lbound rbound (<[hl := hr]> m) l r
      end
  | _, _ => None
  end.

Fixpoint extend_match_of_abstract_tensors 
  (lbound rbound : gset Idx) (m : gmap Idx Idx)
  (labs rabs : list (Idx * list Idx * list Idx)) : option (gmap Idx Idx) :=
  match labs with 
  | [] => match rabs with
    | [] => Some m
    | _ => None
    end
  | (fl, lowl, upl) :: labs => 
    head ('((_, lowr, upr), rrest) ← list_select (fun '(fr, _, _) => fl = fr) rabs;
      from_option (λ x, [x]) [] 
        (m' ← extend_map_of_abstract_pair lbound rbound m lowl lowr;
         m'' ← extend_map_of_abstract_pair lbound rbound m' upl upr;
         extend_match_of_abstract_tensors lbound rbound m'' labs rrest)
      )
  end.

Definition match_tensorlist (tl tl' : tensorlist) : option (gmap Idx Idx) :=
  extend_match_of_abstract_tensors (tl_bound_varset tl) (tl_bound_varset tl')
    ∅ (tl.(tl_abstracts)) (tl'.(tl_abstracts)).


(** Reducing [tensorlist]s by removing unused / overridden sums
TODO: Rename to 'reduce_tl_aux*' *)

(* Extract from a tensorlist (in the auxiliary function represented by its data)
  (1) a list of the _relevant_ sums (i.e., not overwritten by later 
    sums _and_ appearing in the abstract terms)
  (2) a list of the types of the irrelevant sums (i.e., those later 
    overwritten by a sum or not used in the abstract terms)
  (3) the set of free variables of the tensorlist *)
Fixpoint canonify_tl_aux (sums : list (Ty * Idx)) 
  (abs : list (Idx * list Idx * list Idx)) : 
    list (Ty * Idx) * (* The relevent (used and non-overwritten) sums *)
    list Ty * (* The types of irrelevant binders *)
    gset Idx (* tl_free_varset (mk_tl sums abs) *) :=
  match sums with 
  | [] => ([], [], abstracts_vars abs) (* no sums; all vars are free *)
  | (ty, var) :: sums => 
    let '(sums', irrel', free') := canonify_tl_aux sums abs in 
    if bool_decide (var ∈ free') then 
      (* This sum is relevant! *)
      ((ty, var) :: sums', irrel', free' ∖ {[var]})
    else
      (* This sum is irrelevant! *)
      (sums', ty :: irrel', free')
  end.

Fixpoint canonify_tl_aux' (sums : list (Ty * Idx)) 
  (abs : gset Idx) : 
    list (Ty * Idx) * (* The relevent (used and non-overwritten) sums *)
    list Ty * (* The types of irrelevant binders *)
    gset Idx (* tl_free_varset (mk_tl sums abs) *) :=
  match sums with 
  | [] => ([], [], abs) (* no sums; all vars are free *)
  | (ty, var) :: sums => 
    let '(sums', irrel', free') := canonify_tl_aux' sums abs in 
    if bool_decide (var ∈ free') then 
      (* This sum is relevant! *)
      ((ty, var) :: sums', irrel', free' ∖ {[var]})
    else
      (* This sum is irrelevant! *)
      (sums', ty :: irrel', free')
  end.


Fixpoint canonify_tl_aux'' (sums : list (Ty * Idx)) 
  (abs : list (Idx * list Idx * list Idx)) : 
    list (Ty * Idx) * (* The relevent (used and non-overwritten) sums *)
    list Ty * (* The types of irrelevant binders *)
    Pset (* tl_free_varset (mk_tl sums abs) *) :=
  match sums with 
  | [] => ([], [], list_to_set $ encode <$> ('(_, low, up) ← abs; low ++ up)) (* no sums; all vars are free *)
  | (ty, var) :: sums => 
    let '(sums', irrel', free') := canonify_tl_aux'' sums abs in 
    if bool_decide (encode var ∈ free') then 
      (* This sum is relevant! *)
      ((ty, var) :: sums', irrel', free' ∖ {[encode var]})
    else
      (* This sum is irrelevant! *)
      (sums', ty :: irrel', free')
  end.


Fixpoint canonify_tl_aux''' (sums : list (Ty * Idx)) 
  (abs : Pset) : 
    list (Ty * Idx) * (* The relevent (used and non-overwritten) sums *)
    list Ty * (* The types of irrelevant binders *)
    Pset (* tl_free_varset (mk_tl sums abs) *) :=
  match sums with 
  | [] => ([], [], abs) (* no sums; all vars are free *)
  | (ty, var) :: sums => 
    let '(sums', irrel', free') := canonify_tl_aux''' sums abs in 
    if bool_decide (encode var ∈ free') then 
      (* This sum is relevant! *)
      ((ty, var) :: sums', irrel', free' ∖ {[encode var]})
    else
      (* This sum is irrelevant! *)
      (sums', ty :: irrel', free')
  end.

Definition canonify_tl (tl : tensorlist) := 
  canonify_tl_aux tl.(tl_sums) tl.(tl_abstracts).





Local Open Scope lazy_bool_scope.

Definition tensorlist_eqb (tl tl' : tensorlist) : bool :=
  let 'mk_tl sums abs := tl in 
  let 'mk_tl sums' abs' := tl' in 
  bool_decide (sums.*1 ≡ₚ sums'.*1) &&&
  let '(usedsums, tys, _) := canonify_tl_aux'' sums abs in 
  let '(usedsums', tys', _) := canonify_tl_aux'' sums' abs' in 
  bool_decide (length tys = length tys') &&&
  match 
    match_tensorlist (mk_tl usedsums abs) (mk_tl usedsums' abs') with
  | None => false
  | Some m => 
    let tym := tl_type_map (mk_tl usedsums abs) in 
    let tym' := tl_type_map (mk_tl usedsums' abs') in 
    bool_decide (map_Forall (fun v v' => 
      tym !! v = 
      tym' !! v') m)
  end.







Lemma tensorexpr_of_tensorlist_aux_eq_fold_right sums abs : 
  tensorexpr_of_tensorlist_aux sums abs = 
  fold_right (fun '(ty, var) => tsum var ty) (
      tproducts (tabstract' <$> abs)
    ) sums.
Proof.
  induction sums; [reflexivity|cbn; case_match; congruence].
Qed.

Lemma tensorexpr_of_tensorlist_eq_fold_right tl : 
  tensorexpr_of_tensorlist tl = 
  fold_right (fun '(ty, var) => tsum var ty) (
      tproducts (tabstract' <$> tl.(tl_abstracts))
    ) tl.(tl_sums).
Proof.
  apply tensorexpr_of_tensorlist_aux_eq_fold_right.
Qed.







Lemma tl_times_aux_l_eq_lsums avoid lsums lsums' labs rsums rabs 
  len_lsums len_lsums' prf prf' : 
  lsums = lsums' -> 
  tl_times_aux_l avoid lsums labs rsums rabs len_lsums prf = 
  tl_times_aux_l avoid lsums' labs rsums rabs len_lsums' prf'.
Proof.
  intros <-.
  rewrite <- prf'.
  rewrite <- prf.
  reflexivity.
Qed.

Lemma tl_times_aux_r_eq_rsums avoid labs rsums rsums' rabs 
  len_rsums len_rsums' prf prf' : 
  rsums = rsums' -> 
  tl_times_aux_base_r avoid labs rsums rabs len_rsums prf = 
  tl_times_aux_base_r avoid labs rsums' rabs len_rsums' prf'.
Proof.
  intros <-.
  rewrite <- prf'.
  rewrite <- prf.
  reflexivity.
Qed.

Lemma tl_times_aux_lsums_succ (avoid : gset Idx)
  ty var
  (lsums' : list (Ty * Idx)) (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) :
  tl_times_aux avoid ((ty, var) :: lsums') labs rsums rabs =
  let var' := fresh_var var avoid in 
  (* let lsums'' := relabel_one_in_sums var var' rsums' in  *)
  let labs' := relabel_one_in_abs var var' labs in
  tl_cons_sum ty var' (tl_times_aux (avoid ∪ ({[var']} ∖ {[var]})) 
    (relabel_one_in_sums var var' lsums') labs' rsums rabs).
Proof.
  cbn.
  f_equal.
  now apply tl_times_aux_l_eq_lsums.
Qed.


Lemma tl_free_varset_correct tl : 
  tl_free_varset tl = te_free_varset tl.
Proof.
  destruct tl as [sums abs].
  unfold tl_free_varset.
  cbn.
  revert abs; induction sums as [|[ty var] sums IHsums]; intros abs.
  - cbn.
    rewrite difference_empty_L.
    induction abs as [|((idx&lower)&upper) abs IHabs]; [reflexivity|].
    cbn.
    rewrite list_to_set_app_L.
    now rewrite IHabs.
  - cbn.
    rewrite <- IHsums.
    rewrite difference_difference_l_L.
    now rewrite (union_comm_L {[var]}).
Qed.


Lemma tl_varset_correct tl : 
  tl_varset tl = te_varset tl.
Proof.
  destruct tl as [sums abs].
  unfold tl_varset.
  cbn.
  revert abs; induction sums as [|[ty var] sums IHsums]; intros abs.
  - cbn.
    rewrite union_empty_r_L.
    induction abs as [|((idx&lower)&upper) abs IHabs]; [reflexivity|].
    cbn.
    rewrite list_to_set_app_L.
    now rewrite IHabs.
  - cbn.
    rewrite <- IHsums.
    set_solver.
Qed.


Lemma te_bound_varset_subseteq te : 
  te_bound_varset te ⊆ te_varset te.
Proof.
  rewrite te_varset_bound_free_decomp; set_solver.
Qed.

Lemma te_free_varset_subseteq te : 
  te_free_varset te ⊆ te_varset te.
Proof.
  rewrite te_varset_bound_free_decomp; set_solver.
Qed.


Lemma fold_tensorexpr_of_tensorlist_aux sums abs : 
  tensorexpr_of_tensorlist_aux sums abs = 
  mk_tl sums abs.
Proof.
  reflexivity.
Qed.

Lemma abstract_vars_correct abs : 
  abstracts_vars abs = te_free_varset (tproducts (tabstract' <$> abs)).
Proof.
  unfold abstracts_vars.
  induction abs as [|[[] ?]]; cbn; [reflexivity|].
  set_solver.
Qed.

Lemma abstract_vars_correct' abs : 
  abstracts_vars abs = te_varset (tproducts (tabstract' <$> abs)).
Proof.
  unfold abstracts_vars.
  induction abs as [|[[] ?]]; cbn; [reflexivity|].
  set_solver.
Qed.

Lemma relabel_one_in_correct var var' sums abs : 
  {|
    tl_sums :=
      relabel_one_in_sums var var' sums;
    tl_abstracts :=
      relabel_one_in_abs var var' abs
  |} =@{tensorexpr} 
  relabel_te (relabel_var var var') (mk_tl sums abs).
Proof.
  cbn.
  induction sums as [|[ty v] sums IHsums].
  - cbn.
    induction abs as [|[[idx lower] upper] abs IHabs]; [reflexivity|].
    cbn.
    f_equiv.
    apply IHabs.
  - cbn.
    f_equal.
    apply IHsums.
Qed.









Lemma te_bound_varset_tproducts tes : 
  te_bound_varset (tproducts tes) = 
  ⋃ (te_bound_varset <$> tes).
Proof.
  induction tes; cbn; set_solver.
Qed.

Lemma te_free_varset_tproducts tes : 
  te_free_varset (tproducts tes) = 
  ⋃ (te_free_varset <$> tes).
Proof.
  induction tes; cbn; set_solver.
Qed.

Lemma te_varset_tproducts tes : 
  te_varset (tproducts tes) = 
  ⋃ (te_varset <$> tes).
Proof.
  induction tes; cbn; set_solver.
Qed.


Lemma tl_bound_varset_correct tl : 
  tl_bound_varset tl = te_bound_varset tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  induction sums as [|[ty var] sums IHsums]; [|cbn in *; set_solver].
  cbn.
  rewrite te_bound_varset_tproducts.
  rewrite <- list_fmap_compose.
  apply set_eq; intros x.
  rewrite elem_of_union_list.
  split; [easy|].
  intros (X & (((?&?)&?) & -> & ?)%elem_of_list_fmap & Hx).
  apply Hx.
Qed.


Lemma helper_relabel_bound_aux_tl f bound sums abs :
  relabel_bound_aux f bound (mk_tl sums abs) = 
  fold_right (fun '(ty, var) => tsum var ty) 
    (relabel_bound_aux f (bound ∪ list_to_set sums.*2) (mk_tl [] abs))
  (prod_map id f <$> sums).
Proof.
  cbn.
  revert bound;
  induction sums; intros bound.
  - cbn.
    now rewrite union_empty_r_L.
  - cbn.
    case_match.
    cbn in *.
    rewrite IHsums.
    do 3 f_equal.
    clear; set_solver.
Qed.

(* Lemma relabel_tl_bound_aux_correct bound f tl : 
  tl_bound_varset tl ⊆ bound ->
  relabel_tl_bound f tl =@{tensorexpr} relabel_bound_aux f bound tl.
Proof.
  destruct tl as [sums abs].
  cbn. *)

Lemma relabel_tl_bound_correct f tl : 
  relabel_tl_bound f tl =@{tensorexpr} relabel_bound f tl.
Proof.
  destruct tl as [sums abs].
  unfold relabel_bound.
  rewrite helper_relabel_bound_aux_tl.
  rewrite tensorexpr_of_tensorlist_eq_fold_right.
  f_equal.
  cbn.
  rewrite union_empty_l_L.
  induction abs as [|[[idx lower] upper] abs IHabs]; cbn; [reflexivity|].
  rewrite IHabs.
  reflexivity.
Qed.





Lemma make_sums_free_diff_free avoid sums : 
  list_to_set (make_sums_free avoid sums).*2 ∖ list_to_set sums.*2 ## avoid.
Proof.
  hnf.
  induction sums as [|[ty var] sums IHsums]; [set_solver|].
  cbn.
  intros x.
  case_decide as Hx.
  - specialize (IHsums x).
    pose proof (fresh_var_fresh var (avoid ∪ list_to_set (make_sums_free avoid sums).*2)).
    clear Hx.
    set_solver.
  - set_solver.
Qed.

Lemma make_sums_free_supseteq avoid sums : 
  list_to_set sums.*2 ⊆@{gset Idx} list_to_set (make_sums_free avoid sums).*2.
Proof.
  induction sums as [|[ty var] sums IHsums]; [set_solver|].
  cbn.
  intros x.
  case_decide as Hx; set_solver.
Qed.

Lemma NoDup_make_sums_free avoid sums : 
  NoDup (make_sums_free avoid sums).*2.
Proof.
  induction sums as [|(ty & var) sums IHsums]; [constructor|].
  cbn.
  apply NoDup_cons.
  split; [|apply IHsums].
  case_decide; [|now rewrite elem_of_list_to_set in *].
  rewrite <- (not_elem_of_list_to_set (C:=gset Idx)).
  apply (not_elem_of_weaken _ _ _ (fresh_var_fresh _ _)).
  apply union_subseteq_r.
Qed.

Lemma tl_dedup_sums_NoDup_vars tl : 
  NoDup (tl_dedup_sums tl).(tl_sums).*2.
Proof.
  apply NoDup_make_sums_free.
Qed.

Lemma tl_free_varset_tl_dedup_sums tl : 
  tl_free_varset (tl_dedup_sums tl) = tl_free_varset tl.
Proof.
  unfold tl_free_varset.
  cbn -[abstracts_vars].
  pose proof (make_sums_free_diff_free (tl_varset tl) (tl_sums tl)) as Hdisj.
  pose proof (make_sums_free_supseteq (tl_varset tl) (tl_sums tl)) as Hsup.
  set_solver.
Qed.


Lemma fold_tl_bound_varset tl : 
  list_to_set tl.(tl_sums).*2 = tl_bound_varset tl.
Proof.
  reflexivity.
Qed.

Lemma tl_dedup_sums_vars_supset tl : 
  tl_bound_varset tl ⊆ tl_bound_varset (tl_dedup_sums tl).
Proof.
  apply make_sums_free_supseteq.
Qed.

Lemma tl_dedup_sums_vars_disj tl : 
  tl_bound_varset (tl_dedup_sums tl) ∖ tl_bound_varset tl ## tl_varset tl.
Proof.
  apply make_sums_free_diff_free.
Qed.


Lemma make_sums_free_spec_lookup_same avoid (sums : list (Ty * Idx)) i ty v : 
  list_to_set sums.*2 ⊆ avoid ->
  sums !! i = Some (ty, v) -> 
  v ∉ drop (S i) sums.*2 ->
  make_sums_free avoid sums !! i = Some (ty, v).
Proof.
  revert sums; induction i; (intros [|[ty' v'] sums]; [easy|]).
  - rewrite not_elem_of_drop_iff.
    cbn.
    intros Hsubs [= -> ->] Hnotin.
    rewrite decide_False; [easy|].
    intros Hv. 
    pose proof (make_sums_free_diff_free avoid sums) as Hdisj.
    specialize (Hdisj v).
    rewrite elem_of_difference in Hdisj.
    apply Hdisj; [|set_solver].
    split; [easy|].
    rewrite elem_of_list_to_set, elem_of_list_lookup.
    intros (i & Hi).
    rewrite list_lookup_fmap in Hi.
    apply fmap_Some in Hi as (tyv & Htyv & Hvtyv).
    apply (Hnotin (S i) tyv.2 ltac:(lia)); [|easy].
    cbn.
    setoid_rewrite list_lookup_fmap.
    now setoid_rewrite Htyv.
  - intros Hsubs.
    cbn.
    apply IHi.
    rewrite <- Hsubs; apply union_subseteq_r.
Qed.

Lemma make_sums_free_lookup_spec avoid (sums : list (Ty * Idx)) i : 
  (make_sums_free avoid sums !! i = sums !! i /\
   forall v, snd <$> (make_sums_free avoid sums !! i) = Some v -> v ∉ drop (S i) sums.*2) \/
  (exists ty var', (make_sums_free avoid sums !! i) = Some (ty, var') /\
    fst <$> (sums !! i) = Some ty /\ var' ∉ avoid).
Proof.
  revert i; induction sums as [|[ty var] sums IHsums]; intros i; [now left|].
  destruct i; [|apply IHsums].
  cbn.
  case_decide as Hvar; cbn.
  - right.
    eexists ty, _.
    split; [reflexivity|].
    split; [easy|].
    eapply not_elem_of_weaken; [apply fresh_var_fresh|].
    apply union_subseteq_l.
  - left.
    split; [easy|].
    intros _ [= <-].
    rewrite <- (elem_of_list_to_set (C:=gset Idx)).
    rewrite drop_0.
    now intros Hvar'%(make_sums_free_supseteq avoid sums).
Qed.


Lemma relabel_tl_bound_ext f g tl : 
  (forall x, x ∈ tl_bound_varset tl -> f x = g x) -> 
  relabel_tl_bound f tl = relabel_tl_bound g tl.
Proof.
  intros Hfg.
  unfold relabel_tl_bound.
  f_equal.
  - apply list_fmap_ext.
    intros i (ty & var) Hvar%elem_of_list_lookup_2.
    cbn.
    f_equal.
    apply Hfg.
    unfold tl_bound_varset.
    rewrite elem_of_list_to_set.
    now apply (elem_of_list_fmap_1 snd) in Hvar.
  - apply list_fmap_ext.
    intros _ [[idx lower] upper] _.
    cbn.
    f_equal; [f_equal|]; apply list_fmap_ext; 
    intros _ v _; unfold relabel_bound_Idx;
    case_decide; auto.
Qed.



Add Parametric Morphism : relabel_tl_bound with signature
  pointwise_relation Idx eq ==> tensorlist_perm_eq ==> 
  tensorlist_perm_eq as relabel_tl_bound_perm_mor.
Proof.
  intros f g Hfg tl tl' Htl.
  pose proof Htl as [Hsums Habs].
  rewrite (relabel_tl_bound_ext f g) by now intros; apply Hfg.
  split; cbn.
  - now rewrite Hsums.
  - unfold tl_bound_varset.
    now rewrite Habs, Hsums.
Qed.

Lemma tl_bound_varset_subseteq tl : tl_bound_varset tl ⊆ tl_varset tl.
Proof.
  now rewrite tl_bound_varset_correct, 
    tl_varset_correct, te_bound_varset_subseteq.
Qed.

Lemma tl_free_varset_subseteq tl : tl_free_varset tl ⊆ tl_varset tl.
Proof.
  now rewrite tl_free_varset_correct, 
    tl_varset_correct, te_free_varset_subseteq.
Qed.


Lemma relabel_bound_aux_tl_alt f bound (tl : tensorlist) : 
  relabel_bound_aux f bound tl = 
  relabel_bound_aux f (bound ∪ tl_bound_varset tl) tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  revert bound; induction sums as [|[ty var] sums IHsums]; intros bound.
  - cbn.
    f_equal; set_solver.
  - cbn.
    rewrite IHsums.
    do 2 f_equal.
    clear; set_solver.
Qed.



Lemma tl_free_varset_eq_diff (tl : tensorlist) : 
  tl_free_varset tl = tl_varset tl ∖ tl_bound_varset tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  unfold tl_varset, tl_free_varset.
  cbn.
  set_solver.
Qed.

Lemma tl_varset_bound_free_disjoint tl : 
  tl_bound_varset tl ## tl_free_varset tl.
Proof.
  rewrite tl_free_varset_eq_diff.
  set_solver.
Qed.



Lemma elem_of_tl_bound_varset_relabel_tl_bound f tl x : 
  x ∈ tl_bound_varset (relabel_tl_bound f tl) <-> 
    exists y, y ∈ tl_bound_varset tl /\ x = f y.
Proof.
  cbn.
  unfold tl_bound_varset.
  setoid_rewrite elem_of_list_to_set.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_list_fmap.
  split; [naive_solver|].
  intros (? & ((t&v) & -> & ?) & ?).
  cbn in *.
  exists (t, x).
  split; [easy|].
  eexists (_,_); cbn; eauto 20 using f_equal.
Qed.



Lemma relabel_abs_ext f g abs : 
  f <$> (abs.1.2 ++ abs.2) = g <$> (abs.1.2 ++ abs.2) ->
  relabel_abs f abs = relabel_abs g abs.
Proof.
  destruct abs as [[idx lower] upper].
  unfold relabel_abs.
  cbn.
  rewrite 2 fmap_app.
  intros [-> ->]%app_inj_len_l; [easy|].
  now simpl_list.
Qed.


Lemma relabel_abs_ext' f g abs abs' :
  abs.1.1 = abs'.1.1 ->
  length abs.2 = length abs'.2 ->
  f <$> (abs.1.2 ++ abs.2) = g <$> (abs'.1.2 ++ abs'.2) ->
  relabel_abs f abs = relabel_abs g abs'.
Proof.
  destruct abs as [[idx lower] upper], abs' as [[idx' lower'] upper'].
  unfold relabel_abs.
  cbn.
  rewrite 2 fmap_app.
  intros -> Hlen [-> ->]%app_inj_len_r; [easy|].
  now simpl_list.
Qed.



Lemma relabel_tl_bound_compose f g tl : 
  (forall v, v ∈ tl_bound_varset tl -> g v ∉ tl_free_varset tl) ->
  relabel_tl_bound (f ∘ g) tl =
  relabel_tl_bound f (relabel_tl_bound g tl).
Proof.
  intros Hg.
  apply tl_ext; cbn -[tl_bound_varset].
  - rewrite <- list_fmap_compose.
    reflexivity.
  - rewrite <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ [[idx lower] upper] Habs%elem_of_list_lookup_2.
    cbn [compose].
    apply relabel_abs_ext'; [reflexivity|now cbn; simpl_list|].
    cbn -[tl_bound_varset].
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
    unfold relabel_bound_Idx; cbn -[tl_bound_varset].
    case_decide as Hvbd.
    + symmetry; apply decide_True.
      rewrite elem_of_tl_bound_varset_relabel_tl_bound.
      eauto.
    + symmetry; apply decide_False.
      rewrite elem_of_tl_bound_varset_relabel_tl_bound.
      intros (y & Hybd & ->).
      apply (Hg y); [easy|].
      rewrite tl_free_varset_eq_diff.
      apply elem_of_difference; split; [|easy].
      unfold tl_varset.
      rewrite elem_of_union; left.
      unfold abstracts_vars.
      rewrite list_to_set_concat, elem_of_union_list.
      exists (list_to_set (lower ++ upper)).
      split; [apply elem_of_list_fmap_1;
        refine (elem_of_list_fmap_1 _ _ (idx, lower, upper) Habs)|].
      now apply elem_of_list_to_set.
Qed.


Lemma relabel_tl_bound_id tl : 
  relabel_tl_bound id tl = tl.
Proof.
  apply tl_ext; cbn.
  - rewrite <- (list_fmap_id tl.(tl_sums)) at 2.
    now apply list_fmap_ext; intros ? [].
  - rewrite <- (list_fmap_id tl.(tl_abstracts)) at 2.
    apply list_fmap_ext; intros ? [[]] _; cbn.
    f_equal; [f_equal|];
    symmetry; rewrite <- list_fmap_id at 1; 
    apply list_fmap_ext; intros ? ? _;
    unfold relabel_bound_Idx; now case_decide.
Qed.








Lemma extend_map_of_abstract_pair_dom_img_strong {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m' = dom m ∪ lbound ∩ list_to_set l /\
  map_img m' = map_img m ∪ rbound ∩ list_to_set r.
Proof.
  revert r m m';
  induction l as [|hl l IHl];
  intros r m m';
  destruct r as [|hr r]; 
  [|easy..|].
  - cbn.
    intros [= <-].
    set_solver.
  - cbn.
    (repeat case_decide || case_match);
    try easy;
    intros Heq;
    specialize (IHl _ _ _ Heq) as [Hdomm' Himgm'];
    repeat_on_hyps (fun H => apply elem_of_dom_2 in H as ?; 
      apply (elem_of_map_img_2 (SA:=gset Idx)) in H);
    subst;
    (
    split;
    [rewrite Hdomm';
      rewrite 1?dom_insert;
      clear Hdomm' Himgm';
      set_solver
    |
      rewrite Himgm';
      rewrite ?map_img_insert_notin_L by easy;
      set_solver
    ]).
Qed.

Lemma extend_map_of_abstract_pair_dom_img {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m' ⊆ dom m ∪ lbound /\
  map_img m' ⊆ map_img m ∪ rbound.
Proof.
  intros [Hdom Himg]%extend_map_of_abstract_pair_dom_img_strong.
  split.
  - rewrite Hdom; clear; set_solver.
  - rewrite Himg; clear; set_solver.
Qed.




Lemma extend_map_of_abstract_pair_dom {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m' ⊆ dom m ∪ lbound.
Proof.
  now intros ?%extend_map_of_abstract_pair_dom_img.
Qed.

Lemma extend_map_of_abstract_pair_dom' {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m ⊆ lbound ->
  dom m' ⊆ lbound.
Proof.
  intros ?%extend_map_of_abstract_pair_dom.
  set_solver.
Qed.


Lemma extend_map_of_abstract_pair_subseteq {lbound rbound m l r m'} : 
  dom m ⊆ lbound ->
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  m ⊆ m'.
Proof.
  revert r m m';
  induction l as [|hl l IHl];
  intros r m m';
  destruct r as [|hr r]; 
  [now intros ? [= <-]..|].
  intros Hdom.
  cbn.
  case_decide as Hlfree.
  - case_decide as Heq; [subst | easy].
    now apply IHl.
  - case_decide as Hrbound; [easy|].
    case_match eqn:Hmhl.
    + case_decide as Heq; [|easy].
      now apply IHl.
    + intros Hsub%IHl.
      * rewrite <- Hsub.
        now apply insert_subseteq.
      * set_solver.
Qed.

Lemma extend_map_of_abstract_pair_dom_contains {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m ∪ (lbound ∩ list_to_set l) ⊆ dom m'.
Proof.
  intros [-> _]%extend_map_of_abstract_pair_dom_img_strong.
  reflexivity.
Qed.


Lemma extend_map_of_abstract_pair_dom_eq {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  dom m' = dom m ∪ (lbound ∩ list_to_set l).
Proof.
  now intros Heq%extend_map_of_abstract_pair_dom_img_strong.
Qed.

Lemma extend_map_of_abstract_pair_img_eq {lbound rbound m l r m'} : 
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  map_img m' = map_img m ∪ (rbound ∩ list_to_set r).
Proof.
  now intros Heq%extend_map_of_abstract_pair_dom_img_strong.
Qed.

Lemma extend_map_of_abstract_pair_is_Some_free {lbound rbound m l r} : 
  is_Some (extend_map_of_abstract_pair lbound rbound m l r) ->
  list_to_set l ∖ lbound = list_to_set r ∖ rbound.
Proof.
  intros [m' Heq].
  revert Heq.
  revert r m m';
  induction l as [|hl l IHl];
  intros r m m';
  destruct r as [|hr r]; 
  [intros [= <-]; set_solver..|].
  cbn.
  case_decide as Hlfree.
  - case_decide as Heq; [subst | easy].
    intros Heq'%IHl.
    set_solver.
  - case_decide as Hrbound; [easy|].
    case_match eqn:Hmhl.
    + case_decide as Heq; [|easy].
      intros Heq'%IHl.
      set_solver.
    + intros Hsub%IHl.
      set_solver.
Qed.

Lemma extend_map_of_abstract_pair_spec_full {lbound rbound m l r m'} : 
  dom m ⊆ lbound ->
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  (forall mext, dom mext ⊆ lbound -> m' ⊆ mext ->
  gmap_map mext <$> l = r).
Proof.
  revert r m m';
  induction l as [|hl l IHl];
  intros r m m';
  destruct r as [|hr r]; 
  [easy..|].
  intros Hdom.
  cbn.
  case_decide as Hlfree.
  - case_decide as Heq; [destruct_and!; subst | easy].
    intros Heq.
    specialize (IHl _ _ _ Hdom Heq).
    specialize (extend_map_of_abstract_pair_dom Heq)
      as Hdom'.
    intros mext Hdomext Hsub.
    rewrite gmap_map_idemp by set_solver. 
    now rewrite IHl.
  - case_decide as Hrbound; [easy|].
    case_match eqn:Hmhl.
    + case_decide as Heq; [|easy].
      subst.
      intros Heq.
      intros mext Hdomext Hsub.
      rewrite (IHl _ _ _ Hdom Heq) by easy.
      f_equal.
      apply gmap_map_correct.
      revert Hsub.
      apply lookup_weaken.
      specialize (extend_map_of_abstract_pair_subseteq Hdom Heq).
      now apply lookup_weaken.
    + intros Heq.
      specialize (fun H => IHl _ _ _ H Heq).
      specialize (IHl ltac:(set_solver)).
      intros mext Hdomext Hsub.
      rewrite IHl by easy.
      f_equal.
      apply gmap_map_correct.
      revert Hsub.
      apply lookup_weaken.
      specialize (extend_map_of_abstract_pair_subseteq 
        (lbound:=lbound) (m:=<[hl := hr]> m)
        ltac:(set_solver) Heq).
      apply lookup_weaken.
      apply lookup_insert.
Qed.


Lemma extend_map_of_abstract_pair_spec {lbound rbound m l r m'} : 
  dom m ⊆ lbound ->
  extend_map_of_abstract_pair lbound rbound m l r = Some m' ->
  gmap_map m' <$> l = r.
Proof.
  intros Hdom Heq.
  apply (extend_map_of_abstract_pair_spec_full Hdom Heq).
  - now apply (extend_map_of_abstract_pair_dom' Heq).
  - reflexivity.
Qed.



Local Add Parametric Morphism : abstracts_vars with signature
  Permutation ==> eq as abstracts_vars_perm_mor_.
Proof.
  unfold abstracts_vars.
  now intros ? ? ->.
Qed.

Lemma extend_match_of_abstract_tensors_dom_img_strong {lbound rbound m labs rabs mres} : 
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  dom mres = dom m ∪ (lbound ∩ abstracts_vars labs) /\
  map_img mres = map_img m ∪ (rbound ∩ abstracts_vars rabs).
Proof.
  revert rabs m mres;
  induction labs as [|[[fl lowl] upl] labs IHlabs];
  intros rabs m mres;
  [destruct rabs; [|easy]; now intros [= <-]; set_solver|].
  cbn.
  intros Heq.
  apply head_Some_elem_of in Heq as Hmem.
  apply elem_of_list_bind in Hmem as 
    (([[fr lowr] upr] & rrest) & 
      (m' & Hm_m' & 
      (m'' & Hm'_m'' & Hm'')%bind_Some
      )%elem_of_from_option_list_singleton%bind_Some & 
      Hsel).
  apply elem_of_list_select_perm in Hsel as Hrperm.
  revert Hsel; intros (-> & Hdecomp)%elem_of_list_select.
  clear Heq.
  rewrite Hrperm.
  cbn.
  rewrite 4 list_to_set_app_L.
  fold (abstracts_vars labs).
  fold (abstracts_vars rrest).
  specialize (IHlabs _ _ _ Hm'').
  specialize (extend_map_of_abstract_pair_dom_img_strong Hm_m').
  specialize (extend_map_of_abstract_pair_dom_img_strong Hm'_m'').
  destruct IHlabs as [Hdom1 Himg1].
  rewrite Hdom1, Himg1.
  intros [-> ->] [-> ->].
  clear; set_solver.
Qed.


Lemma extend_match_of_abstract_tensors_is_Some_free {lbound rbound m labs rabs} : 
  is_Some (extend_match_of_abstract_tensors lbound rbound m labs rabs) ->
  abstracts_vars labs ∖ lbound = abstracts_vars rabs ∖ rbound.
Proof.
  intros [mres Heq].
  revert Heq.
  revert rabs m mres;
  induction labs as [|[[fl lowl] upl] labs IHlabs];
  intros rabs m mres;
  [destruct rabs; [|easy]; now intros [= <-]; set_solver|].
  cbn.
  intros Heq.
  apply head_Some_elem_of in Heq as Hmem.
  apply elem_of_list_bind in Hmem as 
    (([[fr lowr] upr] & rrest) & 
      (m' & Hm_m' & 
      (m'' & Hm'_m'' & Hm'')%bind_Some
      )%elem_of_from_option_list_singleton%bind_Some & 
      Hsel).
  apply elem_of_list_select_perm in Hsel as Hrperm.
  revert Hsel; intros (-> & Hdecomp)%elem_of_list_select.
  clear Heq.
  rewrite Hrperm.
  cbn.
  rewrite 4 list_to_set_app_L.
  fold (abstracts_vars labs).
  fold (abstracts_vars rrest).
  specialize (IHlabs _ _ _ Hm'').
  specialize (extend_map_of_abstract_pair_is_Some_free (mk_is_Some _ _ Hm_m')).
  specialize (extend_map_of_abstract_pair_is_Some_free (mk_is_Some _ _ Hm'_m'')).
  clear -IHlabs.
  rewrite 2 (difference_union_distr_l_L _ _ lbound).
  rewrite 2 (difference_union_distr_l_L _ _ rbound).
  intros -> ->.
  rewrite IHlabs.
  reflexivity.
Qed.

Lemma extend_match_of_abstract_tensors_dom_img {lbound rbound m labs rabs mres} : 
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  dom mres ⊆ dom m ∪ lbound /\
  map_img mres ⊆ map_img m ∪ rbound.
Proof.
  intros [-> ->]%extend_match_of_abstract_tensors_dom_img_strong.
  set_solver.
Qed.




Lemma extend_match_of_abstract_tensors_dom {lbound rbound m labs rabs mres} : 
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  dom mres ⊆ dom m ∪ lbound.
Proof.
  now intros ?%extend_match_of_abstract_tensors_dom_img.
Qed.

Lemma extend_match_of_abstract_tensors_dom' {lbound rbound m labs rabs mres} : 
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  dom m ⊆ lbound ->
  dom mres ⊆ lbound.
Proof.
  intros ?%extend_match_of_abstract_tensors_dom.
  set_solver.
Qed.


Lemma extend_match_of_abstract_tensors_dom_contains {lbound rbound m labs rabs mres} : 
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  dom m ∪ (lbound ∩ abstracts_vars labs) ⊆ dom mres.
Proof.
  now intros [-> _]%extend_match_of_abstract_tensors_dom_img_strong.
Qed.


Lemma extend_match_of_abstract_tensors_subseteq {lbound rbound m labs rabs mres} : 
  dom m ⊆ lbound ->
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  m ⊆ mres.
Proof.
  revert rabs m mres;
  induction labs as [|[[fl lowl] upl] labs IHlabs];
  intros rabs m mres;
  [destruct rabs; [|easy]; now intros ? [= <-]; set_solver|].
  cbn.
  intros Hdom Heq.
  apply head_Some_elem_of in Heq as Hmem.
  apply elem_of_list_bind in Hmem as 
    (([[fr lowr] upr] & rrest) & 
      (m' & Hm_m' & 
      (m'' & Hm'_m'' & Hm'')%bind_Some
      )%elem_of_from_option_list_singleton%bind_Some & 
      (-> & Hdecomp)%elem_of_list_select).
  specialize (fun H => IHlabs _ _ _ H Hm'') as Hsub''.
  specialize (fun H => 
    extend_map_of_abstract_pair_subseteq H Hm_m') as Hsub'.
  specialize (fun H =>
    extend_map_of_abstract_pair_subseteq H Hm'_m'') as Hsub.

  specialize (Hsub' Hdom).
  specialize (extend_map_of_abstract_pair_dom' Hm_m' Hdom) as Hdom'.
  specialize (extend_map_of_abstract_pair_dom' Hm'_m'' Hdom') as Hdom''.
  specialize (extend_match_of_abstract_tensors_dom' Hm'' Hdom'') as Hdom'''.
  now rewrite Hsub', Hsub, Hsub'' by auto.
Qed.

Lemma extend_match_of_abstract_tensors_spec_full {lbound rbound m labs rabs mres} : 
  dom m ⊆ lbound ->
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  forall mext, dom mext ⊆ lbound -> mres ⊆ mext ->
  relabel_abs (gmap_map mext) <$> labs ≡ₚ rabs.
Proof.
  revert rabs m mres;
  induction labs as [|[[fl lowl] upl] labs IHlabs];
  intros rabs m mres;
  [destruct rabs; [|easy]; now intros ? [= <-]; set_solver|].
  cbn.
  intros Hdom Heq.
  apply head_Some_elem_of in Heq as Hmem.
  apply elem_of_list_bind in Hmem as 
    (([[fr lowr] upr] & rrest) & 
      (m' & Hm_m' & 
      (m'' & Hm'_m'' & Hm'')%bind_Some
      )%elem_of_from_option_list_singleton%bind_Some & 
      Hright).
  apply elem_of_list_select_perm in Hright as Hrperm.
  specialize (extend_map_of_abstract_pair_dom' Hm_m' Hdom) as Hdom'.
  specialize (extend_map_of_abstract_pair_dom' Hm'_m'' Hdom') as Hdom''.
  specialize (extend_match_of_abstract_tensors_dom' Hm'' Hdom'') as Hdomres.
  specialize (extend_map_of_abstract_pair_subseteq Hdom Hm_m') as Hsubm_m'.
  specialize (extend_map_of_abstract_pair_subseteq Hdom' Hm'_m'') as Hsubm'_m''.
  specialize (extend_match_of_abstract_tensors_subseteq Hdom'' Hm'') as Hsubm''_res.
  intros mext Hdomext Hsub.


  rewrite Hrperm.
  f_equiv.
  - apply elem_of_list_select in Hright as (-> & _).
    f_equal; [f_equal|].
    + apply (extend_map_of_abstract_pair_spec_full Hdom Hm_m'); [easy|].
      repeat first [solve [eauto] | etransitivity].
    + apply (extend_map_of_abstract_pair_spec_full Hdom' Hm'_m''); [easy|].
      repeat first [solve [eauto] | etransitivity].
  - now apply (IHlabs _ _ _ Hdom'' Hm'').
Qed.

Lemma extend_match_of_abstract_tensors_spec {lbound rbound m labs rabs mres} : 
  dom m ⊆ lbound ->
  extend_match_of_abstract_tensors lbound rbound m labs rabs = Some mres ->
  relabel_abs (gmap_map mres) <$> labs ≡ₚ rabs.
Proof.
  intros Hdom Heq.
  apply (extend_match_of_abstract_tensors_spec_full Hdom Heq); [|reflexivity].
  apply (extend_match_of_abstract_tensors_dom' Heq Hdom).
Qed.


Lemma match_tensorlist_spec_aux_dom {m tl tl'} : 
  match_tensorlist tl tl' = Some m ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl.
Proof.
  intros Heq.
  specialize (extend_match_of_abstract_tensors_dom_img_strong 
    (lbound := tl_bound_varset tl) (m := ∅) Heq).
  intros [-> _].
  set_solver.
Qed.

Lemma match_tensorlist_spec_aux_img {m tl tl'} : 
  match_tensorlist tl tl' = Some m ->
  map_img m = tl_bound_varset tl' ∩ tl_used_varset tl'.
Proof.
  intros Heq.
  specialize (extend_match_of_abstract_tensors_dom_img_strong 
    (lbound := tl_bound_varset tl) (m := ∅) Heq).
  intros [_ ->].
  set_solver.
Qed.

Lemma match_tensorlist_spec_aux_free {tl tl'} : 
  is_Some (match_tensorlist tl tl') ->
  tl_free_varset tl = tl_free_varset tl'.
Proof.
  intros Hfree%extend_match_of_abstract_tensors_is_Some_free.
  apply Hfree.
Qed.


Lemma match_tensorlist_spec_aux_1 {m tl tl'} : 
  match_tensorlist tl tl' = Some m ->
  relabel_abs (gmap_map m) <$> tl.(tl_abstracts) ≡ₚ tl'.(tl_abstracts).
Proof.
  intros Heq.
  apply (extend_match_of_abstract_tensors_spec 
    (lbound := tl_bound_varset tl) (m := ∅) ltac:(set_solver) Heq).
Qed.

Lemma match_tensorlist_spec_aux_2 {m tl tl'} : 
  match_tensorlist tl tl' = Some m ->
  relabel_abs (relabel_bound_Idx (gmap_map m) (tl_bound_varset tl)) <$> 
    tl.(tl_abstracts) ≡ₚ tl'.(tl_abstracts).
Proof.
  intros Heq.
  rewrite <- (match_tensorlist_spec_aux_1 Heq).
  apply (ltac:(now intros ? ? ->) : subrelation eq (≡ₚ)).
  apply list_fmap_ext.
  intros _ [[f low] up] _.
  (* intros _ [[f low] up] Hf%elem_of_list_lookup_2. *)
  apply relabel_abs_ext.
  apply list_fmap_ext.
  intros _ v _.
  (* intros _ v Hv%elem_of_list_lookup_2. *)
  unfold relabel_bound_Idx.
  case_decide as Hvbound; [easy|].
  symmetry.
  apply gmap_map_idemp.
  specialize (extend_match_of_abstract_tensors_dom' Heq ltac:(set_solver)).
  set_solver.
Qed.

Lemma tl_dedup_sums_types tl : 
  (tl_dedup_sums tl).(tl_sums).*1 = tl.(tl_sums).*1.
Proof.
  destruct tl as [sums aux].
  cbn.
  remember (tl_varset _) as frees eqn:Heq.
  clear.
  induction sums as [|[ty var] sums IHsums]; [reflexivity|].
  cbn; congruence.
Qed.

Lemma relabel_one_until_binder_tl_unused tl v v' : 
  v ∉ tl_used_varset tl ->
  relabel_one_until_binder v v' tl = tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  fold (abstracts_vars abs).
  intros Hvars.
  induction sums as [|[ty var] sums IHsums].
  - cbn.
    induction abs; [reflexivity|].
    cbn.
    f_equal; [|apply IHabs; set_solver].
    destruct a as [[f low] up].
    cbn.
    f_equal; 
    (etransitivity; [|apply list_fmap_id]);
    apply list_fmap_ext; intros _ x ?%elem_of_list_lookup_2;
    unfold relabel_var;
    apply decide_False;
    intros ->; apply Hvars; cbn; set_solver.
  - cbn.
    rewrite IHsums.
    now case_decide.
Qed.





Lemma tl_app_sums_eq_fold sums tl :
  tl_app_sums sums tl = fold_right (uncurry tl_cons_sum) tl sums.
Proof.
  induction sums as [|[ty var]]; cbn; congruence. 
Qed.

Lemma tl_app_sums_eq_app sums tl : 
  tl_app_sums sums tl = mk_tl (sums ++ tl.(tl_sums)) (tl.(tl_abstracts)).
Proof.
  destruct tl as [sums' abs].
  induction sums as [|[ty var]]; [reflexivity|]. 
  cbn. 
  rewrite IHsums.
  reflexivity.
Qed.

Lemma mk_tl_app_sums_aux sums sums' abs : 
  mk_tl (sums ++ sums') abs = fold_right (uncurry tl_cons_sum) (mk_tl sums' abs) sums.
Proof.
  induction sums as [|[ty var]]; [reflexivity|].
  cbn.
  rewrite <- IHsums.
  reflexivity.
Qed.


Lemma fold_mk_tl tl :
  mk_tl (tl.(tl_sums)) (tl.(tl_abstracts)) = tl.
Proof. 
  now destruct tl.
Qed.

Lemma tl_used_varset_tl_app_sums sums tl : 
  tl_used_varset (tl_app_sums sums tl) = tl_used_varset tl.
Proof.
  now rewrite tl_app_sums_eq_app.
Qed.




Lemma elem_of_vars_tl_unused_bound_vars tl v : 
  v ∈ (tl_unused_bound_vars tl).*2 <-> v ∈ tl_bound_varset tl ∖ tl_used_varset tl.
Proof.
  unfold tl_unused_bound_vars.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_list_filter.
  rewrite elem_of_difference.
  unfold tl_bound_varset.
  rewrite elem_of_list_to_set, elem_of_list_fmap.
  naive_solver.
Qed.

Lemma elem_of_vars_tl_used_bound_vars tl v : 
  v ∈ (tl_used_bound_vars tl).*2 <-> v ∈ tl_bound_varset tl ∩ tl_used_varset tl.
Proof.
  unfold tl_used_bound_vars.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_list_filter.
  rewrite elem_of_intersection.
  unfold tl_bound_varset.
  rewrite elem_of_list_to_set, elem_of_list_fmap.
  naive_solver.
Qed.


Lemma list_to_set_vars_tl_used_bound_vars tl : 
  list_to_set (tl_used_bound_vars tl).*2 = 
    tl_bound_varset tl ∩ tl_used_varset tl.
Proof.
  apply set_eq; intros v.
  now rewrite elem_of_list_to_set, elem_of_vars_tl_used_bound_vars.
Qed.

Lemma list_to_set_vars_tl_unused_bound_vars tl : 
  list_to_set (tl_unused_bound_vars tl).*2 = 
    tl_bound_varset tl ∖ tl_used_varset tl.
Proof.
  apply set_eq; intros v.
  now rewrite elem_of_list_to_set, elem_of_vars_tl_unused_bound_vars.
Qed.

Lemma tl_sums_used_unused_decomp tl : 
  tl.(tl_sums) ≡ₚ tl_unused_bound_vars tl ++ tl_used_bound_vars tl.
Proof.
  symmetry.
  apply filter_neg_with_Permutation.
Qed.


Lemma tl_app_unused_sums_abstracts tys tl : 
  (tl_app_unused_sums tys tl).(tl_abstracts) = tl.(tl_abstracts).
Proof.
  induction tys; cbn; congruence.
Qed.

Lemma tl_used_varset_tl_app_unused_sums tys tl : 
  tl_used_varset (tl_app_unused_sums tys tl) = tl_used_varset tl.
Proof.
  unfold tl_used_varset; now rewrite tl_app_unused_sums_abstracts.
Qed.

Lemma tl_app_unused_sums_eq_app tys tl : 
  tl_app_unused_sums tys tl = 
  mk_tl (((., fresh (tl_used_varset tl)) <$> tys) ++ tl.(tl_sums)) 
    tl.(tl_abstracts).
Proof.
  induction tys; [now destruct tl|].
  cbn.
  unfold tl_cons_unused_sum.
  rewrite tl_used_varset_tl_app_unused_sums.
  now rewrite IHtys.
Qed.



Lemma tl_free_varset_eq_diff' tl : 
  tl_free_varset tl = tl_used_varset tl ∖ tl_bound_varset tl.
Proof. 
  reflexivity.
Qed.


Lemma tl_free_varset_subseteq_tl_used_varset tl : 
  tl_free_varset tl ⊆ tl_used_varset tl.
Proof.
  rewrite tl_free_varset_eq_diff'; set_solver.
Qed.


Lemma tl_free_varset_tl_used_bound_vars tl : 
  tl_free_varset {|
    tl_sums := tl_used_bound_vars tl; tl_abstracts := tl_abstracts tl
  |} = tl_free_varset tl.
Proof.
  rewrite 2 tl_free_varset_eq_diff'.
  cbn.
  rewrite list_to_set_vars_tl_used_bound_vars.
  fold (abstracts_vars (tl.(tl_abstracts))).
  fold (tl_used_varset tl).
  generalize tl_bound_varset, tl_used_varset; set_solver.
Qed.




Local Notation NoDup_vars tl := (NoDup tl.(tl_sums).*2) (only parsing).





Lemma lookup_tl_type_map_Some tl var ty : 
  NoDup_vars tl ->
  tl_type_map tl !! var = Some ty <->
  (ty, var) ∈ tl.(tl_sums).
Proof.
  intros Hdup.
  unfold tl_type_map.
  rewrite <- elem_of_list_to_map by 
    now rewrite fsts_prod_swap, reverse_Permutation.
  rewrite reverse_Permutation.
  rewrite elem_of_list_fmap.
  rewrite exists_pair.
  cbn.
  naive_solver.
Qed.


Lemma tl_type_map_eq_fold_left tl : 
  tl_type_map tl = 
  fold_left (fun m '(ty, var) => <[var := ty]> m) tl.(tl_sums) (∅ :> gmap Idx Ty).
Proof.
  unfold tl_type_map.
  rewrite list_to_map_eq_fold_right.
  rewrite fmap_reverse.
  remember ∅ as m eqn:Hm.
  clear Hm.
  revert m;
  induction (tl_sums tl) as [|[ty var] sums IHsums]; intros m.
  - reflexivity.
  - rewrite fmap_cons, reverse_cons, foldr_app.
    cbn.
    apply IHsums.
Qed.

Lemma dom_tl_type_map tl : 
  dom (tl_type_map tl) = list_to_set tl.(tl_sums).*2.
Proof.
  unfold tl_type_map.
  rewrite dom_list_to_map_L.
  now rewrite fsts_prod_swap, reverse_Permutation.
Qed.


Lemma tl_type_map_tl_dedup_sums tl : 
  tl_type_map tl ⊆ tl_type_map (tl_dedup_sums tl).
Proof.
  unfold tl_type_map at 1.

  cbn -[rev_append].
  (* remember (tl_varset tl) as vars eqn:Hv.
  remember (tl_sums tl) as sums eqn:Hs. *)
  apply map_subseteq_spec.
  intros var ty.
  rewrite lookup_list_to_map_gen.
  rewrite fmap_reverse, filter_reverse, head_reverse.
  rewrite fmap_Some.
  intros (vty & Hlast & Hty).
  apply last_filter_Some in Hlast as (i & Hi & Hvar & Hmax).
  apply lookup_tl_type_map_Some; [apply tl_dedup_sums_NoDup_vars|].
  apply elem_of_list_lookup.
  exists i.
  apply make_sums_free_spec_lookup_same.
  - set_solver.
  - rewrite list_lookup_fmap in Hi.
    destruct vty as [v' t']; cbn in *; subst v' t'.
    destruct (tl_sums tl !! i) as [[]|] in *; cbn in *; congruence.
  - rewrite not_elem_of_drop_S_iff.
    intros j var' Hij.
    rewrite list_lookup_fmap.
    destruct (tl_sums tl !! j) as [[ty' var'']|] eqn:Hj; [|easy].
    cbn.
    intros [= ->].
    apply (Hmax j (var', ty') Hij).
    now rewrite list_lookup_fmap, Hj.
Qed.


Lemma tl_type_map_tl_dedup_sums_on_varset tl var : 
  var ∈ tl_varset tl -> 
  tl_type_map (tl_dedup_sums tl) !! var = tl_type_map tl !! var.
Proof.
  intros Hvar.
  apply option_eq.
  pose proof (tl_type_map_tl_dedup_sums tl) as Hsubs.
  rewrite map_subseteq_spec in Hsubs.
  intros ty.
  split; [|apply Hsubs]. 
  intros Heq.
  apply lookup_tl_type_map_Some in Heq; [|apply tl_dedup_sums_NoDup_vars].
  apply elem_of_list_lookup_1 in Heq as (i & Hi).
  cbn in Hi.

  specialize (make_sums_free_lookup_spec (tl_varset tl) (tl_sums tl) i).
  setoid_rewrite Hi.
  intros [[Hsums%eq_sym Hnotin]|(ty' & var' & [= <- <-] & Hlook & Hni)].
  - specialize (Hnotin var eq_refl).
    unfold tl_type_map.
    rewrite lookup_list_to_map_gen.
    rewrite fmap_reverse, filter_reverse, head_reverse.
    rewrite fmap_Some.
    exists (var, ty).
    split; [|easy].
    rewrite last_filter_Some.
    rewrite not_elem_of_drop_S_iff in Hnotin.
    exists i.
    split.
    + rewrite list_lookup_fmap.
      now setoid_rewrite Hsums.
    + split; [easy|].
      intros j [var' ty'] Hij Heq. 
      rewrite list_lookup_fmap in Heq.
      specialize (Hnotin _ var' Hij).
      rewrite list_lookup_fmap in Hnotin.
      destruct (tl_sums tl !! j) as [(ty'' & var'')|]; [|easy].
      cbn in *.
      apply Hnotin; congruence.
  - easy.
Qed.


Lemma match_tensorlist_correct_aux_map_NoDup_prod_map tl (m : gmap Idx Idx) : 
  NoDup_vars tl ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl -> 
  size (dom m) = size (map_img m :> gset Idx) ->
  NoDup (prod_map id (gmap_map m) <$> tl_used_bound_vars tl).*2.
Proof.
  intros Hdup Hdom Hinj.
  pose proof Hinj as Hsize.
  rewrite map_dom_img_eq_card_iff_inj in Hinj.
  assert (NoDup (tl_used_bound_vars tl).*2) as Hudup by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup; apply Hdup).
  assert (NoDup (tl_unused_bound_vars tl).*2) as Huudup by 
    (now rewrite tl_sums_used_unused_decomp, 
    fmap_app, NoDup_app in Hdup; apply Hdup).
  rewrite snds_prod_map; apply NoDup_fmap_2_strong; [|easy].
  intros v v'.
  cbn.
  rewrite 2 elem_of_vars_tl_used_bound_vars.
  rewrite <- Hdom.
  intros [mv Hmv]%elem_of_dom [mv' Hmv']%elem_of_dom.
  rewrite (gmap_map_correct _ _ _ Hmv), (gmap_map_correct _ _ _ Hmv').
  intros ->.
  eauto.
Qed.


Lemma match_tensorlist_correct_aux_map_used_bound tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl -> 
  map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' -> 
  size (dom m) = size (map_img m :> gset Idx) ->
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  prod_map id (gmap_map m) <$> tl_used_bound_vars tl
  ≡ₚ tl_used_bound_vars tl'.
Proof.
  intros Hdup Hdup' Hdom Himg Hinj Htypes.
  pose proof Hinj as Hsize.
  rewrite map_dom_img_eq_card_iff_inj in Hinj.
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
  eassert (Hndm : _) by 
  now eapply (match_tensorlist_correct_aux_map_NoDup_prod_map tl m); eauto.
  apply NoDup_Permutation; 
  [now apply NoDup_fmap_1 in Hndm|now apply NoDup_fmap_1 in Hudup'|].
  intros [ty var].
  rewrite elem_of_list_fmap_prod_map.
  cbn.
  hnf in Htypes.
  setoid_rewrite (@option_eq Ty) in Htypes.
  setoid_rewrite lookup_tl_type_map_Some in Htypes; [|easy..].
  split.
  * intros (_ & b & Htyb & -> & Hmap).
    apply (elem_of_list_fmap_1 snd) in Htyb 
      as Hb.
    rewrite elem_of_vars_tl_used_bound_vars in Hb.
    pose proof Hb as Hb'.
    rewrite <- Hdom in Hb'.
    apply elem_of_dom in Hb' as (mb & Hmb).
    cbn in *.
    apply (elem_of_map_img_2 (SA:=gset Idx)) in Hmb as Hmbbd.
    rewrite (gmap_map_correct _ _ _ Hmb) in Hmap.
    subst mb.
    assert (Hvar : var ∈ (tl_used_bound_vars tl').*2) by (
      rewrite elem_of_vars_tl_used_bound_vars; now rewrite Himg in Hmbbd).
    specialize (Htypes _ _ Hmb).
    cbn in Htypes.
    apply elem_of_list_filter in Htyb.
    rewrite Htypes in Htyb.
    apply elem_of_list_filter.
    split; [|easy].
    now rewrite elem_of_vars_tl_used_bound_vars, elem_of_intersection in Hvar.
  * intros Htyvar.
    apply elem_of_list_filter in Htyvar as Htv.
    apply (elem_of_list_fmap_1 snd) in Htyvar
      as Hvar.
    cbn in Hvar.
    rewrite elem_of_vars_tl_used_bound_vars, <- Himg in Hvar.
    apply elem_of_map_img_1 in Hvar as Hb.
    destruct Hb as (b & Hb).
    rewrite <- (Htypes _ _ Hb) in Htv.
    exists ty, b.
    split; [|now rewrite (gmap_map_correct _ _ _ Hb); done].
    apply elem_of_list_filter.
    split; [cbn|easy].
    apply elem_of_dom_2 in Hb.
    now rewrite Hdom, elem_of_intersection in Hb.
Qed.


Lemma elem_of_tl_used_varset tl v : 
  v ∈ tl_used_varset tl <-> 
  exists abs_low_up, 
    v ∈ abs_low_up.1.2 ++ abs_low_up.2 /\
    abs_low_up ∈ tl.(tl_abstracts).
Proof.
  unfold tl_used_varset, abstracts_vars.
  rewrite list_to_set_concat, elem_of_union_list.
  setoid_rewrite elem_of_list_fmap.
  rewrite 2 exists_pair.
  cbn.
  split. 
  - intros (? & (lowup & -> & ([[abs low] up] & -> 
    & Habs)%elem_of_list_fmap) & Hv%elem_of_list_to_set).
    eauto.
  - intros (abs & low & up & Hv & Habs). 
    eexists.
    split; [exists (low ++ up); split; [reflexivity|]|
      now apply elem_of_list_to_set].
    apply elem_of_list_fmap.
    now exists (abs, low, up).
Qed.


Lemma elem_of_tl_used_varset' tl v : 
  v ∈ tl_used_varset tl <-> 
  exists abs low up, 
    v ∈ low ++ up /\
    (abs, low, up) ∈ tl.(tl_abstracts).
Proof.
  rewrite elem_of_tl_used_varset.
  now rewrite 2 exists_pair.
Qed.


Lemma match_tensorlist_correct_aux_map_unused tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl -> 
  map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' -> 
  size (dom m) = size (map_img m :> gset Idx) ->
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  (tl.(tl_sums)).*1 ≡ₚ (tl'.(tl_sums)).*1 ->
  (tl_unused_bound_vars tl).*1 ≡ₚ (tl_unused_bound_vars tl').*1.
Proof.
  intros Hdup Hdup' Hdom Himg Hinj Htypes.
  rewrite 2 tl_sums_used_unused_decomp.
  rewrite 2 fmap_app.
  intros Hperm.
  eapply Permutation_app_inv_r.
  etransitivity; [apply Hperm|].
  f_equiv.
  eassert (Hnd : _) by now
    apply (match_tensorlist_correct_aux_map_used_bound tl tl' m); eauto.
  rewrite <- Hnd.
  now rewrite fsts_prod_map, list_fmap_id.
Qed.

Lemma elements_tl_bound_used_varset tl : 
  NoDup_vars tl ->
  elements (tl_bound_varset tl ∩ tl_used_varset tl) ≡ₚ (tl_used_bound_vars tl).*2.
Proof.
  intros Hdup.
  apply NoDup_Permutation; [apply NoDup_elements| 
  rewrite tl_sums_used_unused_decomp, fmap_app, NoDup_app in Hdup; apply Hdup|].
  intros x.
  now rewrite elem_of_vars_tl_used_bound_vars, elem_of_elements.
Qed.

Lemma elements_tl_bound_unused_varset tl : 
  NoDup_vars tl ->
  elements (tl_bound_varset tl ∖ tl_used_varset tl) ≡ₚ (tl_unused_bound_vars tl).*2.
Proof.
  intros Hdup.
  apply NoDup_Permutation; [apply NoDup_elements| 
  rewrite tl_sums_used_unused_decomp, fmap_app, NoDup_app in Hdup; apply Hdup|].
  intros x.
  now rewrite elem_of_vars_tl_unused_bound_vars, elem_of_elements.
Qed.

Lemma match_tensorlist_correct_aux_map_inj tl tl' (m : gmap Idx Idx) : 
  NoDup_vars tl -> NoDup_vars tl' ->
  dom m = tl_bound_varset tl ∩ tl_used_varset tl -> 
  map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' -> 
  (* map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m ->
  (tl.(tl_sums)).*1 ≡ₚ (tl'.(tl_sums)).*1 -> *)
  length (tl_used_bound_vars tl) = length (tl_used_bound_vars tl') ->
  size (dom m) = size (map_img m :> gset Idx).
Proof.
  intros Hdup Hdup' Hdom Himg Hlen.
  rewrite Hdom, Himg.
  unfold size, set_size.
  cbn.
  rewrite 2 elements_tl_bound_used_varset by easy.
  now rewrite 2 length_fmap.
Qed.


Lemma tl_dedup_sums_used_bound_vars tl : 
  (tl_used_bound_vars (tl_dedup_sums tl)).*2 ≡ 
  (tl_used_bound_vars tl).*2.
Proof.
  rewrite <- (list_to_set_equiv (C:=gset Idx)).
  rewrite 2 list_to_set_vars_tl_used_bound_vars.
  (* rewrite leibniz_equiv_iff. *)
  change (tl_used_varset (tl_dedup_sums tl)) with (tl_used_varset tl).
  apply set_subseteq_antisymm.
  - intros x [Hxbd Hxused]%elem_of_intersection.
    apply elem_of_intersection; split; [|easy].
    apply dec_stable.
    intros Hnin.
    apply (tl_dedup_sums_vars_disj tl x ltac:(set_solver)).
    set_solver.
  - intros x [Hx%tl_dedup_sums_vars_supset ?]%elem_of_intersection.
    now apply elem_of_intersection.
Qed.



Lemma match_tensorlist_correct_aux_dedup tl tl' (m : gmap Idx Idx) : 
  let dtl := (tl_dedup_sums tl) in 
  let dtl' := (tl_dedup_sums tl') in 
  match_tensorlist dtl dtl' = Some m ->
  (* dom m = tl_bound_varset tl ∩ tl_used_varset tl ->  *)
  (* map_img m = tl_bound_varset tl' ∩ tl_used_varset tl' ->  *)
  (* size (dom m) = size (map_img m :> gset Idx) -> *)
  (* tl_free_varset tl = tl_free_varset tl' ->  *)
  dtl.(tl_sums).*1 ≡ₚ dtl'.(tl_sums).*1 ->
  length (tl_used_bound_vars dtl) = length (tl_used_bound_vars dtl') ->
  map_Forall (fun v v' => tl_type_map dtl !! v = tl_type_map dtl' !! v') m <->
  (* (tl_unused_bound_vars tl).*1 ≡ₚ (tl_unused_bound_vars tl').*1 -> *)
  (* relabel_abs (relabel_bound_Idx (gmap_map m) (tl_bound_varset tl)) <$>
	tl_abstracts tl ≡ₚ tl_abstracts tl' -> *)
  map_Forall (fun v v' => tl_type_map tl !! v = tl_type_map tl' !! v') m.
Proof.
  intros dtl dtl' Heq.
  assert (Hdup : NoDup_vars dtl) by now apply tl_dedup_sums_NoDup_vars.
  assert (Hdup' : NoDup_vars dtl') by now apply tl_dedup_sums_NoDup_vars.
  apply mk_is_Some in Heq as Hsome.
  apply match_tensorlist_spec_aux_dom in Heq as Hdom.
  apply match_tensorlist_spec_aux_img in Heq as Himg.
  intros Hperm Hlen.
  split.
  (* apply (match_tensorlist_correct_aux_map_inj dtl dtl' m) in Hlen; [|easy..].
  apply match_tensorlist_spec_aux_free in Hsome as Hfrees.
  apply match_tensorlist_spec_aux_2 in Heq as Hmabs.
  apply (match_tensorlist_correct_aux_map_unused dtl dtl' m) in Hperm; [|easy..]. *)
  - hnf.
    intros Htypes v mv Hmv.
    apply Htypes in Hmv as Hty.
    rewrite <- tl_type_map_tl_dedup_sums_on_varset. 2:{
      apply elem_of_dom_2 in Hmv as Hvdom.
      rewrite Hdom in Hvdom.
      rewrite <- elem_of_vars_tl_used_bound_vars in Hvdom.
      rewrite (unfold dtl), tl_dedup_sums_used_bound_vars, 
        elem_of_vars_tl_used_bound_vars in Hvdom.
      apply tl_bound_varset_subseteq.
      now apply elem_of_intersection in Hvdom.
    }
    rewrite <- (tl_type_map_tl_dedup_sums_on_varset tl'). 2:{
      apply (elem_of_map_img_2 (SA:=gset Idx)) in Hmv as Hmvimg.
      rewrite Himg in Hmvimg.
      rewrite <- elem_of_vars_tl_used_bound_vars in Hmvimg.
      rewrite (unfold dtl'), tl_dedup_sums_used_bound_vars, 
        elem_of_vars_tl_used_bound_vars in Hmvimg.
      apply tl_bound_varset_subseteq.
      now apply elem_of_intersection in Hmvimg.
    }
    apply Hty.
  - hnf.
    intros Htypes v mv Hmv.
    apply Htypes in Hmv as Hty.
    rewrite <- tl_type_map_tl_dedup_sums_on_varset in Hty. 2:{
      apply elem_of_dom_2 in Hmv as Hvdom.
      rewrite Hdom in Hvdom.
      rewrite <- elem_of_vars_tl_used_bound_vars in Hvdom.
      rewrite (unfold dtl), tl_dedup_sums_used_bound_vars, 
        elem_of_vars_tl_used_bound_vars in Hvdom.
      apply tl_bound_varset_subseteq.
      now apply elem_of_intersection in Hvdom.
    }
    rewrite <- (tl_type_map_tl_dedup_sums_on_varset tl') in Hty. 2:{
      apply (elem_of_map_img_2 (SA:=gset Idx)) in Hmv as Hmvimg.
      rewrite Himg in Hmvimg.
      rewrite <- elem_of_vars_tl_used_bound_vars in Hmvimg.
      rewrite (unfold dtl'), tl_dedup_sums_used_bound_vars, 
        elem_of_vars_tl_used_bound_vars in Hmvimg.
      apply tl_bound_varset_subseteq.
      now apply elem_of_intersection in Hmvimg.
    }
    apply Hty.
Qed.




Lemma make_sums_free'_spec avoid sums : 
  list_to_set sums.*2 ⊆ avoid ->
  make_sums_free' avoid sums = (make_sums_free avoid sums,
  list_to_set (make_sums_free avoid sums).*2).
Proof.
  intros Hav.
  induction sums as [|[ty var] sums IHsums]; [reflexivity|].
  specialize (IHsums ltac:(rewrite <- Hav; apply union_subseteq_r)).
  cbn.
  rewrite IHsums.
  reflexivity.
Qed.

Lemma tl_dedup_sums'_correct tl : 
  tl_dedup_sums' tl = tl_dedup_sums tl.
Proof.
  unfold tl_dedup_sums'.
  rewrite make_sums_free'_spec by set_solver.
  reflexivity.
Qed.

Lemma tl_used_varset_subseteq tl : tl_used_varset tl ⊆ tl_varset tl.
Proof. 
  set_solver. 
Qed.

Lemma elem_of_vars_make_sums_free_varset_bound avoid sums var : 
  var ∈ avoid -> 
  var ∈@{gset Idx} list_to_set (make_sums_free avoid sums).*2 <->
  var ∈ sums.*2.
Proof.
  intros Hvarav.
  split.
  - intros Hmakefree.
    apply dec_stable.
    intros Hnin.
    apply (make_sums_free_diff_free avoid sums var ltac:(set_solver) Hvarav).
  - intros Hsums.
    now apply make_sums_free_supseteq, elem_of_list_to_set.
Qed.

Lemma fresh_var_fresh_subseteq avoid avoid' var : 
  avoid ⊆ avoid' -> 
  fresh_var var avoid' ∉ avoid.
Proof.
  apply not_elem_of_weaken, fresh_var_fresh.
Qed.




Lemma canonify_tl_aux_spec sums abs : 
  canonify_tl_aux sums abs = 
  (tl_used_bound_vars (tl_dedup_sums (mk_tl sums abs)),
   (tl_unused_bound_vars (tl_dedup_sums (mk_tl sums abs))).*1,
   tl_free_varset (mk_tl sums abs)).
Proof.
  cbn -[abstracts_vars].
  change (tl_used_varset (tl_dedup_sums ?x)) with (tl_used_varset x).
  unfold tl_free_varset.
  remember (tl_varset _) as avoid eqn:Hav_eq.
  assert (Havoid : tl_varset (mk_tl sums abs) ⊆ avoid) by now apply eq_reflexivity.
  clear Hav_eq.
  unfold tl_varset in Havoid.
  cbn [ tl_abstracts tl_sums ] in *.
  change (tl_used_varset _) with (abstracts_vars abs).
  induction sums as [|[ty var] sums IHsums].
  - cbn.
    now rewrite difference_empty_L.
  - cbn [canonify_tl_aux].
    rewrite IHsums by (set_solver +Havoid). 
    clear IHsums.
    rewrite <- decide_bool_decide.
    case_decide as Hvar.
    + (* used *)
      f_equal; [|set_solver +].
      cbn [make_sums_free].
      apply elem_of_difference in Hvar as [Hvarabs Hvarnin].
      rewrite decide_False. 2:{
        intros HF.
        rewrite elem_of_vars_make_sums_free_varset_bound in HF by 
          now apply Havoid, union_subseteq_l, Hvarabs.
        now rewrite elem_of_list_to_set in Hvarnin.
      }
      f_equal.
      * (* relevant *)
        rewrite filter_cons.
        rewrite decide_True by exact Hvarabs.
        reflexivity.
      * (* not irrelevant *)
        cbn -[ tl_used_varset].
        rewrite decide_False by (intros HF; exact (HF Hvarabs)).
        reflexivity.
    + (* unused *)
      f_equal; [|set_solver +Hvar].
      cbn [make_sums_free].
      apply not_elem_of_difference in Hvar as Hvar'.
      rewrite (decide_ext _ (var ∈ sums.*2)) by 
        now apply elem_of_vars_make_sums_free_varset_bound, Havoid;
          set_solver +.
      rewrite elem_of_list_to_set in Hvar'.
      case_decide as Hvar_overr.
      * (* sum is later overriden *)
        cbn. 
        rewrite decide_False by 
          now apply fresh_var_fresh_subseteq; set_solver +Havoid.
        rewrite decide_True by 
          now apply fresh_var_fresh_subseteq; set_solver +Havoid.
        reflexivity.
      * (* sum is unused *)
        destruct Hvar' as [Hvar_nabs |]; [|easy].
        cbn.
        rewrite decide_False by done.
        rewrite decide_True by done.
        reflexivity.
Qed.


Lemma canonify_tl_aux'''_spec sums abs : 
  canonify_tl_aux''' sums 
  (list_to_set $ strings.string_to_pos <$> elements (abstracts_vars abs)) = 
  (tl_used_bound_vars (tl_dedup_sums (mk_tl sums abs)),
   (tl_unused_bound_vars (tl_dedup_sums (mk_tl sums abs))).*1,
   list_to_set $ strings.string_to_pos <$> elements 
    (tl_free_varset (mk_tl sums abs))).
Proof.
  cbn -[abstracts_vars].
  change (tl_used_varset (tl_dedup_sums ?x)) with (tl_used_varset x).
  unfold tl_free_varset.
  remember (tl_varset _) as avoid eqn:Hav_eq.
  assert (Havoid : tl_varset (mk_tl sums abs) ⊆ avoid) by now apply eq_reflexivity.
  clear Hav_eq.
  unfold tl_varset in Havoid.
  cbn [ tl_abstracts tl_sums ] in *.
  change (tl_used_varset _) with (abstracts_vars abs).
  induction sums as [|[ty var] sums IHsums].
  - cbn.
    now rewrite difference_empty_L.
  - cbn [canonify_tl_aux'''].
    rewrite IHsums by (set_solver +Havoid). 
    clear IHsums.
    rewrite <- decide_bool_decide.
    rewrite (decide_ext _ (var ∈ abstracts_vars abs ∖ list_to_set sums.*2)).
    2:{
      rewrite elem_of_list_to_set.
      rewrite elem_of_list_fmap_inj by apply _.
      apply elem_of_elements.
    }
    case_decide as Hvar.
    + (* used *)
      f_equal.
      2:{
        apply set_eq.
        intros p.
        rewrite elem_of_difference, 2 elem_of_list_to_set, 2 elem_of_list_fmap.
        setoid_rewrite elem_of_elements.
        cbn.
        rewrite not_elem_of_singleton.
        setoid_rewrite elem_of_difference.
        setoid_rewrite not_elem_of_union.
        setoid_rewrite not_elem_of_singleton.
        split; [naive_solver|].
        intros (y & -> & Hyabs & Hynv & Hysums).
        split; [by eauto|].
        assert (Hs2p : Inj (=) (=) strings.string_to_pos) 
          by refine (@encode_inj string _ _).
        now intros ?%(inj strings.string_to_pos).
      }
      cbn [make_sums_free].
      apply elem_of_difference in Hvar as [Hvarabs Hvarnin].
      rewrite decide_False. 2:{
        intros HF.
        rewrite elem_of_vars_make_sums_free_varset_bound in HF by 
          now apply Havoid, union_subseteq_l, Hvarabs.
        now rewrite elem_of_list_to_set in Hvarnin.
      }
      f_equal.
      * (* relevant *)
        rewrite filter_cons.
        rewrite decide_True by exact Hvarabs.
        reflexivity.
      * (* not irrelevant *)
        cbn -[ tl_used_varset].
        rewrite decide_False by (intros HF; exact (HF Hvarabs)).
        reflexivity.
    + (* unused *)
      f_equal; [|set_solver +Hvar].
      cbn [make_sums_free].
      apply not_elem_of_difference in Hvar as Hvar'.
      rewrite (decide_ext _ (var ∈ sums.*2)) by 
        now apply elem_of_vars_make_sums_free_varset_bound, Havoid;
          set_solver +.
      rewrite elem_of_list_to_set in Hvar'.
      case_decide as Hvar_overr.
      * (* sum is later overriden *)
        cbn. 
        rewrite decide_False by 
          now apply fresh_var_fresh_subseteq; set_solver +Havoid.
        rewrite decide_True by 
          now apply fresh_var_fresh_subseteq; set_solver +Havoid.
        reflexivity.
      * (* sum is unused *)
        destruct Hvar' as [Hvar_nabs |]; [|easy].
        cbn.
        rewrite decide_False by done.
        rewrite decide_True by done.
        reflexivity.
Qed.


Lemma canonify_tl_aux''_spec' sums abs : 
  canonify_tl_aux'' sums abs =
  canonify_tl_aux''' sums
  (list_to_set $ strings.string_to_pos <$> elements (abstracts_vars abs)).
Proof.
  induction sums.
  - cbn.
    f_equal.
    apply set_eq.
    intros x.
    rewrite 2 elem_of_list_to_set.
    rewrite 2 elem_of_list_fmap.
    unfold encode; cbn.
    apply exists_iff; intros y.
    f_equiv.
    rewrite elem_of_list_bind, elem_of_elements.
    unfold abstracts_vars.
    rewrite list_to_set_concat.
    rewrite elem_of_union_list.
    do 2 setoid_rewrite elem_of_list_fmap.
    do 2 setoid_rewrite exists_pair.
    split; [|naive_solver subst; set_solver].
    intros (idx & low & up & Hy & Habs).
    eexists.
    split; [exists (low ++ up); split; first by done
      |by apply elem_of_list_to_set].
    eauto.
  - cbn.
    rewrite IHsums.
    reflexivity.
Qed.

Lemma canonify_tl_aux''_spec sums abs : 
  canonify_tl_aux'' sums abs =
  (tl_used_bound_vars (tl_dedup_sums (mk_tl sums abs)),
   (tl_unused_bound_vars (tl_dedup_sums (mk_tl sums abs))).*1,
   gset_to_Pset 
    (tl_free_varset (mk_tl sums abs))).
Proof.
  rewrite canonify_tl_aux''_spec', canonify_tl_aux'''_spec.
  reflexivity.
Qed.


Lemma extend_map_of_abstract_pair_indep {lbound rbound lbound' rbound' m l r} : 
  lbound ∩ list_to_set l = lbound' ∩ list_to_set l ->
  rbound ∩ list_to_set r = rbound' ∩ list_to_set r ->
  extend_map_of_abstract_pair lbound rbound m l r = 
  extend_map_of_abstract_pair lbound' rbound' m l r.
Proof.
  revert r m;
  induction l as [|hl l IHl];
  intros r m;
  destruct r as [|hr r]; 
  [reflexivity..|].
  cbn.
  intros Hlbound Hrbound.
  rewrite (decide_ext (hl ∉ lbound') (hl ∉ lbound)) by set_solver +Hlbound.
  case_decide as Hlfree.
  - rewrite (decide_ext _ (hl = hr /\ hr ∉ rbound')) by set_solver +Hrbound.
    case_decide as Heq; [destruct_and!; subst | easy].
    apply IHl; [set_solver +Hlbound|set_solver +Hrbound].
  - rewrite (decide_ext (hr ∉ rbound') (hr ∉ rbound)) by set_solver +Hrbound.
    case_decide as Hhrbound; [easy|].
    case_match eqn:Hmhl.
    + case_decide as Heq; [|easy].
      apply IHl; [set_solver +Hlbound|set_solver +Hrbound].
    + apply IHl; [set_solver +Hlbound|set_solver +Hrbound].
Qed.


Lemma extend_match_of_abstract_tensors_indep 
  {lbound rbound lbound' rbound' m labs rabs} : 
  lbound ∩ abstracts_vars labs = lbound' ∩ abstracts_vars labs ->
  rbound ∩ abstracts_vars rabs = rbound' ∩ abstracts_vars rabs ->
  extend_match_of_abstract_tensors lbound rbound m labs rabs = 
  extend_match_of_abstract_tensors lbound' rbound' m labs rabs.
Proof.
  revert rabs m;
  induction labs as [|[[absl lowl] upl] labs IHlabs];
  intros rabs m;
  [reflexivity|].
  intros Hlbound Hrbound.
  cbn [extend_match_of_abstract_tensors].
  f_equal.
  apply list_bind_ext_strong.
  intros ([[absr lowr] upr] & rrest) Helem.
  apply elem_of_list_select_perm in Helem as Hperm.
  f_equal.
  erewrite extend_map_of_abstract_pair_indep; [apply option_bind_ext; [|reflexivity]|..];
  [|revert Hlbound; apply caps_eq_r_weaken_L|revert Hrbound; apply caps_eq_r_weaken_L].
  2: {
    cbn.
    rewrite 2 list_to_set_app.
    apply union_subseteq_l', union_subseteq_l.
  }
  2: {
    rewrite Hperm.
    cbn.
    rewrite 2 list_to_set_app.
    apply union_subseteq_l', union_subseteq_l.
  }
  intros m'.
  apply option_bind_ext.
  2: {
    apply extend_map_of_abstract_pair_indep;
    [revert Hlbound|revert Hrbound]; apply caps_eq_r_weaken_L;
    [|rewrite Hperm];
    cbn;
    rewrite 2 list_to_set_app;
    apply union_subseteq_l', union_subseteq_r.
  }
  intros m''.
  apply IHlabs;
  [revert Hlbound|revert Hrbound]; apply caps_eq_r_weaken_L;
  [|rewrite Hperm];
  cbn;
  rewrite 2 list_to_set_app;
  apply union_subseteq_r.
Qed.


Lemma list_to_set_tl_dedup_sums_used_bound_vars tl : 
  list_to_set (tl_used_bound_vars (tl_dedup_sums tl)).*2 =@{gset Idx}
  list_to_set (tl_used_bound_vars tl).*2.
Proof.
  unfold_leibniz.
  apply list_to_set_equiv.
  apply tl_dedup_sums_used_bound_vars.
Qed.


Lemma tl_type_map_tl_used_bound_vars_on_used tl v : 
  v ∈ tl_used_varset tl -> 
  tl_type_map (mk_tl (tl_used_bound_vars tl) (tl.(tl_abstracts))) !! v = 
  tl_type_map tl !! v.
Proof.
  intros Hv.
  unfold tl_type_map.
  cbn -[reverse].
  rewrite 2 lookup_list_to_map_gen.
  unfold tl_used_bound_vars.
  rewrite <- filter_reverse.
  rewrite (list_fmap_filter_inv _ prod_swap).
  unfold compose. 
  unfold prod_swap at 1.
  cbn [snd].
  rewrite list_filter_filter.
  do 2 f_equal.
  rewrite 2 list_filter_fmap.
  f_equal.
  unfold compose, prod_swap.
  cbn.
  apply list_filter_iff.
  intros [ty var].
  naive_solver.
Qed.





Lemma tensorlist_eqb_spec_aux_1 tl tl' :
  tensorlist_eqb tl tl' <->
  (tl_sums tl).*1 ≡ₚ (tl_sums tl').*1 /\
  length (tl_unused_bound_vars (tl_dedup_sums tl)) = 
    length (tl_unused_bound_vars (tl_dedup_sums tl')) /\
  is_Some (m ← match_tensorlist (tl_dedup_sums tl) (tl_dedup_sums tl');
    _ ← guard (map_Forall (fun v v' => 
      tl_type_map (tl_dedup_sums tl) !! v = 
      tl_type_map (tl_dedup_sums tl') !! v') m);
    Some ()).
Proof.
  unfold tensorlist_eqb.
  destruct tl as [sums abs], tl' as [sums' abs'].
  cbn [ tl_sums ].
  rewrite <- andb_lazy_alt.
  rewrite andb_True.
  rewrite bool_decide_spec.
  f_equiv.
  rewrite 2 canonify_tl_aux''_spec.

  rewrite <- andb_lazy_alt, andb_True, bool_decide_spec.
  rewrite 2 length_fmap.
  f_equiv.
  replace (match_tensorlist _ _) with 
    (match_tensorlist (tl_dedup_sums (mk_tl sums abs)) 
      (tl_dedup_sums (mk_tl sums' abs'))).
  2: {
    apply extend_match_of_abstract_tensors_indep.
    - transitivity (list_to_set (tl_used_bound_vars (tl_dedup_sums (mk_tl sums abs))).*2 :> gset Idx).
      + rewrite list_to_set_vars_tl_used_bound_vars.
        reflexivity.
      + rewrite list_to_set_tl_dedup_sums_used_bound_vars.
        unfold tl_bound_varset.
        cbn [ tl_sums ].
        rewrite list_to_set_tl_dedup_sums_used_bound_vars.
        rewrite list_to_set_vars_tl_used_bound_vars.
        unfold tl_used_varset.
        cbn -[abstracts_vars tl_type_map tl_used_bound_vars].
        now rewrite <- intersection_assoc_L, intersection_idemp_L.
    - transitivity (list_to_set 
      (tl_used_bound_vars (tl_dedup_sums (mk_tl sums' abs'))).*2 :> gset Idx).
      + rewrite list_to_set_vars_tl_used_bound_vars.
        reflexivity.
      + rewrite list_to_set_tl_dedup_sums_used_bound_vars.
        unfold tl_bound_varset.
        cbn [ tl_sums ].
        rewrite list_to_set_tl_dedup_sums_used_bound_vars.
        rewrite list_to_set_vars_tl_used_bound_vars.
        unfold tl_used_varset.
        cbn -[abstracts_vars tl_type_map tl_used_bound_vars].
        now rewrite <- intersection_assoc_L, intersection_idemp_L.
  } 
  case_match eqn:Hm; [|cbn; by split; [|intros ?%is_Some_None]].
  cbn -[abstracts_vars tl_type_map tl_used_bound_vars].
  rewrite bool_decide_spec.
  rewrite guard_is_Some.
  unfold map_Forall.
  apply match_tensorlist_spec_aux_dom in Hm as Hdom.
  rewrite <- list_to_set_vars_tl_used_bound_vars, 
    list_to_set_tl_dedup_sums_used_bound_vars,
    list_to_set_vars_tl_used_bound_vars in Hdom.
  apply match_tensorlist_spec_aux_img in Hm as Himg.
  rewrite <- list_to_set_vars_tl_used_bound_vars, 
    list_to_set_tl_dedup_sums_used_bound_vars,
    list_to_set_vars_tl_used_bound_vars in Himg.
  apply forall_iff; intros v.
  apply forall_iff; intros gv.
  apply forall_iff; intros Hvgv.
  apply elem_of_dom_2 in Hvgv as Hv.
  apply (elem_of_map_img_2 (SA:=gset Idx)) in Hvgv as Hgv.
  rewrite Hdom in Hv.
  rewrite Himg in Hgv.
  rewrite (tl_type_map_tl_used_bound_vars_on_used 
    (tl_dedup_sums (mk_tl sums abs))) by set_solver +Hv.
  rewrite (tl_type_map_tl_used_bound_vars_on_used 
    (tl_dedup_sums (mk_tl sums' abs'))) by set_solver +Hgv.
  reflexivity.
Qed.

End TensorExpr.

Notation NoDup_vars tl := (NoDup tl.(tl_sums).*2) (only parsing).


Module TensorExprNotations.

Import StringCustomNotation.

Declare Custom Entry tensorexpr.

Declare Custom Entry tensorexpr_args.

Notation "'(' x , .. , y ')'" :=
  (@cons Idx x .. (@cons Idx y nil) ..)
  (in custom tensorexpr_args at level 0, 
    x custom string at level 0,
    y custom string at level 0).

Notation "'(' ')'" :=
  (@nil Idx)
  (in custom tensorexpr_args at level 0, only parsing).


Notation "'()'" :=
  (@nil Idx)
  (in custom tensorexpr_args at level 0).


(* Notation "'(' x , .. , y ') " :=
  (@cons Idx x .. (@cons Idx y nil) ..)
  (in custom tensorexpr_args at level 0,
  x constr, y constr, only printing). *)

Notation "f lower upper" :=
  (tabstract f lower upper)
  (in custom tensorexpr at level 10, 
    f custom string at level 0,
    lower custom tensorexpr_args at level 0,
    upper custom tensorexpr_args at level 0).
(* 
Notation "f @ lower upper" :=
  (tabstract f lower upper)
  (in custom tensorexpr at level 10, 
    f constr,
    lower custom tensorexpr_args at level 0,
    upper custom tensorexpr_args at level 0, only printing). *)

Notation "'(' te ')'" := 
    (te) (in custom tensorexpr at level 0, 
    te custom tensorexpr at level 200).

Notation "l * r" :=
  (tproduct l r) 
  (in custom tensorexpr at level 50, left associativity).

Declare Custom Entry tensorexpr_sum.

Notation "∑' smd" :=
  (smd) 
  (in custom tensorexpr at level 60, 
    smd custom tensorexpr_sum at level 60).

Notation "var : 'V' ty , smd" :=
  (tsum var ty smd) 
  (in custom tensorexpr_sum at level 60, 
    var custom string at level 0,
    ty constr,
    smd custom tensorexpr_sum at level 60,
    right associativity).

Notation "∑ var : 'V' ty , smd" :=
  (tsum var ty smd) 
  (in custom tensorexpr at level 60, 
    var custom string at level 0,
    ty constr,
    smd custom tensorexpr at level 60,
    right associativity).

Notation "var : 'V' ty ; smd" :=
  (tsum var ty smd) 
  (in custom tensorexpr_sum at level 60, 
    var custom string at level 0,
    ty constr,
    smd custom tensorexpr at level 60,
    right associativity).

Notation "1" := tone 
  (in custom tensorexpr at level 0).

Notation "'[te'  x  ']'" := x 
  (x custom tensorexpr at level 200, at level 0).


Declare Custom Entry tensorlist.

Declare Custom Entry tensorlist_summand.

Notation "var  :  'V'  ty" :=
  ((ty, var))
  (in custom tensorlist_summand at level 10,
    ty constr at level 0,
    var custom string at level 0).


Declare Custom Entry tensorlist_abstracts.
Declare Custom Entry tensorlist_abstract.


Notation "f  lower  upper" :=
  (f, lower, upper)
  (in custom tensorlist_abstract at level 10, 
    f custom string at level 0,
    lower custom tensorexpr_args at level 0,
    upper custom tensorexpr_args at level 0).

Notation "x  *  ..  *  y" :=
  (cons x .. (cons y nil) ..)
  (in custom tensorlist_abstracts at level 50, 
    x custom tensorlist_abstract at level 10,
    y custom tensorlist_abstract at level 10).

Notation "1" :=
  (nil)
  (in custom tensorlist_abstracts at level 0).


Notation "∑  x ,  .. ,  y ;  abs" :=
  (mk_tl (cons x .. (cons y nil) ..) abs)
  (in custom tensorlist at level 0,
    x custom tensorlist_summand,
    y custom tensorlist_summand,
    abs custom tensorlist_abstracts).

Notation "'[tl' x ']'" := x 
  (x custom tensorlist at level 200, at level 0,
  format "[tl  x  ]").


End TensorExprNotations.