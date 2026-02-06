Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp Aux_pos.

#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.

(* FIXME: Move *)

Definition make_vecs_map {A n m} (ins : vec positive n) (outs : vec positive m)
  (insv : vec A n) (outsv : vec A m) : Pmap A :=
  list_to_map (vzip ins insv) ∪ list_to_map (vzip outs outsv).

(* Section TensorExprDB.  *)

Notation Idx := positive (only parsing).

Local Open Scope positive_scope.
Local Open Scope list_scope.

(* The type of variables in an expression *)
Inductive var :=
  | bound : Idx -> var (* A DeBruijn-indexed bound variable, which is summed over *)
  | free : Idx -> var. (* A free variable, usually an input or output of the diagram *)

#[export] Instance bound_inj : Inj eq eq bound.
Proof. congruence. Qed.

#[export] Instance free_inj : Inj eq eq free.
Proof. congruence. Qed.


#[export] Instance var_dec : EqDecision var. refine
  (fun v v' =>
  match v, v' with
  | bound r, bound r' =>
    match Pos.eq_dec r r' with
    | left Heq => left (f_equal bound Heq)
    | right Hneq => right (fun Heq => Hneq (bound_inj _ _ Heq))
    end
  | free l, free l' =>
    match Pos.eq_dec l l' with
    | left Heq => left (f_equal free Heq)
    | right Hneq => right (fun Heq => Hneq (free_inj _ _ Heq))
    end
  | _, _ => right _
  end); abstract congruence.
Defined.

#[export] Instance var_countable : Countable var := {
  encode v := match v with
    | bound r => r~0
    | free l => l~1
    end%positive;
  decode p := match p with
    | r~0 => Some (bound r)
    | l~1 => Some (free l)
    | 1 => None
    end%positive;
  decode_encode v :=
    match v with | bound p | free p => eq_refl end
}.

Definition v2bound (v : var) : option Idx :=
  match v with
  | bound r => Some r
  | _ => None
  end.

Definition v2free (v : var) : option Idx :=
  match v with
  | free l => Some l
  | _ => None
  end.

Definition var_map (fr fl : Idx -> Idx) : var -> var :=
  fun v => match v with
  | bound r => bound (fr r)
  | free l => free (fl l)
  end.

Lemma var_map_decomp fr fl v :
  var_map fr fl v = default v (((bound ∘ fr) <$> v2bound v) ∪
    ((free ∘ fl) <$> v2free v)).
Proof.
  now destruct v.
Qed.

Add Parametric Morphism : var_map with signature
  (pointwise_relation Idx eq) ==> (pointwise_relation Idx eq) ==>
  (pointwise_relation var eq) as var_map_mor.
Proof.
  intros fr fr' Hfr fl fl' Hfl [];
  cbn; f_equal; auto.
Qed.

Definition var_elim {A : Type} (fr fl : Idx -> A) : var -> A :=
  fun v => match v with
  | bound r => fr r
  | free l => fl l
  end.


Inductive tensorexpr :=
  | tone : tensorexpr (* The element 1 *)
  | tdelta1 (l u : var) (* The delta-tensor, equal to 1 if [l = u] and 0 otherwise*)
  | tabstract (absidx : Idx) (lower : list var) (upper : list var)
    (* An abstract tensor, indexed by [absidx], with arguments
      [lower] and [upper] *)
  | tproduct (l r : tensorexpr) (* The binary product of [tensorexpr]s *)
  | tsum (summand : tensorexpr).

Definition tabstract' (abs : Idx * list var * list var) : tensorexpr :=
  let '(abs, lower, upper) := abs in tabstract abs lower upper.

Definition tdelta1' (lu : var * var) : tensorexpr :=
  let '(l, u) := lu in tdelta1 l u.

Fixpoint tproducts (tes : list tensorexpr) : tensorexpr :=
  match tes with
  | [] => tone
  (* | [te] => te *)
  | te :: tes => tproduct te (tproducts tes)
  end.

Fixpoint tdelta (idxs : list (var * var)) : tensorexpr :=
  match idxs with
  | [] => tone
  | (l, u) :: idxs => tproduct (tdelta1 l u) (tdelta idxs)
  end.

Definition addbound (shift : N) (v : var) : var :=
  match v with
  | bound r => bound (pos_add_N r shift)
  | _ => v
  end.

Definition withboundshift (shift : N) (f : var -> var) (v : var) : var :=
  match v with
  | bound r => if decide (Npos r <= shift)%N then bound r else
      addbound shift (f (bound (pos_sub_N r shift)))
  | _ => addbound shift (f v)
  end.

Add Parametric Morphism : withboundshift with signature
  eq ==> pointwise_relation var eq ==> pointwise_relation var eq
  as withboundshift_ext.
Proof.
  intros s f f' Hf []; [|cbn; f_equal; apply Hf..].
  cbn.
  case_decide; [reflexivity|].
  f_equal; apply Hf.
Qed.

Lemma addbound_add s s' v :
  addbound s (addbound s' v) = addbound (s + s') v.
Proof.
  destruct v; cbn; f_equal.
  lia.
Qed.

Lemma withboundshift_add s s' f v :
  withboundshift s (withboundshift s' f) v = withboundshift (s + s') f v.
Proof.
  destruct v; [|cbn; apply addbound_add..].
  cbn.
  repeat case_decide; lia || fast_reflexivity || cbn.
  - f_equal; destruct s; cbn; try lia.
  - now rewrite addbound_add, pos_sub_N_add.
Qed.

Fixpoint relabel_te_aux (shift : N) (f : var -> var) (te : tensorexpr) : tensorexpr :=
  match te with
  | tone => tone
  | tdelta1 l u => tdelta1 (withboundshift shift f l) (withboundshift shift f u)
  | tabstract absidx lower upper =>
    tabstract absidx (withboundshift shift f <$> lower)
      (withboundshift shift f <$> upper)
  | tproduct l r => tproduct (relabel_te_aux shift f l) (relabel_te_aux shift f r)
  | tsum summand =>
    tsum (relabel_te_aux (N.succ shift) f summand)
  end.

Add Parametric Morphism s : (relabel_te_aux s) with signature
  pointwise_relation var eq ==> eq ==> eq as relabel_te_aux_ext.
Proof.
  intros f f' Hf te.
  revert s.
  induction te; intros s.
  - reflexivity.
  - cbn.
    f_equal; now apply withboundshift_ext.
  - cbn.
    f_equal; apply list_fmap_ext;
    intros _ ? _; now apply withboundshift_ext.
  - cbn.
    f_equal; auto.
  - cbn.
    f_equal; auto.
Qed.

Definition relabel_te (f : var -> var) (te : tensorexpr) : tensorexpr :=
  relabel_te_aux 0 f te.

Fixpoint relabel_te_alt (f : var -> var) (te : tensorexpr) : tensorexpr :=
  match te with
  | tone => tone
  | tdelta1 l u => tdelta1 (f l) (f u)
  | tabstract absidx lower upper =>
    tabstract absidx (f <$> lower) (f <$> upper)
  | tproduct l r => tproduct (relabel_te_alt f l) (relabel_te_alt f r)
  | tsum summand =>
    tsum (relabel_te_alt (withboundshift 1 f) summand)
  end.


Add Parametric Morphism : relabel_te_alt with signature
  pointwise_relation var eq ==> eq ==> eq as relabel_te_alt_ext.
Proof.
  intros f f' Hf te.
  revert f f' Hf;
  induction te; intros f f' Hf.
  - reflexivity.
  - cbn; f_equal; apply Hf.
  - cbn.
    f_equal; apply list_fmap_ext;
    intros _ ? _; now apply Hf.
  - cbn.
    f_equal; auto.
  - cbn.
    f_equal.
    apply IHte.
    now apply withboundshift_ext.
Qed.

Lemma relabel_te_alt_correct_aux shift f te :
  relabel_te_alt (withboundshift shift f) te =
  relabel_te_aux shift f te.
Proof.
  revert shift f; induction te; intros shift f.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn.
    f_equal; auto.
  - cbn.
    rewrite <- IHte.
    f_equal.
    apply relabel_te_alt_ext; [|easy].
    intros v.
    rewrite withboundshift_add.
    apply withboundshift_ext; easy + lia.
Qed.




Fixpoint te_varset (te : tensorexpr) : gset var :=
  match te with
  | tone => ∅
  | tdelta1 l u => {[l; u]}
  | tabstract _ lower upper => list_to_set (lower ++ upper)
  | tproduct l r => te_varset l ∪ te_varset r
  | tsum summand =>
    te_varset summand
  end.

(* FIXME: Move *)
(* The predicate determining that a [tensorexpr] is well-typed
  _only with respect to bound [bound] variables_ *)
Fixpoint te_wellbound_aux (bnd : Idx) (te : tensorexpr) : bool :=
  match te with
  | tone => true
  | tdelta1 l u =>
    bool_decide (Forall (λ p, p < bnd) (omap v2bound [l;u]))
  | tabstract _ low up =>
    bool_decide (Forall (λ p, p < bnd) (omap v2bound (low ++ up)))
  | tproduct l r => te_wellbound_aux bnd l && te_wellbound_aux bnd r
  | tsum smd =>
    te_wellbound_aux (Pos.succ bnd) smd
  end.

Definition te_wellbound (te : tensorexpr) : bool :=
  te_wellbound_aux 1 te.


Fixpoint te_bound_varset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tdelta1 l u => list_to_set (omap v2bound [l;u])
  | tabstract _ lower upper => list_to_set (omap v2bound (lower ++ upper))
  | tproduct l r => te_bound_varset l ∪ te_bound_varset r
  | tsum smd =>
    te_bound_varset smd
  end.

Fixpoint te_free_varset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tdelta1 l u => list_to_set (omap v2free [l;u])
  | tabstract _ lower upper => list_to_set (omap v2free (lower ++ upper))
  | tproduct l r => te_free_varset l ∪ te_free_varset r
  | tsum smd =>
    te_free_varset smd
  end.


Fixpoint te_absset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tdelta1 _ _ => ∅
  | tabstract idx _ _ => {[ idx ]}
  | tproduct l r => te_absset l ∪ te_absset r
  | tsum summand =>
    te_absset summand
  end.


Lemma te_varset_decomp te :
  te_varset te = set_map bound (te_bound_varset te) ∪
    set_map free (te_free_varset te).
Proof.
  unfold_leibniz.
  induction te; cbn in *; [set_solver| destruct l, u; set_solver+| |
    rewrite 1?IHte1, 1?IHte2; set_solver +|apply IHte].
  generalize (lower ++ upper) as l.
  intros l; induction l as [|[]]; [set_solver|
    cbn [list_to_set omap list_omap v2bound v2free];
  rewrite IHl; set_solver+..].
Qed.







Record tensorlist := mk_tl {
  tl_sums : nat;
  tl_abstracts : list (Idx * list var * list var);
  tl_deltas : list (var * var)
}.

Lemma tl_ext tl tl' :
  tl.(tl_sums) = tl'.(tl_sums) ->
  tl.(tl_abstracts) = tl'.(tl_abstracts) ->
  tl.(tl_deltas) = tl'.(tl_deltas) ->
  tl = tl'.
Proof.
  destruct tl, tl'; cbn; congruence.
Qed.

Definition tl_add_sums (n : nat) (tl : tensorlist) : tensorlist :=
  mk_tl (n + tl.(tl_sums)) (tl.(tl_abstracts)) (tl.(tl_deltas)).


Fixpoint tensorexpr_of_tensorlist_aux sums abs delts : tensorexpr :=
  match sums with
  | O => tproducts ((tabstract' <$> abs) ++ (tdelta1' <$> delts))
  | S sums => tsum (tensorexpr_of_tensorlist_aux sums abs delts)
  end.

Definition tensorexpr_of_tensorlist (tl : tensorlist) : tensorexpr :=
  tensorexpr_of_tensorlist_aux tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas).

Coercion tensorexpr_of_tensorlist : tensorlist >-> tensorexpr.


Definition tlone : tensorlist := mk_tl O [] [].

Lemma tlone_correct : tlone =@{tensorexpr} tone.
Proof.
  reflexivity.
Qed.


Definition tensorlist_perm_eq (tl tl' : tensorlist) :=
  tl.(tl_sums) = tl'.(tl_sums) /\
  tl.(tl_abstracts) ≡ₚ tl'.(tl_abstracts) /\
  tl.(tl_deltas) ≡ₚ tl'.(tl_deltas).


(* Variable sets for [tensorlist]s *)

Definition abstracts_vars (abs : list (Idx * list var * list var)) : gset var :=
  list_to_set ('(_, lower, upper) ← abs; lower ++ upper).

Definition abstracts_bound_vars
  (abs : list (Idx * list var * list var)) : Pset :=
  list_to_set ('(_, lower, upper) ← abs; omap v2bound (lower ++ upper)).

Definition abstracts_free_vars
  (abs : list (Idx * list var * list var)) : Pset :=
  list_to_set ('(_, lower, upper) ← abs; omap v2free (lower ++ upper)).

Definition deltas_vars (delts : list (var * var)) : gset var :=
  list_to_set ('(l, u) ← delts; [l;u]).

Definition deltas_bound_vars (delts : list (var * var)) : Pset :=
  list_to_set ('(l, u) ← delts; omap v2bound [l;u]).

Definition deltas_free_vars (delts : list (var * var)) : Pset :=
  list_to_set ('(l, u) ← delts; omap v2free [l;u]).



(** Relabeling in [tensorlist]s *)

Definition relabel_abs {I} {A B} (f : A -> B) (abs : I * list A * list A) :=
  let '(idx, lower, upper) := abs in
  (idx, f <$> lower, f <$> upper).

Definition relabel_delt {A B} (f : B -> A) (delt : B * B) :=
  let '(l, u) := delt in
  (f l, f u).

Definition relabel_tl (f : var -> var) (tl : tensorlist) : tensorlist :=
  mk_tl (tl.(tl_sums))
    (relabel_abs f <$> tl.(tl_abstracts))
    (relabel_delt f <$> tl.(tl_deltas)).

Definition relabel_bounds (f : Idx -> Idx) : var -> var :=
  var_map f id.


(* A simpler, but less performant, definition *)
(* Definition tl_times_spec_defn (l r : tensorlist) : tensorlist :=
  let 'mk_tl lsums labs ldelts := l in
  let 'mk_tl rsums rabs rdelts := r in
  (* let lenl := length lsums in
  let lenr := length rsums in *)
  let labs' := relabel_abs (relabel_bounds
    (λ p, pos_add_N p (N.of_nat rsums))) <$> labs in
  let rabs' := relabel_abs (relabel_bounds (λ p,
    if decide (p < rsums)%nat then p
    else pos_add_N p (N.of_nat lsums))) <$> rabs in
  let ldelts' := relabel_delt (relabel_bounds
    (λ p, pos_add_N p (N.of_nat rsums))) <$> ldelts in
  let rdelts' := relabel_delt (relabel_bounds (λ p,
    if decide (p < rsums)%nat then p
    else pos_add_N p (N.of_nat lsums))) <$> rdelts in
  mk_tl (lsums + rsums) (labs' ++ rabs') (ldelts' ++ rdelts'). *)


Definition tl_times (l r : tensorlist) : tensorlist :=
  (* let 'mk_tl lsums labs := l in
  let 'mk_tl rsums rabs := r in
  let lenl := lengthN lsums in
  let lenr := lengthN rsums in
  let labs' := match lenr with
    | N0 => labs
    | Npos lenr => relabel_abs (relabel_bounds (Pos.add lenr)) <$> labs
    end in
  let rabs' := match lenl with
    | N0 => rabs
    | Npos lenl => match lenr with
      | N0 => relabel_abs (relabel_bounds (Pos.add lenl)) <$> rabs
      | Npos lenr => relabel_abs (relabel_bounds (λ p,
        if Pos.leb p lenr then p else Pos.add lenl p)) <$> rabs
      end
    end in
  mk_tl (lsums ++ rsums) (labs' ++ rabs'). *)
  let 'mk_tl lsums labs ldelts := l in
  let 'mk_tl rsums rabs rdelts := r in
  (* let lenl := length lsums in
  let lenr := length rsums in *)
  let labs' := relabel_abs (relabel_bounds
    (λ p, pos_add_N p (N.of_nat rsums))) <$> labs in
  let rabs' := relabel_abs (relabel_bounds (λ p,
    if decide (p < rsums)%nat then p
    else pos_add_N p (N.of_nat lsums))) <$> rabs in
  let ldelts' := relabel_delt (relabel_bounds
    (λ p, pos_add_N p (N.of_nat rsums))) <$> ldelts in
  let rdelts' := relabel_delt (relabel_bounds (λ p,
    if decide (p < rsums)%nat then p
    else pos_add_N p (N.of_nat lsums))) <$> rdelts in
  mk_tl (lsums + rsums) (labs' ++ rabs') (ldelts' ++ rdelts').


Lemma relabel_abs_id {I A} abs : relabel_abs (I:=I) (@id A) abs = abs.
Proof.
  destruct abs as [[f low] up]; cbn.
  now rewrite 2 list_fmap_id.
Qed.

Lemma relabel_abs_ext {I A B} f g abs :
  (forall x, f x = g x) -> @relabel_abs I A B f abs = relabel_abs g abs.
Proof.
  intros Heq.
  destruct abs as [[idx low] up]; cbn.
  f_equal; [f_equal|]; apply list_fmap_ext; intros; apply Heq.
Qed.

Lemma relabel_abs_id' {I A} f abs :
  (forall x : A, f x = x) -> relabel_abs (I:=I) f abs = abs.
Proof.
  intros Hid.
  erewrite relabel_abs_ext; [apply relabel_abs_id|apply Hid].
Qed.

Lemma relabel_abs_compose {I A B C} (f : A -> B) (g : B -> C) l :
  relabel_abs g (relabel_abs (I:=I) f l) = relabel_abs (g ∘ f) l.
Proof.
  unfold relabel_abs.
  destruct l as ((idx, low), up).
  now rewrite <- 2 list_fmap_compose.
Qed.

Lemma relabel_delt_id {A} delt : relabel_delt (@id A) delt = delt.
Proof.
  now destruct delt.
Qed.

Lemma relabel_delt_ext {A B} f g delt :
  (forall x, f x = g x) -> @relabel_delt A B f delt = relabel_delt g delt.
Proof.
  intros Heq.
  destruct delt as [l u]; cbn; f_equal; apply Heq.
Qed.

Lemma relabel_delt_id' {A} f delt :
  (forall x : A, f x = x) -> relabel_delt f delt = delt.
Proof.
  intros Hid.
  erewrite relabel_delt_ext; [apply relabel_delt_id|apply Hid].
Qed.

Lemma relabel_delt_compose {A B C} (f : A -> B) (g : B -> C) lu :
  relabel_delt g (relabel_delt f lu) = relabel_delt (g ∘ f) lu.
Proof.
  now destruct lu.
Qed.

Lemma relabel_bounds_ext f g :
  (forall r, f r = g r) -> forall v, relabel_bounds f v = relabel_bounds g v.
Proof.
  intros Hfg.
  destruct v; [|reflexivity..].
  cbn; now rewrite Hfg.
Qed.

Add Parametric Morphism : relabel_bounds with signature
  pointwise_relation _ eq ==> eq ==> eq as relabel_bounds_mor.
Proof.
  apply relabel_bounds_ext.
Qed.

Lemma relabel_bounds_id v : relabel_bounds id v = v.
Proof. now destruct v. Qed.

Lemma relabel_bounds_id' f v :
  (forall r, f r = r) -> relabel_bounds f v = v.
Proof.
  intros Hf.
  erewrite relabel_bounds_ext; [apply relabel_bounds_id|apply Hf].
Qed.


Lemma relabel_abs_ext_strong {I A B} (f g : A -> B) abs :
  (forall x, x ∈ abs.1.2 ++ abs.2 ->
    f x = g x) -> @relabel_abs I A B f abs = relabel_abs g abs.
Proof.
  intros Hfg.
  unfold relabel_abs.
  destruct abs as ((idx, low), up).
  f_equal; [f_equal|]; apply list_fmap_ext; intros _ ? ?%elem_of_list_lookup_2;
  apply Hfg, elem_of_app; [left|right]; easy.
Qed.

Lemma relabel_abs_id_strong {I A} (f : A -> A) abs :
  (forall x, x ∈ abs.1.2 ++ abs.2 -> f x = x) -> relabel_abs (I:=I) f abs = abs.
Proof.
  intros Hf.
  transitivity (relabel_abs id abs); [|apply relabel_abs_id].
  now apply relabel_abs_ext_strong.
Qed.

Lemma relabel_delt_ext_strong {A B} (f g : A -> B) lu :
  (forall x, x = lu.1 \/ x = lu.2 -> f x = g x) ->
    relabel_delt f lu = relabel_delt g lu.
Proof.
  intros Hfg.
  destruct lu as [l u].
  cbn.
  f_equal; auto.
Qed.

Lemma relabel_delt_id_strong {A} (f : A -> A) lu :
  (forall x, x = lu.1 \/ x = lu.2 -> f x = x) ->
  relabel_delt f lu = lu.
Proof.
  intros Hf.
  transitivity (relabel_delt id lu); [|apply relabel_delt_id].
  now apply relabel_delt_ext_strong.
Qed.

Lemma relabel_bounds_compose g f v :
  relabel_bounds g (relabel_bounds f v) =
  relabel_bounds (g ∘ f) v.
Proof.
  now destruct v.
Qed.

Lemma imap_to_fmap {A B} (f : A -> B) l :
  imap (fun _ => f) l = f <$> l.
Proof.
  induction l; cbn; rewrite <- ? IHl; reflexivity.
Qed.

(* Lemma tl_times_spec_defn_correct l r :
  tl_times l r = tl_times_spec_defn l r.
Proof.
  destruct l as [lsums labs], r as [rsums rabs].
  cbn.
  rewrite <- !lengthN_correct_rev, <- !lengthN_correct.
  f_equal; f_equal.
  - case_match eqn:Hrsums.
    + cbn.
      symmetry.
      apply list_fmap_id'.
      intros; apply relabel_abs_id'.
      now intros [].
    + apply list_fmap_ext; intros _ ? _.
      apply relabel_abs_ext; intros []; [cbn; now rewrite Pos.add_comm|
        reflexivity..].
  - destruct (lengthN lsums) as [|lenl] eqn:Hlsums;
    [|destruct (lengthN rsums) as [|lenr] eqn:Hrsums].
    + cbn.
      symmetry.
      apply list_fmap_id'.
      intros; apply relabel_abs_id'.
      now intros []; cbn; [case_match|..].
    + apply list_fmap_ext; intros _ ? _.
      apply relabel_abs_ext; intros []; [cbn; now rewrite Pos.add_comm|
        reflexivity..].
    + apply list_fmap_ext; intros _ ? _.
      apply relabel_abs_ext.
      intros [p| |]; [|reflexivity..].
      cbn.
      destruct (Pos.leb_spec p lenr);
      [rewrite decide_True by lia|rewrite decide_False by lia];
      f_equal; lia.
Qed. *)



(** Converting a [tensorexpr] to a [tensorlist] *)

Fixpoint tensorlist_of_tensorexpr (te : tensorexpr) : tensorlist :=
  match te with
  | tone => tlone
  | tdelta1 l u => mk_tl O [] [(l, u)]
  | tabstract idx lower upper => mk_tl O [(idx, lower, upper)] []
  | tproduct l r => tl_times (tensorlist_of_tensorexpr l) (tensorlist_of_tensorexpr r)
  | tsum smd =>
    tl_add_sums 1 (tensorlist_of_tensorexpr smd)
  end.



(* Matching on [tensorlist]s *)

(* FIXME: Move *)
Definition Pmap_map (m : Pmap Idx) : Idx -> Idx :=
  fun v => default v (m !! v).


Definition var_subst_frees (f : Idx -> var) (v : var) : var :=
  match v with
  | free l => f l
  | _ => v
  end.









Record tensorequation := mk_teq {
  teq_lhs : tensorexpr;
  teq_rhs : tensorexpr;
  teq_univ : Pset;
    (* The set of universally-quantified variables *)
}.


Record tensorlistequation := mk_tleq {
  tleq_lhs : tensorlist;
  tleq_rhs : tensorlist;
  tleq_univ : Pset;
    (* The set of universally-quantified variables *)
}.


(* FIXME: Move *)

Definition get_var {A} (ml : Pmap A) (mr : list A) (v : var) : option A :=
  match v with
  | bound r => mr !! (r :> nat)
  | free l => ml !! l
  end.



Fixpoint te_substl (f : Idx -> var) (te : tensorexpr) : tensorexpr :=
  match te with
  | tone => tone
  | tdelta1 l u => tdelta1 (from_option f l (v2free l)) (from_option f u (v2free u))
  | tabstract abs low up =>
    tabstract abs ((λ v, from_option f v (v2free v)) <$> low)
      ((λ v, from_option f v (v2free v)) <$> up)
  | tproduct l r =>
    tproduct (te_substl f l) (te_substl f r)
  | tsum smd =>
    tsum (te_substl (addbound 1 ∘ f) smd)
  end.














Lemma withboundshift_0 f :
  pointwise_relation var eq (withboundshift 0 f) f.
Proof.
  now intros []; cbv; case_match.
Qed.


Add Parametric Morphism : te_substl with signature
  pointwise_relation _ eq ==> eq ==> eq as te_substl_ext.
Proof.
  intros f g Hfg te.
  revert f g Hfg; induction te; intros f g Hfg.
  - easy.
  - destruct l, u; cbn; f_equal; apply Hfg.
  - cbn.
    f_equal; apply list_fmap_ext; intros _ [] _; easy + cbn; apply Hfg.
  - cbn; f_equal; auto.
  - cbn.
    f_equal.
    apply IHte.
    intros ?.
    cbn.
    now rewrite Hfg.
Qed.

Lemma elem_of_te_free_varset_tabstract absidx lower upper l :
  l ∈ te_free_varset (tabstract absidx lower upper) <->
  free l ∈ lower ++ upper.
Proof.
  cbn.
  rewrite elem_of_list_to_set, elem_of_list_omap.
  split; [|unfold v2free; eexists; split; [eauto|reflexivity]].
  now intros ([] & ? & [= ->]).
Qed.



Lemma relabel_te_ext f g te :
  pointwise_relation var eq f g ->
  relabel_te f te = relabel_te g te.
Proof.
  intros; now apply relabel_te_aux_ext.
Qed.

Lemma withboundshift_compose shift f g v :
  withboundshift shift f (withboundshift shift g v) =
  withboundshift shift (f ∘ g) v.
Proof.
  destruct v; cbn; [|destruct (g _); cbn; [rewrite decide_False by lia;
    repeat first [lia | f_equal] |reflexivity..]..].
  case_decide.
  - cbn; now apply decide_True.
  - destruct (g _); [|reflexivity..].
    cbn.
    rewrite decide_False by lia.
    repeat first [lia | f_equal].
Qed.


Lemma withboundshift_id shift v :
  withboundshift shift id v = v.
Proof.
  destruct v; [|reflexivity..].
  cbn.
  case_decide; f_equal; lia.
Qed.

Lemma relabel_te_aux_compose shift f g te :
  relabel_te_aux shift g (relabel_te_aux shift f te) =
  relabel_te_aux shift (g ∘ f) te.
Proof.
  revert shift; induction te; intros shift.
  - reflexivity.
  - cbn.
    f_equal; apply withboundshift_compose.
  - cbn.
    rewrite <- ! list_fmap_compose.
    f_equal; apply list_fmap_ext; intros _ v _;
    cbn; apply withboundshift_compose.
  - cbn; f_equal; auto.
  - cbn.
    f_equal.
    auto.
Qed.

Lemma relabel_te_compose f g te :
  relabel_te g (relabel_te f te) = relabel_te (g ∘ f) te.
Proof.
  apply relabel_te_aux_compose.
Qed.


Lemma relabel_te_aux_id shift te :
  relabel_te_aux shift id te =
  te.
Proof.
  revert shift; induction te; intros shift.
  - reflexivity.
  - cbn.
    now rewrite 2 withboundshift_id.
  - cbn.
    now rewrite 2 list_fmap_id' by now intros; apply withboundshift_id.
  - cbn; f_equal; auto.
  - cbn.
    f_equal.
    auto.
Qed.

Lemma relabel_te_id te :
  relabel_te id te = te.
Proof.
  apply relabel_te_aux_id.
Qed.




(* Typing for [tensorexpr]s *)

Declare Scope tensorexpr_scope.
Delimit Scope tensorexpr_scope with te.
Bind Scope tensorexpr_scope with tensorexpr.

Declare Custom Entry args_print.

Declare Custom Entry var_print.

Notation " '#' r " := (bound r) (in custom var_print at level 1).
Notation " 'L@' l " := (free l) (in custom var_print at level 1).

Notation " '()' " := (@nil var) (in custom args_print at level 0).
Notation " '(' x ,  .. ,  y ')'" :=
  (cons x .. (cons y nil) ..)
  (in custom args_print at level 0, x custom var_print at level 1,
    y custom var_print at level 1).


Notation "te  *  te'" := (tproduct te%te te'%te) : tensorexpr_scope.
Notation "1" := (tone) : tensorexpr_scope.
Notation "'δ[' l ,  u ']'" := (tdelta1 l u)
  (l custom args_print, u custom args_print) : tensorexpr_scope.
Notation "∑'  ty ,  te" := (tsum ty%nat te%te)
  (at level 45, right associativity) : tensorexpr_scope.
Notation "'!{' f '}'  low  up" :=
  (tabstract f low up) (at level 10,
    low custom args_print at level 0,
    up custom args_print at level 0) : tensorexpr_scope.



Fixpoint well_typed (sums : nat) (frees : Pset) (te : tensorexpr) : Prop :=
  match te with
  | tone => True
  | tdelta1 l r =>
    var_elim (λ p, (p < sums)%nat) (.∈ frees) l /\
      var_elim (λ p, (p < sums)%nat) (.∈ frees) r
  | tabstract f low up =>
    Forall (var_elim (λ p, (p < sums)%nat) (.∈ frees)) (low ++ up)
  | tproduct te te' =>
    well_typed sums frees te /\ well_typed sums frees te'
  | tsum te => well_typed (S sums) frees te
  end.


Fixpoint is_well_typed (sums : nat) (frees : Pset) (te : tensorexpr) : bool :=
  match te with
  | tone => true
  | tdelta1 l r =>
    var_elim (λ p, bool_decide (p < sums)%nat) (λ fr, bool_decide (fr ∈ frees)) l &&
      var_elim (λ p, bool_decide (p < sums)%nat) (λ fr, bool_decide (fr ∈ frees)) r
  | tabstract f low up =>
    forallb (var_elim (λ p, bool_decide (p < sums)%nat) (λ fr, bool_decide (fr ∈ frees)))
      (low ++ up)
  | tproduct te te' =>
    is_well_typed sums frees te && is_well_typed sums frees te'
  | tsum te => is_well_typed (S sums) frees te
  end.

Lemma is_well_typed_correct sums frees te :
  is_well_typed sums frees te <->
  well_typed sums frees te.
Proof.
  revert sums; induction te; intros sums; cbn.
  - easy.
  - rewrite andb_True.
    destruct l, u; cbn; f_equiv; apply bool_decide_spec.
  - rewrite forallb_True.
    apply Forall_iff.
    intros []; cbn; apply bool_decide_spec.
  - now rewrite andb_True, IHte1, IHte2.
  - apply IHte.
Qed.

Lemma is_well_typed_correct_alt sums frees te :
  if (is_well_typed sums frees te)
  then well_typed sums frees te else ¬ well_typed sums frees te.
Proof.
  specialize (is_well_typed_correct sums frees te).
  destruct (is_well_typed _ _ _); cbn; naive_solver.
Qed.

#[global] Instance well_typed_dec sums frees te : Decision (well_typed sums frees te) :=
  match is_well_typed sums frees te
    as b return ((if b return Prop then _ else _) -> _) with
  | true => left
  | false => right
  end (is_well_typed_correct_alt sums frees te).
(*

Definition all_bound (tl : tensorlist) : Prop :=
  abstracts_bound_vars tl.(tl_abstracts) =
  list_to_set (pseq 1 (lengthN tl.(tl_sums))).

Definition tleq_well_typed tc teeq : Prop :=
  let tc' := mk_tc tc.(tc_ma) tc.(tc_mg) teeq.(tleq_univ) [] in
  well_typed tc' teeq.(tleq_lhs) /\
  well_typed tc' teeq.(tleq_rhs) /\
  te_free_varset teeq.(tleq_rhs) ⊆ te_free_varset teeq.(tleq_lhs) /\
  dom teeq.(tleq_univ) = te_free_varset teeq.(tleq_lhs)
    (* NB: ⊆ suffices, by the first WT condition *).

(* (* TODO: Make; FIXME: Move *)
Fixpoint Pmap_ne_sizeP {A} (p : Pmap_ne A) : positive := *)
 *)

(*
Local Open Scope lazy_bool_scope.
Definition tleq_is_well_typed_aux ta tg lhs rhs univ :=
  let '(mk_tl lsums labs) := lhs in
  let '(mk_tl rsums rabs) := rhs in
  let lhs_mr := reverse lsums in
  let rhs_mr := reverse rsums in
  (forallb (λ '(f, low, up),
    is_well_typed_abs ta tg univ lhs_mr f low up) labs &&&
  forallb (λ '(f, low, up),
    is_well_typed_abs ta tg univ rhs_mr f low up) rabs &&&
  let lfrees := abstracts_free_vars labs in
  Pset_subseteqb (abstracts_free_vars rabs) lfrees &&&
  Pmap_dom_subseteqb univ (lfrees.(mapset.mapset_car))
  ). *)

Lemma is_well_typed_tproducts sums frees tes :
  is_well_typed sums frees (tproducts tes) =
  forallb (is_well_typed sums frees) tes.
Proof.
  induction tes as [|te tes]; cbn; [easy|rewrite <- IHtes].
  congruence.
Qed.
(*
Lemma tl_is_well_typed_alt_aux ta tg tl tr (tel : tensorlist) :
  is_well_typed ta tg tl tr tel =
    let '(mk_tl lsums labs ldelts) := tel in
    forallb (λ '(f, low, up),
    is_well_typed_abs ta tg tl (rev_append lsums tr) f low up) labs &&
    .
Proof.
  destruct tel as [lsums labs].
  revert tr; induction lsums; intros tr.
  - cbn.
    rewrite is_well_typed_tproducts.
    apply Bool.eq_iff_eq_true;
    rewrite 2 forallb_forall, <- 2 List.Forall_forall.
    rewrite Forall_fmap.
    apply Forall_iff.
    intros ((f, low), up); reflexivity.
  - cbn.
    apply IHlsums.
Qed.

Lemma well_typed_free_varset_subseteq tc te :
  well_typed tc te -> te_free_varset te ⊆ dom (tc.(tc_ml)).
Proof.
  revert tc;
  induction te; intros tc.
  - easy.
  - cbn.
    destruct (tc_ma tc !! _) as [tys|]; [cbn|easy].
    generalize (lower ++ upper); intros vs.
    intros [= Hvs].
    revert tys Hvs;
    induction vs as [|v vs IHvs];
    [easy|intros [|ty tys] [= Hv Hvs%IHvs]].
    cbn.
    destruct v as [|l|]; [apply Hvs| |apply Hvs].
    simpl.
    cbn in Hv.
    symmetry in Hv.
    apply elem_of_dom_2 in Hv.
    set_solver + Hv Hvs.
  - cbn; set_solver.
  - cbn.
    apply IHte.
Qed. *)



Lemma elem_of_abstracts_bound_vars l abs :
  l ∈ abstracts_bound_vars abs <->
  exists idx low up, (idx, low, up) ∈ abs /\ bound l ∈ low ++ up.
Proof.
  unfold abstracts_bound_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_list_omap.
  split; [|naive_solver].
  intros (idx & low & up & ([] & ? & [= ->]) & ?).
  eauto.
Qed.
Lemma elem_of_abstracts_free_vars l abs :
  l ∈ abstracts_free_vars abs <->
  exists idx low up, (idx, low, up) ∈ abs /\ free l ∈ low ++ up.
Proof.
  unfold abstracts_free_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_list_omap.
  split; [|naive_solver].
  intros (idx & low & up & ([] & ? & [= ->]) & ?).
  eauto.
Qed.

Lemma elem_of_deltas_bound_vars r delts :
  r ∈ deltas_bound_vars delts <->
  exists l u, (l, u) ∈ delts /\ (l = bound r \/ u = bound r).
Proof.
  unfold deltas_bound_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite exists_pair.
  apply exists_iff; intros l.
  apply exists_iff; intros u.
  rewrite (and_comm _).
  f_equiv.
  now destruct l, u; set_solver.
Qed.
Lemma elem_of_deltas_free_vars r delts :
  r ∈ deltas_free_vars delts <->
  exists l u, (l, u) ∈ delts /\ (l = free r \/ u = free r).
Proof.
  unfold deltas_free_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite exists_pair.
  apply exists_iff; intros l.
  apply exists_iff; intros u.
  rewrite (and_comm _).
  f_equiv.
  now destruct l, u; set_solver.
Qed.

Lemma te_free_varset_tproducts tes :
  te_free_varset (tproducts tes) = ⋃ (te_free_varset <$> tes).
Proof.
  induction tes; cbn; set_solver.
Qed.

Lemma tabstract'_alt abs :
  tabstract' abs = tabstract abs.1.1 abs.1.2 abs.2.
Proof.
  now destruct abs as [[]].
Qed.

Lemma tdelta1'_alt lu :
  tdelta1' lu = tdelta1 lu.1 lu.2.
Proof.
  now destruct lu.
Qed.

Lemma te_free_varset_tl (tl : tensorlist) :
  te_free_varset tl =
  abstracts_free_vars tl.(tl_abstracts) ∪ deltas_free_vars tl.(tl_deltas).
Proof.
  destruct tl as [sums abs delts].
  cbn -[abstracts_free_vars deltas_free_vars].
  induction sums; [|apply IHsums].
  cbn.
  rewrite te_free_varset_tproducts.
  rewrite fmap_app, union_list_app_L.
  rewrite <- 2 list_fmap_compose.
  unfold compose.
  setoid_rewrite tabstract'_alt.
  setoid_rewrite tdelta1'_alt.
  cbn -[omap].
  change (_ <$> abs) with (((list_to_set (C:=Pset)) ∘ (λ x, omap v2free (x.1.2 ++ x.2))) <$> abs).
  change (_ <$> delts) with
    (((list_to_set (C:=Pset)) ∘ (λ x, omap v2free [x.1; x.2])) <$> delts).
  rewrite 2 list_fmap_compose, <- 2 list_to_set_concat_L.
  rewrite <- 2 flat_map_concat_map, <- list_bind_flat_map.
  change (list_bind ?A ?B) with (@mbind list list_bind A B).
  f_equiv.
  - unfold abstracts_free_vars.
    f_equiv.
    now apply list_bind_ext; [intros [[]]|].
  - unfold deltas_free_vars.
    f_equiv.
    now apply list_bind_ext; [intros []|].
Qed.

(*
Lemma tleq_is_well_typed_aux_correct ta tg tl tr lhs rhs univ :
  tleq_is_well_typed_aux ta tg lhs rhs univ <->
  tleq_well_typed (mk_tc ta tg tl tr) (mk_tleq lhs rhs univ).
Proof.
  unfold tleq_is_well_typed_aux, tleq_well_typed; cbn.
  destruct lhs as [lsums labs], rhs as [rsums rabs].
  rewrite 3 lazy_andb_True, <- (and_assoc _).
  apply and_iff_from_l;
    [now rewrite <- is_well_typed_correct, tl_is_well_typed_alt_aux|].
  intros Hall_l Hty_l.
  apply and_iff_from_l;
    [now rewrite <- is_well_typed_correct, tl_is_well_typed_alt_aux|].
  intros Hall_r Hty_r.
  apply and_iff_from_l;
    [now rewrite Pset_subseteqb_correct, 2 te_free_varset_tl|].
  intros Hsub%Pset_subseteqb_correct Hsub'.
  rewrite Pmap_dom_subseteqb_correct, Aux_stdpp.dom_Pset.
  rewrite te_free_varset_tl; cbn [tl_abstracts].
  split; [|now intros ->].
  intros Hsub''.
  unfold_leibniz.
  apply set_subseteq_antisymm; [easy|].
  apply well_typed_free_varset_subseteq in Hty_l.
  rewrite te_free_varset_tl in Hty_l.
  apply Hty_l.
Qed. *)


Lemma pos_swap_alt p :
  pos_swap p = (if decide (p = 1) then 2 else if decide (p = 2) then 1 else p)%positive.
Proof.
  unfold pos_swap.
  destruct p as [| []|]; reflexivity.
Qed.


(*
Lemma te_substl_wt_aux ctx bounds tys te (substs : Pmap var) :
  (forall l, l ∈ te_free_varset te ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
  well_typed (tc_app_types bounds (tc_eqn_with_frees ctx tys)) te ->
  well_typed (tc_app_types bounds ctx)
    (te_substl (addbound (lengthN bounds) ∘ λ l, default (free l) (substs !! l)) te).
Proof.
  revert bounds ctx;
  induction te; intros bounds ctx Hty.
  - easy.
  - cbn.
    intros Hhyp.
    assert (Hbounds : forall r, bound r ∈ lower ++ upper -> (N.pos r <= lengthN bounds)%N). 1:{
      apply fmap_Some in Hhyp as (argtys & _ & Heq).
      intros r (i & Hlui)%elem_of_list_lookup_1.
      apply (f_equal (.!! i)) in Heq.
      rewrite 2 list_lookup_fmap, Hlui in Heq.
      cbn in Heq.
      rewrite app_nil_r in Heq.
      destruct (argtys !! i); [|easy].
      cbn in Heq.
      injection Heq.
      intros ?%lookup_lt_Some.
      rewrite lengthN_correct_rev.
      lia.
    }
    revert Hhyp.
    intros ->.
    setoid_rewrite elem_of_te_free_varset_tabstract in Hty.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
    destruct v as [r|l|]; [..|reflexivity].
    + cbn.
      apply Hbounds in Hv.
      rewrite lengthN_correct_rev in Hv.
      now rewrite 2 lookup_app_l by lia.
    + cbn.
      specialize (Hty l Hv).
      rewrite lookup_union.
      destruct (substs !! l), (tys !! l); try easy; cbn in *.
      * rewrite union_Some_l.
        revert Hty; intros [= <-].
        unfold tc_get_var; cbn.
        destruct v; [|reflexivity..].
        cbn.
        rewrite lengthN_correct_rev.
        rewrite lookup_app_r by lia.
        f_equal; lia.
      * now rewrite option_union_left_id.
  - cbn; intros [?%IHte1 ?%IHte2]; [|set_solver +Hty..].
    now split.
  - cbn.
    intros Hte.
    erewrite (te_substl_ext _
      (addbound (N.succ (lengthN bounds)) ∘ λ l, default (free l) (substs !! l)));
      [| | reflexivity].
    2: {
      intros v; cbn.
      destruct (substs !! v) as [[]|]; [|reflexivity..].
      cbn.
      f_equal; lia.
    }
    rewrite tc_cons_app_type.
    apply (IHte (ty :: bounds)); [easy|].
    now rewrite tc_cons_app_type in Hte.
Qed.

Lemma te_substl_wt ctx tys te (substs : Pmap var) :
  (forall l, l ∈ te_free_varset te ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
  well_typed (tc_eqn_with_frees ctx tys) te ->
  well_typed ctx
    (te_substl (λ l, default (free l) (substs !! l)) te).
Proof.
  specialize (te_substl_wt_aux ctx [] tys te substs) as Hen.
  intros Hty Hwt.
  specialize (Hen Hty Hwt).
  replace (tc_app_types _ _) with ctx in Hen by now destruct ctx.
  erewrite te_substl_ext; [apply Hen | | reflexivity].
  intros v; cbn.
  destruct (substs !! v) as [[]|]; reflexivity.
Qed. *)








(*

Fixpoint tl_to_te_with_aux (base : list tensorexpr) (sums : list Ty)
  (abs : list (Idx * list var * list var)) : tensorexpr :=
  match sums with
  | [] => tproducts (base ++ (tabstract' <$> abs))
  | ty :: sums => tsum ty (tl_to_te_with_aux base sums abs)
  end.

Notation tl_to_te_with base tl :=
  (tl_to_te_with_aux base (tl_sums tl) (tl_abstracts tl)).

Lemma tensorexpr_of_tensorlist_aux_to_tl_to_te_with_aux sums abs :
  tensorexpr_of_tensorlist_aux sums abs =
  tl_to_te_with_aux [] sums abs.
Proof.
  induction sums; cbn; congruence.
Qed. *)


Add Parametric Relation : tensorlist tensorlist_perm_eq
  reflexivity proved by ltac:(split; [|split]; reflexivity)
  symmetry proved by ltac:(unfold tensorlist_perm_eq; split; [|split]; now symmetry)
  transitivity proved by ltac:(unfold tensorlist_perm_eq; intros ???(?&?&?)(?&?&?);
     split; [|split]; etransitivity; eauto)
  as tensorlist_perm_eq_setoid.

Add Parametric Morphism : abstracts_vars with signature
  Permutation ==> eq as abstracts_vars_perm_mor.
Proof.
  unfold abstracts_vars.
  now intros ? ? ->.
Qed.

(* Equivalence of [tensorlist]s up to (alpha-equivalence and) permutation *)
Definition tl_aeq : relation tensorlist :=
  fun tl tl' =>
  exists (fr : Idx -> Idx),
    let n := (Pos.of_succ_nat tl.(tl_sums)) in
    posperm n fr /\
    tl.(tl_sums) = tl'.(tl_sums) /\
    tl.(tl_abstracts) ≡ₚ
      relabel_abs (relabel_bounds $ make_pwf n fr) <$> tl'.(tl_abstracts) /\
    tl.(tl_deltas) ≡ₚ
      relabel_delt (relabel_bounds $ make_pwf n fr) <$> tl'.(tl_deltas).

#[export] Instance tl_aeq_of_perm : subrelation tensorlist_perm_eq tl_aeq.
Proof.
  intros [lsums labs ldelt] [rsums rabs rdelt] [Hsums [Habs Hdelt]].
  cbn in *.
  exists id.
  split_and!; cbn; [apply posperm_id|easy|rewrite Habs|rewrite Hdelt];
  apply eq_reflexivity; symmetry;
  apply list_fmap_id';
  [intros [[f l] u] _; apply relabel_abs_id'|intros [l u] _; apply relabel_delt_id'];
  intros v; apply relabel_bounds_id'; intros r;
  cbn; case_decide; easy.
Qed.


Lemma tl_aeq_refl tl : tl_aeq tl tl.
Proof.
  apply tl_aeq_of_perm; reflexivity.
Qed.


Lemma tl_aeq_symm tl tl' : tl_aeq tl tl' -> tl_aeq tl' tl.
Proof.
  intros (f & Hf & Hsums & Habs & Hdelt).
  exists (posperm_inv (Pos.of_succ_nat tl.(tl_sums)) f).
  (* apply (f_equal length) in Hsums as Hlen.
  rewrite length_ppermute, 2 length_reverse in Hlen.
  pose proof Hlen as HlenN.
  rewrite <- 2 lengthN_correct in HlenN.
  apply N2Nat.inj in HlenN. *)
  intros n.
  split; [subst n; rewrite <- Hsums; now apply posperm_inv_posperm|].
  split; [easy|].
  eenough (Hen : _);
  [split; cycle 1|].
  - rewrite Hdelt.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity, symmetry, list_fmap_id'.
    intros (l, u) _.
    cbn.
    rewrite 2 relabel_bounds_compose.
    f_equal; apply relabel_bounds_id'; intros r; exact (Hen r).
  - rewrite Habs.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity, symmetry, list_fmap_id'.
    intros ((fidx, low), up) _.
    cbn.
    rewrite <- 2 list_fmap_compose.
    f_equal; [f_equal|]; apply list_fmap_id'; intros [r|] _; try reflexivity;
    cbn; f_equal;
    apply Hen.
  - intros r.
    cbn;
    subst n;
    rewrite <- Hsums;
    (destruct_decide (decide (Pos.of_succ_nat tl.(tl_sums) <= r)) as Hr;
    [now rewrite decide_True |
      rewrite decide_False by
      now pose proof (posperm_bounded _ _ Hf r); lia]);
    f_equal; apply posperm_inv_linv; easy + lia.
Qed.

Lemma tl_aeq_trans tl tl' tl'' : tl_aeq tl tl' -> tl_aeq tl' tl'' ->
  tl_aeq tl tl''.
Proof.
  intros (f & Hf & Hfsums & Hfabs & Hfdelt)
    (g & Hg & Hgsums & Hgabs & Hgdelt).
  exists (f ∘ g).
  intros n.
  (* apply (f_equal length) in Hfsums as Hflen.
  apply (f_equal length) in Hgsums as Hglen.
  rewrite length_ppermute, !length_reverse in Hflen, Hglen.
  pose proof Hflen as HflenN.
  pose proof Hglen as HglenN.
  rewrite <- 2 lengthN_correct in HflenN, HglenN.
  apply N2Nat.inj in HflenN, HglenN. *)
  split; [now apply posperm_compose; subst n; congruence|].
  eenough (Hen : _);
  [split; [congruence|split]|].
  - rewrite Hfabs, Hgabs.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity.
    apply list_fmap_ext; intros _ ((idx, low), up) _.
    cbn.
    rewrite <- 2 list_fmap_compose.
    f_equal; [f_equal|]; apply list_fmap_ext; intros _ [r|] _; try reflexivity;
    cbn [compose]; exact (Hen r).
  - rewrite Hfdelt, Hgdelt.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity.
    apply list_fmap_ext; intros _ (l, u) _.
    cbn.
    destruct l, u; now rewrite ?Hen.
  - intros r.
    cbn;
    subst n;
    rewrite <- Hfsums;
    (destruct_decide (decide (Pos.of_succ_nat tl.(tl_sums) <= r)) as Hr;
    [now rewrite decide_True |
      now rewrite decide_False by
      now pose proof (posperm_bounded _ _ Hg r); lia]).
Qed.

Add Parametric Relation : tensorlist tl_aeq
  reflexivity proved by tl_aeq_refl
  symmetry proved by tl_aeq_symm
  transitivity proved by tl_aeq_trans
  as tl_aeq_setoid.

(* TODO: This ^ gives us the proper definition of semantic tensorexpr equality *)

(* TODO: Unused variables!!! *)

Arguments N.of_nat !_/.

Lemma tl_times_tlone_l tl : tl_times tlone tl = tl.
Proof.
  destruct tl as [sums abs delt]; cbn.
  erewrite list_fmap_id' by now
    intros; apply relabel_abs_id'; intros; apply relabel_bounds_id';
    intros; now case_decide.
  erewrite list_fmap_id' by now
    intros; apply relabel_delt_id'; intros; apply relabel_bounds_id';
    intros; now case_decide.
  reflexivity.
Qed.

Lemma tl_times_tlone_r tl : tl_times tl tlone = tl.
Proof.
  destruct tl as [sums abs delt]; cbn.
  erewrite list_fmap_id' by now
    intros; apply relabel_abs_id'; intros; apply relabel_bounds_id.
  erewrite list_fmap_id' by now
    intros; apply relabel_delt_id'; intros; apply relabel_bounds_id.
  rewrite Nat.add_0_r, 2 app_nil_r.
  reflexivity.
Qed.

Lemma tensorlist_of_tensorexpr_tproducts tes :
  tensorlist_of_tensorexpr (tproducts tes) =
  fold_right tl_times tlone (tensorlist_of_tensorexpr <$> tes).
Proof.
  induction tes as [|te tes IHtes]; [reflexivity|].
  cbn; congruence.
Qed.

(* Lemma tensorlist_of_tl_to_te_with_aux tes sums abs :
  tensorlist_of_tensorexpr (tl_to_te_with_aux tes sums abs) =
  tl_app_sums sums $
  fold_right tl_times (mk_tl [] abs) (tensorlist_of_tensorexpr <$> tes).
Proof.
  induction sums.
  - cbn.
    rewrite tensorlist_of_tensorexpr_tproducts.
    rewrite fmap_app, fold_right_app.
    f_equal.
    induction abs as [|((f, low), up)]; [reflexivity|cbn].
    rewrite IHabs.
    cbn.
    reflexivity.
  - cbn.
    now rewrite IHsums.
Qed. *)


Infix "=tl=" := tl_aeq (at level 70).

(* FIXME: Move *)
Lemma abs_fmap_l_ext {A} (idx : Idx) (f f' : A -> var) (low : list A) up up' :
  (f <$> low) ++ up = (f' <$> low) ++ up' ->
  (idx, f <$> low, up) = (idx, f' <$> low, up').
Proof.
  intros Heq%app_inj_len_l; [|now simpl_list].
  destruct Heq;
  congruence.
Qed.
Add Parametric Morphism {I A B} : (relabel_abs (I:=I)) with signature
  pointwise_relation A (@eq B) ==> eq ==>
  eq as relabel_abs_mor.
Proof.
  intros; now apply relabel_abs_ext.
Qed.


Lemma tl_times_comm_aeq tl tl' :
  tl_times tl tl' =tl= tl_times tl' tl.
Proof.
  (* rewrite 2 tl_times_spec_defn_correct. *)
  destruct tl as [lsums labs ldelt], tl' as [rsums rabs rdelt].
  cbn.
  eexists (pbig_swap rsums lsums); cbn -[reverse].
  split; [eapply pbig_swap_posperm'; lia|].
  split; [lia|].
  split.
  - rewrite Permutation_app_comm.
    rewrite fmap_app, <- 2 list_fmap_compose.
    apply Permutation_app.
    + apply eq_reflexivity, list_fmap_ext; intros _ flu _.
      cbn.
      rewrite relabel_abs_compose.
      apply relabel_abs_ext; intros [r|]; [|reflexivity].
      cbn.
      f_equal.
      unfold pbig_swap.
      repeat case_decide; lia.
    + apply eq_reflexivity, list_fmap_ext; intros _ flu _.
      cbn.
      rewrite relabel_abs_compose.
      apply relabel_abs_ext; intros [r|]; [|reflexivity].
      cbn.
      f_equal.
      unfold pbig_swap.
      repeat case_decide; lia.
  - rewrite Permutation_app_comm.
    rewrite fmap_app, <- 2 list_fmap_compose.
    apply Permutation_app.
    + apply eq_reflexivity, list_fmap_ext; intros _ lu _.
      cbn.
      rewrite relabel_delt_compose.
      apply relabel_delt_ext; intros [r|]; [|reflexivity].
      cbn.
      f_equal.
      unfold pbig_swap.
      repeat case_decide; lia.
    + apply eq_reflexivity, list_fmap_ext; intros _ lu _.
      cbn.
      rewrite relabel_delt_compose.
      apply relabel_delt_ext; intros [r|]; [|reflexivity].
      cbn.
      f_equal.
      unfold pbig_swap.
      repeat case_decide; lia.
Qed.

(* FIXME: Move *)
(* Lemma Pmap_posperm_of *)

Lemma map_inverses_empty `{FinMap A MA, FinMap B MB} :
  map_inverses (∅ :> MA B) (∅ :> MB A).
Proof.
  intros ? ?.
  rewrite 2 lookup_empty.
  easy.
Qed.


(* FIXME: Move!!!! *)
#[global] Instance var_inhabited : Inhabited var := populate (bound 1).


(*
(* FIXME: Move *)

Definition tl_well_bound (tl : tensorlist) : Prop :=
  abstracts_bound_vars tl.(tl_abstracts) ⊆
  list_to_set (pseq 1 (lengthN tl.(tl_sums))).

(* FIXME: Move*)


Add Parametric Morphism : mk_tl with signature
  eq ==> Permutation ==> tl_aeq as mk_tl_aeq_Permutation.
Proof.
  intros sums abs abs' Habs'.
  exists id.
  cbn.
  split; [apply posperm_id|].
  split; [apply ppermute_id|].
  rewrite Habs'.
  apply eq_reflexivity, symmetry, list_fmap_id'.
  intros x _.
  apply relabel_abs_id'.
  intros v.
  apply relabel_bounds_id'.
  intros; unfold make_pwf; case_decide; reflexivity.
Qed.



Lemma extend_match_of_abstract_tensors_correct'
  (P : Pmap Idx -> Pmap Idx -> Pmap var -> Pset ->
    list (Idx * list var * list var) -> Prop)
  `{HP : forall mb mbi ml mlran rrest, Decision (P mb mbi ml mlran rrest)}
  (labs rabs : list (Idx * list var * list var))
  mb' mbi' ml' mlran' rrest :

  extend_match_of_abstract_tensors P ∅ ∅ ∅ ∅ labs rabs =
    Some (mb', mbi', ml', mlran', rrest) ->

  P mb' mbi' ml' mlran' rrest /\
  map_inverses mb' mbi' /\
  dom mb' = abstracts_bound_vars labs /\
  dom mbi' ⊆ abstracts_bound_vars rabs /\
  map_img ml' ⊆ abstracts_vars rabs /\
  set_Forall (λ r, mbi' !! r = None) mlran' /\
  map_img (omap v2bound ml') = mlran' /\
  dom ml' = abstracts_free_vars labs /\
  (relabel_abs (var_elim (fmap bound ∘ (mb' !!.)) (ml' !!.)
     (λ g, Some (glob g))) <$> labs) ++
     (relabel_abs Some <$> rrest) ≡ₚ relabel_abs Some <$> rabs /\
  (relabel_abs (var_elim (bound ∘ (mb' !!!.)) (ml' !!!.)
     (glob)) <$> labs) ++
     rrest ≡ₚ rabs /\
  forall a,
    a ∈ labs
    → relabel_abs
        (var_elim (fmap bound ∘ λ i : Idx, mb' !! i)
           (λ i : Idx, ml' !! i) (λ g : Idx, Some (glob g))) a
      ∈ relabel_abs Some <$> rabs.
Proof.
  intros Heq.
  apply extend_match_of_abstract_tensors_correct in Heq;
  [|apply map_inverses_empty|apply set_Forall_empty|reflexivity].
  assert (Hsubs :
    (relabel_abs
     (var_elim (fmap bound ∘ λ i : Idx, mb' !! i)
        (λ i : Idx, ml' !! i) (λ g : Idx, Some (glob g))) <$> labs) ⊆
        relabel_abs Some <$> rabs). 1: {
      intros x Hx.
    rewrite <- Heq.2.2.2.2.2.2.2.2.2, elem_of_app; now left.
    }
  pose proof (fun x Hx => Hsubs _ (elem_of_list_fmap_1 _ labs x Hx)) as Hsubs'.
  rewrite 2 dom_empty_L, 2 union_empty_l_L in Heq.
  split_and!; [..|solve [auto]]; try apply Heq;
  destruct Heq as (_ & _ & _ & _ & Hinvs & Hdom & Hdisjl & Himg & Hldom & Heq).
  - intros q (p & Hp)%elem_of_dom.
    apply Hinvs in Hp as Hp'.

    (* pose proof (fun x => elem_of_Permutation_proper x _ _ Heq) as Heq'. *)
    apply elem_of_dom_2 in Hp' as Hpdom.
    rewrite Hdom in Hpdom.
    set_unfold in Hpdom.
    destruct Hpdom as (a & Hpa & Ha).
    apply Hsubs' in Ha as Ha'.
    apply elem_of_list_fmap in Ha' as (x & Hx & Hxrabs).
    unfold abstracts_bound_vars.
    apply elem_of_list_to_set, elem_of_list_bind.
    exists x.
    split; [|easy].
    destruct a as ((idx, low), up), x as ((idx', low'), up').
    cbn in Hx.
    rewrite elem_of_list_omap.
    exists (bound q).
    split; [|reflexivity].
    revert Hx.
    intros [= <- Hl Hu].
    rewrite elem_of_app.
    apply elem_of_list_omap in Hpa
      as ([] & [Hpl|Hpu]%elem_of_app & [= ->]).
    + left.
      apply elem_of_list_lookup in Hpl as (i & Hi).
      apply (f_equal (.!! i)) in Hl.
      rewrite 2 list_lookup_fmap, Hi in Hl.
      cbn in Hl.
      rewrite Hp' in Hl.
      cbn in Hl.
      apply elem_of_list_lookup.
      exists i.
      destruct (low' !! i); cbn in Hl; congruence.
    + right.
      apply elem_of_list_lookup in Hpu as (i & Hi).
      apply (f_equal (.!! i)) in Hu.
      rewrite 2 list_lookup_fmap, Hi in Hu.
      cbn in Hu.
      rewrite Hp' in Hu.
      cbn in Hu.
      apply elem_of_list_lookup.
      exists i.
      destruct (up' !! i); cbn in Hu; congruence.
  - intros v (l & Hl)%elem_of_map_img.
    apply elem_of_dom_2 in Hl as Hl'.
    rewrite Hldom in Hl'.
    apply elem_of_list_to_set, elem_of_list_bind in Hl' as (a & Hla & Ha).
    apply Hsubs' in Ha.
    apply elem_of_list_fmap in Ha as (b & Hab & Hb).
    apply elem_of_list_to_set, elem_of_list_bind.
    exists b.
    split; [|easy].
    destruct a as ((idx, low), up), b as ((idx', low'), up').
    cbn in Hab.
    revert Hab.
    intros [= <- Hlow Hup].
    apply elem_of_app.
    apply elem_of_list_omap in Hla as
      ([|_|] & [Hll|Hlu]%elem_of_app & [= ->]).
    + left.
      apply elem_of_list_lookup in Hll as (i & Hi).
      apply (f_equal (.!! i)) in Hlow.
      rewrite 2 list_lookup_fmap, Hi in Hlow.
      cbn in Hlow.
      apply elem_of_list_lookup.
      exists i.
      destruct (low' !! i); cbn in *; congruence.
    + right.
      apply elem_of_list_lookup in Hlu as (i & Hi).
      apply (f_equal (.!! i)) in Hup.
      rewrite 2 list_lookup_fmap, Hi in Hup.
      cbn in Hup.
      apply elem_of_list_lookup.
      exists i.
      destruct (up' !! i); cbn in *; congruence.
  - apply (fmap_Permutation (relabel_abs (default (bound 1)))) in Heq
      as Hdecomp'.
    rewrite <- list_fmap_compose in Hdecomp'.
    rewrite (list_fmap_id' (_ ∘ _)) in Hdecomp'. 2:{
      intros abs _.
      unfold compose.
      rewrite relabel_abs_compose.
      apply relabel_abs_id.
    }
    rewrite <- Hdecomp'.
    rewrite fmap_app, <- 2 list_fmap_compose.
    unfold compose at 1.
    symmetry.
    erewrite list_fmap_ext by now intros; apply relabel_abs_compose.
    erewrite (list_fmap_ext (_ ∘ _)) by now
      intros; unfold compose; rewrite relabel_abs_compose; apply relabel_abs_id.
    rewrite list_fmap_id.
    apply eq_reflexivity.
    f_equal.
    apply list_fmap_ext.
    intros _ a _.
    apply relabel_abs_ext.
    intros [r|l|g]; [|reflexivity..].
    cbn; rewrite lookup_total_alt.
    destruct (_ !! _); reflexivity.
Qed.

Lemma map_inverses_comm `{Lookup A B MA, Lookup B A MB} (ma : MA) (mb : MB) :
  map_inverses ma mb <-> map_inverses mb ma.
Proof.
  unfold map_inverses. firstorder.
Qed.

Lemma map_inverses_card_img `{FinMapDom A MA SA, !Elements A SA,
  !FinSet A SA, FinMap B MB, FinSet B SB, !boundDecision (∈@{SB}) }
  (ma : MA B) (mb : MB A) :
  map_inverses ma mb ->
  size (dom ma :> SA) = size (map_img ma :> SB).
Proof.
  intros Hinv.
  rewrite map_dom_img_eq_card_iff_inj.
  intros ? ? ? ?%Hinv ?%Hinv.
  congruence.
Qed.

Lemma map_inverses_img `{FinMap A MA, FinMapDom B MB SB}
  (ma : MA B) (mb : MB A) :
    map_inverses ma mb ->
    map_img ma ≡@{SB} dom mb.
Proof.
  intros Hab x.
  rewrite elem_of_map_img, elem_of_dom.
  setoid_rewrite (fun x => Hab x).
  reflexivity.
Qed.


Lemma map_inverses_img_L `{FinMap A MA, FinMapDom B MB SB, !LeibnizEquiv SB}
  (ma : MA B) (mb : MB A) :
    map_inverses ma mb ->
    map_img ma =@{SB} dom mb.
Proof.
  unfold_leibniz.
  apply map_inverses_img.
Qed.

Definition tl_well_typed_aux tc sums abs :=
  let tc' := tc_app_types (reverse sums) tc in
  Forall (fun '(f, low, up) =>
  fmap Some <$> tc_ma tc' !! f = Some (tc_get_var tc' <$> low ++ up)) abs.

Notation tl_well_typed tc tl :=
    (tl_well_typed_aux tc tl.(tl_sums) tl.(tl_abstracts)).

Lemma well_typed_tproducts tc tes :
  well_typed tc (tproducts tes) <-> Forall (well_typed tc) tes.
Proof.
  induction tes; [naive_solver|].
  rewrite Forall_cons, <- IHtes.
  cbn.
  destruct tes; naive_solver.
Qed.

Lemma tl_well_typed_correct tc tl :
  tl_well_typed tc tl <-> well_typed tc tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  revert tc; induction sums; intros tc.
  - cbn.
    rewrite well_typed_tproducts.
    unfold tl_well_typed_aux.
    rewrite Forall_fmap.
    apply Forall_iff.
    intros ((f, low), up).
    cbn.
    now destruct tc.
  - cbn.
    rewrite <- IHsums.
    unfold tl_well_typed_aux.
    destruct tc; unfold tc_app_types; rewrite reverse_cons; cbn.
    rewrite <- app_assoc.
    reflexivity.
Qed.



Lemma extend_match_of_abstract_tensors_correct_WT_pre
  (P : Pmap Idx -> Pmap Idx -> Pmap var -> Pset ->
    list (Idx * list var * list var) -> Prop)
  `{HP : forall mb mbi ml mlran rrest, Decision (P mb mbi ml mlran rrest)}
  (labs rabs : list (Idx * list var * list var))
  mb' mbi' ml' mlran' rrest :

  extend_match_of_abstract_tensors P ∅ ∅ ∅ ∅ labs rabs =
    Some (mb', mbi', ml', mlran', rrest) ->
  forall tc univ lsums rsums,
  tl_well_typed_aux (tc_eqn_with_frees tc univ) lsums labs ->
  tl_well_typed_aux tc rsums rabs ->
  (forall l ty v, univ !! l = Some ty -> ml' !! l = Some v ->
    tc_get_var (tc_app_types (reverse rsums) tc) v = Some ty) /\
  (forall (r r' : Idx) ty, reverse lsums !! (r:>nat) = Some ty ->
    mb' !! r = Some r' -> (reverse rsums ++ tc.(tc_mr)) !! (r':>nat) = Some ty).
Proof.
  intros Hext tc univ lsums rsums Hl Hr.
  apply extend_match_of_abstract_tensors_correct' in Hext as
    (_ & Hinvs & Hdom_mb & Hdom_mbi & Hlimg & Hldisj & Hmlran
      & Hdomml & Hpermeq & Hperm & Hsubs).
  split.
  - intros l ty v Hty_univ Hml'_v.
    apply elem_of_dom_2 in Hml'_v as Hv.
    rewrite Hdomml in Hv.
    apply elem_of_abstracts_free_vars in Hv as (idx & low & up & Hinl & Hl_lu).
    apply Hsubs in Hinl as Hlu_r.
    cbn in Hlu_r.
    apply elem_of_list_fmap in Hlu_r as (((idx', low'), up') & Heq & Hinr).
    cbn in Heq.
    revert Heq.
    intros [= <- Hlow Hup].
    hnf in Hr, Hl.
    rewrite Forall_forall in Hr, Hl.
    specialize (Hr _ Hinr).
    specialize (Hl _ Hinl).
    cbn in Hr, Hl.
    generalize (f_equal2 app Hlow Hup).
    rewrite <- 2 fmap_app.
    intros Hlowup.
    remember (low ++ up) as lowup eqn:Hlowup_eq.
    remember (low' ++ up') as lowup' eqn:Hlowup'_eq.
    apply elem_of_list_lookup in Hl_lu as (i & Hi).
    apply (f_equal (.!! i)) in Hlowup.
    rewrite 2 list_lookup_fmap, Hi in Hlowup.
    cbn in Hlowup.
    rewrite Hml'_v in Hlowup.
    destruct (lowup' !! i) as [?|] eqn:Hlowup'_i; [|easy].
    cbn in Hlowup.
    revert Hlowup.
    intros [= <-].
    apply (f_equal (λ ml, (.!! i) <$> ml)) in Hl, Hr.
    cbn in Hl, Hr.
    rewrite Hl in Hr.
    rewrite 2 list_lookup_fmap in Hr.
    rewrite Hi, Hlowup'_i in Hr.
    cbn in Hr.
    injection Hr.
    intros <-.
    rewrite lookup_union, Hty_univ.
    now rewrite union_Some_l.
  - intros r r' ty Hl_r Hmb_r.
    apply elem_of_dom_2 in Hmb_r as Hrdom.
    rewrite Hdom_mb in Hrdom.
    apply elem_of_abstracts_bound_vars in Hrdom as (idx & low & up & Hinl & Hl_lu).
    apply Hsubs in Hinl as Hlu_r.
    cbn in Hlu_r.
    apply elem_of_list_fmap in Hlu_r as (((idx', low'), up') & Heq & Hinr).
    cbn in Heq.
    revert Heq.
    intros [= <- Hlow Hup].
    hnf in Hr, Hl.
    rewrite Forall_forall in Hr, Hl.
    specialize (Hr _ Hinr).
    specialize (Hl _ Hinl).
    cbn in Hr, Hl.
    generalize (f_equal2 app Hlow Hup).
    rewrite <- 2 fmap_app.
    intros Hlowup.
    remember (low ++ up) as lowup eqn:Hlowup_eq.
    remember (low' ++ up') as lowup' eqn:Hlowup'_eq.
    apply elem_of_list_lookup in Hl_lu as (i & Hi).
    apply (f_equal (.!! i)) in Hlowup.
    rewrite 2 list_lookup_fmap, Hi in Hlowup.
    cbn in Hlowup.
    rewrite Hmb_r in Hlowup.
    destruct (lowup' !! i) as [?|] eqn:Hlowup'_i; [|easy].
    cbn in Hlowup.
    revert Hlowup.
    intros [= <-].
    apply (f_equal (λ ml, (.!! i) <$> ml)) in Hl, Hr.
    cbn in Hl, Hr.
    rewrite Hl in Hr.
    rewrite 2 list_lookup_fmap in Hr.
    rewrite Hi, Hlowup'_i in Hr.
    cbn in Hr.
    injection Hr.
    rewrite app_nil_r.
    intros <-.
    easy.
Qed.

Lemma tl_well_typed_well_bound mabs mg ml tl :
  tl_well_typed (mk_tc mabs mg ml []) tl ->
  tl_well_bound tl.
Proof.
  intros HWT.
  hnf in HWT |- *.
  intros r (idx & low & up & Hlu_in & Hin_lu)%elem_of_abstracts_bound_vars.
  rewrite Forall_forall in HWT.
  specialize (HWT _ Hlu_in).
  cbn in HWT.
  apply elem_of_list_lookup in Hin_lu as (i & Hi).
  apply (f_equal (λ ml, (.!! i) <$> ml)) in HWT.
  revert HWT.
  cbn.
  destruct (mabs !! idx) as [tys|]; [|easy].
  cbn.
  rewrite 2 list_lookup_fmap, Hi.
  cbn.
  rewrite app_nil_r.
  destruct (tys !! i) as [tyi|]; [|easy].
  cbn.
  intros [= Heq%eq_sym%lookup_lt_Some].
  rewrite length_reverse in Heq.
  rewrite lengthN_correct_rev, elem_of_list_to_set, elem_of_pseq_1.
  lia.
Qed.



Lemma tl_well_typed_aux_mono mabs mg ml mabs' mg' ml' mr sums abs :
  mabs ⊆ mabs' -> mg ⊆ mg' -> ml ⊆ ml' ->
  tl_well_typed_aux (mk_tc mabs mg ml mr) sums abs ->
  tl_well_typed_aux (mk_tc mabs' mg' ml' mr) sums abs.
Proof.
  intros Habs Hg Hl.
  intros Hall.
  eapply Forall_impl; [exact Hall|].
  intros ((f, low), up).
  cbn.
  destruct (mabs !! f) as [mf|] eqn:Hmf; [|easy].
  eapply lookup_weaken in Hmf as Hm'f; [|eassumption].
  rewrite Hm'f.
  cbn.
  intros [= HSmf].
  f_equal.
  apply (list_eq_same_length _ _ _ eq_refl);
    [apply (f_equal length) in HSmf; now rewrite ?length_fmap in *|].
  rewrite length_fmap.
  intros i x y Hi.
  rewrite 2 list_lookup_fmap.
  destruct (mf !! i) as [mfi|] eqn:Hmfi; [|easy].
  cbn.
  intros [= <-].
  apply (f_equal (.!! i)) in HSmf.
  rewrite 2 list_lookup_fmap, Hmfi in HSmf.
  cbn in HSmf.
  destruct ((low ++ up) !! i) as [v|] eqn:Hv; [cbn|easy].
  intros [= <-].
  cbn in HSmf.
  revert HSmf.
  intros [= Heq].
  destruct v as [r|l|g]; cbn in *;
  [easy|symmetry in Heq |- *; eapply lookup_weaken; eassumption..].
Qed.






Lemma elem_of_abstracts_vars v abs :
  v ∈ abstracts_vars abs <-> exists idx low up,
    (idx, low, up) ∈ abs /\ v ∈ low ++ up.
Proof.
  set_unfold.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_app.
  firstorder.
Qed.

Lemma elem_of_abstracts_vars_bound r abs :
  bound r ∈ abstracts_vars abs <-> r ∈ abstracts_bound_vars abs.
Proof.
  now rewrite elem_of_abstracts_bound_vars, elem_of_abstracts_vars.
Qed.

Lemma elem_of_abstracts_vars_free r abs :
  free r ∈ abstracts_vars abs <-> r ∈ abstracts_free_vars abs.
Proof.
  now rewrite elem_of_abstracts_free_vars, elem_of_abstracts_vars.
Qed.

Lemma elem_of_abstracts_vars_glob r abs :
  glob r ∈ abstracts_vars abs <-> r ∈ abstracts_global_vars abs.
Proof.
  now rewrite elem_of_abstracts_global_vars, elem_of_abstracts_vars.
Qed.

Lemma and_exists_l {A} {P Q} : (P /\ exists a : A, Q a) <->
  exists a, P /\ Q a.
Proof.
  firstorder.
Qed.


Lemma match_tensorlist_aux_correct mabs mg univ univ' lhs targ utl boundmap freemap :
  match_tensorlist_aux lhs targ = Some (utl, boundmap, freemap) ->
  all_bound lhs ->
  tl_well_typed (mk_tc mabs mg univ []) lhs ->
  tl_well_typed (mk_tc mabs mg univ' []) targ ->
  (* tl_well_bound targ -> *)
  abstracts_free_vars lhs.(tl_abstracts) = dom freemap /\
  (forall l ty v, univ !! l = Some ty -> freemap !! l = Some v ->
    tc_get_var (mk_tc mabs mg univ' (reverse utl.(tl_sums))) v = Some ty) /\
  targ =tl= fill_tensorlist_rewrite utl lhs boundmap freemap.
Proof.
  cbv delta [match_tensorlist_aux] beta.
  destruct (extend_match_of_abstract_tensors _ _ _ _ _ _ _)
    as [((((mb, mbi), ml), mlran), rrest)|] eqn:Hext; [|intros [=]].
  pose proof Hext as Hext'.
  intros Heq.
  apply (inj Some) in Heq.
  revert Heq.
  cbv zeta.
  set (ntys := imap _ (reverse _)).
  set (unused_tys := filter _ ntys).
  set (newty_info := imap _ unused_tys).
  set (rrest_map := list_to_map _).
  set (newtys := reverse _).
  set (ml' := relabel_bounds _ <$> ml).
  intros [= <- <- <-].
  intros Hlhs Htylhs Htytarg.
  apply tl_well_typed_well_bound in Htytarg as Htarg.

  apply extend_match_of_abstract_tensors_correct' in Hext as
    (Hrestdisj & Hinvs & Hdom & Hdommbi & Hlimg & Hldisj & Hmlran &
      Hldom & Hdecomp & Hperm & Hsubs).
  destruct targ as [tsums tabs], lhs as [rsums rabs].
  unfold all_bound, tl_well_bound in Hlhs, Htarg.
  cbn [tl_sums tl_abstracts] in *.
  split. 1:{
    unfold ml'.
    rewrite dom_fmap_L.
    auto.
  }

  assert (Hlenlt : (length rsums <= length tsums)%nat). 1:{
    apply (map_inverses_card_img (SB:=Pset)) in Hinvs as Hcard.
    rewrite Hdom in Hcard.
    rewrite Hlhs in Hcard.
    rewrite size_list_to_set, length_pseq, lengthN_correct
      in Hcard by apply NoDup_pseq.
    rewrite map_inverses_img in Hcard by eassumption.
    rewrite Hcard.
    eapply Nat.le_trans;
    [apply subseteq_size, Hdommbi|].
    rewrite <- lengthN_correct, <- (length_pseq 1),
      <- (size_list_to_set (C:=Pset))
      by apply NoDup_pseq.
    apply subseteq_size.
    apply Htarg.
  }

  assert (Hdommbi' : dom mbi =
    list_to_set (filter (λ '(idx, _), is_Some (mbi !! idx)) ntys).*1). 1:{

    setoid_rewrite <- leibniz_equiv_iff.
    intros x.
    rewrite elem_of_dom.
    rewrite elem_of_list_to_set, elem_of_list_fmap.
    setoid_rewrite elem_of_list_filter.
    unfold ntys.
    setoid_rewrite elem_of_lookup_imap.
    split; cycle 1.
    + intros ([] & -> & Hsome & _).
      apply Hsome.
    + intros Hx.
      rewrite Htarg in Hdommbi.
      specialize (Hdommbi x ltac:(now apply elem_of_dom))
        as Hxlt%elem_of_list_to_set%elem_of_pseq_1.
      specialize (lookup_lt_is_Some (reverse tsums) x).2 as Hlx.
      tspecialize Hlx by now rewrite length_reverse, <- lengthN_correct; lia.
      destruct Hlx as [rx Hrx].
      exists (x, rx).
      split; [easy|].
      split; [easy|].
      exists x, rx.
      split; [f_equal; lia|].
      apply Hrx.
  }

  assert (HNoDup_fsts_filter :
    NoDup (filter (λ '(idx, _), is_Some (mbi !! idx)) ntys).*1). 1:{

    eapply (fun H => ((NoDup_app _ _).1 H).1).
    rewrite <- fmap_app.
    rewrite filter_with_neg_Permutation.
    unfold ntys.
    rewrite fmap_imap.
    unfold compose.
    cbn.
    rewrite imap_seq_0.
    apply NoDup_fmap_2; [hnf; clear; lia|].
    apply NoDup_seq.
  }

  assert (HNoDup_fsts_filter' :
    NoDup (filter (λ '(idx, _), ¬ is_Some (mbi !! idx)) ntys).*1). 1:{

    eapply (fun H => ((NoDup_app _ _).1 H).1).
    rewrite <- fmap_app.
    rewrite filter_with_neg_Permutation.
    unfold ntys.
    rewrite fmap_imap.
    unfold compose.
    cbn.
    rewrite imap_seq_0.
    apply NoDup_fmap_2; [hnf; clear; lia|].
    apply NoDup_seq.
  }

  assert (Hlens : (length rsums + length unused_tys = length tsums)%nat). 1:{
    transitivity (length ntys);
    [|subst ntys; now rewrite length_imap, length_reverse].

    erewrite <- (filter_neg_with_Permutation (P:=λ '(idx, _), is_Some (mbi !! idx)) ntys).
    rewrite length_app, Nat.add_comm.
    f_equal; [f_equal; apply list_filter_iff; now intros []|].

    apply (map_inverses_card_img (SB:=Pset)) in Hinvs as Hcard.
    rewrite Hdom in Hcard.
    rewrite Hlhs in Hcard.
    rewrite size_list_to_set, length_pseq, lengthN_correct
      in Hcard by apply NoDup_pseq.
    rewrite map_inverses_img in Hcard by eassumption.
    rewrite Hcard.
    rewrite <- (length_fmap fst).
    rewrite <- (size_list_to_set (C:=Pset)) by easy.
    f_equal.
    assumption.
  }

  rewrite <- Hperm.

  cbv delta [fill_tensorlist_rewrite] beta match zeta.
  set (shift := relabel_bounds _).
  rewrite Permutation_app_comm.


  assert (Hnewty_info_alt :
    newty_info = imap (λ inew iold_ty,
      (iold_ty.1, Pos.of_succ_nat inew, iold_ty.2)) unused_tys). 1:{
    apply imap_ext; now intros ? [].
  }

  assert (HNoDup_newty_info_1_1 : NoDup newty_info.*1.*1). 1:{
    rewrite Hnewty_info_alt.
    rewrite 2 fmap_imap.
    unfold compose; cbn.
    rewrite imap_to_fmap.
    unfold unused_tys.
    apply HNoDup_fsts_filter'.
  }


  set (used_tys := filter (λ '(idx, _), is_Some (mbi !! idx)) ntys).
  set (oldty_info := imap (λ inew '(iold, ty), (iold, Pos.of_succ_nat inew, ty))
    used_tys).
  set (rrest_inv_map := list_to_map (prod_swap <$> newty_info.*1) :> Pmap Idx).


  pose proof (lengthN_correct tsums).
  pose proof (lengthN_correct rsums).
  pose proof (lengthN_correct unused_tys).

  assert (Hrrest_inv_inv : forall x, x ∈ abstracts_bound_vars tabs ->
    ¬ (is_Some (mbi !! x)) ->
    (if decide (Pmap_map rrest_map x < lengthP unused_tys)
    then rrest_inv_map !!! Pmap_map rrest_map x
    else pos_add_N (Pmap_map rrest_map x) (lengthN rsums)) = x). 1:{
      clear Hrestdisj.
      intros x Hx_rrest Hrestdisj.
      assert (Hxdom : x ∈ dom rrest_map). 1:{
        unfold rrest_map.
        rewrite dom_list_to_map_L, elem_of_list_to_set.
        unfold newty_info.
        rewrite 2 fmap_imap.
        unfold compose.
        rewrite (imap_ext _ (λ _ x, x.1)) by now intros ? [].
        rewrite imap_to_fmap.
        unfold unused_tys.
        rewrite elem_of_list_fmap.
        cbn in Hrestdisj.
        assert (Hxtys : ((x :> nat) < length tsums)%nat). 1:{
          apply Htarg, elem_of_list_to_set, elem_of_pseq_1 in Hx_rrest; lia.
        }
        rewrite <- length_reverse in Hxtys.
        apply lookup_lt_is_Some in Hxtys as Htx.
        destruct Htx as [tx Htx].
        exists (x, tx).
        split; [reflexivity|].
        apply elem_of_list_filter.
        split; [easy|].
        unfold ntys.
        apply elem_of_lookup_imap.
        exists x, tx.
        split; [f_equal; lia|].
        easy.
      }
      apply elem_of_dom in Hxdom as [rx Hrx].
      unfold Pmap_map.
      rewrite Hrx; cbn.
      rewrite decide_True. 2:{
        unfold rrest_map in Hrx.
        rewrite <- elem_of_list_to_map in Hrx by easy.
        apply elem_of_list_fmap in Hrx as ((? & ty) & Hsubst & Hin_newty_info).
        cbn in Hsubst.
        revert Hsubst.
        intros <-.
        rewrite Hnewty_info_alt in Hin_newty_info.
        apply elem_of_lookup_imap in Hin_newty_info as (idx & [] & [= <- Hidxeq <-] & Hidx).
        apply lookup_lt_Some in Hidx.
        lia.
      }
      apply lookup_total_correct.
      apply elem_of_list_to_map. 1:{
        rewrite fsts_prod_swap.
        rewrite Hnewty_info_alt.
        rewrite 2 fmap_imap.
        unfold compose.
        cbn.
        rewrite imap_seq_0.
        apply NoDup_fmap_2; [hnf; lia|].
        apply NoDup_seq.
      }
      rewrite elem_of_list_fmap.
      exists (x, rx).
      split; [reflexivity|].
      unfold rrest_map in Hrx.
      rewrite <- elem_of_list_to_map in Hrx by easy.
      easy.
  }

  pose proof (extend_match_of_abstract_tensors_correct_WT_pre
    _ _ _ _ _ _ _ _ Hext') as HWT.
  specialize (HWT (mk_tc mabs mg univ' []) univ rsums tsums).
  unfold tc_eqn_with_frees in HWT.
  cbn in HWT.

  specialize (fun H => HWT H Htytarg).
  tspecialize HWT. 1:{
    eapply tl_well_typed_aux_mono; try eassumption; [reflexivity..|].
    apply map_union_subseteq_l.
  }
  rewrite (unfold tc_app_types), 2 app_nil_r in HWT.
  cbn in HWT.
  split. 1:{
    unfold ml'.
    intros l ty v Huniv_l.
    rewrite lookup_fmap.
    destruct (ml !! l) as [[r| |]|] eqn:Hml_l; [|
    cbn; intros [= <-];
    apply (HWT.1 l ty _ Huniv_l Hml_l)..|easy].
    cbn.
    intros [= <-].
    cbn.
    unfold newtys.
    rewrite reverse_involutive.
    rewrite list_lookup_fmap.
    assert (Hrran : r ∈ mlran). 1:{
      subst mlran.
      rewrite elem_of_map_img.
      exists l.
      rewrite lookup_omap, Hml_l.
      reflexivity.
    }
    assert (Hrdom : r ∈ dom (rrest_map)). 1:{
      unfold rrest_map.
      rewrite dom_list_to_map, elem_of_list_to_set.
      rewrite Hnewty_info_alt.
      rewrite 2 fmap_imap.
      unfold compose.
      cbn.
      rewrite imap_to_fmap.
      unfold unused_tys.
      rewrite elem_of_list_fmap.
      assert (Hnmbi : ¬ is_Some (mbi !! r)) by now rewrite Hldisj.
      assert (Hrlt : ((r:>nat) < length tsums)%nat). 1:{
        specialize (Hlimg (bound r)) as Hrvar.
        tspecialize Hrvar by now apply elem_of_map_img; eauto.
        rewrite elem_of_abstracts_vars_bound in Hrvar.
        apply Htarg in Hrvar.
        rewrite elem_of_list_to_set, elem_of_pseq_1 in Hrvar.
        lia.
      }
      rewrite <- length_reverse in Hrlt.
      apply lookup_lt_is_Some in Hrlt as Hlook.
      destruct Hlook as [rtr Hrtr].
      exists (r, rtr).
      split; [easy|].
      rewrite elem_of_list_filter.
      split; [easy|].
      apply elem_of_lookup_imap.
      exists r, rtr.
      split; [f_equal; lia|].
      easy.
    }
    apply elem_of_dom in Hrdom as Hrr.
    destruct Hrr as [rr_r Hrr_r].
    unfold Pmap_map.
    rewrite Hrr_r.
    cbn.
    (* unfold newty_info.
    rewrite list_lookup_imap.
    unfold unused_tys.
    unfold rrest_map in Hrr_r. *)
    apply elem_of_list_to_map in Hrr_r; [|easy].
    apply elem_of_list_fmap in Hrr_r as (((_, _), ty') & [= <- <-] & Hin_nti).
    rewrite Hnewty_info_alt in Hin_nti |- *.
    rewrite elem_of_lookup_imap in Hin_nti.
    destruct Hin_nti as (idx & (_, _) & [= <- -> <-] & Hlook).
    rewrite list_lookup_imap.
    rewrite pos_to_nat_pred_of_nat.
    rewrite Hlook.
    cbn.
    specialize (HWT.1 l ty (bound r) Huniv_l Hml_l) as HWT'.
    cbn in HWT'.
    unfold unused_tys in Hlook.
    apply elem_of_list_lookup_2 in Hlook as
      (Hnsome & (i & _ & [= -> <-] & Hlook)%elem_of_lookup_imap)%elem_of_list_filter.
    rewrite pos_to_nat_pred_of_nat in *.
    congruence.
  }





  (* exists (λ p, default _ (mbi) ) *)
  (* symmetry. *)
  exists (λ p, if decide (p < lengthP rsums) then
    mb !!! p
      else rrest_inv_map !!! (pos_sub_N p (lengthN rsums))).
  cbn [tl_sums tl_abstracts] in *.



  apply and_from_l, conj; [|intros Hpperm; apply and_from_l, conj;
    [|intros Hppermute]].
  - apply surj_is_posperm.
    intros p Hp.
    destruct_decide (decide (is_Some (mbi !! p))) as Hpbnd.
    + destruct Hpbnd as [q Hq].
      exists q.
      apply Hinvs in Hq as Hq'.
      apply elem_of_dom_2 in Hq' as Hqdom.
      rewrite Hdom, Hlhs, elem_of_list_to_set, elem_of_pseq_1 in Hqdom.
      split; [lia|].
      rewrite decide_True by easy.
      now apply lookup_total_correct.
    + assert (Hunu : (p, (reverse tsums) !!! (p:>nat)) ∈ unused_tys). 1:{
        apply elem_of_list_filter.
        split; [easy|].
        apply elem_of_list_lookup.
        exists p.
        unfold ntys.
        rewrite list_lookup_imap.
        pose proof (lookup_lt_is_Some (reverse tsums) p).2 as Hsome.
        tspecialize Hsome by now rewrite length_reverse; lia.
        rewrite list_lookup_total_alt.
        destruct Hsome as [? ->].
        cbn.
        do 2 f_equal; lia.
      }
      apply elem_of_list_lookup in Hunu as (i & Hi).
      exists (pos_add_N (Pos.of_succ_nat i) (lengthN rsums))%nat.
      rewrite decide_False by lia.
      replace (pos_sub_N _ _) with (Pos.of_succ_nat i) by lia.
      unfold rrest_inv_map.
      split; [apply lookup_lt_Some in Hi;
      pose proof (lengthN_correct unused_tys); lia|].
      apply lookup_total_correct.
      apply elem_of_list_to_map.
      * rewrite fsts_prod_swap.
        unfold newty_info.
        rewrite imap_to_zip_with_seq.
        rewrite 2 fmap_zip_with.
        replace (zip_with _ _ _) with (pseq 1 (lengthN unused_tys));
          [apply NoDup_pseq|].
        apply (fun H => list_eq_same_length _ _ _ H eq_refl);
          [rewrite length_zip_with, length_pseq, lengthN_correct, length_seq;
            apply Nat.min_id|].
        rewrite length_pseq, lengthN_correct.
        pose proof (lengthN_correct unused_tys).
        intros j x y Hj.
        rewrite lookup_pseq_1_lt by lia.
        intros [= <-].
        rewrite lookup_zip_with, lookup_seq_lt by lia.
        cbn.
        destruct (unused_tys !! j) as [[]|]; [|easy].
        cbn.
        now intros [= <-].
      * rewrite elem_of_list_fmap.
        exists (p, Pos.of_succ_nat i).
        split; [reflexivity|].
        apply elem_of_list_lookup.
        exists i.
        rewrite list_lookup_fmap.
        unfold newty_info.
        rewrite list_lookup_imap, Hi.
        reflexivity.
  - apply (fun H => list_eq_same_length _ _ _ H eq_refl);
    rewrite length_ppermute. 1:{
      rewrite 2 length_reverse, length_app.
      rewrite <- Hlens, Nat.add_comm.
      f_equal.
      unfold newtys, newty_info.
      now rewrite length_reverse, length_fmap, length_imap.
    }
    intros i x y Hi.
    rewrite lookup_ppermute_alt_bdd by
      (easy + apply posperm_bounded; now rewrite lengthN_reverse).
    rewrite reverse_app.
    case_decide as Hsmall.
    + rewrite lookup_app_l by now rewrite length_reverse; lia.
      assert (Hidom : Pos.of_succ_nat i ∈ dom mb). 1:{
        rewrite Hdom, Hlhs, elem_of_list_to_set, elem_of_pseq_1; lia.
      }
      apply elem_of_dom in Hidom as [mb_i Hmb_i].
      rewrite lookup_total_alt, Hmb_i.
      cbn.
      intros Ht_mb_i Hr_i.
      specialize (HWT.2 (Pos.of_succ_nat i) mb_i y) as Heq.
      rewrite pos_to_nat_pred_of_nat in Heq.
      specialize (Heq Hr_i Hmb_i).
      congruence.
    + rewrite lookup_app_r by now rewrite !length_reverse; lia.
      rewrite length_reverse.
      unfold rrest_inv_map.
      unfold newtys.
      rewrite reverse_involutive.
      unfold newty_info at 1.
      rewrite 2 fmap_imap.
      unfold compose; cbn.
      erewrite (imap_ext _ (λ inew iold_ty,
        (Pos.of_succ_nat inew, iold_ty.1))). 2:{
        intros ? []; reflexivity.
      }
      rewrite lookup_total_alt.
      rewrite lookup_list_to_map_imap_to_pos.
      replace (pos_to_nat_pred (pos_sub_N _ _)) with (i - length rsums)%nat by lia.
      unfold newty_info.
      rewrite list_lookup_fmap.
      rewrite list_lookup_imap.
      destruct (unused_tys !! _) as [[iold ity]|] eqn:Heq; [|easy].
      cbn.
      unfold unused_tys in Heq.
      apply elem_of_list_lookup_2 in Heq as [Hnmbi Helem]%elem_of_list_filter.
      unfold ntys in Helem.
      apply elem_of_lookup_imap in Helem as (iold' & ity' & [= -> <-] & Hlook).
      rewrite pos_to_nat_pred_of_nat.
      congruence.
  - rewrite fmap_app.
    apply Permutation_app.
    + symmetry.
      rewrite <- 2 list_fmap_compose.
      apply eq_reflexivity.
      apply list_fmap_id'.
      intros ((f, low), up) Hlu_rrest.
      unfold compose.
      rewrite 2 relabel_abs_compose.
      apply relabel_abs_id_strong.
      intros x Hx.
      cbn in Hx.
      unfold compose.
      unfold shift.
      rewrite 2 relabel_bounds_compose.
      destruct x as [x| |]; [|reflexivity..].
      cbn.
      f_equal.
      rewrite (decide_False (mb !!! _)) by lia.
      rewrite <- decide_not, (decide_ext _ (Pmap_map rrest_map x < lengthP unused_tys))
        by lia.
      replace (pos_sub_N _ _) with (Pmap_map rrest_map x) by lia.

      move Hrestdisj at bottom.
      specialize (Hrestdisj x).
      assert (Hx_rrest : x ∈ abstracts_bound_vars rrest) by
        now rewrite elem_of_abstracts_bound_vars; eauto.
      tspecialize Hrestdisj by auto.
      apply Hrrest_inv_inv; [|easy].
      enough (abstracts_bound_vars rrest ⊆ abstracts_bound_vars tabs) as Hsub
        by now apply Hsub in Hx_rrest.
      intros a.
      rewrite 2 elem_of_abstracts_bound_vars.
      enough (rrest ⊆ tabs) as Hsub by (clear -Hsub; naive_solver).
      intros flu.
      rewrite <- Hperm.
      rewrite elem_of_app.
      now right.
    + rewrite <- list_fmap_compose.
      apply eq_reflexivity.
      apply list_fmap_ext.
      intros _ ((f, low), up) Hflu%elem_of_list_lookup_2.
      unfold compose.
      rewrite relabel_abs_compose.
      apply relabel_abs_ext_strong.
      intros x Hx.
      cbn in Hx.
      cbn.
      destruct x as [r|l|g]; cbn; [..|reflexivity].
      * assert (Hrdom : r ∈ dom mb). 1:{
          rewrite Hdom, elem_of_abstracts_bound_vars; eauto.
        }
        rewrite lookup_total_alt.
        apply elem_of_dom in Hrdom as [mr Hmr].
        rewrite Hmr.
        cbn.
        f_equal.
        assert (Hrbound : r ∈ abstracts_bound_vars rabs) by
          now rewrite elem_of_abstracts_bound_vars; eauto.
        rewrite Hlhs, elem_of_list_to_set, elem_of_pseq_1 in Hrbound.
        rewrite decide_False by lia.
        rewrite decide_True by lia.
        reflexivity.
      * assert (Hlfree : l ∈ abstracts_free_vars rabs) by
          now rewrite elem_of_abstracts_free_vars; eauto.
        rewrite <- Hldom in Hlfree.
        unfold ml'.
        rewrite lookup_fmap, lookup_total_alt.
        apply elem_of_dom in Hlfree as [v Hv].
        rewrite Hv.
        cbn.
        destruct v as [r| |]; [|reflexivity..].
        cbn.
        rewrite (decide_False (mb !!! _)) by lia.
        rewrite <- decide_not, (decide_ext _ (Pmap_map rrest_map r < lengthP unused_tys))
          by lia.
        replace (pos_sub_N _ _) with (Pmap_map rrest_map r) by lia.
        f_equal.
        symmetry.
        move Hlimg at bottom.
        specialize (Hlimg (bound r)).
        tspecialize Hlimg by now apply elem_of_map_img; eauto.
        assert (Hrabs : r ∈ abstracts_bound_vars tabs). 1:{
          clear - Hlimg.
          set_unfold.
          rewrite !exists_pair in *.
          setoid_rewrite elem_of_list_omap.
          naive_solver.
        }
        apply Hrrest_inv_inv; [easy|].
        rewrite Hldisj; [easy|].
        subst mlran.
        apply elem_of_map_img.
        exists l.
        rewrite lookup_omap, Hv.
        reflexivity.
Qed.


*)







Record namedtensorlist := mk_ntl {
  ntl_sums : list Idx;
  ntl_abstracts : list (Idx * list var * list var);
  ntl_deltas : list (var * var);
}.

Definition ntl_free_varset (ntl : namedtensorlist) : Pset :=
  abstracts_free_vars ntl.(ntl_abstracts) ∪
    deltas_free_vars ntl.(ntl_deltas).

Definition ntl_bound_varset ntl :=
  abstracts_bound_vars ntl.(ntl_abstracts) ∪
  deltas_bound_vars ntl.(ntl_deltas).

Definition ntl_varset ntl :=
  abstracts_vars ntl.(ntl_abstracts) ∪
  deltas_vars ntl.(ntl_deltas).


Definition ntl2tl (ntl : namedtensorlist) :=
  let '(mk_ntl sums abs delt) := ntl in
  let varmap : Pmap Idx := list_to_map
    (imap (λ idx r, (r, Pos.of_succ_nat idx)) sums) in
  mk_tl (length sums)
  (relabel_abs (relabel_bounds (λ v, default v (varmap !! v))) <$> abs)
  (relabel_delt (relabel_bounds (λ v, default v (varmap !! v))) <$> delt).

Definition tl2ntl (tl : tensorlist) :=
  let '(mk_tl sums abs delt) := tl in
  mk_ntl (pseq 1 sums)
    abs
    delt.

Definition WF_ntl (ntl : namedtensorlist) : Prop :=
  NoDup ntl.(ntl_sums) /\
  abstracts_bound_vars ntl.(ntl_abstracts) ⊆ list_to_set ntl.(ntl_sums) /\
  deltas_bound_vars ntl.(ntl_deltas) ⊆ list_to_set ntl.(ntl_sums).

Definition WF_tl (tl : tensorlist) : Prop :=
  set_Forall (fun k => (k < Pos.of_succ_nat tl.(tl_sums)))
  (abstracts_bound_vars tl.(tl_abstracts) ∪
  deltas_bound_vars tl.(tl_deltas)).

Lemma tl2ntl2tl tl :
  ntl2tl (tl2ntl tl) = tl.
Proof.
  destruct tl as [sums abs delt].
  cbn.
  rewrite length_pseq.
  f_equal; [lia|..].
  - apply list_fmap_id'; intros flu _;
    apply relabel_abs_id'; intros [r|]; [|reflexivity].
    cbn.
    f_equal.
    rewrite pseq_to_seq.
    rewrite imap_fmap.
    unfold compose.
    rewrite imap_to_zip_with_seq.
    rewrite length_seq.
    change (xH :> nat) with O.
    rewrite <- zip_with_flip.
    unfold flip.
    rewrite <- (length_seq 0 (N.to_nat sums)) at 1.
    rewrite <- imap_to_zip_with_seq.
    rewrite lookup_list_to_map_imap_to_pos.
    destruct_decide (decide (r < sums)%nat) as Hrsm.
    + rewrite lookup_seq_lt by lia.
      cbn. lia.
    + now rewrite lookup_seq_ge by lia.
  - apply list_fmap_id'; intros lu _;
    apply relabel_delt_id'; intros [r|]; [|reflexivity].
    cbn.
    f_equal.
    rewrite pseq_to_seq.
    rewrite imap_fmap.
    unfold compose.
    rewrite imap_to_zip_with_seq.
    rewrite length_seq.
    change (xH :> nat) with O.
    rewrite <- zip_with_flip.
    unfold flip.
    rewrite <- (length_seq 0 (N.to_nat sums)) at 1.
    rewrite <- imap_to_zip_with_seq.
    rewrite lookup_list_to_map_imap_to_pos.
    destruct_decide (decide (r < sums)%nat) as Hrsm.
    + rewrite lookup_seq_lt by lia.
      cbn. lia.
    + now rewrite lookup_seq_ge by lia.
Qed.



Definition ntl_aeq : relation namedtensorlist :=
  λ ntl ntl',
  exists fr : Idx -> Idx,
    set_Forall2 (λ i j, fr i = fr j -> i = j)
      (list_to_set ntl.(ntl_sums) ∪ abstracts_bound_vars ntl.(ntl_abstracts)
        ∪ deltas_bound_vars ntl.(ntl_deltas)) /\
    fr <$> ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\
    (* prod_map fr id <$> ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\ *)
    relabel_abs (relabel_bounds fr) <$> ntl.(ntl_abstracts) ≡ₚ
      ntl'.(ntl_abstracts) /\
    relabel_delt (relabel_bounds fr) <$> ntl.(ntl_deltas) ≡ₚ
      ntl'.(ntl_deltas).

Infix "=ntl=" := ntl_aeq (at level 70).



Add Parametric Morphism : abstracts_bound_vars with signature
  (≡) ==> eq as abstracts_bound_vars_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_abstracts_bound_vars.
  now setoid_rewrite Habs.
Qed.
Add Parametric Morphism : abstracts_bound_vars with signature
  (≡ₚ) ==> eq as abstracts_bound_vars_perm_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_abstracts_bound_vars.
  now setoid_rewrite Habs.
Qed.
Add Parametric Morphism : deltas_bound_vars with signature
  (≡) ==> eq as deltas_bound_vars_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_deltas_bound_vars.
  now setoid_rewrite Habs.
Qed.
Add Parametric Morphism : deltas_bound_vars with signature
  (≡ₚ) ==> eq as deltas_bound_vars_perm_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_deltas_bound_vars.
  now setoid_rewrite Habs.
Qed.
Lemma abstracts_bound_vars_relabel_bounds (f : positive -> positive)
  (abs : list _) :
  abstracts_bound_vars (relabel_abs (relabel_bounds f) <$> abs) =
  set_map f (abstracts_bound_vars abs).
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_map, elem_of_abstracts_bound_vars.
  setoid_rewrite elem_of_abstracts_bound_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  setoid_rewrite exists_pair.
  split.
  - intros (_ & _ & _ & (idx & low & up & [= -> -> ->] & Hlu) & Hr).
    rewrite <- fmap_app, elem_of_list_fmap in Hr.
    destruct Hr as ([] & [= ->] & Hr).
    eauto 20.
  - intros (r' & -> & idx & low & up & Hlu & Hr').
    eexists _, _, _.
    split; [exists idx, low, up; split; [cbn; reflexivity|easy]|].
    rewrite <- fmap_app.
    apply (elem_of_list_fmap_1 (relabel_bounds f) _ _ Hr').
Qed.
Lemma deltas_bound_vars_relabel_bounds (f : positive -> positive)
  (delt : list _) :
  deltas_bound_vars (relabel_delt (relabel_bounds f) <$> delt) =
  set_map f (deltas_bound_vars delt).
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_map, elem_of_deltas_bound_vars.
  setoid_rewrite elem_of_deltas_bound_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  cbn.
  split; [|set_solver].
  intros (l & u & (a & b & [= -> ->] & Hab) & Hor).
  destruct a, b; cbn in *; naive_solver.
Qed.

(* Lemma kmap_kmap `{FinMap K1 M1, FinMap K2 M2, FinMap K3 M3} {A}
  (f : K1 -> K2) (g : K2 -> K3) (m : M1 A) :
  kmap g (kmap f m :> M2 A) =@{M3 A} kmap (g ∘ f) m.
Proof.
  apply map_eq.
  intros i.
  apply option_eq.
  induction m using map_first_key_ind. *)
Lemma ntl_aeq_of_perm ntl ntl' :
  ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) ->
  ntl.(ntl_abstracts) ≡ₚ ntl'.(ntl_abstracts) ->
  ntl.(ntl_deltas) ≡ₚ ntl'.(ntl_deltas) ->
  ntl =ntl= ntl'.
Proof.
  destruct ntl as [isums abs delt], ntl' as [isums' abs' delt'];
  cbn.
  intros Hsums Habs Hdelt.
  exists id; cbn.
  split; [easy|].
  rewrite list_fmap_id.
  split; [done|].
  rewrite <- Habs, <- Hdelt.
  split;
  apply eq_reflexivity, list_fmap_id'; intros;
  [apply relabel_abs_id'|apply relabel_delt_id']; intros;
  apply relabel_bounds_id.
Qed.
Lemma ntl_aeq_refl ntl : ntl =ntl= ntl.
Proof.
  now apply ntl_aeq_of_perm.
Qed.
Lemma ntl_aeq_symm ntl ntl' : ntl =ntl= ntl' -> ntl' =ntl= ntl.
Proof.
  intros (fr & Hfr & Hsums & Habs & Hdelt).
  exists (invfun fr (ntl.(ntl_sums) ++
    elements (abstracts_bound_vars ntl.(ntl_abstracts)
    ∪ deltas_bound_vars ntl.(ntl_deltas)))).
  assert (Hfrinj : ForallPairs (λ a a' : Idx, fr a = fr a' → a = a')
  (ntl.(ntl_sums) ++
    elements (abstracts_bound_vars ntl.(ntl_abstracts)
    ∪ deltas_bound_vars ntl.(ntl_deltas)))). 1:{
     rewrite ForallPairs_forall; hnf in Hfr; set_solver +Hfr.
  }
  (* apply (fmap_Permutation fst) in Hsums as Hdoms. *)
  (* rewrite fsts_prod_map in Hdoms. *)
  split; [|split; [|split]].
  - intros a b Ha Hb.
    rewrite <- Hsums in Ha, Hb.
    rewrite <- Habs in Ha, Hb.
    rewrite <- Hdelt in Ha, Hb.
    rewrite abstracts_bound_vars_relabel_bounds,
      deltas_bound_vars_relabel_bounds in Ha, Hb.
    rewrite <- (set_map_list_to_set (SA:=Pset)) in Ha, Hb.
    rewrite <- set_map_union in Ha.
    apply invfun_inj; [easy|..].
    + apply elem_of_list_In.
      set_solver + Ha.
    + apply elem_of_list_In.
      set_solver + Hb.
  - rewrite <- Hsums.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity, list_fmap_id'.
    intros i.
    intros Hity.
    cbn.
    f_equal.
    apply invfun_linv; [easy|].
    now apply elem_of_app; left.
  - rewrite <- Habs.
    apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros flu Hflu.
    cbn.
    rewrite relabel_abs_compose.
    apply relabel_abs_id_strong.
    intros [r|] Hr; [|done..].
    cbn.
    f_equal.
    apply invfun_linv; [easy|].
    apply elem_of_app; right.
    apply elem_of_elements, elem_of_union, or_introl, elem_of_abstracts_bound_vars.
    destruct flu as [[f l] u]; eauto.
  - rewrite <- Hdelt.
    apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros lu Hlu.
    cbn.
    rewrite relabel_delt_compose.
    apply relabel_delt_id_strong.
    intros v Hv.
    destruct v as [r|]; [|reflexivity].
    cbn.
    f_equal.
    apply invfun_linv; [easy|].
    apply elem_of_app; right.
    apply elem_of_elements, elem_of_union, or_intror, elem_of_deltas_bound_vars.
    destruct lu as [l u]; cbn in *.
    naive_solver.
Qed.
Lemma ntl_aeq_trans ntl ntl' ntl'' :
  ntl =ntl= ntl' -> ntl' =ntl= ntl'' ->
  ntl =ntl= ntl''.
Proof.
  intros (fr & Hfr & Hsums & Habs & Hdelt)
    (fr' & Hfr' & Hsums' & Habs' & Hdelt').
  exists (fr' ∘ fr).
  split; [|split; [|split]].
  - intros a a' Ha Ha'.
    cbn.
    intros Hfas%Hfr'; [|rewrite <- Habs, <- Hdelt, <- Hsums,
      abstracts_bound_vars_relabel_bounds, deltas_bound_vars_relabel_bounds..];
      [|set_solver +Ha|set_solver +Ha'].
    revert Hfas.
    now apply Hfr.
  - rewrite <- Hsums', <- Hsums.
    now rewrite <- list_fmap_compose.
  - rewrite <- Habs', <- Habs.
    rewrite <- list_fmap_compose.
    unfold compose.
    setoid_rewrite relabel_abs_compose.
    apply eq_reflexivity, list_fmap_ext; intros _ flu _.
    apply relabel_abs_ext; intros v.
    now unfold compose; rewrite relabel_bounds_compose.
  - rewrite <- Hdelt', <- Hdelt.
    rewrite <- list_fmap_compose.
    unfold compose.
    setoid_rewrite relabel_delt_compose.
    apply eq_reflexivity, list_fmap_ext; intros _ lu _.
    apply relabel_delt_ext; intros v.
    now unfold compose; rewrite relabel_bounds_compose.
Qed.
Add Parametric Relation : namedtensorlist ntl_aeq
  reflexivity proved by ntl_aeq_refl
  symmetry proved by ntl_aeq_symm
  transitivity proved by ntl_aeq_trans
  as ntl_aeq_setoid.

Lemma union_eq_l `{SemiSet A C} (X Y : C) : Y ⊆ X ->
  X ∪ Y ≡ X.
Proof.
  set_solver.
Qed.



(* FIXME: Move *)
#[export]
Instance pos_to_nat_pred_inj : Inj (=) (=) pos_to_nat_pred.
Proof.
  intros p p'.
  lia.
Qed.

Lemma ntl2tl2ntl ntl :
  WF_ntl ntl ->
  tl2ntl (ntl2tl ntl) =ntl= ntl.
Proof.
  destruct ntl as [isums abs delt].
  intros [Hdup Hbnd].
  cbn -[abstracts_bound_vars deltas_bound_vars] in *.
  (* rewrite fmap_reverse, reverse_involutive. *)
  exists (Pmap_map (list_to_map
    (imap (λ idx idx', (Pos.of_succ_nat idx, idx')) isums)));
  cbn -[abstracts_bound_vars deltas_bound_vars].
  rewrite abstracts_bound_vars_relabel_bounds,
    deltas_bound_vars_relabel_bounds.
  split_and!.
  - erewrite union_mono; [|apply union_mono; [reflexivity|]|];
    [|(eapply set_map_mono; [apply reflexivity|apply Hbnd])..].
    rewrite <- (union_assoc _), (union_idemp _).
    rewrite union_eq_l. 2:{
      rewrite set_map_list_to_set.
      apply list_to_set_subseteq.

      intros _ (idx & -> & Hidx)%elem_of_list_fmap.
      cbn.
      apply elem_of_list_lookup in Hidx as Hi.
      destruct Hi as [i Hi].
      replace (list_to_map _ !! _) with
        (Some (Pos.of_succ_nat i)).
      - cbn.
        rewrite elem_of_pseq_1.
        now apply lookup_lt_Some in Hi; lia.
      - symmetry.
        apply elem_of_list_to_map.
        + rewrite fmap_imap.
          unfold compose; cbn.
          rewrite imap_to_fmap, list_fmap_id; easy.
        + rewrite elem_of_lookup_imap.
          exists i, idx; easy.
    }
    rewrite set_Forall2_list_to_set.
    (* rewrite ForallPairs_map. *)
    hnf.
    intros i j Hi%elem_of_list_In%elem_of_pseq_1 Hj%elem_of_list_In%elem_of_pseq_1.
    unfold Pmap_map.
    (* destruct Hi as [_ Hi], Hj as [_ Hj]. *)
    rewrite 2 lookup_list_to_map_imap_to_pos, 2 option_fmap_id.
    assert (Hi' : (i < length isums)%nat) by lia.
    assert (Hj' : (j < length isums)%nat) by lia.

    apply lookup_lt_is_Some in Hi' as Hli.
    apply lookup_lt_is_Some in Hj' as Hlj.
    destruct Hli as [li Hli], Hlj as [lj Hlj].
    rewrite Hli, Hlj.
    cbn.
    intros <-.
    apply (inj pos_to_nat_pred).
    revert Hli Hlj.
    now apply NoDup_lookup.
  -
    apply eq_reflexivity.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap, length_pseq; lia|].
    intros i x y Hi.
    rewrite list_lookup_fmap.
    destruct (isums !! i) as [idx|] eqn:Hidxi; [|easy].
    rewrite lookup_pseq_1_lt by lia.
    cbn.
    intros [= <-] [= <-].
    unfold Pmap_map.
    rewrite lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat.
    now rewrite Hidxi.
  - apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros ((f, low), up) Hflu.
    cbn [compose].
    rewrite relabel_abs_compose.
    apply relabel_abs_id_strong.
    intros v Hv.
    destruct v as [r|]; [|reflexivity].
    cbn.
    revert Hbnd; intros [Hbnd _].
    specialize (Hbnd r).
    tspecialize Hbnd by now apply elem_of_abstracts_bound_vars; eauto.
    rewrite elem_of_list_to_set in Hbnd.
    apply elem_of_list_lookup in Hbnd as [i Hi].
    replace (list_to_map _ !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap.
        unfold compose.
        cbn.
        now rewrite imap_to_fmap, list_fmap_id.
      - rewrite elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    unfold Pmap_map.
    rewrite lookup_list_to_map_imap_to_pos,
      pos_to_nat_pred_of_nat, Hi.
    reflexivity.
  - apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros [l u] Hlu.
    cbn [compose].
    rewrite relabel_delt_compose.
    apply relabel_delt_id_strong.
    intros v Hv.
    destruct v as [r|]; [|reflexivity].
    cbn in *.
    revert Hbnd; intros [_ Hbnd].
    specialize (Hbnd r).
    tspecialize Hbnd by now apply elem_of_deltas_bound_vars; naive_solver.
    rewrite elem_of_list_to_set in Hbnd.
    apply elem_of_list_lookup in Hbnd as [i Hi].
    replace (list_to_map _ !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap.
        unfold compose.
        cbn.
        now rewrite imap_to_fmap, list_fmap_id.
      - rewrite elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    unfold Pmap_map.
    rewrite lookup_list_to_map_imap_to_pos,
      pos_to_nat_pred_of_nat, Hi.
    reflexivity.
Qed.

Lemma tl2ntl_WF tl :
  WF_tl tl <-> WF_ntl (tl2ntl tl).
Proof.
  destruct tl as [sums abs].
  cbn.
  unfold WF_tl, WF_ntl.
  cbn -[abstracts_bound_vars deltas_bound_vars].
  rewrite and_is_True_l by now apply NoDup_pseq.
  rewrite <- union_subseteq.
  apply forall_iff; intros r.
  apply forall_iff; intros Hr.
  rewrite elem_of_list_to_set, elem_of_pseq_1.
  lia.
Qed.

Lemma ntl2tl_WF ntl : WF_ntl ntl -> WF_tl (ntl2tl ntl).
Proof.
  destruct ntl as [isums abs delt].
  intros [Hdup Hsub].
  unfold WF_tl.
  cbn -[abstracts_bound_vars deltas_bound_vars] in *.
  apply set_Forall_union.
  - rewrite abstracts_bound_vars_relabel_bounds.
    intros x (idx & -> & Hi)%elem_of_map.
    apply Hsub in Hi as Hi'.
    rewrite elem_of_list_to_set in Hi'.
    pose proof Hi' as [i Hisi]%elem_of_list_lookup.
    replace (list_to_map _ !! _) with (Some (Pos.of_succ_nat i));
      [cbn; apply lookup_lt_Some in Hisi; lia|].
    symmetry.
    apply elem_of_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      now rewrite imap_to_fmap, list_fmap_id.
    + rewrite elem_of_lookup_imap.
      eexists _, _; split; [|apply Hisi].
      reflexivity.
  - rewrite deltas_bound_vars_relabel_bounds.
    intros x (idx & -> & Hi)%elem_of_map.
    apply Hsub in Hi as Hi'.
    rewrite elem_of_list_to_set in Hi'.
    pose proof Hi' as [i Hisi]%elem_of_list_lookup.
    replace (list_to_map _ !! _) with (Some (Pos.of_succ_nat i));
      [cbn; apply lookup_lt_Some in Hisi; lia|].
    symmetry.
    apply elem_of_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      now rewrite imap_to_fmap, list_fmap_id.
    + rewrite elem_of_lookup_imap.
      eexists _, _; split; [|apply Hisi].
      reflexivity.
Qed.

Fixpoint infinite_injection_aux `{Infinite A} (n : nat) : A * list A :=
  match n with
  | 0 => (fresh [], [])
  | S n' => let fn' := infinite_injection_aux n' in
    (fresh (fn'.1 :: fn'.2), fn'.1 :: fn'.2)
  end%nat.

Lemma infinite_injection_aux_fresh `{Infinite A} (n : nat):
  ((infinite_injection_aux n).1 :> A) ∉ (infinite_injection_aux n).2.
Proof.
  destruct n; apply infinite_is_fresh.
Qed.

Lemma infinite_injection_aux_contains `{Infinite A} (n m : nat) :
  (n < m)%nat ->
  uncurry cons (infinite_injection_aux n) ⊆@{list A} (infinite_injection_aux m).2.
Proof.
  intros Hlt.
  induction Hlt.
  - cbn.
    now destruct (infinite_injection_aux _).
  - cbn.
    rewrite IHHlt.
    now apply list_subseteq_cons.
Qed.

Definition infinite_injection `{Infinite A} (n : nat) : A :=
  (infinite_injection_aux n).1.

#[global] Instance infinite_injection_inj `{Infinite A} :
  Inj (=) (@eq A) infinite_injection.
Proof.
  eenough (Hen : _) by
  (intros n m; destruct (Nat.lt_trichotomy n m) as [Hnm | [-> | Hmn]];
  [exact (Hen n m Hnm)|easy|exact (fun H => eq_sym (Hen m n Hmn (eq_sym H)))]).
  intros n m Hnm.
  unfold infinite_injection.
  pose proof (infinite_injection_aux_fresh (A:=A) m) as Hfresh.
  pose proof (infinite_injection_aux_contains (A:=A) n m Hnm) as Hcont.
  rewrite (surjective_pairing (infinite_injection_aux n)) in Hcont.
  cbn in Hcont.
  intros Heq.
  rewrite Heq in Hcont.
  specialize (Hcont (infinite_injection_aux m).1 ltac:(constructor)).
  easy.
Qed.


Fixpoint infinite_injection_avoiding_aux `{Infinite A} (l : list A) (n : nat) :
  A * list A :=
  match n with
  | 0 => (fresh l, l)
  | S n' => let fn' := infinite_injection_avoiding_aux l n' in
    (fresh (fn'.1 :: fn'.2), fn'.1 :: fn'.2)
  end%nat.

Lemma infinite_injection_avoiding_aux_fresh `{Infinite A} (l : list A) (n : nat) :
  (infinite_injection_avoiding_aux l n).1 ∉ (infinite_injection_avoiding_aux l n).2.
Proof.
  destruct n; apply infinite_is_fresh.
Qed.

Lemma infinite_injection_avoiding_aux_contains `{Infinite A}
  (l : list A) (n m : nat) :
  (n < m)%nat ->
  uncurry cons (infinite_injection_avoiding_aux l n) ⊆
    (infinite_injection_avoiding_aux l m).2.
Proof.
  intros Hlt.
  induction Hlt.
  - cbn.
    now destruct (infinite_injection_avoiding_aux _).
  - cbn.
    rewrite IHHlt.
    now apply list_subseteq_cons.
Qed.


Lemma infinite_injection_avoiding_aux_contains_avoid `{Infinite A}
  (l : list A) (n : nat) :
  l ⊆ (infinite_injection_avoiding_aux l n).2.
Proof.
  induction n; [reflexivity|].
  cbn.
  now apply list_subseteq_cons.
Qed.

Definition infinite_injection_avoiding `{Infinite A} (l : list A) (n : nat) : A :=
  (infinite_injection_avoiding_aux l n).1.

#[global] Instance infinite_injection_avoiding_inj `{Infinite A} l :
  Inj (=) (@eq A) (infinite_injection_avoiding l).
Proof.
  eenough (Hen : _) by
  (intros n m; destruct (Nat.lt_trichotomy n m) as [Hnm | [-> | Hmn]];
  [exact (Hen n m Hnm)|easy|exact (fun H => eq_sym (Hen m n Hmn (eq_sym H)))]).
  intros n m Hnm.
  unfold infinite_injection_avoiding.
  pose proof (infinite_injection_avoiding_aux_fresh l m) as Hfresh.
  pose proof (infinite_injection_avoiding_aux_contains l n m Hnm) as Hcont.
  rewrite (surjective_pairing (infinite_injection_avoiding_aux l n)) in Hcont.
  cbn in Hcont.
  intros Heq.
  rewrite Heq in Hcont.
  specialize (Hcont (infinite_injection_avoiding_aux l m).1 ltac:(constructor)).
  easy.
Qed.

Lemma infinite_injection_avoiding_avoids `{Infinite A} (l : list A) (n : nat) :
  infinite_injection_avoiding l n ∉ l.
Proof.
  pose proof (infinite_injection_avoiding_aux_fresh l n) as Hfresh.
  now intros ?%(infinite_injection_avoiding_aux_contains_avoid l n).
Qed.



Lemma partial_injection_extension `{Countable A, Infinite B}
  (l : list A) (f : A -> B) :
    ForallPairs (λ i j, f i = f j → i = j) l ->
    exists (g : A -> B), Inj (=) (=) g /\ Forall (fun a => g a = f a) l.
Proof.
  intros Hlinj.
  set (g := infinite_injection_avoiding (f <$> l) ∘ pos_to_nat_pred).
  exists (λ a, if decide (a ∈ l) then f a else g (encode a)).
  split; [|now rewrite Forall_forall; intros a Ha; rewrite decide_True].
  intros a b.
  case_decide as Ha; case_decide as Hb.
  - now apply Hlinj; apply elem_of_list_In.
  - intros Heq%eq_sym.
    exfalso.
    apply (infinite_injection_avoiding_avoids (f <$> l) (encode b)).
    subst g.
    cbn in Heq.
    rewrite Heq.
    now apply elem_of_list_fmap_1.
  - intros Heq.
    exfalso.
    apply (infinite_injection_avoiding_avoids (f <$> l) (encode a)).
    subst g.
    cbn in Heq.
    rewrite Heq.
    now apply elem_of_list_fmap_1.
  - intros Heq.
    apply (inj encode).
    revert Heq.
    apply inj.
    unfold g; apply _.
Qed.

Lemma set_Forall2_elements `{FinSet A SA} (R : relation A) (X : SA) :
  set_Forall2 R X <-> ForallPairs R (elements X).
Proof.
  rewrite <- (set_Forall2_list_to_set (C:=SA)).
  now rewrite list_to_set_elements.
Qed.

Lemma partial_injection_extension' `{Countable A, Infinite B, FinSet A SA}
  (X : SA) (f : A -> B) :
  set_Forall2 (λ i j, f i = f j → i = j) X ->
    exists (g : A -> B), Inj (=) (=) g /\ set_Forall (fun a => g a = f a) X.
Proof.
  rewrite set_Forall2_elements.
  intros (g & Hg & Hgeq%set_Forall_elements)%partial_injection_extension.
  eauto.
Qed.


Lemma kmap_ext `{FinMap K1 M1, FinMap K2 M2} {A}
  (f g : K1 -> K2) (m : M1 A) :
  (forall k a, m !! k = Some a -> f k = g k) ->
  kmap f m =@{M2 A} kmap g m.
Proof.
  intros Hfg.
  unfold kmap.
  f_equal.
  apply list_fmap_ext; intros _ (k, a) Hka%elem_of_list_lookup_2%elem_of_map_to_list.
  cbn.
  f_equal; eauto.
Qed.

Lemma ntl_aeq_alt ntl ntl' :
  WF_ntl ntl ->
  ntl =ntl= ntl' <->
  exists fr, Inj (=) (=) fr /\
    fr <$> ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\
    relabel_abs (relabel_bounds fr) <$> ntl.(ntl_abstracts) ≡ₚ
      ntl'.(ntl_abstracts) /\
    relabel_delt (relabel_bounds fr) <$> ntl.(ntl_deltas) ≡ₚ
      ntl'.(ntl_deltas).
Proof.
  intros HWF.
  split; cycle 1.
  - intros (f & Hf & Hsums & Habs & Hdelt).
    exists f.
    split; [intros ? ? ? ?; apply Hf|].
    split_and!; assumption.
  - intros (fr & Hfr & Hsums & Habs & Hdelt).
    apply partial_injection_extension' in Hfr as (g & Hginj & Hgf).
    (* rewrite Forall_forall in Hgf. *)
    exists g.
    split; [easy|].
    split; [|split].
    + rewrite <- Hsums.
      apply eq_reflexivity, list_fmap_ext; intros _ idx Hidx%elem_of_list_lookup_2.
      cbn.
      f_equal.
      apply Hgf; set_solver + Hidx.
    + rewrite <- Habs.
      apply eq_reflexivity.
      apply list_fmap_ext; intros _ flu Hflu%elem_of_list_lookup_2.
      apply relabel_abs_ext_strong.
      intros [r|] Hr; [|reflexivity..].
      cbn.
      f_equal.
      apply Hgf.
      rewrite elem_of_union; left.
      rewrite elem_of_union; right.
      rewrite elem_of_abstracts_bound_vars.
      now destruct flu as [[f l] u]; cbn; eauto.
    + rewrite <- Hdelt.
      apply eq_reflexivity.
      apply list_fmap_ext; intros _ lu Hlu%elem_of_list_lookup_2.
      apply relabel_delt_ext_strong.
      intros [r|] Hr; [|reflexivity..].
      cbn.
      f_equal.
      apply Hgf.
      rewrite elem_of_union; right.
      rewrite elem_of_deltas_bound_vars.
      now destruct lu as [l u]; cbn; naive_solver.
Qed.



Lemma ntl2tl_aeq ntl ntl' :
  WF_ntl ntl -> WF_ntl ntl' ->
  ntl =ntl= ntl' ->
  ntl2tl ntl =tl= ntl2tl ntl'.
Proof.
  destruct ntl as [isums abs delt], ntl' as [isums' abs' delt'].
  cbn.
  intros Hntl Hntl' (fr & Hfrinj & Hsums & Habs & Hdelt)%(ntl_aeq_alt _ _ Hntl).
  cbn in *.
  set (g := λ i : Idx,
    (si ← isums !! (i:>nat);
    (Pos.of_succ_nat ∘ fst) <$> list_find (λ si', fr si = si') isums') :> option Idx).
  assert (Hgsome : forall i j,
    g i = Some j <-> exists idx, isums !! (i:>nat) = Some (idx) /\
      isums' !! (j:>nat) = Some (fr idx)). 1:{
    pose proof (lengthN_correct isums).
    intros i j.
    subst g.
    cbn.
    rewrite bind_Some.
    apply exists_iff; intros idx.
    apply and_iff_from_l; [reflexivity|]; intros Hidx _.
    split.
    - apply elem_of_list_lookup_2 in Hidx as Hidx_in.
      apply (elem_of_list_fmap_1 fr) in Hidx_in.
      rewrite Hsums in Hidx_in.
      apply elem_of_list_lookup in Hidx_in as Hidx'.
      destruct Hidx' as [j' Hj'].
      (* apply elem_of_list_lookup_2 in Hidx' as Hidx_in'. *)

      specialize (list_find_elem_of (λ si', fr idx = si') _ _ Hidx_in
        eq_refl) as Hsome.
      destruct Hsome as [(j'', lj) Hlj].
      cbn.
      rewrite Hlj.
      cbn.
      intros [= <-].
      rewrite pos_to_nat_pred_of_nat.
      apply list_find_Some in Hlj as [Hlook Hlj1].
      rewrite Hlook.
      now destruct Hlj1 as [<- _].
    - intros Hsums'.
      specialize (list_find_elem_of (λ si', fr idx = si') _ _ (elem_of_list_lookup_2 _ _ _ Hsums')
        eq_refl) as Hsome.
      destruct Hsome as [lj Hlj].
      cbn.
      rewrite Hlj.
      cbn.
      destruct lj as [j' fridx].
      apply list_find_Some in Hlj as (Hj' & [= <-] & Hlooks).
      cbn.
      f_equal.
      apply pos_to_nat_pred_inj.
      rewrite pos_to_nat_pred_of_nat.
      revert Hj' Hsums'.
      apply NoDup_lookup, Hntl'.
  }
  assert (HgisSome : forall i, i < lengthP isums -> exists j, g i = Some j /\
    j < lengthP isums'). 1:{
    pose proof (lengthN_correct isums).
    intros i Hi.

    cbn.
    destruct (isums !! (i:>nat)) as [idx|] eqn:Hidx;
      [|apply lookup_ge_None_1 in Hidx; lia].
    cbn.
    (* apply (fmap_Permutation fst) in Hsums as Hsums''.
    rewrite fsts_prod_map in Hsums''. *)
    (* apply Permutation equiv
    apply (f_equal dom) in Hsums as Hsums'. *)
    (* rewrite dom_kmap_L', <- leibniz_equiv_iff in Hsums'. *)
    assert (Hsums' : fr <$> isums ≡ isums') by now intros ?; rewrite Hsums.
    specialize (Hsums' (fr idx)).1 as Hdom.
    tspecialize Hdom. 1:{
      apply elem_of_list_fmap_1.
      now apply elem_of_list_lookup_2 in Hidx.
    }
    apply elem_of_list_lookup in Hdom as [j Hj].
    exists (Pos.of_succ_nat j).
    split; [|apply lookup_lt_Some in Hj; rewrite lengthN_correct_rev; lia].
    apply Hgsome.
    exists idx.
    now rewrite pos_to_nat_pred_of_nat.
  }
  pose proof (lengthN_correct isums).
  pose proof (lengthN_correct isums').
  assert (Hginv : forall j, j < lengthP isums' -> exists i, g i = Some j /\
    i < lengthP isums). 1:{
    intros j Hj.

    destruct (isums' !! (j:>nat)) as [fridx|] eqn:Hidx;
      [|apply lookup_ge_None_1 in Hidx; lia].

    apply elem_of_list_lookup_2 in Hidx as Hidx_in.
    rewrite <- Hsums in Hidx_in.
    apply elem_of_list_fmap in Hidx_in as (idx & [= ->] & Hidx_in).
    apply elem_of_list_lookup in Hidx_in as Hi.
    destruct Hi as [i Hi].
    exists (Pos.of_succ_nat i).
    split; [|apply lookup_lt_Some in Hi; lia].
    apply Hgsome.
    exists idx.
    now rewrite pos_to_nat_pred_of_nat.
  }
  symmetry.
  exists (λ i, default i (g i)); cbn -[reverse].
  assert (Hlens : length isums = length isums'). 1:{
    now rewrite <- Hsums, length_fmap.
  }
  apply lengthN_eq in Hlens as HlenNs.
  (* rewrite lengthN_fmap, lengthN_reverse, 2 fmap_reverse, 2 reverse_involutive. *)
  assert (Hgperm : posperm (lengthP isums) (λ i : Idx, default i (g i))). 1:{
    apply surj_is_posperm.
    intros j Hj.
    rewrite HlenNs in Hj.
    apply Hginv in Hj as Hi.
    destruct Hi as (i & Hgi & Hi).
    exists i.
    rewrite Hgi; eauto.
  }
  assert (Hpperm : ppermute (λ i : Idx, default i (g i)) isums' = fr <$> isums). 1:{
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_ppermute, length_fmap|].
    intros i x y Hi.
    rewrite length_fmap in Hi.
    rewrite lookup_ppermute_alt_bdd by
      now (apply posperm_bounded; rewrite <- ?HlenNs) || lia.
    (* rewrite <- Hlens in Hi. *)
    specialize (HgisSome (Pos.of_succ_nat i) ltac:(lia)) as Hgi.
    destruct Hgi as (j & Hgi & Hj).
    rewrite Hgi.
    cbn.
    apply Hgsome in Hgi as (idx & Hisums & Hisums').
    rewrite pos_to_nat_pred_of_nat in Hisums.
    rewrite list_lookup_fmap.
    rewrite Hisums, Hisums'.
    cbn.
    congruence.
  }
  split; [rewrite <- Hlens; replace (Pos.of_succ_nat (length isums))
    with (lengthP isums) by lia; easy|].
  split; [easy|].
  (* rewrite ppermute_fmap, Hpperm, snds_prod_map, list_fmap_id.
  apply (conj eq_refl). *)
  rewrite <- Habs.
  rewrite <- 2 list_fmap_compose.
  split.
  - apply eq_reflexivity.
    apply list_fmap_ext; intros _ flu Hlu%elem_of_list_lookup_2.
    cbn.
    rewrite 2 relabel_abs_compose.
    apply relabel_abs_ext_strong.
    intros [r|] Hr; [|done..].
    cbn [compose relabel_bounds var_map].
    specialize (Hntl.2.1 r) as Hrabs.
    tspecialize Hrabs by now apply elem_of_abstracts_bound_vars;
      destruct flu as [[f l] u]; cbn in *; eauto.
    rewrite elem_of_list_to_set in Hrabs.
    cbn in Hrabs.
    (* apply elem_of_list_fmap in Hrabs as ((_, ty) & [= <-] & Hrty). *)
    apply elem_of_list_lookup in Hrabs as Hi.
    destruct Hi as (i & Hi).
    replace ((list_to_map (imap _ isums)) !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap; unfold compose; cbn; rewrite imap_to_fmap, list_fmap_id; apply Hntl.
      - rewrite elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    apply lookup_lt_Some in Hi as Hilt.
    rewrite decide_False by lia.
    specialize (HgisSome (Pos.of_succ_nat i) ltac:(lia)) as (j & Hgi & Hj).
    rewrite Hgi.
    cbn.
    replace (list_to_map _ !! _) with (Some j); [done|].
    symmetry.
    apply elem_of_list_to_map;
    [rewrite fmap_imap; unfold compose; cbn; rewrite imap_to_fmap, list_fmap_id; apply Hntl'|].
    rewrite elem_of_lookup_imap.
    apply Hgsome in Hgi.
    exists (pos_to_nat_pred j), (fr r).
    rewrite pos_to_nat_pred_to_pos.
    split; [easy|].
    rewrite pos_to_nat_pred_of_nat in Hgi.
    destruct Hgi as (? & ? & ?); congruence.
  - rewrite <- Hdelt, <- 2 list_fmap_compose.
    apply eq_reflexivity.
    apply list_fmap_ext; intros _ lu Hlu%elem_of_list_lookup_2.
    cbn.
    rewrite 2 relabel_delt_compose.
    apply relabel_delt_ext_strong.
    intros [r|] Hr; [|done..].
    cbn [compose relabel_bounds var_map].
    specialize (Hntl.2.2 r) as Hrabs.
    tspecialize Hrabs by now apply elem_of_deltas_bound_vars;
      destruct lu as [l u]; cbn in *; naive_solver.
    rewrite elem_of_list_to_set in Hrabs.
    cbn in Hrabs.
    (* apply elem_of_list_fmap in Hrabs as ((_, ty) & [= <-] & Hrty). *)
    apply elem_of_list_lookup in Hrabs as Hi.
    destruct Hi as (i & Hi).
    replace ((list_to_map (imap _ isums)) !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap; unfold compose; cbn; rewrite imap_to_fmap, list_fmap_id; apply Hntl.
      - rewrite elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    apply lookup_lt_Some in Hi as Hilt.
    rewrite decide_False by lia.
    specialize (HgisSome (Pos.of_succ_nat i) ltac:(lia)) as (j & Hgi & Hj).
    rewrite Hgi.
    cbn.
    replace (list_to_map _ !! _) with (Some j); [done|].
    symmetry.
    apply elem_of_list_to_map;
    [rewrite fmap_imap; unfold compose; cbn; rewrite imap_to_fmap, list_fmap_id; apply Hntl'|].
    rewrite elem_of_lookup_imap.
    apply Hgsome in Hgi.
    exists (pos_to_nat_pred j), (fr r).
    rewrite pos_to_nat_pred_to_pos.
    split; [easy|].
    rewrite pos_to_nat_pred_of_nat in Hgi.
    destruct Hgi as (? & ? & ?); congruence.
Qed.


Lemma imap_to_imap_pair {A B} (f : nat -> A -> B) l :
  imap f l = uncurry f <$> imap pair l.
Proof.
  rewrite fmap_imap.
  reflexivity.
Qed.

Lemma zip_with_ext_strong {A B C} (f g : A -> B -> C)
  (l1 l2 : list A) (k1 k2 : list B) :
  (forall a b, a ∈ l1 -> b ∈ k1 -> f a b = g a b) ->
  l1 = l2 -> k1 = k2 ->
  zip_with f l1 k1 = zip_with g l2 k2.
Proof.
  intros Hfg <- <-.
  revert k1 Hfg; induction l1; intros k1 Hfg; [done|].
  destruct k1; [done|].
  cbn.
  f_equal; [|now apply IHl1; eauto using elem_of_list_further].
  apply Hfg; constructor.
Qed.


Lemma make_pwf_inj n f :
  posperm n f ->
  Inj (=) (=) (make_pwf n f).
Proof.
  intros Hf.
  specialize (posperm_inj _ _ Hf) as Hfinj.
  specialize (posperm_bounded _ _ Hf) as Hfbdd.
  intros p q.
  specialize (Hfinj p q).
  generalize (Hfbdd p) (Hfbdd q).
  cbn.
  do 2 case_decide; lia.
Qed.

Lemma tl2ntl_aeq tl tl' :
  tl =tl= tl' ->
  tl2ntl tl =ntl= tl2ntl tl'.
Proof.
  intros (f & Hf & Hlen & Habs & Hdelt)%symmetry.
  destruct tl as [sums abs delt], tl' as [sums' abs' delt'].
  cbn in *.
  eexists.
  assert (Hinj : Inj (=) (=) (make_pwf (Pos.of_succ_nat sums') f)) by
    now apply make_pwf_inj.
  split; [intros ????; apply Hinj|
    split; [|split; [symmetry; apply Habs | symmetry; apply Hdelt]]].
  cbn.
  pose proof Hf as Hperm.
  hnf in Hperm.
  replace (Pos.pred_N (Pos.of_succ_nat sums')) with (sums' :> N)
    in Hperm by lia.
  rewrite <- Hperm.
  apply eq_reflexivity.
  rewrite Hlen.
  apply list_fmap_ext; intros _ p Hp%elem_of_list_lookup_2%elem_of_pseq_1.
  apply decide_False; lia.
Qed.

(*
Section abstracts_perm_eq.

Context {A B : Type}.
Implicit Types (abs : A * list B * list B).

Definition abstracts_perm_eq abs abs' : Prop :=
  abs.1.1 = abs'.1.1 /\ abs.1.2 ≡ₚ abs'.1.2 /\ abs.2 ≡ₚ abs'.2.

#[freeal] Infix "≡abs≡ₚ" := abstracts_perm_eq (at level 70).

Lemma abstracts_perm_eq_refl abs : abs ≡abs≡ₚ abs.
Proof. easy. Qed.
Lemma abstracts_perm_eq_symm abs abs' : abs ≡abs≡ₚ abs' -> abs' ≡abs≡ₚ abs.
Proof. intros (? & ? & ?); split_and!; now symmetry. Qed.
Lemma abstracts_perm_eq_trans abs abs' abs'' :
  abs ≡abs≡ₚ abs' -> abs' ≡abs≡ₚ abs'' -> abs ≡abs≡ₚ abs''.
Proof. intros (? & ? & ?) (? & ? & ?); split_and!; now etransitivity; eauto. Qed.

End abstracts_perm_eq.

Infix "≡abs≡ₚ" := abstracts_perm_eq (at level 70).

Add Parametric Relation {A B} : (A * list B * list B) abstracts_perm_eq
  reflexivity proved by abstracts_perm_eq_refl
  symmetry proved by abstracts_perm_eq_symm
  transitivity proved by abstracts_perm_eq_trans as abstracts_perm_eq_setoid.

Add Parametric Morphism {A B} : relabel_abs with signature
  pointwise_relation A (@eq B) ==> abstracts_perm_eq ==>
  abstracts_perm_eq as relabel_abs_perm_mor.
Proof.
  intros f g Hfg abs abs' Habs.
  rewrite (relabel_abs_ext f g) by apply Hfg.
  unfold abstracts_perm_eq in *.
  destruct abs as [[i l] u], abs' as [[i' l'] u'].
  cbn in *.
  split_and!; easy + now apply fmap_Permutation.
Qed.

Import SetoidList SetoidPermutation list.

Definition ntl_perm_eq (ntl ntl' : namedtensorlist) :=
  ntl.(ntl_sums) = ntl'.(ntl_sums) /\
  PermutationA abstracts_perm_eq
    ntl.(ntl_abstracts) ntl'.(ntl_abstracts).

Definition ntl_perm_eq' (ntl ntl' : namedtensorlist) :=
  list_to_map (ntl.(ntl_sums)) =@{Pmap _} list_to_map (ntl'.(ntl_sums)) /\
  PermutationA abstracts_perm_eq
    ntl.(ntl_abstracts) ntl'.(ntl_abstracts).

Definition tl_perm_eq (tl tl' : tensorlist) :=
  tl.(tl_sums) = tl'.(tl_sums) /\
  PermutationA abstracts_perm_eq tl.(tl_abstracts) tl'.(tl_abstracts).

Infix "≡ntl≡ₚ" := ntl_perm_eq (at level 70).
Infix "≡ntl'≡ₚ" := ntl_perm_eq' (at level 70).
Infix "≡tl≡ₚ" := tl_perm_eq (at level 70).

Lemma ntl_perm_eq_refl ntl : ntl ≡ntl≡ₚ ntl.
Proof. easy. Qed.
Lemma ntl_perm_eq_symm ntl ntl' : ntl ≡ntl≡ₚ ntl' -> ntl' ≡ntl≡ₚ ntl.
Proof. intros []; split; now symmetry. Qed.
Lemma ntl_perm_eq_trans ntl ntl' ntl'' :
  ntl ≡ntl≡ₚ ntl' -> ntl' ≡ntl≡ₚ ntl'' -> ntl ≡ntl≡ₚ ntl''.
Proof. intros [] []; split; now etransitivity; eauto. Qed.

Add Parametric Relation : namedtensorlist ntl_perm_eq
  reflexivity proved by ntl_perm_eq_refl
  symmetry proved by ntl_perm_eq_symm
  transitivity proved by ntl_perm_eq_trans as ntl_perm_eq_setoid.

Lemma ntl_perm_eq'_refl ntl : ntl ≡ntl'≡ₚ ntl.
Proof. easy. Qed.
Lemma ntl_perm_eq'_symm ntl ntl' : ntl ≡ntl'≡ₚ ntl' -> ntl' ≡ntl'≡ₚ ntl.
Proof. intros []; split; now symmetry. Qed.
Lemma ntl_perm_eq'_trans ntl ntl' ntl'' :
  ntl ≡ntl'≡ₚ ntl' -> ntl' ≡ntl'≡ₚ ntl'' -> ntl ≡ntl'≡ₚ ntl''.
Proof. intros [] []; split; now etransitivity; eauto. Qed.

Add Parametric Relation : namedtensorlist ntl_perm_eq'
  reflexivity proved by ntl_perm_eq'_refl
  symmetry proved by ntl_perm_eq'_symm
  transitivity proved by ntl_perm_eq'_trans as ntl_perm_eq'_setoid.

#[export] Instance ntl_perm_eq_ntl_perm_eq' : subrelation ntl_perm_eq ntl_perm_eq'.
Proof.
  unfold ntl_perm_eq, ntl_perm_eq'.
  now intros ntl ntl' [-> ?].
Qed.

Lemma tl_perm_eq_refl tl : tl ≡tl≡ₚ tl.
Proof. easy. Qed.
Lemma tl_perm_eq_symm tl tl' : tl ≡tl≡ₚ tl' -> tl' ≡tl≡ₚ tl.
Proof. intros []; split; now symmetry. Qed.
Lemma tl_perm_eq_trans tl tl' tl'' :
  tl ≡tl≡ₚ tl' -> tl' ≡tl≡ₚ tl'' -> tl ≡tl≡ₚ tl''.
Proof. intros [] []; split; now etransitivity; eauto. Qed.

Add Parametric Relation : tensorlist tl_perm_eq
  reflexivity proved by tl_perm_eq_refl
  symmetry proved by tl_perm_eq_symm
  transitivity proved by tl_perm_eq_trans as tl_perm_eq_setoid.

Lemma fmap_eqlistA `{RA : relation A, RB : relation B}
  (f : A -> B) {Hf : Proper (RA ==> RB) f} (l l' : list A) :
  eqlistA RA l l' -> eqlistA RB (f <$> l) (f <$> l').
Proof.
  intros Hl.
  induction Hl; cbn; eauto using eqlistA.
Qed.

Lemma fmap_PermutationA `{RA : relation A, RB : relation B}
  (f : A -> B) (Hf : Proper (RA ==> RB) f) (l l' : list A) :
  PermutationA RA l l' -> PermutationA RB (f <$> l) (f <$> l').
Proof.
  intros Hl.
  induction Hl; cbn; eauto using PermutationA.
Qed.



Lemma ntl2tl_perm_eq ntl ntl' :
  ntl ≡ntl≡ₚ ntl' -> ntl2tl ntl ≡tl≡ₚ ntl2tl ntl'.
Proof.
  intros [Hsums Habs].
  destruct ntl as [isums abs], ntl' as [isums' abs'].
  cbn in *.
  subst isums'.
  split; [done|cbn].
  revert Habs.
  apply fmap_PermutationA, _.
Qed.

Lemma tl2ntl_perm_eq tl tl' :
  tl ≡tl≡ₚ tl' -> tl2ntl tl ≡ntl≡ₚ tl2ntl tl'.
Proof.
  intros [Hsums Habs].
  destruct tl as [sums abs], tl' as [sums' abs'].
  cbn in *.
  subst sums'.
  done.
Qed.

Lemma ntl_aeq_of_perm ntl ntl' :
  ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) ->
  ntl.(ntl_abstracts) ≡ₚ ntl'.(ntl_abstracts) ->
  ntl =ntl= ntl'.
Proof.
  destruct ntl as [isums abs], ntl' as [isums' abs'].
  cbn.
  intros Hsums Habs.
  exists id.
  split; [easy|].
  rewrite list_fmap_id' by now intros [] _.
  rewrite list_fmap_id' by now intros ? _; apply relabel_abs_id'; intros [].
  done.
Qed.


Lemma ntl_aeq_of_eq_map_NoDup ntl ntl' :
  NoDup ntl.(ntl_sums).*1 -> NoDup ntl'.(ntl_sums).*1 ->
  list_to_map ntl.(ntl_sums) =@{Pmap _} list_to_map ntl'.(ntl_sums) ->
  ntl.(ntl_abstracts) ≡ₚ ntl'.(ntl_abstracts) ->
  ntl =ntl= ntl'.
Proof.
  intros Hdup Hdup' Hmaps.
  apply ntl_aeq_of_perm.
  revert Hmaps.
  now apply list_to_map_inj.
Qed.

Lemma ntl_perm_eq'_NoDup ntl ntl' :
  NoDup ntl.(ntl_sums).*1 -> NoDup ntl'.(ntl_sums).*1 ->
  ntl ≡ntl'≡ₚ ntl' ->
  ntl =ntl= mk_ntl ntl'.(ntl_sums) ntl.(ntl_abstracts) /\
  mk_ntl ntl'.(ntl_sums) ntl.(ntl_abstracts) ≡ntl≡ₚ ntl'.
Proof.
  intros Hdup Hdup' [Hmap Habs].
  split; [|easy].
  now apply ntl_aeq_of_eq_map_NoDup.
Qed.


















Fixpoint list2vec {A} (n : nat) (l : list A) : option (vec A n) :=
  match n with
  | 0 => match l with
    | [] => Some [#]
    | _ => None
    end
  | S n' =>
    match l with
    | [] => None
    | a :: l => vcons a <$> list2vec n' l
    end
  end.

Lemma list2vec_eq_may_cast {A} n (l : list A) :
  list2vec n l = H ← guard (length l = n) ;
  Some (Vector.cast (Vector.of_list l) H).
Proof.
  revert l; induction n; intros [|a l].
  - reflexivity.
  - easy.
  - easy.
  - cbn.
    rewrite IHn.
    case_guard as Hlen; case_guard as Hlen'; [|lia..|reflexivity].
    cbn.
    f_equal.
    f_equal.
    f_equal; apply proof_irbound.
Qed.

Lemma option_bind_comm {A B C} (f : A -> B -> option C)
  (ma : option A) (mb : option B) :
  (ma ≫= λ a, mb ≫= λ b, f a b) =
  (mb ≫= λ b, ma ≫= λ a, f a b).
Proof.
  now destruct ma, mb.
Qed.

Lemma option_bind_fmap {A B C} (f : A -> option B) (g : B -> C)
  (ma : option A) :
  g <$> (ma ≫= f) = ma ≫= λ a, g <$> f a.
Proof.
  now destruct ma.
Qed.

Lemma option_fmap_bind {A B C} (f : A -> B) (g : B -> option C)
  (ma : option A) :
  ((f <$> ma) ≫= g) = ma ≫= g ∘ f.
Proof.
  now destruct ma.
Qed.

Lemma option_bind_assoc' {A B C} (f : A -> option B) (g : B -> option C)
  (ma : option A) :
  (ma ≫= f) ≫= g = ma ≫= λ a, f a ≫= g.
Proof.
  now destruct ma.
Qed.

Lemma join_list_fmap_mbind {A B} (f : A -> option B) (lm : list (option A)) :
  join_list (mbind f <$> lm) =
  l ← join_list lm;
  join_list (f <$> l).
Proof.
  induction lm as [|ma lm IHlm]; [reflexivity|].
  cbn.
  rewrite IHlm.
  destruct ma as [a|]; [|reflexivity].
  cbn.
  rewrite option_bind_assoc.
  destruct (join_list lm) as [l|]; [|now case_match].
  reflexivity.
Qed.

Add Parametric Morphism {A B} : (@mbind option _ A B) with signature
  pointwise_relation A eq ==> eq ==> eq as option_bind_mor.
Proof.
  intros; now apply option_bind_ext.
Qed.

Lemma join_list_app {A} (ml ml' : list (option A)) :
  join_list (ml ++ ml') =
  l ← join_list ml;
  (l ++.) <$> join_list ml'.
Proof.
  induction ml as [|ma ml IHml]; [cbn; now rewrite option_fmap_id|].
  cbn.
  rewrite IHml.
  case_match; [|reflexivity].
  cbn.
  rewrite 2 option_bind_assoc.
  unfold compose.
  cbn.
  setoid_rewrite option_fmap_bind.
  reflexivity.
Qed.

Lemma join_list_app' {A} (ml ml' : list (option A)) :
  join_list (ml ++ ml') =
  l' ← join_list ml';
  (.++ l') <$> join_list ml.
Proof.
  induction ml as [|ma ml IHml]; [cbn; now destruct (join_list ml')|].
  cbn.
  rewrite IHml.
  destruct ma as [a|].
  - rewrite option_bind_assoc.
    unfold compose.
    setoid_rewrite option_fmap_bind.
    reflexivity.
  - cbn.
    now destruct (join_list ml').
Qed.
Lemma option_fmap_to_bind {A B} (f : A -> B) (ma : option A) :
  f <$> ma = ma ≫= λ a, Some (f a).
Proof.
  reflexivity.
Qed.

Lemma option_bind_None_r {A B} (ma : option A) :
  (ma ≫= λ a, @None B) = None.
Proof.
  now destruct ma.
Qed.









Lemma join_list_Some_length {A} (ml : list (option A)) l :
  join_list ml = Some l ->
  length ml = length l.
Proof.
  intros Hlen%join_list_Some%(f_equal length).
  now rewrite length_fmap in Hlen.
Qed.

Lemma list2vec_plus n m {A} (l : list A) :
  list2vec (n + m) l =
  list2vec n (firstn n l) ≫= λ v, (v +++.) <$> list2vec m (skipn n l).
Proof.
  revert l; induction n; intros l.
  - cbn; rewrite take_0.
    cbn.
    now rewrite option_fmap_id.
  - cbn.
    destruct l as [|a l]; [reflexivity|].
    cbn.
    rewrite IHn.
    rewrite option_fmap_bind, option_bind_fmap.
    now destruct (list2vec m (drop n l)).
Qed.

(* FIXME: Find existing; consolidate *)
Lemma cast_id {A n} (v : vec A n) H :
  Vector.cast v H = v.
Proof.
  revert H; induction v; intros ?; cbn; f_equal; auto.
Qed.

Lemma list2vec_length {A} (l : list A) :
  list2vec (length l) l = Some (Vector.of_list l).
Proof.
  rewrite list2vec_eq_may_cast.
  case_guard; [|easy].
  cbn.
  now rewrite cast_id.
Qed.

Lemma list2vec_length' {A n} {l : list A} (H : length l = n) :
  list2vec n l = Some (Vector.cast (Vector.of_list l) H).
Proof.
  subst n.
  rewrite cast_id.
  apply list2vec_length.
Qed.

Lemma list2vec_app {A} (l l' : list A) :
  list2vec _ (l ++ l') = Some (Vector.of_list l +++ Vector.of_list l').
Proof.
  induction l; [apply list2vec_length|].
  cbn.
  now rewrite IHl.
Qed.

Lemma list2vec_app' {A n m} {l l' : list A }
  (Hl : length l = n) (Hl' : length l' = m) :
  list2vec (n + m) (l ++ l') =
    Some (Vector.cast (Vector.of_list l) Hl +++ Vector.cast (Vector.of_list l') Hl').
Proof.
  subst n m.
  now rewrite list2vec_app, 2 cast_id.
Qed.






Definition abst_WT' {A} (mabst : Pmap (nat * nat)) (abs : Idx * list A * list A) : Prop :=
  (mabst !! abs.1.1) = Some (length abs.1.2, length abs.2).

Add Parametric Morphism {A} mabst : (@abst_WT' A mabst) with signature
  abstracts_perm_eq ==> iff as abst_WT'_mor.
Proof.
  intros ((f, low), up) ((f', low'), up')
    ([= ->] & Hlow%Permutation_length & Hup%Permutation_length).
  unfold abst_WT'.
  cbn in *.
  f_equiv; congruence.
Qed.

Lemma join_list_Permutation {A} (ml ml' : list (option A)) :
  ml ≡ₚ ml' -> option_Forall2 Permutation (join_list ml) (join_list ml').
Proof.
  intros Hperm.
  pose proof (join_list_is_Some ml) as Hsome.
  rewrite Hperm in Hsome at 2.
  rewrite <- join_list_is_Some in Hsome.
  rewrite 2 is_Some_alt in Hsome.
  destruct (join_list ml) as [l|] eqn:Hl;
  destruct (join_list ml') as [l'|] eqn:Hl'; [|tauto..|];
  constructor.
  apply join_list_Some in Hl, Hl'.
  apply (f_equal (omap id)) in Hl, Hl'.
  rewrite list_omap_fmap in Hl, Hl'.
  unfold compose, id in Hl, Hl'.
  rewrite <- list_fmap_alt, list_fmap_id in Hl, Hl'.
  subst l l'.
  apply omap_Permutation.
  now rewrite Hperm.
Qed.

Lemma vec_to_list_cast {A m} (v : vec A m) {n} (H : m = n) :
  vec_to_list (Vector.cast v H) = v.
Proof.
  revert n H; induction v; intros ? <-; cbn; f_equal; auto.
Qed.



Lemma list2vec_Permutation n {A} (l l' : list A) :
  l ≡ₚ l' -> option_Forall2 (λ v v',
    vec_to_list v ≡ₚ vec_to_list v') (list2vec n l) (list2vec n l').
Proof.
  intros Hl.
  rewrite 2 list2vec_eq_may_cast.
  case_guard as Hlen; cbn;
  pose proof Hlen as Hlen';
  rewrite Hl in Hlen';
  case_guard; [|easy..|];
  cbn; constructor.
  rewrite 2 vec_to_list_cast.
  now rewrite 2 vec_to_list_to_vec.
Qed.


Lemma option_Forall2_alt {A B} (P : A -> B -> Prop) ma mb :
  option_Forall2 P ma mb <->
  match ma, mb with
  | Some a, Some b => P a b
  | None, None => True
  | _, _ => False
  end.
Proof.
  split; [now intros []|].
  destruct ma, mb; easy + now constructor.
Qed.
Lemma eqlistA_cons_iff `{eqA : relation A} {x x' : A} {l l' : list A} :
  eqlistA eqA (x :: l) (x' :: l') <-> eqA x x' /\ eqlistA eqA l l'.
Proof.
  split; [|now intros []; apply eqlistA_cons].
  intros Heq.
  inversion Heq; now subst.
Qed.
Lemma PermutationA_iff_exists_Forall2_Permutation
  `{RA : relation A} `{!Equivalence RA} l l' :
  PermutationA RA l l' <-> exists l'', l ≡ₚ l'' /\ Forall2 RA l'' l'.
Proof.
  split.
  - intros (l'' & Hl'' & Heq%eqlistA_altdef)%PermutationA_decompose; eauto.
  - intros (l'' & Hperm & Heq%eqlistA_altdef).
    etransitivity;
    [now apply Permutation_PermutationA; eauto|].
    now apply eqlistA_PermutationA.
Qed.



Lemma Forall2_iff_pred {A B} (P : A -> Prop) (Q : B -> Prop) (l : list A) l' :
  Forall2 (λ a b, P a <-> Q b) l l' ->
  Forall P l <-> Forall Q l'.
Proof.
  intros Hl.
  induction Hl; rewrite ?Forall_cons, ?Forall_nil; tauto.
Qed.

Lemma relabel_abs_WT'_iff {A B} mabst (f : A -> B) abs :
  abst_WT' mabst (relabel_abs f abs) <->
  abst_WT' mabst abs.
Proof.
  destruct abs as [[idx l] u]; cbn.
  unfold abst_WT'.
  cbn.
  now rewrite 2 length_fmap.
Qed.


Lemma ntl2tl_abst_WT'_all2 mabst ntl :
  Forall2 (λ a b, abst_WT' mabst a <-> abst_WT' mabst b)
    ntl.(ntl_abstracts) (ntl2tl ntl).(tl_abstracts).
Proof.
  destruct ntl as [isums abs].
  cbn.
  rewrite Forall2_fmap_r.
  apply Forall_Forall2_diag.
  rewrite Forall_forall.
  intros a _.
  cbn.
  symmetry; apply relabel_abs_WT'_iff.
Qed.


*)

From stdpp Require Import functions.


Definition prod_swap_eq {A} : relation (A * A) :=
  fun ab ab' => ab = ab' \/ prod_swap ab = ab'.

Lemma prod_swap_eq_pair {A} (a b a' b' : A) :
  prod_swap_eq (a, b) (a', b') <->
  a = a' /\ b = b' \/ a = b' /\ b = a'.
Proof.
  unfold prod_swap_eq.
  cbn.
  rewrite 2 pair_eq; tauto.
Qed.

Add Parametric Relation {A} : (A * A) prod_swap_eq
  reflexivity proved by
    ltac:(repeat first [intros []|intro|rewrite ?prod_swap_eq_pair in *; cbn in *; tauto])
  symmetry proved by
    ltac:(repeat first [intros [? ?]|intro|rewrite ?prod_swap_eq_pair in *; cbn in *; naive_solver])
  transitivity proved by
    ltac:(repeat first [intros [? ?]|intro|rewrite ?prod_swap_eq_pair in *; cbn in *; naive_solver])
  as prod_swap_eq_setoid.


From stdpp Require Import functions.

Import SetoidList SetoidPermutation stdpp.list.

Definition ntl_delta_perm_eq : relation namedtensorlist :=
  fun ntl ntl' =>
  ntl.(ntl_sums) = ntl'.(ntl_sums) /\
  ntl.(ntl_abstracts) = ntl'.(ntl_abstracts) /\
  PermutationA prod_swap_eq ntl.(ntl_deltas) ntl'.(ntl_deltas).

#[export] Program Instance ntl_delta_perm_eq_setoid : Equivalence ntl_delta_perm_eq.
Next Obligation.
  easy.
Qed.
Next Obligation.
  hnf.
  intros * Heq; hnf; split_and!; symmetry; apply Heq.
Qed.
Next Obligation.
  hnf.
  unfold ntl_delta_perm_eq.
  intros ??? (?&?&?) (?&?&?);
  split_and!; etransitivity; eassumption.
Qed.


(* FIXME: Move *)
#[export] Instance relation_elem_of {A B} : ElemOf (A * B) (A -> B -> Prop) :=
  fun ab R => R ab.1 ab.2.
#[export] Instance relation_empty {A B} : Empty (A -> B -> Prop) :=
  fun a b => False.
#[export] Instance relation_top {A B} : Top (A -> B -> Prop) :=
  fun a b => True.
#[export] Instance relation_singleton {A B} : Singleton (A * B) (A -> B -> Prop) :=
  fun ab => fun a b => (a, b) = ab.
#[export] Instance relation_union {A B} : Union (A -> B -> Prop) :=
  fun R R' => fun a b => R a b \/ R' a b.
#[export] Instance relation_intersection {A B} : Intersection (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ R' a b.
#[export] Instance relation_difference {A B} : Difference (A -> B -> Prop) :=
  fun R R' => fun a b => R a b /\ ~ R' a b.

#[global] Arguments relation_elem_of {_ _} _ _ / : assert.
#[global] Arguments relation_empty {_ _} _ _ / : assert.
#[global] Arguments relation_top {_ _} _ _ / : assert.
#[global] Arguments relation_singleton {_ _} _ _ _ / : assert.
#[global] Arguments relation_union {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_intersection {_ _} _ _ _ _ / : assert.
#[global] Arguments relation_difference {_ _} _ _ _ _ / : assert.




#[export] Program Instance relation_semi_set {A B} : SemiSet (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_set {A B} : Set_ (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).

#[export] Program Instance relation_top_set {A B} : TopSet (A * B) (A -> B -> Prop).
Solve All Obligations with (repeat first [intros []|intro|cbv in *; tauto]).



Definition ntl_delta_subst (lb : positive) (r : var) : relation namedtensorlist :=
  fun ntl ntl' =>
  r <> bound lb /\
  ntl.(ntl_sums) ≡ₚ lb :: ntl'.(ntl_sums) /\
  ntl'.(ntl_abstracts) = relabel_abs {[bound lb := r]} <$> ntl.(ntl_abstracts) /\
  head ntl.(ntl_deltas) = Some (bound lb, r) /\
  ntl'.(ntl_deltas) = relabel_delt {[bound lb := r]} <$> tail ntl.(ntl_deltas).

Definition ntl_delta_idemp (v : var) : relation namedtensorlist :=
  fun ntl ntl' =>
  ntl.(ntl_sums) = ntl'.(ntl_sums) /\
  ntl'.(ntl_abstracts) = ntl.(ntl_abstracts) /\
  ntl'.(ntl_deltas) = (v, v) :: ntl.(ntl_deltas).

Definition psets_to_varset (bounds frees : Pset) : gset var :=
  set_map bound bounds ∪ set_map free frees.

Lemma elem_of_psets_to_varset bounds frees v :
  v ∈ psets_to_varset bounds frees <->
  match v with
  | bound r => r ∈ bounds
  | free l => l ∈ frees
  end.
Proof.
  unfold psets_to_varset.
  destruct v; set_solver.
Qed.

(* FIXME: Move *)
Lemma ntl_aeq_WF ntl ntl' :
  ntl =ntl= ntl' -> WF_ntl ntl -> WF_ntl ntl'.
Proof.
  intros (fr & Hfr & Hfsums & Hfabs & Hfdelt).
  intros (Hdup & Habs & Hdelt).
  split; [|split].
  - rewrite <- Hfsums.
    apply NoDup_fmap_2_strong, Hdup.
    intros ? ? Hx Hy; apply Hfr; set_solver + Hx Hy.
  - rewrite <- Hfabs, <- Hfsums.
    rewrite <- (set_map_list_to_set (SA:=Pset)),
      abstracts_bound_vars_relabel_bounds.
    now apply set_map_mono.
  - rewrite <- Hfdelt, <- Hfsums.
    rewrite <- (set_map_list_to_set (SA:=Pset)),
      deltas_bound_vars_relabel_bounds.
    now apply set_map_mono.
Qed.

Definition WT_ntl (tl : Pset) (ntl : namedtensorlist) :=
  abstracts_free_vars ntl.(ntl_abstracts) ⊆ tl /\
  deltas_free_vars ntl.(ntl_deltas) ⊆ tl /\
  WF_ntl ntl.

Inductive ntl_delta_eq (tl : Pset) : relation namedtensorlist :=
  | ntl_delta_eq_idemp v ntl ntl' :
    v ∈ psets_to_varset (list_to_set ntl.(ntl_sums)) tl ->
    ntl_delta_idemp v ntl ntl' -> ntl_delta_eq tl ntl ntl'
  | ntl_delta_eq_subst lb r ntl ntl' :
    lb ∉ ntl'.(ntl_sums) ->
    r ∈ psets_to_varset (list_to_set ntl'.(ntl_sums)) tl ->
    ntl_delta_subst lb r ntl ntl' -> ntl_delta_eq tl ntl ntl'
  | ntl_delta_eq_perm ntl ntl' :
    ntl_delta_perm_eq ntl ntl' -> ntl_delta_eq tl ntl ntl'
  | ntl_delta_eq_symm ntl ntl' :
    ntl_delta_eq tl ntl ntl' -> ntl_delta_eq tl ntl' ntl
  | ntl_delta_eq_trans ntl ntl' ntl'' :
    ntl_delta_eq tl ntl ntl' -> ntl_delta_eq tl ntl' ntl'' ->
    ntl_delta_eq tl ntl ntl''.

Add Parametric Relation tl : namedtensorlist (ntl_delta_eq tl)
  reflexivity proved by
    ltac:(intros ?; apply ntl_delta_eq_perm; done)
  symmetry proved by (ntl_delta_eq_symm _)
  transitivity proved by (ntl_delta_eq_trans _)
  as ntl_delta_eq_setoid.

Lemma ntl_delta_idemp_WF tl v ntl ntl' :
  v ∈ psets_to_varset (list_to_set ntl.(ntl_sums)) tl ->
  ntl_delta_idemp v ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  intros Hv Heq.
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct Heq as (<- & -> & ->).
  cbn.
  unfold WF_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  do 2 f_equiv.
  destruct v as [r|l]; [|reflexivity].
  rewrite elem_of_psets_to_varset in Hv.
  set_solver +Hv.
Qed.

Lemma ntl_delta_idemp_WT tl v ntl ntl' :
  v ∈ psets_to_varset (list_to_set ntl.(ntl_sums)) tl ->
  ntl_delta_idemp v ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  intros Hv Heq.
  unfold WT_ntl.
  rewrite 2 (and_assoc _).
  f_equiv; [|now eapply ntl_delta_idemp_WF; eauto].
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct Heq as (<- & -> & ->).
  f_equiv.
  destruct v as [r|l]; [reflexivity|].
  rewrite elem_of_psets_to_varset in Hv.
  set_solver +Hv.
Qed.


Lemma v2bound_Some (v : var) (r : Idx) : v2bound v = Some r <-> v = bound r.
Proof.
  destruct v; cbn; firstorder congruence.
Qed.

Lemma v2free_Some (v : var) (r : Idx) : v2free v = Some r <-> v = free r.
Proof.
  destruct v; cbn; firstorder congruence.
Qed.


Lemma elem_of_abstracts_vars v abs :
  v ∈ abstracts_vars abs <-> exists idx low up,
    (idx, low, up) ∈ abs /\ v ∈ low ++ up.
Proof.
  set_unfold.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_app.
  firstorder.
Qed.

Lemma elem_of_deltas_vars v delt :
  v ∈ deltas_vars delt <-> exists l u,
    (l, u) ∈ delt /\ (v = l \/ v = u).
Proof.
  set_unfold.
  rewrite exists_pair.
  set_solver.
Qed.

Lemma abstracts_bound_vars_relabel_abs (f : var -> var) (abs : _) :
  abstracts_bound_vars (relabel_abs f <$> abs) =
  set_omap (v2bound ∘ f) (abstracts_vars abs).
Proof.
  apply set_eq; intros r.
  rewrite elem_of_abstracts_bound_vars.
  rewrite elem_of_set_omap.
  cbn.
  setoid_rewrite v2bound_Some.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_abstracts_vars.
  do 2 setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  setoid_rewrite pair_eq.
  firstorder.
  - subst.
    rewrite <- fmap_app, elem_of_list_fmap in *.
    naive_solver.
  - eexists _, _, _.
    split; [|replace <- (bound r);
      erewrite <- fmap_app; apply elem_of_list_fmap_1; eassumption].
    naive_solver.
Qed.

Lemma deltas_bound_vars_relabel_delt (f : var -> var) (abs : _) :
  deltas_bound_vars (relabel_delt f <$> abs) =
  set_omap (v2bound ∘ f) (deltas_vars abs).
Proof.
  apply set_eq; intros r.
  rewrite elem_of_deltas_bound_vars.
  rewrite elem_of_set_omap.
  cbn.
  setoid_rewrite v2bound_Some.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_deltas_vars.
  setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  split; [|naive_solver].
  firstorder; subst; [|naive_solver].
  eexists; split; [|eassumption].
  naive_solver.
Qed.


Lemma abstracts_free_vars_relabel_abs (f : var -> var) (abs : _) :
  abstracts_free_vars (relabel_abs f <$> abs) =
  set_omap (v2free ∘ f) (abstracts_vars abs).
Proof.
  apply set_eq; intros r.
  rewrite elem_of_abstracts_free_vars.
  rewrite elem_of_set_omap.
  cbn.
  setoid_rewrite v2free_Some.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_abstracts_vars.
  do 2 setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  setoid_rewrite pair_eq.
  firstorder.
  - subst.
    rewrite <- fmap_app, elem_of_list_fmap in *.
    naive_solver.
  - eexists _, _, _.
    split; [|replace <- (free r);
      erewrite <- fmap_app; apply elem_of_list_fmap_1; eassumption].
    naive_solver.
Qed.

Lemma deltas_free_vars_relabel_delt (f : var -> var) (abs : _) :
  deltas_free_vars (relabel_delt f <$> abs) =
  set_omap (v2free ∘ f) (deltas_vars abs).
Proof.
  apply set_eq; intros r.
  rewrite elem_of_deltas_free_vars.
  rewrite elem_of_set_omap.
  cbn.
  setoid_rewrite v2free_Some.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_deltas_vars.
  setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  split; [|naive_solver].
  firstorder; subst; [|naive_solver].
  eexists; split; [|eassumption].
  naive_solver.
Qed.

Lemma abstracts_vars_decomp abs :
  abstracts_vars abs =
  set_map bound (abstracts_bound_vars abs) ∪
  set_map free (abstracts_free_vars abs).
Proof.
  apply set_eq; intros v.
  rewrite elem_of_abstracts_vars.
  rewrite elem_of_union, 2 elem_of_map.
  setoid_rewrite elem_of_abstracts_bound_vars.
  setoid_rewrite elem_of_abstracts_free_vars.
  destruct v; cbn; set_solver.
Qed.

Lemma deltas_vars_decomp abs :
  deltas_vars abs =
  set_map bound (deltas_bound_vars abs) ∪
  set_map free (deltas_free_vars abs).
Proof.
  apply set_eq; intros v.
  rewrite elem_of_deltas_vars.
  rewrite elem_of_union, 2 elem_of_map.
  setoid_rewrite elem_of_deltas_bound_vars.
  setoid_rewrite elem_of_deltas_free_vars.
  destruct v; cbn; set_solver.
Qed.


Lemma set_omap_set_map `{FinSet A SA, FinSet B SB, FinSet C SC}
  (f : A -> B) (g : B -> option C) (X : SA) :
  set_omap g (set_map f X :> SB) ≡@{SC} set_omap (g ∘ f) X.
Proof.
  set_solver.
Qed.

Lemma list_to_set_filter `{P : A -> Prop} `{forall a, Decision (P a)}
  `{FinSet A SA} (l : list A) :
  list_to_set (filter P l) ≡@{SA} filter P (list_to_set l).
Proof.
  set_unfold.
  now intros; rewrite elem_of_list_filter.
Qed.

Lemma abstracts_bound_vars_relabel_abs_singleton lb r abs :
  abstracts_bound_vars (relabel_abs {[bound lb := r]} <$> abs) =
  abstracts_bound_vars abs ∖ {[lb]} ∪ if decide (lb ∈ abstracts_bound_vars abs)
    then list_to_set (omap v2bound [r]) else ∅.
Proof.
  rewrite abstracts_bound_vars_relabel_abs, abstracts_vars_decomp.
  unfold_leibniz.
  rewrite set_omap_union, 2 set_omap_set_map.
  assert (Hemp : set_omap (v2bound ∘ {[bound lb := r]} ∘ free)
    (abstracts_free_vars abs) =@{Pset} ∅). 1:{
    apply elem_of_equiv_empty_L.
    intros b.
    rewrite elem_of_set_omap.
    cbn.
    intros (? & ? & Heq).
    rewrite fn_lookup_singleton_ne in Heq by congruence.
    easy.
  }
  rewrite Hemp, (union_empty_r _).
  case_decide as Helem.
  - intros v.
    rewrite elem_of_set_omap.
    rewrite elem_of_union, elem_of_difference.
    setoid_rewrite elem_of_abstracts_bound_vars.
    cbn.
    setoid_rewrite v2bound_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (r' & (idx & low & up & Hflu & Hbnd) & Hdec).
      case_decide as Heq.
      * subst.
        right.
        set_solver +.
      * left.
        set_solver.
    + intros [[(idx & low & up & Hflu & Hbnd) Hv] | Hv].
      * exists v.
        rewrite decide_False by set_solver +Hv.
        eauto 20.
      * destruct r as [r|]; [|easy].
        cbn -[list_to_set] in Hv.
        rewrite list_to_set_singleton, elem_of_singleton in Hv.
        subst v.
        apply elem_of_abstracts_bound_vars in Helem
          as (idx & low & up & Hflu & Hbnd).
        exists lb.
        rewrite decide_True by easy.
        eauto 20.
  - transitivity (abstracts_bound_vars abs); [|set_solver +Helem].
    intros x.
    rewrite elem_of_set_omap.
    cbn.
    setoid_rewrite v2bound_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (x' & Hx' & Hlook).
      rewrite decide_False in Hlook by congruence.
      congruence.
    + intros Hx.
      exists x.
      split; [easy|].
      now rewrite decide_False by congruence.
Qed.

Lemma deltas_bound_vars_relabel_delt_singleton lb r delt :
  deltas_bound_vars (relabel_delt {[bound lb := r]} <$> delt) =
  deltas_bound_vars delt ∖ {[lb]} ∪ if decide (lb ∈ deltas_bound_vars delt)
    then list_to_set (omap v2bound [r]) else ∅.
Proof.
  rewrite deltas_bound_vars_relabel_delt, deltas_vars_decomp.
  unfold_leibniz.
  rewrite set_omap_union, 2 set_omap_set_map.
  assert (Hemp : set_omap (v2bound ∘ {[bound lb := r]} ∘ free)
    (deltas_free_vars delt) =@{Pset} ∅). 1:{
    apply elem_of_equiv_empty_L.
    intros b.
    rewrite elem_of_set_omap.
    cbn.
    intros (? & ? & Heq).
    rewrite fn_lookup_singleton_ne in Heq by congruence.
    easy.
  }
  rewrite Hemp, (union_empty_r _).
  case_decide as Helem.
  - intros v.
    rewrite elem_of_set_omap.
    rewrite elem_of_union, elem_of_difference.
    setoid_rewrite elem_of_deltas_bound_vars.
    cbn.
    setoid_rewrite v2bound_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (r' & (low & up & Hflu & Hbnd) & Hdec).
      case_decide as Heq.
      * subst.
        right.
        set_solver +.
      * left.
        set_solver.
    + intros [[(low & up & Hflu & Hbnd) Hv] | Hv].
      * exists v.
        rewrite decide_False by set_solver +Hv.
        eauto 20.
      * destruct r as [r|]; [|easy].
        cbn -[list_to_set] in Hv.
        rewrite list_to_set_singleton, elem_of_singleton in Hv.
        subst v.
        apply elem_of_deltas_bound_vars in Helem
          as (low & up & Hflu & Hbnd).
        exists lb.
        rewrite decide_True by easy.
        eauto 20.
  - transitivity (deltas_bound_vars delt); [|set_solver +Helem].
    intros x.
    rewrite elem_of_set_omap.
    cbn.
    setoid_rewrite v2bound_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (x' & Hx' & Hlook).
      rewrite decide_False in Hlook by congruence.
      congruence.
    + intros Hx.
      exists x.
      split; [easy|].
      now rewrite decide_False by congruence.
Qed.


Lemma abstracts_free_vars_relabel_abs_singleton lb r abs :
  abstracts_free_vars (relabel_abs {[bound lb := r]} <$> abs) =
  abstracts_free_vars abs ∪ if decide (lb ∈ abstracts_bound_vars abs)
    then list_to_set (omap v2free [r]) else ∅.
Proof.
  rewrite abstracts_free_vars_relabel_abs, abstracts_vars_decomp.
  unfold_leibniz.
  rewrite set_omap_union, 2 set_omap_set_map.
  rewrite (union_comm _).
  f_equiv.
  - intros b.
    rewrite elem_of_set_omap.
    cbn.
    setoid_rewrite v2free_Some.
    setoid_rewrite fn_lookup_singleton_ne; [|easy].
    naive_solver.
  - intros x.
    rewrite elem_of_set_omap.
    cbn -[omap].
    setoid_rewrite v2free_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (lb' & Hlb & Hdec).
      case_decide as Heq; [|easy].
      subst r.
      rewrite decide_True by congruence.
      set_solver +.
    + case_decide as Hlb; [|easy].
      destruct r as [|r]; [easy|].
      intros Hx.
      assert (x = r) by set_solver +Hx.
      subst x.
      exists lb.
      split; [easy|].
      now apply decide_True.
Qed.

Lemma deltas_free_vars_relabel_delt_singleton lb r delt :
  deltas_free_vars (relabel_delt {[bound lb := r]} <$> delt) =
  deltas_free_vars delt ∪ if decide (lb ∈ deltas_bound_vars delt)
    then list_to_set (omap v2free [r]) else ∅.
Proof.
  rewrite deltas_free_vars_relabel_delt, deltas_vars_decomp.
  unfold_leibniz.
  rewrite set_omap_union, 2 set_omap_set_map.
  rewrite (union_comm _).
  f_equiv.
  - intros b.
    rewrite elem_of_set_omap.
    cbn.
    setoid_rewrite v2free_Some.
    setoid_rewrite fn_lookup_singleton_ne; [|easy].
    naive_solver.
  - intros x.
    rewrite elem_of_set_omap.
    cbn -[omap].
    setoid_rewrite v2free_Some.
    setoid_rewrite fn_lookup_singleton_case.
    split.
    + intros (lb' & Hlb & Hdec).
      case_decide as Heq; [|easy].
      subst r.
      rewrite decide_True by congruence.
      set_solver +.
    + case_decide as Hlb; [|easy].
      destruct r as [|r]; [easy|].
      intros Hx.
      assert (x = r) by set_solver +Hx.
      subst x.
      exists lb.
      split; [easy|].
      now apply decide_True.
Qed.



Lemma subseteq_union_r `{Set_ A SA} `{!RelDecision (∈@{SA})} (X Y Z : SA):
  X ⊆ Y ∪ Z <-> X ∖ Y ⊆ Z.
Proof.
  (* intros ?. *)
  split; [set_solver|].
  set_unfold.
  intros HXY x Hx.
  destruct_decide (decide (x ∈ Y)); [now left|right; now apply HXY].
Qed.

Lemma ntl_delta_subst_WF tl lb r ntl ntl' :
  lb ∉ ntl'.(ntl_sums) ->
  r ∈ psets_to_varset (list_to_set ntl'.(ntl_sums)) tl ->
  ntl_delta_subst lb r ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  intros Hlb Hr Heq.
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct delt as [|lu delt]; [easy|].
  cbn in Heq.
  destruct Heq as (Hneq & Hsums & -> & [= ->] & ->).
  unfold WF_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  rewrite Hsums.
  rewrite NoDup_cons.
  apply and_iff_from_l; [set_solver + Hlb|].
  intros _ Hdup.
  rewrite abstracts_bound_vars_relabel_abs_singleton.
  rewrite deltas_bound_vars_relabel_delt_singleton.
  rewrite elem_of_psets_to_varset in Hr.
  f_equiv.
  - rewrite list_to_set_cons.
    rewrite subseteq_union_r.
    split; [|set_solver +].
    intros Hsubs.
    rewrite union_subseteq;
    split; [easy|].
    case_decide as Hlb'; [|set_solver+].
    destruct r; [|set_solver +].
    set_solver +Hr.
  - rewrite list_to_set_cons.
    rewrite subseteq_union_r.
    case_decide as Hlb'.
    + split; [|set_solver +].
      destruct r; set_solver + Hr.
    + split; [set_solver +|].
      destruct r; set_solver + Hr.
Qed.


Lemma ntl_delta_subst_WT tl lb r ntl ntl' :
  lb ∉ ntl'.(ntl_sums) ->
  r ∈ psets_to_varset (list_to_set ntl'.(ntl_sums)) tl ->
  ntl_delta_subst lb r ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  intros Hlb Hr Heq.
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  unfold WT_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  rewrite 2 (and_assoc _), 2 (and_comm _ (WF_ntl _)).
  apply and_iff_from_l; [now eapply ntl_delta_subst_WF; eauto|].
  intros HWF HWF'.
  destruct delt as [|lu delt]; [easy|].
  cbn in Heq.
  destruct Heq as (Hneq & Hsums & -> & [= ->] & ->).
  unfold WF_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  rewrite abstracts_free_vars_relabel_abs_singleton.
  rewrite deltas_free_vars_relabel_delt_singleton.
  rewrite elem_of_psets_to_varset in Hr.
  enough (list_to_set (omap v2free [r]) ⊆ tl) as Hsub by
    now f_equiv; case_decide; set_solver + Hsub.
  destruct r as [|r]; [set_solver+|].
  set_solver +Hr.
Qed.

Lemma deltas_bound_vars_cons lu delt :
  deltas_bound_vars (lu :: delt) =
  list_to_set (omap v2bound [lu.1; lu.2]) ∪ deltas_bound_vars delt.
Proof.
  destruct lu; cbn; set_solver.
Qed.


Lemma deltas_free_vars_cons lu delt :
  deltas_free_vars (lu :: delt) =
  list_to_set (omap v2free [lu.1; lu.2]) ∪ deltas_free_vars delt.
Proof.
  destruct lu; cbn; set_solver.
Qed.

Lemma deltas_bound_vars_permA_mor :
  Proper (PermutationA prod_swap_eq ==> eq) deltas_bound_vars.
Proof.
  intros delt delt' Hdelt.
  induction Hdelt as [|x y delt delt' Hx Hdelt| |];
    [reflexivity| |set_solver|etransitivity; eassumption].
  rewrite 2 deltas_bound_vars_cons.
  f_equiv; [|easy].
  destruct Hx as [<- | <-]; [done|].
  unfold_leibniz.
  apply list_to_set_perm.
  destruct x as [[] []]; cbn; [solve_Permutation|done..].
Qed.


Lemma deltas_free_vars_permA_mor :
  Proper (PermutationA prod_swap_eq ==> eq) deltas_free_vars.
Proof.
  intros delt delt' Hdelt.
  induction Hdelt as [|x y delt delt' Hx Hdelt| |];
    [reflexivity| |set_solver|etransitivity; eassumption].
  rewrite 2 deltas_free_vars_cons.
  f_equiv; [|easy].
  destruct Hx as [<- | <-]; [done|].
  unfold_leibniz.
  apply list_to_set_perm.
  destruct x as [[] []]; cbn; [done..|solve_Permutation].
Qed.




Lemma ntl_delta_perm_eq_WF ntl ntl' :
  ntl_delta_perm_eq ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  intros (Hsum & Habs & Hdelt).
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  unfold WF_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  subst sums' abs'.
  f_equiv.
  f_equiv.
  f_equiv.
  now apply eq_reflexivity,
    deltas_bound_vars_permA_mor.
Qed.


Lemma ntl_delta_perm_eq_WT tl ntl ntl' :
  ntl_delta_perm_eq ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  intros (Hsum & Habs & Hdelt).
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  unfold WT_ntl;
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  subst sums' abs'.
  f_equiv.
  f_equiv; [|now apply ntl_delta_perm_eq_WF].
  f_equiv.
  now apply eq_reflexivity,
    deltas_free_vars_permA_mor.
Qed.

Lemma ntl_delta_eq_WF tl ntl ntl' :
  ntl_delta_eq tl ntl ntl' ->
  WF_ntl ntl <-> WF_ntl ntl'.
Proof.
  induction 1.
  - eauto using ntl_delta_idemp_WF.
  - eauto using ntl_delta_subst_WF.
  - eauto using ntl_delta_perm_eq_WF.
  - easy.
  - etransitivity; eassumption.
Qed.

Lemma ntl_delta_eq_WT tl ntl ntl' :
  ntl_delta_eq tl ntl ntl' ->
  WT_ntl tl ntl <-> WT_ntl tl ntl'.
Proof.
  induction 1.
  - eauto using ntl_delta_idemp_WT.
  - eauto using ntl_delta_subst_WT.
  - eauto using ntl_delta_perm_eq_WT.
  - easy.
  - etransitivity; eassumption.
Qed.



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

(* FIXME: Move *)
Add Parametric Morphism {A B} : (relabel_delt) with signature
  pointwise_relation A (@eq B) ==> eq ==>
  eq as relabel_delt_mor.
Proof.
  intros; now apply relabel_delt_ext.
Qed.

(*
Lemma simplify_ntl_deltas_relabel fsubst summed delt delt_other abs :
  simplify_ntl_deltas_aux (fsubst) summed delt delt_other abs =
  prod_map (prod_map (prod_map (.∪ fsubst) id) id) id $
  simplify_ntl_deltas_aux ∅ summed
    (relabel_delt (gmap_map fsubst) <$> delt)
    (relabel_delt (gmap_map fsubst) <$> delt_other)
    (relabel_abs (gmap_map fsubst) <$> abs).
Proof.
  revert fsubst summed delt_other abs.
  induction delt as [delt IHdelt] using (Nat.measure_induction _ (@length (var*var))).
  intros fsubst summed delt_other abs.
  destruct delt as [|(l_, r_) delt].
  - cbn.
    rewrite (map_empty_union _).
    repeat apply (f_equal2 pair);
    [done|done|symmetry; rewrite <- list_fmap_compose;
      apply list_fmap_ext;
      intros _ lu _;
      cbn;
      rewrite gmap_map_empty
      (* rewrite ?relabel_delt_compose;
      try apply relabel_delt_ext *)
      ..];
    [now rewrite relabel_delt_id|now rewrite relabel_abs_id].
  - cbn delta [simplify_ntl_deltas_aux] fix match.
    set (l := gmap_map fsubst l_).
    set (r := gmap_map fsubst r_).
    cbv zeta.


    case_decide as Hlr. 1:{
      rewrite IHdelt by now cbn; lia.
      f_equal.
      cbn.
      rewrite 2 gmap_map_empty.
      now rewrite decide_True by easy.
    }
    cbn.
    rewrite 2 gmap_map_empty.
    rewrite decide_False by easy.
    cbn.
    fold l r.
    case_match eqn:Hl.
    + case_decide as Hlsummed.
      * rewrite IHdelt by now cbn; lia.
        symmetry.
        rewrite IHdelt by now rewrite length_fmap; cbn; lia.


    setoid_rewrite list_fmap_ext.
    erewrite (list_fmap_mor _ _ (gmap_map ∅ :> var -> var)). by first [apply gmap_map_empty|reflexivity].
    (* relabel_delt_mor *)
    rewrite gmap_map_empty at 1. *)



(* Lemma simplify_ntl_deltas_insert v v' fsubst summed delt delt_other abs :

  simplify_ntl_deltas_aux (<[v := v']> fsubst) summed delt delt_other abs =
  prod_map (prod_map (prod_map <[v := v']> id) id) id $
  simplify_ntl_deltas_aux fsubst summed
    (relabel_delt {[v := v']} <$> delt)
    (relabel_delt {[v := v']} <$> delt_other)
    (relabel_abs {[v := v']} <$> abs).
Proof.
  revert fsubst summed delt_other abs.
  induction delt as [delt IHdelt] using (Nat.measure_induction _ (@length (var*var))).
  intros fsubst summed delt_other abs.
  destruct delt as [|(l, r) delt].
  - cbn.


  (length delt)  *)


(* Lemma simplify_ntl_deltas_cons  *)

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



(* Fixpoint simplify_ntl_deltas_aux (fsubst : gmap var var) (summed : list Idx)
  (delt : list (var * var)) (delt_other : list (var * var)) (abs : list (Idx * list var * list var)) :
    gmap var var * list Idx * list (var * var) *
    list (Idx * list var * list var) :=
  match delt with
  | [] => (fsubst, summed, relabel_delt (gmap_map fsubst) <$> delt_other,
    relabel_abs (gmap_map fsubst) <$> abs)
  | (l_, r_) :: delt =>
    let l := gmap_map fsubst l_ in let r := gmap_map fsubst r_ in
    if decide (l = r) then simplify_ntl_deltas_aux fsubst summed delt delt_other abs else
    let neither :=
      simplify_ntl_deltas_aux fsubst summed delt (delt_other ++ [(l, r)]) abs in
    let not_l :=
      match r with
      | free _ =>
        neither
      | bound rb =>
        if decide (rb ∈ summed) then
          simplify_ntl_deltas_aux (<[bound rb := l]> fsubst)
            (filter (.≠ rb) summed) delt delt_other abs
        else
          neither
      end in
    match l with
    | bound lb =>
      if decide (lb ∈ summed) then
        simplify_ntl_deltas_aux (<[bound lb := r]> fsubst)
          (filter (.≠ lb) summed) delt delt_other abs
      else
        not_l
    | free _ => not_l
    end
  end. *)

Definition get_subst (summed : list Idx) (l r : var) : option (Idx * var) :=
  match l with
  | bound lr =>
    if decide (lr ∈ summed) then
      Some (lr, r)
    else
      match r with
      | bound rr =>
        if decide (rr ∈ summed) then
          Some (rr, l)
        else
          None
      | free _ => None
      end
  | free _ =>
    match r with
    | bound rr =>
      if decide (rr ∈ summed) then
        Some (rr, l)
      else
        None
    | free _ => None
    end
  end.


Fixpoint simplify_ntl_deltas_aux (summed : list Idx)
  {n} : forall (delt : vec (var * var) n) (delt_other : list (var * var))
    (abs : list (Idx * list var * list var)),
    list Idx * list (var * var) *
    list (Idx * list var * list var) :=
  match n (* delt *) with
  | O (* [# ] *) => fun delt delt_other abs => (summed, delt_other, abs)
  | S n' (* (l, r) ::: delt *) =>
    fun delt' delt_other abs =>
    let '(l, r) := Vector.hd delt' in
    let delt := Vector.tl delt' in
    if decide (l = r) then
      simplify_ntl_deltas_aux summed delt delt_other abs
    else
      match get_subst summed l r with
      | Some (iold, vnew) =>
        simplify_ntl_deltas_aux (filter (.≠iold) summed)
          (vmap (relabel_delt {[bound iold := vnew]}) delt)
          (relabel_delt {[bound iold := vnew]} <$> delt_other)
          (relabel_abs {[bound iold := vnew]} <$> abs)
      | None =>
        simplify_ntl_deltas_aux summed delt ((l, r) :: delt_other) abs
      end
  end.

Lemma simplify_ntl_deltas_aux_unfold summed {n} (delt : vec _ n) delt_other abs :
  simplify_ntl_deltas_aux summed delt delt_other abs =
  match delt with
  | [# ] => (summed, delt_other, abs)
  | (l, r) ::: delt =>
    if decide (l = r) then
      simplify_ntl_deltas_aux summed delt delt_other abs
    else
      match get_subst summed l r with
      | Some (iold, vnew) =>
        simplify_ntl_deltas_aux (filter (.≠iold) summed)
          (vmap (relabel_delt {[bound iold := vnew]}) delt)
          (relabel_delt {[bound iold := vnew]} <$> delt_other)
          (relabel_abs {[bound iold := vnew]} <$> abs)
      | None =>
        simplify_ntl_deltas_aux summed delt ((l, r) :: delt_other) abs
      end
  end.
Proof.
  destruct delt as [|(l, r) delt]; reflexivity.
Qed.


Lemma simplify_ntl_deltas_cons summed {n} (delt : vec _ n) delt_other abs lr :
  simplify_ntl_deltas_aux summed (lr ::: delt) delt_other abs =
  if decide (lr.1 = lr.2) then
    simplify_ntl_deltas_aux summed delt delt_other abs
  else
    match get_subst summed lr.1 lr.2 with
    | Some (iold, vnew) =>
      simplify_ntl_deltas_aux (filter (.≠iold) summed)
        (vmap (relabel_delt {[bound iold := vnew]}) delt)
        (relabel_delt {[bound iold := vnew]} <$> delt_other)
        (relabel_abs {[bound iold := vnew]} <$> abs)
    | None =>
      simplify_ntl_deltas_aux summed delt (lr :: delt_other) abs
    end.
Proof.
  rewrite simplify_ntl_deltas_aux_unfold.
  now destruct lr.
Qed.


Lemma get_subst_correct_aux sums l r iold vnew :
  get_subst sums l r = Some (iold, vnew) ->
  prod_swap_eq (l, r) (bound iold, vnew) /\
  iold ∈ sums.
Proof.
  rewrite prod_swap_eq_pair.
  unfold get_subst.
  repeat case_match; subst; cbn; naive_solver congruence.
Qed.

Lemma set_omap_v2bound_deltas_vars delt :
  set_omap v2bound (deltas_vars delt) = deltas_bound_vars delt.
Proof.
  rewrite <- (deltas_bound_vars_relabel_delt id).
  f_equal.
  apply list_fmap_id'; intros ? _;
  apply relabel_delt_id.
Qed.

Lemma set_omap_v2free_deltas_vars delt :
  set_omap v2free (deltas_vars delt) = deltas_free_vars delt.
Proof.
  rewrite <- (deltas_free_vars_relabel_delt id).
  f_equal.
  apply list_fmap_id'; intros ? _;
  apply relabel_delt_id.
Qed.

Lemma set_omap_v2bound_abstracts_vars abs :
  set_omap v2bound (abstracts_vars abs) = abstracts_bound_vars abs.
Proof.
  rewrite <- (abstracts_bound_vars_relabel_abs id).
  f_equal.
  apply list_fmap_id'; intros ? _;
  apply relabel_abs_id.
Qed.

Lemma set_omap_v2free_abstracts_vars abs :
  set_omap v2free (abstracts_vars abs) = abstracts_free_vars abs.
Proof.
  rewrite <- (abstracts_free_vars_relabel_abs id).
  f_equal.
  apply list_fmap_id'; intros ? _;
  apply relabel_abs_id.
Qed.

Lemma subseteq_psets_to_varset vars bounds frees :
  vars ⊆ psets_to_varset bounds frees <->
  set_omap v2bound vars ⊆ bounds /\
  set_omap v2free vars ⊆ frees.
Proof.
  unfold subseteq, set_subseteq_instance.
  setoid_rewrite elem_of_psets_to_varset.
  setoid_rewrite elem_of_set_omap.
  setoid_rewrite v2bound_Some.
  setoid_rewrite v2free_Some.
  split; [naive_solver|].
  intros; case_match; naive_solver.
Qed.


Lemma WT_ntl_alt tl ntl :
  WT_ntl tl ntl <->
  NoDup ntl.(ntl_sums) /\
  abstracts_vars ntl.(ntl_abstracts) ∪
  deltas_vars ntl.(ntl_deltas)
   ⊆ psets_to_varset (list_to_set ntl.(ntl_sums)) tl.
Proof.
  rewrite union_subseteq, 2 subseteq_psets_to_varset.
  rewrite set_omap_v2bound_abstracts_vars, set_omap_v2free_abstracts_vars.
  rewrite set_omap_v2bound_deltas_vars, set_omap_v2free_deltas_vars.
  unfold WT_ntl, WF_ntl.
  tauto.
Qed.


Lemma WT_ntl_alt' tl ntl :
  WT_ntl tl ntl <->
  NoDup ntl.(ntl_sums) /\
  abstracts_vars ntl.(ntl_abstracts)
    ⊆ psets_to_varset (list_to_set ntl.(ntl_sums)) tl /\
  deltas_vars ntl.(ntl_deltas)
   ⊆ psets_to_varset (list_to_set ntl.(ntl_sums)) tl.
Proof.
  now rewrite WT_ntl_alt, union_subseteq.
Qed.

Lemma get_subst_correct tl sums l r iold vnew abs delt :
  NoDup sums ->
  l <> r ->
  list_to_set [l;r] ⊆ psets_to_varset (list_to_set sums) tl ->
  get_subst sums l r = Some (iold, vnew) ->
  ntl_delta_eq tl
  {|
    ntl_sums := sums;
    ntl_abstracts := abs;
    ntl_deltas := (l, r) :: delt
  |}
  {|
    ntl_sums := filter (λ y : positive, y ≠ iold) sums;
    ntl_abstracts :=
      relabel_abs {[bound iold := vnew]} <$> abs;
    ntl_deltas :=
      relabel_delt {[bound iold := vnew]} <$> delt
  |}.
Proof.
  intros Hdup Hne Hsubs [Heq Hin]%get_subst_correct_aux.
  transitivity (mk_ntl sums abs ((bound iold, vnew) :: delt)).
  - apply ntl_delta_eq_perm.
    do 2 apply (conj eq_refl).
    cbn.
    constructor; easy.
  - apply (ntl_delta_eq_subst tl iold vnew);
      cbn [ntl_sums].
    + rewrite elem_of_list_filter.
      easy.
    + rewrite prod_swap_eq_pair in Heq.
      assert (vnew <> bound iold) by now clear -Hne Heq; firstorder congruence.      assert (Hvnew : vnew ∈@{gset var} list_to_set [l; r]) by (set_solver +Heq).
      apply Hsubs in Hvnew.
      rewrite elem_of_psets_to_varset in *.
      destruct vnew; [|easy].
      rewrite list_to_set_filter, elem_of_filter.
      split; [congruence|easy].
    + hnf; cbn.
      split; [rewrite prod_swap_eq_pair in Heq; clear Hsubs; firstorder congruence|].
      split; [|easy].
      now apply NoDup_perm_filter_out.
Qed.

Lemma deltas_vars_cons lu delt :
  deltas_vars (lu :: delt) =
  list_to_set [lu.1; lu.2] ∪ deltas_vars delt.
Proof.
  destruct lu; cbn; set_solver.
Qed.

Lemma deltas_vars_relabel_delt f delt :
  deltas_vars (relabel_delt f <$> delt) =
  set_map f $ deltas_vars delt.
Proof.
  apply set_eq; intros l.
  rewrite elem_of_deltas_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  rewrite elem_of_map.
  setoid_rewrite elem_of_deltas_vars.
  naive_solver.
Qed.

Lemma simplify_ntl_deltas_aux_correct_eq_aux tl sums {n} (delt : vec _ n)
  delt_other abs sums' delt' abs' :
  NoDup sums ->
  deltas_vars delt ⊆ psets_to_varset (list_to_set sums) tl ->
  simplify_ntl_deltas_aux sums delt delt_other abs =
  (sums', delt', abs') ->
  ntl_delta_eq tl (mk_ntl sums abs (delt ++ delt_other))
    (mk_ntl sums' abs' delt').
Proof.
  revert delt sums delt_other abs sums' delt' abs'.
  (* induction delt as [delt IHdelt] using (Nat.measure_induction _ (@length (var*var))). *)
  induction n as [|n IHn];
  [refine (vec_0_inv _ _)|refine (vec_S_inv _ _); intros (l & r) delt];
  intros sums delt_other abs sums' delt' abs' Hsums Hdelt;
  [cbn; intros [= <- <- <-]; reflexivity|].
  cbn delta [simplify_ntl_deltas_aux Vector.hd Vector.tl Vector.caseS]
    beta fix match zeta.
  cbn [vec_to_list] in Hdelt.
  rewrite deltas_vars_cons in Hdelt.
  cbn [fst snd] in Hdelt.
  case_decide as Hlr. 1:{
    intros Heq.
    rewrite <- Hlr.
    etransitivity;
    [instantiate (1:=mk_ntl _ _ _);
    symmetry; apply ntl_delta_eq_idemp with l;
      [|hnf; cbn; split_and!; f_equal; reflexivity]|].
    - apply Hdelt.
      set_solver.
    - apply IHn; easy + set_solver + Hdelt.
  }
  destruct (get_subst sums l r) as [(iold, vnew)|] eqn:Hsubst; cycle 1.
  - intros Heq.
    apply IHn in Heq; [|easy + set_solver + Hdelt..].
    rewrite <- Heq.
    apply ntl_delta_eq_perm.
    hnf.
    do 2 apply (conj eq_refl).
    cbn.
    apply (Permutation_PermutationA _).
    solve_Permutation.
  - intros Heq.
    apply union_subseteq in Hdelt as [Hlrsub Hdeltsub].
    apply IHn in Heq; [|now apply NoDup_filter|].
    + rewrite <- Heq.
      cbn.
      rewrite vec_to_list_map, <- fmap_app.
      now apply get_subst_correct.
    + rewrite vec_to_list_map.
      rewrite deltas_vars_relabel_delt.
      intros _ (v & -> & Hv%Hdeltsub)%elem_of_map.
      rewrite fn_lookup_singleton_case.
      case_decide as Hveq.
      * subst v.
        assert (vnew ∈@{gset var} list_to_set [l; r]) as Hvnew%Hlrsub by
          (apply get_subst_correct_aux in Hsubst as [Hsubst%prod_swap_eq_pair _];
          set_solver + Hsubst).
        rewrite elem_of_psets_to_varset in Hvnew |- *.
        destruct vnew; [|easy].
        rewrite list_to_set_filter, elem_of_filter.
        split; [|easy].
        apply get_subst_correct_aux in Hsubst as [Hsubst%prod_swap_eq_pair _].
        clear -Hlr Hsubst; firstorder congruence.
      * rewrite elem_of_psets_to_varset in Hv |- *.
        destruct v; [|easy].
        rewrite list_to_set_filter, elem_of_filter.
        split; [congruence|easy].
Qed.




Lemma simplify_ntl_deltas_aux_WF sums {n} (delt : vec _ n)
  delt_other abs sums' delt' abs' :
  WF_ntl (mk_ntl sums abs (delt ++ delt_other)) ->
  simplify_ntl_deltas_aux sums delt delt_other abs =
  (sums', delt', abs') ->
  WF_ntl (mk_ntl sums' abs' delt').
Proof.
  revert delt sums delt_other abs sums' delt' abs'.
  (* induction delt as [delt IHdelt] using (Nat.measure_induction _ (@length (var*var))). *)
  induction n as [|n IHn];
  [refine (vec_0_inv _ _)|refine (vec_S_inv _ _); intros (l & r) delt];
  intros sums delt_other abs sums' delt' abs' Hsums;
  [cbn; intros [= <- <- <-]; easy|].
  cbn delta [simplify_ntl_deltas_aux Vector.hd Vector.tl Vector.caseS]
    beta fix match zeta.
  case_decide as Hlr. 1:{
    intros Heq.
    apply IHn in Heq; [easy|].
    hnf; cbn -[abstracts_bound_vars deltas_bound_vars].
    split; [apply Hsums|].
    split; [apply Hsums|].
    generalize (Hsums.2.2).
    cbn -[abstracts_bound_vars deltas_bound_vars].
    set_solver +.
  }
  destruct (get_subst sums l r) as [(iold, vnew)|] eqn:Hsubst; cycle 1.
  - intros Heq.
    apply IHn in Heq; [easy|].
    split; [apply Hsums|].
    split; [apply Hsums|].
    generalize (Hsums.2.2).
    cbn -[abstracts_bound_vars deltas_bound_vars].
    erewrite deltas_bound_vars_perm_mor; [exact id|].
    solve_Permutation.
  - intros Heq.
    apply IHn in Heq; [easy|].
    hnf in Hsums |- *; cbn -[abstracts_bound_vars deltas_bound_vars] in Hsums |- *.
    split; [now apply NoDup_filter|].
    rewrite vec_to_list_map, <- fmap_app.
    split.
    + rewrite abstracts_bound_vars_relabel_abs.
      rewrite abstracts_vars_decomp.
      rewrite set_omap_union.
      intros x [Hx|Hf]%elem_of_union. 2:{
        exfalso.
        rewrite elem_of_set_omap in Hf.
        cbn in Hf.
        setoid_rewrite v2bound_Some in Hf.
        destruct Hf as (x' & (? & -> & _)%elem_of_map & Hxeq).
        now rewrite fn_lookup_singleton_ne in Hxeq by easy.
      }
      rewrite set_omap_set_map in Hx.
      rewrite list_to_set_filter.
      rewrite elem_of_filter.
      apply get_subst_correct_aux in Hsubst as Hsubst'.
      rewrite prod_swap_eq_pair in Hsubst'.
      apply elem_of_set_omap in Hx as (x' & Hx'%Hsums & Heqx).
      cbn in Heqx.
      rewrite fn_lookup_singleton_case in Heqx.
      case_decide as Hx'iold; cbn in Heqx.
      * destruct vnew as [inew|]; [cbn in *|easy].
        revert Heqx; intros [= <-].
        split; [generalize Hlr Hsubst'.1;clear; firstorder congruence|].
        destruct Hsubst' as [[[-> ->]|[-> ->]] Hold];
        apply Hsums.2.2; set_solver +.
      * revert Heqx; intros [= <-].
        split; [congruence|].
        easy.
    + rewrite deltas_bound_vars_relabel_delt.
      rewrite deltas_vars_decomp.
      rewrite set_omap_union.
      intros x [Hx|Hf]%elem_of_union. 2:{
        exfalso.
        rewrite elem_of_set_omap in Hf.
        cbn in Hf.
        setoid_rewrite v2bound_Some in Hf.
        destruct Hf as (x' & (? & -> & _)%elem_of_map & Hxeq).
        now rewrite fn_lookup_singleton_ne in Hxeq by easy.
      }
      rewrite set_omap_set_map in Hx.
      rewrite list_to_set_filter.
      rewrite elem_of_filter.
      apply get_subst_correct_aux in Hsubst as Hsubst'.
      rewrite prod_swap_eq_pair in Hsubst'.
      assert (Hdelt : deltas_bound_vars (delt ++ delt_other)
          ⊆ list_to_set sums) by now rewrite <- Hsums.2.2; set_solver +.
      apply elem_of_set_omap in Hx as (x' & Hx'%Hdelt & Heqx).
      cbn in Heqx.
      rewrite fn_lookup_singleton_case in Heqx.
      case_decide as Hx'iold; cbn in Heqx.
      * destruct vnew as [inew|]; [cbn in *|easy].
        revert Heqx; intros [= <-].
        split; [generalize Hlr Hsubst'.1;clear; firstorder congruence|].
        destruct Hsubst' as [[[-> ->]|[-> ->]] Hold];
        apply Hsums.2.2; set_solver +.
      * revert Heqx; intros [= <-].
        split; [congruence|].
        easy.
Qed.


Definition simplify_ntl_deltas (ntl : namedtensorlist) : namedtensorlist :=
  let '(sums, delt, abs) := simplify_ntl_deltas_aux ntl.(ntl_sums)
    (list_to_vec ntl.(ntl_deltas)) [] ntl.(ntl_abstracts) in
  mk_ntl sums abs delt.

Lemma simplify_ntl_deltas_correct tl ntl :
  WT_ntl tl ntl ->
  ntl_delta_eq tl (simplify_ntl_deltas ntl) ntl.
Proof.
  intros Hdup.
  unfold simplify_ntl_deltas.
  destruct (simplify_ntl_deltas_aux _ _ _ _) as [[sums delt] abs] eqn:Hsimp.
  apply (simplify_ntl_deltas_aux_correct_eq_aux tl) in Hsimp;
    [|now rewrite ?vec_to_list_to_vec; apply WT_ntl_alt' in Hdup..].
  rewrite <- Hsimp.
  rewrite vec_to_list_to_vec, app_nil_r.
  now destruct ntl.
Qed.

Lemma simplify_ntl_deltas_WF ntl :
  WF_ntl ntl ->
  WF_ntl (simplify_ntl_deltas ntl).
Proof.
  intros Hntl.
  unfold simplify_ntl_deltas.
  destruct (simplify_ntl_deltas_aux _ _ _ _) as [[sums delt] abs] eqn:Hsimp.
  apply simplify_ntl_deltas_aux_WF in Hsimp; [easy|].
  rewrite vec_to_list_to_vec, app_nil_r.
  apply Hntl.
Qed.

Lemma simplify_ntl_deltas_WT tl ntl :
  WT_ntl tl ntl ->
  WT_ntl tl (simplify_ntl_deltas ntl).
Proof.
  intros Hntl.
  eapply ntl_delta_eq_WT; [|eassumption].
  now apply simplify_ntl_deltas_correct.
Qed.


Definition ntl_eq tl : relation namedtensorlist :=
  rtc (ntl_aeq ∪ ntl_delta_eq tl).

#[export] Instance union_symmetric {A} {R R' : relation A} :
  Symmetric R -> Symmetric R' -> Symmetric (R ∪ R').
Proof.
  unfold Symmetric.
  unfold union, relation_union.
  firstorder.
Qed.

#[export] Instance ntl_eq_setoid tl : Equivalence (ntl_eq tl).
Proof.
  apply rtc_equivalence.
  apply _.
Qed.


Add Parametric Morphism : abstracts_free_vars with signature
  (≡ₚ) ==> eq as abstracts_free_vars_perm_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_abstracts_free_vars.
  now setoid_rewrite Habs.
Qed.
Add Parametric Morphism : deltas_free_vars with signature
  (≡ₚ) ==> eq as deltas_free_vars_perm_mor.
Proof.
  intros abs abs' Habs.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_deltas_free_vars.
  now setoid_rewrite Habs.
Qed.

Lemma abstracts_free_vars_relabel_bounds f abs : 
  abstracts_free_vars (relabel_abs (relabel_bounds f) <$> abs) = 
  abstracts_free_vars abs.
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_abstracts_free_vars.
  setoid_rewrite elem_of_abstracts_free_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  setoid_rewrite exists_pair.
  split.
  - intros (_ & _ & _ & (idx & low & up & [= -> -> ->] & Hlu) & Hr).
    rewrite <- fmap_app, elem_of_list_fmap in Hr.
    destruct Hr as ([] & [= ->] & Hr).
    eauto 20.
  - intros (idx & low & up & Hlu & Hr').
    eexists _, _, _.
    split; [exists idx, low, up; split; [cbn; reflexivity|easy]|].
    rewrite <- fmap_app.
    apply (elem_of_list_fmap_1 (relabel_bounds f) _ _ Hr').
Qed.


Lemma deltas_free_vars_relabel_bounds (f : positive -> positive)
  (delt : list _) :
  deltas_free_vars (relabel_delt (relabel_bounds f) <$> delt) =
  deltas_free_vars delt.
Proof.
  apply set_eq.
  intros r.
  rewrite elem_of_deltas_free_vars.
  setoid_rewrite elem_of_deltas_free_vars.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  cbn.
  split; [|set_solver].
  intros (l & u & (a & b & [= -> ->] & Hab) & Hor).
  destruct a, b; cbn in *; naive_solver.
Qed.


(* FIXME: Move *)
Lemma ntl_aeq_WT tl ntl ntl' :
  ntl =ntl= ntl' -> WT_ntl tl ntl -> WT_ntl tl ntl'.
Proof.
  intros Heq.
  intros (Habs & Hdelt & Hwf).
  split; [|split; [|now eapply ntl_aeq_WF; eauto]];
  revert Heq;
  intros (fr & Hfr & Hfsums & Hfabs & Hfdelt).
  - now rewrite <- Hfabs, abstracts_free_vars_relabel_bounds.
  - now rewrite <- Hfdelt, deltas_free_vars_relabel_bounds.
Qed.







Fixpoint te_relabel_absidx (f : Idx -> Idx) (te : tensorexpr) :=
  match te with
  | tone => tone
  | tdelta1 l r => tdelta1 l r
  | tabstract idx low up => tabstract (f idx) low up
  | tproduct l r =>
    tproduct (te_relabel_absidx f l) (te_relabel_absidx f r)
  | tsum smd => tsum (te_relabel_absidx f smd)
  end.

Definition tl_relabel_absidx (f : Idx -> Idx) (tl : tensorlist) : tensorlist :=
  mk_tl tl.(tl_sums)
    ((prod_map (prod_map f id) id) <$> tl.(tl_abstracts)) tl.(tl_deltas).

Definition ntl_relabel_absidx (f : Idx -> Idx) (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl ntl.(ntl_sums)
    ((prod_map (prod_map f id) id) <$> ntl.(ntl_abstracts)) ntl.(ntl_deltas).

Lemma tl_relabel_absidx_correct f tl :
  tl_relabel_absidx f tl =@{tensorexpr} te_relabel_absidx f tl.
Proof.
  destruct tl as [sums abs delt].
  cbn.
  induction sums; [|cbn; f_equal; done].
  cbn.
  induction abs as [|[[idx l] u] abs IHabs].
  - cbn.
    induction delt as [|[l u] delt IHdelt]; cbn; f_equal; auto.
  - cbn.
    now f_equal.
Qed.

Lemma ntl_relabel_absidx_correct f ntl :
  ntl2tl (ntl_relabel_absidx f ntl) = tl_relabel_absidx f (ntl2tl ntl).
Proof.
  destruct ntl as [isums abs delt];
  unfold tl_relabel_absidx; cbn.
  f_equal.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; intros _ [[idx low] up] _; done.
Qed.





Definition relabel_frees (f : positive -> positive) : var -> var :=
  var_map id f.

Lemma abstracts_bound_vars_app abs abs' :
  abstracts_bound_vars (abs ++ abs') =
  abstracts_bound_vars abs ∪ abstracts_bound_vars abs'.
Proof.
  set_solver.
Qed.

Lemma deltas_bound_vars_app delt delt' :
  deltas_bound_vars (delt ++ delt') =
  deltas_bound_vars delt ∪ deltas_bound_vars delt'.
Proof.
  set_solver.
Qed.


Lemma elem_of_abstracts_vars_bound r abs :
  bound r ∈ abstracts_vars abs <-> r ∈ abstracts_bound_vars abs.
Proof.
  now rewrite elem_of_abstracts_bound_vars, elem_of_abstracts_vars.
Qed.

Lemma elem_of_abstracts_vars_free r abs :
  free r ∈ abstracts_vars abs <-> r ∈ abstracts_free_vars abs.
Proof.
  now rewrite elem_of_abstracts_free_vars, elem_of_abstracts_vars.
Qed.

Lemma elem_of_deltas_vars_bound r delt :
  bound r ∈ deltas_vars delt <-> r ∈ deltas_bound_vars delt.
Proof.
  rewrite elem_of_deltas_bound_vars, elem_of_deltas_vars; naive_solver.
Qed.

Lemma elem_of_deltas_vars_free r delt :
  free r ∈ deltas_vars delt <-> r ∈ deltas_free_vars delt.
Proof.
  rewrite elem_of_deltas_free_vars, elem_of_deltas_vars; naive_solver.
Qed.



Definition ntl_relabel_bound f (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl (f <$> ntl.(ntl_sums))
    (relabel_abs (relabel_bounds f) <$> ntl.(ntl_abstracts))
    (relabel_delt (relabel_bounds f) <$> ntl.(ntl_deltas)).

Definition ntl_relabel_free f (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl ntl.(ntl_sums) (relabel_abs (relabel_frees f) <$> ntl.(ntl_abstracts))
    (relabel_delt (relabel_frees f) <$> ntl.(ntl_deltas)).


Definition relabel_ntl f (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl ntl.(ntl_sums) (relabel_abs f <$> ntl.(ntl_abstracts))
    (relabel_delt f <$> ntl.(ntl_deltas)).

Definition ntl_insert_sum (r : Idx) (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl (r :: ntl.(ntl_sums)) ntl.(ntl_abstracts) ntl.(ntl_deltas).


Definition ntl_insert_sums (rs : list Idx) (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl (rs ++ ntl.(ntl_sums)) ntl.(ntl_abstracts) ntl.(ntl_deltas).

Definition ntl_subst_free_as (l : Idx) (r : Idx) (ntl : namedtensorlist) :=
  ntl_insert_sum r (relabel_ntl
    (var_elim bound (λ l', if decide (l' = l) then bound r else free l')) ntl).


Lemma ntl_subst_free_as_WF l r ntl : r ∉ ntl.(ntl_sums) ->
  WF_ntl ntl ->
  WF_ntl (ntl_subst_free_as l r ntl).
Proof.
  intros Hr [Hdup Hsubs].
  split;
  [now apply NoDup_cons|].
  cbn -[abstracts_bound_vars deltas_bound_vars list_to_set].
  split.
  - rewrite abstracts_bound_vars_relabel_abs.
    intros r'.
    rewrite elem_of_set_omap.
    cbn -[list_to_set].
    setoid_rewrite v2bound_Some.
    intros (v & Hvabs & Hr').
    revert Hr'.
    destruct v as [|l'']; [intros [= ->];
      rewrite list_to_set_cons; apply union_subseteq_r, Hsubs.1;
      now rewrite elem_of_abstracts_vars_bound in Hvabs|].
    cbn -[list_to_set].
    case_decide; [|easy].
    intros [= <-].
    set_solver +.
  - rewrite deltas_bound_vars_relabel_delt.
    intros r'.
    rewrite elem_of_set_omap.
    cbn -[list_to_set].
    setoid_rewrite v2bound_Some.
    intros (v & Hvabs & Hr').
    revert Hr'.
    destruct v as [|l'']; [intros [= ->];
      rewrite list_to_set_cons; apply union_subseteq_r, Hsubs.2;
      now rewrite elem_of_deltas_vars_bound in Hvabs|].
    cbn -[list_to_set].
    case_decide; [|easy].
    intros [= <-].
    set_solver +.
Qed.



Definition ntl_subst_free (l : Idx) (ntl : namedtensorlist) :=
  ntl_subst_free_as l (fresh ntl.(ntl_sums)) ntl.


Lemma ntl_subst_free_WF l ntl :
  WF_ntl ntl ->
  WF_ntl (ntl_subst_free l ntl).
Proof.
  intros HWF.
  apply ntl_subst_free_as_WF, HWF.
  apply infinite_is_fresh.
Qed.

Definition ntl_times_aux (l r : namedtensorlist) : namedtensorlist :=
  mk_ntl (l.(ntl_sums) ++ r.(ntl_sums))
    (l.(ntl_abstracts) ++ r.(ntl_abstracts))
    (l.(ntl_deltas) ++ r.(ntl_deltas)).


Definition ntl_times (l r : namedtensorlist) : namedtensorlist :=
  ntl_times_aux (ntl_relabel_bound (bcons false) l) (ntl_relabel_bound (bcons true) r).

Lemma ntl_times_alt l r :
ntl_times l r = mk_ntl ((bcons false <$> l.(ntl_sums)) ++
    (bcons true <$> r.(ntl_sums)))
    ((relabel_abs (relabel_bounds (bcons false)) <$> l.(ntl_abstracts))
      ++ (relabel_abs (relabel_bounds (bcons true)) <$> r.(ntl_abstracts)))
    ((relabel_delt (relabel_bounds (bcons false)) <$> l.(ntl_deltas))
      ++ (relabel_delt (relabel_bounds (bcons true)) <$> r.(ntl_deltas))).
Proof.
  reflexivity.
Qed.

Lemma ntl_times_aux_WF l r :
  WF_ntl l -> WF_ntl r ->
  l.(ntl_sums) ## r.(ntl_sums) ->
  WF_ntl (ntl_times_aux l r).
Proof.
  intros Hl Hr Hlr.
  split.
  - cbn.
    apply NoDup_app.
    split_and!.
    + apply Hl.
    + exact Hlr.
    + apply Hr.
  - cbn -[abstracts_bound_vars deltas_bound_vars list_to_set].
    rewrite abstracts_bound_vars_app, deltas_bound_vars_app, list_to_set_app.
    split; (apply union_mono; [apply Hl|apply Hr]).
Qed.

Lemma ntl_relabel_bound_WF_strong f ntl :
  ForallPairs (fun i j => f i = f j -> i = j) ntl.(ntl_sums) ->
  WF_ntl ntl ->
  WF_ntl (ntl_relabel_bound f ntl).
Proof.
  intros Hf Hntl.
  rewrite ForallPairs_forall in Hf.
  split; [|split]; cbn -[abstracts_bound_vars deltas_bound_vars].
  - apply NoDup_fmap_2_strong; [apply Hf|apply Hntl].
  - rewrite abstracts_bound_vars_relabel_bounds, <- (set_map_list_to_set (SA:=Pset)).
    now apply set_map_mono, Hntl.
  - rewrite deltas_bound_vars_relabel_bounds, <- (set_map_list_to_set (SA:=Pset)).
    now apply set_map_mono, Hntl.
Qed.


Lemma ntl_relabel_bound_WF f `{Hf : !Inj eq eq f} ntl :
  WF_ntl ntl ->
  WF_ntl (ntl_relabel_bound f ntl).
Proof.
  intros Hntl.
  apply ntl_relabel_bound_WF_strong; [|easy].
  now intros ? ? ? ?; apply Hf.
Qed.

Lemma ntl_times_WF l r :
  WF_ntl l -> WF_ntl r ->
  WF_ntl (ntl_times l r).
Proof.
  intros Hl Hr.
  apply ntl_times_aux_WF; [now apply (ntl_relabel_bound_WF _)..|].
  cbn.
  intros ? []%elem_of_list_fmap []%elem_of_list_fmap.
  lia.
Qed.

Definition add_delta_ntl (l u : var) (ntl : namedtensorlist) : namedtensorlist :=
  mk_ntl ntl.(ntl_sums) ntl.(ntl_abstracts) ((l, u) :: ntl.(ntl_deltas)).

Definition add_loop_ntl (l r : positive) (ntl : namedtensorlist) : namedtensorlist :=
  ntl_subst_free l (ntl_subst_free r (add_delta_ntl (free l) (free r) ntl)).

Definition add_loop_ntl_alt_as (l r x : positive) (ntl : namedtensorlist) : namedtensorlist :=
  ntl_insert_sum x (
  relabel_ntl
    (var_elim bound (λ l', if decide (l' = l \/ l' = r) then bound x else free l'))  
    ntl).

Definition add_loop_ntl_alt (l r : positive) (ntl : namedtensorlist) : namedtensorlist :=
  add_loop_ntl_alt_as l r (fresh ntl.(ntl_sums)) ntl.


