Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp.

Definition pos_to_nat_pred (p : positive) : nat :=
  pred (Pos.to_nat p).

#[local] Coercion pos_to_nat_pred : positive >-> nat.

Definition pos_add_N (p : positive) (n : N) : positive :=
  match n with
  | N0 => p
  | Npos q => Pos.add p q
  end.

Lemma pos_add_N_to_Z n p : (Zpos (pos_add_N p n) = Zpos p + Z.of_N n)%Z.
Proof.
  unfold pos_add_N; destruct n; lia.
Qed.


Definition pos_sub_N (p : positive) (n : N) : positive :=
  match n with
  | N0 => p
  | Npos q => Pos.sub p q
  end.

Lemma pos_sub_N_to_Z n p : N.lt n (Npos p) ->
  (Zpos (pos_sub_N p n) = Zpos p - Z.of_N n)%Z.
Proof.
  unfold pos_sub_N; destruct n; lia.
Qed.

(* FIXME: Move *)
#[global]
Program Instance Op_pos_to_nat_pred : ZifyClasses.UnOp pos_to_nat_pred :=
  { TUOp x := (x - 1)%Z }.
Next Obligation.
  cbn.
  unfold pos_to_nat_pred.
  intros; lia.
Qed.
Add Zify UnOp Op_pos_to_nat_pred.

#[global]
Program Instance Op_pos_add_N : ZifyClasses.BinOp pos_add_N :=
  { TBOp x y := (x + y)%Z }.
Next Obligation.
  cbn.
  intros.
  apply pos_add_N_to_Z.
Qed.
Add Zify BinOp Op_pos_add_N.

#[global]
Program Instance Op_pos_sub_N : ZifyClasses.BinOp pos_sub_N :=
  { TBOp x y := Z.max 1 (x - y)%Z }.
Next Obligation.
  cbn.
  intros.
  unfold pos_sub_N.
  destruct m; lia.
Qed.
Add Zify BinOp Op_pos_sub_N.


(* FIXME: Move *)
Section lengthN.

Local Open Scope N_scope.

Fixpoint lengthN {A} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: l => N.succ (lengthN l)
  end.
Lemma lengthN_correct {A} (l : list A) :
  N.to_nat (lengthN l) = length l.
Proof. induction l; cbn; lia. Qed.
Lemma lengthN_correct_rev {A} (l : list A) :
  lengthN l = N.of_nat (length l).
Proof. rewrite <- lengthN_correct; lia. Qed.
Lemma lengthN_app {A} (l l' : list A) :
  lengthN (l ++ l') = lengthN l + lengthN l'.
Proof.
  now rewrite 3 lengthN_correct_rev, length_app, Nat2N.inj_add.
Qed.

End lengthN.


(* Section TensorExprDB.  *)

Notation Idx := positive.
  (* Almost all values are [positive]s, as these are more efficient to
    work with ([Pmap] is much, much faster than [gmap]) *)
Notation Ty := nat.
  (* However, types are [nat]s, so that our typing environment can be
    a list (we will never meaningfully manipulate types anyways) *)

Local Open Scope positive_scope.
Local Open Scope list_scope.

(* The type of variables in an expression *)
Inductive var :=
  | rel : Idx -> var (* A relative/DeBruijn variable, which is summed over *)
  | loc : Idx -> var (* A variable in the local context
    (which is semantically universally quantified) *)
  | glob : Idx -> var. (* A variable in the global context *)

#[export] Instance rel_inj : Inj eq eq rel.
Proof. congruence. Qed.

#[export] Instance loc_inj : Inj eq eq loc.
Proof. congruence. Qed.

#[export] Instance glob_inj : Inj eq eq glob.
Proof. congruence. Qed.

#[export] Instance var_dec : EqDecision var. refine
  (fun v v' =>
  match v, v' with
  | rel r, rel r' =>
    match Pos.eq_dec r r' with
    | left Heq => left (f_equal rel Heq)
    | right Hneq => right (fun Heq => Hneq (rel_inj _ _ Heq))
    end
  | loc l, loc l' =>
    match Pos.eq_dec l l' with
    | left Heq => left (f_equal loc Heq)
    | right Hneq => right (fun Heq => Hneq (loc_inj _ _ Heq))
    end
  | glob g, glob g' =>
    match Pos.eq_dec g g' with
    | left Heq => left (f_equal glob Heq)
    | right Hneq => right (fun Heq => Hneq (glob_inj _ _ Heq))
    end
  | _, _ => right _
  end); abstract congruence.
Defined.

#[export] Instance var_countable : Countable var := {
  encode v := match v with
    | rel r => r~0~0
    | loc l => l~1~0
    | glob g => g~1
    end%positive;
  decode p := match p with
    | r~0~0 => Some (rel r)
    | l~1~0 => Some (loc l)
    | g~1 => Some (glob g)
    | 1 | 2 => None
    end%positive;
  decode_encode v :=
    match v with | rel p | loc p | glob p => eq_refl end
}.

Definition v2rel (v : var) : option Idx :=
  match v with
  | rel r => Some r
  | _ => None
  end.

Definition v2loc (v : var) : option Idx :=
  match v with
  | loc l => Some l
  | _ => None
  end.

Definition v2glob (v : var) : option Idx :=
  match v with
  | glob g => Some g
  | _ => None
  end.

Definition var_map (fr fl fg : Idx -> Idx) : var -> var :=
  fun v => match v with
  | rel r => rel (fr r)
  | loc l => loc (fl l)
  | glob g => glob (fg g)
  end.

Lemma var_map_decomp fr fl fg v :
  var_map fr fl fg v = default v (((rel ∘ fr) <$> v2rel v) ∪
    ((loc ∘ fl) <$> v2loc v) ∪
    ((glob ∘ fg) <$> v2glob v)).
Proof.
  now destruct v.
Qed.

Add Parametric Morphism : var_map with signature
  (pointwise_relation Idx eq) ==> (pointwise_relation Idx eq) ==>
  (pointwise_relation Idx eq) ==> (pointwise_relation var eq) as var_map_mor.
Proof.
  intros fr fr' Hfr fl fl' Hfl fg fg' Hfg [];
  cbn; f_equal; auto.
Qed.


Inductive tensorexpr :=
  | tone : tensorexpr (* The element 1 *)
  | tabstract (absidx : Idx) (lower : list var) (upper : list var)
    (* An abstract tensor, indexed by [absidx], with arguments
      [lower] and [upper] *)
  | tproduct (l r : tensorexpr) (* The binary product of [tensorexpr]s *)
  | tsum (ty : Ty) (summand : tensorexpr)
    (* A sum *).

Definition tabstract' (abs : Idx * list var * list var) : tensorexpr :=
  let '(abs, lower, upper) := abs in tabstract abs lower upper.

Fixpoint tproducts (tes : list tensorexpr) : tensorexpr :=
  match tes with
  | [] => tone
  | [te] => te
  | te :: tes => tproduct te (tproducts tes)
  end.


Definition addrel (shift : N) (v : var) : var :=
  match v with
  | rel r => rel (pos_add_N r shift)
  | _ => v
  end.

Definition withrelshift (shift : N) (f : var -> var) (v : var) : var :=
  match v with
  | rel r => if decide (Npos r <= shift)%N then rel r else
      addrel shift (f (rel (pos_sub_N r shift)))
  | _ => addrel shift (f v)
  end.

Add Parametric Morphism : withrelshift with signature
  eq ==> pointwise_relation var eq ==> pointwise_relation var eq
  as withrelshift_ext.
Proof.
  intros s f f' Hf []; [|cbn; f_equal; apply Hf..].
  cbn.
  case_decide; [reflexivity|].
  f_equal; apply Hf.
Qed.

Lemma addrel_add s s' v :
  addrel s (addrel s' v) = addrel (s + s') v.
Proof.
  destruct v; cbn; f_equal.
  lia.
Qed.

Lemma pos_sub_N_add p n n' :
  pos_sub_N p (n + n') = pos_sub_N (pos_sub_N p n) n'.
Proof.
  unfold N.add; destruct n, n'; cbn; lia.
Qed.

Lemma withrelshift_add s s' f v :
  withrelshift s (withrelshift s' f) v = withrelshift (s + s') f v.
Proof.
  destruct v; [|cbn; apply addrel_add..].
  cbn.
  repeat case_decide; lia || fast_reflexivity || cbn.
  - f_equal; destruct s; cbn; try lia.
  - now rewrite addrel_add, pos_sub_N_add.
Qed.

Fixpoint relabel_te_aux (shift : N) (f : var -> var) (te : tensorexpr) : tensorexpr :=
  match te with
  | tone => tone
  | tabstract absidx lower upper =>
    tabstract absidx (withrelshift shift f <$> lower)
      (withrelshift shift f <$> upper)
  | tproduct l r => tproduct (relabel_te_aux shift f l) (relabel_te_aux shift f r)
  | tsum ty summand =>
    tsum ty (relabel_te_aux (N.succ shift) f summand)
  end.

Add Parametric Morphism s : (relabel_te_aux s) with signature
  pointwise_relation var eq ==> eq ==> eq as relabel_te_aux_ext.
Proof.
  intros f f' Hf te.
  revert s.
  induction te; intros s.
  - reflexivity.
  - cbn.
    f_equal; apply list_fmap_ext;
    intros _ ? _; now apply withrelshift_ext.
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
  | tabstract absidx lower upper =>
    tabstract absidx (f <$> lower) (f <$> upper)
  | tproduct l r => tproduct (relabel_te_alt f l) (relabel_te_alt f r)
  | tsum ty summand =>
    tsum ty (relabel_te_alt (withrelshift 1 f) summand)
  end.


Add Parametric Morphism : relabel_te_alt with signature
  pointwise_relation var eq ==> eq ==> eq as relabel_te_alt_ext.
Proof.
  intros f f' Hf te.
  revert f f' Hf;
  induction te; intros f f' Hf.
  - reflexivity.
  - cbn.
    f_equal; apply list_fmap_ext;
    intros _ ? _; now apply Hf.
  - cbn.
    f_equal; auto.
  - cbn.
    f_equal.
    apply IHte.
    now apply withrelshift_ext.
Qed.

Lemma relabel_te_alt_correct_aux shift f te :
  relabel_te_alt (withrelshift shift f) te =
  relabel_te_aux shift f te.
Proof.
  revert shift f; induction te; intros shift f.
  - reflexivity.
  - reflexivity.
  - cbn.
    f_equal; auto.
  - cbn.
    rewrite <- IHte.
    f_equal.
    apply relabel_te_alt_ext; [|easy].
    intros v.
    rewrite withrelshift_add.
    apply withrelshift_ext; easy + lia.
Qed.




Fixpoint te_varset (te : tensorexpr) : gset var :=
  match te with
  | tone => ∅
  | tabstract _ lower upper => list_to_set (lower ++ upper)
  | tproduct l r => te_varset l ∪ te_varset r
  | tsum ty summand =>
    te_varset summand
  end.

(* FIXME: Move *)
(* The predicate determining that a [tensorexpr] is well-typed
  _only with respect to bound [rel] variables_ *)
Fixpoint te_wellbound_aux (bnd : Idx) (te : tensorexpr) : bool :=
  match te with
  | tone => true
  | tabstract _ low up =>
    bool_decide (Forall (λ p, p < bnd) (omap v2rel (low ++ up)))
  | tproduct l r => te_wellbound_aux bnd l && te_wellbound_aux bnd r
  | tsum _ smd =>
    te_wellbound_aux (Pos.succ bnd) smd
  end.

Definition te_wellbound (te : tensorexpr) : bool :=
  te_wellbound_aux 1 te.


Fixpoint te_rel_varset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tabstract _ lower upper => list_to_set (omap v2rel (lower ++ upper))
  | tproduct l r => te_rel_varset l ∪ te_rel_varset r
  | tsum _ smd =>
    te_rel_varset smd
  end.

Fixpoint te_local_varset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tabstract _ lower upper => list_to_set (omap v2loc (lower ++ upper))
  | tproduct l r => te_local_varset l ∪ te_local_varset r
  | tsum _ smd =>
    te_local_varset smd
  end.

Fixpoint te_global_varset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tabstract _ lower upper => list_to_set (omap v2glob (lower ++ upper))
  | tproduct l r => te_global_varset l ∪ te_global_varset r
  | tsum _ smd =>
    te_global_varset smd
  end.

Fixpoint te_absset (te : tensorexpr) : Pset :=
  match te with
  | tone => ∅
  | tabstract idx _ _ => {[ idx ]}
  | tproduct l r => te_absset l ∪ te_absset r
  | tsum _ summand =>
    te_absset summand
  end.


Lemma te_varset_decomp te :
  te_varset te = set_map rel (te_rel_varset te) ∪
    set_map loc (te_local_varset te) ∪
    set_map glob (te_global_varset te).
Proof.
  unfold_leibniz.
  induction te; cbn in *; [set_solver| |
    rewrite 1?IHte1, 1?IHte2; set_solver +|apply IHte].
  generalize (lower ++ upper) as l.
  intros l; induction l as [|[]]; [set_solver|
    cbn [list_to_set omap list_omap v2rel v2loc v2glob];
  rewrite IHl; set_solver+..].
Qed.







Record tensorlist := mk_tl {
  tl_sums : list Ty;
  tl_abstracts : list (Idx * list var * list var)
}.

Lemma tl_ext tl tl' :
  tl.(tl_sums) = tl'.(tl_sums) ->
  tl.(tl_abstracts) = tl'.(tl_abstracts) ->
  tl = tl'.
Proof.
  destruct tl, tl'; cbn; congruence.
Qed.

Definition tl_cons_sum ty (tl : tensorlist) : tensorlist :=
  mk_tl (ty :: tl.(tl_sums)) (tl.(tl_abstracts)).

Fixpoint tl_app_sums sums tl :=
  match sums with
  | [] => tl
  | ty :: sums => tl_cons_sum ty (tl_app_sums sums tl)
  end.

Fixpoint tensorexpr_of_tensorlist_aux sums abs : tensorexpr :=
  match sums with
  | [] => tproducts (tabstract' <$> abs)
  | ty :: sums => tsum ty (tensorexpr_of_tensorlist_aux sums abs)
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

Definition abstracts_vars (abs : list (Idx * list var * list var)) : gset var :=
  list_to_set ('(_, lower, upper) ← abs; lower ++ upper).

Definition abstracts_rel_vars
  (abs : list (Idx * list var * list var)) : Pset :=
  list_to_set ('(_, lower, upper) ← abs; omap v2rel (lower ++ upper)).

Definition abstracts_local_vars
  (abs : list (Idx * list var * list var)) : Pset :=
  list_to_set ('(_, lower, upper) ← abs; omap v2loc (lower ++ upper)).

Definition abstracts_global_vars
  (abs : list (Idx * list var * list var)) : Pset :=
  list_to_set ('(_, lower, upper) ← abs; omap v2glob (lower ++ upper)).




(** Relabeling in [tensorlist]s *)

Definition relabel_abs (f : var -> var) (abs : Idx * list var * list var) :=
  let '(idx, lower, upper) := abs in
  (idx, f <$> lower, f <$> upper).

Definition relabel_tl (f : var -> var) (tl : tensorlist) : tensorlist :=
  mk_tl (tl.(tl_sums))
    (relabel_abs f <$> tl.(tl_abstracts)).

Definition relabel_rels (f : Idx -> Idx) : var -> var :=
    var_map f id id.


(* A simpler, but less performant, definition *)
Definition tl_times_spec_defn (l r : tensorlist) : tensorlist :=
  let 'mk_tl lsums labs := l in
  let 'mk_tl rsums rabs := r in
  let lenl := length lsums in
  let lenr := length rsums in
  let labs' := relabel_abs (relabel_rels
    (λ p, pos_add_N p (N.of_nat lenr))) <$> labs in
  let rabs' := relabel_abs (relabel_rels (λ p,
    if decide (p < lenr)%nat then p
    else pos_add_N p (N.of_nat lenl))) <$> rabs in
  mk_tl (lsums ++ rsums) (labs' ++ rabs').


Definition tl_times (l r : tensorlist) : tensorlist :=
  let 'mk_tl lsums labs := l in
  let 'mk_tl rsums rabs := r in
  let lenl := lengthN lsums in
  let lenr := lengthN rsums in
  let labs' := match lenr with
    | N0 => labs
    | Npos lenr => relabel_abs (relabel_rels (Pos.add lenr)) <$> labs
    end in
  let rabs' := match lenl with
    | N0 => rabs
    | Npos lenl => match lenr with
      | N0 => relabel_abs (relabel_rels (Pos.add lenl)) <$> rabs
      | Npos lenr => relabel_abs (relabel_rels (λ p,
        if Pos.leb p lenr then p else Pos.add lenl p)) <$> rabs
      end
    end in
  mk_tl (lsums ++ rsums) (labs' ++ rabs').


(* FIXME: Move *)
Lemma list_fmap_id' `(f : A -> A) (l : list A) :
  (forall a, a ∈ l -> f a = a) ->
  f <$> l = l.
Proof.
  intros Hf.
  etransitivity; [|apply list_fmap_id].
  apply list_fmap_ext; intros _ ? ?%elem_of_list_lookup_2.
  now apply Hf.
Qed.

Ltac tspecialize_with C tac :=
  match type of C with
  | forall _ : ?A, _ =>
    let H := fresh in
    assert (H : A); [
      tac | specialize (C H); clear H
    ]
  end.

Tactic Notation "tspecialize" uconstr(C) "by" tactic3(tac) :=
  tspecialize_with C ltac:(solve [tac]).

Tactic Notation "tspecialize" uconstr(C) :=
  tspecialize_with C ltac:(idtac).

#[local] Coercion N.of_nat : nat >-> N.

Lemma relabel_abs_id abs : relabel_abs id abs = abs.
Proof.
  destruct abs as [[f low] up]; cbn.
  now rewrite 2 list_fmap_id.
Qed.

Lemma relabel_abs_ext f g abs :
  (forall x, f x = g x) -> relabel_abs f abs = relabel_abs g abs.
Proof.
  intros Heq.
  destruct abs as [[idx low] up]; cbn.
  f_equal; [f_equal|]; apply list_fmap_ext; intros; apply Heq.
Qed.

Lemma relabel_abs_id' f abs :
  (forall x, f x = x) -> relabel_abs f abs = abs.
Proof.
  intros Hid.
  erewrite relabel_abs_ext; [apply relabel_abs_id|apply Hid].
Qed.

Lemma relabel_rels_ext f g :
  (forall r, f r = g r) -> forall v, relabel_rels f v = relabel_rels g v.
Proof.
  intros Hfg.
  destruct v; [|reflexivity..].
  cbn; now rewrite Hfg.
Qed.


Lemma tl_times_spec_defn_correct l r :
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
Qed.



(** Converting a [tensorexpr] to a [tensorlist] *)

Fixpoint tensorlist_of_tensorexpr (te : tensorexpr) : tensorlist :=
  match te with
  | tone => tlone
  | tabstract idx lower upper => mk_tl [] [(idx, lower, upper)]
  | tproduct l r => tl_times (tensorlist_of_tensorexpr l) (tensorlist_of_tensorexpr r)
  | tsum ty smd =>
    tl_cons_sum ty (tensorlist_of_tensorexpr smd)
  end.



(* Matching on [tensorlist]s *)


(* TO DO: When I figure out the "boundary condition" or whatever that is,
   incorporate it into the function at this level somehow? *)
(* TODO: Figure out incorporating typing into this!! As-is this will be 
  hard to reason about without WF conditions*)
  (* TODO: Why do I hate WF conditions? TODO: Do I hate WF conditions? 
    Checking it is probably a pretty small price to pay... especially at
    the tensorlist level*)
Fixpoint extend_map_of_abstract_pair
  (mb mbi : Pmap Idx) (* The map and inverse map of [rel]/bound variables, 
    which must map to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (mlran : Pset) (* The set of [rel] variables in the range of [ml], which
     must be disjoint from the image of [mb] / domain of [mbi] *)
  (l r : list var) : option (Pmap Idx * Pmap Idx * Pmap var) :=
  match l, r with
  | [], [] => Some (mb, mbi, ml)
  | hl :: l, hr :: r =>
    match hl, hr with
    | glob gl, glob gr => (* global variables must match exactly! *)
      if bool_decide (gl = gr) then
        extend_map_of_abstract_pair mb mbi ml mlran l r
      else None
    | glob gl, _ => (* global variables can't map anywhere (nontrivially) *)
      None
    | loc ll, vr => (* local variables can map anywhere (ab initio, at least) *)
      match ml !! ll with
      | None => 
        match vr with 
        | rel rr => 
          match mbi !! rr with
          | Some _ => None (* This variable is already bound; we can't use it locally *)
          | None =>
            extend_map_of_abstract_pair mb mbi (<[ll := rel rr]> ml) ({[rr]} ∪ mlran) 
              l r
          end
        | vr => 
          extend_map_of_abstract_pair mb mbi (<[ll := vr]> ml) mlran l r
        end
      | Some vr' =>
        if bool_decide (vr = vr') then
          extend_map_of_abstract_pair mb mbi ml mlran l r
        else None
      end
    | rel rl, rel rr => (* bound variables must map to bound variables *)
      match mb !! rl with
      | None => 
        match mbi !! rr with (* Preserve the inverses! *)
        | None => 
          if bool_decide (rr ∈ mlran) then 
            (* This relative variable is mapped to by a local variable already *)
            None 
          else 
            extend_map_of_abstract_pair 
              (<[rl := rr]> mb) (<[rr := rl]> mbi) ml mlran l r
        | Some _ => None (* This variable is already mapped to *)
        end
      | Some rr' =>
        if bool_decide (rr = rr') then
          extend_map_of_abstract_pair mb mbi ml mlran l r
        else None
      end
    | rel rl, _ => (* bound variables can only map to other bound variables *)
      None
    end
  | _, _ => None
  end.

(* FIXME: Move *)
Definition list_first_omap {A B} (f : A -> option B) : list A -> option B :=
  fix list_first_omap l :=
  match l with
  | [] => None
  | a :: l =>
    match f a with
    | Some b => Some b
    | None => list_first_omap l
    end
  end.


(* TODO: rewrite with collate (also, optionally shortcut to false if
  we don't use up all the abstracts for a given index) *)
Fixpoint extend_match_of_abstract_tensors
  (P : Pmap Idx -> Pmap Idx -> Pmap var -> Pset -> 
    list (Idx * list var * list var) -> Prop)
  `{HP : forall mb mbi ml mlran rrest, Decision (P mb mbi ml mlran rrest)}
  (mb mbi : Pmap Idx) (* The map and inverse map of [rel]/bound variables, 
    which must map to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (mlran : Pset) (* The set of [rel] variables in the range of [ml], which
     must be disjoint from the image of [mb] / domain of [mbi] *)
  (labs rabs : list (Idx * list var * list var)) :
    option (Pmap Idx * Pmap Idx * Pmap var * Pset * list (Idx * list var * list var)) :=
  match labs with
  | [] =>
    if decide (P mb mbi ml mlran rabs) then
      Some (mb, mbi, ml, mlran, rabs)
    else None
  | (fl, lowl, upl) :: labs =>
    list_first_omap (fun '((_, lowr, upr), rrest) =>
      '(mb, mbi, ml) ← extend_map_of_abstract_pair mb mbi ml mlran lowl lowr;
         '(mb, mbi, ml) ← extend_map_of_abstract_pair mb mbi ml mlran upl upr;
        extend_match_of_abstract_tensors P mb mbi ml mlran labs rrest)
      (list_select (fun '(fr, _, _) => fl = fr) rabs)
    (* head ('((_, lowr, upr), rrest) ← list_select (fun '(fr, _, _) => fl = fr) rabs;
      from_option (λ x, [x]) []
        (m' ← extend_map_of_abstract_pair lbound rbound m lowl lowr;
         m'' ← extend_map_of_abstract_pair lbound rbound m' upl upr;
         extend_match_of_abstract_tensors lbound rbound m'' labs rrest)
      ) *)
  end.

(* TODO: Theory of: 
Definition lookup _ endomorphism `{Lookup A A M} (m : M) : A -> A :=
  fun a => default a (m !! a). *)

(* FIXME: Move *)
Definition Pmap_map (m : Pmap Idx) : Idx -> Idx :=
  fun v => default v (m !! v).

Definition match_tensorlist_aux (tl tl' : tensorlist) : 
  option (tensorlist * (* What remains of [tl'] after the match of [tl] is removed *)
  Pmap Idx * (* The mapping of _unmatched_ bound variables from the unmatched
    portion of [tl'] to those in the returned tensorlist *)
  Pmap var) (* The mapping of the local variables of [tl] to variables of
    [tl'], possibly including relative variables (which are reindexed to
      be correct within the returned tensorlist; however, they must be 
      shifted along with the variables of the abstracts of the returned
      tensorlist if (innermost) sums are added to the tensorlist) *) :=
  match extend_match_of_abstract_tensors
    (fun mb mbi ml mlran rabs => 
      (* TODO: Check this progressively, using [collate] *)
      set_Forall (λ r, ~ is_Some (mbi !! r)) (abstracts_rel_vars rabs))
    ∅ ∅ ∅ ∅ (tl.(tl_abstracts)) (tl'.(tl_abstracts)) with 
  | None => None
  | Some (mb, mbi, ml, mlran, rrest) =>
  
  (* We have: [mb/mbi] : maps [Idx -> Idx] such that 
    [mb <$> tl] is a subexpression of [tl']; notably:
    (i) the sums not included in [mb <$> tl] are those of [tl'] 
      that are _not_ included in [img mb = dom mbi]
    (ii) the abstracts not included in [mb <$> tl] are [rrest] 
    
    We need two maps [reord reord_rest : Idx -> Idx] such that
    [reord_rest <$> rrest] makes the variables correct there, assuming
    we simply remove the match (we also need to figure out the order of 
    types; same thing), and such that [reord]
    *)
  Some (
  let ntys := imap (fun i ty => (Pos.of_succ_nat i, ty)) (reverse tl'.(tl_sums)) in 
  let unused_tys := filter (fun '(idx, _) => ~ is_Some (mbi !! idx)) ntys in 
  let newty_info := imap (fun inew '(iold, ty) => (iold, Pos.of_succ_nat inew, ty)) unused_tys in 
  let rrest_map : Pmap _ := list_to_map newty_info.*1 in 
  let newtys := reverse newty_info.*2 in 
  let ml' := (relabel_rels (Pmap_map rrest_map) <$> ml) in
  (mk_tl newtys (relabel_abs (relabel_rels (Pmap_map rrest_map)) <$> 
    rrest),
  rrest_map, ml'))
  end.

Definition var_subst_locals (f : Idx -> var) (v : var) : var :=
  match v with 
  | loc l => f l
  | _ => v
  end.

(* TODO: Definitely need to make sure [ml] maps locals to variables 
  of the correct type. Can do this with overall WF of goal (can get 
  all typing from the abstract map, then check; if [lhs == rhs] not
  WF, we should still maybe be fine? I'd thought this worked before
  but now I'm not positive). *)

(* Assuming [lhs == rhs] (for the moment, ignore typing and context),
  rewrite this equality in [targ], if possible. *)
Definition match_rewrite_tensorlist (lhs rhs targ : tensorlist) : 
  option tensorlist := 
  '((mk_tl usums uabs), relmap, locmap) ← match_tensorlist_aux lhs targ;
  let '(mk_tl rsums rabs) := rhs in 
  let rsize := lengthN rsums in 
  let shift := relabel_rels (λ p, pos_add_N p rsize) in 
  let uabs_shifted := relabel_abs shift <$> uabs in 
  let rabs_subst := relabel_abs (var_subst_locals (λ l, 
    from_option shift (loc l) (locmap !! l))) <$> rabs in 
  Some (mk_tl (usums ++ rsums) (uabs_shifted ++ rabs_subst)).



(* 

Record namedtensorlist := mk_ntl {
  ntl_sums : list (Idx * Ty);
  ntl_abstracts : list (Idx * list var * list var);
}.


Definition ntl2tl (ntl : namedtensorlist) :=
  let '(mk_ntl sums abs) := ntl in 
  let varmap : Pmap Idx := list_to_map 
    (imap (λ idx '(r, ty), (r, Pos.of_succ_nat idx))
      sums) in
  mk_tl sums.*2
  (relabel_abs (relabel_rels (λ v, default v (varmap !! v))) <$> abs).

Definition tl2ntl (tl : tensorlist) := 
  let '(mk_tl sums abs) := tl in 
  mk_ntl (imap (λ i v, (Pos.of_succ_nat i, v)) (reverse sums))
    abs.

Definition WF_ntl (ntl : namedtensorlist) : Prop :=
  NoDup ntl.(ntl_sums).*1 /\
  abstracts_rel_vars ntl.(ntl_abstracts) ⊆ list_to_set ntl.(ntl_sums).*1.

Definition WF_tl (tl : tensorlist) : Prop :=
  set_Forall (fun k => (k < Pos.of_succ_nat (length tl.(tl_sums))))
  (abstracts_rel_vars tl.(tl_abstracts)).

(* Definition match_tensorlist_eq (tl tl' : tensorlist) :
  option (Pmap Idx * Pmap Idx * Pmap var * Pset * list (Idx * list var * list var)) :=
  extend_match_of_abstract_tensors
    (fun mb mbi ml mlran rabs => rabs = [])
    ∅ ∅ ∅ ∅ (tl.(tl_abstracts)) (tl'.(tl_abstracts)). *)

Definition make_match_namedtensorlist_data 
  (rsums : list (Idx * Ty)) (rabs : list _) 
  (mbi : Pmap Idx) : namedtensorlist :=
  mk_ntl (filter (λ '(idx, ty), ~ is_Some (mbi !! idx)) rsums) rabs.

Definition match_namedtensorlist_aux (tl tl' : namedtensorlist) :
  option (namedtensorlist * Pmap Idx * Pmap Idx * Pmap var * Pset) :=
  '(mb, mbi, ml, mlran, rrest) ← extend_match_of_abstract_tensors
    (fun mb mbi ml mlran rabs => 
      set_Forall (λ r, ~ is_Some (mbi !! r)) (abstracts_rel_vars rabs))
    ∅ ∅ ∅ ∅ (tl.(ntl_abstracts)) (tl'.(ntl_abstracts));
  Some (make_match_namedtensorlist_data tl'.(ntl_sums) rrest mbi, 
    mb, mbi, ml, mlran).

Definition match_rewrite_namedtensorlist (lhs rhs target : namedtensorlist) : 
  option namedtensorlist :=
  '() match_namedtensorlist_aux lhs target with 
  | None => None
  | (* TODO: Problem!!! Here, I want to insert the rhs—but the bound variables
    could conflict! I want to work only with WF namedtensorlist, so this is 
    actually a big problem. (Un)Fortunately, there's a simple solution: I just
    need to work with [tensorlist]s exclusively (yes, with all the relabeling
    hell that will create). I believe the algorithm should be essentially the
    same, and we'll do much the same as [ntl2tl] to do the renumbering
    (i.e., [imap] is the key) *) MThrow

Definition match_tensorlist *)



(* OLD: 

(* Matching on [tensorlist]s *)

(* TODO: When I figure out the "boundary condition" or whatever that is,
   incorporate it into the function at this level somehow? *)
Fixpoint extend_map_of_abstract_pair
  (mb : Pmap Idx) (* The map of [rel]/bound variables, which must map
    to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (l r : list var) : option (Pmap Idx * Pmap var) :=
  match l, r with
  | [], [] => Some (mb, ml)
  | hl :: l, hr :: r =>
    match hl, hr with
    | glob gl, glob gr => (* global variables must match exactly! *)
      if bool_decide (gl = gr) then
        extend_map_of_abstract_pair mb ml l r
      else None
    | glob gl, _ => (* global variables can't map anywhere (nontrivially) *)
      None
    | loc ll, vr => (* local variables can map anywhere (ab initio, at least) *)
      match ml !! ll with
      | None => extend_map_of_abstract_pair mb (<[ll := vr]> ml) l r
      | Some vr' =>
        if bool_decide (vr = vr') then
          extend_map_of_abstract_pair mb ml l r
        else None
      end
    | rel rl, rel rr => (* bound variables must map to bound variables *)
      match mb !! rl with
      | None => extend_map_of_abstract_pair (<[rl := rr]> mb) ml l r
      | Some rr' =>
        if bool_decide (rr = rr') then
          extend_map_of_abstract_pair mb ml l r
        else None
      end
    | rel rl, _ => (* bound variables can only map to other bound variables *)
      None
    end
  | _, _ => None
  end.

Definition list_first_omap {A B} (f : A -> option B) : list A -> option B :=
  fix list_first_omap l :=
  match l with
  | [] => None
  | a :: l =>
    match f a with
    | Some b => Some b
    | None => list_first_omap l
    end
  end.


(* TODO: rewrite with collate (also, optionally shortcut to false if
  we don't use up all the abstracts for a given index) *)
Fixpoint extend_match_of_abstract_tensors
  (P : Pmap Idx -> Pmap var -> list (Idx * list var * list var) -> Prop)
  `{HP : forall mb ml rrest, Decision (P mb ml rrest)}
  (mb : Pmap Idx) (* The map of [rel]/bound variables, which must map
    to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (labs rabs : list (Idx * list var * list var)) :
    option (Pmap Idx * Pmap var * list (Idx * list var * list var)) :=
  match labs with
  | [] =>
    if decide (P mb ml rabs) then
      Some (mb, ml, rabs)
    else None
  | (fl, lowl, upl) :: labs =>
    list_first_omap (fun '((_, lowr, upr), rrest) =>
      '(mb, ml) ← extend_map_of_abstract_pair mb ml lowl lowr;
         '(mb, ml) ← extend_map_of_abstract_pair mb ml upl upr;
        extend_match_of_abstract_tensors P mb ml labs rrest)
      (list_select (fun '(fr, _, _) => fl = fr) rabs)
    (* head ('((_, lowr, upr), rrest) ← list_select (fun '(fr, _, _) => fl = fr) rabs;
      from_option (λ x, [x]) []
        (m' ← extend_map_of_abstract_pair lbound rbound m lowl lowr;
         m'' ← extend_map_of_abstract_pair lbound rbound m' upl upr;
         extend_match_of_abstract_tensors lbound rbound m'' labs rrest)
      ) *)
  end.

Definition match_tensorlist (tl tl' : tensorlist) :
  option (Pmap Idx * Pmap var * list (Idx * list var * list var)) :=
  extend_match_of_abstract_tensors
    (fun mb ml rabs => rabs = [])
    ∅ ∅ (tl.(tl_abstracts)) (tl'.(tl_abstracts)).


*)


