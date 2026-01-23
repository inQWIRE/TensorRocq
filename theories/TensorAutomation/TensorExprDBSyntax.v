Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap.
From stdpp Require Import pretty.

Require Import Aux_stdpp Aux_pos.

#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.


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

Definition var_elim {A : Type} (fr fl fg : Idx -> A) : var -> A :=
  fun v => match v with
  | rel r => fr r
  | loc l => fl l
  | glob g => fg g
  end.


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

Definition relabel_abs {A B} (f : B -> A) (abs : Idx * list B * list B) :=
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


Lemma relabel_abs_id {A} abs : relabel_abs (@id A) abs = abs.
Proof.
  destruct abs as [[f low] up]; cbn.
  now rewrite 2 list_fmap_id.
Qed.

Lemma relabel_abs_ext {A B} f g abs :
  (forall x, f x = g x) -> @relabel_abs A B f abs = relabel_abs g abs.
Proof.
  intros Heq.
  destruct abs as [[idx low] up]; cbn.
  f_equal; [f_equal|]; apply list_fmap_ext; intros; apply Heq.
Qed.

Lemma relabel_abs_id' {A} f abs :
  (forall x : A, f x = x) -> relabel_abs f abs = abs.
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
  (l r : list var) : option (Pmap Idx * Pmap Idx * Pmap var * Pset) :=
  match l, r with
  | [], [] => Some (mb, mbi, ml, mlran)
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
      '(mb, mbi, ml, mlran) ← extend_map_of_abstract_pair mb mbi ml mlran lowl lowr;
         '(mb, mbi, ml, mlran) ← extend_map_of_abstract_pair mb mbi ml mlran upl upr;
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

Definition fill_tensorlist_rewrite (outer : tensorlist) (inner : tensorlist)
  (relmap : Pmap Idx) (locmap : Pmap var) : tensorlist :=
  let '(mk_tl usums uabs) := outer in (* 'unmatched' sums and abtracts *)
  let '(mk_tl rsums rabs) := inner in (* the 'right-hand side' *)
  let rsize := lengthN rsums in
  let shift := relabel_rels (λ p, pos_add_N p rsize) in
  let uabs_shifted := relabel_abs shift <$> uabs in
  let rabs_subst := relabel_abs (var_subst_locals (λ l,
    from_option shift (loc l) (locmap !! l))) <$> rabs in
  mk_tl (usums ++ rsums) (uabs_shifted ++ rabs_subst).



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









Record tensorequation := mk_teq {
  teq_lhs : tensorexpr;
  teq_rhs : tensorexpr;
  teq_univ : Pmap Ty;
    (* The set of universally-quantified variables and their types *)
}.


Record tensorlistequation := mk_tleq {
  tleq_lhs : tensorlist;
  tleq_rhs : tensorlist;
  tleq_univ : Pmap Ty;
    (* The set of universally-quantified variables and their types *)
}.


(* FIXME: Move *)

Definition get_var {A} (mg ml : Pmap A) (mr : list A) (v : var) : option A :=
  match v with
  | rel r => mr !! (r :> nat)
  | loc l => ml !! l
  | glob g => mg !! g
  end.



Fixpoint te_substl (f : Idx -> var) (te : tensorexpr) : tensorexpr :=
  match te with
  | tone => tone
  | tabstract abs low up =>
    tabstract abs ((λ v, from_option f v (v2loc v)) <$> low)
      ((λ v, from_option f v (v2loc v)) <$> up)
  | tproduct l r =>
    tproduct (te_substl f l) (te_substl f r)
  | tsum ty smd =>
    tsum ty (te_substl (addrel 1 ∘ f) smd)
  end.














Lemma withrelshift_0 f :
  pointwise_relation var eq (withrelshift 0 f) f.
Proof.
  now intros []; cbv; case_match.
Qed.


Add Parametric Morphism : te_substl with signature
  pointwise_relation _ eq ==> eq ==> eq as te_substl_ext.
Proof.
  intros f g Hfg te.
  revert f g Hfg; induction te; intros f g Hfg.
  - easy.
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

Lemma elem_of_te_local_varset_tabstract absidx lower upper l :
  l ∈ te_local_varset (tabstract absidx lower upper) <->
  loc l ∈ lower ++ upper.
Proof.
  cbn.
  rewrite elem_of_list_to_set, elem_of_list_omap.
  split; [|unfold v2loc; eexists; split; [eauto|reflexivity]].
  now intros ([] & ? & [= ->]).
Qed.



Lemma relabel_te_ext f g te :
  pointwise_relation var eq f g ->
  relabel_te f te = relabel_te g te.
Proof.
  intros; now apply relabel_te_aux_ext.
Qed.

Lemma withrelshift_compose shift f g v :
  withrelshift shift f (withrelshift shift g v) =
  withrelshift shift (f ∘ g) v.
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


Lemma withrelshift_id shift v :
  withrelshift shift id v = v.
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
    rewrite <- ! list_fmap_compose.
    f_equal; apply list_fmap_ext; intros _ v _;
    cbn; apply withrelshift_compose.
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
    now rewrite 2 list_fmap_id' by now intros; apply withrelshift_id.
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



















(* TODO: Rewrite condition: te_local_varset lhs ⊆ te_local_varset rhs *)

Lemma extend_map_of_abstract_pair_correct
  (mb mbi : Pmap Idx) (* The map and inverse map of [rel]/bound variables,
    which must map to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (mlran : Pset) (* The set of [rel] variables in the range of [ml], which
     must be disjoint from the image of [mb] / domain of [mbi] *)
  (l r : list var)
  mb' mbi' ml' mlran' :
  extend_map_of_abstract_pair mb mbi ml mlran l r =
    Some (mb', mbi', ml', mlran') ->
  map_inverses mb mbi ->
  set_Forall (λ r, mbi !! r = None) mlran ->
  map_img (omap v2rel ml) = mlran ->
  mb ⊆ mb' /\ mbi ⊆ mbi' /\ ml ⊆ ml' /\
  map_inverses mb' mbi' /\
  dom mb' = dom mb ∪ list_to_set (omap v2rel l) /\
  set_Forall (λ r, mbi' !! r = None) mlran' /\
  map_img (omap v2rel ml') = mlran' /\
  dom ml' = dom ml ∪ list_to_set (omap v2loc l) /\
  Some <$> r = (var_elim (fmap rel ∘ (mb' !!.)) (ml' !!.)
     (λ g, Some (glob g))) <$> l.
Proof.
  revert r mb mbi ml mlran mb' mbi' ml' mlran';
  induction l as [|hl l IHl]; intros [|hr r]; [|easy..|];
  intros mb mbi ml mlran mb' mbi' ml' mlran';
  [cbn; intros [= -> -> -> ->] **; split_and!; easy + set_solver +|].
  cbn [extend_map_of_abstract_pair].
  refine (match hl with
    | rel rl => match hr with
      | rel rr => _
      | _ => fun H => False_rect _ (None_ne_Some _ H)
      end
    | loc ll => _
    | glob gl =>
      match hr with
      | glob gr => _
      | _ => fun H => False_rect _ (None_ne_Some _ H)
      end
    end).
  - destruct (mb !! rl) as [rr'|] eqn:Hrr';
    [|destruct (mbi !! rr) eqn:Hrl; [easy|]];
    rewrite <- decide_bool_decide.
    + case_decide as Heq; [|easy].
      subst rr'.
      intros Hext Hinvs Hdisj Hmlran.
      apply IHl in Hext as Hs; [|eauto..].
      split_and!; try apply Hs;
        destruct Hs as (Hmb & Hmbi & Hml & Hinvs' & Hdoms & Hs).
      * rewrite Hdoms.
        cbn [omap list_omap v2rel list_to_set].
        apply elem_of_dom_2 in Hrr'.
        set_solver + Hrr'.
      * f_equal /=; [|apply Hs].
        apply (fun H => lookup_weaken _ _ _ _ H Hmb) in Hrr'.
        now rewrite Hrr'.
    + case_decide as Hrr_disj; [easy|].
      intros Hext Hinvs Hdisj Hmlran.
      specialize (IHl _ _ _ _ _ _ _ _ _ Hext).
      tspecialize IHl by now apply map_inverses_insert_fresh.
      tspecialize IHl by now
        intros lr Hlr;
        rewrite lookup_insert_ne by (now intros <-);
        now apply Hdisj.
      tspecialize IHl by easy.
      split_and!; try apply IHl.
      1: now rewrite <- IHl.1; apply insert_subseteq.
      1: now rewrite <- IHl.2.1; apply insert_subseteq.
      1: cbn [omap list_omap v2rel list_to_set];
        rewrite IHl.2.2.2.2.1; set_solver +.
      cbn; f_equal.
      * specialize (IHl.1 rl).
        cbn.
        rewrite lookup_insert.
        cbn.
        destruct (mb' !! rl) as [|]; [|easy].
        intros <-.
        easy.
      * destruct IHl as (Hmb & _ & Hml & _ & _ & _ & _ & _ & Hlr).
        apply (list_eq_same_length) with (length r);
        [apply (f_equal length) in Hlr; revert Hlr;
          simpl_list; easy| now rewrite length_fmap|].
        intros i mri mli Hi Heq.
        pose proof Heq as Heq'.
        rewrite list_lookup_fmap in Heq.
        apply lookup_lt_is_Some in Hi as Hri.
        destruct Hri as [ri Hri].
        rewrite Hri in Heq.
        cbn in Heq.
        apply (inj Some) in Heq.
        subst mri.
        rewrite list_lookup_fmap.
        rewrite Hlr in Heq'.
        rewrite list_lookup_fmap in Heq'.
        destruct (l !! i) as [li|]; [|easy].
        cbn in Heq'.
        apply (inj Some) in Heq'.
        destruct li as [lr | ll | lg]; cbn in Heq' |- *;
        now intros [= <-].
  - destruct (ml !! ll) as [vr'|] eqn:Hvr';
    [rewrite <- decide_bool_decide; case_decide as Heq; [|intros [=]]|
    destruct hr as [rr|rl|rg] eqn:Hhr;
    [destruct (mbi !! rr) eqn:Hmbirr;
      [intros [=]|]|..]].
    + intros Hext Hinvs Hdisj Hmlran.
      specialize (IHl _ _ _ _ _ _ _ _ _ Hext).
      do 3 tspecialize IHl by easy.
      split_and!; try apply IHl.
      * rewrite IHl.2.2.2.2.2.2.2.1.
        cbn [omap list_omap v2loc list_to_set].
        apply elem_of_dom_2 in Hvr'.
        set_solver +Hvr'.
      * destruct IHl as (Hmb & Hmbi & Hml & Hs).
        f_equal /=; [|apply Hs].
        subst.
        now apply (fun H => lookup_weaken _ _ _ _ H Hml) in Hvr'.
    + intros Hext Hinvs Hdisj Hmlran.
      specialize (IHl _ _ _ _ _ _ _ _ _ Hext Hinvs).
      tspecialize IHl. 1:{
        apply set_Forall_union; [|easy].
        now apply set_Forall_singleton.
      }
      tspecialize IHl. 1:{
        rewrite omap_insert.
        cbn [v2rel].
        rewrite map_img_insert_notin_L, Hmlran; [easy|].
        now rewrite lookup_omap, Hvr'.
      }
      split_and!; try apply IHl.
      1: now rewrite <- IHl.2.2.1; apply insert_subseteq.
      1: now rewrite IHl.2.2.2.2.2.2.2.1; set_solver +.
      destruct IHl as (Hmb & Hmbi & Hml & Hs).
      cbn; f_equal; [|apply Hs].
      symmetry.
      revert Hml.
      apply lookup_weaken, lookup_insert.
    + intros Hext Hinvs Hdisj Hmlran.
      specialize (IHl _ _ _ _ _ _ _ _ _ Hext Hinvs Hdisj).
      rewrite omap_insert_None in IHl by reflexivity.
      rewrite delete_notin in IHl by now rewrite lookup_omap, Hvr'.
      tspecialize IHl by easy.
      subst hr.
      split_and!; try apply IHl.
      1: now rewrite <- IHl.2.2.1; apply insert_subseteq.
      1: now rewrite IHl.2.2.2.2.2.2.2.1; set_solver +.
      destruct IHl as (Hmb & Hmbi & Hml & Hs).
      cbn; f_equal; [|apply Hs].
      symmetry.
      revert Hml.
      apply lookup_weaken, lookup_insert.
    + intros Hext Hinvs Hdisj Hmlran.
      specialize (IHl _ _ _ _ _ _ _ _ _ Hext Hinvs Hdisj).
      rewrite omap_insert_None in IHl by reflexivity.
      rewrite delete_notin in IHl by now rewrite lookup_omap, Hvr'.
      tspecialize IHl by easy.
      subst hr.
      split_and!; try apply IHl.
      1: now rewrite <- IHl.2.2.1; apply insert_subseteq.
      1: now rewrite IHl.2.2.2.2.2.2.2.1; set_solver +.
      destruct IHl as (Hmb & Hmbi & Hml & Hs).
      cbn; f_equal; [|apply Hs].
      symmetry.
      revert Hml.
      apply lookup_weaken, lookup_insert.
  - rewrite <- decide_bool_decide.
    case_decide as Hgs; [|easy].
    intros Hext Hinvs Hdisj Hmlran.
    specialize (IHl _ _ _ _ _ _ _ _ _ Hext Hinvs Hdisj Hmlran).
    split_and!; try apply IHl.
    f_equal /=; [now subst|].
    apply IHl.
Qed.


Lemma list_first_omap_eq_head_bind {A B} (f : A -> option B) l :
  list_first_omap f l =
  head (x ← l; from_option (λ x, [x]) [] (f x)).
Proof.
  induction l; [done|].
  cbn.
  rewrite IHl.
  destruct (f a); reflexivity.
Qed.

Lemma list_first_omap_Some {A B} (f : A -> option B) l b :
  list_first_omap f l = Some b ->
  exists a, a ∈ l /\ f a = Some b.
Proof.
  rewrite list_first_omap_eq_head_bind.
  intros (a & Hb & Ha)%head_Some_elem_of%elem_of_list_bind.
  exists a; split; [easy|].
  destruct (f a); [|easy].
  cbn in Hb.
  rewrite elem_of_list_singleton in Hb.
  now subst.
Qed.





Lemma extend_match_of_abstract_tensors_correct
  (P : Pmap Idx -> Pmap Idx -> Pmap var -> Pset ->
    list (Idx * list var * list var) -> Prop)
  `{HP : forall mb mbi ml mlran rrest, Decision (P mb mbi ml mlran rrest)}
  (mb mbi : Pmap Idx) (* The map and inverse map of [rel]/bound variables,
    which must map to other bound variables *)
  (ml : Pmap var) (* The map of local variables, which can map to any [var] *)
  (mlran : Pset) (* The set of [rel] variables in the range of [ml], which
     must be disjoint from the image of [mb] / domain of [mbi] *)
  (labs rabs : list (Idx * list var * list var))
  mb' mbi' ml' mlran' rrest :

  extend_match_of_abstract_tensors P mb mbi ml mlran labs rabs =
    Some (mb', mbi', ml', mlran', rrest) ->

    map_inverses mb mbi ->
  set_Forall (λ r, mbi !! r = None) mlran ->
  map_img (omap v2rel ml) = mlran ->
  P mb' mbi' ml' mlran' rrest /\
  mb ⊆ mb' /\ mbi ⊆ mbi' /\ ml ⊆ ml' /\
  map_inverses mb' mbi' /\
  dom mb' = dom mb ∪ abstracts_rel_vars labs /\
  set_Forall (λ r, mbi' !! r = None) mlran' /\
  map_img (omap v2rel ml') = mlran' /\
  dom ml' = dom ml ∪ abstracts_local_vars labs /\
  (relabel_abs (var_elim (fmap rel ∘ (mb' !!.)) (ml' !!.)
     (λ g, Some (glob g))) <$> labs) ++
     (relabel_abs Some <$> rrest) ≡ₚ relabel_abs Some <$> rabs.
Proof.
  revert rabs mb mbi ml mlran mb' mbi' ml' mlran' rrest;
  induction labs as [|((fl, lowl), upl) labs IHlabs];
  intros rabs mb mbi ml mlran mb' mbi' ml' mlran' rrest;
  [cbn; case_decide; intros [= -> -> -> -> ->] **; split_and!;
    easy + set_solver +|].
  cbn.
  intros ((((absr, lowr), upr), rrest') &
    (Habsr & Hperm)%elem_of_list_select_perm_Prop
    & ([[[mb1 mbi1] ml1] mlran1] & Hext1 &
      ([[[mb2 mbi2] ml2] mlran2] & Hext2 & Hext)%bind_Some
      )%bind_Some)%list_first_omap_Some.
  intros Invs Hdisj Hmlran.
  specialize (extend_map_of_abstract_pair_correct _ _ _ _ _ _
    _ _ _ _ Hext1) as Hext1'.
  clear Hext1; rename Hext1' into Hext1.
  tspecialize Hext1 by auto.
  tspecialize Hext1 by auto.
  tspecialize Hext1 by auto.
  specialize (extend_map_of_abstract_pair_correct _ _ _ _ _ _
    _ _ _ _ Hext2) as Hext2'.
  clear Hext2; rename Hext2' into Hext2.
  tspecialize Hext2 by apply Hext1.
  tspecialize Hext2 by apply Hext1.
  tspecialize Hext2 by apply Hext1.
  specialize (IHlabs _ _ _ _ _ _ _ _ _ _ Hext).
  move IHlabs at bottom.
  tspecialize IHlabs by apply Hext2.
  tspecialize IHlabs by apply Hext2.
  tspecialize IHlabs by apply Hext2.
  split; [apply IHlabs|].
  split; [now rewrite Hext1.1, Hext2.1|].
  split; [now rewrite Hext1.2.1, Hext2.2.1|].
  split; [now rewrite Hext1.2.2.1, Hext2.2.2.1|].
  split; [apply IHlabs|].
  split.
  1: {
    rewrite IHlabs.2.2.2.2.2.1, Hext2.2.2.2.2.1, Hext1.2.2.2.2.1.
    rewrite list_to_set_app_L.
    rewrite omap_app, list_to_set_app_L.
    set_solver +.
  }
  split; [apply IHlabs|].
  split; [apply IHlabs|].
  split.
  1: {
    rewrite IHlabs.2.2.2.2.2.2.2.2.1,
      Hext2.2.2.2.2.2.2.2.1, Hext1.2.2.2.2.2.2.2.1.
    rewrite list_to_set_app_L.
    rewrite omap_app, list_to_set_app_L.
    set_solver +.
  }

  rewrite Hperm.
  cbn.
  rewrite <- IHlabs.2.2.2.2.2.2.2.2.2.
  cbn.
  f_equiv.
  f_equal; [f_equal; [easy|]|].
  - pose proof Hext1.2.2.2.2.2.2.2.2 as Hlowl.
    apply list_eq_same_length with (length lowl);
    [generalize (f_equal length Hlowl); now simpl_list|
    now rewrite length_fmap|].
    intros i x y Hi.
    rewrite 2!list_lookup_fmap.
    generalize (f_equal (.!! i) Hlowl).
    rewrite 2!list_lookup_fmap.
    destruct (lowl !! i) as [li|]; [|easy].
    destruct (lowr !! i) as [ri|]; [|easy].
    cbn in *.
    intros [= Hli] [= <-] [= <-].
    destruct li as [lr | ll | lg]; cbn in *;
    rewrite Hli; [f_equal | | reflexivity].
    + destruct (mb1 !! lr) as [mb1lr|] eqn:Hmb1lr ; [|easy].
      apply (lookup_weaken _ _ _ _ (Hmb1lr)).
      rewrite Hext2.1; apply IHlabs.2.1.
    + destruct (ml1 !! ll) as [ml1ll|] eqn:Hml1ll ; [|easy].
      apply (lookup_weaken _ _ _ _ (Hml1ll)).
      rewrite Hext2.2.2.1; apply IHlabs.2.2.2.1.
  - pose proof Hext2.2.2.2.2.2.2.2.2 as Hupl.
    apply list_eq_same_length with (length upl);
    [generalize (f_equal length Hupl); now simpl_list|
    now rewrite length_fmap|].
    intros i x y Hi.
    rewrite 2!list_lookup_fmap.
    generalize (f_equal (.!! i) Hupl).
    rewrite 2!list_lookup_fmap.
    destruct (upl !! i) as [li|]; [|easy].
    destruct (upr !! i) as [ri|]; [|easy].
    cbn in *.
    intros [= Hli] [= <-] [= <-].
    destruct li as [lr | ll | lg]; cbn in *;
    rewrite Hli; [f_equal | | reflexivity].
    + destruct (mb2 !! lr) as [mb1lr|] eqn:Hmb1lr ; [|easy].
      apply (lookup_weaken _ _ _ _ (Hmb1lr)).
      apply IHlabs.2.1.
    + destruct (ml2 !! ll) as [ml1ll|] eqn:Hml1ll ; [|easy].
      apply (lookup_weaken _ _ _ _ (Hml1ll)).
      apply IHlabs.2.2.2.1.
Qed.






(* Typing for [tensorexpr]s *)

Notation vartypecontext := (Pmap Ty).
Notation abstypecontext := (Pmap (list Ty)).

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

Definition tc_app_types (tys : list Ty) (tc : typecontext) : typecontext :=
  mk_tc (tc.(tc_ma)) (tc.(tc_mg)) (tc.(tc_ml)) (tys ++ tc.(tc_mr)).

Lemma tc_cons_app_type ty tys tc :
  tc_cons_type ty (tc_app_types tys tc) = tc_app_types (ty :: tys) tc.
Proof.
  reflexivity.
Qed.

(* FIXME: Move *)
Definition tc_eqn_with_locals (tc : typecontext) (tl : Pmap Ty) : typecontext :=
  mk_tc (tc.(tc_ma)) (tc.(tc_mg)) (tl ∪ tc.(tc_ml)) [].

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
Notation "1" := (tone) : tensorexpr_scope.
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


Definition is_well_typed_abs (ta : abstypecontext)
  (tg tl : vartypecontext) (tr : list Ty)
  (f : Idx) (low up : list var) : bool :=
  bool_decide ((fmap Some) <$> ta !! f =@{option (list _)}
    Some ((get_var tg tl tr) <$> (low ++ up))).

Fixpoint is_well_typed (ta : abstypecontext)
  (tg tl : vartypecontext) (tr : list Ty) (te : tensorexpr) : bool :=
  match te with
  | tone => true
  | tabstract f low up => is_well_typed_abs ta tg tl tr f low up
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


Definition all_bound (tl : tensorlist) : Prop :=
  abstracts_rel_vars tl.(tl_abstracts) =
  list_to_set (pseq 1 (lengthN tl.(tl_sums))).

Definition tleq_well_typed tc teeq : Prop :=
  let tc' := mk_tc tc.(tc_ma) tc.(tc_mg) teeq.(tleq_univ) [] in
  well_typed tc' teeq.(tleq_lhs) /\
  well_typed tc' teeq.(tleq_rhs) /\
  te_local_varset teeq.(tleq_rhs) ⊆ te_local_varset teeq.(tleq_lhs) /\
  dom teeq.(tleq_univ) = te_local_varset teeq.(tleq_lhs)
    (* NB: ⊆ suffices, by the first WT condition *).

(* (* TODO: Make; FIXME: Move *)
Fixpoint Pmap_ne_sizeP {A} (p : Pmap_ne A) : positive := *)
  


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
  let llocs := abstracts_local_vars labs in
  Pset_subseteqb (abstracts_local_vars rabs) llocs &&&
  Pmap_dom_subseteqb univ (llocs.(mapset.mapset_car))
  ).

Lemma is_well_typed_tproducts ta tg tl tr tes :
  is_well_typed ta tg tl tr (tproducts tes) =
  forallb (is_well_typed ta tg tl tr) tes.
Proof.
  induction tes as [|te tes]; cbn; [easy|rewrite <- IHtes].
  f_equal.
  destruct tes; [|easy].
  cbn; now rewrite andb_true_r.
Qed.

Lemma tl_is_well_typed_alt_aux ta tg tl tr (tel : tensorlist) :
  is_well_typed ta tg tl tr tel =
    let '(mk_tl lsums labs) := tel in
    forallb (λ '(f, low, up),
    is_well_typed_abs ta tg tl (rev_append lsums tr) f low up) labs.
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

Lemma well_typed_local_varset_subseteq tc te :
  well_typed tc te -> te_local_varset te ⊆ dom (tc.(tc_ml)).
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
Qed.

Lemma and_iff_from_l {P Q R S} :
  (P <-> Q) -> (P -> Q -> (R <-> S)) ->
  P /\ R <-> Q /\ S.
Proof.
  tauto.
Qed.

Lemma te_local_varset_tl (tl : tensorlist) :
  te_local_varset tl =
  abstracts_local_vars tl.(tl_abstracts).
Proof.
  destruct tl as [sums abs].
  cbn.
  induction sums; [|apply IHsums].
  cbn.
  induction abs as [|((f, low), up) abs IHabs]; [reflexivity|].
  cbn.
  rewrite list_to_set_app_L, <- IHabs.
  destruct abs as [|((f', low'), up') abs]; cbn.
  - now rewrite union_empty_r_L.
  - reflexivity.
Qed.


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
    [now rewrite Pset_subseteqb_correct, 2 te_local_varset_tl|].
  intros Hsub%Pset_subseteqb_correct Hsub'.
  rewrite Pmap_dom_subseteqb_correct, Aux_stdpp.dom_Pset.
  rewrite te_local_varset_tl; cbn [tl_abstracts].
  split; [|now intros ->].
  intros Hsub''.
  unfold_leibniz.
  apply set_subseteq_antisymm; [easy|].
  apply well_typed_local_varset_subseteq in Hty_l.
  rewrite te_local_varset_tl in Hty_l.
  apply Hty_l.
Qed.


Lemma pos_swap_alt p :
  pos_swap p = (if decide (p = 1) then 2 else if decide (p = 2) then 1 else p)%positive.
Proof.
  unfold pos_swap.
  destruct p as [| []|]; reflexivity.
Qed.


Lemma relabel_te_swap_wt_aux ctx prefix ty ty' te :
  well_typed {|
    tc_ma := tc_ma ctx;
    tc_mg := tc_mg ctx;
    tc_ml := tc_ml ctx;
    tc_mr := prefix ++ ty' :: ty :: tc_mr ctx
  |} te
  -> well_typed {|
      tc_ma := tc_ma ctx;
      tc_mg := tc_mg ctx;
      tc_ml := tc_ml ctx;
      tc_mr := prefix ++ ty :: ty' :: tc_mr ctx
    |}
    (relabel_te_aux (lengthN prefix) (relabel_rels pos_swap) te).
Proof.
  revert prefix; induction te; intros prefix; cbn.
  - easy.
  - intros ->.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v _.
    destruct v; [|easy..].
    cbn.
    case_decide as Hle; cbn.
    + rewrite 2 lookup_app_l by now
        rewrite <- lengthN_correct; lia.
      reflexivity.
    + rewrite 2 lookup_app_r by now
        rewrite <- lengthN_correct; lia.
      rewrite pos_swap_alt.
      case_decide as H1; [|case_decide as H2].
      * replace (_ - _)%nat with 0%nat by
          now rewrite <- lengthN_correct; lia.
        replace (_ - _)%nat with 1%nat by
          now rewrite <- lengthN_correct; lia.
        reflexivity.
      * replace (_ - _)%nat with 1%nat by
          now rewrite <- lengthN_correct; lia.
        replace (_ - _)%nat with 0%nat by
          now rewrite <- lengthN_correct; lia.
        reflexivity.
      * symmetry.
        replace (_ - _)%nat with (pos_to_nat_pred p - length prefix)%nat by lia.
        enough (Hge : (pos_to_nat_pred p - length prefix >= 2)%nat) by
          now clear -Hge; rewrite ! lookup_cons_ne_0 by lia.
        rewrite <- lengthN_correct; lia.
  - intros []; auto.
  - unfold tc_cons_type; cbn.
    rewrite app_comm_cons.
    apply IHte.
Qed.

Lemma relabel_te_swap_wt ctx ty ty' te :
  well_typed (tc_cons_type ty' (tc_cons_type ty ctx)) te
  -> well_typed (tc_cons_type ty (tc_cons_type ty' ctx))
    (relabel_te (relabel_rels pos_swap) te).
Proof.
  rewrite (unfold relabel_te).
  unfold tc_cons_type; cbn.
  change (ty' :: ty :: ?x) with ([] ++ ty' :: ty :: x).
  change (ty :: ty' :: ?x) with ([] ++ ty :: ty' :: x).
  remember nil as prefix eqn:Hpre.
  replace 0%N with (lengthN prefix) by now subst.
  clear Hpre.
  apply relabel_te_swap_wt_aux.
Qed.



Lemma relabel_te_cons_wt_aux ctx pre tys te :
  well_typed {|
      tc_ma := tc_ma ctx;
      tc_mg := tc_mg ctx;
      tc_ml := tc_ml ctx;
      tc_mr := pre ++ tc_mr ctx
    |} te <->
  well_typed {|
      tc_ma := tc_ma ctx;
      tc_mg := tc_mg ctx;
      tc_ml := tc_ml ctx;
      tc_mr := pre ++ tys ++ tc_mr ctx
    |} (relabel_te_aux (lengthN pre) (relabel_rels (λ p, pos_add_N p (lengthN tys))) te).
Proof.
  revert tys pre.
  induction te; intros tys pre.
  - easy.
  - cbn.
    f_equiv.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v _.
    destruct v; [|easy..].
    cbn.
    case_decide as Hle; cbn.
    + rewrite 2 lookup_app_l by now
        rewrite <- lengthN_correct; lia.
      reflexivity.
    + rewrite 2 lookup_app_r by now
        rewrite <- lengthN_correct; lia.
      rewrite <- lengthN_correct.
      rewrite lookup_app_r by now rewrite <- lengthN_correct; lia.
      f_equal.
      rewrite <- lengthN_correct; lia.
  - cbn; naive_solver.
  - cbn. unfold tc_cons_type; cbn.
    rewrite 2 app_comm_cons.
    apply IHte.
Qed.

Lemma relabel_te_cons_wt ctx ty te :
  well_typed ctx te <->
  well_typed (tc_cons_type ty ctx) (relabel_te (relabel_rels Pos.succ) te).
Proof.
  rewrite (unfold relabel_te).
  unfold tc_cons_type; cbn.
  change (ty :: ?x) with ([] ++ ty :: x).
  remember nil as prefix eqn:Hpre.
  replace 0%N with (lengthN prefix) by now subst.
  (* intros Hwt. *)
  erewrite relabel_te_aux_ext;
  [| | reflexivity]; [etransitivity; [|apply (relabel_te_cons_wt_aux _ _ [ty])]|];
  [|intros []; [|reflexivity..]; cbn; f_equal; lia].
  subst.
  now destruct ctx.
Qed.



Lemma te_substl_wt_aux ctx rels tys te (substs : Pmap var) :
  (forall l, l ∈ te_local_varset te ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
  well_typed (tc_app_types rels (tc_eqn_with_locals ctx tys)) te ->
  well_typed (tc_app_types rels ctx)
    (te_substl (addrel (lengthN rels) ∘ λ l, default (loc l) (substs !! l)) te).
Proof.
  revert rels ctx;
  induction te; intros rels ctx Hty.
  - easy.
  - cbn.
    intros Hhyp.
    assert (Hrels : forall r, rel r ∈ lower ++ upper -> (N.pos r <= lengthN rels)%N). 1:{
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
    setoid_rewrite elem_of_te_local_varset_tabstract in Hty.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
    destruct v as [r|l|]; [..|reflexivity].
    + cbn.
      apply Hrels in Hv.
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
      (addrel (N.succ (lengthN rels)) ∘ λ l, default (loc l) (substs !! l)));
      [| | reflexivity].
    2: {
      intros v; cbn.
      destruct (substs !! v) as [[]|]; [|reflexivity..].
      cbn.
      f_equal; lia.
    }
    rewrite tc_cons_app_type.
    apply (IHte (ty :: rels)); [easy|].
    now rewrite tc_cons_app_type in Hte.
Qed.

Lemma te_substl_wt ctx tys te (substs : Pmap var) :
  (forall l, l ∈ te_local_varset te ->
    (tc_get_var ctx) <$> (substs !! l) = (Some <$> tys !! l)) ->
  well_typed (tc_eqn_with_locals ctx tys) te ->
  well_typed ctx
    (te_substl (λ l, default (loc l) (substs !! l)) te).
Proof.
  specialize (te_substl_wt_aux ctx [] tys te substs) as Hen.
  intros Hty Hwt.
  specialize (Hen Hty Hwt).
  replace (tc_app_types _ _) with ctx in Hen by now destruct ctx.
  erewrite te_substl_ext; [apply Hen | | reflexivity].
  intros v; cbn.
  destruct (substs !! v) as [[]|]; reflexivity.
Qed.










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
Qed.



(* Equivalence of [tensorlist]s up to (alpha-equivalence and) permutation *)
Definition tl_aeq : relation tensorlist :=
  fun tl tl' =>
  exists (fr : Idx -> Idx),
    let n := N.succ_pos (lengthN (tl.(tl_sums))) in
    posperm n fr /\
    ppermute fr (reverse tl.(tl_sums))
      = (reverse tl'.(tl_sums)) /\
    tl.(tl_abstracts) ≡ₚ
      relabel_abs (relabel_rels $ make_pwf n fr) <$> tl'.(tl_abstracts).

Lemma tl_aeq_refl tl : tl_aeq tl tl.
Proof.
  exists id.
  split; [apply posperm_id|].
  split; [apply ppermute_id|].
  apply eq_reflexivity, symmetry, list_fmap_id'.
  intros ((f, low), up) _.
  cbn.
  f_equal; [f_equal|]; apply list_fmap_id'; intros [] _; reflexivity ||
    now cbn; case_decide.
Qed.


Lemma tl_aeq_symm tl tl' : tl_aeq tl tl' -> tl_aeq tl' tl.
Proof.
  intros (f & Hf & Hsums & Habs).
  exists (posperm_inv (N.succ_pos $ lengthN tl.(tl_sums)) f).
  apply (f_equal length) in Hsums as Hlen.
  rewrite length_ppermute, 2 length_reverse in Hlen.
  pose proof Hlen as HlenN.
  rewrite <- 2 lengthN_correct in HlenN.
  apply N2Nat.inj in HlenN.
  intros n.
  split; [subst n; rewrite <- HlenN; now apply posperm_inv_posperm|].
  split.
  - rewrite <- Hsums.
    rewrite ppermute_compose by
      now rewrite lengthN_reverse;
        apply posperm_inv_bounded + apply posperm_bounded.
    apply ppermute_id'.
    rewrite lengthN_reverse.
    intros p Hp.
    now apply posperm_inv_rinv.
  - rewrite Habs.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity, symmetry, list_fmap_id'.
    intros ((fidx, low), up) _.
    cbn.
    rewrite <- 2 list_fmap_compose.
    f_equal; [f_equal|]; apply list_fmap_id'; intros [r| |] _; try reflexivity;
      cbn;
      subst n;
      rewrite <- HlenN;
      (destruct_decide (decide (N.succ_pos (lengthN tl.(tl_sums)) <= r)) as Hr;
      [now rewrite decide_True |
       rewrite decide_False by
        now pose proof (posperm_bounded _ _ Hf r); lia]);
    f_equal; apply posperm_inv_linv; easy + lia.
Qed.

Lemma tl_aeq_trans tl tl' tl'' : tl_aeq tl tl' -> tl_aeq tl' tl'' ->
  tl_aeq tl tl''.
Proof.
  intros (f & Hf & Hfsums & Hfabs)
    (g & Hg & Hgsums & Hgabs).
  exists (f ∘ g).
  intros n.
  apply (f_equal length) in Hfsums as Hflen.
  apply (f_equal length) in Hgsums as Hglen.
  rewrite length_ppermute, !length_reverse in Hflen, Hglen.
  pose proof Hflen as HflenN.
  pose proof Hglen as HglenN.
  rewrite <- 2 lengthN_correct in HflenN, HglenN.
  apply N2Nat.inj in HflenN, HglenN.
  split; [now apply posperm_compose; subst n; congruence|].
  split.
  - rewrite <- Hgsums, <- Hfsums.
    symmetry; apply ppermute_compose;
    rewrite lengthN_reverse;
    now apply posperm_bounded; congruence.
  - rewrite Hfabs, Hgabs.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity.
    apply list_fmap_ext; intros _ ((idx, low), up) _.
    cbn.
    rewrite <- 2 list_fmap_compose.
    f_equal; [f_equal|]; apply list_fmap_ext; intros _ [r| |] _; try reflexivity;
      cbn;
      subst n;
      rewrite <- HflenN;
      (destruct_decide (decide (N.succ_pos (lengthN tl.(tl_sums)) <= r)) as Hr;
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

Lemma tl_times_tlone_l tl : tl_times tlone tl = tl.
Proof.
  destruct tl as [sums abs]; cbn.
  now case_match.
Qed.

Lemma tl_times_tlone_r tl : tl_times tl tlone = tl.
Proof.
  destruct tl as [sums abs]; cbn.
  now case_match;
  rewrite 2 app_nil_r.
Qed.

Lemma tensorlist_of_tensorexpr_tproducts tes :
  tensorlist_of_tensorexpr (tproducts tes) =
  fold_right tl_times tlone (tensorlist_of_tensorexpr <$> tes).
Proof.
  induction tes as [|te tes IHtes]; [reflexivity|].
  cbn.
  rewrite <- IHtes.
  destruct tes; [|reflexivity].
  cbn.
  now rewrite tl_times_tlone_r.
Qed.

Lemma tensorlist_of_tl_to_te_with_aux tes sums abs :
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
Qed.


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



Lemma tl_times_comm_aeq tl tl' :
  tl_times tl tl' =tl= tl_times tl' tl.
Proof.
  rewrite 2 tl_times_spec_defn_correct.
  destruct tl as [lsums labs], tl' as [rsums rabs].
  cbn.
  eexists; cbn -[reverse].
  rewrite 2 reverse_app.
  split; [|split; [apply ppermute_pbig_swap_app|]];
  [eapply pbig_swap_posperm'; rewrite lengthN_app, 2 lengthN_reverse; lia|].
  rewrite Permutation_app_comm.
  rewrite fmap_app, <- 2 list_fmap_compose.
  pose proof (lengthN_correct rsums).
  pose proof (lengthN_correct lsums).
  rewrite 2 lengthN_reverse, lengthN_app.
  apply Permutation_app; apply eq_reflexivity, list_fmap_ext;
    intros _ ((f, low), up) _; cbn;
    rewrite <- 2 list_fmap_compose;
    apply abs_fmap_l_ext; rewrite <- 2 fmap_app;
    generalize (low ++ up); intros l;
    apply list_fmap_ext;
    (intros _ [r| |] _; [cbn|reflexivity..]);
    unfold pbig_swap;
    repeat case_decide; f_equal; lia || reflexivity.
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

(* FIXME: Move *)

Definition tl_well_bound (tl : tensorlist) : Prop :=
  abstracts_rel_vars tl.(tl_abstracts) ⊆
  list_to_set (pseq 1 (lengthN tl.(tl_sums))).

(* FIXME: Move*)
Lemma relabel_abs_compose {A B C} (f : A -> B) (g : B -> C) l :
  relabel_abs g (relabel_abs f l) = relabel_abs (g ∘ f) l.
Proof.
  unfold relabel_abs.
  destruct l as ((idx, low), up).
  now rewrite <- 2 list_fmap_compose.
Qed.
Lemma relabel_rels_id v : relabel_rels id v = v.
Proof. now destruct v. Qed.
Lemma relabel_rels_id' f v :
  (forall r, f r = r) -> relabel_rels f v = v.
Proof.
  intros Hf.
  erewrite relabel_rels_ext; [apply relabel_rels_id|apply Hf].
Qed.


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
  apply relabel_rels_id'.
  intros; unfold make_pwf; case_decide; reflexivity.
Qed.

Add Parametric Morphism {A B} : fmap with signature
  pointwise_relation A (@eq B) ==> (@eq (list A)) ==> (@eq (list B)) as list_fmap_mor.
Proof.
  intros; unfold pointwise_relation;
  apply list_fmap_ext; auto.
Qed.

(* FIXME: Move!!!! *)
#[global] Instance var_inhabited : Inhabited var := populate (rel 1).

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
  dom mb' = abstracts_rel_vars labs /\
  dom mbi' ⊆ abstracts_rel_vars rabs /\
  map_img ml' ⊆ abstracts_vars rabs /\
  set_Forall (λ r, mbi' !! r = None) mlran' /\
  map_img (omap v2rel ml') = mlran' /\
  dom ml' = abstracts_local_vars labs /\
  (relabel_abs (var_elim (fmap rel ∘ (mb' !!.)) (ml' !!.)
     (λ g, Some (glob g))) <$> labs) ++
     (relabel_abs Some <$> rrest) ≡ₚ relabel_abs Some <$> rabs /\
  (relabel_abs (var_elim (rel ∘ (mb' !!!.)) (ml' !!!.)
     (glob)) <$> labs) ++
     rrest ≡ₚ rabs /\
  forall a,
    a ∈ labs
    → relabel_abs
        (var_elim (fmap rel ∘ λ i : Idx, mb' !! i)
           (λ i : Idx, ml' !! i) (λ g : Idx, Some (glob g))) a
      ∈ relabel_abs Some <$> rabs.
Proof.
  intros Heq.
  apply extend_match_of_abstract_tensors_correct in Heq;
  [|apply map_inverses_empty|apply set_Forall_empty|reflexivity].
  assert (Hsubs :
    (relabel_abs
     (var_elim (fmap rel ∘ λ i : Idx, mb' !! i)
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
    unfold abstracts_rel_vars.
    apply elem_of_list_to_set, elem_of_list_bind.
    exists x.
    split; [|easy].
    destruct a as ((idx, low), up), x as ((idx', low'), up').
    cbn in Hx.
    rewrite elem_of_list_omap.
    exists (rel q).
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
  - apply (fmap_Permutation (relabel_abs (default (rel 1)))) in Heq
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
  !FinSet A SA, FinMap B MB, FinSet B SB, !RelDecision (∈@{SB}) }
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

(* FIXME: Move *)
Lemma elem_of_abstracts_rel_vars l abs :
  l ∈ abstracts_rel_vars abs <->
  exists idx low up, (idx, low, up) ∈ abs /\ rel l ∈ low ++ up.
Proof.
  unfold abstracts_rel_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_list_omap.
  split; [|naive_solver].
  intros (idx & low & up & ([] & ? & [= ->]) & ?).
  eauto.
Qed.
Lemma elem_of_abstracts_local_vars l abs :
  l ∈ abstracts_local_vars abs <->
  exists idx low up, (idx, low, up) ∈ abs /\ loc l ∈ low ++ up.
Proof.
  unfold abstracts_local_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_list_omap.
  split; [|naive_solver].
  intros (idx & low & up & ([] & ? & [= ->]) & ?).
  eauto.
Qed.
Lemma elem_of_abstracts_global_vars l abs :
  l ∈ abstracts_global_vars abs <->
  exists idx low up, (idx, low, up) ∈ abs /\ glob l ∈ low ++ up.
Proof.
  unfold abstracts_global_vars.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite 2 exists_pair.
  setoid_rewrite elem_of_list_omap.
  split; [|naive_solver].
  intros (idx & low & up & ([] & ? & [= ->]) & ?).
  eauto.
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
  tl_well_typed_aux (tc_eqn_with_locals tc univ) lsums labs ->
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
    apply elem_of_abstracts_local_vars in Hv as (idx & low & up & Hinl & Hl_lu).
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
    apply elem_of_abstracts_rel_vars in Hrdom as (idx & low & up & Hinl & Hl_lu).
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
  intros r (idx & low & up & Hlu_in & Hin_lu)%elem_of_abstracts_rel_vars.
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




Lemma lookup_list_to_map_imap_to_pos `{FinMap positive M} {A B}
  (f : A -> B) (l : list A) (i : positive) :
  (list_to_map (imap (fun j v => (Pos.of_succ_nat j, f v)) l) :> M B) !! i =
  f <$> (l !! (i:>nat)).
Proof.
  apply option_eq.
  intros x.
  rewrite <- elem_of_list_to_map. 2:{
    rewrite fmap_imap.
    unfold compose.
    cbn.
    rewrite imap_seq_0.
    apply NoDup_fmap_2; [hnf; lia|].
    apply NoDup_seq.
  }
  rewrite elem_of_lookup_imap.
  split.
  - intros (i' & z & [= -> ->] & Heq).
    now rewrite pos_to_nat_pred_of_nat, Heq.
  - destruct (l !! (i:>nat)) as [li|] eqn:Heq; [|easy].
    cbn.
    intros [= <-].
    exists (i:>nat).
    rewrite pos_to_nat_pred_to_pos.
    eauto.
Qed.

Lemma relabel_abs_ext_strong {A B} (f g : A -> B) abs :
  (forall x, x ∈ abs.1.2 ++ abs.2 ->
    f x = g x) -> relabel_abs f abs = relabel_abs g abs.
Proof.
  intros Hfg.
  unfold relabel_abs.
  destruct abs as ((idx, low), up).
  f_equal; [f_equal|]; apply list_fmap_ext; intros _ ? ?%elem_of_list_lookup_2;
  apply Hfg, elem_of_app; [left|right]; easy.
Qed.

Lemma relabel_abs_id_strong {A} (f : A -> A) abs :
  (forall x, x ∈ abs.1.2 ++ abs.2 -> f x = x) -> relabel_abs f abs = abs.
Proof.
  intros Hf.
  transitivity (relabel_abs id abs); [|apply relabel_abs_id].
  now apply relabel_abs_ext_strong.
Qed.

Lemma relabel_rels_compose g f v :
  relabel_rels g (relabel_rels f v) =
  relabel_rels (g ∘ f) v.
Proof.
  now destruct v.
Qed.

Lemma imap_to_fmap {A B} (f : A -> B) l :
  imap (fun _ => f) l = f <$> l.
Proof.
  induction l; cbn; rewrite <- ? IHl; reflexivity.
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

Lemma elem_of_abstracts_vars_rel r abs :
  rel r ∈ abstracts_vars abs <-> r ∈ abstracts_rel_vars abs.
Proof.
  now rewrite elem_of_abstracts_rel_vars, elem_of_abstracts_vars.
Qed.

Lemma elem_of_abstracts_vars_loc r abs :
  loc r ∈ abstracts_vars abs <-> r ∈ abstracts_local_vars abs.
Proof.
  now rewrite elem_of_abstracts_local_vars, elem_of_abstracts_vars.
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


Lemma match_tensorlist_aux_correct mabs mg univ univ' lhs targ utl relmap locmap :
  match_tensorlist_aux lhs targ = Some (utl, relmap, locmap) ->
  all_bound lhs ->
  tl_well_typed (mk_tc mabs mg univ []) lhs ->
  tl_well_typed (mk_tc mabs mg univ' []) targ ->
  (* tl_well_bound targ -> *)
  abstracts_local_vars lhs.(tl_abstracts) = dom locmap /\
  (forall l ty v, univ !! l = Some ty -> locmap !! l = Some v ->
    tc_get_var (mk_tc mabs mg univ' (reverse utl.(tl_sums))) v = Some ty) /\
  targ =tl= fill_tensorlist_rewrite utl lhs relmap locmap.
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
  set (ml' := relabel_rels _ <$> ml).
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
  set (shift := relabel_rels _).
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

  assert (Hrrest_inv_inv : forall x, x ∈ abstracts_rel_vars tabs ->
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
  unfold tc_eqn_with_locals in HWT.
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
        specialize (Hlimg (rel r)) as Hrvar.
        tspecialize Hrvar by now apply elem_of_map_img; eauto.
        rewrite elem_of_abstracts_vars_rel in Hrvar.
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
    specialize (HWT.1 l ty (rel r) Huniv_l Hml_l) as HWT'.
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
      rewrite 2 relabel_rels_compose.
      destruct x as [x| |]; [|reflexivity..].
      cbn.
      f_equal.
      rewrite (decide_False (mb !!! _)) by lia.
      rewrite <- decide_not, (decide_ext _ (Pmap_map rrest_map x < lengthP unused_tys))
        by lia.
      replace (pos_sub_N _ _) with (Pmap_map rrest_map x) by lia.

      move Hrestdisj at bottom.
      specialize (Hrestdisj x).
      assert (Hx_rrest : x ∈ abstracts_rel_vars rrest) by
        now rewrite elem_of_abstracts_rel_vars; eauto.
      tspecialize Hrestdisj by auto.
      apply Hrrest_inv_inv; [|easy].
      enough (abstracts_rel_vars rrest ⊆ abstracts_rel_vars tabs) as Hsub
        by now apply Hsub in Hx_rrest.
      intros a.
      rewrite 2 elem_of_abstracts_rel_vars.
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
          rewrite Hdom, elem_of_abstracts_rel_vars; eauto.
        }
        rewrite lookup_total_alt.
        apply elem_of_dom in Hrdom as [mr Hmr].
        rewrite Hmr.
        cbn.
        f_equal.
        assert (Hrrel : r ∈ abstracts_rel_vars rabs) by
          now rewrite elem_of_abstracts_rel_vars; eauto.
        rewrite Hlhs, elem_of_list_to_set, elem_of_pseq_1 in Hrrel.
        rewrite decide_False by lia.
        rewrite decide_True by lia.
        reflexivity.
      * assert (Hlloc : l ∈ abstracts_local_vars rabs) by
          now rewrite elem_of_abstracts_local_vars; eauto.
        rewrite <- Hldom in Hlloc.
        unfold ml'.
        rewrite lookup_fmap, lookup_total_alt.
        apply elem_of_dom in Hlloc as [v Hv].
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
        specialize (Hlimg (rel r)).
        tspecialize Hlimg by now apply elem_of_map_img; eauto.
        assert (Hrabs : r ∈ abstracts_rel_vars tabs). 1:{
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



(* TODO: Correctness of substitution!!! Then I'm honestly pretty close to done (I hope I swear plase don't make me regret writing this)

  Using fill_tensorlist_rewrite, just need to figure out
  typing requirements and how to induct and then I'm golden! I hope...
  NB: I think the best way to approach doing _this_ is to set up
  the lemma rephrasing semantics of fill_tensorlist_rewrite
  (including switching from reasoning about substituted terms
   to reasoning about semantics with precomposed term maps/contexts)

  So, first lemma should be something like :
    tl_total_semantics _* (fill_tensorlist_rewrite outer inner relmap locmap) =
    [something like]
    ∑ (outer sum shenanigans...),
    tl_total_semantics [NOT THE SAME AS _*; modified using relmap / locmap; possibly want to unfold with the alternate semantics to permute the maps directly]
    * (outer sum abstracts).
  Then, correctness of [tl_tensor_equation] in terms of
  extensionality of [tl_total_semantics] based on well-typed term maps,
  and we can just do that rewrite
*)



































