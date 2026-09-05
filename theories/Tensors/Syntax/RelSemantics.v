From TensorRocq Require Import Summable.
(* Require StringCustomNotation. *)

From TensorRocq Require Import Syntax.Definitions.
From TensorRocq Require Import Rel.Definitions.

From TensorRocq Require Import Aux_pos Aux_stdpp PropAux.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

From stdpp Require Import functions list.



#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.

(* FIXME: Move *)


(* FIXME: Move *)


Section TensorExprDBrel_semantics.

Local Open Scope nat_scope.


(* Import Relation_Definitions.

Import Setoid. *)

Import SetoidList SetoidPermutation list.



(* FIXME: Move*)
Lemma list_to_map_swap_mid `{FinMap K M} {A}
  (l : list (K * A)) ka l' :
  ka.1 ∉ l.*1 ->
  list_to_map (l ++ ka :: l') =@{M A} list_to_map (ka :: (l ++ l')).
Proof.
  intros Hka.
  apply map_eq; intros i.
  cbn.
  rewrite 2 list_to_map_app.
  cbn.
  rewrite lookup_union, 2 lookup_insert_case, lookup_union.
  case_decide.
  - enough (list_to_map l !! i = None) as -> by done.
    apply not_elem_of_list_to_map.
    now subst.
  - done.
Qed.


(* FIXME: Move *)
#[export] Instance default_Proper {B} (R : relation B) :
  Proper (R ==> option_Forall2 R ==> R) default.
Proof.
  intros r s Hrs ma mb Hab.
  induction Hab; cbn; done.
Qed.


(* FIXME: Move *)
#[export] Instance vcast_surj {B n m} (prf : n = m) :
  Surj eq (λ v, @Vector.cast B _ v _ prf).
Proof.
  subst.
  intros v.
  exists v.
  now rewrite cast_id.
Qed.


(* FIXME: Move *)
Lemma exists_vec_0 `(P : vec A 0 -> Prop) :
  ex P <-> P [#].
Proof.
  split; [|eauto].
  intros []; inv_all_vec_fin; done.
Qed.
Lemma exists_vec_S `(P : vec A (S n) -> Prop) :
  ex P <-> exists a v, P (a ::: v).
Proof.
  split; [|naive_solver].
  intros [x Hx].
  inv_all_vec_fin; eauto.
Qed.
Lemma exists_vec_rev `(P : vec A n -> Prop) :
  ex P <-> exists v, P (Vector.rev v).
Proof.
  split; [|intros []; eauto].
  intros [v Hv].
  exists (Vector.rev v).
  rewrite Vector.rev_rev.
  done.
Qed.

(* FIXME: Move *)
Lemma exists_vec_add {B n m} (P : vec B (n + m) -> Prop) :
  ex P <-> exists v w, P (v +++ w).
Proof.
  split; [|now intros (?&?&?); eauto].
  intros (v & Hv).
  induction v using vec_add_inv.
  eauto.
Qed.
Lemma exists_vec_1 {B} (P : vec B 1 -> Prop) :
  ex P <-> exists a, P [#a].
Proof.
  split; [|now intros []; eauto].
  intros []; inv_all_vec_fin; eauto.
Qed.
Lemma exists_comm {B C} `(P : B -> C -> Prop) :
  (exists a b, P a b) <-> exists b a, P a b.
Proof.
  firstorder.
Qed.
Lemma exists_vec_cast {B n m} (P : vec B n -> Prop)
  (prf : m = n) : ex P <-> exists v, P (Vector.cast v prf).
Proof.
  subst.
  setoid_rewrite cast_id.
  done.
Qed.


Section SVmap.

Context {A : Type}.

Definition WF_SVmap tys (m : Pmap A) : Prop :=
  dom m =@{Pset} list_to_set tys.

Definition SVmap (tys : list Idx) := @dsig _ (WF_SVmap tys)
  (λ _, decide_rel (=@{Pset}) _ _).

Definition SVmap_map {tys} (m : SVmap tys) : Pmap A :=
  `m.

Coercion SVmap_map : SVmap >-> Pmap.


(* FIXME: Move *)
Definition Vempty : SVmap [] := dexist ∅ dom_empty_L.

Lemma SVmap_insert_prf {ty val tys svmap}
  (Hv : WF_SVmap tys svmap) : WF_SVmap (ty :: tys) (<[ty := val]> svmap).
Proof.
  unfold WF_SVmap.
  rewrite dom_insert_L.
  cbn -[union].
  f_equal.
  apply Hv.
Qed.

Definition SVmap_insert ty val {tys} (m : SVmap tys) : SVmap (ty :: tys) :=
  dexist (<[ty := val]> (`m)) (SVmap_insert_prf (proj2_dsig m)).



Lemma exists_SVmap_perm tys tys' (f : Pmap A -> Prop) : tys ≡ₚ tys' ->
  (∃ m : SVmap tys, f m) <-> (∃ m : SVmap tys', f m).
Proof.
  intros Hperm.
  unfold SVmap, SVmap_map.
  setoid_rewrite exists_dsig.
  apply exists_iff; intros v.
  f_equiv.
  unfold WF_SVmap.
  f_equiv.
  now apply list_to_set_perm_L.
Qed.

(* FIXME: Move*)
Lemma kmap_SVmap_prf {f : positive -> positive} {tys} {m : Pmap A}
  (Hm : WF_SVmap tys m) : WF_SVmap (f <$> tys) (kmap f m).
Proof.
  hnf.
  apply leibniz_equiv_iff.
  rewrite dom_kmap'.
  rewrite <- (set_map_list_to_set (SA:=Pset)).
  rewrite Hm.
  done.
Qed.

(* FIXME: Move*)
Definition kmap_SVmap (f : positive -> positive) {tys} (m : SVmap tys) :
  SVmap (f <$> tys) :=
  dexist (kmap f (`m)) (kmap_SVmap_prf (proj2_dsig m)).


#[export] Instance kmap_SVmap_surj (f : positive -> positive)
  {Hf : Inj eq eq f}
  {tys} : Surj eq (@kmap_SVmap f tys).
Proof.
  set (Hfi := partial_injection_extension (f <$> tys) (invfun f tys)).
  assert (Hftys : ForallPairs (λ a a' : positive, f a = f a' → a = a') tys)
    by (hnf; naive_solver).
  tspecialize Hfi. 1:{
    apply invfun_inj; done.
  }
  destruct Hfi as (fi & Hfi & Hfiinv').
  intros [m Hm].
  setoid_rewrite dsig_eq.
  cbn.
  apply bool_decide_spec in Hm.
  apply (exists_dsig (Q:=(λ x, kmap f x = m))).
  rewrite Forall_forall in Hfiinv'.
  exists (kmap fi m).
  split.
  - apply (@kmap_SVmap_prf fi _ _) in Hm.
    rewrite <- list_fmap_compose in Hm.
    erewrite list_fmap_id' in Hm; [done|].
    intros a Ha.
    cbn.
    rewrite Hfiinv' by set_solver + Ha.
    apply invfun_linv, Ha; done.
  - rewrite kmap_kmap by apply _.
    rewrite <- (kmap_id m) at 2.
    apply kmap_ext.
    intros k a Hmk%elem_of_dom_2.
    cbn.
    rewrite Hm in Hmk.
    apply elem_of_list_to_set in Hmk.
    rewrite Hfiinv' by done.
    now apply invfun_rinv.
Qed.


(* FIXME: Move*)
Definition SVmap_cast {tys tys'} (Htys : tys = tys')
  (v : SVmap tys) : SVmap tys' := dexist (`v) (eq_trans (proj2_dsig v) (f_equal list_to_set Htys)).

#[export] Instance SVmap_cast_cancel_r {tys tys'} (Htys : tys = tys') :
  Cancel eq (SVmap_cast Htys) (SVmap_cast (eq_sym Htys)).
Proof.
  intros m.
  apply dsig_eq; done.
Qed.

#[export] Instance SVmap_cast_cancel_l {tys tys'} (Htys : tys = tys') :
  Cancel eq (SVmap_cast (eq_sym Htys)) (SVmap_cast Htys).
Proof.
  intros m.
  apply dsig_eq; done.
Qed.

#[export] Instance SVmap_cast_inj {tys tys'} (Htys : tys = tys')
  : Inj eq eq (SVmap_cast Htys).
Proof.
  apply cancel_inj.
Qed.

#[export] Instance SVmap_cast_surj {tys tys'} (Htys : tys = tys')
  : Surj eq (SVmap_cast Htys).
Proof.
  apply cancel_surj.
Qed.

Definition SVmap_castP {tys tys'} (Htys : tys ≡ₚ tys')
  (v : SVmap tys) : SVmap tys' := dexist (`v) (eq_trans (proj2_dsig v)
    (list_to_set_perm_L _ _ Htys)).

#[export] Instance SVmap_castP_cancel_r {tys tys'} (Htys : tys ≡ₚ tys') :
  Cancel eq (SVmap_castP Htys) (SVmap_castP (symmetry Htys)).
Proof.
  intros m.
  apply dsig_eq; done.
Qed.

#[export] Instance SVmap_castP_cancel_l {tys tys'} (Htys : tys ≡ₚ tys') :
  Cancel eq (SVmap_castP (symmetry Htys)) (SVmap_castP Htys).
Proof.
  intros m.
  apply dsig_eq; done.
Qed.

#[export] Instance SVmap_castP_inj {tys tys'} (Htys : tys ≡ₚ tys')
  : Inj eq eq (SVmap_castP Htys).
Proof.
  apply cancel_inj.
Qed.

#[export] Instance SVmap_castP_surj {tys tys'} (Htys : tys ≡ₚ tys')
  : Surj eq (SVmap_castP Htys).
Proof.
  apply cancel_surj.
Qed.

(* FIXME: Move *)
Lemma SVmap_union_prf {tys tys'} {v : Pmap A} {v' : Pmap A} :
  WF_SVmap tys v -> WF_SVmap tys' v' ->
  WF_SVmap (tys ++ tys') (v ∪ v').
Proof.
  intros [=Hv] [=Hv'].
  hnf.
  rewrite dom_union_L, list_to_set_app_L.
  congruence.
Qed.
Definition SVmap_union {tys tys'} (v : SVmap tys) (v' : SVmap tys') : SVmap (tys ++ tys') :=
  dexist _ (SVmap_union_prf (proj2_dsig v) (proj2_dsig v')).
Lemma SVmap_insert_union_l {ty tys tys'}
  (a : A) (v : SVmap tys) (v' : SVmap tys') : 
  SVmap_insert ty a (SVmap_union v v') = 
  SVmap_union (SVmap_insert ty a v) v'.
Proof.
  apply dsig_eq.
  cbn.
  apply insert_union_l.
Qed.


(* FIXME: Move *)
Lemma exists_SVmap_cons ty tys f :
  (∃ mr : SVmap (ty :: tys), f mr) <->
  ∃ mr' : SVmap tys, ∃ vty : A, f (SVmap_insert ty vty mr').
Proof.
  split.
  - intros ([mr Hmr] & Hfmr).
    assert (Hmty : is_Some (mr !! ty)). 1:{
      apply elem_of_dom.
      rewrite (bool_decide_unpack _ Hmr).
      now apply elem_of_list_to_set; constructor.
    }
    destruct Hmty as [vty Hvty].
    destruct_decide (decide (ty ∈ tys)) as Hty.
    + assert (Hmr' : WF_SVmap tys mr) by
        (unfold WF_SVmap in *; rewrite (bool_decide_unpack _ Hmr); set_solver +Hty).
      exists (dexist _ Hmr').
      exists vty.
      refine (eq_rect _ _ Hfmr _ _).
      apply dsig_eq.
      cbn.
      symmetry.
      now apply insert_id.
    + assert (Hmr' : WF_SVmap tys (delete ty mr)). 1:{
        unfold WF_SVmap in *.
        clear Hfmr.
        apply bool_decide_spec in Hmr.
        rewrite dom_delete_L.
        rewrite Hmr.
        set_solver + Hty.
      }
      exists (dexist _ Hmr').
      exists vty.
      refine (eq_rect _ _ Hfmr _ _).
      apply dsig_eq.
      cbn.
      symmetry.
      now apply insert_delete.
  - naive_solver.
Qed.


Lemma exists_SVmap_fmap (f : positive -> positive) `{Hf : !Inj eq eq f}
  (sums : list positive) (fr : _ -> Prop) :
  (∃ v : SVmap (f <$> sums), fr v) <->
  ∃ v : SVmap sums, fr (kmap_SVmap f v).
Proof.
  unfold SVmap;
  eapply (exists_relabel'_r2l (kmap_SVmap f) _ _ (RA:=eq) (RB:=eq));
  [apply _..|].
  done.
Qed.


Lemma exists_SVmap_nil (fr : _ -> Prop) :
  (∃ v : SVmap [], fr v) <-> fr Vempty.
Proof.
  apply exists_iff_of_unique.
  intros [b Hb] _.
  apply dsig_eq.
  cbn.
  apply bool_decide_spec in Hb.
  apply dom_empty_iff_L in Hb.
  done.
Qed.

Lemma exists_SVmap_cons' ty tys f :
  (∃ mr : SVmap (ty :: tys), f mr) <->
  ∃ vty : A, ∃ mr' : SVmap tys, f (SVmap_insert ty vty mr').
Proof.
  now rewrite exists_SVmap_cons, exists_comm.
Qed.


Lemma exists_SVmap_app
  (sums sums' : list positive) (fr : _ -> Prop) :
  (∃ v : SVmap (sums ++ sums'), fr v) <->
  ∃ v : SVmap sums, ∃ v' : SVmap sums', fr (SVmap_union v v').
Proof.
  revert fr; induction sums; intros fr.
  - rewrite exists_SVmap_nil.
    cbn.
    apply exists_iff; intros.
    f_equiv.
    apply dsig_eq.
    cbn.
    now rewrite map_empty_union.
  - cbn.
    rewrite 2 exists_SVmap_cons'.
    apply exists_iff; intros va.
    rewrite IHsums.
    unfold SVmap.
    setoid_rewrite SVmap_insert_union_l.
    reflexivity.
Qed.

End SVmap.



Context {A : Type}.
(* Let Tensor := (@Tensor R). *)

Let DimensionlessRel := (DimensionlessRel A).


Definition Vapplys_rel (f : DimensionlessRel) (l u : list A) : Prop :=
  f (length l) (length u) (list_to_vec l) (list_to_vec u).

Notation varcontext := (Pmap A).

Notation abscontext := (Pmap DimensionlessRel).


Definition rget_var (ml : varcontext) (mr : list A) (v : var) : option A :=
  match v with
  | bound r => mr !! (r :> nat)
  | free l => ml !! l
  end.

(*
Fixpoint rel_semantics (abs : abscontext) (vars : varcontext)
  (te : tensorexpr) : option R :=
  match te with
  | tone => Some rI
  | tabstract absidx lower upper =>
      args ← join_list ((vars !!.) <$> (lower ++ upper));
      fval ← abs !! absidx;
      Vapplys_rel fval args
  | tproduct l r =>
      lval ← rel_semantics abs vars l;
      rval ← rel_semantics abs vars r;
      Some (rmul lval rval)
  | tsum v n summand =>
      Some (sum_of (fun x : V n =>
        default rO (rel_semantics abs (<[v := mk_A x]> vars) summand)))
  end. *)

Definition abstract_rel_semantics (mabs : abscontext) ml mr
  (absidx : Idx) (lower : list var) (upper : list var) : Prop :=
  default False (largs ← join_list ((rget_var ml mr) <$> lower);
      uargs ← join_list ((rget_var ml mr) <$> upper);
      fval ← mabs !! absidx;
      Some (Vapplys_rel fval largs uargs)).

Notation abstract_rel_semantics' mabs mg ml mr abs :=
  (abstract_rel_semantics mabs mg ml mr abs.1.1 abs.1.2 abs.2).


Lemma abstract_rel_semantics_ext mabs ml mr mabs' ml' mr'
  idx lower upper idx' lower' upper' :
  mabs !! idx = mabs' !! idx' ->
  (rget_var ml mr) <$> lower = (rget_var ml' mr') <$> lower' ->
  (rget_var ml mr) <$> upper = (rget_var ml' mr') <$> upper' ->
  abstract_rel_semantics mabs ml mr idx lower upper =
  abstract_rel_semantics mabs' ml' mr' idx' lower' upper'.
Proof.
  intros Hidx Hl Hu.
  unfold abstract_rel_semantics.
  now rewrite Hidx, Hl, Hu.
Qed.

Definition delta_rel_semantics ml mr (l u : var) : Prop :=
  default False (la ← rget_var ml mr l;
    ua ← rget_var ml mr u;
    Some (id_rel 1 [# la] [# ua])).

Lemma delta_rel_semantics_ext ml mr ml' mr' l u l' u' :
  rget_var ml mr l = rget_var ml' mr' l' ->
  rget_var ml mr u = rget_var ml' mr' u' ->
  delta_rel_semantics ml mr l u =
  delta_rel_semantics ml' mr' l' u'.
Proof.
  intros Hl Hu.
  unfold delta_rel_semantics.
  now rewrite Hl, Hu.
Qed.

Fixpoint total_rel_semantics_aux mabs ml mr (te : tensorexpr) : Prop :=
  match te with
  | tone => True
  | tdelta1 l u =>
    delta_rel_semantics ml mr l u
  | tabstract absidx lower upper =>
      abstract_rel_semantics mabs ml mr absidx lower upper
  | tproduct l r =>
      (total_rel_semantics_aux mabs ml mr l) /\
        (total_rel_semantics_aux mabs ml mr r)
  | tsum summand =>
      ex (fun x : A =>
        total_rel_semantics_aux mabs ml (x :: mr) summand)
  end.

Notation total_rel_semantics mabs ml te := (total_rel_semantics_aux mabs ml [] te).

Fixpoint tl_total_rel_semantics_aux mabs ml mr sums abs delt : Prop :=
  match sums with
  | 0 => Rlist_prod
    ((λ '(abs, low, up), abstract_rel_semantics mabs ml mr abs low up) <$> abs) /\
    Rlist_prod ((λ '(l, u), delta_rel_semantics ml mr l u) <$> delt)
  | S sums =>
    ex (fun x : A =>
      tl_total_rel_semantics_aux mabs ml (x :: mr) sums abs delt)
  end.

Notation tl_total_rel_semantics mabs ml tl :=
  (tl_total_rel_semantics_aux mabs ml [] tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).





Lemma total_rel_semantics_aux_cons_gen mabs ml mr mr' te p x :
  p ∉ te_free_varset te ->
  total_rel_semantics_aux mabs ml (mr ++ x :: mr') te <->
  total_rel_semantics_aux mabs (<[p:=x]> ml) (mr ++ mr')
    (relabel_te_aux (N.of_nat (length mr)) (substbound p) te).
Proof.
  intros Hp.
  revert mr.
  enough (Hen : forall mr v, v <> free p ->
    rget_var ml (mr ++ x :: mr') v =
      rget_var (<[p:=x]> ml) (mr ++ mr')
        (withboundshift (length mr) (substbound p) v));
  [induction te; intros mr|].
  - reflexivity.
  - cbn.
    assert (Hl : l ∈ te_varset (tdelta1 l u)) by now set_solver +.
    assert (Hu : u ∈ te_varset (tdelta1 l u)) by now set_solver +.
    rewrite elem_of_te_free_varset_free in Hp.
    assert (Hlp : l <> free p) by congruence.
    assert (Hup : u <> free p) by congruence.
    apply eq_reflexivity, delta_rel_semantics_ext;
    [exact (Hen mr l Hlp)|exact (Hen mr u Hup)].
  - cbn.
    apply eq_reflexivity, abstract_rel_semantics_ext; [reflexivity|..];
    rewrite <- list_fmap_compose;
    apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2;
    apply Hen;
    cbn;
    rewrite elem_of_te_free_varset_free in Hp;
    intros Heq; apply Hp;
    rewrite <- Heq; apply elem_of_list_to_set, elem_of_app; auto.
  - cbn.
    f_equiv; [apply IHte1|apply IHte2]; cbn in Hp; set_solver +Hp.
  - cbn.
    apply exists_iff; intros val.
    rewrite (IHte Hp (val :: mr)).
    cbn.
    f_equiv.
    f_equal; lia.
  - intros mr [r|l] Hv.
    + cbn.
      case_decide as Hr; [cbn; now rewrite 2 lookup_app_l by lia|].
      rewrite lookup_app_r by lia.
      destruct (pos_sub_N r (length mr)) eqn:Hsub using Pos.peano_rect.
      * cbn.
        replace (_ - _) with O by lia.
        cbn.
        now rewrite lookup_insert.
      * rewrite lookup_cons_ne_0 by lia.
        rewrite Pos.peano_rect_succ.
        cbn.
        rewrite lookup_app_r by lia.
        f_equal; lia.
    + cbn.
      now rewrite lookup_insert_ne by congruence.
Qed.


Lemma total_rel_semantics_aux_cons mabs ml mr' te p x :
  p ∉ te_free_varset te ->
  total_rel_semantics_aux mabs ml (x :: mr') te <->
  total_rel_semantics_aux mabs (<[p:=x]> ml) mr'
    (relabel_te (substbound p) te).
Proof.
  intros Hp%(total_rel_semantics_aux_cons_gen mabs ml [] mr' te p x).
  apply Hp.
Qed.


Lemma total_rel_semantics_tsum_alt mabs ml te :
  total_rel_semantics mabs ml (tsum te) <->
  ∃ x : A,
    total_rel_semantics mabs (<[fresh (te_free_varset te):=x]> ml)
    (relabel_te (substbound (fresh (te_free_varset te))) te).
Proof.
  cbn.
  apply exists_iff; intros x.
  apply total_rel_semantics_aux_cons.
  apply is_fresh.
Qed.


Lemma tl_total_rel_semantics_aux_ext_base mabs mabs' ml ml' mr mr'
  abs abs' delt delt' :
  Forall2 (fun flu flu' =>
    mabs !! flu.1.1 = mabs' !! flu'.1.1 /\
    Forall2 (fun v v' => rget_var ml mr v = rget_var ml' mr' v') flu.1.2 flu'.1.2
    /\ Forall2 (fun v v' => rget_var ml mr v = rget_var ml' mr' v') flu.2 flu'.2
    ) abs abs' ->
  Forall2 (fun lu lu' =>
    rget_var ml mr lu.1 = rget_var ml' mr' lu'.1 /\
    rget_var ml mr lu.2 = rget_var ml' mr' lu'.2) delt delt' ->
  tl_total_rel_semantics_aux mabs ml mr 0 abs delt <->
  tl_total_rel_semantics_aux mabs' ml' mr' 0 abs' delt'.
Proof.
  intros Habs Hdelt.
  cbn.
  f_equiv.
  - induction Habs as [|flu flu' abs abs' [Hf Hlu] Habs IHabs]; [reflexivity|].
   cbn.
    f_equiv; [|apply IHabs].
    clear Habs IHabs.
    destruct flu as [[f low] up], flu' as [[f' low'] up'].
    apply eq_reflexivity, abstract_rel_semantics_ext; [exact Hf|..];
    now apply list_eq_Forall2, Forall2_fmap.
  - induction Hdelt as [|lu lu' delt delt' [Hl Hu] Hdelt IHdelt]; [reflexivity|].
    cbn.
    f_equiv; [|easy].
    destruct lu, lu'; now apply eq_reflexivity, delta_rel_semantics_ext.
Qed.


(* Lemma tl_total_rel_semantics_aux_tl_times_aux mabs ml mr mr'
  lsums labs ldelt rsums rabs rdelt :
  (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < rsums + length mr')%nat ->
  (∀ p : positive, p ∈ deltas_bound_vars rdelt -> p < rsums + length mr')%nat ->
  tl_total_rel_semantics_aux mabs ml (mr' ++ mr) (lsums + rsums)
    ((relabel_abs (relabel_bounds (λ p,
      if decide (p < lsums)%nat then
        pos_add_N p rsums
      else pos_add_N p (length mr' + rsums))) <$> labs) ++
      (relabel_abs (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rabs))
    ((relabel_delt (relabel_bounds (λ p,
      if decide (p < lsums)%nat then
        pos_add_N p rsums
      else pos_add_N p (length mr' + rsums))) <$> ldelt) ++
      (relabel_delt (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rdelt)) <->
  tl_total_rel_semantics_aux mabs ml mr lsums labs ldelt *
  tl_total_rel_semantics_aux mabs ml mr' rsums rabs rdelt.
Proof.
  intros Hrabs Hrdelt.
  revert mr; induction lsums as [|lsums IHlsums]; intros mr.
  - cbn [app length Nat.add N.of_nat pos_add_N].
    change (if decide (_ < 0) then _ else ?x) with x.
    erewrite (list_fmap_ext _ _ rabs). 2:{
      intros; apply relabel_abs_id';
      intros; apply relabel_bounds_id';
      intros; apply decide_same.
    }
    erewrite (list_fmap_ext _ _ rdelt). 2:{
      intros; apply relabel_delt_id';
      intros; apply relabel_bounds_id';
      intros; apply decide_same.
    }
    rewrite 2 list_fmap_id.


    (* setoid_rewrite relabel_bounds_ext.
    setoid_rewrite decide_same.
    setoid_rewrite relabel_abs_id'.
    setoid_rewrite relabel_bounds_id'.
    relabel_bounds_ext

    setoid_rewrite decide_same.
    unfold N.of_nat at 4.
    cbn [pos_add_N].
    rewrite (list_fmap_id' _ rabs). 2:{
      intros [[f low] up] _.
      apply relabel_abs_id'.
      intros []; [|reflexivity..].
      cbn.
      now case_decide.
    }
    erewrite list_fmap_ext. 2:{
      intros _ abs _.
      apply relabel_abs_ext.
      apply relabel_bounds_ext.
      intros r.
      rewrite decide_False by lia.
      reflexivity.
    }
    cbn. *)
    revert mr' Hrabs Hrdelt;
    induction rsums as [|rsums IHrsums]; intros mr' Hrabs Hrdelt.
    + cbn.
      rewrite rmul_comm_double.
      f_equiv.
      * rewrite fmap_app.
        rewrite Rlist_prod_app.
        f_equiv.
        --apply eq_reflexivity.
          f_equal.
          rewrite <- list_fmap_compose.
          apply list_fmap_ext; intros _ [[f low] up] _.
          cbn.
          apply abstract_rel_semantics_ext; [reflexivity|..].
          ++rewrite <- list_fmap_compose.
            apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
            destruct v; [|reflexivity..].
            cbn.
            rewrite lookup_app_r by lia;
            f_equal; lia.
          ++rewrite <- list_fmap_compose.
            apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
            destruct v; [|reflexivity..].
            cbn.
            rewrite lookup_app_r by lia;
            f_equal; lia.
        --apply eq_reflexivity.
          f_equal.
          apply list_fmap_ext; intros _ [[f low] up] Hf%elem_of_list_lookup_2.
          cbn.
          apply abstract_rel_semantics_ext; [reflexivity|..].
          ++apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
            destruct v; [|reflexivity..].
            cbn.
            apply lookup_app_l.
            specialize (Hrabs p).
            tspecialize Hrabs by now
              apply elem_of_abstracts_bound_vars;
              set_solver +Hv Hf.
            easy.
          ++apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
            destruct v; [|reflexivity..].
            cbn.
            apply lookup_app_l.
            specialize (Hrabs p).
            tspecialize Hrabs by now
              apply elem_of_abstracts_bound_vars;
              set_solver +Hv Hf.
            easy.
      *
    + cbn.
      rewrite exists_and_l.
      apply exists_iff; intros x.
      rewrite <- (IHrsums (mk_A x :: mr')) by
        now cbn in Hrabs |- *; intros ? ?%Hrabs; lia.
      (* 2: cbn; intros ? ?%Hrabs; lia. *)
      cbn.
      f_equiv.
      f_equal.
      apply list_fmap_ext; intros _ [[f low] up] _.
      apply relabel_abs_ext, relabel_bounds_ext.
      intros r; f_equal; lia.
  - cbn.
    rewrite exists_and_r.
    apply exists_iff; intros x.
    rewrite <- IHlsums.
    apply tl_total_rel_semantics_aux_ext_mr.
    apply Forall2_app; clear -Hrabs.
    + clear Hrabs.
      induction labs as [|[[f low] up] labs IHlabs]; constructor;
      [clear IHlabs|apply IHlabs].
      split; [reflexivity|].
      cbn.
      rewrite <- 2 fmap_app.
      generalize (low ++ up) as lu.
      intros lu.
      induction lu as [|v lu IHlu]; constructor; [|apply IHlu].
      destruct v as [r|l|g]; [|reflexivity..].
      cbn.
      rewrite 2 pos_sub_N_to_nat.
      rewrite !(dif_dist pos_to_nat_pred).
      rewrite !pos_add_N_to_nat.
      remember (pos_to_nat_pred r) as nr eqn:Hnr.
      replace r with (Pos.of_succ_nat nr) by (subst; unfold pos_to_nat_pred; lia).
      clear r Hnr.
      rewrite !N2Nat.inj_add.
      rewrite !Nat2N.id.
      rewrite length_app.
      destruct_decide (decide (nr < S (length lsums))) as HnrS;
      [destruct_decide (decide (nr < (length lsums))) as Hnr|
        rewrite (decide_False (P:= nr < _)) by lia;
        rewrite decide_False by lia].
      * rewrite decide_True by lia.
        reflexivity.
      * replace nr with (length lsums) by lia.
        rewrite decide_False by lia.
        rewrite Nat.sub_diag.
        cbn.
        rewrite lookup_app_r by lia.
        now replace (_ - _) with O by lia.
      * rewrite lookup_app_r by lia.
        rewrite 2 lookup_cons_ne_0 by lia.
        rewrite lookup_app_r by lia.
        f_equal; lia.
    + induction rabs as [|[[f low] up] rabs IHrabs]; constructor;
        [clear IHrabs|apply IHrabs; set_solver +Hrabs].
      split; [reflexivity|].
      cbn.
      rewrite <- 2 fmap_app.
      pose proof Hrabs as Hlu.
      cbn in Hlu.
      setoid_rewrite elem_of_list_to_set in Hlu.
      setoid_rewrite elem_of_app in Hlu.
      pose proof (fun p H => Hlu p (or_introl H)) as Hlu.
      clear Hrabs.
      revert Hlu.
      generalize (low ++ up) as lu.
      intros lu.
      induction lu as [|v lu IHlu]; intros Hlu; constructor.
      2: {
        apply IHlu.
        intros p Hp; apply Hlu.
        cbn.
        now destruct (v2bound v); [constructor|].
      }

      destruct v as [r|l|g]; [|reflexivity..].
      cbn.
      specialize (Hlu r ltac:(constructor)).
      rewrite 2 pos_sub_N_to_nat.
      rewrite !(dif_dist pos_to_nat_pred).
      rewrite !pos_add_N_to_nat.
      remember (pos_to_nat_pred r) as nr eqn:Hnr.
      replace r with (Pos.of_succ_nat nr) by (subst; unfold pos_to_nat_pred; lia).
      clear r Hnr.
      rewrite !Nat2N.id.
      rewrite length_app.
      destruct_decide (decide (nr < (length rsums))) as Hnr;
      [rewrite decide_True by lia; reflexivity|].
      rewrite decide_False by lia.
      rewrite lookup_cons_ne_0 by lia.
      rewrite 2 lookup_app_l by lia.
      f_equal; lia.
Qed. *)

Lemma fold_tl_rel_semantics_aux_base mabs ml mr abst delt :
  (Rlist_prod ((λ '(abs, low, up),
    abstract_rel_semantics mabs ml mr abs low up) <$> abst) /\
  Rlist_prod ((λ '(l, u),
    delta_rel_semantics ml mr l u) <$> delt)) =
  tl_total_rel_semantics_aux mabs ml mr O abst delt.
Proof.
  reflexivity.
Qed.

Lemma tl_total_rel_semantics_aux_ext_base_mr mabs ml mr mr'
  abs abs' delt delt' :

  Forall2 (fun flu flu' =>
    flu.1.1 = flu'.1.1 /\
    let P := (fun v v' =>
      match v, v' with
      | bound r, bound r' =>
        mr !! (r :> nat) = mr' !! (r' :> nat)
      | free l, free l' => l = l'
      | _, _ => False
      end) in
    Forall2 P flu.1.2 flu'.1.2 /\
    Forall2 P flu.2 flu'.2) abs abs' ->
  Forall2 (fun lu lu' =>
    let P := (fun v v' =>
      match v, v' with
      | bound r, bound r' =>
        mr !! (r :> nat) = mr' !! (r' :> nat)
      | free l, free l' => l = l'
      | _, _ => False
      end) in
    P lu.1 lu'.1 /\ P lu.2 lu'.2) delt delt' ->
  tl_total_rel_semantics_aux mabs ml mr O abs delt <->
  tl_total_rel_semantics_aux mabs ml mr' O abs' delt'.
Proof.
  intros Habs Hdelt.
  apply tl_total_rel_semantics_aux_ext_base.
  - apply (Forall2_impl _ _ _ _ Habs).
    intros flu flu' [Hf Hlu].
    split; [now rewrite Hf|].
    cbv zeta in Hlu.
    split; [apply (Forall2_impl _ _ _ _ Hlu.1)|
      apply (Forall2_impl _ _ _ _ Hlu.2)];
    (intros [r|l] [r'|l']; [|now intros []..]);
    cbn; easy.
  - apply (Forall2_impl _ _ _ _ Hdelt).
    intros [l u] [l' u'] [Hl Hu]; cbn in *.
    split; unfold rget_var; [destruct l, l'|destruct u, u']; cbn; now subst.
Qed.


Lemma tl_total_rel_semantics_aux_ext_mr mabs ml mr mr'
  sums abs abs' delt delt' :
  Forall2 (fun flu flu' =>
    let P := (fun v v' =>
      match v, v' with
      | bound r, bound r' =>
        if decide (r < sums \/ r' < sums) then r = r'
          else mr !! (pos_sub_N r sums :> nat) =
            mr' !! (pos_sub_N r' sums :> nat)
      | free l, free l' => l = l'
      | _, _ => False
      end) in
    flu.1.1 = flu'.1.1 /\
    Forall2 P flu.1.2 flu'.1.2 /\
    Forall2 P flu.2 flu'.2) abs abs' ->
  Forall2 (fun lu lu' =>
    let P := (fun v v' =>
      match v, v' with
      | bound r, bound r' =>
        if decide (r < sums \/ r' < sums) then r = r'
          else mr !! (pos_sub_N r sums :> nat) =
            mr' !! (pos_sub_N r' sums :> nat)
      | free l, free l' => l = l'
      | _, _ => False
      end) in
    P lu.1 lu'.1 /\ P lu.2 lu'.2) delt delt' ->
  tl_total_rel_semantics_aux mabs ml mr sums abs delt <->
  tl_total_rel_semantics_aux mabs ml mr' sums abs' delt'.
Proof.
  revert mr mr'.
  induction sums as [|sums IHsums]; intros mr mr' Habs Hdelt.
  - apply tl_total_rel_semantics_aux_ext_base_mr.
    + apply (Forall2_impl _ _ _ _ Habs).
      intros flu flu' [Hf Hlu].
      split; [now rewrite Hf|].
      cbv zeta.
      split; [apply (Forall2_impl _ _ _ _ Hlu.1)|
        apply (Forall2_impl _ _ _ _ Hlu.2)];
      (intros [r|l] [r'|l']; [|now intros []..]);
      cbn; easy.
    + apply (Forall2_impl _ _ _ _ Hdelt).
      intros [l u] [l' u'] [Hl Hu]; cbn in *.
      split; unfold rget_var; [destruct l, l'|destruct u, u']; cbn; now subst.
  - cbn.
    apply exists_iff; intros x.
    apply IHsums.
    + apply (Forall2_impl _ _ _ _ Habs).
      intros flu flu' [Hf Hlu].
      split; [now rewrite Hf|].
        split; [apply (Forall2_impl _ _ _ _ Hlu.1)|
          apply (Forall2_impl _ _ _ _ Hlu.2)];
      (intros [r|l] [r'|l']; [|now intros []..]);
      (intros Hrs;
      destruct_decide (decide (r < sums \/ r' < sums)) as Hrsm;
      [now rewrite decide_True in Hrs by lia|
      case_decide as HrS;[subst; now replace (pos_to_nat_pred _) with O by lia|
        rewrite 2 lookup_cons_ne_0 by lia;
        etransitivity; [etransitivity; [|apply Hrs]|];
        f_equal; lia]]).
    + apply (Forall2_impl _ _ _ _ Hdelt).
      intros [l u] [l' u'] [Hl Hu].
      cbn in *.
      split; [destruct l as [r|], l' as [r'|]|
        destruct u as [r|], u' as [r'|]]; try easy;
      [revert Hl|revert Hu];
      (intros Hrs;
      destruct_decide (decide (r < sums \/ r' < sums)) as Hrsm;
      [now rewrite decide_True in Hrs by lia|
      case_decide as HrS;[subst; now replace (pos_to_nat_pred _) with O by lia|
        rewrite 2 lookup_cons_ne_0 by lia;
        etransitivity; [etransitivity; [|apply Hrs]|];
        f_equal; lia]]).
Qed.


Lemma tl_total_rel_semantics_aux_tl_times_aux' mabs ml mr mr'
  lsums labs ldelt rsums rabs rdelt :
  (* (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < length rsums + length mr')%nat -> *)
  tl_total_rel_semantics_aux mabs ml (mr' ++ mr) (lsums + rsums)
    ((relabel_abs (relabel_bounds (λ p,
      if decide (p < lsums)%nat then
        pos_add_N p (rsums)
      else pos_add_N p (length mr' + rsums))) <$> labs) ++
      (relabel_abs (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else
        if decide (p < rsums + length mr') then
          pos_add_N p (lsums)
        else
          pos_add_N p (lsums + length mr))) <$> rabs))
    ((relabel_delt (relabel_bounds (λ p,
      if decide (p < lsums)%nat then
        pos_add_N p (rsums)
      else pos_add_N p (length mr' + rsums))) <$> ldelt) ++
      (relabel_delt (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else
        if decide (p < rsums + length mr') then
          pos_add_N p (lsums)
        else
          pos_add_N p (lsums + length mr))) <$> rdelt)) <->
  tl_total_rel_semantics_aux mabs ml mr lsums labs ldelt /\
  tl_total_rel_semantics_aux mabs ml mr' rsums rabs rdelt.
Proof.
  (* intros Hrabs. *)
  revert mr; induction lsums as [|lsums IHlsums]; intros mr.
  - cbn [app length N.of_nat pos_add_N].
    change (if decide (_ < 0) then _ else ?x) with x.
    (* erewrite (list_fmap_ext _ _ rabs). 2:{
      intros; apply relabel_abs_id';
      intros; apply relabel_bounds_id';
      intros; apply decide_same.
    }
    erewrite (list_fmap_ext _ _ rdelt). 2:{
      intros; apply relabel_delt_id';
      intros; apply relabel_bounds_id';
      intros; apply decide_same.
    }
    rewrite 2 list_fmap_id.
    unfold N.of_nat at 4.
    cbn [pos_add_N].

    erewrite (list_fmap_ext _ _ labs). 2:{
      intros _ abs _.
      apply relabel_abs_ext.
      apply relabel_bounds_ext.
      intros r.
      rewrite decide_False by lia.
      reflexivity.
    } *)
    cbn.
    revert mr';
    induction rsums as [|rsums IHrsums]; intros mr'.
    2:{
      cbn.
      rewrite exists_and_l.
      apply exists_iff; intros x.
      rewrite <- (IHrsums (x :: mr')) by
        now cbn in Hrabs |- *; intros ? ?%Hrabs; lia.
      (* 2: cbn; intros ? ?%Hrabs; lia. *)
      cbn.
      f_equiv.
      f_equal.
      * apply list_fmap_ext; intros _ [[f low] up] _.
        apply relabel_abs_ext, relabel_bounds_ext.
        intros r; f_equal; lia.
      * apply list_fmap_ext; intros _ [[f low] up] _.
        apply relabel_abs_ext, relabel_bounds_ext.
        intros r; repeat case_decide; repeat first [lia | f_equal].
      * f_equal;
        apply list_fmap_ext; intros _ [l u] _;
        apply relabel_delt_ext;
        intros; apply relabel_bounds_ext;
        intros; f_equal; [lia|];
        repeat case_decide; lia.
    }
    cbn.
    rewrite rmul_comm_double.
    f_equiv.
    + rewrite fmap_app.
      rewrite Rlist_prod_app.
      f_equiv.
      * apply eq_reflexivity.
        f_equal.
        rewrite <- list_fmap_compose.
        apply list_fmap_ext; intros _ [[f low] up] _.
        cbn.
        apply abstract_rel_semantics_ext; [reflexivity|..];
        rewrite <- list_fmap_compose;
        apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2;
        (destruct v; [|reflexivity..]);
        cbn;
        rewrite lookup_app_r by lia;
        f_equal; lia.
      * apply Rlist_prod_perm_mor, SetoidPermutation.eqlistA_PermutationA,
          SetoidList.eqlistA_altdef.
        rewrite Forall2_fmap, Forall2_fmap_l.
        apply Forall_Forall2_diag.
        rewrite Forall_forall.
        intros [[f low] up] _.
        cbn.
        apply eq_reflexivity, abstract_rel_semantics_ext; [reflexivity|..];
        rewrite <- list_fmap_compose; apply list_fmap_ext;
          (intros _ [r|] _; [|reflexivity]);
        cbn;
        rewrite decide_False by easy;
        (case_decide as Hsm; [now rewrite lookup_app_l by lia|]);
        now rewrite 2 lookup_ge_None_2 by now rewrite ?length_app; lia.
    + rewrite fmap_app, Rlist_prod_app.
      f_equiv;
      apply Rlist_prod_perm_mor, SetoidPermutation.eqlistA_PermutationA,
          SetoidList.eqlistA_altdef;
      rewrite Forall2_fmap, Forall2_fmap_l;
      apply Forall_Forall2_diag;
      rewrite Forall_forall;
      intros [l u] _; cbn.
      * apply eq_reflexivity, delta_rel_semantics_ext;
        symmetry; unfold rget_var;
        (case_match; cbn; [|reflexivity];
        rewrite lookup_app_r; [f_equal|]; lia).
      * apply eq_reflexivity, delta_rel_semantics_ext;
        symmetry; unfold rget_var;
        (case_match; cbn; [|reflexivity]);
        rewrite decide_False by easy;
        (case_decide as Hsm; [now rewrite lookup_app_l by lia|]);
        now rewrite 2 lookup_ge_None_2 by now rewrite ?length_app; lia.
  - cbn.
    rewrite exists_and_r.
    apply exists_iff; intros x.
    rewrite <- IHlsums.
    apply tl_total_rel_semantics_aux_ext_mr.
    + apply Forall2_app; clear; apply Forall2_fmap, Forall_Forall2_diag;
      rewrite Forall_forall;
      intros [[f low] up] _; cbn;
      (split; [reflexivity|]);
      (eenough (Hen: _);
        [split; apply Forall2_fmap, Forall_Forall2_diag;
        rewrite Forall_forall; (intros [r|] _; [|reflexivity]);
        cbn; exact (Hen r)|]); intros r; cbn.
      * destruct_decide (decide (r < S lsums));
          [destruct_decide (decide (r < lsums))|
          rewrite (decide_False (P:=(r<_))) by lia];
        [rewrite decide_True by lia; done|rewrite decide_False by lia..];
        [|rewrite lookup_cons_ne_0, 2 lookup_app_r, lookup_cons_ne_0 by lia;
        f_equal; lia].
        replace (pos_to_nat_pred _) with O by lia.
        cbn.
        rewrite lookup_app_r by lia.
        replace (_-_) with O by lia.
        reflexivity.
      * destruct_decide (decide (r < rsums));
          [rewrite decide_True by lia; reflexivity|
          destruct_decide (decide (r < rsums + length mr'));
          rewrite decide_False by lia];
        [|rewrite lookup_cons_ne_0, 2 lookup_app_r, lookup_cons_ne_0 by lia;
        f_equal; lia].
        rewrite lookup_cons_ne_0, 2 lookup_app_l by lia.
        f_equal; lia.
    + apply Forall2_app; clear; apply Forall2_fmap, Forall_Forall2_diag;
      rewrite Forall_forall;
      intros [l u] _; cbn;
      (eenough (Hen : _);
      [split; [destruct l as [r|]; [|reflexivity]|
        destruct u as [r|]; [|reflexivity]]; cbn; exact (Hen r)|]);
      intros r.
      * destruct_decide (decide (r < S lsums));
          [destruct_decide (decide (r < lsums))|
          rewrite (decide_False (P:=(r<_))) by lia];
        [rewrite decide_True by lia; done|rewrite decide_False by lia..];
        [|rewrite lookup_cons_ne_0, 2 lookup_app_r, lookup_cons_ne_0 by lia;
        f_equal; lia].
        replace (pos_to_nat_pred _) with O by lia.
        cbn.
        rewrite lookup_app_r by lia.
        replace (_-_) with O by lia.
        reflexivity.
      * destruct_decide (decide (r < rsums));
          [rewrite decide_True by lia; reflexivity|
          destruct_decide (decide (r < rsums + length mr'));
          rewrite decide_False by lia];
        [|rewrite lookup_cons_ne_0, 2 lookup_app_r, lookup_cons_ne_0 by lia;
        f_equal; lia].
        rewrite lookup_cons_ne_0, 2 lookup_app_l by lia.
        f_equal; lia.
Qed.


Lemma tl_total_rel_semantics_aux_tl_times_aux_alt mabs ml mr
  lsums labs ldelt rsums rabs rdelt :
  (* (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < length rsums + length mr')%nat -> *)
  tl_total_rel_semantics_aux mabs ml mr (lsums + rsums)
    ((relabel_abs (relabel_bounds (λ p, pos_add_N p rsums)) <$> labs) ++
      (relabel_abs (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rabs))
    ((relabel_delt (relabel_bounds (λ p, pos_add_N p rsums)) <$> ldelt) ++
      (relabel_delt (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rdelt)) <->
  tl_total_rel_semantics_aux mabs ml mr lsums labs ldelt /\
  tl_total_rel_semantics_aux mabs ml mr rsums rabs rdelt.
Proof.
  rewrite <- tl_total_rel_semantics_aux_tl_times_aux'.
  apply tl_total_rel_semantics_aux_ext_mr.
  - apply Forall2_app; apply Forall2_fmap, Forall_Forall2_diag;
    rewrite Forall_forall; intros [[f low] up] _; cbn;
    (split; [reflexivity|]);
    (eenough (Hen : _);
    [split; (apply Forall2_fmap, Forall_Forall2_diag;
     rewrite Forall_forall; intros [r|] _; [|reflexivity];
     cbn; exact (Hen r))|]); intros r.
     + destruct_decide (decide (r < lsums));
      [now rewrite decide_True by lia|rewrite decide_False by lia].
      rewrite lookup_app_r by lia.
      f_equal; lia.
    + destruct_decide (decide (r < rsums)); [now rewrite decide_True by lia|].
      destruct_decide (decide (r < rsums + length mr));
      [now rewrite decide_False, lookup_app_l by lia|
      rewrite decide_False, lookup_app_r by lia; f_equal; lia].
  - apply Forall2_app; apply Forall2_fmap, Forall_Forall2_diag;
    rewrite Forall_forall; intros [l u] _; cbn;
    (eenough (Hen : _);
    [split; [destruct l as [r|];[|reflexivity]|
      destruct u as [r|];[|reflexivity]]; cbn; exact (Hen r)|]);
      intros r; cbn.
     + destruct_decide (decide (r < lsums));
      [now rewrite decide_True by lia|rewrite decide_False by lia].
      rewrite lookup_app_r by lia.
      f_equal; lia.
    + destruct_decide (decide (r < rsums)); [now rewrite decide_True by lia|].
      destruct_decide (decide (r < rsums + length mr));
      [now rewrite decide_False, lookup_app_l by lia|
      rewrite decide_False, lookup_app_r by lia; f_equal; lia].
Qed.


Lemma tl_total_rel_semantics_aux_tl_times mabs ml mr tl tl' :
  tl_total_rel_semantics_aux mabs ml mr
    (tl_times tl tl').(tl_sums) (tl_times tl tl').(tl_abstracts)
    (tl_times tl tl').(tl_deltas) <->
  tl_total_rel_semantics_aux mabs ml mr tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas) /\
  tl_total_rel_semantics_aux mabs ml mr tl'.(tl_sums) tl'.(tl_abstracts) tl'.(tl_deltas).
Proof.
  rewrite <- tl_total_rel_semantics_aux_tl_times_aux_alt.
  destruct tl, tl'; reflexivity.
Qed.


Lemma tensorlist_of_tensorexpr_correct_rel mabs ml te :
  tl_total_rel_semantics mabs ml (tensorlist_of_tensorexpr te) <->
  total_rel_semantics mabs ml te.
Proof.
  generalize (@nil A).
  induction te; intros mr.
  - cbn; tauto.
  - cbn; tauto.
  - cbn.
    tauto.
  - cbn.
    rewrite <- IHte1, <- IHte2.
    now rewrite tl_total_rel_semantics_aux_tl_times; f_equiv.
  - cbn.
    apply exists_iff; intros x.
    apply IHte.
Qed.



Section Treq.

Definition treq_at mabs mr : relation tensorexpr :=
  fun te1 te2 => forall ml,
  total_rel_semantics_aux mabs ml mr te1 <->
  total_rel_semantics_aux mabs ml mr te2.

Definition treq : relation tensorexpr :=
  fun te1 te2 => forall mabs mr, treq_at mabs mr te1 te2.

Local Notation "te1  '=tr[' mabs ','  mg ']='  te2" :=
  (treq_at mabs mg [] te1 te2) (at level 70).

Local Notation "te1  '=tr='  te2" :=
  (treq te1 te2) (at level 70).

Section Treq_at.

Context (mabs : abscontext) (mr : list A).

Local Notation treq_at := (treq_at mabs mr).

#[global]
Instance treq_treq_at_subrelation :
  subrelation treq treq_at.
Proof.
  easy.
Qed.

Lemma treq_at_refl : Reflexive treq_at.
Proof. easy. Qed.

Lemma treq_at_symm : Symmetric treq_at.
Proof. easy. Qed.

Lemma treq_at_trans : Transitive treq_at.
Proof.
  unfold treq, treq_at.
  firstorder.
Qed.

#[global]
Add Parametric Relation : tensorexpr treq_at
  reflexivity proved by treq_at_refl
  symmetry proved by treq_at_symm
  transitivity proved by treq_at_trans
  as treq_at_setoid.


#[global]
Add Parametric Morphism ml : (total_rel_semantics_aux mabs ml mr)
  with signature treq_at ==> iff as total_rel_semantics_at_mor.
Proof.
  unfold treq_at; auto.
Qed.


#[global]
Add Parametric Morphism : tproduct with signature
  treq_at ==> treq_at ==> treq_at as tproduct_at_mor.
Proof.
  intros l l' Hl r r' Hr vars.
  cbn.
  f_equiv; [apply Hl|apply Hr].
Qed.

End Treq_at.

Lemma tsum_at_ext mabs mr te te' :
  (forall x : A, treq_at mabs (x :: mr) te te') ->
  treq_at mabs mr (tsum te) (tsum te').
Proof.
  unfold treq_at.
  cbn.
  intros; apply exists_iff; auto.
Qed.

(* FIXME: Move *)
#[global]
Instance total_rel_semantics_aux_Params : Params total_rel_semantics_aux 3 := {}.

#[global]
Add Parametric Morphism : tsum with signature
  treq ==> treq as tsum_mor.
Proof.
  intros smd smd' Hsmd abs rels frees.
  cbn.
  now setoid_rewrite Hsmd.
Qed.



Lemma treq_refl : Reflexive treq.
Proof. easy. Qed.

Lemma treq_symm : Symmetric treq.
Proof. easy. Qed.

Lemma treq_trans : Transitive treq.
Proof.
  unfold treq, treq_at.
  hnf; naive_solver.
Qed.

#[global]
Add Parametric Relation : tensorexpr treq
  reflexivity proved by treq_refl
  symmetry proved by treq_symm
  transitivity proved by treq_trans
  as treq_setoid.

#[global]
Add Parametric Morphism : tproduct with signature
  treq ==> treq ==> treq as tproduct_mor.
Proof.
  intros l l' Hl r r' Hr abs rels frees.
  cbn.
  now rewrite Hl, Hr.
Qed.

Local Ltac cring :=
  intros abs rels frees; cbn; tauto.

Lemma tproduct_tone_l te : treq (tproduct tone te) te.
Proof.
  cring.
Qed.

Lemma tproduct_tone_r te : treq (tproduct te tone) te.
Proof.
  cring.
Qed.

Lemma tproduct_assoc te1 te2 te3 :
  treq (tproduct te1 (tproduct te2 te3))
  (tproduct (tproduct te1 te2) te3).
Proof.
  cring.
Qed.

Lemma tproduct_comm te1 te2 :
  treq (tproduct te1 te2)
    (tproduct te2 te1).
Proof.
  cring.
Qed.

Lemma tproducts_cons te tes :
  treq (tproducts (te :: tes)) (tproduct te (tproducts tes)).
Proof.
  destruct tes; [|reflexivity].
  cbn.
  now rewrite tproduct_tone_r.
Qed.

#[global]
Add Parametric Morphism : tproducts with signature
  Permutation ==> treq as tproducts_perm_mor.
Proof.
  intros tes tes' Hperm.
  induction Hperm; [reflexivity|..|etransitivity; eauto].
  - rewrite 2 tproducts_cons; now f_equiv.
  - rewrite !tproducts_cons.
    rewrite 2 tproduct_assoc.
    f_equiv.
    apply tproduct_comm.
Qed.


End Treq.




(* FIXME: Move *)
Notation tl_total_rel_semantics_aux' mabs ml mr tl :=
  (tl_total_rel_semantics_aux mabs ml mr tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).





(* TODO:
  (1) Add lemma about relabeling sum_of
  --(2) Add lemma rephrasing tl_total_rel_semantics using [∃ m : Vlist (reverse sums), _]
  (3) Put these together to prove the result connecting to tl_total_rel_semantics_alt *)



Lemma tl_total_rel_semantics_aux_alt_vec mabs ml mr sums abs delt :
  tl_total_rel_semantics_aux mabs ml mr sums abs delt <->
  exists m : vec A sums,
    tl_total_rel_semantics_aux mabs ml (rev_append m mr) O abs delt.
Proof.
  revert mr; induction sums; intros mr.
  - rewrite exists_vec_0; reflexivity.
  - cbn.
    setoid_rewrite IHsums.
    rewrite exists_vec_S.
    reflexivity.
Qed.

Lemma tl_total_rel_semantics_alt_vec mabs ml tl :
  tl_total_rel_semantics mabs ml tl <->
  exists m : vec A tl.(tl_sums),
    tl_total_rel_semantics_aux mabs ml m O tl.(tl_abstracts) tl.(tl_deltas).
Proof.
  rewrite tl_total_rel_semantics_aux_alt_vec.
  rewrite exists_vec_rev.
  f_equiv; intros mr.
  now rewrite vec_to_list_rev, rev_append_reverse, reverse_involutive, app_nil_r.
Qed.




Definition rget_var_alt (ml mr : varcontext) (v : var) : option A :=
  match v with
  | bound r => mr !! r
  | free l => ml !! l
  end.

Definition abstract_rel_semantics_alt (mabs : abscontext) ml mr
  (absidx : Idx) (lower : list var) (upper : list var) : Prop :=
  default False (largs ← join_list ((rget_var_alt ml mr) <$> lower);
      uargs ← join_list ((rget_var_alt ml mr) <$> upper);
      fval ← mabs !! absidx;
      Some (Vapplys_rel fval largs uargs)).

Notation abstract_rel_semantics_alt' mabs ml mr abs :=
  (abstract_rel_semantics_alt mabs ml mr abs.1.1 abs.1.2 abs.2).

Definition delta_rel_semantics_alt ml mr (l u : var) : Prop :=
  default False (la ← (rget_var_alt ml mr l);
      ua ← (rget_var_alt ml mr u);
      Some (id_rel 1 [#la] [#ua])).

Notation delta_rel_semantics_alt' ml mr delt :=
  (delta_rel_semantics_alt ml mr delt.1 delt.2).




Definition tl_total_rel_semantics_alt_aux mabs ml
  (tys : list Idx) abs delt : Prop :=
  ∃ mr : SVmap tys,
  Rlist_prod ((λ '(f, low, up),
    abstract_rel_semantics_alt mabs ml mr f low up) <$> abs) /\
  Rlist_prod ((λ '(l, u), delta_rel_semantics_alt ml mr l u) <$> delt).

Lemma tl_total_rel_semantics_alt_aux_unfold mabs ml tys abs delt :
  tl_total_rel_semantics_alt_aux mabs ml tys abs delt <->
  ∃ mr : SVmap tys,
  Rlist_prod ((λ flu,
    abstract_rel_semantics_alt' mabs ml mr flu) <$> abs) /\
  Rlist_prod ((λ lu, delta_rel_semantics_alt' ml mr lu) <$> delt).
Proof.
  apply exists_iff.
  intros m.
  f_equiv.
  - f_equiv.
    apply eqlistA_PermutationA, eqlistA_altdef, Forall2_fmap, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [[]] _;
    done.
  - f_equiv.
    apply eqlistA_PermutationA, eqlistA_altdef, Forall2_fmap, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [];
    done.
Qed.


Lemma tl_total_rel_semantics_alt_aux_correct_rel mabs ml sums abs delt :
  tl_total_rel_semantics_aux mabs ml [] sums abs delt <->
  tl_total_rel_semantics_alt_aux mabs ml
    (* (list_to_map (imap (λ i v, (pos_add_N (Pos.of_succ_nat i) (lengthN sums), v)) (reverse mr))) *)
    (pseq 1 sums)
    abs delt.
Proof.
  rewrite tl_total_rel_semantics_aux_alt_vec.
  change (rev_append ?x []) with (reverse x).
  unfold tl_total_rel_semantics_alt_aux.
  unfold SVmap, SVmap_map.
  set (f:=(λ b, Rlist_prod ((λ '(y, up),
        let '(f, low) := y in abstract_rel_semantics_alt mabs ml b f low up) <$>
     abs)
  ∧ Rlist_prod ((λ '(l, u), delta_rel_semantics_alt ml b l u) <$> delt))).
  erewrite (exists_iff (A:=dsig _) _
  (λ a, f (`a))) by done.
  rewrite exists_dsig.
  subst f.
  split.
  - intros (m & Hm).
    exists (list_to_map (imap (fun i v => ((Pos.of_succ_nat i), v)) (reverse m))).
    split. 1:{
      hnf.
      rewrite dom_list_to_map_L.
      rewrite fmap_imap; unfold compose.
      cbn.
      rewrite imap_seq_0.
      rewrite pseq_to_seq.
      rewrite length_reverse, length_vec_to_list.
      rewrite Nat2N.id.
      done.
    }
    destruct Hm as [Habs Hdelt].
    split; (refine (proj1 (_ : _ <-> _) _)); [|exact Habs| |exact Hdelt];
    f_equiv;
    apply eqlistA_PermutationA, eqlistA_altdef, Forall2_fmap, Forall_Forall2_diag;
    rewrite Forall_forall.
    + intros [[]] _.
      unfold abstract_rel_semantics, abstract_rel_semantics_alt.
      apply default_Proper; [done|].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        f_equiv.
        apply list_fmap_ext.
        intros _ [rel|loc] _; [|done].
        cbn.
        rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
        done.
      }
      intros largs _ [= <-].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        f_equiv.
        apply list_fmap_ext.
        intros _ [rel|loc] _; [|done].
        cbn.
        rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
        done.
      }
      intros rargs _ [= <-].
      apply (@option_bind_proper _ eq), option_Forall2_refl, _.
      intros idx _ [= <-].
      constructor.
      done.
    + intros [a b] _.
      unfold delta_rel_semantics, delta_rel_semantics_alt.
      apply default_Proper; [done|].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        apply eq_reflexivity.
        destruct a as [rel|loc]; [|done].
        cbn.
        rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
        done.
      }
      intros la _ [= <-].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        apply eq_reflexivity.
        destruct b as [rel|loc]; [|done].
        cbn.
        rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
        done.
      }
      intros ub _ [= <-].
      constructor.
      done.
  - intros (m & Hm & Habs & Hdelt).
    assert (Hmi : forall (i : nat), i < sums ->
      is_Some (m !! (Pos.of_succ_nat (sums - S i)))). 1:{
      intros i Hi.
      apply elem_of_dom.
      rewrite Hm.
      apply elem_of_list_to_set.
      apply elem_of_pseq_1.
      lia.
    }
    exists (fun_to_vec (λ i, is_Some_proj (Hmi i (fin_to_nat_lt i)))).
    split; (refine (proj1 (_ : _ <-> _) _)); [|exact Habs| |exact Hdelt];
    f_equiv;
    apply eqlistA_PermutationA, eqlistA_altdef, Forall2_fmap, Forall_Forall2_diag;
    rewrite Forall_forall.
    + intros [[]] _.
      unfold abstract_rel_semantics, abstract_rel_semantics_alt.
      apply default_Proper; [done|].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        f_equiv.
        apply list_fmap_ext.
        intros _ [rel|loc] _; [|done].
        cbn.
        assert (Hmrel : is_Some (m !! rel) <-> rel < Pos.of_succ_nat sums) by
          (rewrite <- elem_of_dom, Hm, elem_of_list_to_set, elem_of_pseq_1; lia).
        symmetry.
        destruct (m !! rel) as [a|] eqn:Hmreleq.
        - apply proj1 in Hmrel.
          tspecialize Hmrel by done.
          apply reverse_lookup_Some.
          rewrite length_vec_to_list.
          split; [|lia].
          rewrite lookup_vec_to_list.
          case_guard; [|lia].
          cbn.
          f_equal.
          rewrite lookup_fun_to_vec.
          unfold is_Some_proj.
          remember (Hmi _ _) as Hmi' eqn:HHmi'; clear HHmi'.
          revert Hmi'.
          rewrite fin_to_nat_to_fin.
          replace (_ - _) with (pos_to_nat_pred rel) by lia.
          rewrite pos_to_nat_pred_to_pos.
          rewrite Hmreleq.
          done.
        - apply lookup_ge_None_2.
          rewrite length_reverse, length_vec_to_list.
          specialize (fun p => is_Some_None (Hmrel.2 p)) as Hnlt.
          lia.
      }
      intros largs _ [= <-].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        f_equiv.
        apply list_fmap_ext.
        intros _ [rel|loc] _; [|done].
        cbn.
        assert (Hmrel : is_Some (m !! rel) <-> rel < Pos.of_succ_nat sums) by
          (rewrite <- elem_of_dom, Hm, elem_of_list_to_set, elem_of_pseq_1; lia).
        symmetry.
        destruct (m !! rel) as [a|] eqn:Hmreleq.
        - apply proj1 in Hmrel.
          tspecialize Hmrel by done.
          apply reverse_lookup_Some.
          rewrite length_vec_to_list.
          split; [|lia].
          rewrite lookup_vec_to_list.
          case_guard; [|lia].
          cbn.
          f_equal.
          rewrite lookup_fun_to_vec.
          unfold is_Some_proj.
          remember (Hmi _ _) as Hmi' eqn:HHmi'; clear HHmi'.
          revert Hmi'.
          rewrite fin_to_nat_to_fin.
          replace (_ - _) with (pos_to_nat_pred rel) by lia.
          rewrite pos_to_nat_pred_to_pos.
          rewrite Hmreleq.
          done.
        - apply lookup_ge_None_2.
          rewrite length_reverse, length_vec_to_list.
          specialize (fun p => is_Some_None (Hmrel.2 p)) as Hnlt.
          lia.
      }
      intros rargs _ [= <-].
      apply (@option_bind_proper _ eq), option_Forall2_refl, _.
      intros idx _ [= <-].
      constructor.
      done.
    + intros [a b] _.
      unfold delta_rel_semantics, delta_rel_semantics_alt.
      apply default_Proper; [done|].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        destruct a as [rel|loc]; [|done].
        cbn.
        apply eq_reflexivity.
        assert (Hmrel : is_Some (m !! rel) <-> rel < Pos.of_succ_nat sums) by
          (rewrite <- elem_of_dom, Hm, elem_of_list_to_set, elem_of_pseq_1; lia).
        symmetry.
        destruct (m !! rel) as [a|] eqn:Hmreleq.
        - apply proj1 in Hmrel.
          tspecialize Hmrel by done.
          apply reverse_lookup_Some.
          rewrite length_vec_to_list.
          split; [|lia].
          rewrite lookup_vec_to_list.
          case_guard; [|lia].
          cbn.
          f_equal.
          rewrite lookup_fun_to_vec.
          unfold is_Some_proj.
          remember (Hmi _ _) as Hmi' eqn:HHmi'; clear HHmi'.
          revert Hmi'.
          rewrite fin_to_nat_to_fin.
          replace (_ - _) with (pos_to_nat_pred rel) by lia.
          rewrite pos_to_nat_pred_to_pos.
          rewrite Hmreleq.
          done.
        - apply lookup_ge_None_2.
          rewrite length_reverse, length_vec_to_list.
          specialize (fun p => is_Some_None (Hmrel.2 p)) as Hnlt.
          lia.
      }
      intros la _ [= <-].
      apply (@option_bind_proper _ eq).
      2:{
        hnf.
        destruct b as [rel|loc]; [|done].
        cbn.
        apply eq_reflexivity.
        assert (Hmrel : is_Some (m !! rel) <-> rel < Pos.of_succ_nat sums) by
          (rewrite <- elem_of_dom, Hm, elem_of_list_to_set, elem_of_pseq_1; lia).
        symmetry.
        destruct (m !! rel) as [b|] eqn:Hmreleq.
        - apply proj1 in Hmrel.
          tspecialize Hmrel by done.
          apply reverse_lookup_Some.
          rewrite length_vec_to_list.
          split; [|lia].
          rewrite lookup_vec_to_list.
          case_guard; [|lia].
          cbn.
          f_equal.
          rewrite lookup_fun_to_vec.
          unfold is_Some_proj.
          remember (Hmi _ _) as Hmi' eqn:HHmi'; clear HHmi'.
          revert Hmi'.
          rewrite fin_to_nat_to_fin.
          replace (_ - _) with (pos_to_nat_pred rel) by lia.
          rewrite pos_to_nat_pred_to_pos.
          rewrite Hmreleq.
          done.
        - apply lookup_ge_None_2.
          rewrite length_reverse, length_vec_to_list.
          specialize (fun p => is_Some_None (Hmrel.2 p)) as Hnlt.
          lia.
      }
      intros ub _ [= <-].
      constructor.
      done.
Qed.







Lemma abstract_rel_semantics_alt_ext mabs ml mr mabs' ml' mr'
  idx lower upper idx' lower' upper' :
  mabs !! idx = mabs' !! idx' ->
  (rget_var_alt ml mr) <$> lower = (rget_var_alt ml' mr') <$> lower' ->
  (rget_var_alt ml mr) <$> upper = (rget_var_alt ml' mr') <$> upper' ->
  abstract_rel_semantics_alt mabs ml mr idx lower upper =
  abstract_rel_semantics_alt mabs' ml' mr' idx' lower' upper'.
Proof.
  intros Hidx Hl Hu.
  unfold abstract_rel_semantics_alt.
  now rewrite Hidx, Hl, Hu.
Qed.

Lemma delta_rel_semantics_alt_ext ml mr ml' mr'
  l u l' u' :
  (rget_var_alt ml mr) l = (rget_var_alt ml' mr') l' ->
  (rget_var_alt ml mr) u = (rget_var_alt ml' mr') u' ->
  delta_rel_semantics_alt ml mr l u =
  delta_rel_semantics_alt ml' mr' l' u'.
Proof.
  intros Hl Hu.
  unfold delta_rel_semantics_alt.
  now rewrite Hl, Hu.
Qed.






Lemma tl_total_rel_semantics_alt_aux_relabel mabs ml mr (f : Idx -> Idx)
  {Hf : Inj eq eq f} abs delt :
  tl_total_rel_semantics_alt_aux mabs ml mr abs delt <->
  tl_total_rel_semantics_alt_aux mabs ml (f <$> mr)
    (relabel_abs (relabel_bounds f) <$> abs)
    (relabel_delt (relabel_bounds f) <$> delt).
Proof.
  unfold tl_total_rel_semantics_alt_aux.
  unshelve (eapply (exists_relabel'_l2r (kmap_SVmap f) _ _
    (RA:=eq) (RB:=eq))); [apply _..|].
  intros [m Hm].
  cbn.
  apply bool_decide_spec in Hm.
  f_equiv.
  - apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r; unfold compose.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros ((fidx, low), up) _.
    cbn.
    apply eq_reflexivity, abstract_rel_semantics_alt_ext; [reflexivity|..];
    rewrite <- list_fmap_compose;
    apply list_fmap_ext; (intros _ [r|] _; [|reflexivity]);
    cbn;
    now rewrite (lookup_kmap _).
  - apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r; unfold compose.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros (l, u) _.
    cbn.
    apply eq_reflexivity, delta_rel_semantics_alt_ext;
    [destruct l as [r|]|destruct u as [r|]]; try reflexivity;
    cbn;
    now rewrite (lookup_kmap _).
Qed.


Lemma tl_aeq_correct_rel mabs ml tl tl' :
  tl =tl= tl' ->
  tl_total_rel_semantics mabs ml tl <->
  tl_total_rel_semantics mabs ml tl'.
Proof.
  intros (f & Hf & Htypes & Habs & Hdelt).
  rewrite 2 tl_total_rel_semantics_alt_aux_correct_rel.

  rewrite <- Htypes.
  unfold tl_total_rel_semantics_alt_aux.
  set (p:=Pos.of_succ_nat tl.(tl_sums)) in *.
  assert (Hfinj : Inj (=) (=) (make_pwf p f)) by now apply make_pwf_inj.
  assert (Hperm: make_pwf p f <$> pseq 1 (tl_sums tl) ≡ₚ pseq 1 (tl_sums tl)). 1:{
    hnf in Hf.
    unfold p in Hf.
    replace (Pos.pred_N _) with (N.of_nat (tl_sums tl)) in Hf by lia.
    rewrite <- Hf at 2.
    apply eq_reflexivity.
    apply list_fmap_ext.
    intros _ q Hq%elem_of_list_lookup_2%elem_of_pseq_1.
    unfold make_pwf.
    case_decide; [lia|done].
  }
  apply (exists_relabel'_r2l (SVmap_castP Hperm ∘ kmap_SVmap (make_pwf p f)) _ _
    (RA:=eq) (RB:=eq)); [apply _..|].
  intros [m Hm].
  cbn.
  apply bool_decide_spec in Hm.
  f_equiv.
  - erewrite Rlist_prod_perm by now rewrite Habs.
    apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, Forall2_fmap.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [[idx low] up] _.
    cbn.
    apply eq_reflexivity, abstract_rel_semantics_alt_ext; [reflexivity|..];
      rewrite <- list_fmap_compose; apply list_fmap_ext;
        (intros _ [r|] _; [|reflexivity]; cbn -[make_pwf];
        apply (lookup_kmap _)).
  - erewrite Rlist_prod_perm by now rewrite Hdelt.
    apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, Forall2_fmap.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [l u] _.
    cbn.
    apply eq_reflexivity, delta_rel_semantics_alt_ext;
    [destruct l as [r|]; [|reflexivity]|destruct u as [r|]; [|reflexivity]];
    cbn -[make_pwf]; apply (lookup_kmap _).
Qed.




Definition abstracts_rel_semantics mabs ml mr abs :=
  Rlist_prod ((λ '(f, low, up), abstract_rel_semantics mabs ml mr f low up)
    <$> abs).

Definition abstracts_rel_semantics_alt mabs ml mr abs :=
  Rlist_prod ((λ '(f, low, up), abstract_rel_semantics_alt mabs ml mr f low up)
    <$> abs).

Definition deltas_rel_semantics ml mr delt :=
  Rlist_prod ((λ '(l, u), delta_rel_semantics ml mr l u)
    <$> delt).

Definition deltas_rel_semantics_alt ml mr delt :=
  Rlist_prod ((λ '(l, u), delta_rel_semantics_alt ml mr l u)
    <$> delt).

Definition ntl_total_rel_semantics mabs ml ntl :=
  tl_total_rel_semantics mabs ml (ntl2tl ntl).

Lemma tl_total_rel_semantics_alt_aux_eq mabs ml mr abs delt :
  tl_total_rel_semantics_alt_aux mabs ml mr abs delt =
  ∃ mr : SVmap mr,
    abstracts_rel_semantics_alt mabs ml mr abs /\
    deltas_rel_semantics_alt ml mr delt.
Proof.
  reflexivity.
Qed.

Lemma ntl_total_rel_semantics_alt mabs ml ntl :
  WF_ntl ntl ->
  ntl_total_rel_semantics mabs ml ntl <->
  ∃ mr : SVmap ntl.(ntl_sums),
  abstracts_rel_semantics_alt mabs ml mr ntl.(ntl_abstracts) /\
  deltas_rel_semantics_alt ml mr ntl.(ntl_deltas).
Proof.
  intros Hwf.
  unfold ntl_total_rel_semantics.
  unfold tl_total_rel_semantics.
  rewrite tl_total_rel_semantics_alt_aux_correct_rel.
  destruct ntl as [isums abs delt]; cbn -[reverse abstracts_rel_semantics_alt].
  specialize (partial_injection_extension (pseq 1 (lengthP isums))
    (fun p => default p (isums !! (p:>nat)))) as Hinj.
  pose proof (lengthN_correct isums).
  tspecialize Hinj. 1:{
    intros a b Ha%elem_of_list_In%elem_of_pseq_1
      Hb%elem_of_list_In%elem_of_pseq_1.
    (* rewrite 2 list_lookup_fmap. *)
    destruct (isums !! (a:>nat)) as [ia|] eqn:Hia;
      [|apply lookup_ge_None_1 in Hia; lia].
    destruct (isums !! (b:>nat)) as [ib|] eqn:Hib;
      [|apply lookup_ge_None_1 in Hib; lia].
    cbn.
    intros ->.
    apply pos_to_nat_pred_inj.
    revert Hia Hib.
    apply NoDup_lookup, Hwf.
  }
  destruct Hinj as (g & Hginj & Hgeq).
  rewrite Forall_forall in Hgeq.
  setoid_rewrite elem_of_pseq_1 in Hgeq.

  rewrite (tl_total_rel_semantics_alt_aux_relabel _ _ _ g).
  replace (_ <$> _) with isums. 2:{

    apply (fun H => list_eq_same_length _ _ _ H eq_refl);
      [now rewrite length_fmap, length_pseq; lia|].
    intros i x y Hi.
    rewrite list_lookup_fmap, lookup_pseq_1_lt by lia.
    cbn.
    rewrite Hgeq by lia.
    rewrite pos_to_nat_pred_of_nat.
    intros Hisi.
    rewrite Hisi.
    cbn.
    congruence.
  }
  replace (_ <$> _) with abs. 2:{
    symmetry.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros flu Hflu.
    cbn.
    rewrite relabel_abs_compose.
    apply relabel_abs_id_strong; intros [r|] Hr; [|done..].
    cbn.
    specialize (Hwf.2.1 r) as Hr'.
    tspecialize Hr' by now apply elem_of_abstracts_bound_vars;
      destruct flu as [[f l] u]; eauto.
    rewrite elem_of_list_to_set in Hr'.
    cbn in Hr'.
    (* apply elem_of_list_fmap in Hr' as ((_, ty) & [= <-] & Hr'). *)
    apply elem_of_list_lookup in Hr' as Hi.
    destruct Hi as [i Hi].
    replace (list_to_map _ !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_to_fmap, list_fmap_id; apply Hwf.
      - apply elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    rewrite Hgeq by (apply lookup_lt_Some in Hi; lia).
    rewrite pos_to_nat_pred_of_nat, Hi.
    reflexivity.
  }
  replace (_ <$> _) with delt. 2:{
    symmetry.
    rewrite <- list_fmap_compose.
    apply list_fmap_id'; intros lu Hlu.
    cbn.
    rewrite relabel_delt_compose.
    apply relabel_delt_id_strong; intros [r|] Hr; [|done..].
    cbn.
    specialize (Hwf.2.2 r) as Hr'.
    tspecialize Hr' by now apply elem_of_deltas_bound_vars;
      destruct lu as [l u]; naive_solver.
    rewrite elem_of_list_to_set in Hr'.
    cbn in Hr'.
    (* apply elem_of_list_fmap in Hr' as ((_, ty) & [= <-] & Hr'). *)
    apply elem_of_list_lookup in Hr' as Hi.
    destruct Hi as [i Hi].
    replace (list_to_map _ !! r) with (Some (Pos.of_succ_nat i)). 2:{
      symmetry.
      apply elem_of_list_to_map.
      - rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_to_fmap, list_fmap_id; apply Hwf.
      - apply elem_of_lookup_imap.
        exists i, r.
        easy.
    }
    cbn.
    rewrite Hgeq by (apply lookup_lt_Some in Hi; lia).
    rewrite pos_to_nat_pred_of_nat, Hi.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma tl2ntl_correct_rel mabs ml tl :
  WF_tl tl ->
  ntl_total_rel_semantics mabs ml (tl2ntl tl) <->
  tl_total_rel_semantics mabs ml tl.
Proof.
  intros Hwf.
  rewrite ntl_total_rel_semantics_alt by now apply tl2ntl_WF.
  unfold tl_total_rel_semantics.
  rewrite tl_total_rel_semantics_alt_aux_correct_rel.
  now destruct tl.
Qed.

Lemma ntl2tl_correct_rel mabs ml ntl :
  tl_total_rel_semantics mabs ml (ntl2tl ntl) <->
  ntl_total_rel_semantics mabs ml ntl.
Proof.
  reflexivity.
Qed.



Lemma ntl_aeq_correct_rel mabs ml ntl ntl' :
  WF_ntl ntl ->
  ntl =ntl= ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros Hntl Heq.
  apply ntl_aeq_WF in Heq as Hntl'; [|easy].
  unfold ntl_total_rel_semantics.
  apply tl_aeq_correct_rel.
  now apply ntl2tl_aeq.
Qed.

Lemma ntl_delta_idemp_correct_rel mabs ml ntl ntl' v :
  WT_ntl (dom ml) ntl -> WT_ntl (dom ml) ntl' ->
  ntl_delta_idemp v ntl ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros HWT HWT' Hidemp.
  hnf in Hidemp.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn -[ntl2tl] in *.
  rewrite 2 ntl_total_rel_semantics_alt by first [apply HWT|apply HWT'].
  cbn [ntl_sums ntl_abstracts ntl_deltas].
  destruct Hidemp as (<- & -> & ->).
  apply exists_iff; intros [mr Hmr].
  cbn.
  apply bool_decide_spec in Hmr.
  cbn [deltas_rel_semantics_alt fmap list_fmap Rlist_prod].
  enough (delta_rel_semantics_alt ml mr v v <-> True) as Heq
    by now unfold deltas_rel_semantics_alt; tauto.
  destruct v as [r|l].
  - cbn.
    assert (Hr : r ∈ dom mr). 1:{
      rewrite Hmr.
      apply HWT'.2.2.2.2.
      set_solver +.
    }
    unfold SVmap in *.
    apply elem_of_dom in Hr as [a Ha].
    rewrite Ha.
    cbn.
    done.
  - cbn.
    assert (Hl : l ∈ dom ml). 1:{
      apply HWT'.2.1.
      set_solver +.
    }
    unfold SVmap in *.
    apply elem_of_dom in Hl as [a Ha].
    rewrite Ha.
    cbn.
    done.
Qed.

(* Lemma SVmap_elements_cons_alt ty tys :
  SVmap_elements ty tys  *)


Lemma deltas_rel_semantics_alt_cons ml mr lu delt :
  deltas_rel_semantics_alt ml mr (lu :: delt) =
  (delta_rel_semantics_alt ml mr lu.1 lu.2 /\
  deltas_rel_semantics_alt ml mr delt).
Proof.
  now destruct lu.
Qed.




Lemma abstracts_rel_semantics_alt_ext mabs ml mr mabs' ml' mr'
  abs abs' :
  Forall2 (fun '(idx, lower, upper) '(idx', lower', upper') =>
    mabs !! idx = mabs' !! idx' /\
  (rget_var_alt ml mr) <$> lower = (rget_var_alt ml' mr') <$> lower' /\
  (rget_var_alt ml mr) <$> upper = (rget_var_alt ml' mr') <$> upper') abs abs' ->
  abstracts_rel_semantics_alt mabs ml mr abs =
  abstracts_rel_semantics_alt mabs' ml' mr' abs'.
Proof.
  intros Hall2.
  unfold abstracts_rel_semantics_alt.
  f_equal.
  apply list_eq_Forall2, Forall2_fmap.
  apply (Forall2_impl _ _ _ _ Hall2).
  intros [[f low] up] [[f' low'] up'].
  intros (?&?&?); now apply abstract_rel_semantics_alt_ext.
Qed.

Lemma deltas_rel_semantics_alt_ext ml mr ml' mr' delt delt' :
  Forall2 (fun '(l, u) '(l', u') =>
  (rget_var_alt ml mr) l = (rget_var_alt ml' mr') l' /\
  (rget_var_alt ml mr) u = (rget_var_alt ml' mr') u') delt delt' ->
  deltas_rel_semantics_alt ml mr delt =
  deltas_rel_semantics_alt ml' mr' delt'.
Proof.
  intros Hall2.
  unfold deltas_rel_semantics_alt.
  f_equal.
  apply list_eq_Forall2, Forall2_fmap.
  apply (Forall2_impl _ _ _ _ Hall2).
  intros [l u] [l' u'].
  intros (?&?); now apply delta_rel_semantics_alt_ext.
Qed.

Lemma ntl_delta_subst_correct_rel mabs ml ntl ntl' lb r :
  WT_ntl (dom ml) ntl -> WT_ntl (dom ml) ntl' ->
  ntl_delta_subst lb r ntl ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros Hwt Hwt' Hsubst.
  hnf in Hsubst.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct delt as [|lu delt]; [easy|].
  cbn [head tail] in Hsubst.
  pose proof Hsubst as (Hne & Hsums & Habs & [= ->] & Hdelt).
  subst abs' delt'.
  assert (Heq : ntl_aeq {|
    ntl_sums := sums;
    ntl_abstracts := abs;
    ntl_deltas := (bound lb, r) :: delt
  |} {|
    ntl_sums := lb :: sums';
    ntl_abstracts := abs;
    ntl_deltas := (bound lb, r) :: delt
  |}) by now eapply (ntl_aeq_of_perm _ (mk_ntl _ _ _));
    [apply Hsums|cbn; reflexivity..].

  etransitivity; [apply ntl_aeq_correct_rel; [apply Hwt|apply Heq]|].

  rewrite ntl_total_rel_semantics_alt by now
    apply (ntl_aeq_WF _ _ Heq), Hwt.
  rewrite ntl_total_rel_semantics_alt by apply Hwt'.
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  rewrite exists_SVmap_cons.
  apply exists_iff; intros [mr' Hmr'].
  cbn -[deltas_rel_semantics_alt abstracts_rel_semantics_alt].
  apply bool_decide_unpack in Hmr'.
  assert (Hr : exists ar, rget_var_alt ml mr' r = Some ar). 1:{
    destruct r as [r|l].
    - cbn.
      assert (r ∈ dom mr') as Hdom.
      + rewrite Hmr'.
        pose proof Hwt.2.2.2.2 as Hr.
        cbn -[union] in Hr.
        assert (Hr' : r ∈ list_to_set sums)
          by (now apply Hr, elem_of_union_r, elem_of_union_l, elem_of_singleton).
        rewrite Hsums in Hr'.
        set_solver +Hr' Hne.
      + unfold SVmap in Hdom.
        apply elem_of_dom in Hdom as [ar Har].
        eauto.
    - cbn.
      assert (l ∈ dom ml) as Hdom.
      + apply Hwt.2.1.
        set_solver +.
      + apply elem_of_dom in Hdom as [ar Har].
        eauto.
  }
  assert (Hgetr : forall a, rget_var_alt ml (<[lb:=a]> mr') r =
    rget_var_alt ml mr' r). 1:{
    intros a.
    destruct r as [r|]; [|easy].
    cbn.
    unfold SVmap.
    apply lookup_insert_ne; congruence.
  }
  destruct Hr as (ar & Har).
  erewrite (exists_iff _ (fun a => a = ar /\
    (abstracts_rel_semantics_alt mabs ml (<[lb:=a]> mr') abs /\
    deltas_rel_semantics_alt ml (<[lb:=a]> mr') delt))). 2:{
    intros a.
    rewrite deltas_rel_semantics_alt_cons.
    unfold delta_rel_semantics_alt.
    cbn [fst snd rget_var_alt].
    unfold SVmap.
    rewrite lookup_insert.
    cbn [mbind option_bind from_option id].
    rewrite Hgetr, Har.
    cbn.
    unfold id_rel.
    unshelve (erewrite (inj_iff (R:=eq) (λ a, [#a]) (Inj0:=_));
      tauto).
    refine (cancel_inj (f:=vhd)).
    done.
  }
  rewrite exists_eq_l_iff.
  cbn.
  f_equiv.
  - apply eq_reflexivity.
    unfold SVmap.
    apply abstracts_rel_semantics_alt_ext, Forall2_fmap_r, Forall_Forall2_diag.
    rewrite Forall_forall; intros [[f low] up] Hflu.
    cbn.
    split; [easy|].
    split;
    rewrite <- list_fmap_compose; apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2;
    (destruct v as [vr|vl]; [|reflexivity]);
    cbn;
    rewrite lookup_insert_case, fn_lookup_singleton_case;
    now case_decide as Hvr_lb;
    [rewrite decide_True by congruence|rewrite decide_False by congruence].
  - apply eq_reflexivity, deltas_rel_semantics_alt_ext, Forall2_fmap_r, Forall_Forall2_diag.
    rewrite Forall_forall; intros [l u] Hlu.
    cbn.
    unfold SVmap.
    split;
    [rename l into v|rename u into v];
    (destruct v as [vr|vl]; [|reflexivity]);
    cbn;
    rewrite lookup_insert_case, fn_lookup_singleton_case;
    now case_decide as Hvr_lb;
    [rewrite decide_True by congruence|rewrite decide_False by congruence].
Qed.


Lemma delta_rel_semantics_alt_comm ml mr v v' :
  delta_rel_semantics_alt ml mr v v' <->
  delta_rel_semantics_alt ml mr v' v.
Proof.
  unfold delta_rel_semantics_alt.
  destruct (rget_var_alt ml mr v), (rget_var_alt ml mr v'); [|done..].
  cbn.
  apply symmetry_iff, _.
Qed.

Lemma ntl_delta_perm_eq_correct_rel mabs ml ntl ntl' :
  WF_ntl ntl -> WF_ntl ntl' ->
  ntl_delta_perm_eq ntl ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros HWF HWF' Heq.
  rewrite 2 ntl_total_rel_semantics_alt by easy.
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct Heq as (<- & <- & Hdelt).
  apply exists_iff; intros [mr Hmr].
  cbn.
  apply bool_decide_unpack in Hmr.
  f_equiv.
  unfold deltas_rel_semantics_alt.
  apply Rlist_prod_perm_mor.
  clear HWF HWF'.
  induction Hdelt as [|? ? ? ? Heq | |].
  - done.
  - cbn.
    f_equiv; [|easy].
    do 2 case_match.
    rewrite prod_swap_eq_pair in Heq.
    destruct Heq as [[-> ->]|[-> ->]]; [done|].
    apply delta_rel_semantics_alt_comm.
  - apply (Permutation_PermutationA _).
    solve_Permutation.
  - now etransitivity; eassumption.
Qed.





Lemma ntl_delta_eq_correct_rel mabs ml ntl ntl' :
  WT_ntl (dom ml) ntl ->
  ntl_delta_eq (dom ml) ntl ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros HWF Heq.
  assert (HWF' : WT_ntl (dom ml) ntl') by now
    eapply ntl_delta_eq_WT; eauto.
  induction Heq.
  - eapply ntl_delta_idemp_correct_rel; eauto.
  - eapply ntl_delta_subst_correct_rel; eauto.
  - eapply ntl_delta_perm_eq_correct_rel; solve [eauto|apply HWF|apply HWF'].
  - symmetry; eauto.
  - assert (WT_ntl (dom ml) ntl') by now eapply ntl_delta_eq_WT; eauto.
    etransitivity; [apply IHHeq1|apply IHHeq2]; easy.
Qed.



Lemma ntl_eq_correct_rel mabs ml ntl ntl' :
  WT_ntl (dom ml) ntl -> (* WT_ntl (dom ml) ntl' -> *)
  ntl_eq (dom ml) ntl ntl' ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml ntl'.
Proof.
  intros HWF Heq.
  induction Heq as [|ntl ntl' ntl'' Hntl Hrtc IHntl]; [done|].
  hnf in Hntl.
  assert (Hntl' : WT_ntl (dom ml) ntl'). 1:{
    destruct Hntl as [Hntl|Hntl];
    [eapply ntl_aeq_WT|eapply ntl_delta_eq_WT];
    eauto; now symmetry.
  }
  etransitivity; [|apply IHntl; easy].
  destruct Hntl as [Hntl|Hntl].
  - apply ntl_aeq_correct_rel; easy + apply HWF.
  - apply ntl_delta_eq_correct_rel; easy.
Qed.


Lemma abstract_rel_semantics_alt_ext_tens (mabs : Pmap DimensionlessRel)
   ml mr mabs'
  idx idx' lower upper :
  mabs !! idx ≡ mabs' !! idx' ->
  abstract_rel_semantics_alt mabs ml mr idx lower upper <->
  abstract_rel_semantics_alt mabs' ml mr idx' lower upper.
Proof.
  intros Hidx.
  unfold abstract_rel_semantics_alt.
  induction Hidx as [dt dt' Hdt|]; [|cbn; now rewrite !option_bind_None_r].
  cbn.
  destruct (join_list (_ <$> lower)) as [largs|] eqn:Hlargs; [cbn|done].
  destruct (join_list (_ <$> upper)) as [uargs|] eqn:Huargs; [cbn|done].
  apply Hdt.
Qed.

(* Fixpoint join_vec {A n} (v : vec (option A) n) : option (vec A n) :=
  match v in vec _ n return option (vec A n) with
  | [#] => Some [#]
  | ma ::: mv =>
    ma ≫= λ a, join_vec mv ≫= λ v, Some (a ::: v)
  end.

Lemma vec_to_list_join `{A : Type} {n} (v : vec (option A) n) :
  vec_to_list <$> join_vec v = join_list v.
Proof. *)

(* rel_semantics of a tensorexpr as a (dimensioned) tensor, based on
  vectors of input and output vertices *)
Definition tensorexpr_to_rel (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (te : tensorexpr) : @Rel A n m :=
  fun ins outs =>
    total_rel_semantics mabs (make_vecs_map inputs outputs ins outs) te.


Definition tensorlist_to_rel (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (tl : tensorlist) : @Rel A n m :=
  fun ins outs =>
    tl_total_rel_semantics mabs (make_vecs_map inputs outputs ins outs) tl.

Definition namedtensorlist_to_rel (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (ntl : namedtensorlist) : @Rel A n m :=
  fun ins outs =>
    ntl_total_rel_semantics mabs (make_vecs_map inputs outputs ins outs) ntl.

#[global] Arguments tensorexpr_to_rel _ {_ _} _ _ _ _ _ /.
#[global] Arguments tensorlist_to_rel _ {_ _} _ _ _ _ _ /.
#[global] Arguments namedtensorlist_to_rel _ {_ _} _ _ _ _ _ /.


Lemma tl_total_rel_semantics_tl_subst_free mabs ml l tl :
  tl_total_rel_semantics mabs ml (tl_subst_free l tl) <->
  ∃ a : A, tl_total_rel_semantics mabs (<[l:=a]> ml) tl.
Proof.
  destruct tl as [sums abs delt].
  rewrite tl_total_rel_semantics_alt_vec.
  cbn [tl_subst_free tl_add_sums relabel_tl tl_sums tl_abstracts tl_deltas].
  rewrite exists_vec_S.
  apply exists_iff.
  intros a.
  rewrite (tl_total_rel_semantics_alt_vec _ _ (mk_tl sums abs delt)).
  cbn [tl_sums tl_abstracts tl_deltas].
  apply exists_iff; intros m.
  apply tl_total_rel_semantics_aux_ext_base.
  - apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [[f low] up] _.
    cbn.
    split; [reflexivity|].
    split;
    apply Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall;
    intros v _;
    cbn;
    (destruct v as [r|l']; cbn;
    [rewrite lookup_cons_ne_0 by lia; f_equal; lia|];
    rewrite lookup_insert_case;
    do 2 case_decide; done).
  - apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [lv uv] _;
    cbn.
    split; [rename lv into v|rename uv into v];
    (destruct v as [r|l']; cbn;
    [rewrite lookup_cons_ne_0 by lia; f_equal; lia|];
    rewrite lookup_insert_case;
    do 2 case_decide; done).
Qed.

(* Definition compose_tensorlist (mids : list Idx) (l r : tensorlist) : tensorlist :=
  tl_add_sums (length mids) (relabel_tl
    (var_elim (bound ∘ (λ p, pos_add_N p (lengthN mids))) (λ fr,
      from_option (bound ∘ Pos.of_succ_nat ∘ (λ n, (length mids - S n)%nat))
      (free fr) (list_index fr mids))) (tl_times l r)).
 *)




Lemma tl_total_rel_semantics_compose_tensorlist_aux mabs ml mids (l r : tensorlist) :
  tl_total_rel_semantics mabs ml (compose_tensorlist mids l r) <->
  ∃ rmi : vec A (length (reverse (reverse mids))),
    tl_total_rel_semantics mabs (list_to_map (zip mids rmi) ∪ ml) (tl_times l r).
Proof.
  rewrite compose_tensorlist_foldr.
  erewrite exists_iff by now intros;
    replace (zip mids) with (zip_with (B:=A) pair (reverse (reverse mids))) by (now rewrite (reverse_involutive mids));
    refine (reflexivity _).
  cbv beta.
  generalize (reverse mids) as rmids.
  clear mids.
  intros mids.
  revert ml;
  induction mids as [|mid mids IHmid]; intros ml.
  - rewrite exists_vec_0.
    cbn.
    now rewrite map_empty_union.
  - cbn [foldr].
    unshelve (rewrite (fun H =>
      exists_surjection (λ v, Vector.cast (m:=length (reverse mids) + 1) v H)
        (Hf:=vcast_surj H))).
    1:{
      abstract (rewrite reverse_cons, length_app at 1; cbn;
      exact eq_refl).
    }
    2:{
      apply _.
    }
    unfold compose.
    setoid_rewrite vec_to_list_cast.

    rewrite exists_vec_add, exists_comm.
    rewrite tl_total_rel_semantics_tl_subst_free.
    rewrite exists_vec_1.
    apply exists_iff; intros a.
    rewrite IHmid.
    apply exists_iff; intros mr.
    f_equiv.
    rewrite reverse_cons, vec_to_list_app.
    rewrite zip_with_app by now rewrite length_vec_to_list.
    rewrite list_to_map_app.
    cbn.
    rewrite <- map_union_assoc.
    now rewrite <- insert_union_l, map_empty_union.
Qed.


Lemma tl_total_rel_semantics_free_varset_ext mabs ml ml' tl :
  (forall l, l ∈ tl_free_varset tl -> ml !! l = ml' !! l) ->
  tl_total_rel_semantics mabs ml tl <-> tl_total_rel_semantics mabs ml' tl.
Proof.
  intros Hml.
  rewrite 2 tl_total_rel_semantics_alt_vec.
  apply exists_iff; intros mr.
  apply tl_total_rel_semantics_aux_ext_base;
  apply Forall_Forall2_diag; rewrite Forall_forall.
  - intros [[f low] up] Hflu.
    cbn [fst snd].
    split; [easy|].
    split; apply Forall_Forall2_diag; rewrite Forall_forall;
    (intros [|l] Hl; [done|]); cbn;
    apply Hml;
    apply elem_of_union; left;
    rewrite elem_of_abstracts_free_vars; set_solver + Hflu Hl.
  - intros [l u] Hlu.
    cbn.
    split; [rename l into v|rename u into v];
    (destruct v as [|l']; [done|]); cbn;
    apply Hml;
    apply elem_of_union; right;
    rewrite elem_of_deltas_free_vars; set_solver + Hlu.
Qed.

Lemma compose_tensorlist_correct_rel mabs {n m o} (ins : vec Idx n)
  (mids : vec Idx m) (outs : vec Idx o) (ltl rtl : tensorlist) :
  ins ##@{list _} mids ->
  mids ##@{list _} outs ->
  ins ##@{list _} outs ->
  tl_free_varset ltl ⊆ list_to_set (ins ++ mids) ->
  tl_free_varset rtl ⊆ list_to_set (mids ++ outs) ->
  tensorlist_to_rel mabs ins outs (compose_tensorlist mids ltl rtl) ≡
  compose_rel (tensorlist_to_rel mabs ins mids ltl)
    (tensorlist_to_rel mabs mids outs rtl).
Proof.
  intros Hins_mids Hmids_outs Hins_outs Hltl Hrtl.
  intros v w.
  unfold compose_rel, tensorlist_to_rel.
  rewrite tl_total_rel_semantics_compose_tensorlist_aux.
  unshelve (rewrite (exists_vec_cast (m:=m))).
  1:{
    abstract (now rewrite reverse_involutive, length_vec_to_list).
  }
  apply exists_iff; intros mr.
  rewrite vec_to_list_cast.
  rewrite tl_total_rel_semantics_aux_tl_times.
  f_equiv.
  - apply tl_total_rel_semantics_free_varset_ext.
    intros l Hl.
    apply Hltl in Hl as Hl'.
    rewrite elem_of_list_to_set, elem_of_app in Hl'.
    destruct Hl' as [Hl'|Hl'].
    + rewrite lookup_union_r. 2:{
        apply not_elem_of_dom.
        rewrite dom_list_to_map.
        rewrite fst_zip
          by now rewrite 2 length_vec_to_list.
        rewrite elem_of_list_to_set.
        now apply Hins_mids in Hl'.
      }
      unfold make_vecs_map.
      rewrite 2 lookup_union.
      eenough (Hen : _) by now
      rewrite 2 union_eq_l by exact Hen.
      apply elem_of_dom.
      rewrite dom_list_to_map.
      rewrite elem_of_list_to_set.
      now rewrite vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
    + rewrite lookup_union, union_eq_l
        by now rewrite <- elem_of_dom, dom_list_to_map, elem_of_list_to_set,
          fst_zip by now rewrite 2 length_vec_to_list.
      unfold make_vecs_map.
      rewrite 2 vec_to_list_zip_with, lookup_union_r; [done|].
      apply not_elem_of_dom.
      rewrite dom_list_to_map, elem_of_list_to_set,
        fst_zip by now rewrite 2 length_vec_to_list.
      now intros ?%Hins_mids.
  - apply tl_total_rel_semantics_free_varset_ext.
    intros l Hl.
    apply Hrtl in Hl as Hl'.
    rewrite elem_of_list_to_set, elem_of_app in Hl'.
    destruct Hl' as [Hl'|Hl'].
    + unfold make_vecs_map.
      now rewrite 3 lookup_union, 2 union_eq_l, <- vec_to_list_zip_with by now
        rewrite <- elem_of_dom, dom_list_to_map, elem_of_list_to_set,
          ?vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
    + rewrite lookup_union_r. 2:{
        apply not_elem_of_dom.
        rewrite dom_list_to_map, fst_zip, elem_of_list_to_set
          by now rewrite 2 length_vec_to_list.
        now intros ?%Hmids_outs.
      }
      unfold make_vecs_map.
      rewrite 2 lookup_union_r by
        now apply not_elem_of_dom;
        rewrite dom_list_to_map, ?vec_to_list_zip_with, fst_zip, elem_of_list_to_set
          by (now rewrite 2 length_vec_to_list);
        now intros ?%Hmids_outs || intros ?%Hins_outs.
      done.
Qed.



Lemma ntl_total_rel_semantics_ntl_subst_free_as mabs ml l r ntl :
  r ∉ ntl.(ntl_sums) ->
  WF_ntl ntl ->
  ntl_total_rel_semantics mabs ml (ntl_subst_free_as l r ntl) <->
  ∃ a : A, ntl_total_rel_semantics mabs (<[l:=a]> ml) ntl.
Proof.
  intros Hr HWF.
  rewrite ntl_total_rel_semantics_alt by now apply ntl_subst_free_as_WF.
  setoid_rewrite ntl_total_rel_semantics_alt; [|easy].
  destruct ntl as [sums abs delt].
  cbn -[abstracts_rel_semantics_alt deltas_rel_semantics_alt].
  rewrite exists_SVmap_cons, exists_comm.
  apply exists_iff; intros a.
  apply exists_iff; intros [mr Hmr].
  cbn [SVmap_map SVmap_insert dexist proj1_sig].
  apply bool_decide_unpack in Hmr.
  f_equiv.
  - apply eq_reflexivity, abstracts_rel_semantics_alt_ext.
    apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [[f low] up] Hflu;
    cbn.
    split; [reflexivity|].
    rewrite 2 list_eq_Forall2.
    split;
    apply Forall2_fmap, Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall;
    intros v Hv;
    cbn;
    (destruct v as [r'|l']; cbn;
    [unfold SVmap; apply lookup_insert_ne; intros Heq;
     apply Hr; subst r; cbn; rewrite <- (elem_of_list_to_set (C:=Pset));
     apply HWF.2.1, elem_of_abstracts_bound_vars; set_solver +Hv Hflu|
     rewrite lookup_insert_case; do 2 case_decide; cbn;
      done || unfold SVmap; apply lookup_insert]).
  - apply eq_reflexivity, deltas_rel_semantics_alt_ext.
    apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [lv uv] Hlu;
    cbn.
    split; [rename lv into v|rename uv into v];
    (destruct v as [r'|l']; cbn;
    [unfold SVmap; apply lookup_insert_ne; intros Heq;
     apply Hr; subst r; cbn; rewrite <- (elem_of_list_to_set (C:=Pset));
     apply HWF.2.2, elem_of_deltas_bound_vars; set_solver +Hlu|
    rewrite lookup_insert_case; do 2 case_decide; cbn;
      done || unfold SVmap; apply lookup_insert]).
Qed.


Lemma ntl_total_rel_semantics_ntl_subst_free mabs ml l ntl :
  WF_ntl ntl ->
  ntl_total_rel_semantics mabs ml (ntl_subst_free l ntl) <->
  ∃ a : A, ntl_total_rel_semantics mabs (<[l:=a]> ml) ntl.
Proof.
  intros HWF.
  apply ntl_total_rel_semantics_ntl_subst_free_as, HWF.
  apply infinite_is_fresh.
Qed.








Lemma abstracts_rel_semantics_alt_app mabs ml mr abs abs' :
  abstracts_rel_semantics_alt mabs ml mr (abs ++ abs') <->
  abstracts_rel_semantics_alt mabs ml mr abs /\
  abstracts_rel_semantics_alt mabs ml mr abs'.
Proof.
  unfold abstracts_rel_semantics_alt.
  now rewrite fmap_app, Rlist_prod_app.
Qed.


Lemma deltas_rel_semantics_alt_app ml mr delt delt' :
  deltas_rel_semantics_alt ml mr (delt ++ delt') <->
  deltas_rel_semantics_alt ml mr delt /\
  deltas_rel_semantics_alt ml mr delt'.
Proof.
  unfold deltas_rel_semantics_alt.
  now rewrite fmap_app, Rlist_prod_app.
Qed.

Lemma ntl_total_rel_semantics_ntl_times mabs ml l r :
  WF_ntl l -> WF_ntl r ->
  ntl_total_rel_semantics mabs ml (ntl_times l r) <->
  ntl_total_rel_semantics mabs ml l /\ ntl_total_rel_semantics mabs ml r.
Proof.
  intros Hl Hr.
  rewrite ntl_total_rel_semantics_alt by now apply ntl_times_WF.
  rewrite 2 ntl_total_rel_semantics_alt by easy.
  cbn -[abstracts_rel_semantics_alt deltas_rel_semantics_alt list_to_set].
  rewrite exists_SVmap_app, (exists_SVmap_fmap _).
  rewrite exists_and_r.
  apply exists_iff; intros [mr_l Hmr_l].
  cbn.
  apply bool_decide_spec in Hmr_l.
  rewrite exists_and_l, (exists_SVmap_fmap _).
  apply exists_iff; intros [mr_r Hmr_r].
  cbn.
  apply bool_decide_spec in Hmr_r.
  rewrite abstracts_rel_semantics_alt_app, deltas_rel_semantics_alt_app.
  symmetry.
  rewrite rmul_comm_double.
  symmetry.
  f_equiv.
  - f_equiv;
    apply eq_reflexivity, abstracts_rel_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall; intros [[f low] up] _;
    cbn;
    (split; [easy|]);
    split;
    rewrite <- list_fmap_compose; apply list_fmap_ext;
    (intros _ [v|] _; [cbn -[bcons]|done]);
    try (rewrite lookup_union_l by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _));
    rewrite lookup_union_r by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _).
  - f_equiv;
    apply eq_reflexivity, deltas_rel_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall; intros [vl vu] _;
    cbn;
    (split; [rename vl into v|rename vu into v]);
    (destruct v as [v|]; [cbn -[bcons]|done]);
    try (rewrite lookup_union_l by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _));
    rewrite lookup_union_r by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _).
Qed.




Lemma ntl_total_rel_semantics_compose_namedtensorlist_aux mabs ml mids
  (l r : namedtensorlist) :
  WF_ntl l -> WF_ntl r ->
  ntl_total_rel_semantics mabs ml (compose_namedtensorlist mids l r) <->
  ∃ rmi : vec A (length (reverse (reverse mids))),
    ntl_total_rel_semantics mabs (list_to_map (zip mids rmi) ∪ ml) (ntl_times l r).
Proof.
  unfold compose_namedtensorlist.
  erewrite exists_iff by now intros;
    replace (zip mids) with (zip_with (B:=A) pair (reverse (reverse mids))) by (now rewrite (reverse_involutive mids));
    refine (reflexivity _).
  cbv beta.
  generalize (reverse mids) as rmids.
  clear mids.
  intros mids.
  intros Hl Hr.
  revert ml;
  induction mids as [|mid mids IHmid]; intros ml.
  - rewrite exists_vec_0.
    cbn.
    now rewrite map_empty_union.
  - cbn [foldr].
    unshelve (rewrite (exists_vec_cast (m:=length (reverse mids) + 1))).
    1: {
      abstract (rewrite reverse_cons, length_app at 1; cbn;
      exact eq_refl).
    }
    setoid_rewrite vec_to_list_cast.
    rewrite exists_vec_add, exists_comm.
    rewrite ntl_total_rel_semantics_ntl_subst_free by now apply compose_namedtensorlist_WF'.
    rewrite exists_vec_1.
    apply exists_iff; intros a.
    rewrite IHmid.
    apply exists_iff; intros mr.
    f_equiv.
    rewrite reverse_cons, vec_to_list_app.
    rewrite zip_with_app by now rewrite length_vec_to_list.
    rewrite list_to_map_app.
    cbn.
    rewrite <- map_union_assoc.
    now rewrite <- insert_union_l, map_empty_union.
Qed.


Lemma ntl_total_rel_semantics_free_varset_ext mabs ml ml' ntl :
  (forall l, l ∈ ntl_free_varset ntl -> ml !! l = ml' !! l) ->
  ntl_total_rel_semantics mabs ml ntl <-> ntl_total_rel_semantics mabs ml' ntl.
Proof.
  intros Hml.
  apply tl_total_rel_semantics_free_varset_ext.
  now rewrite <- ntl_free_varset_correct.
Qed.

Lemma compose_namedtensorlist_correct_rel mabs {n m o} (ins : vec Idx n)
  (mids : vec Idx m) (outs : vec Idx o) (ltl rtl : namedtensorlist) :
  ins ##@{list _} mids ->
  mids ##@{list _} outs ->
  ins ##@{list _} outs ->
  WF_ntl ltl -> WF_ntl rtl ->
  ntl_free_varset ltl ⊆ list_to_set (ins ++ mids) ->
  ntl_free_varset rtl ⊆ list_to_set (mids ++ outs) ->
  namedtensorlist_to_rel mabs ins outs (compose_namedtensorlist mids ltl rtl) ≡
  compose_rel (namedtensorlist_to_rel mabs ins mids ltl)
    (namedtensorlist_to_rel mabs mids outs rtl).
Proof.
  intros Hins_mids Hmids_outs Hins_outs HWFl HWFr Hltl Hrtl.
  intros v w.
  unfold compose_rel, namedtensorlist_to_rel.
  rewrite ntl_total_rel_semantics_compose_namedtensorlist_aux by easy.
  unshelve (rewrite (exists_vec_cast (m:=m))).
  1:{
    abstract (now rewrite reverse_involutive, length_vec_to_list).
  }
  apply exists_iff; intros mr.
  rewrite vec_to_list_cast.
  rewrite ntl_total_rel_semantics_ntl_times by easy.
  f_equiv.
  - apply ntl_total_rel_semantics_free_varset_ext.
    intros l Hl.
    apply Hltl in Hl as Hl'.
    rewrite elem_of_list_to_set, elem_of_app in Hl'.
    destruct Hl' as [Hl'|Hl'].
    + rewrite lookup_union_r. 2:{
        apply not_elem_of_dom.
        rewrite dom_list_to_map.
        rewrite fst_zip
          by now rewrite 2 length_vec_to_list.
        rewrite elem_of_list_to_set.
        now apply Hins_mids in Hl'.
      }
      unfold make_vecs_map.
      rewrite 2 lookup_union.
      eenough (Hen : _) by now
      rewrite 2 union_eq_l by exact Hen.
      apply elem_of_dom.
      rewrite dom_list_to_map.
      rewrite elem_of_list_to_set.
      now rewrite vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
    + rewrite lookup_union, union_eq_l
        by now rewrite <- elem_of_dom, dom_list_to_map, elem_of_list_to_set,
          fst_zip by now rewrite 2 length_vec_to_list.
      unfold make_vecs_map.
      rewrite 2 vec_to_list_zip_with, lookup_union_r; [done|].
      apply not_elem_of_dom.
      rewrite dom_list_to_map, elem_of_list_to_set,
        fst_zip by now rewrite 2 length_vec_to_list.
      now intros ?%Hins_mids.
  - apply ntl_total_rel_semantics_free_varset_ext.
    intros l Hl.
    apply Hrtl in Hl as Hl'.
    rewrite elem_of_list_to_set, elem_of_app in Hl'.
    destruct Hl' as [Hl'|Hl'].
    + unfold make_vecs_map.
      now rewrite 3 lookup_union, 2 union_eq_l, vec_to_list_zip_with
        by now rewrite <- elem_of_dom, dom_list_to_map, elem_of_list_to_set,
          ?vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
    + rewrite lookup_union_r. 2:{
        apply not_elem_of_dom.
        rewrite dom_list_to_map, fst_zip, elem_of_list_to_set
          by now rewrite 2 length_vec_to_list.
        now intros ?%Hmids_outs.
      }
      unfold make_vecs_map.
      rewrite 2 lookup_union_r by
        now apply not_elem_of_dom;
        rewrite dom_list_to_map, vec_to_list_zip_with, fst_zip, elem_of_list_to_set
          by (now rewrite 2 length_vec_to_list);
        now intros ?%Hmids_outs || intros ?%Hins_outs.
      done.
Qed.



Lemma total_rel_semantics_aux_kmap_te_relabel_absidx mabs ml mr
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} te :
  total_rel_semantics_aux (kmap f mabs) ml mr (te_relabel_absidx f te) <->
  total_rel_semantics_aux mabs ml mr te.
Proof.
  revert mr; induction te; intros mr; [reflexivity..| | |apply exists_iff; intros; apply IHte].
  - cbn.
    apply eq_reflexivity, abstract_rel_semantics_ext; [|reflexivity..].
    apply (lookup_kmap _).
  - cbn; f_equiv; auto.
Qed.

Lemma tl_total_rel_semantics_aux_kmap_tl_relabel_absidx mabs ml mr
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} tl :
  tl_total_rel_semantics_aux' (kmap f mabs) ml mr (tl_relabel_absidx f tl) <->
  tl_total_rel_semantics_aux' mabs ml mr tl.
Proof.
  rewrite 2 tl_total_rel_semantics_aux_alt_vec.
  destruct tl as [sums abs delt];
  cbn -[tl_total_rel_semantics_aux].
  apply exists_iff; intros m.
  apply tl_total_rel_semantics_aux_ext_base;
  [|apply Forall_Forall2_diag; rewrite Forall_forall; intros ? _; split; done].
  apply Forall2_fmap_l, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros [[idx low] up] _.
  cbn.
  rewrite (lookup_kmap _).
  split; [easy|].
  split; apply Forall_Forall2_diag; rewrite Forall_forall; intros ? _; done.
Qed.


Lemma ntl_total_rel_semantics_kmap_ntl_relabel_absidx mabs ml
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} ntl :
  ntl_total_rel_semantics (kmap f mabs) ml (ntl_relabel_absidx f ntl) <->
  ntl_total_rel_semantics mabs ml ntl.
Proof.
  unfold ntl_total_rel_semantics.
  rewrite ntl_relabel_absidx_correct.
  apply (tl_total_rel_semantics_aux_kmap_tl_relabel_absidx _ _ _ _).
Qed.


Lemma simplify_ntl_deltas_correct_rel_sem mabs ml ntl :
  WT_ntl (dom ml) ntl ->
  ntl_total_rel_semantics mabs ml ntl <->
  ntl_total_rel_semantics mabs ml (simplify_ntl_deltas ntl).
Proof.
  intros HWT.
  eapply ntl_delta_eq_correct_rel; [done..|].
  symmetry.
  now apply simplify_ntl_deltas_correct.
Qed.















End TensorExprDBrel_semantics.


Notation total_rel_semantics mabs ml te := (total_rel_semantics_aux mabs ml [] te).

Notation tl_total_rel_semantics mabs ml tl :=
  (tl_total_rel_semantics_aux mabs ml [] tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).
