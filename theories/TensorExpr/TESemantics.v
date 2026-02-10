Require Import Summable.
Require StringCustomNotation.

Require Import TESyntax.
Require Tensor.

Require Import Aux_pos Aux_stdpp.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

From stdpp Require Import functions list.



#[local] Coercion pos_to_nat_pred : positive >-> nat.
#[local] Coercion N.of_nat : nat >-> N.

(* FIXME: Move *)
Lemma sumbool_same {P Q A} (HPQ : {P} + {Q}) (a : A) :
  (if HPQ then a else a) = a.
Proof.
  now destruct HPQ.
Qed.
Lemma decide_same `{Decision P} `(a : A) :
  (if decide P then a else a) = a.
Proof.
  apply sumbool_same.
Qed.



Add Parametric Morphism : relabel_bounds with signature
  pointwise_relation _ eq ==> eq ==>
  eq as relabel_bound_mor.
Proof.
  intros f g Hfg v.
  now apply relabel_bounds_ext.
Qed.


Add Parametric Morphism A B : (@mbind list list_bind A B) with signature
  pointwise_relation A eq ==> eq ==> eq as list_bind_mor.
Proof.
  intros; apply list_bind_ext; naive_solver.
Qed.



Section list_index.
Context `{EqDecision A}.
Implicit Type l : list A.

Definition list_index (x : A) l :=
  fst <$> list_find (eq x) l.

Lemma list_index_is_Some x l :
  is_Some (list_index x l) <-> x ∈ l.
Proof.
  unfold list_index.
  rewrite fmap_is_Some.
  split; [|intros Hx; apply (list_find_elem_of _ _ x Hx eq_refl)].
  now intros [[] (?%elem_of_list_lookup_2 & <- & _)%list_find_Some].
Qed.

Lemma list_index_Some x l i :
  list_index x l = Some i <->
  l !! i = Some x /\ forall j y, l !! j = Some y -> j < i -> x <> y.
Proof.
  unfold list_index.
  rewrite fmap_Some, exists_pair.
  setoid_rewrite list_find_Some.
  naive_solver.
Qed.

Lemma list_index_Some_NoDup x l i :
  NoDup l ->
  list_index x l = Some i <-> l !! i = Some x.
Proof.
  intros Hdup.
  rewrite list_index_Some.
  rewrite <- (and_True (l !! i = Some x)) at 2.
  apply and_iff_from_l; [reflexivity|intros Hli _].
  apply iff_True_1.
  intros j y Hlj Hji ->.
  enough (i = j) by lia.
  revert Hli Hlj.
  now apply NoDup_lookup.
Qed.

Lemma list_index_inj x y l i :
  list_index x l = Some i -> list_index y l = Some i -> x = y.
Proof.
  rewrite 2 list_index_Some.
  intros [] [].
  congruence.
Qed.

Lemma list_index_lt x l i :
  list_index x l = Some i -> i < length l.
Proof.
  now intros [?%lookup_lt_Some _]%list_index_Some.
Qed.

Lemma list_index_ppermute_NoDup x l f : posperm (lengthP l) f ->
  NoDup l ->
  list_index x (ppermute f l) =
  (pos_to_nat_pred ∘ posperm_inv (lengthP l) f ∘ Pos.of_succ_nat) <$> list_index x l.
Proof.
  intros Hf Hl.
  apply option_eq; intros i.
  rewrite list_index_Some_NoDup by now rewrite ppermute_permutation.
  pose proof (lengthN_correct l).
  split.
  - intros Hlook.
    apply lookup_lt_Some in Hlook as Hi.
    rewrite length_ppermute in Hi.
    rewrite lookup_ppermute_alt_bdd in Hlook by now easy + apply posperm_bounded.
    replace (list_index x l) with (Some (f (Pos.of_succ_nat i) :> nat)) by
      now symmetry; apply list_index_Some_NoDup.
    cbn.
    rewrite pos_to_nat_pred_to_pos.
    rewrite posperm_inv_linv by now easy + lia.
    f_equal; lia.
  - destruct (list_index x l) as [fi|] eqn:Hfi; [|easy].
    apply list_index_Some in Hfi as [Hfi _].
    apply lookup_lt_Some in Hfi as Hfilt.
    cbn.
    intros [= <-].
    rewrite lookup_ppermute_alt_bdd by first [
      now apply posperm_bounded|
      specialize (posperm_inv_bounded (lengthP l) f (Pos.of_succ_nat fi));
      lia
    ].
    rewrite pos_to_nat_pred_to_pos.
    rewrite posperm_inv_rinv by now easy || lia.
    now rewrite pos_to_nat_pred_of_nat.
Qed.

Lemma list_lookup_omap_all_is_Some `(f : A -> option B) (l : list A) (i : nat)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l !! i = l !! i ≫= f.
Proof.
  rewrite <- Forall_forall in Hf.
  revert i;
  induction Hf; [now intros []|intros i].
  cbn.
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  destruct i; [cbn; now rewrite Hfx|].
  cbn.
  apply IHHf.
Qed.

Lemma length_omap_all_is_Some `(f : A -> option B) (l : list A)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  length (omap f l) = length l.
Proof.
  rewrite <- Forall_forall in Hf.
  induction Hf; [done|cbn].
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  cbn.
  f_equal; apply IHHf.
Qed.

Lemma omap_all_is_Some_default `(f : A -> option B) (l : list A) (g : A -> B)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l = (λ i, default (g i) (f i)) <$> l.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl).
  - now rewrite length_fmap; apply length_omap_all_is_Some.
  - intros i x y.
    rewrite length_fmap.
    intros Hi.
    rewrite list_lookup_omap_all_is_Some by easy.
    rewrite list_lookup_fmap.
    destruct (l !! i) as [li|]; [|easy].
    cbn.
    destruct (f li); [|easy].
    cbn; congruence.
Qed.

Lemma ppermute_alt_list_index_aux_Some f l : posbdd (lengthP l) f -> NoDup l ->
  forall x, x ∈ l ->
    is_Some (i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat)).
Proof.
  intros Hf Hl x Hx.
  pose proof (lengthN_correct l).
  apply elem_of_list_lookup in Hx as Hi.
  destruct Hi as [i Hi].
  apply list_index_Some_NoDup in Hi as Hi'; [|easy].
  rewrite Hi'.
  cbn.
  apply lookup_lt_Some in Hi as Hilt.
  apply lookup_lt_is_Some.
  specialize (Hf (Pos.of_succ_nat i)).
  lia.
Qed.

Lemma ppermute_alt_list_index f l : posbdd (lengthP l) f -> NoDup l ->
  ppermute f l = omap (λ x, i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat)) l.
Proof.
  intros Hf Hl.
  pose proof (lengthN_correct l).
  specialize (ppermute_alt_list_index_aux_Some f l Hf Hl) as Hsome.
  apply length_omap_all_is_Some in Hsome as Hlen.
  apply (λ H, list_eq_same_length _ _ _ H eq_refl);
  [now rewrite length_ppermute, Hlen|].
  intros i x y.
  rewrite length_ppermute.
  intros Hi.
  rewrite lookup_ppermute_alt_bdd by easy.
  rewrite list_lookup_omap_all_is_Some by easy.
  apply lookup_lt_is_Some in Hi as Hli.
  destruct Hli as [li Hli].
  rewrite Hli.
  cbn.
  apply list_index_Some_NoDup in Hli as Hli'; [|easy].
  rewrite Hli'.
  cbn.
  congruence.
Qed.

Lemma ppermute_alt_list_index_total
  f l : posbdd (lengthP l) f -> NoDup l ->
  ppermute f l = (λ x, default x
    (i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat))) <$> l.
Proof.
  intros Hf Hl.
  rewrite ppermute_alt_list_index by easy.
  now apply omap_all_is_Some_default, ppermute_alt_list_index_aux_Some.
Qed.

End list_index.



Section TensorExprDBSemantics.

Local Open Scope nat_scope.

Import Tensor.

(* Import Relation_Definitions.

Import Setoid. *)

Import SetoidList SetoidPermutation list.

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


(* FIXME: Move (and can just use flat_map)*)
Lemma Rlist_sum_bind {A} (f : A -> list R) l :
  req (Rlist_sum (l ≫= f)) (Rlist_sum ((λ x, Rlist_sum (f x)) <$> l)).
Proof.
  induction l; [reflexivity|].
  cbn.
  now rewrite Rlist_sum_app, IHl.
Qed.


Context `{SA : Summable A, AEQ : EqDecision A}.



(* Let Tensor := (@Tensor R). *)

Let DimensionlessTensor := (@DimensionlessTensor R A).


Definition Vapplys (f : DimensionlessTensor) (l u : list A) : R :=
  f (length l) (length u) (list_to_vec l) (list_to_vec u).

Notation varcontext := (Pmap A).

Notation abscontext := (Pmap DimensionlessTensor).


Definition get_var (ml : varcontext) (mr : list A) (v : var) : option A :=
  match v with
  | bound r => mr !! (r :> nat)
  | free l => ml !! l
  end.

(*
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
        default rO (semantics abs (<[v := mk_A x]> vars) summand)))
  end. *)

Definition abstract_semantics (mabs : abscontext) ml mr
  (absidx : Idx) (lower : list var) (upper : list var) : R :=
  default rO (largs ← join_list ((get_var ml mr) <$> lower);
      uargs ← join_list ((get_var ml mr) <$> upper);
      fval ← mabs !! absidx;
      Some (Vapplys fval largs uargs)).

Notation abstract_semantics' mabs mg ml mr abs :=
  (abstract_semantics mabs mg ml mr abs.1.1 abs.1.2 abs.2).


Lemma abstract_semantics_ext mabs ml mr mabs' ml' mr'
  idx lower upper idx' lower' upper' :
  mabs !! idx = mabs' !! idx' ->
  (get_var ml mr) <$> lower = (get_var ml' mr') <$> lower' ->
  (get_var ml mr) <$> upper = (get_var ml' mr') <$> upper' ->
  abstract_semantics mabs ml mr idx lower upper =
  abstract_semantics mabs' ml' mr' idx' lower' upper'.
Proof.
  intros Hidx Hl Hu.
  unfold abstract_semantics.
  now rewrite Hidx, Hl, Hu.
Qed.

Definition delta_semantics ml mr (l u : var) : R :=
  default rO (la ← get_var ml mr l;
    ua ← get_var ml mr u;
    Some (delta_tensor (n:=1) [# la] [# ua])).

Lemma delta_semantics_ext ml mr ml' mr' l u l' u' :
  get_var ml mr l = get_var ml' mr' l' ->
  get_var ml mr u = get_var ml' mr' u' ->
  delta_semantics ml mr l u =
  delta_semantics ml' mr' l' u'.
Proof.
  intros Hl Hu.
  unfold delta_semantics.
  now rewrite Hl, Hu.
Qed.

Fixpoint total_semantics_aux mabs ml mr (te : tensorexpr) : R :=
  match te with
  | tone => rI
  | tdelta1 l u =>
    delta_semantics ml mr l u
  | tabstract absidx lower upper =>
      abstract_semantics mabs ml mr absidx lower upper
  | tproduct l r =>
      rmul (total_semantics_aux mabs ml mr l)
        (total_semantics_aux mabs ml mr r)
  | tsum summand =>
      sum_of (fun x : A =>
        total_semantics_aux mabs ml (x :: mr) summand)
  end.

Notation total_semantics mabs ml te := (total_semantics_aux mabs ml [] te).

Fixpoint tl_total_semantics_aux mabs ml mr sums abs delt : R :=
  match sums with
  | 0 => Rlist_prod
    ((λ '(abs, low, up), abstract_semantics mabs ml mr abs low up) <$> abs) *
    Rlist_prod ((λ '(l, u), delta_semantics ml mr l u) <$> delt)
  | S sums =>
    sum_of (fun x : A =>
      tl_total_semantics_aux mabs ml (x :: mr) sums abs delt)
  end.

Notation tl_total_semantics mabs ml tl :=
  (tl_total_semantics_aux mabs ml [] tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).



(* FIXME: Move to syntax, rename *)
Definition substbound (l : Idx) : var -> var :=
  fun v => match v with
  | bound r => Pos.peano_rect _ (free l) (λ r _, bound r) r
  | free l => free l
  end.

Lemma shiftbound_alt_defn l v :
  substbound l v =
  match v with
  | bound r => if decide (r = xH) then free l else bound (Pos.pred r)
  | _ => v
  end.
Proof.
  destruct v; [|reflexivity..].
  cbn.
  induction p using Pos.peano_rect.
  - reflexivity.
  - rewrite Pos.peano_rect_succ.
    rewrite decide_False by lia.
    now rewrite Pos.pred_succ.
Qed.

Definition swapbound (v : var) : var :=
  match v with
  | bound r => bound match r with
    | xH => 2
    | 2%positive => 1
    | _ => r
    end
  | _ => v
  end.

Lemma elem_of_te_free_varset_free te l :
  l ∈ te_free_varset te <-> free l ∈ te_varset te.
Proof.
  rewrite te_varset_decomp.
  set_solver.
Qed.

Lemma elem_of_te_bound_varset_bound te l :
  l ∈ te_bound_varset te <-> bound l ∈ te_varset te.
Proof.
  rewrite te_varset_decomp.
  set_solver.
Qed.


Lemma total_semantics_aux_cons_gen mabs ml mr mr' te p x :
  p ∉ te_free_varset te ->
  total_semantics_aux mabs ml (mr ++ x :: mr') te ==
  total_semantics_aux mabs (<[p:=x]> ml) (mr ++ mr')
    (relabel_te_aux (N.of_nat (length mr)) (substbound p) te).
Proof.
  intros Hp.
  revert mr.
  enough (Hen : forall mr v, v <> free p ->
    get_var ml (mr ++ x :: mr') v =
      get_var (<[p:=x]> ml) (mr ++ mr')
        (withboundshift (length mr) (substbound p) v));
  [induction te; intros mr|].
  - reflexivity.
  - cbn.
    assert (Hl : l ∈ te_varset (tdelta1 l u)) by now set_solver +.
    assert (Hu : u ∈ te_varset (tdelta1 l u)) by now set_solver +.
    rewrite elem_of_te_free_varset_free in Hp.
    assert (Hlp : l <> free p) by congruence.
    assert (Hup : u <> free p) by congruence.
    apply eq_reflexivity, delta_semantics_ext;
    [exact (Hen mr l Hlp)|exact (Hen mr u Hup)].
  - cbn.
    apply eq_reflexivity, abstract_semantics_ext; [reflexivity|..];
    rewrite <- list_fmap_compose;
    apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2;
    apply Hen;
    cbn;
    rewrite elem_of_te_free_varset_free in Hp;
    intros Heq; apply Hp;
    rewrite <- Heq; set_solver.
  - cbn.
    f_equiv; [apply IHte1|apply IHte2]; cbn in Hp; set_solver +Hp.
  - cbn.
    apply sum_of_ext; intros val.
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


Lemma total_semantics_aux_cons mabs ml mr' te p x :
  p ∉ te_free_varset te ->
  total_semantics_aux mabs ml (x :: mr') te ==
  total_semantics_aux mabs (<[p:=x]> ml) mr'
    (relabel_te (substbound p) te).
Proof.
  intros Hp%(total_semantics_aux_cons_gen mabs ml [] mr' te p x).
  apply Hp.
Qed.


Lemma total_semantics_tsum_alt mabs ml te :
  total_semantics mabs ml (tsum te) ==
  ∑ x : A,
    total_semantics mabs (<[fresh (te_free_varset te):=x]> ml)
    (relabel_te (substbound (fresh (te_free_varset te))) te).
Proof.
  cbn.
  apply sum_of_ext; intros x.
  apply total_semantics_aux_cons.
  apply is_fresh.
Qed.


Lemma tl_total_semantics_aux_ext_base mabs mabs' ml ml' mr mr'
  abs abs' delt delt' :
  Forall2 (fun flu flu' =>
    mabs !! flu.1.1 = mabs' !! flu'.1.1 /\
    Forall2 (fun v v' => get_var ml mr v = get_var ml' mr' v') flu.1.2 flu'.1.2
    /\ Forall2 (fun v v' => get_var ml mr v = get_var ml' mr' v') flu.2 flu'.2
    ) abs abs' ->
  Forall2 (fun lu lu' =>
    get_var ml mr lu.1 = get_var ml' mr' lu'.1 /\
    get_var ml mr lu.2 = get_var ml' mr' lu'.2) delt delt' ->
  tl_total_semantics_aux mabs ml mr 0 abs delt ==
  tl_total_semantics_aux mabs' ml' mr' 0 abs' delt'.
Proof.
  intros Habs Hdelt.
  cbn.
  f_equiv.
  - induction Habs as [|flu flu' abs abs' [Hf Hlu] Habs IHabs]; [reflexivity|].
   cbn.
    f_equiv; [|apply IHabs].
    clear Habs IHabs.
    destruct flu as [[f low] up], flu' as [[f' low'] up'].
    apply eq_reflexivity, abstract_semantics_ext; [exact Hf|..];
    now apply list_eq_Forall2, Forall2_fmap.
  - induction Hdelt as [|lu lu' delt delt' [Hl Hu] Hdelt IHdelt]; [reflexivity|].
    cbn.
    f_equiv; [|easy].
    destruct lu, lu'; now apply eq_reflexivity, delta_semantics_ext.
Qed.

Lemma rmul_comm_double (r0 r1 r2 r3 : R) :
  (r0 * r1) * (r2 * r3) == (r0 * r2) * (r1 * r3).
Proof.
  ring.
Qed.

(* Lemma tl_total_semantics_aux_tl_times_aux mabs ml mr mr'
  lsums labs ldelt rsums rabs rdelt :
  (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < rsums + length mr')%nat ->
  (∀ p : positive, p ∈ deltas_bound_vars rdelt -> p < rsums + length mr')%nat ->
  tl_total_semantics_aux mabs ml (mr' ++ mr) (lsums + rsums)
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
      else pos_add_N p lsums)) <$> rdelt)) ==
  tl_total_semantics_aux mabs ml mr lsums labs ldelt *
  tl_total_semantics_aux mabs ml mr' rsums rabs rdelt.
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
          apply abstract_semantics_ext; [reflexivity|..].
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
          apply abstract_semantics_ext; [reflexivity|..].
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
      rewrite sum_of_distr_r.
      apply sum_of_ext; intros x.
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
    rewrite sum_of_distr_l.
    apply sum_of_ext; intros x.
    rewrite <- IHlsums.
    apply tl_total_semantics_aux_ext_mr.
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

Lemma fold_tl_semantics_aux_base mabs ml mr abst delt :
  Rlist_prod ((λ '(abs, low, up),
    abstract_semantics mabs ml mr abs low up) <$> abst) *
  Rlist_prod ((λ '(l, u),
    delta_semantics ml mr l u) <$> delt) =
  tl_total_semantics_aux mabs ml mr O abst delt.
Proof.
  reflexivity.
Qed.

Lemma tl_total_semantics_aux_ext_base_mr mabs ml mr mr'
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
  tl_total_semantics_aux mabs ml mr O abs delt ==
  tl_total_semantics_aux mabs ml mr' O abs' delt'.
Proof.
  intros Habs Hdelt.
  apply tl_total_semantics_aux_ext_base.
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
    split; unfold get_var; [destruct l, l'|destruct u, u']; cbn; now subst.
Qed.


Lemma tl_total_semantics_aux_ext_mr mabs ml mr mr'
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
  tl_total_semantics_aux mabs ml mr sums abs delt ==
  tl_total_semantics_aux mabs ml mr' sums abs' delt'.
Proof.
  revert mr mr'.
  induction sums as [|sums IHsums]; intros mr mr' Habs Hdelt.
  - apply tl_total_semantics_aux_ext_base_mr.
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
      split; unfold get_var; [destruct l, l'|destruct u, u']; cbn; now subst.
  - cbn.
    apply sum_of_ext; intros x.
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


Lemma tl_total_semantics_aux_tl_times_aux' mabs ml mr mr'
  lsums labs ldelt rsums rabs rdelt :
  (* (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < length rsums + length mr')%nat -> *)
  tl_total_semantics_aux mabs ml (mr' ++ mr) (lsums + rsums)
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
          pos_add_N p (lsums + length mr))) <$> rdelt)) ==
  tl_total_semantics_aux mabs ml mr lsums labs ldelt *
  tl_total_semantics_aux mabs ml mr' rsums rabs rdelt.
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
      rewrite sum_of_distr_r.
      apply sum_of_ext; intros x.
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
        apply abstract_semantics_ext; [reflexivity|..];
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
        apply eq_reflexivity, abstract_semantics_ext; [reflexivity|..];
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
      * apply eq_reflexivity, delta_semantics_ext;
        symmetry; unfold get_var;
        (case_match; cbn; [|reflexivity];
        rewrite lookup_app_r; [f_equal|]; lia).
      * apply eq_reflexivity, delta_semantics_ext;
        symmetry; unfold get_var;
        (case_match; cbn; [|reflexivity]);
        rewrite decide_False by easy;
        (case_decide as Hsm; [now rewrite lookup_app_l by lia|]);
        now rewrite 2 lookup_ge_None_2 by now rewrite ?length_app; lia.
  - cbn.
    rewrite sum_of_distr_l.
    apply sum_of_ext; intros x.
    rewrite <- IHlsums.
    apply tl_total_semantics_aux_ext_mr.
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


Lemma tl_total_semantics_aux_tl_times_aux_alt mabs ml mr
  lsums labs ldelt rsums rabs rdelt :
  (* (∀ p : positive, p ∈ abstracts_bound_vars rabs -> p < length rsums + length mr')%nat -> *)
  tl_total_semantics_aux mabs ml mr (lsums + rsums)
    ((relabel_abs (relabel_bounds (λ p, pos_add_N p rsums)) <$> labs) ++
      (relabel_abs (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rabs))
    ((relabel_delt (relabel_bounds (λ p, pos_add_N p rsums)) <$> ldelt) ++
      (relabel_delt (relabel_bounds (λ p,
      if decide (p < rsums)%nat then p
      else pos_add_N p lsums)) <$> rdelt)) ==
  tl_total_semantics_aux mabs ml mr lsums labs ldelt *
  tl_total_semantics_aux mabs ml mr rsums rabs rdelt.
Proof.
  rewrite <- tl_total_semantics_aux_tl_times_aux'.
  apply tl_total_semantics_aux_ext_mr.
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


Lemma tl_total_semantics_aux_tl_times mabs ml mr tl tl' :
  tl_total_semantics_aux mabs ml mr
    (tl_times tl tl').(tl_sums) (tl_times tl tl').(tl_abstracts)
    (tl_times tl tl').(tl_deltas) ==
  tl_total_semantics_aux mabs ml mr tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas) *
  tl_total_semantics_aux mabs ml mr tl'.(tl_sums) tl'.(tl_abstracts) tl'.(tl_deltas).
Proof.
  rewrite <- tl_total_semantics_aux_tl_times_aux_alt.
  destruct tl, tl'; reflexivity.
Qed.


Lemma tensorlist_of_tensorexpr_correct mabs ml te :
  tl_total_semantics mabs ml (tensorlist_of_tensorexpr te) ==
  total_semantics mabs ml te.
Proof.
  generalize (@nil A).
  induction te; intros mr.
  - cbn; ring.
  - cbn; ring.
  - cbn.
    ring.
  - cbn.
    rewrite <- IHte1, <- IHte2.
    now rewrite tl_total_semantics_aux_tl_times; f_equiv.
  - cbn.
    apply sum_of_ext; intros x.
    apply IHte.
Qed.



Section Teq.

Definition teq_at mabs mr : relation tensorexpr :=
  fun te1 te2 => forall ml,
  total_semantics_aux mabs ml mr te1 ==
  total_semantics_aux mabs ml mr te2.

Definition teq : relation tensorexpr :=
  fun te1 te2 => forall mabs mr, teq_at mabs mr te1 te2.

Local Notation "te1  '=t[' mabs ','  mg ']='  te2" :=
  (teq_at mabs mg [] te1 te2) (at level 70).

Local Notation "te1  '=t='  te2" :=
  (teq te1 te2) (at level 70).

Section Teq_at.

Context (mabs : abscontext) (mr : list A).

Local Notation teq_at := (teq_at mabs mr).

#[global]
Instance teq_teq_at_subrelation :
  subrelation teq teq_at.
Proof.
  easy.
Qed.

Lemma teq_at_refl : Reflexive teq_at.
Proof. easy. Qed.

Lemma teq_at_symm : Symmetric teq_at.
Proof. easy. Qed.

Lemma teq_at_trans : Transitive teq_at.
Proof.
  unfold teq, teq_at.
  pose proof (Req_equivalence.(Equivalence_Transitive)) as ?.
  eauto.
Qed.

#[global]
Add Parametric Relation : tensorexpr teq_at
  reflexivity proved by teq_at_refl
  symmetry proved by teq_at_symm
  transitivity proved by teq_at_trans
  as teq_at_setoid.


#[global]
Add Parametric Morphism ml : (total_semantics_aux mabs ml mr)
  with signature teq_at ==> req as total_semantics_at_mor.
Proof.
  unfold teq_at; auto.
Qed.


#[global]
Add Parametric Morphism : tproduct with signature
  teq_at ==> teq_at ==> teq_at as tproduct_at_mor.
Proof.
  intros l l' Hl r r' Hr vars.
  cbn.
  f_equiv; [apply Hl|apply Hr].
Qed.

End Teq_at.

Lemma tsum_at_ext mabs mr te te' :
  (forall x : A, teq_at mabs (x :: mr) te te') ->
  teq_at mabs mr (tsum te) (tsum te').
Proof.
  unfold teq_at.
  cbn.
  intros; apply sum_of_ext; auto.
Qed.

(* FIXME: Move *)
#[global]
Instance total_semantics_aux_Params : Params total_semantics_aux 3 := {}.

#[global]
Add Parametric Morphism : tsum with signature
  teq ==> teq as tsum_mor.
Proof.
  intros smd smd' Hsmd abs rels frees.
  cbn.
  now setoid_rewrite Hsmd.
Qed.



Lemma teq_refl : Reflexive teq.
Proof. easy. Qed.

Lemma teq_symm : Symmetric teq.
Proof. easy. Qed.

Lemma teq_trans : Transitive teq.
Proof.
  unfold teq, teq_at.
  pose proof (Req_equivalence.(Equivalence_Transitive)) as ?.
  eauto.
Qed.

#[global]
Add Parametric Relation : tensorexpr teq
  reflexivity proved by teq_refl
  symmetry proved by teq_symm
  transitivity proved by teq_trans
  as teq_setoid.

#[global]
Add Parametric Morphism : tproduct with signature
  teq ==> teq ==> teq as tproduct_mor.
Proof.
  intros l l' Hl r r' Hr abs rels frees.
  cbn.
  now rewrite Hl, Hr.
Qed.

Local Ltac cring :=
  intros abs rels frees; cbn; ring.

Lemma tproduct_tone_l te : teq (tproduct tone te) te.
Proof.
  cring.
Qed.

Lemma tproduct_tone_r te : teq (tproduct te tone) te.
Proof.
  cring.
Qed.

Lemma tproduct_assoc te1 te2 te3 :
  teq (tproduct te1 (tproduct te2 te3))
  (tproduct (tproduct te1 te2) te3).
Proof.
  cring.
Qed.

Lemma tproduct_comm te1 te2 :
  teq (tproduct te1 te2)
    (tproduct te2 te1).
Proof.
  cring.
Qed.

Lemma tproducts_cons te tes :
  teq (tproducts (te :: tes)) (tproduct te (tproducts tes)).
Proof.
  destruct tes; [|reflexivity].
  cbn.
  now rewrite tproduct_tone_r.
Qed.

#[global]
Add Parametric Morphism : tproducts with signature
  Permutation ==> teq as tproducts_perm_mor.
Proof.
  intros tes tes' Hperm.
  induction Hperm; [reflexivity|..|etransitivity; eauto].
  - rewrite 2 tproducts_cons; now f_equiv.
  - rewrite !tproducts_cons.
    rewrite 2 tproduct_assoc.
    f_equiv.
    apply tproduct_comm.
Qed.


End Teq.




(* FIXME: Move *)
Notation tl_total_semantics_aux' mabs ml mr tl :=
  (tl_total_semantics_aux mabs ml mr tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).





(* TODO:
  (1) Add lemma about relabeling sum_of
  --(2) Add lemma rephrasing tl_total_semantics using [∑ m : Vlist (reverse sums), _]
  (3) Put these together to prove the result connecting to tl_total_semantics_alt *)


Lemma tl_total_semantics_aux_alt_vec mabs ml mr sums abs delt :
  tl_total_semantics_aux mabs ml mr sums abs delt ==
  ∑ m : vec A sums,
    tl_total_semantics_aux mabs ml (rev_append m mr) O abs delt.
Proof.
  revert mr; induction sums; intros mr.
  - rewrite sum_of_vec_0; reflexivity.
  - cbn.
    setoid_rewrite IHsums.
    rewrite sum_of_vec_succ.
    reflexivity.
Qed.

Lemma tl_total_semantics_alt_vec mabs ml tl :
  tl_total_semantics mabs ml tl ==
  ∑ m : vec A tl.(tl_sums),
    tl_total_semantics_aux mabs ml m O tl.(tl_abstracts) tl.(tl_deltas).
Proof.
  rewrite tl_total_semantics_aux_alt_vec.
  rewrite sum_of_vec_rev.
  f_equiv; intros mr.
  now rewrite vec_to_list_rev, rev_append_reverse, reverse_involutive, app_nil_r.
Qed.




Definition get_var_alt (ml mr : varcontext) (v : var) : option A :=
  match v with
  | bound r => mr !! r
  | free l => ml !! l
  end.

Definition abstract_semantics_alt (mabs : abscontext) ml mr
  (absidx : Idx) (lower : list var) (upper : list var) : R :=
  default rO (largs ← join_list ((get_var_alt ml mr) <$> lower);
      uargs ← join_list ((get_var_alt ml mr) <$> upper);
      fval ← mabs !! absidx;
      Some (Vapplys fval largs uargs)).

Notation abstract_semantics_alt' mabs ml mr abs :=
  (abstract_semantics_alt mabs ml mr abs.1.1 abs.1.2 abs.2).

Definition delta_semantics_alt ml mr (l u : var) : R :=
  default rO (la ← (get_var_alt ml mr l);
      ua ← (get_var_alt ml mr u);
      Some (delta_tensor (n:=1) [#la] [#ua])).

Notation delta_semantics_alt' ml mr delt :=
  (delta_semantics_alt ml mr delt.1 delt.2).


Definition Vmap (tys : list Idx) : Type :=
  Pmap A.

Definition WF_Vmap {tys} (m : Vmap tys) : Prop :=
  dom m =@{Pset} list_to_set tys /\
  map_Forall (fun _ v => v ∈ sum_elements) m.

Fixpoint Vmap_elements tys : list (Vmap tys) :=
  match tys with
  | [] => [∅]
  | idx :: tys =>
    m ← Vmap_elements tys;
    (λ v, <[idx := v]> m) <$> sum_elements
  end.

Instance Vmap_summable tys : Summable (Vmap tys) :=
  sum_over (Vmap_elements tys).


Lemma elem_of_Vmap_elements_1 tys m :
  m ∈ Vmap_elements tys ->
  WF_Vmap m.
Proof.
  unfold WF_Vmap, Vmap.
  revert m; induction tys as [|idx tys IHtys]; intros m;
  [cbn; rewrite elem_of_list_singleton; intros ->;
    unfold Vmap; split; [apply dom_empty_L|apply map_Forall_empty]|].
  cbn -[list_to_set].
  rewrite list_to_set_cons.
  unfold Vmap.
  intros (m' & (x & -> & Hx)%elem_of_list_fmap
    & Hm'%IHtys)%elem_of_list_bind.
  split; [now rewrite dom_insert_L, Hm'.1|].
  now apply map_Forall_insert_2.
Qed.

Lemma elem_of_Vmap_elements tys m :
  NoDup tys ->
  m ∈ Vmap_elements tys <->
  WF_Vmap m.
Proof.
  intros Hnd.
  split; [apply elem_of_Vmap_elements_1|].
  revert Hnd m; induction tys as [|idx tys IHtys]; intros Hnd m;
  [unfold WF_Vmap; cbn; intros [Hdom _];
    unfold Vmap in *;
    rewrite elem_of_list_singleton; eapply (dom_empty_iff_L _).1; exact Hdom|].

  cbn.
  unfold Vmap.
  apply NoDup_cons in Hnd as [Hidx Htys].
  rewrite elem_of_list_bind.
  setoid_rewrite elem_of_list_fmap.
  tspecialize IHtys by easy.
  intros [Hdomm Helems].
  exists (delete idx m).
  split.
  - assert (Hidxm : idx ∈ dom m) by now rewrite Hdomm; set_solver +.
    unfold Vmap in *.
    apply elem_of_dom in Hidxm as (ty & Hty).
    exists ty.
    rewrite insert_delete by easy.
    split; [easy|].
    now apply (Helems idx ty).
  - apply IHtys.
    split;
    unfold Vmap in *; [|now apply map_Forall_delete].
    rewrite dom_delete_L, Hdomm.
    set_solver + Hidx.
Qed.


Lemma Vmap_elements_perm tys tys' :
  tys ≡ₚ tys' ->
  Vmap_elements tys ≡ₚ Vmap_elements tys'.
Proof.
  intros Hperm.
  induction Hperm; [reflexivity| | |].
  - cbn in *.
    now rewrite IHHperm.
  - cbn.
    rewrite 2 list_bind_assoc.
    unfold compose.
    setoid_rewrite list_fmap_bind; unfold compose.
    apply bind_pointwise_Permutation_strong; [|easy].
    intros m _.
    setoid_rewrite list_fmap_to_bind.
    destruct_decide (decide (x = y)).
    + subst.
      reflexivity.
    + rewrite list_bind_comm.
      rewrite 2 list_bind_to_cprod.
      apply eq_reflexivity, list_bind_mor; [|reflexivity].
      intros (?,?).
      cbn.
      unfold Vmap in *.
      now rewrite insert_commute.
  - etransitivity; [apply IHHperm1|]; eauto.
Qed.


Lemma sum_of_Vmap_perm tys tys' f : tys ≡ₚ tys' ->
  ∑ m : Vmap tys, f m == ∑ m : Vmap tys', f m.
Proof.
  intros Hperm.
  unfold_sum_of.
  unfold sum_elements; cbn.
  rewrite list_map_fmap.
  apply Rlist_sum_perm.
  now rewrite (Vmap_elements_perm tys tys').
Qed.


Definition tl_total_semantics_alt_aux mabs ml
  (tys : list Idx) abs delt : R :=
  ∑ mr : Vmap tys,
  Rlist_prod ((λ '(f, low, up),
    abstract_semantics_alt mabs ml mr f low up) <$> abs) *
  Rlist_prod ((λ '(l, u), delta_semantics_alt ml mr l u) <$> delt).

Lemma tl_total_semantics_alt_aux_unfold mabs ml tys abs delt :
  tl_total_semantics_alt_aux mabs ml tys abs delt =
  ∑ mr : Vmap tys,
  Rlist_prod ((λ flu,
    abstract_semantics_alt' mabs ml mr flu) <$> abs) *
  Rlist_prod ((λ lu, delta_semantics_alt' ml mr lu) <$> delt).
Proof.
  apply sum_of_ext_eq.
  intros m.
  f_equiv; f_equal; (apply list_fmap_mor; [|reflexivity]);
  [intros [[]]|intros []]; reflexivity.
Qed.

Lemma flat_map_to_list_bind `(f : A -> list B) (l : list A) :
  flat_map f l = l ≫= f.
Proof.
  now rewrite list_bind_flat_map.
Qed.

Lemma list_to_map_vec_elements_gen f sums :
  (λ mr : vec A sums,
    list_to_map (imap (fun i v => (f (Pos.of_succ_nat i), v)) mr)) <$>
    @vec_elements A sum_elements sums ≡ₚ
  Vmap_elements (f <$> pseq 1 sums).
Proof.
  revert f;
  induction sums; intros f; [reflexivity|].
  rewrite Nat2N.inj_succ.
  rewrite pseq_succ.
  cbn.
  rewrite pseq_succ_start.
  rewrite <- list_fmap_compose.
  rewrite flat_map_to_list_bind.
  rewrite <- IHsums.
  rewrite list_fmap_bind.
  unfold compose.
  rewrite list_bind_fmap.
  symmetry.

  erewrite (bind_pointwise_Permutation_strong _
    (λ a, sum_elements ≫= (λ x, [<[f xH := x]> (list_to_map
            (imap (λ i v, (f (Pos.succ (Pos.of_succ_nat i)), v))
            (vec_to_list a)))]))) by
    first [exact (Permutation_refl _)|
    intros; rewrite list_fmap_to_bind; reflexivity].
  rewrite list_bind_comm.
  apply eq_reflexivity.
  f_equiv; intros a.
  rewrite list_map_fmap.
  rewrite (list_fmap_to_bind (vcons a)).
  rewrite list_bind_fmap.
  reflexivity.
Qed.

Lemma vec_to_map_vec_sum_elements sums :
  (vec_to_map) <$>
    (sum_elements :> list (vec A sums)) ≡ₚ
  (sum_elements :> list (Vmap (pseq 1 sums))).
Proof.
  pose proof (list_to_map_vec_elements_gen id sums) as Heq.
  rewrite list_fmap_id in Heq.
  apply Heq.
Qed.

Lemma tl_total_semantics_alt_aux_correct mabs ml sums abs delt :
  tl_total_semantics_aux mabs ml [] sums abs delt ==
  tl_total_semantics_alt_aux mabs ml
    (* (list_to_map (imap (λ i v, (pos_add_N (Pos.of_succ_nat i) (lengthN sums), v)) (reverse mr))) *)
    (pseq 1 sums)
    abs delt.
Proof.
  rewrite tl_total_semantics_aux_alt_vec.
  change (rev_append ?x []) with (reverse x).
  unfold tl_total_semantics_alt_aux.

  rewrite (sum_of_relabel _ _ (vec_to_map_vec_sum_elements sums)).
  rewrite sum_of_vec_rev.
  apply sum_of_ext; intros v.
  rewrite vec_to_list_rev, reverse_involutive.
  cbn.
  f_equiv;
  apply Rlist_prod_perm_mor, eqlistA_PermutationA, eqlistA_altdef,
    Forall2_fmap, Forall_Forall2_diag;
  rewrite Forall_forall;
  [intros [[f low] up] _|intros [l u] _].
  - unfold abstract_semantics, abstract_semantics_alt.
    f_equiv.
    apply option_bind_ext; [intros largs;
      apply option_bind_ext; [reflexivity|]|];
    f_equal; apply list_fmap_ext; (intros _ [r|] _; [|reflexivity]); cbn;
    symmetry;
    apply lookup_vec_to_map_to_list'.
  - unfold delta_semantics, delta_semantics_alt.
    f_equiv.
    apply option_bind_ext; [intros largs;
      apply option_bind_ext; [reflexivity|]|];
    f_equal.
    + destruct u as [r|]; [|reflexivity].
      cbn; symmetry; apply lookup_vec_to_map_to_list'.
    + destruct l as [r|]; [|reflexivity].
      cbn; symmetry; apply lookup_vec_to_map_to_list'.
Qed.





Lemma list_inj_exists_partial_inverse `{EqDecision A, EqDecision B,
  Inhabited (B -> A)}
  (dom : list A) (f : A -> B) :
  (forall a b, a ∈ dom -> b ∈ dom -> f a = f b -> a = b) ->
  exists (g : B -> A), forall a, a ∈ dom -> g (f a) = a.
Proof.
  induction dom; [now exists inhabitant|].
  intros Hf.
  tspecialize IHdom by now intros ? ? ? ?; apply Hf; now constructor.
  destruct IHdom as (g & Hg).
  exists (<[f a := a]> g).
  intros c [-> | Hc]%elem_of_cons.
  - apply fn_lookup_insert.
  - destruct_decide (decide (f c = f a)) as Hfc.
    + rewrite Hfc.
      rewrite fn_lookup_insert.
      symmetry.
      revert Hfc.
      apply Hf; apply elem_of_cons; auto.
    + rewrite fn_lookup_insert_ne by easy.
      now apply Hg.
Qed.


Lemma abstract_semantics_alt_ext mabs ml mr mabs' ml' mr'
  idx lower upper idx' lower' upper' :
  mabs !! idx = mabs' !! idx' ->
  (get_var_alt ml mr) <$> lower = (get_var_alt ml' mr') <$> lower' ->
  (get_var_alt ml mr) <$> upper = (get_var_alt ml' mr') <$> upper' ->
  abstract_semantics_alt mabs ml mr idx lower upper =
  abstract_semantics_alt mabs' ml' mr' idx' lower' upper'.
Proof.
  intros Hidx Hl Hu.
  unfold abstract_semantics_alt.
  now rewrite Hidx, Hl, Hu.
Qed.

Lemma delta_semantics_alt_ext ml mr ml' mr'
  l u l' u' :
  (get_var_alt ml mr) l = (get_var_alt ml' mr') l' ->
  (get_var_alt ml mr) u = (get_var_alt ml' mr') u' ->
  delta_semantics_alt ml mr l u =
  delta_semantics_alt ml' mr' l' u'.
Proof.
  intros Hl Hu.
  unfold delta_semantics_alt.
  now rewrite Hl, Hu.
Qed.

Lemma kmap_Vmap_elements (f : positive -> positive) {Hf : Inj eq eq f}
  (sums : list Idx) :
  kmap (M2:=Pmap) f <$> Vmap_elements sums =
  Vmap_elements (f <$> sums).
Proof.
  induction sums; [reflexivity|].
  cbn.
  rewrite list_bind_fmap.
  rewrite <- IHsums.
  rewrite list_fmap_bind.
  apply list_bind_mor; [|reflexivity].
  intros m.
  cbn.
  rewrite <- list_fmap_compose.
  unfold compose.
  apply list_fmap_ext.
  intros _ b _.
  unfold Vmap in *.
  now rewrite (kmap_insert _).
Qed.


Lemma tl_total_semantics_alt_aux_relabel mabs ml mr (f : Idx -> Idx)
  {Hf : Inj eq eq f} abs delt :
  tl_total_semantics_alt_aux mabs ml mr abs delt ==
  tl_total_semantics_alt_aux mabs ml (f <$> mr)
    (relabel_abs (relabel_bounds f) <$> abs)
    (relabel_delt (relabel_bounds f) <$> delt).
Proof.
  unfold tl_total_semantics_alt_aux.
  unshelve (eapply sum_of_relabel'_l2r); [exact (kmap f)| |
  unfold sum_elements; cbn; now rewrite ?kmap_Vmap_elements].
  intros m Hm%elem_of_Vmap_elements_1.
  f_equiv.
  - apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r, (unfold @compose).
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros ((fidx, low), up) _.
    cbn.
    apply eq_reflexivity, abstract_semantics_alt_ext; [reflexivity|..];
    rewrite <- list_fmap_compose;
    apply list_fmap_ext; (intros _ [r|] _; [|reflexivity]);
    cbn;
    now rewrite (lookup_kmap _).
  - apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r, (unfold @compose).
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros (l, u) _.
    cbn.
    apply eq_reflexivity, delta_semantics_alt_ext;
    [destruct l as [r|]|destruct u as [r|]]; try reflexivity;
    cbn;
    now rewrite (lookup_kmap _).
Qed.

(*
Lemma Vlist_elements_app tys tys' :
  Vlist_elements (tys ++ tys') ≡ₚ
  Vlist_elements tys ≫= λ l,
    (l ++.) <$> Vlist_elements tys'.
Proof.
  induction tys; [cbn; now rewrite list_fmap_id, app_nil_r|].
  cbn.
  rewrite IHtys.
  rewrite 2 list_bind_assoc.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros l Hl.
  cbn.
  generalize (Vlist_elements tys') as m.
  gen_sum_elem m'.
  intros m.
  revert m'; induction m; intros m'.
  - cbn.
    now rewrite list_bind_nil_r.
  - cbn.
    rewrite list_bind_cons_r.
    rewrite <- list_fmap_compose, (unfold @compose).
    rewrite IHm.
    reflexivity.
Qed.


Lemma Vlist_elements_app_alt tys tys' :
  Vlist_elements (tys ++ tys') ≡ₚ
  Vlist_elements tys' ≫= λ l,
    (.++ l) <$> Vlist_elements tys.
Proof.
  induction tys; [now cbn; rewrite list_bind_singleton_r, list_fmap_id|].
  cbn.
  rewrite IHtys.
  rewrite list_bind_assoc.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros l Hl.
  cbn.
  rewrite list_fmap_bind, list_bind_fmap.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros l' Hl'.
  rewrite <- list_fmap_compose.
  reflexivity.
Qed.


Lemma Vlist_elements_cons_alt ty tys :
  Vlist_elements (ty :: tys) ≡ₚ
  x ← (sum_elements :> list (V ty));
  (mk_A x ::.) <$> Vlist_elements tys.
Proof.
  change (ty :: tys) with ([ty] ++ tys).
  rewrite Vlist_elements_app.
  cbn.
  rewrite app_nil_r.
  rewrite list_fmap_to_bind, list_bind_assoc.
  apply bind_pointwise_Permutation_strong; [|easy].
  intros x _.
  cbn.
  now rewrite app_nil_r.
Qed.

Lemma Vlist_elements_two_inserts tys ty tys' ty' tys'' :
  Vlist_elements (tys ++ ty :: tys' ++ ty' :: tys'') ≡ₚ
  x ← (sum_elements :> list (V ty));
  x' ← (sum_elements :> list (V ty'));
  l ← Vlist_elements tys;
  l' ← Vlist_elements tys';
  l'' ← Vlist_elements tys'';
  [l ++ mk_A x :: l' ++ mk_A x' :: l''].
Proof.
  rewrite Vlist_elements_app_alt.
  rewrite Vlist_elements_cons_alt, list_bind_assoc.
  apply bind_pointwise_Permutation_strong; [|easy].
  intros x _; cbn.
  rewrite list_fmap_to_bind, list_bind_assoc.
  rewrite Vlist_elements_app_alt, Vlist_elements_cons_alt.
  rewrite 2 list_bind_assoc.
  apply bind_pointwise_Permutation_strong; [|easy].
  intros x' _; cbn.
  rewrite list_fmap_to_bind, list_bind_assoc.
  unfold compose; cbn.
  do 2 setoid_rewrite app_nil_r.
  setoid_rewrite list_fmap_bind.
  unfold compose; cbn.
  rewrite list_bind_comm.
  rewrite (list_bind_comm _ (Vlist_elements tys)).
  apply bind_pointwise_Permutation_strong; [|easy].
  intros l' _.
  rewrite list_bind_comm.
  apply bind_pointwise_Permutation_strong; [|easy].
  intros l'' _.
  now rewrite list_bind_singleton_r.
Qed.




Lemma ppermute_posperm_swap_permutes_Vlist_elements tys (p q : positive) :
  (p < q)%positive -> (q < lengthP tys)%positive ->
  ppermute (posperm_swap p q) <$> Vlist_elements tys
  ≡ₚ Vlist_elements (ppermute (posperm_swap p q) tys).
Proof.
  intros Hpq Hqlen.
  pose proof (lengthN_correct tys) as HlenNtys.
  assert ((q :> nat) < length tys) as [tq Htq]%lookup_lt_is_Some by lia.
  apply elem_of_list_split_length in Htq as Hqdecomp.
  destruct Hqdecomp as (l12 & l3 & Htys & Hlen1).
  apply (f_equal length) in Htys as Hlens.
  rewrite length_app in Hlens.
  cbn in Hlens.
  assert ((p :> nat) < length l12) as [tp Htp]%lookup_lt_is_Some by lia.
  apply elem_of_list_split_length in Htp as Hpdecomp.
  destruct Hpdecomp as (l1 & l2 & Hl12 & Hlen2).
  pose proof (lengthN_correct l1).
  pose proof (lengthN_correct l2).
  pose proof (lengthN_correct l3).

  subst tys l12.
  rewrite <- (app_assoc _).
  cbn.
  rewrite Vlist_elements_two_inserts.
  rewrite_strat (topdown list_bind_fmap).
  rewrite length_app, length_cons in Hlen1.
  rewrite ppermute_posperm_swap_swaps by lia.
  rewrite Vlist_elements_two_inserts.
  rewrite list_bind_comm.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros xq _.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros xp _.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros v1 Hv1%elem_of_Vlist_elements%Forall2_length.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros v2 Hv2%elem_of_Vlist_elements%Forall2_length.
  apply bind_pointwise_Permutation_strong; [|reflexivity].
  intros v3 Hv3%elem_of_Vlist_elements%Forall2_length.
  rewrite fmap_cons, fmap_nil.
  fold A in *.
  rewrite ppermute_posperm_swap_swaps by (rewrite ?lengthN_correct_rev; lia).
  solve_Permutation.
Qed.

Lemma ppermute_posperm_permutes_Vlist_elements f tys :
  posperm (lengthP tys) f ->
  ppermute f <$> Vlist_elements tys ≡ₚ
  Vlist_elements (ppermute f tys).
Proof.
  remember (lengthP tys) as n eqn:Hn.
  intros Hf.
  revert f Hf tys Hn.
  refine (posperm_ind_fn_comp' _ _ _ _ _ _).
  - intros f g Hf Hg Hfg.
    intros Hp tys ->.
    specialize (Hp tys eq_refl).
    rewrite <- (ppermute_ext _ _ _ Hfg).
    rewrite <- Hp.
    apply eq_reflexivity.
    apply list_fmap_ext; intros _ x
      Hx%elem_of_list_lookup_2%elem_of_Vlist_elements%Forall2_length.
    symmetry; apply ppermute_ext.
    fold A in *.
    rewrite lengthN_correct_rev, <- Hx, <- lengthN_correct_rev.
    apply Hfg.
  - intros tys ->.
    rewrite ppermute_id.
    apply eq_reflexivity.
    apply list_fmap_id'.
    intros; apply ppermute_id.
  - intros p q Hp Hq.
    intros tys ->.
    now apply ppermute_posperm_swap_permutes_Vlist_elements.
  - intros f g Hf Hg IHf IHg tys ->.
    rewrite <- ppermute_compose by auto using posperm_bounded.
    rewrite <- IHf by now rewrite lengthN_ppermute.
    rewrite <- IHg by reflexivity.
    rewrite <- list_fmap_compose.
    apply eq_reflexivity.
    apply list_fmap_ext;
    intros _ vs Hvs%elem_of_list_lookup_2%elem_of_Vlist_elements%Forall2_length.
    fold A in *.
    rewrite <- ppermute_compose by
      (apply posperm_bounded; rewrite ?lengthN_correct_rev in *; congruence).
    reflexivity.
Qed. *)



(* FIXME: Move *)
Lemma Rlist_prod_Forall2_ext (rs rs' : list R) :
  Forall2 req rs rs' -> Rlist_prod rs == Rlist_prod rs'.
Proof.
  intros Halls.
  f_equiv.
  now apply eqlistA_PermutationA, eqlistA_altdef.
Qed.

Lemma tl_aeq_correct mabs ml tl tl' :
  tl =tl= tl' ->
  tl_total_semantics mabs ml tl ==
  tl_total_semantics mabs ml tl'.
Proof.
  intros (f & Hf & Htypes & Habs & Hdelt).
  rewrite 2 tl_total_semantics_alt_aux_correct.

  rewrite <- Htypes.
  unfold tl_total_semantics_alt_aux.
  set (p:=Pos.of_succ_nat tl.(tl_sums)) in *.
  assert (Hfinj : Inj (=) (=) (make_pwf p f)) by now apply make_pwf_inj.
  apply (sum_of_relabel'_r2l (kmap (M2:=Pmap) (M1:=Pmap) (make_pwf p f))).
  2: {
    unfold sum_elements; cbn.
    rewrite (kmap_Vmap_elements _).
    apply Vmap_elements_perm.
    replace (N.of_nat tl.(tl_sums)) with (Pos.pred_N p) by lia.
    rewrite <- Hf at 2.
    apply eq_reflexivity, list_fmap_ext;
      intros _ k Hk%elem_of_list_lookup_2%elem_of_pseq_1.
    apply decide_False.
    lia.
  }
  intros m Hm%elem_of_Vmap_elements_1.
  f_equiv.
  - erewrite Rlist_prod_perm by now rewrite Habs.
    apply Rlist_prod_Forall2_ext.
    rewrite Forall2_fmap_l, Forall2_fmap.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [[idx low] up] _.
    cbn.
    apply eq_reflexivity, abstract_semantics_alt_ext; [reflexivity|..];
      rewrite <- list_fmap_compose; apply list_fmap_ext;
        (intros _ [r|] _; [|reflexivity]; cbn -[make_pwf];
        apply (lookup_kmap _)).
  - erewrite Rlist_prod_perm by now rewrite Hdelt.
    apply Rlist_prod_Forall2_ext.
    rewrite Forall2_fmap_l, Forall2_fmap.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [l u] _.
    cbn.
    apply eq_reflexivity, delta_semantics_alt_ext;
    [destruct l as [r|]; [|reflexivity]|destruct u as [r|]; [|reflexivity]];
    cbn -[make_pwf]; apply (lookup_kmap _).
Qed.


(* Notation tl_total_semantics_alt mabs mg ml mr tl :=
  tl_total_semantics_alt_aux mabs mg ml mr (tl.()) *)



(* TODO: Extensionality of semantics from equation semantics*)
(*

(* TODO: Remove this alt version with union.
  NB: would require correctness condition; I believe somehting about the
    image of freemap? Probably all rels being large *)
Lemma fill_tensorlist_rewrite_semantics' mabs mg ml
  outer inner relmap freemap :
  tl_total_semantics mabs mg ml
    (fill_tensorlist_rewrite outer inner relmap freemap) ==
  ∑ mro : Vlist (reverse outer.(tl_sums)),
    tl_total_semantics_aux' mabs mg
      (omap (get_var mg ml mro) freemap ∪ ml) (* NB: Shouldn't need union, if WT *)
      mro inner
    * tl_total_semantics_aux mabs mg ml mro [] outer.(tl_abstracts).
Proof.
  rewrite tl_total_semantics_alt_Vlist.
  destruct outer as [osums oabs], inner as [isums iabs].
  cbn -[reverse].
  setoid_rewrite fmap_app.
  setoid_rewrite Rlist_prod_app.
  rewrite reverse_app, sum_of_Vlist_app, sum_of_comm.
  apply sum_of_ext'.
  intros mro Hmro.
  rewrite tl_total_semantics_aux_alt_Vlist.
  symmetry.
  setoid_rewrite (rev_append_reverse _ mro).
  rewrite <- (sum_of_Vlist_reverse _ (λ m, tl_total_semantics_aux _ _ _ (m ++ mro) _ _)).
  rewrite sum_of_distr_l.
  apply sum_of_ext'.
  intros mri Hmri.
  rewrite rmul_comm.
  f_equiv.
  - apply tl_total_semantics_aux_ext_base.
    rewrite Forall2_fmap_r.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros ((f, low), up) Hflu.
    cbn.
    split; [easy|].
    rewrite <- fmap_app.
    rewrite Forall2_fmap_r.
    apply Forall_Forall2_diag.
    apply Forall_forall; intros v Hv.
    cbn.
    destruct v as [r| |]; [|reflexivity..].
    cbn.
    apply elem_of_Vlist_elements, Forall2_length in Hmri.
    rewrite length_reverse in Hmri.
    pose proof (lengthN_correct isums).
    fold A in *.
    rewrite lookup_app_r by lia.
    f_equal; lia.
  - apply tl_total_semantics_aux_ext_base.
    rewrite Forall2_fmap_r.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros ((f, low), up) Hflu.
    cbn.
    split; [easy|].
    rewrite <- fmap_app.
    rewrite Forall2_fmap_r.
    apply Forall_Forall2_diag.
    apply Forall_forall; intros v Hv.
    cbn.
    destruct v as [r| |]; [reflexivity| |reflexivity].
    cbn.
    rewrite lookup_union, lookup_omap.
    destruct (freemap !! p) as [v|]; [|now cbn; destruct (ml !! p)].
    cbn.
    rewrite union_eq_l.
    + destruct v as [r| |]; [|reflexivity..].
      cbn.
      apply elem_of_Vlist_elements, Forall2_length in Hmri.
      rewrite length_reverse in Hmri.
      pose proof (lengthN_correct isums).
      fold A in *.
      rewrite lookup_app_r by lia.
      f_equal; lia.
    +

    }
    cbn.
    apply elem_of_Vlist_elements, Forall2_length in Hmri.
    rewrite length_reverse in Hmri.
    pose proof (lengthN_correct isums).
    fold A in *.
    rewrite lookup_app_r by lia.
    f_equal; lia.


  tl_total_semantics_aux_alt_Vlist

  unfold tl_total_semantics.
  rewrite tl_total_semantics_alt_aux_correct.
  unfold .


get_var_alt *)




(*
Lemma tl_total_semantics_alt_aux_relabel_gen_full mabs mg ml mr (f : Idx -> Idx) abs :
  (forall i j, i ∈ mr.*1 -> j ∈ mr.*1 -> f i = f j -> i = j) ->
  (forall i j, i ∉ mr.*1 -> j ∈ mr.*1 -> f i ≠ f j) ->
  tl_total_semantics_alt_aux mabs mg ml mr abs ==
  tl_total_semantics_alt_aux mabs mg ml (prod_map f id <$> mr)
    (relabel_abs (relabel_bounds f) <$> abs).
Proof.
  intros Hfinj Hfsafe.
  unfold tl_total_semantics_alt_aux.
  (* apply list_inj_exists_partial_inverse in Hfinj as Hg.
  destruct Hg as (g & Hg). *)
  unshelve (eapply sum_of_relabel'_l2r); [exact (kmap f)| |].
  - intros a Ha%elem_of_Vmap_elements_1.
    apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r, (unfold @compose).
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros ((fidx, low), up) _.
    cbn.
    apply eq_reflexivity, abstract_semantics_alt_ext; [reflexivity|].
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v _.
    destruct v as [r| |]; [|reflexivity..].
    cbn.
    symmetry.
    pose proof (map_is_typed_domL _ _ _ Ha.1) as Hdom.
    fold A in Hdom.
    apply lookup_kmap_full_gen.
    + intros j _ Hj%elem_of_dom_2 k _ Hk%elem_of_dom_2.
      rewrite Hdom, dom_list_to_map_L, elem_of_list_to_set in Hj, Hk.
      now apply Hfinj.
    + intros j Hj%not_elem_of_dom_2 k _ Hk%elem_of_dom_2.
      rewrite Hdom, dom_list_to_map_L, elem_of_list_to_set in Hj, Hk.
      symmetry.
      now apply Hfsafe.
  -

    lookup kmap *)






(*

Fixpoint tensorequation_semantics_aux
  mabs mg mr
  (lhs rhs : tensorexpr) (univ : list (positive * Ty))
    (ml : Pmap A) : Prop :=
  match univ with
  | [] => total_semantics_aux mabs mg ml mr lhs ==
    total_semantics_aux mabs mg ml mr rhs
  | (l, ty) :: univ =>
    forall x : V ty,
    tensorequation_semantics_aux mabs mg mr lhs rhs univ
      (<[l := mk_A x]> ml)
  end.

Definition tensorequation_semantics mabs mg teeq : Prop :=
  tensorequation_semantics_aux mabs mg [] teeq.(teq_lhs) teeq.(teq_rhs)
    (map_to_list teeq.(teq_univ)) ∅.


Lemma tensorequation_semantics_aux_perm
  mabs mg mr lhs rhs univ univ' ml :
  NoDup univ.*1 -> univ ≡ₚ univ' ->
  tensorequation_semantics_aux mabs mg mr lhs rhs univ ml <->
  tensorequation_semantics_aux mabs mg mr lhs rhs univ' ml.
Proof.
  intros Hdup Hperm.
  revert ml;
  induction Hperm as [|(l, ty) univ univ' Hperm IHuniv|
    (l, ty) (l', ty') univ |]; intros ml.
  - reflexivity.
  - cbn in Hdup.
    rewrite NoDup_cons in Hdup.
    cbn in Hdup.
    tspecialize IHuniv by easy.
    cbn.
    apply forall_iff; intros x.
    auto.
  - cbn.
    cbn in Hdup.
    rewrite 2 NoDup_cons, not_elem_of_cons in Hdup.
    setoid_rewrite (insert_commute _ l l'); [|easy].
    split; auto.
  - pose proof Hdup as Hdup'.
    rewrite Hperm1 in Hdup'.
    etransitivity; [apply IHHperm1|apply IHHperm2]; auto.
Qed.

Lemma Vmap_elements_cons_alt idxty univ :
  Vmap_elements (idxty :: univ) ≡ₚ
  (sum_elements :> list (V idxty.2)) ≫=
  λ x, (insert idxty.1 (mk_A x)) <$> Vmap_elements univ.
Proof.
  cbn.
  setoid_rewrite list_fmap_to_bind.
  rewrite list_bind_comm.
  reflexivity.
Qed.

Lemma tensorequation_semantics_aux_alt mabs mg mr lhs rhs univ ml :
  NoDup univ.*1 ->
  tensorequation_semantics_aux mabs mg mr lhs rhs univ ml ->
  forall ml',
  map_is_typed projT1 (list_to_map univ :> Pmap Ty) ml' ->
  total_semantics_aux mabs mg (ml' ∪ ml) mr lhs ==
    total_semantics_aux mabs mg (ml' ∪ ml) mr rhs.
Proof.
  remember univ.*1 as fstuniv eqn:Hfstuniv.
  intros Hdup.
  revert univ Hfstuniv ml.
  induction Hdup; intros [|[idx ty] univ]; [|easy..|].
  - intros _ ml.
    cbn.
    intros Heq ml'.
    rewrite map_is_typed_empty_l.
    intros ->.
    rewrite map_empty_union.
    easy.
  - cbn [fmap list_fmap fst].
    intros [= -> Hl] ml Heq ml'.
    cbn.
    intros Htyped%map_is_typed_insert_l'. 2:{
      apply not_elem_of_list_to_map.
      now subst l.
    }
    cbn in Heq.
    destruct Htyped as ((tyx & x) & md' & Htyx & Hml' & Hmd' & Htyped).
    cbn in Htyx.
    subst tyx.
    rewrite Hml'.
    rewrite <- insert_union_l.
    rewrite insert_union_r; [|easy].
    apply (IHHdup univ); easy.
Qed.

Lemma total_semantics_aux_tproducts mabs mg ml mr tes :
  total_semantics_aux mabs mg ml mr (tproducts tes) ==
  Rlist_prod (total_semantics_aux mabs mg ml mr <$> tes).
Proof.
  induction tes; [reflexivity|].
  cbn.
  rewrite <- IHtes.
  destruct tes; [|reflexivity].
  cbn.
  ring.
Qed.

Lemma tl_total_semantics_aux_correct mabs mg ml mr (tl : tensorlist) :
  tl_total_semantics_aux' mabs mg ml mr tl ==
  total_semantics_aux mabs mg ml mr tl.
Proof.
  destruct tl as [sums abs].
  revert mr; induction sums as [|ty sums IHsums]; intros mr.
  - cbn.
    rewrite total_semantics_aux_tproducts.
    apply Rlist_prod_ext.
    rewrite Forall2_fmap_l, 2 Forall2_fmap_r.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    intros ((f, low), up) _.
    cbn.
    reflexivity.
  - cbn.
    apply sum_of_ext; intros x.
    auto.
Qed.



Lemma tensorequation_subst_correct mabs mg mr (lhs rhs : tensorlist) univ :
  NoDup univ.*1 ->
  tensorequation_semantics_aux mabs mg mr lhs rhs univ ∅ ->
  forall (ml : Pmap A),
  map_is_typed projT1 (list_to_map univ :> Pmap Ty) ml ->
  tl_total_semantics_aux' mabs mg ml mr lhs ==
  tl_total_semantics_aux' mabs mg ml mr rhs.
Proof.
  intros Hdup Heq.
  specialize (tensorequation_semantics_aux_alt _ _ _
    _ _ _ _ Hdup Heq) as Hall.
  intros ml Hml.
  specialize (Hall ml Hml).
  rewrite map_union_empty in Hall.
  rewrite 2 tl_total_semantics_aux_correct.
  apply Hall.
Qed.

(* Lemma tensorequation_weaken_frees mabs mg mr mr' lhs rhs univ :
  tensorequation_semantics_aux mabs mg mr lhs rhs univ ∅  *)


(* Lemma tensorlist_equ *)

Lemma tl_well_bound_bound_irrelevant mabs mg ml mr mr' tl :
  tl_well_bound tl ->
  tl_total_semantics_aux' mabs mg ml mr tl ==
  tl_total_semantics_aux' mabs mg ml mr' tl.
Proof.
  intros Htl.
  apply tl_total_semantics_aux_ext_mr.
  apply Forall_Forall2_diag.
  rewrite Forall_forall.
  intros ((f, low), up) Hflu.
  split; [easy|].
  cbn.
  apply Forall_Forall2_diag, Forall_forall.
  intros x Hx.
  destruct x as [r| |]; [|reflexivity..].
  rewrite decide_True; [easy|].
  left.
  specialize (Htl r).
  tspecialize Htl by now rewrite elem_of_abstracts_bound_vars; eauto.
  rewrite elem_of_list_to_set, elem_of_pseq in Htl.
  pose proof (lengthN_correct tl.(tl_sums)).
  lia.
Qed.


Lemma fill_tensorlist_rewrite_tensorequation_semantics
  mabs mg ml (lhs rhs : tensorlist) univ outer freemap relmap :
  NoDup univ.*1 ->
  abstracts_free_vars lhs.(tl_abstracts) ⊆ dom freemap ->
  abstracts_free_vars rhs.(tl_abstracts) ⊆ dom freemap ->
  tl_well_bound lhs -> tl_well_bound rhs ->
  map_is_typed id (list_to_map univ :> Pmap Ty)
    (omap (var_elim (λ r, reverse (tl_sums outer) !! (r:>nat))
      (fmap projT1 ∘ (ml !!.))
      (fmap projT1 ∘ (mg !!.))) freemap) ->
  tensorequation_semantics_aux mabs mg [] lhs rhs univ ∅ ->
  tl_total_semantics mabs mg ml
    (fill_tensorlist_rewrite outer lhs relmap freemap) ==
  tl_total_semantics mabs mg ml
    (fill_tensorlist_rewrite outer rhs relmap freemap).
Proof.
  intros Hdup Hlhs Hrhs HlhsWB HrhsWB Htyped Heq.
  rewrite 2 fill_tensorlist_rewrite_semantics by easy.
  apply sum_of_ext'.
  intros mro Hmro%elem_of_Vlist_elements.
  f_equiv.
  pose proof (tensorequation_subst_correct _ _ _ _ _ _ Hdup Heq) as Heq'.
  rewrite (tl_well_bound_bound_irrelevant _ _ _ _ [] lhs) by easy.
  rewrite (tl_well_bound_bound_irrelevant _ _ _ _ [] rhs) by easy.
  apply Heq'.
  intros l.
  rewrite <- (Htyped l).
  cbn.
  rewrite 2 lookup_omap.
  destruct (freemap !! l) as [v|]; [|easy].
  cbn.
  destruct v; cbn; [|destruct (_ !! p); reflexivity..].
  hnf in Hmro.
  rewrite Forall2_lookup in Hmro.
  specialize (Hmro p).
  fold A in *.
  inversion Hmro; destruct_and?; cbn; congruence.
Qed.


Lemma match_rewrite_tensorlist_alt lhs rhs targ :
  match_rewrite_tensorlist lhs rhs targ =
  '(outer, relmap, freemap) ← match_tensorlist_aux lhs targ;
  Some (fill_tensorlist_rewrite outer rhs relmap freemap).
Proof.
  unfold match_rewrite_tensorlist.
  cbn.
  apply option_bind_ext; [|reflexivity].
  intros (((usums & uabs), relmap), freemap); cbn;
  now destruct rhs.
Qed.

(* FIXME: Move *)
Add Parametric Morphism mabs mg ml : (tl_total_semantics mabs mg ml)
  with signature tl_aeq ==> req as tl_total_semantics_aeq_mor.
Proof.
  apply tl_aeq_correct.
Qed.

Lemma match_correctness_tensorlist mabs mg ml (lhs rhs : tensorlist) targ univ :
  tensorequation_semantics_aux mabs mg [] lhs rhs univ ∅ ->
  NoDup univ.*1 ->
  abstracts_free_vars lhs.(tl_abstracts) = list_to_set univ.*1 ->
  abstracts_free_vars rhs.(tl_abstracts) ⊆ abstracts_free_vars lhs.(tl_abstracts) ->
  all_bound lhs ->
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (list_to_map univ) []) lhs ->
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (list_to_map univ) []) rhs ->
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml) []) targ -> (* TODO: extend to other bound contexts than [] *)
  forall out, match_rewrite_tensorlist lhs rhs targ = Some out ->
  tl_total_semantics_aux' mabs mg ml [] targ ==
  tl_total_semantics_aux' mabs mg ml [] out.
Proof.
  intros Hrewrite Hdup Hlhs_free Hrhs_free Hlhs_bound HlhsWT HrhsWT HtargWT.
  intros out.
  rewrite match_rewrite_tensorlist_alt.
  intros (((outer, relmap), freemap) & Hmatch & [= Hout])%bind_Some.
  subst out.
  pose proof (match_tensorlist_aux_correct _ _ _ _ _ _ _ _ _
    Hmatch Hlhs_bound HlhsWT HtargWT) as (Hldom & Htyl & Hteq).
  rewrite (tl_aeq_correct mabs mg ml _ _ Hteq).
  apply (fun Hl Hr HlB HrB Hwt =>
    fill_tensorlist_rewrite_tensorequation_semantics mabs mg ml _ _
    _ _ _ _ Hdup Hl Hr HlB HrB Hwt Hrewrite).
  - now rewrite Hldom.
  - now rewrite <- Hldom.
  - now apply tl_well_typed_well_bound in HlhsWT.
  - now apply tl_well_typed_well_bound in HrhsWT.
  - intros k.
    rewrite option_fmap_id.
    apply option_eq.
    intros ty.
    rewrite lookup_omap, <- elem_of_list_to_map by easy.
    destruct (freemap !! k) as [v|] eqn:Hkv. 2:{
      cbn.
      split; [easy|].
      intros Hin%(elem_of_list_fmap_1 fst).
      cbn in Hin.
      apply not_elem_of_dom in Hkv.
      rewrite <- Hldom, Hlhs_free, elem_of_list_to_set in Hkv.
      easy.
    }
    apply elem_of_dom_2 in Hkv as Hkdom.
    cbn.
    rewrite <- Hldom, Hlhs_free, elem_of_list_to_set in Hkdom.
    apply elem_of_list_lookup in Hkdom as (i & Hi).
    rewrite list_lookup_fmap in Hi.
    apply fmap_Some in Hi as ((_ & ty') & Huniv_i & [= <-]).
    transitivity (ty = ty'). 2:{
      apply elem_of_list_lookup_2 in Huniv_i.
      split; [now intros ->|].
      intros Hin.
      specialize (NoDup_fmap_1_strong _ _ Hdup (k, ty) (k, ty')
        Hin Huniv_i eq_refl).
        now intros [=].
    }

    specialize (Htyl k ty' v).
    tspecialize Htyl by
      now apply elem_of_list_lookup_2 in Huniv_i; rewrite <- elem_of_list_to_map.
    tspecialize Htyl by easy.
    destruct v as [vr|vl|vg]; cbn in *.
    + split; congruence.
    + rewrite lookup_fmap in Htyl.
      fold A in *.
      split; congruence.
    + rewrite lookup_fmap in Htyl.
      fold A in *.
      split; congruence.
Qed.

Lemma tl_total_semantics_correct mabs mg ml tl :
  tl_total_semantics mabs mg ml tl ==
  total_semantics mabs mg ml tl.
Proof.
  apply tl_total_semantics_aux_correct.
Qed.

Lemma match_correctness_tensorexpr_aux mabs mg ml (telhs terhs : tensorexpr) targ univ :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->
  NoDup univ.*1 ->
  let lhs := tensorlist_of_tensorexpr telhs in
  let rhs := tensorlist_of_tensorexpr terhs in
  tleq_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) ∅ [])
    (mk_tleq lhs rhs (list_to_map univ)) ->
  (* abstracts_free_vars lhs.(tl_abstracts) = list_to_set univ.*1 ->
  abstracts_free_vars rhs.(tl_abstracts) ⊆ abstracts_free_vars lhs.(tl_abstracts) -> *)
  all_bound lhs ->
  (* tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (list_to_map univ) []) lhs ->
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (list_to_map univ) []) rhs -> *)
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml) []) targ -> (* TODO: extend to other bound contexts than [] *)
  forall out, match_rewrite_tensorlist lhs rhs targ = Some out ->
  tl_total_semantics_aux' mabs mg ml [] targ ==
  tl_total_semantics_aux' mabs mg ml [] out.
Proof.
  intros Heq Hdup lhs rhs HeqWT Hlhs_bound.
  hnf in HeqWT.
  cbn in HeqWT.
  rewrite 2 te_free_varset_tl in HeqWT.
  apply match_correctness_tensorlist with univ; auto.
  - revert Heq.
    clear HeqWT.
    remember ∅ as ml' eqn:Hrem.
    clear Hrem.
    revert ml'.
    induction univ as [|(idx & ty) univ IHuniv]; intros ml'.
    + cbn.
      subst lhs rhs.
      rewrite <- 2 tl_total_semantics_correct.
      rewrite 2 tensorlist_of_tensorexpr_correct.
      easy.
    + cbn.
      intros Hte x.
      apply IHuniv; [now apply NoDup_cons in Hdup|].
      auto.
  - rewrite <- HeqWT.2.2.2.
    apply dom_list_to_map_L.
  - apply HeqWT.
  - rewrite tl_well_typed_correct.
    apply HeqWT.
  - rewrite tl_well_typed_correct.
    apply HeqWT.
Qed.

Definition teeq_correct_aux mabs mg telhs terhs univ :=
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ /\
  NoDup univ.*1 /\
  let lhs := tensorlist_of_tensorexpr telhs in
  let rhs := tensorlist_of_tensorexpr terhs in
  tleq_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) ∅ [])
    (mk_tleq lhs rhs (list_to_map univ)) /\
    all_bound lhs.

Local Open Scope lazy_bool_scope.

(* FIXME: Move *)
Definition teeq_is_correct_aux (mabs : abstypecontext)
  (mg : vartypecontext) telhs terhs univ :=
  bool_decide (NoDup univ.*1) &&&
  let lhs := tensorlist_of_tensorexpr telhs in
  let rhs := tensorlist_of_tensorexpr terhs in
  tleq_is_well_typed_aux mabs mg
    lhs rhs (list_to_map univ) &&&
  Nat.eqb (size (abstracts_bound_vars lhs.(tl_abstracts)))
    (length lhs.(tl_sums)).

Lemma teeq_is_correct_aux_correct_aux (mabs : abscontext) (mg : varcontext)
  telhs terhs univ :
  teeq_is_correct_aux (projT1 <$> mabs) (projT1 <$> mg) telhs terhs univ <->
  NoDup univ.*1 /\
  let lhs := tensorlist_of_tensorexpr telhs in
  let rhs := tensorlist_of_tensorexpr terhs in
  tleq_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) ∅ [])
    (mk_tleq lhs rhs (list_to_map univ)) /\
    all_bound lhs.
Proof.
  cbv delta [teeq_is_correct_aux] beta.
  rewrite lazy_andb_True.
  rewrite bool_decide_spec.
  f_equiv.
  set (lhs := tensorlist_of_tensorexpr telhs).
  set (rhs := tensorlist_of_tensorexpr terhs).
  cbv zeta.
  rewrite lazy_andb_True.
  rewrite (tleq_is_well_typed_aux_correct _ _ ∅ []).
  rewrite Is_true_true.
  rewrite Nat.eqb_eq.
  apply and_iff_from_l; [reflexivity|].
  intros HWT _.
  hnf in HWT.
  cbn in HWT.
  pose proof HWT.1 as HlhsWT%tl_well_typed_correct%tl_well_typed_well_bound.
  unfold tl_well_bound in HlhsWT.
  apply subseteq_size in HlhsWT as Hle.
  rewrite <- lengthN_correct, <- (length_pseq 1), <- (size_list_to_set (C:=Pset))
    by apply NoDup_pseq.
  transitivity (size (list_to_set (pseq 1 (lengthN lhs.(tl_sums))) :> Pset) <=
    size (abstracts_bound_vars lhs.(tl_abstracts))); [lia|].
  unfold all_bound.
  (* transitivity (list_to_set (pseq 1 (lengthN (tl_sums lhs))) ⊆
    abstracts_bound_vars (tl_abstracts lhs)); [|set_solver +HlhsWT]. *)
  split.
  + now apply set_subseteq_size_eq.
  + intros ->.
    easy.
Qed.

Lemma teeq_is_correct_aux_correct {mabs mg telhs terhs univ} :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->
  teeq_is_correct_aux (projT1 <$> mabs) (projT1 <$> mg) telhs terhs univ ->
  teeq_correct_aux mabs mg telhs terhs univ.
Proof.
  unfold teeq_correct_aux.
  intros ? ?%teeq_is_correct_aux_correct_aux; cbv zeta in *; tauto.
Qed.

Definition match_rewrite_tensorexpr tabs tg tl telhs terhs univ tetarg : option tensorexpr :=
  match teeq_is_correct_aux tabs tg telhs terhs univ &&&
    is_well_typed tabs tg tl [] tetarg with
  | false => None
  | true =>
    let lhs := tensorlist_of_tensorexpr telhs in
    let rhs := tensorlist_of_tensorexpr terhs in
    let targ := tensorlist_of_tensorexpr tetarg in
    match match_rewrite_tensorlist lhs rhs targ with
    | None => None
    | Some out => Some (tensorexpr_of_tensorlist out)
    end
  end.

Lemma tl_times_well_typed tc tl tl' :
  tl_well_typed tc (tl_times tl tl') <->
  tl_well_typed tc tl /\ tl_well_typed tc tl'.
Proof.
  rewrite tl_times_spec_defn_correct.
  destruct tl as [lsums labs], tl' as [rsums rabs].
  cbn.
  unfold tl_well_typed_aux; cbn.
  rewrite Forall_app.
  f_equiv.
  - rewrite Forall_fmap.
    apply Forall_iff.
    intros ((f, low), up).
    cbn.
    f_equiv.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v _.
    destruct v; [|reflexivity..].
    cbn.
    rewrite pos_add_N_to_nat, reverse_app, <- app_assoc.
    rewrite lookup_app_r by now rewrite length_reverse; lia.
    rewrite length_reverse.
    f_equal; lia.
  - rewrite Forall_fmap.
    apply Forall_iff.
    intros ((f, low), up).
    cbn.
    f_equiv.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext; intros _ v _.
    destruct v; [|reflexivity..].
    cbn.
    rewrite reverse_app, <- app_assoc.
    case_decide.
    + now rewrite 2 lookup_app_l by now rewrite length_reverse; lia.
    + rewrite 3 lookup_app_r by now rewrite ?length_reverse; lia.
      rewrite ?length_reverse; f_equal; lia.
Qed.

Lemma tl_cons_sum_WT tc ty tl :
  tl_well_typed tc (tl_cons_sum ty tl) <->
  tl_well_typed (tc_cons_type ty tc) tl.
Proof.
  unfold tl_well_typed, tl_well_typed_aux.
  cbn -[reverse].
  apply Forall_iff.
  intros ((f, low), up).
  f_equiv.
  f_equal.
  f_equal.
  f_equal.
  unfold tc_app_types, tc_cons_type; f_equal; try reflexivity.
  rewrite reverse_cons, <- app_assoc.
  reflexivity.
Qed.

Lemma tensorlist_of_tensorexpr_WT tc te :
  well_typed tc te <-> tl_well_typed tc (tensorlist_of_tensorexpr te).
Proof.
  revert tc; induction te; intros tc.
  - cbn.
    unfold tl_well_typed_aux.
    now rewrite Forall_nil.
  - cbn.
    unfold tl_well_typed_aux.
    rewrite Forall_singleton.
    cbn.
    destruct tc; reflexivity.
  - cbn.
    rewrite tl_times_well_typed.
    f_equiv; auto.
  - cbn [tensorlist_of_tensorexpr].
    rewrite tl_cons_sum_WT.
    cbn.
    apply IHte.
Qed.

Lemma match_rewrite_tensorexpr_correct' mabs mg ml telhs terhs univ tetarg :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->
  forall out,
  match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg = Some out ->
  total_semantics mabs mg ml tetarg ==
  total_semantics mabs mg ml out.
Proof.
  intros Hsemeq out.
  cbv delta [match_rewrite_tensorexpr] beta.
  rewrite <- andb_lazy_alt, andb_if.
  case_match eqn:His_correct; [|easy].
  case_match eqn:HWT; [|easy].
  apply Is_true_true in His_correct.
  specialize (teeq_is_correct_aux_correct Hsemeq His_correct) as Hcorr.
  cbv zeta.
  case_match eqn:Hmatch; [|easy].
  intros [= <-].
  specialize (match_correctness_tensorexpr_aux mabs mg ml telhs terhs
    (tensorlist_of_tensorexpr tetarg) univ Hsemeq) as Heq.
  rewrite <- tensorlist_of_tensorexpr_correct, <- tl_total_semantics_correct.
  apply Heq; try apply Hcorr.
  - apply tensorlist_of_tensorexpr_WT.
    apply is_well_typed_correct, Is_true_true.
    apply HWT.
  - easy.
Qed.


Lemma helper_rewrite_in_lhs
  mabs mg ml telhs terhs univ tetarg RHS :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => total_semantics mabs mg ml out == RHS
  | None => False
  end ->
  total_semantics mabs mg ml tetarg == RHS.
Proof.
  intros Hsemeq.
  case_match eqn:Hout; [|easy].
  intros <-.
  eapply match_rewrite_tensorexpr_correct'; eauto.
Qed.

Lemma helper_rewrite_in_rhs
  mabs mg ml telhs terhs univ tetarg LHS :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => LHS == total_semantics mabs mg ml out
  | None => False
  end ->
  LHS == total_semantics mabs mg ml tetarg.
Proof.
  intros Hsemeq.
  case_match eqn:Hout; [|easy].
  intros ->.
  symmetry.
  eapply match_rewrite_tensorexpr_correct'; eauto.
Qed.

Lemma helper_rewrite_in_lhs_or_rhs
  mabs mg ml telhs terhs univ tetarg tetarg' :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => total_semantics mabs mg ml out ==
    total_semantics mabs mg ml tetarg'
  | None =>
    match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
        telhs terhs univ tetarg' with
    | Some out => total_semantics mabs mg ml tetarg ==
      total_semantics mabs mg ml out
    | None => False
    end
  end ->
  total_semantics mabs mg ml tetarg == total_semantics mabs mg ml tetarg'.
Proof.
  intros Hsemeq.
  case_match eqn:Hout; [intros Hhyp;
    eapply helper_rewrite_in_lhs; [eassumption|]; now rewrite Hout|].
  now apply helper_rewrite_in_rhs.
Qed.


Lemma helper_rewrite_in_lhs'
  mabs mg ml telhs terhs univ tetarg RHS :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  (forall sem RHS', sem = total_semantics_aux mabs mg ml [] -> RHS' = RHS ->
  match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => sem out == RHS'
  | None => False
  end) ->
  total_semantics mabs mg ml tetarg == RHS.
Proof.
  intros Hsemeq Hmatch.
  eapply helper_rewrite_in_lhs; [eauto|].
  now apply Hmatch.
Qed.

Lemma helper_rewrite_in_rhs'
  mabs mg ml telhs terhs univ tetarg LHS :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  (forall sem LHS', sem = total_semantics_aux mabs mg ml [] -> LHS' = LHS ->
  match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => LHS' == sem out
  | None => False
  end) ->
  LHS == total_semantics mabs mg ml tetarg.
Proof.
  intros Hsemeq Hmatch.
  eapply helper_rewrite_in_rhs; [eauto|].
  now apply Hmatch.
Qed.

Lemma helper_rewrite_in_lhs_or_rhs'
  mabs mg ml telhs terhs univ tetarg tetarg' :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->

  (forall sem, sem = total_semantics_aux mabs mg ml [] -> match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg with
  | Some out => sem out ==
    sem tetarg'
  | None =>
    match match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
        telhs terhs univ tetarg' with
    | Some out => sem tetarg ==
      sem out
    | None => False
    end
  end) ->
  total_semantics mabs mg ml tetarg == total_semantics mabs mg ml tetarg'.
Proof.
  intros Hsemeq Hmatch.
  eapply helper_rewrite_in_lhs_or_rhs; [eauto|].
  now apply Hmatch.
Qed.












Lemma tl_total_semantics_aux_ext_abs mabs mg ml mr sums abs abs' :
  (forall mr' : Vlist sums, WF_Vlist mr' ->
  Forall2 (fun '(f, low, up) '(f', low', up') =>
    abstract_semantics mabs mg ml (rev_append mr' mr) f low up ==
    abstract_semantics mabs mg ml (rev_append mr' mr) f' low' up')
    abs abs') ->
  tl_total_semantics_aux mabs mg ml mr sums abs ==
  tl_total_semantics_aux mabs mg ml mr sums abs'.
Proof.
  intros Heq.
  rewrite 2 tl_total_semantics_aux_alt_Vlist.
  apply sum_of_ext'.
  intros mr' Hmr'%elem_of_Vlist_elements.
  cbn.
  apply Rlist_prod_ext.
  rewrite Forall2_fmap.
  eapply Forall2_impl; [apply (Heq mr' Hmr')|].
  now intros [[]] [[]].
Qed.

(* FIXME: Move to top*)
Import Tensor.

Let Tensor := (@Tensor R).
Let DimensionlessTensor := (@DimensionlessTensor R).

Fixpoint tensor_to_V_n_args_aux (k : nat) {n A}
   : forall (t : vec (V k) n -> A),
  V_n_args (replicate n k) A :=
  match n with
  | O => fun t => t [#]
  | S n' => fun t =>
    fun a => tensor_to_V_n_args_aux k (t ∘ vcons a)
  end.

Definition tensor_to_V_n_args (k : nat)
  {n m A} (t : vec (V k) n -> vec (V k) m -> A) :=
  tensor_to_V_n_args_aux k (uncurry t ∘ Vector.splitat n).

Let BTensor := {knm : nat * (nat * nat) &
  Tensor knm.2.1 knm.2.2 (V knm.1)}.

Local Definition sigT2pair `{P : A -> Type} (ap : sigT P) : A * (P (projT1 ap)) :=
  (projT1 ap, projT2 ap).

#[local] Coercion sigT2pair : sigT >-> prod.

Definition mabs_of_tensor_map (mabst : Pmap BTensor) : abscontext :=
  (λ knm_T,
  mk_Vfunc _ (tensor_to_V_n_args _ (projT2 knm_T))) <$> mabst.


Fixpoint Vapplys_replicate_vec {A n k} : V_n_args (replicate n k) A ->
  vec (V k) n -> A :=
  match n with
  | O => fun f _ => f
  | S n' =>
    fun f v =>
    Vapplys_replicate_vec (f (Vector.hd v)) (Vector.tl v)
  end.

Lemma Vapplys_replicate_vec_correct {n k} (f : V_n_args (replicate n k) R) args :
  Vapplys (mk_Vfunc _ f) args =
  kargs ← join_list (A_get k <$> args);
  vargs ← list2vec n kargs;
  Some (Vapplys_replicate_vec f vargs).
Proof.
  unfold mk_Vfunc.
  revert f args; induction n;
  intros f args.
  - destruct args as [|v args]; [reflexivity|].
    cbn.
    case_match; [|reflexivity].
    cbn.
    destruct (join_list _); reflexivity.
  - destruct args as [|v args]; [reflexivity|].
    cbn.
    case_match; [|reflexivity].
    cbn.
    rewrite IHn.
    rewrite option_bind_assoc.
    unfold compose.
    cbn.
    apply option_bind_ext; [|reflexivity].
    intros ls.
    rewrite option_fmap_bind.
    reflexivity.
Qed.


Lemma Vapplys_replicate_vec_tensor_to_V_n_args_aux {k n A}
  (t : vec (V k) n -> A) v :
  Vapplys_replicate_vec (tensor_to_V_n_args_aux k t) v
  = t v.
Proof.
  induction v; [reflexivity|].
  apply IHv.
Qed.

Lemma Vapplys_replicate_vec_tensor_to_V_n_args {k n m}
  (t : vec (V k) n -> vec (V k) m -> R) v :
  Vapplys_replicate_vec (tensor_to_V_n_args k t) v
  = uncurry t (Vector.splitat _ v).
Proof.
  unfold tensor_to_V_n_args.
  now rewrite Vapplys_replicate_vec_tensor_to_V_n_args_aux.
Qed.



Lemma abstract_semantics_mabs_of_tensor_map_gen mabst mg ml mr f low up :
  abstract_semantics (mabs_of_tensor_map mabst) mg ml mr f low up =
  default rO (
    knm_T ← (mabst !! f :> option BTensor);
    ins' ← join_list (mbind (A_get knm_T.1.1) <$> (get_var mg ml mr <$> low));
    outs' ← join_list (mbind (A_get knm_T.1.1) <$> (get_var mg ml mr <$> up));
    '(ins, outs) ← Vector.splitat _ <$> list2vec (knm_T.1.2.1 + knm_T.1.2.2) (ins' ++ outs');
    Some ((projT2 (knm_T :> BTensor)) ins outs)
  ).
Proof.
  unfold abstract_semantics.
  unfold mabs_of_tensor_map.
  rewrite lookup_fmap.
  rewrite_strat (outermost option_fmap_bind).
  rewrite option_bind_comm.
  change ({knm : Ty * (Ty * Ty) &
            Tensor knm.2.1 knm.2.2 (V knm.1)}) with BTensor.
  destruct (mabst !! f) as [knm_T|] eqn:HT; [cbn|reflexivity].
  rewrite fmap_app, join_list_app.
  rewrite option_bind_assoc'.
  rewrite 2 join_list_fmap_mbind.
  destruct (join_list (_ <$> low)) as [llow|] eqn:Hllow; [cbn|reflexivity].
  destruct (join_list (_ <$> up)) as [lup|] eqn:Hlup; [cbn|cbn; now rewrite option_bind_None_r].
  rewrite Vapplys_replicate_vec_correct.
  rewrite fmap_app, join_list_app, option_bind_assoc'.
  destruct (join_list (_ <$> llow)) as [klow|] eqn:Hklow; [cbn|reflexivity].
  destruct (join_list (_ <$> lup)) as [kup|] eqn:Hkup; [cbn|reflexivity].
  destruct (list2vec _ _) as [args|] eqn:Hargs; [cbn|reflexivity].
  rewrite Vapplys_replicate_vec_tensor_to_V_n_args.
  now destruct (Vector.splitat _ _).
Qed.

Lemma abstract_semantics_mabs_of_tensor_map mabst mg ml mr f low up :
  snd ∘ projT1 <$> (mabst !! f) = Some (length low, length up) ->
  abstract_semantics (mabs_of_tensor_map mabst) mg ml mr f low up =
  default rO (
    knm_T ← (mabst !! f :> option BTensor);
    ins' ←
      join_list (mbind (A_get knm_T.1.1) <$> (get_var mg ml mr <$> low));
    ins ← list2vec (knm_T.1.2.1) ins';
    outs' ←
      join_list (mbind (A_get knm_T.1.1) <$> (get_var mg ml mr <$> up));
    outs ← list2vec (knm_T.1.2.2) outs';
    Some ((projT2 (knm_T :> BTensor)) ins outs)
  ).
Proof.
  intros Habst.
  rewrite abstract_semantics_mabs_of_tensor_map_gen.
  destruct (mabst !! f) as [[[k nm] T]|] eqn:HT; [cbn|reflexivity].
  cbn in Habst.
  revert Habst.
  intros [= ->].
  destruct (join_list (_ <$> (_ <$> low))) as [largs|] eqn:Hlargs; [cbn|reflexivity].
  apply join_list_Some_length in Hlargs as Hlenl.
  rewrite 2 length_fmap in Hlenl.
  rewrite (option_bind_comm _ (list2vec _ _)).
  destruct (join_list (_ <$> (_ <$> up))) as [uargs|] eqn:Huargs; [cbn|reflexivity].
  apply join_list_Some_length in Huargs as Hlenu.
  rewrite 2 length_fmap in Hlenu.
  rewrite (list2vec_app' (eq_sym Hlenl) (eq_sym Hlenu)).
  cbn.
  rewrite Vector.splitat_append.
  rewrite (list2vec_length' (eq_sym Hlenl)).
  rewrite (list2vec_length' (eq_sym Hlenu)).
  reflexivity.
Qed. *)



(*
Lemma abstract_semantics'_abstracts_perm_eq_permutative_tensor
  (mabst : Pmap BTensor) mg ml mr
  abs abs' :
  abst_WT' (snd ∘ projT1 <$> mabst) abs ->
  (forall t : BTensor, mabst !! abs.1.1 = Some t ->
    permutative_tensor (projT2 t)) ->
  abstracts_perm_eq abs abs' ->
  abstract_semantics' (mabs_of_tensor_map mabst) mg ml mr abs ==
  abstract_semantics' (mabs_of_tensor_map mabst) mg ml mr abs'.
Proof.
  intros HWT Hpermtens Habs.
  pose proof HWT as HWT'.
  rewrite Habs in HWT'.
  rewrite 2 abstract_semantics_mabs_of_tensor_map by
    now rewrite <- lookup_fmap.
  destruct abs as ((f, low), up), abs' as ((f', low'), up').
  cbn in *.
  destruct Habs as ([= <-] & Hlow & Hup).
  cbn in Hlow, Hup.
  destruct (mabst !! f) as [[[k nm] t]|] eqn:Ht in |- *; [cbn|reflexivity].
  specialize (Hpermtens _ Ht).
  cbn in Hpermtens.

  (* pose proof (join_list_is_Some (mbind (A_get k) <$> (get_var mg ml mr <$> low)))
    as Hjoinlow.
  rewrite Hlow in Hjoinlow at 2.
  rewrite <- join_list_is_Some in Hjoinlow.
  rewrite 2 is_Some_alt in Hjoinlow. *)
  pose proof (join_list_Permutation
    (mbind (A_get k) <$> (get_var mg ml mr <$> low))
    (mbind (A_get k) <$> (get_var mg ml mr <$> low'))
    ltac:(now rewrite Hlow)) as Hlperm%option_Forall2_alt.
  pose proof (join_list_Permutation
    (mbind (A_get k) <$> (get_var mg ml mr <$> up))
    (mbind (A_get k) <$> (get_var mg ml mr <$> up'))
    ltac:(now rewrite Hup)) as Huperm%option_Forall2_alt.
  destruct (join_list (_ <$> (_ <$> low))) as [largs|] eqn:Hlargs;
  destruct (join_list (_ <$> (_ <$> low'))) as [largs'|] eqn:Hlargs';
  [cbn|easy..|reflexivity].
  pose proof (list2vec_Permutation nm.1 _ _ Hlperm) as Hlvperm%option_Forall2_alt.
  destruct (list2vec _ largs) as [lvargs|] eqn:Hlvargs;
  destruct (list2vec _ largs') as [lvargs'|] eqn:Hlvargs';
  [cbn|easy..|reflexivity].
  destruct (join_list (_ <$> (_ <$> up))) as [uargs|] eqn:Huargs;
  destruct (join_list (_ <$> (_ <$> up'))) as [uargs'|] eqn:Huargs';
  [cbn|easy..|reflexivity].
  pose proof (list2vec_Permutation nm.2 _ _ Huperm) as Huvperm%option_Forall2_alt.
  destruct (list2vec _ uargs) as [uvargs|] eqn:Huvargs;
  destruct (list2vec _ uargs') as [uvargs'|] eqn:Huvargs';
  [cbn|easy..|reflexivity].
  now apply Hpermtens.
Qed.


Import SetoidList SetoidPermutation list.

Lemma tl_total_semantics_aux_base_eq mabs mg ml mr abs :
  tl_total_semantics_aux mabs mg ml mr [] abs =
  Rlist_prod ((λ a, abstract_semantics' mabs mg ml mr a) <$> abs).
Proof.
  cbn; f_equal.
  apply list_fmap_ext; now intros _ [[]] _.
Qed.

Lemma tl_perm_eq_correct_permutative_aux
  (mabst : Pmap BTensor) mg ml mr sums abs abs' :
  PermutationA abstracts_perm_eq abs abs' ->
  Forall (abst_WT' (snd ∘ projT1 <$> mabst)) abs ->
  (forall (f : Idx), f ∈ abstracts_indices abs -> forall (t : BTensor),
    mabst !! f = Some t ->
    permutative_tensor (projT2 t)) ->
  tl_total_semantics_aux (mabs_of_tensor_map mabst) mg ml mr sums abs ==
  tl_total_semantics_aux (mabs_of_tensor_map mabst) mg ml mr sums abs'.
Proof.
  intros Habs HWT Hperm.
  revert mr; induction sums as [|ty sums IHsums]; intros mr;
  [|now cbn; apply sum_of_ext; intros; apply IHsums].
  rewrite 2 tl_total_semantics_aux_base_eq.
  apply Rlist_prod_perm_mor.
  apply PermutationA_decompose in Habs as (abs'' & Habs_abs'' & Habs''_abs'); [|apply _].
  etransitivity;
  [apply Permutation_PermutationA, fmap_Permutation, Habs_abs''; apply _|].
  unfold abstracts_indices in Hperm.
  setoid_rewrite Habs_abs'' in Hperm.
  rewrite Habs_abs'' in HWT.
  clear abs Habs_abs''.
  apply eqlistA_PermutationA.
  induction Habs''_abs'; [reflexivity|].
  cbn.
  constructor.
  - apply abstract_semantics'_abstracts_perm_eq_permutative_tensor;
    [now apply Forall_cons in HWT | | easy].
    apply Hperm.
    set_solver +.
  - apply IHHabs''_abs'; [now apply Forall_cons in HWT|].
    intros f Hf.
    apply Hperm; set_solver +Hf.
Qed.



Lemma tl_perm_eq_correct_permutative (mabst : Pmap BTensor) mg ml tl tl' :
  tl ≡tl≡ₚ tl' ->
  Forall (abst_WT' (snd ∘ projT1 <$> mabst)) tl.(tl_abstracts) ->
  (forall (f : Idx), f ∈ abstracts_indices tl.(tl_abstracts) ->
    forall (t : BTensor), mabst !! f = Some t ->
    permutative_tensor (projT2 t)) ->
  tl_total_semantics (mabs_of_tensor_map mabst) mg ml tl ==
  tl_total_semantics (mabs_of_tensor_map mabst) mg ml tl'.
Proof.
  destruct tl as [sums abs], tl' as [sums' abs'].
  intros [[= <-] Habs].
  cbn -[abstracts_indices] in *.
  intros HWT Hperm.
  now apply tl_perm_eq_correct_permutative_aux.
Qed. *)


Definition abstracts_semantics mabs ml mr abs :=
  Rlist_prod ((λ '(f, low, up), abstract_semantics mabs ml mr f low up)
    <$> abs).

Definition abstracts_semantics_alt mabs ml mr abs :=
  Rlist_prod ((λ '(f, low, up), abstract_semantics_alt mabs ml mr f low up)
    <$> abs).

Definition deltas_semantics ml mr delt :=
  Rlist_prod ((λ '(l, u), delta_semantics ml mr l u)
    <$> delt).

Definition deltas_semantics_alt ml mr delt :=
  Rlist_prod ((λ '(l, u), delta_semantics_alt ml mr l u)
    <$> delt).

Definition ntl_total_semantics mabs ml ntl :=
  tl_total_semantics mabs ml (ntl2tl ntl).

Lemma tl_total_semantics_alt_aux_eq mabs ml mr abs delt :
  tl_total_semantics_alt_aux mabs ml mr abs delt =
  ∑ mr : Vmap mr,
    abstracts_semantics_alt mabs ml mr abs *
    deltas_semantics_alt ml mr delt.
Proof.
  reflexivity.
Qed.

Lemma ntl_total_semantics_alt mabs ml ntl :
  WF_ntl ntl ->
  ntl_total_semantics mabs ml ntl ==
  ∑ mr : Vmap ntl.(ntl_sums),
  abstracts_semantics_alt mabs ml mr ntl.(ntl_abstracts) *
  deltas_semantics_alt ml mr ntl.(ntl_deltas).
Proof.
  intros Hwf.
  unfold ntl_total_semantics.
  unfold tl_total_semantics.
  rewrite tl_total_semantics_alt_aux_correct.
  destruct ntl as [isums abs delt]; cbn -[reverse abstracts_semantics_alt].
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

  rewrite (tl_total_semantics_alt_aux_relabel _ _ _ g).
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

Lemma tl2ntl_correct mabs ml tl :
  WF_tl tl ->
  ntl_total_semantics mabs ml (tl2ntl tl) ==
  tl_total_semantics mabs ml tl.
Proof.
  intros Hwf.
  rewrite ntl_total_semantics_alt by now apply tl2ntl_WF.
  unfold tl_total_semantics.
  rewrite tl_total_semantics_alt_aux_correct.
  now destruct tl.
Qed.

Lemma ntl2tl_correct mabs ml ntl :
  tl_total_semantics mabs ml (ntl2tl ntl) ==
  ntl_total_semantics mabs ml ntl.
Proof.
  reflexivity.
Qed.

(*
Lemma ntl_perm_eq_correct_permutative mabst mg ml ntl ntl' :
  ntl ≡ntl≡ₚ ntl' ->
  Forall (abst_WT' (snd ∘ projT1 <$> mabst)) ntl.(ntl_abstracts) ->
  (forall (f : Idx), f ∈ abstracts_indices ntl.(ntl_abstracts) ->
    forall (t : BTensor), mabst !! f = Some t ->
    permutative_tensor (projT2 t)) ->
  ntl_total_semantics (mabs_of_tensor_map mabst) mg ml ntl ==
  ntl_total_semantics (mabs_of_tensor_map mabst) mg ml ntl'.
Proof.
  intros Heq Hall Hperm.
  apply ntl2tl_perm_eq in Heq as Heq'.
  unfold ntl_total_semantics.
  apply tl_perm_eq_correct_permutative; [easy|..|now rewrite abstracts_indices_ntl2tl].
  now specialize (ntl2tl_abst_WT'_all2 (snd ∘ projT1 <$> mabst) ntl)
    as Hiff%Forall2_iff_pred; apply Hiff.
Qed. *)

Lemma ntl_aeq_correct mabs ml ntl ntl' :
  WF_ntl ntl ->
  ntl =ntl= ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros Hntl Heq.
  apply ntl_aeq_WF in Heq as Hntl'; [|easy].
  unfold ntl_total_semantics.
  apply tl_aeq_correct.
  now apply ntl2tl_aeq.
Qed.

Lemma ntl_delta_idemp_correct mabs ml ntl ntl' v :
  WT_ntl (dom ml) ntl -> WT_ntl (dom ml) ntl' ->
  ntl_delta_idemp v ntl ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros HWT HWT' Hidemp.
  hnf in Hidemp.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn -[ntl2tl] in *.
  rewrite 2 ntl_total_semantics_alt by first [apply HWT|apply HWT'].
  cbn [ntl_sums ntl_abstracts ntl_deltas].
  destruct Hidemp as (<- & -> & ->).
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  cbn [deltas_semantics_alt fmap list_fmap Rlist_prod].
  enough (delta_semantics_alt ml mr v v == 1) as Heq
    by now unfold deltas_semantics_alt; ring [Heq].
  destruct v as [r|l].
  - cbn.
    assert (Hr : r ∈ dom mr). 1:{
      rewrite Hmr.1.
      apply HWT'.2.2.2.2.
      set_solver +.
    }
    unfold Vmap in *.
    apply elem_of_dom in Hr as [a Ha].
    rewrite Ha.
    cbn.
    apply eq_reflexivity, delta_tensor_eq.
  - cbn.
    assert (Hl : l ∈ dom ml). 1:{
      apply HWT'.2.1.
      set_solver +.
    }
    unfold Vmap in *.
    apply elem_of_dom in Hl as [a Ha].
    rewrite Ha.
    cbn.
    apply eq_reflexivity, delta_tensor_eq.
Qed.

(* Lemma Vmap_elements_cons_alt ty tys :
  Vmap_elements ty tys  *)

Lemma sum_of_Vmap_cons ty tys f :
  ∑ mr : Vmap (ty :: tys), f mr ==
  ∑ mr' : Vmap tys, ∑ vty : A, f (<[ty := vty]> mr').
Proof.
  unfold_sum_of.
  cbn.
  rewrite list_bind_fmap.

  rewrite Rlist_sum_bind.
  apply Rlist_sum_ext, Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros mr Hmr%elem_of_Vmap_elements_1.
  rewrite <- list_fmap_compose.
  reflexivity.
Qed.

Lemma deltas_semantics_alt_cons ml mr lu delt :
  deltas_semantics_alt ml mr (lu :: delt) =
  delta_semantics_alt ml mr lu.1 lu.2 *
  deltas_semantics_alt ml mr delt.
Proof.
  now destruct lu.
Qed.

Context {HAWF : WFSummable A}.




Lemma abstracts_semantics_alt_ext mabs ml mr mabs' ml' mr'
  abs abs' :
  Forall2 (fun '(idx, lower, upper) '(idx', lower', upper') =>
    mabs !! idx = mabs' !! idx' /\
  (get_var_alt ml mr) <$> lower = (get_var_alt ml' mr') <$> lower' /\
  (get_var_alt ml mr) <$> upper = (get_var_alt ml' mr') <$> upper') abs abs' ->
  abstracts_semantics_alt mabs ml mr abs =
  abstracts_semantics_alt mabs' ml' mr' abs'.
Proof.
  intros Hall2.
  unfold abstracts_semantics_alt.
  f_equal.
  apply list_eq_Forall2, Forall2_fmap.
  apply (Forall2_impl _ _ _ _ Hall2).
  intros [[f low] up] [[f' low'] up'].
  intros (?&?&?); now apply abstract_semantics_alt_ext.
Qed.

Lemma deltas_semantics_alt_ext ml mr ml' mr' delt delt' :
  Forall2 (fun '(l, u) '(l', u') =>
  (get_var_alt ml mr) l = (get_var_alt ml' mr') l' /\
  (get_var_alt ml mr) u = (get_var_alt ml' mr') u') delt delt' ->
  deltas_semantics_alt ml mr delt =
  deltas_semantics_alt ml' mr' delt'.
Proof.
  intros Hall2.
  unfold deltas_semantics_alt.
  f_equal.
  apply list_eq_Forall2, Forall2_fmap.
  apply (Forall2_impl _ _ _ _ Hall2).
  intros [l u] [l' u'].
  intros (?&?); now apply delta_semantics_alt_ext.
Qed.

Lemma ntl_delta_subst_correct mabs ml ntl ntl' lb r :
  map_Forall (λ _ a, SummedElement a) ml ->
  WT_ntl (dom ml) ntl -> WT_ntl (dom ml) ntl' ->
  ntl_delta_subst lb r ntl ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros Hml Hwt Hwt' Hsubst.
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

  etransitivity; [apply ntl_aeq_correct; [apply Hwt|apply Heq]|].

  rewrite ntl_total_semantics_alt by now
    apply (ntl_aeq_WF _ _ Heq), Hwt.
  rewrite ntl_total_semantics_alt by apply Hwt'.
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  rewrite sum_of_Vmap_cons.
  apply sum_of_ext'; intros mr' Hmr'%elem_of_Vmap_elements_1.
  assert (Hr : exists ar, get_var_alt ml mr' r = Some ar /\
    SummedElement ar). 1:{
    destruct r as [r|l].
    - cbn.
      assert (r ∈ dom mr') as Hdom.
      + pose proof Hmr'.1 as Hdom.
        unfold Vmap in *.
        rewrite Hdom.
        assert (Hne' : r ≠ lb) by congruence.
        enough (r ∈@{Pset} list_to_set (lb :: sums')) as Hen by
          now rewrite elem_of_list_to_set in Hen |- *;
            rewrite elem_of_cons in Hen; clear -Hne' Hen; firstorder congruence.
        rewrite <- Hsums.
        apply Hwt.2.2.2.2.
        set_solver +.
      + unfold Vmap in Hdom.
        apply elem_of_dom in Hdom as [ar Har].
        exists ar.
        split; [easy|].
        specialize (Hmr'.2 r ar Har) as Harsum.
        now constructor.
    - cbn.
      assert (l ∈ dom ml) as Hdom.
      + apply Hwt.2.1.
        set_solver +.
      + apply elem_of_dom in Hdom as [ar Har].
        specialize (Hml l ar Har).
        eauto.
  }
  assert (Hgetr : forall a, get_var_alt ml (<[lb:=a]> mr') r =
    get_var_alt ml mr' r). 1:{
    intros a.
    destruct r as [r|]; [|easy].
    cbn.
    unfold Vmap.
    apply lookup_insert_ne; congruence.
  }
  destruct Hr as (ar & Har & Harsum).
  erewrite (sum_of_ext _ (fun a => delta_tensor [#a] [#ar] *
    (abstracts_semantics_alt mabs ml (<[lb:=a]> mr') abs *
    deltas_semantics_alt ml (<[lb:=a]> mr') delt))). 2:{
    intros a.
    rewrite deltas_semantics_alt_cons.
    unfold delta_semantics_alt.
    cbn [fst snd get_var_alt].
    unfold Vmap.
    rewrite lookup_insert.
    cbn [mbind option_bind from_option id].
    rewrite Hgetr, Har.
    cbn.
    ring.
  }
  rewrite sum_of_delta_l_1.
  cbn.
  f_equiv.
  - apply eq_reflexivity.
    unfold Vmap.
    apply abstracts_semantics_alt_ext, Forall2_fmap_r, Forall_Forall2_diag.
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
  - apply eq_reflexivity, deltas_semantics_alt_ext, Forall2_fmap_r, Forall_Forall2_diag.
    rewrite Forall_forall; intros [l u] Hlu.
    cbn.
    unfold Vmap.
    split;
    [rename l into v|rename u into v];
    (destruct v as [vr|vl]; [|reflexivity]);
    cbn;
    rewrite lookup_insert_case, fn_lookup_singleton_case;
    now case_decide as Hvr_lb;
    [rewrite decide_True by congruence|rewrite decide_False by congruence].
Qed.


Lemma delta_semantics_alt_comm ml mr v v' :
  delta_semantics_alt ml mr v v' =
  delta_semantics_alt ml mr v' v.
Proof.
  unfold delta_semantics_alt.
  destruct (get_var_alt ml mr v), (get_var_alt ml mr v'); [|done..].
  cbn.
  apply delta_tensor_comm.
Qed.

Lemma ntl_delta_perm_eq_correct mabs ml ntl ntl' :
  WF_ntl ntl -> WF_ntl ntl' ->
  ntl_delta_perm_eq ntl ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros HWF HWF' Heq.
  rewrite 2 ntl_total_semantics_alt by easy.
  hnf in Heq.
  destruct ntl as [sums abs delt], ntl' as [sums' abs' delt'];
  cbn [ntl_sums ntl_abstracts ntl_deltas] in *.
  destruct Heq as (<- & <- & Hdelt).
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  f_equiv.
  unfold deltas_semantics_alt.
  apply Rlist_prod_perm_mor.
  clear HWF HWF'.
  induction Hdelt as [|? ? ? ? Heq | |].
  - done.
  - cbn.
    f_equiv; [|easy].
    do 2 case_match.
    rewrite prod_swap_eq_pair in Heq.
    destruct Heq as [[-> ->]|[-> ->]]; [done|].
    apply eq_reflexivity, delta_semantics_alt_comm.
  - apply (Permutation_PermutationA _).
    solve_Permutation.
  - now etransitivity; eassumption.
Qed.





Lemma ntl_delta_eq_correct mabs ml ntl ntl' :
  map_Forall (λ _ a, SummedElement a) ml ->
  WT_ntl (dom ml) ntl ->
  ntl_delta_eq (dom ml) ntl ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros Hml HWF Heq.
  assert (HWF' : WT_ntl (dom ml) ntl') by now
    eapply ntl_delta_eq_WT; eauto.
  induction Heq.
  - eapply ntl_delta_idemp_correct; eauto.
  - eapply ntl_delta_subst_correct; eauto.
  - eapply ntl_delta_perm_eq_correct; solve [eauto|apply HWF|apply HWF'].
  - symmetry; eauto.
  - assert (WT_ntl (dom ml) ntl') by now eapply ntl_delta_eq_WT; eauto.
    etransitivity; [apply IHHeq1|apply IHHeq2]; easy.
Qed.



Lemma ntl_eq_correct mabs ml ntl ntl' :
  map_Forall (λ _ a, SummedElement a) ml ->
  WT_ntl (dom ml) ntl -> (* WT_ntl (dom ml) ntl' -> *)
  ntl_eq (dom ml) ntl ntl' ->
  ntl_total_semantics mabs ml ntl ==
  ntl_total_semantics mabs ml ntl'.
Proof.
  intros Hml HWF Heq.
  induction Heq as [|ntl ntl' ntl'' Hntl Hrtc IHntl]; [done|].
  hnf in Hntl.
  assert (Hntl' : WT_ntl (dom ml) ntl'). 1:{
    destruct Hntl as [Hntl|Hntl];
    [eapply ntl_aeq_WT|eapply ntl_delta_eq_WT];
    eauto; now symmetry.
  }
  etransitivity; [|apply IHntl; easy].
  destruct Hntl as [Hntl|Hntl].
  - apply ntl_aeq_correct; easy + apply HWF.
  - apply ntl_delta_eq_correct; easy.
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

(* Semantics of a tensorexpr as a (dimensioned) tensor, based on
  vectors of input and output vertices *)
Definition tensorexpr_to_tensor (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (te : tensorexpr) : @Tensor R n m A :=
  fun ins outs =>
    total_semantics mabs (make_vecs_map inputs outputs ins outs) te.


Definition tensorlist_to_tensor (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (tl : tensorlist) : @Tensor R n m A :=
  fun ins outs =>
    tl_total_semantics mabs (make_vecs_map inputs outputs ins outs) tl.

Definition namedtensorlist_to_tensor (mabs : abscontext)
  {n m} (inputs : vec Idx n) (outputs : vec Idx m)
    (ntl : namedtensorlist) : @Tensor R n m A :=
  fun ins outs =>
    ntl_total_semantics mabs (make_vecs_map inputs outputs ins outs) ntl.

Definition tl_subst_free (l : Idx) (tl : tensorlist) :=
  tl_add_sums 1 (relabel_tl
    (var_elim (bound ∘ Pos.succ)
    (λ l', if decide (l' = l) then bound 1 else free l')) tl).

Lemma tl_total_semantics_tl_subst_free mabs ml l tl :
  tl_total_semantics mabs ml (tl_subst_free l tl) ==
  ∑ a : A, tl_total_semantics mabs (<[l:=a]> ml) tl.
Proof.
  destruct tl as [sums abs delt].
  rewrite tl_total_semantics_alt_vec.
  cbn [tl_subst_free tl_add_sums relabel_tl tl_sums tl_abstracts tl_deltas].
  rewrite sum_of_vec_succ.
  apply sum_of_ext'.
  intros a Ha.
  rewrite (tl_total_semantics_alt_vec _ _ (mk_tl sums abs delt)).
  cbn [tl_sums tl_abstracts tl_deltas].
  apply sum_of_ext'; intros m Hm.
  apply tl_total_semantics_aux_ext_base.
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

Lemma list_find_app `(P : X -> Prop) `{forall x, Decision (P x)} (l l' : list X) :
  list_find P (l ++ l') =
  list_find P l ∪ (prod_map (Nat.add (length l)) id <$> list_find P l').
Proof.
  induction l.
  - cbn.
    rewrite option_union_left_id.
    symmetry.
    etransitivity; [|apply option_fmap_id].
    apply option_fmap_ext; now intros [].
  - cbn.
    case_decide; [now rewrite union_Some_l|].
    rewrite IHl.
    destruct (list_find P l) as [[]|].
    + cbn.
      now rewrite 2 union_Some_l.
    + cbn.
      rewrite 2 option_union_left_id.
      rewrite <- option_fmap_compose.
      reflexivity.
Qed.


Definition compose_tensorlist (mids : list Idx) (l r : tensorlist) : tensorlist :=
  tl_add_sums (length mids) (relabel_tl
    (var_elim (bound ∘ (λ p, pos_add_N p (lengthN mids))) (λ fr,
      from_option (bound ∘ Pos.of_succ_nat ∘ (λ n, (length mids - S n)%nat))
      (free fr) (list_index fr mids))) (tl_times l r)).

Lemma compose_tensorlist_foldr mids l r :
  compose_tensorlist mids l r =
  foldr (fun mid tl => tl_subst_free mid tl) (tl_times l r) (reverse mids).
Proof.
  unfold compose_tensorlist.
  set (lr := tl_times l r).
  generalize lr.
  clear l r lr.
  induction mids; intros lr.
  - cbn.
    apply tl_ext; cbn; [reflexivity|..];
    apply list_fmap_id'; intros ? _;
    [apply relabel_abs_id'|apply relabel_delt_id'];
    intros []; done.
  - rewrite reverse_cons, foldr_app.
    cbn.
    rewrite <- IHmids.
    apply tl_ext; [cbn; lia|..];
    cbn;
    rewrite <- list_fmap_compose;
    apply list_fmap_ext; intros _ ? _; cbn;
    [rewrite relabel_abs_compose; apply relabel_abs_ext|
     rewrite relabel_delt_compose; apply relabel_delt_ext];
    (intros [r'|l']; [f_equal/=; lia|]);
    (cbn;
    case_decide as Hl'; cbn;
    [rewrite lengthN_correct_rev; f_equal; lia|];
    unfold list_index;
    destruct (list_find _ _) as [[n ?]|]; done).
Qed.


Lemma tl_total_semantics_compose_tensorlist_aux mabs ml mids (l r : tensorlist) :
  tl_total_semantics mabs ml (compose_tensorlist mids l r) ==
  ∑ rmi : vec A (length (reverse (reverse mids))),
    tl_total_semantics mabs (list_to_map (zip mids rmi) ∪ ml) (tl_times l r).
Proof.
  rewrite compose_tensorlist_foldr.
  erewrite sum_of_ext by now intros;
    replace (zip mids) with (zip_with (B:=A) pair (reverse (reverse mids))) by (now rewrite (reverse_involutive mids));
    refine (reflexivity _).
  cbv beta.
  generalize (reverse mids) as rmids.
  clear mids.
  intros mids.
  revert ml;
  induction mids as [|mid mids IHmid]; intros ml.
  - rewrite sum_of_vec_0.
    cbn.
    now rewrite map_empty_union.
  - cbn [foldr].
    unshelve (rewrite (sum_of_vec_cast (m:=length (reverse mids) + 1))).
    1: {
      abstract (rewrite reverse_cons, length_app at 1; cbn;
      exact eq_refl).
    }
    setoid_rewrite vec_to_list_cast.
    rewrite sum_of_vec_add, sum_of_comm.
    rewrite tl_total_semantics_tl_subst_free.
    rewrite sum_of_vec_1.
    apply sum_of_ext'; intros a Ha.
    rewrite IHmid.
    apply sum_of_ext; intros mr.
    f_equiv.
    rewrite reverse_cons, vec_to_list_app.
    rewrite zip_with_app by now rewrite length_vec_to_list.
    rewrite list_to_map_app.
    cbn.
    rewrite <- map_union_assoc.
    now rewrite <- insert_union_l, map_empty_union.
Qed.

(* FIXME: Move *)
Definition tl_free_varset (tl : tensorlist) : Pset :=
  abstracts_free_vars tl.(tl_abstracts) ∪
  deltas_free_vars tl.(tl_deltas).

Lemma tl_total_semantics_free_varset_ext mabs ml ml' tl :
  (forall l, l ∈ tl_free_varset tl -> ml !! l = ml' !! l) ->
  tl_total_semantics mabs ml tl == tl_total_semantics mabs ml' tl.
Proof.
  intros Hml.
  rewrite 2 tl_total_semantics_alt_vec.
  apply sum_of_ext; intros mr.
  apply tl_total_semantics_aux_ext_base;
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

Lemma compose_tensorlist_correct mabs {n m o} (ins : vec Idx n)
  (mids : vec Idx m) (outs : vec Idx o) (ltl rtl : tensorlist) :
  ins ##@{list _} mids ->
  mids ##@{list _} outs ->
  ins ##@{list _} outs ->
  tl_free_varset ltl ⊆ list_to_set (ins ++ mids) ->
  tl_free_varset rtl ⊆ list_to_set (mids ++ outs) ->
  tensorlist_to_tensor mabs ins outs (compose_tensorlist mids ltl rtl) ≡
  compose_tensor (tensorlist_to_tensor mabs ins mids ltl)
    (tensorlist_to_tensor mabs mids outs rtl).
Proof.
  intros Hins_mids Hmids_outs Hins_outs Hltl Hrtl.
  intros v w Hv Hw.
  unfold compose_tensor, tensorlist_to_tensor.
  rewrite tl_total_semantics_compose_tensorlist_aux.
  unshelve (rewrite (sum_of_vec_cast (m:=m))).
  1:{
    abstract (now rewrite reverse_involutive, length_vec_to_list).
  }
  apply sum_of_ext'; intros mr Hmr.
  rewrite vec_to_list_cast.
  rewrite tl_total_semantics_aux_tl_times.
  f_equiv.
  - apply tl_total_semantics_free_varset_ext.
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
  - apply tl_total_semantics_free_varset_ext.
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


(* FIXME: Move *)

Lemma ntl_total_semantics_ntl_subst_free_as mabs ml l r ntl :
  r ∉ ntl.(ntl_sums) ->
  WF_ntl ntl ->
  ntl_total_semantics mabs ml (ntl_subst_free_as l r ntl) ==
  ∑ a : A, ntl_total_semantics mabs (<[l:=a]> ml) ntl.
Proof.
  intros Hr HWF.
  rewrite ntl_total_semantics_alt by now apply ntl_subst_free_as_WF.
  setoid_rewrite ntl_total_semantics_alt; [|easy].
  destruct ntl as [sums abs delt].
  cbn -[abstracts_semantics_alt deltas_semantics_alt].
  rewrite sum_of_Vmap_cons, sum_of_comm.
  apply sum_of_ext; intros a.
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  f_equiv.
  - apply eq_reflexivity, abstracts_semantics_alt_ext.
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
    [unfold Vmap; apply lookup_insert_ne; intros Heq;
     apply Hr; subst r; cbn; rewrite <- (elem_of_list_to_set (C:=Pset));
     apply HWF.2.1, elem_of_abstracts_bound_vars; set_solver +Hv Hflu|
     rewrite lookup_insert_case; do 2 case_decide; cbn;
      done || unfold Vmap; apply lookup_insert]).
  - apply eq_reflexivity, deltas_semantics_alt_ext.
    apply Forall2_fmap_l, Forall_Forall2_diag.
    rewrite Forall_forall.
    intros [lv uv] Hlu;
    cbn.
    split; [rename lv into v|rename uv into v];
    (destruct v as [r'|l']; cbn;
    [unfold Vmap; apply lookup_insert_ne; intros Heq;
     apply Hr; subst r; cbn; rewrite <- (elem_of_list_to_set (C:=Pset));
     apply HWF.2.2, elem_of_deltas_bound_vars; set_solver +Hlu|
    rewrite lookup_insert_case; do 2 case_decide; cbn;
      done || unfold Vmap; apply lookup_insert]).
Qed.


Lemma ntl_total_semantics_ntl_subst_free mabs ml l ntl :
  WF_ntl ntl ->
  ntl_total_semantics mabs ml (ntl_subst_free l ntl) ==
  ∑ a : A, ntl_total_semantics mabs (<[l:=a]> ml) ntl.
Proof.
  intros HWF.
  apply ntl_total_semantics_ntl_subst_free_as, HWF.
  apply infinite_is_fresh.
Qed.

Lemma sum_of_Vmap_fmap (f : positive -> positive) `{Hf : !Inj eq eq f}
  (sums : list positive) (fr : _ -> R) :
  ∑ v : Vmap (f <$> sums), fr v ==
  ∑ v : Vmap sums, fr (kmap f v).
Proof.
  unfold Vmap;
  apply (sum_of_relabel'_r2l (kmap f));
  [|apply eq_reflexivity, (kmap_Vmap_elements _)].
  easy.
Qed.

Lemma sum_of_Vmap_nil (fr : _ -> R) :
  ∑ v : Vmap [], fr v == fr ∅.
Proof.
  unfold_sum_of.
  cbn.
  ring.
Qed.

Lemma sum_of_Vmap_cons' ty tys f :
  ∑ mr : Vmap (ty :: tys), f mr ==
  ∑ vty : A, ∑ mr' : Vmap tys, f (<[ty := vty]> mr').
Proof.
  now rewrite sum_of_Vmap_cons, sum_of_comm.
Qed.

Lemma sum_of_Vmap_app
  (sums sums' : list positive) (fr : _ -> R) :
  ∑ v : Vmap (sums ++ sums'), fr v ==
  ∑ v : Vmap sums, ∑ v' : Vmap sums', fr ((v :> Pmap _) ∪ v').
Proof.
  revert fr; induction sums; intros fr.
  - rewrite sum_of_Vmap_nil.
    cbn.
    apply sum_of_ext; intros; unfold Vmap; now rewrite map_empty_union.
  - cbn.
    rewrite 2 sum_of_Vmap_cons'.
    apply sum_of_ext; intros va.
    rewrite IHsums.
    unfold Vmap.
    setoid_rewrite insert_union_l.
    reflexivity.
Qed.





Lemma abstracts_semantics_alt_app mabs ml mr abs abs' :
  abstracts_semantics_alt mabs ml mr (abs ++ abs') ==
  abstracts_semantics_alt mabs ml mr abs *
  abstracts_semantics_alt mabs ml mr abs'.
Proof.
  unfold abstracts_semantics_alt.
  now rewrite fmap_app, Rlist_prod_app.
Qed.


Lemma deltas_semantics_alt_app ml mr delt delt' :
  deltas_semantics_alt ml mr (delt ++ delt') ==
  deltas_semantics_alt ml mr delt *
  deltas_semantics_alt ml mr delt'.
Proof.
  unfold deltas_semantics_alt.
  now rewrite fmap_app, Rlist_prod_app.
Qed.

(* 
Lemma ntl_total_semantics_ntl_times_aux mabs ml l r :
  WF_ntl l -> WF_ntl r ->
  ntl_total_semantics mabs ml (ntl_times l r) ==
  ntl_total_semantics mabs ml l * ntl_total_semantics mabs ml r.
Proof.
  intros Hl Hr.
  rewrite ntl_total_semantics_alt by now apply ntl_times_WF.
  rewrite 2 ntl_total_semantics_alt by easy.
  cbn -[abstracts_semantics_alt deltas_semantics_alt list_to_set].
  rewrite sum_of_Vmap_app, (sum_of_Vmap_fmap _).
  rewrite sum_of_distr_l.
  apply sum_of_ext'; intros mr_l Hmr_l.
  rewrite sum_of_distr_r, (sum_of_Vmap_fmap _).
  apply sum_of_ext'; intros mr_r Hmr_r.
  rewrite abstracts_semantics_alt_app, deltas_semantics_alt_app.
  symmetry.
  rewrite rmul_comm_double.
  symmetry.
  f_equiv.
  - f_equiv;
    apply eq_reflexivity, abstracts_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
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
    apply eq_reflexivity, deltas_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall; intros [vl vu] _;
    cbn;
    (split; [rename vl into v|rename vu into v]);
    (destruct v as [v|]; [cbn -[bcons]|done]);
    try (rewrite lookup_union_l by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _));
    rewrite lookup_union_r by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _).
Qed. *)

Lemma ntl_total_semantics_ntl_times mabs ml l r :
  WF_ntl l -> WF_ntl r ->
  ntl_total_semantics mabs ml (ntl_times l r) ==
  ntl_total_semantics mabs ml l * ntl_total_semantics mabs ml r.
Proof.
  intros Hl Hr.
  rewrite ntl_total_semantics_alt by now apply ntl_times_WF.
  rewrite 2 ntl_total_semantics_alt by easy.
  cbn -[abstracts_semantics_alt deltas_semantics_alt list_to_set].
  rewrite sum_of_Vmap_app, (sum_of_Vmap_fmap _).
  rewrite sum_of_distr_l.
  apply sum_of_ext'; intros mr_l Hmr_l.
  rewrite sum_of_distr_r, (sum_of_Vmap_fmap _).
  apply sum_of_ext'; intros mr_r Hmr_r.
  rewrite abstracts_semantics_alt_app, deltas_semantics_alt_app.
  symmetry.
  rewrite rmul_comm_double.
  symmetry.
  f_equiv.
  - f_equiv;
    apply eq_reflexivity, abstracts_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
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
    apply eq_reflexivity, deltas_semantics_alt_ext, Forall2_fmap_l, Forall_Forall2_diag;
    rewrite Forall_forall; intros [vl vu] _;
    cbn;
    (split; [rename vl into v|rename vu into v]);
    (destruct v as [v|]; [cbn -[bcons]|done]);
    try (rewrite lookup_union_l by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _));
    rewrite lookup_union_r by (now apply (lookup_kmap_None _); lia);
    apply (lookup_kmap _).
Qed.

Definition compose_namedtensorlist (mids : list Idx)
  (l r : namedtensorlist) : namedtensorlist :=
  foldr (fun mid tl => ntl_subst_free mid tl) (ntl_times l r) (reverse mids).


Lemma compose_namedtensorlist_WF' mids l r :
  WF_ntl l -> WF_ntl r ->
  WF_ntl (foldr (fun mid tl => ntl_subst_free mid tl) (ntl_times l r) mids).
Proof.
  intros Hl Hr.
  induction mids; [now apply ntl_times_WF|].
  now apply ntl_subst_free_WF.
Qed.

Lemma compose_namedtensorlist_WF mids l r :
  WF_ntl l -> WF_ntl r ->
  WF_ntl (compose_namedtensorlist mids l r).
Proof.
  apply compose_namedtensorlist_WF'.
Qed.



Lemma ntl_total_semantics_compose_namedtensorlist_aux mabs ml mids
  (l r : namedtensorlist) :
  WF_ntl l -> WF_ntl r ->
  ntl_total_semantics mabs ml (compose_namedtensorlist mids l r) ==
  ∑ rmi : vec A (length (reverse (reverse mids))),
    ntl_total_semantics mabs (list_to_map (zip mids rmi) ∪ ml) (ntl_times l r).
Proof.
  unfold compose_namedtensorlist.
  erewrite sum_of_ext by now intros;
    replace (zip mids) with (zip_with (B:=A) pair (reverse (reverse mids))) by (now rewrite (reverse_involutive mids));
    refine (reflexivity _).
  cbv beta.
  generalize (reverse mids) as rmids.
  clear mids.
  intros mids.
  intros Hl Hr.
  revert ml;
  induction mids as [|mid mids IHmid]; intros ml.
  - rewrite sum_of_vec_0.
    cbn.
    now rewrite map_empty_union.
  - cbn [foldr].
    unshelve (rewrite (sum_of_vec_cast (m:=length (reverse mids) + 1))).
    1: {
      abstract (rewrite reverse_cons, length_app at 1; cbn;
      exact eq_refl).
    }
    setoid_rewrite vec_to_list_cast.
    rewrite sum_of_vec_add, sum_of_comm.
    rewrite ntl_total_semantics_ntl_subst_free by now apply compose_namedtensorlist_WF'.
    rewrite sum_of_vec_1.
    apply sum_of_ext'; intros a Ha.
    rewrite IHmid.
    apply sum_of_ext; intros mr.
    f_equiv.
    rewrite reverse_cons, vec_to_list_app.
    rewrite zip_with_app by now rewrite length_vec_to_list.
    rewrite list_to_map_app.
    cbn.
    rewrite <- map_union_assoc.
    now rewrite <- insert_union_l, map_empty_union.
Qed.

Lemma ntl_free_varset_correct ntl :
  ntl_free_varset ntl = tl_free_varset (ntl2tl ntl).
Proof.
  unfold ntl_free_varset, tl_free_varset.
  destruct ntl as [isums abs delt]; cbn -[abstracts_free_vars deltas_free_vars];
  now rewrite abstracts_free_vars_relabel_bounds, deltas_free_vars_relabel_bounds.
Qed.

Lemma ntl_total_semantics_free_varset_ext mabs ml ml' ntl :
  (forall l, l ∈ ntl_free_varset ntl -> ml !! l = ml' !! l) ->
  ntl_total_semantics mabs ml ntl == ntl_total_semantics mabs ml' ntl.
Proof.
  intros Hml.
  apply tl_total_semantics_free_varset_ext.
  now rewrite <- ntl_free_varset_correct.
Qed.

Lemma compose_namedtensorlist_correct mabs {n m o} (ins : vec Idx n)
  (mids : vec Idx m) (outs : vec Idx o) (ltl rtl : namedtensorlist) :
  ins ##@{list _} mids ->
  mids ##@{list _} outs ->
  ins ##@{list _} outs ->
  WF_ntl ltl -> WF_ntl rtl ->
  ntl_free_varset ltl ⊆ list_to_set (ins ++ mids) ->
  ntl_free_varset rtl ⊆ list_to_set (mids ++ outs) ->
  namedtensorlist_to_tensor mabs ins outs (compose_namedtensorlist mids ltl rtl) ≡
  compose_tensor (namedtensorlist_to_tensor mabs ins mids ltl)
    (namedtensorlist_to_tensor mabs mids outs rtl).
Proof.
  intros Hins_mids Hmids_outs Hins_outs HWFl HWFr Hltl Hrtl.
  intros v w Hv Hw.
  unfold compose_tensor, namedtensorlist_to_tensor.
  rewrite ntl_total_semantics_compose_namedtensorlist_aux by easy.
  unshelve (rewrite (sum_of_vec_cast (m:=m))).
  1:{
    abstract (now rewrite reverse_involutive, length_vec_to_list).
  }
  apply sum_of_ext'; intros mr Hmr.
  rewrite vec_to_list_cast.
  rewrite ntl_total_semantics_ntl_times by easy.
  f_equiv.
  - apply ntl_total_semantics_free_varset_ext.
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
  - apply ntl_total_semantics_free_varset_ext.
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



Lemma total_semantics_aux_kmap_te_relabel_absidx mabs ml mr
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} te :
  total_semantics_aux (kmap f mabs) ml mr (te_relabel_absidx f te) ==
  total_semantics_aux mabs ml mr te.
Proof.
  revert mr; induction te; intros mr; [reflexivity..| | |apply sum_of_ext; intros; apply IHte].
  - cbn.
    apply eq_reflexivity, abstract_semantics_ext; [|reflexivity..].
    apply (lookup_kmap _).
  - cbn; f_equiv; auto.
Qed.

Lemma tl_total_semantics_aux_kmap_tl_relabel_absidx mabs ml mr
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} tl :
  tl_total_semantics_aux' (kmap f mabs) ml mr (tl_relabel_absidx f tl) ==
  tl_total_semantics_aux' mabs ml mr tl.
Proof.
  rewrite 2 tl_total_semantics_aux_alt_vec.
  destruct tl as [sums abs delt];
  cbn -[tl_total_semantics_aux].
  apply sum_of_ext; intros m.
  apply tl_total_semantics_aux_ext_base;
  [|apply Forall_Forall2_diag; rewrite Forall_forall; intros ? _; split; done].
  apply Forall2_fmap_l, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros [[idx low] up] _.
  cbn.
  rewrite (lookup_kmap _).
  split; [easy|].
  split; apply Forall_Forall2_diag; rewrite Forall_forall; intros ? _; done.
Qed.


Lemma ntl_total_semantics_kmap_ntl_relabel_absidx mabs ml
  (f : Idx -> Idx) `{Hf : !Inj eq eq f} ntl :
  ntl_total_semantics (kmap f mabs) ml (ntl_relabel_absidx f ntl) ==
  ntl_total_semantics mabs ml ntl.
Proof.
  unfold ntl_total_semantics.
  rewrite ntl_relabel_absidx_correct.
  apply (tl_total_semantics_aux_kmap_tl_relabel_absidx _ _ _ _).
Qed.


Lemma simplify_ntl_deltas_correct_sem mabs ml ntl : 
  map_Forall (λ (_ : positive) (a : A), SummedElement a) ml ->
  WT_ntl (dom ml) ntl ->
  ntl_total_semantics mabs ml ntl == 
  ntl_total_semantics mabs ml (simplify_ntl_deltas ntl).
Proof.
  intros Hsum HWT.
  eapply ntl_delta_eq_correct; [done..|].
  symmetry.
  now apply simplify_ntl_deltas_correct.
Qed.





(*
Lemma ntl_perm_eq'_correct_permutative mabst mg ml ntl ntl' :
  WF_ntl ntl -> WF_ntl ntl' ->
  ntl ≡ntl'≡ₚ ntl' ->
  Forall (abst_WT' (snd ∘ projT1 <$> mabst)) ntl.(ntl_abstracts) ->
  (forall (f : Idx), f ∈ abstracts_indices ntl.(ntl_abstracts) ->
    forall (t : BTensor), mabst !! f = Some t ->
    permutative_tensor (projT2 t)) ->
  ntl_total_semantics (mabs_of_tensor_map mabst) mg ml ntl ==
  ntl_total_semantics (mabs_of_tensor_map mabst) mg ml ntl'.
Proof.
  (* ntl_total_semantics_alt *)
  intros Hntl Hntl' Hpeq'.
  pose proof Hpeq' as (Heq & Hperm)%(ntl_perm_eq'_NoDup _ _ Hntl.1 Hntl'.1).
  intros HWT Hpermut.
  etransitivity;
  [generalize Heq; apply ntl_aeq_correct; try done|].
  - split; [apply Hntl'|].
    etransitivity; [apply Hntl|].
    pose proof Hpeq' as [Hdom _].
    apply (f_equal dom) in Hdom.
    rewrite 2 dom_list_to_map_L in Hdom.
    rewrite Hdom.
    done.
  - now apply ntl_perm_eq_correct_permutative.
Qed. *)











(*

Lemma match_rewrite_tensorexpr_correct mabs mg ml telhs terhs univ tetarg :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->
  total_semantics mabs mg ml tetarg ==
  total_semantics mabs mg ml (default tetarg
    (match_rewrite_tensorexpr (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml)
      telhs terhs univ tetarg)).
Proof.
  intros Heq.
  destruct (match_rewrite_tensorexpr _ _ _ _ _ _ _) as [out|] eqn:Hmatch.



Lemma match_correctness_tensorexpr mabs mg ml telhs terhs univ :
  tensorequation_semantics_aux mabs mg [] telhs terhs univ ∅ ->
  teeq_is_correct_aux mabs mg telhs terhs univ ->
  tl_well_typed (mk_tc (projT1 <$> mabs) (projT1 <$> mg) (projT1 <$> ml) []) targ -> (* TODO: extend to other bound contexts than [] *)
  forall out, match_rewrite_tensorlist lhs rhs targ = Some out ->
  tl_total_semantics_aux' mabs mg ml [] targ ==
  tl_total_semantics_aux' mabs mg ml [] out. *)

(* TODO: Next step:
  Get the parser outputting things in terms of tensorequation_semantics
  and check they're correct, then get rewrite_in_lhs and rewrite_in_rhs
  working. A key thing to consider is passing between maps and lists of
  free variables; it shouldn't matter _too_ too much, except of course
  that for parsing you'll have to have the order exactly right for them
  to unify. I think we may get away with just having the final lemma do
  the nodup checking (i.e. it talks about tensorequation_semantics_aux)
  so we don't have to. Anyways, for now just using ^ should work. Other
  thing we have to do is make the generator for Pmap from Ltac2; should
  be pretty straightforward. Success looks like roundtrip parsing for a
  couple of abstract examples (such as in the Testing module, i.e. make
  [f] and [g] parse custom), and for a couple of simple rewrite lemmas.
  From there, the full (facade of a) rewriting tactic shouldn't be much
  more work.

*)

(*
Definition tl_total_semantics_alt_aux mabs mg ml mr'
  (tys : list (Idx * Ty)) abs : R :=
  ∑ mr : Vmap tys,
  Rlist_prod ((λ '(f, low, up),
    abstract_semantics_alt mabs mg ml (mr' ∪ mr) f low up) <$> abs).

(* FIXME: Rename *)
(* Definition list_to_imap  *)

Lemma tl_total_semantics_alt_aux_correct mabs mg ml mr sums abs :
  tl_total_semantics_aux mabs mg ml mr sums abs =
  tl_total_semantics_alt_aux mabs mg ml
    (list_to_map (imap (λ i v, (pos_add_N (Pos.of_succ_nat i) (lengthN sums), v)) (reverse mr)))
    (imap (λ i v, (Pos.of_succ_nat i, v)) (reverse sums))
    abs.
    (* TODO: Check this ^^^ !!!*)





Lemma tensorequation_semantics_aux_alt_aux mabs mg mr lhs rhs univ ml :
  NoDup univ.*1 ->
  list_to_set univ.*1 ## dom ml ->
  tensorequation_semantics_aux mabs mg mr lhs rhs univ ml <->
  forall ml', map_is_typed projT1 (list_to_map univ :> Pmap _) ml' -> ml ##ₘ ml' ->
  tl_total_semantics_aux' mabs mg (ml ∪ ml') mr lhs ==
    tl_total_semantics_aux' mabs mg (ml ∪ ml') mr rhs.
Proof.
  intros Hdup.
  revert ml;
  induction univ as [|(l, ty) univ IHuniv]; intros ml Hdom.
  - cbn.
    setoid_rewrite map_is_typed_empty_l.
    split; [now intros ? ? -> ?; rewrite map_union_empty|].
    intros Heq.
    specialize (Heq ∅).
    rewrite map_union_empty in Heq.
    apply Heq; [easy|].
    apply map_disjoint_empty_r.
  - cbn in Hdup |- *.
    rewrite NoDup_cons in Hdup.
    setoid_rewrite IHuniv; [|easy|].
    2:{
      rewrite dom_insert.
      rewrite disjoint_union_r, disjoint_singleton_r.
      cbn [fmap list_fmap list_to_set] in Hdom.
      rewrite disjoint_union_l, disjoint_singleton_l in Hdom.
      split; [|easy].
      now rewrite elem_of_list_to_set.
    }
    split.
    + intros Hins ml'.
      rewrite map_is_typed_insert_l by now apply not_elem_of_list_to_map_1.
      intros [(tx & Hml'_l & ->)%fmap_Some Htyped] Hdisj.
      specialize (Hins (projT2 tx) _ Htyped).
      tspecialize Hins. 1:{
        rewrite map_disjoint_insert_l.
        split; [apply lookup_delete|].
        apply (map_disjoint_weaken_r _ _ _ Hdisj).
        apply delete_subseteq.
      }
      rewrite union_insert_delete in Hins;
      [|eapply map_disjoint_Some_l; eauto|
        now destruct tx].
      apply Hins.
    + intros Hins x ml' Hty [Hml'_l Hdisj]%map_disjoint_insert_l.
      specialize (Hins (<[l:=mk_A x]> ml')).
      tspecialize Hins by now apply map_is_typed_insert_2.
      assert (Hml_l : ml !! l = None). 1:{
        apply not_elem_of_dom.
        refine (Hdom _ _).
        apply elem_of_list_to_set.
        cbn.
        constructor.
      }
      tspecialize Hins by now apply map_disjoint_insert_r_2.
      rewrite <- insert_union_l, insert_union_r by easy.
      apply Hins.
Qed.




map_first_key
Lemma tensorequation_semantics_alt mabs mg teeq :
  tensorequation_semantics


  map_fold (fun l ty (IH : Pmap A -> Prop) =>
    fun ml =>
    forall x : V ty,
    IH (<[l := mk_A x]> ml)
  ) (fun ml => tl_total_semantics_aux' mabs mg ml mr ∅

(* We need conditions to be able to say something like the following:
  Given a tensorlist [tl = sums, abs] and a pattern [tl' = sums', abs'],
  we can consider a (pair of) mapping(s) [m = ml, mb] of the free and bound
  variables, respectively, of [tl'], along with a "context"
  [tlctx = sumctx, absctx]. We then say this is "valid" if ["CONDITIONS"],
  meaning the maps give a "valid" decomposition
  [tl = sums, abs = sumctx ++ m <$> sums', absctx ++ m <$> abs'].

  I belive the conditions are:
  (i) [mb] must be injective
  (ii) the support of [absctx] (its bound variables) must be
    disjoint from the image of [mb],
  (iii) the image of [ml] must be disjoint from the image of [mb].

  The motivation is as follows:
  (i) [mb] tells us how to relabel the bound variables; if it failed to be
    surjective, we would sum over strictly fewer variables, necesarily
    creating problems (AN: I belive in essentially all nondegenerate cases)
  (ii) [absctx] describes the abstract tensors _not_ involved in the match,
    hence none of its bound variables can be asked to be summed over
    (otherwise, the tensor containing that variable could not be 'extracted'
    from the inner sum)
  (iii) [ml] can only assign a free variable of [tl'] to something that
    at least _looks_ like a free variable of the match (i.e., a global,
      a free, or a variable bound by [sumctx]), which is _not_ what a
      variable bound by the match looks like
  *)

(* TODO: The above turns into a statement which says:
  given these conditions are true, if we form a tensorexpr as
  [sumctx ++ bndsum, bndabs ++ (shift (length bndsum) absctx)]
  and we have [tensorequation_semantics]*)


(* TODO: Something in [teq_at] about [ml] including all the free variables?
  Otherwise, we maybe lose some expressiveness (specifically, we can easily
  show [teq_at] implies the free variable sets are the same, which maybe isn't
  semantically true, i.e. you could imagine saying 'this operation is actually
  independent of the input')*)

(* Matching on [tensorlist]s *)

(* TODO: When I figure out the "boundary condition" or whatever that is,
   incorporate it into the function at this level somehow? *)
Fixpoint extend_map_of_abstract_pair
  (mb : Pmap Idx) (* The map of [rel]/bound variables, which must map
    to other bound variables *)
  (ml : Pmap var) (* The map of free variables, which can map to any [var] *)
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
    | free ll, vr => (* free variables can map anywhere (ab initio, at least) *)
      match ml !! ll with
      | None => extend_map_of_abstract_pair mb (<[ll := vr]> ml) l r
      | Some vr' =>
        if bool_decide (vr = vr') then
          extend_map_of_abstract_pair mb ml l r
        else None
      end
    | bound rl, bound rr => (* bound variables must map to bound variables *)
      match mb !! rl with
      | None => extend_map_of_abstract_pair (<[rl := rr]> mb) ml l r
      | Some rr' =>
        if bool_decide (rr = rr') then
          extend_map_of_abstract_pair mb ml l r
        else None
      end
    | bound rl, _ => (* bound variables can only map to other bound variables *)
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
  (ml : Pmap var) (* The map of free variables, which can map to any [var] *)
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



Lemma total_semantics_absset_indep mabs mabs' mg ml
  te :
  (forall a, a ∈ te_absset te -> abs !! a = abs' !! a) ->
  total_semantics mabs mg ml te == total_semantics abs' vars te.
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






(*
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
Qed. *)


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
  transitivity (total_semantics abs (<[var:=mk_A x]> vars) te); [|symmetry].
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


Lemma tsum_overwrite_irbound var var' ty ty' te :
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




Lemma tensorlist_abstracts_perm_eq sums abs abs' :
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
  - now apply tensorlist_abstracts_perm_eq.
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
Qed.*)

End TensorExprDBSemantics.


Notation total_semantics mabs ml te := (total_semantics_aux mabs ml [] te).

Notation tl_total_semantics mabs ml tl :=
  (tl_total_semantics_aux mabs ml [] tl.(tl_sums) tl.(tl_abstracts) tl.(tl_deltas)).