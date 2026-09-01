From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)




From TensorRocqEx Require Export NonZXAux.

From TensorRocqEx Require Export ZXrwsymm.

From TensorRocq Require Import BW BWSized SizedProps PropsGraphs SizedPropsGraphs SizedProLike SizedRewriting SizedProQuote.

From TensorRocqEx Require Export ZXsrw_base.





Module ZXmsymm.

Section ZXquote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_SymmetricG_ProLike)).


Lemma zx_quote_symm_cast_nwire_bpath_aux (f : positive -> nat)
  (a b : btree positive)
  (p : bpath a b) :
  Quote (cast _ _
  (btree_size_eq_path p) eq_refl (n_wire (btree_size f b)))
  ((MPRO_to_PRO f (gbpath_to_MPRO p))).
Proof.
  induction p.
  - rewrite cast_id_eq.
    cbn.
    done.
  - cbn.
    constructor.
    cbn.
    f_equiv.
    cast_irrelevance.
  - cbn.
    rewrite <- n_wire_stack.
    rewrite cast_stack_distribute.
    exact (quote_stack _ _ _ _ IHp1 IHp2).
  - erewrite cast_simplify_eq by reflexivity.
    rewrite <- (cast_n_wire_r (n:=btree_size f b)).

    rewrite <- (nwire_removal_l (n_wire _)).
    rewrite cast_compose_distribute.
    cbn -[cast].
    unshelve refine (quote_compose _ _ _ _ IHp1 _).
    rewrite cast_n_wire_r.
    eapply DiagramQuote_proper_equiv, IHp2; [cast_irrelevance|done].
  Unshelve.
    symmetry; apply btree_size_eq_path; assumption.
Qed.


Lemma zx_quote_symm_cast_nwire_bpath (f : positive -> nat)
  (a b : btree positive)
  (Hab : a =@{list _} b)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n)) (MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Hab))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|apply zx_quote_symm_cast_nwire_bpath_aux].
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_bpath (f : positive -> nat)
  (a b a' b' : btree positive)
  (Ha : a =@{list _} a') (Hb : b' =@{list _} b)
  (zx : ZX (btree_size f a') (btree_size f b')) p
  (Hasize : btree_size f a = btree_size f a')
  (Hbsize : btree_size f b = btree_size f b') :
  Quote zx p ->
  Quote (cast _ _ Hasize Hbsize zx) (MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Ha)) ;;
    p ;; MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Hb)))%pro.
Proof.
  intros Hzx.
  rewrite <- (nwire_removal_l zx).
  rewrite cast_compose_distribute.
  rapply @quote_compose;
  [apply zx_quote_symm_cast_nwire_bpath|].
  rewrite <- (nwire_removal_r zx).
  rewrite cast_compose_distribute.
  rapply @quote_compose.
  apply zx_quote_symm_cast_nwire_bpath.
Qed.

Lemma zx_quote_symm_cast_n_wire_setup {n m k} (Hn : n = k) (Hm : m = k) p :
  Quote (cast _ _ (eq_trans_r Hn Hm) eq_refl (n_wire _)) p ->
  Quote (cast _ _ Hn Hm (n_wire k)) p.
Proof.
  subst.
  rewrite 2 cast_id_eq.
  done.
Qed.

Lemma zx_quote_symm_cast_n_wire_add_l {n m o} (Hn : n + m = n + o) p :
  Quote (cast _ _ (proj1 (Nat.add_cancel_l _ _ _) Hn) eq_refl (n_wire _)) p ->
  Quote (cast _ _ Hn eq_refl (n_wire _)) (Pid n * p).
Proof.
  intros [Hp].
  constructor.
  cbn.
  rewrite Hp.
  cbn.
  f_equiv.
  rewrite cast_stack_r_fwd, n_wire_stack.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_n_wire_add_r {n m o} (Hn : m + n = o + n) p :
  Quote (cast _ _ (proj1 (Nat.add_cancel_r _ _ _) Hn) eq_refl (n_wire _)) p ->
  Quote (cast _ _ Hn eq_refl (n_wire _)) (p * Pid n).
Proof.
  intros [Hp].
  constructor.
  cbn.
  rewrite Hp.
  cbn.
  f_equiv.
  rewrite cast_stack_l_fwd, n_wire_stack.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_nwire_bpath_infix_prf {f : positive -> nat}
  {a b : btree positive}
  {l r mid mid' : btree positive}
  (Ha : btree_elems a = (l + mid + r)%btree)
  (Hb : btree_elems b = (l + mid' + r)%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  btree_size f mid = btree_size f mid'.
Proof.
  apply (f_equal (sum_list_with f)) in Ha, Hb.
  rewrite 2 sum_list_with_btree_elems in Ha, Hb.
  cbn in Ha, Hb.
  lia.
Qed.

Lemma zx_quote_symm_cast_nwire_bpath_infix (f : positive -> nat)
  (a b : btree positive)
  (l r mid mid' : btree positive)
  (Ha : btree_elems a = (l + mid + r)%btree)
  (Hb : btree_elems b = (l + mid' + r)%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n))
  ((MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Ha))
    :> PRO _ _ (btree_size f a) (btree_size f l + btree_size f mid + btree_size f r)) ;;
   Pid (btree_size f l) *
   Pgen (btree_size f mid) (btree_size f mid') (inr (bundleDiagram
    (cast _ _ (Canonize.canonize
      (zx_quote_symm_cast_nwire_bpath_infix_prf Ha Hb Han Hbn))
      eq_refl (n_wire _)))) * Pid (btree_size f r) ;;
   MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' (eq_sym Hb)))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|]. 2:{
    Import ZXsymm.
    apply zx_quote_symm_compose, zx_quote_symm_compose.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f a (l + mid + r)).
    - apply DiagramQuote_iff_DiagramDenote.
      cbn.
      apply zx_denote_symm_stack, _.
      apply zx_denote_symm_stack; [apply _|].
      apply _.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f (l + mid' + r) b).
  }
  rewrite cast_stack_r_fwd, cast_stack_l_fwd, 2 n_wire_stack.
  rewrite 2 n_wire_removal_l', 2 cast_contract_eq'.
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_nwire_bpath_prefix_prf {f : positive -> nat}
  {a b : btree positive}
  {l mid mid' : btree positive}
  (Ha : btree_elems a = (l + mid)%btree)
  (Hb : btree_elems b = (l + mid')%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  btree_size f mid = btree_size f mid'.
Proof.
  apply (f_equal (sum_list_with f)) in Ha, Hb.
  rewrite 2 sum_list_with_btree_elems in Ha, Hb.
  cbn in Ha, Hb.
  lia.
Qed.

Lemma zx_quote_symm_cast_nwire_bpath_prefix (f : positive -> nat)
  (a b : btree positive)
  (l mid mid' : btree positive)
  (Ha : btree_elems a = (l + mid)%btree)
  (Hb : btree_elems b = (l + mid')%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n))
  ((MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Ha))
    :> PRO _ _ (btree_size f a) (btree_size f l + btree_size f mid)) ;;
   Pid (btree_size f l) *
   Pgen (btree_size f mid) (btree_size f mid') (inr (bundleDiagram
    (cast _ _ (Canonize.canonize
      (zx_quote_symm_cast_nwire_bpath_prefix_prf Ha Hb Han Hbn))
      eq_refl (n_wire _)))) ;;
   MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' (eq_sym Hb)))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|]. 2:{
    Import ZXsymm.
    apply zx_quote_symm_compose, zx_quote_symm_compose.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f a (l + mid)).
    - apply DiagramQuote_iff_DiagramDenote.
      cbn.
      apply zx_denote_symm_stack, _.
      apply _.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f (l + mid') b).
  }
  rewrite cast_stack_r_fwd, n_wire_stack.
  rewrite 2 n_wire_removal_l', 2 cast_contract_eq'.
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.


Lemma zx_quote_symm_cast_nwire_bpath_suffix_prf {f : positive -> nat}
  {a b : btree positive}
  {r mid mid' : btree positive}
  (Ha : btree_elems a = (mid + r)%btree)
  (Hb : btree_elems b = (mid' + r)%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  btree_size f mid = btree_size f mid'.
Proof.
  apply (f_equal (sum_list_with f)) in Ha, Hb.
  rewrite 2 sum_list_with_btree_elems in Ha, Hb.
  cbn in Ha, Hb.
  lia.
Qed.

Lemma zx_quote_symm_cast_nwire_bpath_suffix (f : positive -> nat)
  (a b : btree positive)
  (r mid mid' : btree positive)
  (Ha : btree_elems a = (mid + r)%btree)
  (Hb : btree_elems b = (mid' + r)%btree)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n))
  ((MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Ha))
    :> PRO _ _ (btree_size f a) (btree_size f mid + btree_size f r)) ;;
   Pgen (btree_size f mid) (btree_size f mid') (inr (bundleDiagram
    (cast _ _ (Canonize.canonize
      (zx_quote_symm_cast_nwire_bpath_suffix_prf Ha Hb Han Hbn))
      eq_refl (n_wire _)))) * Pid (btree_size f r) ;;
   MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' (eq_sym Hb)))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|]. 2:{
    Import ZXsymm.
    apply zx_quote_symm_compose, zx_quote_symm_compose.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f a (mid + r)).
    - apply DiagramQuote_iff_DiagramDenote.
      cbn.
      apply zx_denote_symm_stack, _.
      apply _.
    - apply (zx_quote_symm_cast_nwire_bpath_aux f (mid' + r) b).
  }
  rewrite cast_stack_l_fwd, n_wire_stack.
  rewrite 2 n_wire_removal_l', 2 cast_contract_eq'.
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_n_wire_id {n k} (Hn Hm : n = k) :
  Quote (cast _ _ Hn Hm (n_wire k)) (Pid n).
Proof.
  rewrite cast_n_wire.
  apply _.
Qed.


End ZXquote_symm.

Module QuoteCast.

Import Ltac2.
Import ConstrExtra.

(* Ltac2 solve_zx_symm_quote_cast () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m ?n' ?m' ?hn ?hm ?zx) _] =>
    let (cs, bn) := parse_nat_btree_to_pos [] n in
    let (cs, bn') := parse_nat_btree_to_pos cs n' in
    let (cs, bm) := parse_nat_btree_to_pos cs m in
    let (cs, bm') := parse_nat_btree_to_pos cs m' in
    let cbn := CC.to_btree_typed 'positive CC.to_pos bn in
    let cbm := CC.to_btree_typed 'positive CC.to_pos bm in
    let cbn' := CC.to_btree_typed 'positive CC.to_pos bn' in
    let cbm' := CC.to_btree_typed 'positive CC.to_pos bm' in
    let ccs := CC.mk_list_typed 'nat cs in
    let prf := '(zx_quote_symm_cast_bpath (interp_discrete_hg_inhab $ccs)
      $cbn $cbm $cbn' $cbm' eq_refl eq_refl $zx _ $hn $hm) in
    refine '(id $prf _)
  end. *)

(* FIXME: Move *)
Ltac2 greatest_prefix (eqa : 'a -> 'a -> bool) (l : 'a list) (r : 'a list) : 'a list * 'a list * 'a list :=
  let rec go l r :=
    match l, r with
    | [], [] => ([], [], [])
    | _ :: _, [] => ([], l, [])
    | [], _ :: _ => ([], [], r)
    | a :: l', b :: r' =>
      if eqa a b then
        let (pref, l'', r'') := go l' r' in
        (a :: pref, l'', r'')
      else
        ([], l, r)
    end
  in go l r.

Ltac2 greatest_suffix (eqa : 'a -> 'a -> bool) (l : 'a list) (r : 'a list) :=
  let (revpref, revl, revr) := greatest_prefix eqa (List.rev l) (List.rev r) in
  (List.rev revpref, List.rev revl, List.rev revr).

Ltac2 greatest_common_prefix_suffix (eqa : 'a -> 'a -> bool) (l : 'a list) (r : 'a list) :
  'a list * 'a list * 'a list * 'a list :=
  let (pref, l', r') := greatest_prefix eqa l r in
  let (suff, l'', r'') := greatest_suffix eqa l' r' in
  (pref, suff, l'', r'').

Ltac2 btree_of_list' (l : 'a list) : 'a btree :=
  let rec go acc l :=
    match l with
    | [] => acc
    | a :: l => go (Bnode acc (Bleaf a)) l
    end in
  match l with
  | [] => Bempty
  | a :: l => go (Bleaf a) l
  end.

Ltac2 solve_zx_symm_quote_cast_n_wire_monoidal () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m _ _ ?hn ?hm (n_wire ?_k)) _] =>
    if Bool.and (CC.is_nat_const n) (CC.is_nat_const m) then
      apply (ZXsymm.zx_quote_symm_cast_id $hn $hm)
    else
    let (cs, bn) := parse_nat_btree_to_pos [] n in
    let (cs, bm) := parse_nat_btree_to_pos cs m in
    let cbn := CC.to_btree_typed 'positive CC.to_pos bn in
    let cbm := CC.to_btree_typed 'positive CC.to_pos bm in
    let ccs := CC.mk_list_typed 'nat cs in
    let bn_elems := btree_elems bn in
    let bm_elems := btree_elems bm in
    if List.equal Int.equal bn_elems bm_elems then
      refine constr:(zx_quote_symm_cast_nwire_bpath (interp_discrete_hg_inhab $ccs)
        $cbn $cbm eq_refl $hn $hm)
    else
      let (pref, suff, mid, mid') :=
        greatest_common_prefix_suffix Int.equal bn_elems bm_elems in
      let cbpref := CC.to_btree_typed constr:(positive) CC.to_pos (btree_of_list' pref) in
      let cbsuff := CC.to_btree_typed constr:(positive) CC.to_pos (btree_of_list' suff) in
      let cbmid := CC.to_btree_typed constr:(positive) CC.to_pos (btree_of_list' mid) in
      let cbmid' := CC.to_btree_typed constr:(positive) CC.to_pos (btree_of_list' mid') in
      match pref, suff with
      | _::_, _::_ =>
        refine constr:(zx_quote_symm_cast_nwire_bpath_infix (interp_discrete_hg_inhab $ccs)
          $cbn $cbm $cbpref $cbsuff $cbmid $cbmid' eq_refl eq_refl
          $hn $hm)
      | _::_, [] =>
        refine constr:(zx_quote_symm_cast_nwire_bpath_prefix (interp_discrete_hg_inhab $ccs)
          $cbn $cbm $cbpref $cbmid $cbmid' eq_refl eq_refl $hn $hm)
      | [], _::_ =>
        refine constr:(zx_quote_symm_cast_nwire_bpath_suffix (interp_discrete_hg_inhab $ccs)
          $cbn $cbm $cbsuff $cbmid $cbmid' eq_refl eq_refl
          $hn $hm)
      | [], [] =>
        refine constr:(ZXsymm.zx_quote_symm_cast_n_wire $hn $hm)
      end
      (* apply (zx_quote_symm_cast_n_wire_setup $hn $hm);
      let rec go nm :=
        lazy_match! nm with
        | (?n + ?m, ?n + ?o) =>
          apply (@zx_quote_symm_cast_n_wire_add_l $n $m $o);
          go constr:(pair $m $o)
        | (S ?n, S ?m) =>
          apply (@zx_quote_symm_cast_n_wire_add_l 1 $n $m);
          go constr:(pair $n $m)
        | (?m + ?n, ?o + ?n) =>
          apply (@zx_quote_symm_cast_n_wire_add_r $n $m $o);
          go constr:(pair $m $o)
        | _ =>
          apply ZXsymm.zx_quote_symm_cast_n_wire
        end in
      go constr:(pair $n $m) *)
  end.

End QuoteCast.

Ltac do_cast_MPRO_simpl_flag := fail.

Ltac zx_symm_quote_n_wire_cast_tac_monoidal :=
  lazymatch goal with
  |- (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
      (cast ?n ?m ?hn ?hm (n_wire ?k)) _) =>
    tryif timeout 1 (unify n m) then
      exact (zx_quote_symm_cast_n_wire_id hn hm)
    else
      let Hprf := fresh "Hprf" in
      let quote := match goal with |- ?R _ _ => R end in
      eassert (Hprf : quote (cast n m hn hm (n_wire k)) _) by ltac2:(QuoteCast.solve_zx_symm_quote_cast_n_wire_monoidal());
      tryif do_cast_MPRO_simpl_flag then
        do 2 try lazymatch type of Hprf with
        | context [MPRO_to_PRO _ _] =>
          (* vm_eval (bpath_of_eq' _) in Hprf; *)
          cbn_eval (MPRO_to_PRO _ _) in Hprf
        end
        else idtac;
      lazy [btree_size interp_discrete_hg_inhab list_pth list_drop_pos head tail btree_elems btree_of_list_rassoc] in Hprf;
      exact Hprf
  end.


#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire ?k)) _) =>
    zx_symm_quote_n_wire_cast_tac_monoidal
    : typeclass_instances.

(*
Goal forall (n m o p : nat) Hn Hm, exists pr, DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast (m + o + p) (n + p + m) Hn Hm (n_wire p)) pr /\ pr = pr.
Proof.

  intros.
  eexists; split.
  apply _.
  cbn.

  match goal with |-
  (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire ?k)) _) =>
    tryif timeout 1 (unify n m) then
      exact (zx_quote_symm_cast_n_wire_id hn hm)
    else
      let Hprf := fresh "Hprf" in
      let quote := match goal with |- ?R _ _ => R end in
      eassert (Hprf : quote (cast n m hn hm (n_wire k)) _) by ltac2:(QuoteCast.solve_zx_symm_quote_cast_n_wire_monoidal());
      do 2 try lazymatch type of Hprf with
        | context [MPRO_to_PRO _ _] =>
          cbn_eval (MPRO_to_PRO _ _) in Hprf
        end;
      lazy [btree_size interp_discrete_hg_inhab list_pth list_drop_pos head tail] in Hprf;
      exact Hprf
    end.
  apply _.
  (* apply _. *)
  match goal with |- (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire ?k)) _) =>
  let Hprf := fresh "Hprf" in
  let quote := match goal with |- ?R _ _ => R end in
  eassert (Hprf : quote (cast n m hn hm (n_wire k)) _) by ltac2:(QuoteCast.solve_zx_symm_quote_cast_n_wire_monoidal())
  end.

  let Hprf := fresh "Hprf" in
  eassert (Hprf : cast n m hn hm (n_wire k) _) by ltac2:(QuoteCast.solve_zx_symm_quote_cast_n_wire_monoidal())
  end.
  cbn in Hprf;
  exact Hprf
  apply _.
  Import Ltac2.
  lazy [btree_size interp_discrete_hg_inhab list_pth list_drop_pos head tail] in Hprf |- *.
  ltac2:(let hprf := Fresh.fresh (Fresh.Free.of_goal()) @hprf in
  let goal := Control.goal() in
  Std.assert (Std.AssertType
    (Some (Std.IntroNaming (Std.IntroIdentifier hprf))) goal None)).
  assert (hprf : $goal)). assert (Hprf : )

  apply _.
    ltac2:(QuoteCast.solve_zx_symm_quote_cast_n_wire_monoidal()).
    cbn -[cast gbpath_to_MPRO bpath_of_eq'] in d.


  apply _.
  Import Ltac2.
  Ltac2 Eval lazy_match! Control.goal() with
  | DiagramQuote (@cast ?n ?m _ _ ?hn ?hm (n_wire ?_k)) _ =>
    (* if Bool.and (CC.is_nat_const n) (CC.is_nat_const m) then
      apply (ZXsymm.zx_quote_symm_cast_id $hn $hm)
    else *)
    let (cs, bn) := parse_nat_btree_to_pos [] n in
    let (cs, bm) := parse_nat_btree_to_pos cs m in
    btree_eq (btree_elems bn) (btree_elems bn)
  end.
    if btree_eq Int.equal bn bm then
      let cbn := CC.to_btree_typed 'positive CC.to_pos bn in
      let cbm := CC.to_btree_typed 'positive CC.to_pos bm in
      let ccs := CC.mk_list_typed 'nat cs in
      refine '(zx_quote_symm_cast_nwire_bpath (interp_discrete_hg_inhab $ccs)
        $cbn $cbm eq_refl $hn $hm)
    else
      apply (zx_quote_symm_cast_n_wire_setup $hn $hm);
      let rec go nm :=
        lazy_match! nm with
        | (?n + ?m, ?n + ?o) =>
          apply (@zx_quote_symm_cast_n_wire_add_l $n $m $o);
          go constr:(pair $m $o)
        | (S ?n, S ?m) =>
          apply (@zx_quote_symm_cast_n_wire_add_l 1 $n $m);
          go constr:(pair $n $m)
        | (?m + ?n, ?o + ?n) =>
          apply (@zx_quote_symm_cast_n_wire_add_r $n $m $o);
          go constr:(pair $m $o)
        | _ =>
          apply ZXsymm.zx_quote_symm_cast_n_wire
        end in
      go constr:(pair $n $m)
  end.
  Set Typeclasses Debug.
  apply _. *)

(* TODO: Add instance for when it's a definitional equality *)
#[export] Instance zx_denote_symm_monoidal {n m} (s : Monoidal n m) :
  DiagramDenote (ProD:=ZX_SymmetricG_ProLike)
    (cast _ _ (Monoidal_eq s) eq_refl (n_wire m))
    [str monoidal_inl s].
Proof.
  constructor; done.
Qed.



Import ZXsymm.

Definition zxpscat_lemma := LawfulMProLike_MPRO_quote_test_correct (T':=positive) (MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro.

Definition zxpscat_casted_lemma := LawfulMProLike_MPRO_quote_test_correct_casted (T':=positive) (MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro.

Definition zxpsrw_lhs_lemma := LawfulProLike_MPRO_monog_quote_rewrite_correct (T':=positive) (@MSymmetric)
    (SizedProD:=ZX_SymmetricG_SizedProLike) ZX_SymmetricG_lawpro.

Ltac zxpscat_old :=

  let Hrw := fresh "Hrw" in
  time? "zxpscat setup tactic" specialize (zxpscat_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXDVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));
  lazymatch goal with
  | |- ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  time? "zxpscat quote to PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));
  time? "zxpscat quote to positive PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)
  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  time? "zxpscat quote to MPRO" (epose proof (Hrw _ _ _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error."));
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpscat refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxspcat) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpscat compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxspcat) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxspcat) Unexpected additional goal! Please report this unexpected error."..].

Ltac zxpscat_setup Hrw le :=
  time? "zxpscat setup tactic" specialize (zxpscat_casted_lemma) as Hrw;
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev)).

Ltac zxpscat_parse Hrw :=
  lazymatch goal with
  | |- ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end.

Ltac zxpscat_quote_tac :=
  zx_symm_simplify_quote_tac; typeclasses eauto.

Ltac zxpscat_quote Hrw :=
  time? "zxpscat quote to PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by zxpscat_quote_tac) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?")).

Ltac zxpscat_to_pos_tac :=
  typeclasses eauto.

Ltac zxpscat_to_pos Hrw :=
  time? "zxpscat quote to positive PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by zxpscat_to_pos_tac) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")).

Ltac zxpscat_to_sized_tac :=
  typeclasses eauto.

Ltac zxpscat_to_sized Hrw ln :=
  let lnv := eval unfold ln in ln in
  specialize (Hrw (@interp_discrete_hg_inhab _ Nat.inhabited lnv));
  time? "zxpscat quote to MPRO" (epose proof (Hrw _ _ _ _ _ _) as Hrw;
  (do 2 (tryif timeout 3 (tspecialize Hrw by zxpscat_to_sized_tac) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error."));
  do 2 (specialize (Hrw eq_refl))).

Ltac zxpscat_final Hrw ln le :=
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpscat refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxspcat) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpscat compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxspcat) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxspcat) Unexpected additional goal! Please report this unexpected error."..].

Ltac zxpscat :=

  let Hrw := fresh "Hrw" in
  let le := fresh "le" in evar (le : list ZXDVERT);
  zxpscat_setup Hrw le;
  zxpscat_parse Hrw;
  zxpscat_quote Hrw;
  zxpscat_to_pos Hrw;

  let ln := fresh "ln" in evar (ln : list nat);
  zxpscat_to_sized Hrw ln;

  zxpscat_final Hrw ln le.


Ltac zxpsrw_lhs_setup Hrw le :=
  time? "zxpsrw_lhs setup tactic" specialize (zxpsrw_lhs_lemma) as Hrw;
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev)).

Ltac zxpsrw_lhs_parse Hrw lem match_number :=
  time? "zxpsrw_lhs_parse" (
  let lemT := type of lem in
  lazymatch lemT with
  | ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | _ =>
    fail "cannot recognize lemma (type) as the application of a relation: " lemT
  end;


  lazymatch goal with
  | |- ?R ?dtgt _ =>
    specialize (Hrw _ _ dtgt)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;

  specialize (Hrw match_number);
  specialize (Hrw lem)).

Ltac zxpsrw_lhs_quote_tac :=
  zx_symm_simplify_quote_tac; typeclasses eauto.

Ltac zxpsrw_lhs_quotes Hrw :=

  time? "zxpsrw_lhs setup quote lem/goal" (
    epose proof (Hrw _ _ _) as Hrw);

  time? "zxpsrw_lhs quote lem to PRO" (
  do 2 (tryif timeout 2 (tspecialize Hrw by zxpsrw_lhs_quote_tac) then idtac
    else fail "Timed out trying to quote lemma! Have you declared all necessary instances?"));
  time? "zxpsrw_lhs quote goal to PRO" (
  do 1 (tryif timeout 2 (tspecialize Hrw by zxpsrw_lhs_quote_tac) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?")).

Ltac zxpsrw_lhs_to_pos_tac :=
  typeclasses eauto.

Ltac zxpsrw_lhs_to_pos Hrw :=

  time? "zxpsrw_lhs quote to positive PRO" (epose proof (Hrw _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by zxpsrw_lhs_to_pos_tac) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error."); (* TODO: maybe replace with just tactic? *)

  lazy [btree_size list_pth list_drop_pos head tail btree_elems btree_of_list_rassoc] in Hrw).


Ltac zxpsrw_lhs_to_sized_tac :=
  typeclasses eauto.

Ltac zxpsrw_lhs_to_sized Hrw ln :=
  let lnv := eval unfold ln in ln in
  specialize (Hrw (@interp_discrete_hg_inhab _ Nat.inhabited lnv));
  time? "zxpsrw_lhs quote PRO to MPRO" (
  epose proof (Hrw _ _ _ _   _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by zxpsrw_lhs_to_sized_tac) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.")).


Ltac zxpsrw_lhs_compute Hrw :=
  epose proof (Hrw _) as Hrw;
  time? "zxpsrw_lhs compute rewrite" (tspecialize Hrw; [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ]).

Ltac zxpsrw_lhs_from_sized_tac :=
  typeclasses eauto.

Ltac zxpsrw_lhs_from_sized Hrw :=
  time? "zxpsrw_lhs MPRO to PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by zxpsrw_lhs_from_sized_tac) then idtac
    else fail "Failed interpreting resulting sized MPRO as a PRO! Please report this unexpected error.")).

Ltac zxpsrw_lhs_from_pos_tac :=
  typeclasses eauto.

Ltac zxpsrw_lhs_from_pos Hrw :=
  time? "zxpsrw_lhs denote from positive PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by zxpsrw_lhs_from_pos_tac) then idtac else
    fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.")).

Ltac zxpsrw_lhs_denote_tac :=
  zx_symm_simplify_denote_tac; typeclasses eauto.

Ltac zxpsrw_lhs_denote Hrw :=
  time? "zxpsrw_lhs denote PRO to goal" (epose proof (Hrw _) as Hrw;
  (tryif timeout 10 (tspecialize Hrw by typeclasses eauto) then idtac else
    fail "Timed out trying to denote result! Have you declared all necessary instances?")).

Ltac zxpsrw_lhs_final Hrw le ln :=
  time? "zxpsrw_lhs cleanup and apply" (
  close_evar_ended_list le; close_evar_ended_list ln;
  subst le ln;
  etransitivity; [apply Hrw|clear Hrw]).

Ltac zxpsrw_lhs lem match_number :=

  let Hrw := fresh "Hrw" in
  let le := fresh "le" in evar (le : list ZXDVERT);
  zxpsrw_lhs_setup Hrw le;
  zxpsrw_lhs_parse Hrw lem match_number;
  zxpsrw_lhs_quotes Hrw;
  zxpsrw_lhs_to_pos Hrw;
  let ln := fresh "ln" in evar (ln : list nat);
  zxpsrw_lhs_to_sized Hrw ln;
  (* specialize_with_concr_asgn_list Hrw lnv;
  time? "zxpsrw_lhs prove correctness of concrete assignment" (
    tryif (timeout 1 (tspecialize Hrw by compute_done)) then idtac
    else fail "Failed to prove concrete assignment map correct! Please report this unexpected error"); *)
  zxpsrw_lhs_compute Hrw;
  zxpsrw_lhs_from_sized Hrw;
  zxpsrw_lhs_from_pos Hrw;
  zxpsrw_lhs_denote Hrw;
  zxpsrw_lhs_final Hrw le ln.


Ltac zxpsrw_rhs lem match_number :=
  symmetry;
  zxpsrw_lhs lem match_number;
  symmetry.

Ltac zxpsrw lem match_number :=
  zxpsrw_lhs lem match_number || zxpsrw_rhs lem match_number.


Tactic Notation "zxpsrw_lhs" uconstr(lem) "at" constr(n) :=
  zxpsrw_lhs lem n.

Tactic Notation "zxpsrw_lhs" uconstr(lem) :=
  zxpsrw_lhs lem at O.

Tactic Notation "zxpsrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw_lhs (symmetry lem) at n.

Tactic Notation "zxpsrw_lhs" "<-" uconstr(lem) :=
  zxpsrw_lhs (symmetry lem).

Tactic Notation "zxpsrw_rhs" uconstr(lem) "at" constr(n) :=
  zxpsrw_rhs lem n.

Tactic Notation "zxpsrw_rhs" uconstr(lem) :=
  zxpsrw_rhs lem at O.

Tactic Notation "zxpsrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw_rhs (symmetry lem) at n.

Tactic Notation "zxpsrw_rhs" "<-" uconstr(lem) :=
  zxpsrw_rhs (symmetry lem).

Tactic Notation "zxpsrw" uconstr(lem) "at" constr(n) :=
  zxpsrw lem n.

Tactic Notation "zxpsrw" uconstr(lem) :=
  zxpsrw lem at O.

Tactic Notation "zxpsrw" "<-" uconstr(lem) "at" constr(n) :=
  zxpsrw (symmetry lem) at n.

Tactic Notation "zxpsrw" "<-" uconstr(lem) :=
  zxpsrw (symmetry lem).




Module Examples.


Lemma parametric_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m o β ⟷ Z o p γ ∝=
  Z n m α ⟷ (X m o β ⟷ Z o p γ).
Proof.
  zxpscat.
Qed.


Lemma parametric_stack_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m (o + n + m) β ⟷ (Z o p γ ↕ Z n p γ ↕ Z m p γ) ⟷
    X _ n α ∝=
  Z n m α ⟷ X m (o + (n + m)) β ⟷ (Z o p γ ↕ (Z n p γ ↕ Z m p γ)) ⟷
    X _ n α.
Proof.
  zxpscat.
Qed.

Lemma Z_absolute_fusion' {n m o} (α β : R) : m <> O ->
  Z n m α ⟷ Z m o β ∝= Z n o (α + β).
Proof.
  destruct m; [done|intros _].
  apply Z_absolute_fusion.
Qed.




Lemma Z_absolute_fusion : forall {n m o} α β,
	(Z n (S m) α ⟷ Z (S m) o β) ∝=
	Z n o (α + β).
Proof.
  intros. (* Figure 19a *)
  induction m.
  - apply Z_spider_1_1_fusion.
  - rewrite grow_Z_top_right, grow_Z_top_left.
    zxpsrw (Z_1_2_1_fusion 0 0).
    zxpsrw IHm.
    zxpscat.
Qed.



Lemma parametric_rewriting_example {n m o p : nat} {α β γ : R} : m <> 0 -> n <> 0 ->
  Z n (p + (m + n)) α ⟷ (n_wire p ↕ (Z m n α ↕ Z n m β)) ⟷
  (n_wire p ↕ zx_comm _ _) ⟷ (n_wire p ↕ (Z m n α ↕ Z n m α)) ⟷
  Z (p + (n + m)) p 0 ∝= Z _ _ 0.
Proof.
  intros Hm Hn.
  zxpsrw_lhs (@Z_absolute_fusion' m n m α α Hn).


  (* TODO: Investigate parameter matching like this:
  epose (lem := @Z_absolute_fusion' _ n _ _ _ Hn).
  let lemT := type of lem in
  match lemT with
  | ?R ?lhs _ =>
    eassert (DiagramQuote (ProD:=ZX_SymmetricG_ProLike) lhs _)
  end.
  Hint Mode DiagramQuote + + + + - - ! - : typeclass_instances.
  typeclasses eauto.

  TODO: Or maybe we should parse the target term directly using the known
  composition and stacking? In either case, we need to end up with a list
  of _sized_ generators, from which we can try all matches I guess? With
  a warning that that'll be slow? *)



  (* TODO: etc... let lem := lem *)
Abort.


End Examples.

End ZXmsymm.
