From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)





From TensorRocqEx Require Export ZXrwauto.

From TensorRocq Require Import BW BWSized SizedProps PropsGraphs SizedPropsGraphs SizedProLike SizedRewriting SizedProQuote.

From TensorRocqEx Require Export ZXsrw_base.




Module ZXmauto.

Section ZXquote_auto.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_Autonomous_ProLike)).


Lemma zx_quote_auto_cast_nwire_bpath_aux (f : positive -> nat)
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


Lemma zx_quote_auto_cast_nwire_bpath (f : positive -> nat)
  (a b : btree positive)
  (Hab : a =@{list _} b)
  {n} (Han : btree_size f a = n) (Hbn : btree_size f b = n) :
  Quote (cast _ _ Han Hbn (n_wire n)) (MPRO_to_PRO f (gbpath_to_MPRO (bpath_of_eq' Hab))).
Proof.
  eapply DiagramQuote_proper_equiv; [|done|apply zx_quote_auto_cast_nwire_bpath_aux].
  rewrite cast_n_wire_r.
  cast_irrelevance.
Qed.

Lemma zx_quote_auto_cast_bpath (f : positive -> nat)
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
  [apply zx_quote_auto_cast_nwire_bpath|].
  rewrite <- (nwire_removal_r zx).
  rewrite cast_compose_distribute.
  rapply @quote_compose.
  apply zx_quote_auto_cast_nwire_bpath.
Qed.




End ZXquote_auto.

Module QuoteCast.

Import Ltac2.
Import ConstrExtra.

(* Ltac2 solve_zx_auto_quote_cast () : unit :=
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
    let prf := '(zx_quote_auto_cast_bpath (interp_discrete_hg_inhab $ccs)
      $cbn $cbm $cbn' $cbm' eq_refl eq_refl $zx _ $hn $hm) in
    refine '(id $prf _)
  end. *)

Ltac2 solve_zx_auto_quote_cast_n_wire_monoidal () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m _ _ ?hn ?hm (n_wire ?k)) _] =>
    if Bool.and (CC.is_nat_const n) (CC.is_nat_const m) then
      apply (ZXauto.zx_quote_auto_cast_id $hn $hm)
    else
    let (cs, bn) := parse_nat_btree_to_pos [] n in
    let (cs, bm) := parse_nat_btree_to_pos cs m in
    if btree_eq Int.equal bn bm then
      let cbn := CC.to_btree_typed 'positive CC.to_pos bn in
      let cbm := CC.to_btree_typed 'positive CC.to_pos bm in
      let ccs := CC.mk_list_typed 'nat cs in
      refine '(zx_quote_auto_cast_nwire_bpath (interp_discrete_hg_inhab $ccs)
        $cbn $cbm eq_refl $hn $hm)
    else
      refine '(@ZXauto.zx_quote_auto_cast_n_wire $n $m $k $hn $hm)
  end.

End QuoteCast.


#[export] Hint Extern 4 (DiagramQuote (Struct:=Autonomous) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire ?k)) _) =>
    ltac2:(QuoteCast.solve_zx_auto_quote_cast_n_wire_monoidal())
    : typeclass_instances.


(* TODO: Add instance for when it's a definitional equality *)
#[export] Instance zx_denote_auto_monoidal {n m} (s : Monoidal n m) :
  DiagramDenote (ProD:=ZX_Autonomous_ProLike)
    (cast _ _ (Monoidal_eq s) eq_refl (n_wire m))
    [str symmetric_inl (monoidal_inl s)].
Proof.
  constructor; done.
Qed.



Import ZXauto.

Definition zxpacat_lemma := LawfulMProLike_MPRO_quote_test_correct (T':=positive) (MAutonomous)
    (SizedProD:=ZX_Autonomous_SizedProLike) ZX_Autonomous_lawpro.

Definition zxpacat_casted_lemma := LawfulMProLike_MPRO_quote_test_correct_casted (T':=positive) (MAutonomous)
    (SizedProD:=ZX_Autonomous_SizedProLike) ZX_Autonomous_lawpro.

Definition zxparw_lhs_lemma := LawfulProLike_MPRO_monog_quote_rewrite_correct (T':=positive) (@MAutonomous)
    (SizedProD:=ZX_Autonomous_SizedProLike) ZX_Autonomous_lawpro.

Ltac zxpacat_old :=

  let Hrw := fresh "Hrw" in
  time? "zxpacat setup tactic" specialize (zxpacat_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXDVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));
  lazymatch goal with
  | |- ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  time? "zxpacat quote to PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));
  time? "zxpacat quote to positive PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)
  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  time? "zxpacat quote to MPRO" (epose proof (Hrw _ _ _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error."));
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpacat refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxspcat) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpacat compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxspcat) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxspcat) Unexpected additional goal! Please report this unexpected error."..].


Ltac zxpacat :=

  let Hrw := fresh "Hrw" in
  time? "zxpacat setup tactic" specialize (zxpacat_casted_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXDVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));
  lazymatch goal with
  | |- ?R ?dlhs ?drhs =>
    specialize (Hrw _ _ dlhs drhs)
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  time? "zxpacat quote to PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));
  time? "zxpacat quote to positive PRO" (epose proof (Hrw _ _) as Hrw;
  do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)
  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  time? "zxpacat quote to MPRO" (epose proof (Hrw _ _ _ _ _ _) as Hrw;
  (do 2 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error."));
    do 2 specialize (Hrw eq_refl));
  close_evar_ended_list ln; close_evar_ended_list le;
  time? "zxpacat refine (quick)" notypeclasses refine (Hrw _);
  [
  clear Hrw;
  lazymatch goal with
  | |- ?b = true =>
    tryif has_evar b then fail "(zxspcat) quoted MPRO has evar; will not compute! Please report this unexpected error."
    else
    time? "zxpacat compute" (vm_compute;
    lazymatch goal with
    | |- true = true => exact (eq_refl true)
    | |- false = true => fail "These terms are not isomorphic as hypergraphs!"
    end)
  | |- _ => fail "(zxspcat) Unexpected goal when trying to compute isomorphism test! Please report this unexpected error."
  end|fail "(zxspcat) Unexpected additional goal! Please report this unexpected error."..].


Ltac zxparw_lhs lem match_number :=

  let Hrw := fresh "Hrw" in
  time? "zxparw_lhs setup tactic" specialize (zxparw_lhs_lemma) as Hrw;

  let le := fresh "le" in evar (le : list ZXDVERT);
  let lev := eval unfold le in le in
  specialize (Hrw (interp_discrete_hg_inhab lev));

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
  specialize (Hrw lem);

  epose proof (Hrw _ _ _) as Hrw;

  time? "zxparw_lhs quote lem to PRO" (
  do 2 (tryif timeout 2 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote lemma! Have you declared all necessary instances?"));
  time? "zxparw_lhs quote goal to PRO" (
  do 1 (tryif timeout 2 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Timed out trying to quote goal! Have you declared all necessary instances?"));

  time? "zxparw_lhs quote to positive PRO" (epose proof (Hrw _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this unexpected error.")); (* TODO: maybe replace with just tactic? *)

  let ln := fresh "ln" in evar (ln : list nat);
  let lnv := eval unfold ln in ln in
  specialize (Hrw (interp_discrete_hg_inhab lnv));
  epose proof (Hrw _ _ _ _   _ _ _) as Hrw;
  do 3 (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting PRO as a sized MPRO! Please report this unexpected error.");

  (* specialize_with_concr_asgn_list Hrw lnv;
  time? "zxparw_lhs prove correctness of concrete assignment" (
    tryif (timeout 1 (tspecialize Hrw by compute_done)) then idtac
    else fail "Failed to prove concrete assignment map correct! Please report this unexpected error"); *)

  epose proof (Hrw _) as Hrw;
  time? "zxparw_lhs compute rewrite" (tspecialize Hrw; [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ]);

  time? "zxparw_lhs MPRO to PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac
    else fail "Failed interpreting resulting sized MPRO as a PRO! Please report this unexpected error."));

  time? "zxparw_lhs denote from positive PRO" (epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac else
    fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this."));

  time? "zxparw_lhs denote PRO to goal" (epose proof (Hrw _) as Hrw;
  (tryif timeout 10 (tspecialize Hrw by typeclasses eauto) then idtac else
    fail "Timed out trying to denote result! Have you declared all necessary instances?"));
  close_evar_ended_list le; close_evar_ended_list ln;
  subst le ln;
  etransitivity; [apply Hrw|clear Hrw].


Ltac zxparw_rhs lem match_number :=
  symmetry;
  zxparw_lhs lem match_number;
  symmetry.

Ltac zxparw lem match_number :=
  zxparw_lhs lem match_number || zxparw_rhs lem match_number.


Tactic Notation "zxparw_lhs" uconstr(lem) "at" constr(n) :=
  zxparw_lhs lem n.

Tactic Notation "zxparw_lhs" uconstr(lem) :=
  zxparw_lhs lem at O.

Tactic Notation "zxparw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxparw_lhs (symmetry lem) at n.

Tactic Notation "zxparw_lhs" "<-" uconstr(lem) :=
  zxparw_lhs (symmetry lem).

Tactic Notation "zxparw_rhs" uconstr(lem) "at" constr(n) :=
  zxparw_rhs lem n.

Tactic Notation "zxparw_rhs" uconstr(lem) :=
  zxparw_rhs lem at O.

Tactic Notation "zxparw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxparw_rhs (symmetry lem) at n.

Tactic Notation "zxparw_rhs" "<-" uconstr(lem) :=
  zxparw_rhs (symmetry lem).

Tactic Notation "zxparw" uconstr(lem) "at" constr(n) :=
  zxparw lem n.

Tactic Notation "zxparw" uconstr(lem) :=
  zxparw lem at O.

Tactic Notation "zxparw" "<-" uconstr(lem) "at" constr(n) :=
  zxparw (symmetry lem) at n.

Tactic Notation "zxparw" "<-" uconstr(lem) :=
  zxparw (symmetry lem).




Module Examples.


Lemma parametric_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m o β ⟷ Z o p γ ∝=
  Z n m α ⟷ (X m o β ⟷ Z o p γ).
Proof.
  zxpacat.
Qed.


Lemma parametric_stack_associativity_example {n m o p} {α β γ} :
  Z n m α ⟷ X m (o + n + m) β ⟷ (Z o p γ ↕ Z n p γ ↕ Z m p γ) ⟷
    X _ n α ∝=
  Z n m α ⟷ X m (o + (n + m)) β ⟷ (Z o p γ ↕ (Z n p γ ↕ Z m p γ)) ⟷
    X _ n α.
Proof.
  (* Ltac enable_timing ::= idtac. *)
  (* idtac "--------------------------------------". *)

  Time zxpacat.
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
    zxparw (Z_1_2_1_fusion 0 0).
    rewrite Rplus_0_l.
    zxparw IHm.
    zxpacat.
Qed.



Lemma parametric_rewriting_example {n m o p : nat} {α β γ : R} : m <> 0 -> n <> 0 ->
  Z n (p + (m + n)) α ⟷ (n_wire p ↕ (Z m n α ↕ Z n m β)) ⟷
  (n_wire p ↕ zx_comm _ _) ⟷ (n_wire p ↕ (Z m n α ↕ Z n m α)) ⟷
  Z (p + (n + m)) p 0 ∝= Z _ _ 0.
Proof.
  intros Hm Hn.


  (* TODO: Investigate parameter matching like this:
  epose (lem := @Z_absolute_fusion' _ n _ _ _ Hn).
  let lemT := type of lem in
  match lemT with
  | ?R ?lhs _ =>
    eassert (DiagramQuote (ProD:=ZX_Autonomous_ProLike) lhs _)
  end.
  Hint Mode DiagramQuote + + + + - - ! - : typeclass_instances.
  typeclasses eauto.

  TODO: Or maybe we should parse the target term directly using the known
  composition and stacking? In either case, we need to end up with a list
  of _sized_ generators, from which we can try all matches I guess? With
  a warning that that'll be slow? *)



  (* TODO: etc... let lem := lem *)
  zxparw_lhs (@Z_absolute_fusion' m n m α α Hn).
Abort.


End Examples.

End ZXmauto.
