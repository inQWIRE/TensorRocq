From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.
From TensorRocqEx Require Export ZXrw_base.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)

Import Props.



Module ZXsymm.

Export GeneratorNotations.

Section ZXquote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_SymmetricG_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_quote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_quote_symm_n_wire n : Quote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_symm_wire : Quote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_empty : Quote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_symm_zx_comm n m : Quote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_symm_swap : Quote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.


Lemma zx_quote_symm_cup : Quote ⊂ (Pgen 0 2 (inl (Some (inl (false, 0%R))))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

Lemma zx_quote_symm_cap : Quote ⊃ (Pgen 2 0 (inl (Some (inl (false, 0%R))))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.


Lemma zx_quote_symm_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_symm_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_symm_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.


Lemma zx_quote_symm_cast_lr {n m n' m'} (Hn : n = n') (Hm : m = m')
  (zx : ZX n' m') (ap : PROP ZXDVERT n' m')
  (apl : PROP ZXDVERT n n') (apr : PROP ZXDVERT m' m) :
  DiagramQuote zx ap ->
  DiagramQuote (cast _ _ Hn eq_refl (n_wire _)) apl ->
  DiagramQuote (cast _ _ eq_refl Hm (n_wire _)) apr ->
  DiagramQuote (cast _ _ Hn Hm zx) (apl ;; ap ;; apr).
Proof.
  intros [Hap] [Hapl] [Hapr].
  constructor.
  cbn.
  rewrite Hap, Hapl, Hapr.
  cbn -[cast].
  f_equiv.
  rewrite n_wire_removal_r', n_wire_removal_l'.
  rewrite cast_contract_eq'.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_l {n m n'} (Hn : n = n') (Hm : m = m)
  (zx : ZX n' m) (ap : PROP ZXDVERT n' m)
  (apl : PROP ZXDVERT n n') :
  DiagramQuote zx ap ->
  DiagramQuote (cast _ _ Hn eq_refl (n_wire _)) apl ->
  DiagramQuote (cast _ _ Hn Hm zx) (apl ;; ap).
Proof.
  intros [Hap] [Hapl].
  constructor.
  cbn.
  rewrite Hap, Hapl.
  cbn -[cast].
  f_equiv.
  rewrite n_wire_removal_l'.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_r {n m m'} (Hn : n = n) (Hm : m = m')
  (zx : ZX n m') (ap : PROP ZXDVERT n m')
  (apr : PROP ZXDVERT m' m) :
  DiagramQuote zx ap ->
  DiagramQuote (cast _ _ eq_refl Hm (n_wire _)) apr ->
  DiagramQuote (cast _ _ Hn Hm zx) (ap ;; apr).
Proof.
  intros [Hap] [Hapr].
  constructor.
  cbn.
  rewrite Hap, Hapr.
  cbn -[cast].
  f_equiv.
  rewrite n_wire_removal_r'.
  cast_irrelevance.
Qed.

Lemma zx_quote_symm_cast_id {n m} (Hn : n = n) (Hm : m = m)
  (zx : ZX n m) (ap : PROP ZXDVERT n m) :
  DiagramQuote zx ap ->
  DiagramQuote (cast _ _ Hn Hm zx) (ap).
Proof.
  rewrite CastRules.cast_id_eq.
  done.
Qed.

Lemma zx_quote_symm_cast_n_wire {n m k} (Hn : n = k) (Hm : m = k) :
  DiagramQuote (ProD:=ZX_SymmetricG_ProLike) (cast n m Hn Hm (n_wire k))
    (Pgen _ _ (inr (bundleDiagram (cast n m
      (Canonize.canonize (eq_trans_r Hn Hm)) eq_refl (n_wire m))))).
Proof.
  constructor.
  cbn - [unbundleDiagram].
  rewrite unbundleDiagram_bundleDiagram.
  f_equiv.
  rewrite (@cast_n_wire_l m), (@cast_n_wire_l k).
  cast_irrelevance.
Qed.

#[export] Instance zx_quote_symm_Z n m α α' : Rsimpl_modeq_2PI α α' ->
  Quote (Z n m α) (Pgen n m (inl (Some (inl (false, α'))))) | 1.
Proof.
  intros Hα.
  constructor.
  cbn.
  f_equiv.
  apply Z_Rmodeq_2PI.
  symmetry; apply Hα.
Qed.

#[export] Instance zx_quote_symm_X n m α α' : Rsimpl_modeq_2PI α α' ->
  Quote (X n m α) (Pgen n m (inl (Some (inl (true, α'))))) | 1.
Proof.
  intros Hα.
  constructor.
  cbn.
  f_equiv.
  apply X_Rmodeq_2PI.
  symmetry; apply Hα.
Qed.

#[export] Instance zx_quote_symm_Z_wire :
  Quote (Z 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite Z_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_X_wire :
  Quote (X 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite X_0_is_wire, <- wire_to_n_wire.
Qed.

#[export] Instance zx_quote_symm_H : Quote (Box) (Pgen 1 1 (inl None)).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_quote_symm_const c : Quote (zx_of_const c) (Pgen 0 0 (inl (Some (inr c)))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_symm_scale c {n m} (zx : ZX n m) ap :
  Quote zx ap -> Quote (zx_scale c zx) (Pgen 0 0 (inl (Some (inr c))) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_quote_symm_stack 0 0); apply _.
Qed.

#[export] Instance zx_quote_symm_abs {n m} (zx : ZX n m) :
  Quote zx (Pgen n m (inr (bundleDiagram zx))) | 50.
Proof.
  constructor.
  cbn -[nat_pair_eq_dec_eval].
  case_match; [|done].
  rewrite (proof_irrel _ eq_refl); done.
Qed.

End ZXquote_symm.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) ⊂ _) =>
  exact (zx_quote_symm_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) ⊃ _) =>
  exact (zx_quote_symm_cap) : typeclass_instances.

(*
#[export] Hint Extern 0 (DiagramQuote (n_cup ?n) _) =>
  exact (zx_quote_symm_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (n_cap ?n) _) =>
  exact (zx_quote_symm_cup n) : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) (?zx ↕ ?zx') _) =>
  notypeclasses refine (zx_quote_symm_stack zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) (?zx ⟷ ?zx') _) =>
  notypeclasses refine (zx_quote_symm_compose zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_quote_symm_scale c n m val _ _): typeclass_instances.

(* #[export] Hint Extern 10 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) (?val) _) =>
  progress first [unfold val|simpl] : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=SymmetricG) (D:=ZX) (zx_comm ?n ?m) _) =>
  exact (zx_quote_symm_zx_comm n m) : typeclass_instances.

Module QuoteCast.

Import Ltac2 ConstrExtra BWQuote.

(* In the non-parametric case, this will _always_ serve to simply eliminate
  casts (which must be definitional equalities). However, writing it this
  way allows for proper handling of parametric sizes via monoidal paths *)
Ltac2 solve_zx_symm_quote_cast_nonmonoidal () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m ?n' ?m' ?hn ?hm ?zx) ?ap] =>
    let n_id := quote_constr_eq_timeout 1 n n' in
    let m_id := quote_constr_eq_timeout 1 m m' in
    match n_id, m_id with
    | true, true =>
      let prf := '(@zx_quote_symm_cast_id $n' $m' $hn $hm $zx $ap) in
      apply $prf
    | true, false =>
      let prf := '(@zx_quote_symm_cast_r $n $m $m' $hn $hm $zx _ _ (* _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()] *)
    | false, true =>
      let prf := '(@zx_quote_symm_cast_l $n $m $n' $hn $hm $zx _ _ (* _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()] *)
    | false, false =>
      let prf := '(@zx_quote_symm_cast_lr $n $m $n' $m' $hn $hm $zx _ _ _  (* _ _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()|solve_zx_symm_quote_cast_n_wire()] *)
    end
  end.

End QuoteCast.

Ltac zx_symm_quote_cast_tac :=
  lazymatch goal with
  |- (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
    (cast ?n ?m ?hn ?hm ?zx) _) =>
    lazymatch zx with
    | n_wire ?k => tryif (timeout 1 (unify n m; unify k m)) then
        apply (zx_quote_symm_cast_id hn hm)
        else fail
    | ⦰ => tryif (timeout 1 (unify n m; unify O m)) then
        apply (zx_quote_symm_cast_id hn hm)
        else refine (zx_quote_symm_cast_n_wire hn hm)
    | _ =>
      ltac2:(QuoteCast.solve_zx_symm_quote_cast_nonmonoidal())
    end
  end.

#[export] Hint Extern 2 (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast ?n ?m ?hn ?hm ?zx) _) =>
  zx_symm_quote_cast_tac : typeclass_instances.


Ltac zx_symm_quote_n_wire_cast_tac_backup :=
  lazymatch goal with
  |- (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
    (cast ?n ?m ?hn ?hm (n_wire _)) _) =>
    refine (zx_quote_symm_cast_n_wire hn hm)
  end.

#[export] Hint Extern 1 (DiagramQuote (Struct:=SymmetricG) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire _)) _) =>
  zx_symm_quote_n_wire_cast_tac_backup : typeclass_instances.




Section ZXdenote_symm.

Local Set Typeclasses Unique Instances.

Local Notation Denote := (DiagramDenote (ProD:=ZX_SymmetricG_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_denote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_denote_symm_n_wire n : Denote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_symm_wire : Denote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_denote_symm_empty : Denote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_symm_zx_comm n m : Denote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_symm_swap : Denote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.

(* Lemma zx_denote_symm_n_cap n : Denote (n_cup n) (Pcap n).
Proof.
  constructor.
  cbn -[n_cup].
  rewrite <- (tensor_of_matrix_of_tensor (ZX_tensor_semantics _)).
  rewrite ZX_tensor_semantics_correct.
  apply tensor_of_matrix_n_cup_semantics.
Qed.

Lemma zx_denote_symm_n_cup n : Denote (n_cap n) (Acup n).
Proof.
  constructor.
  cbn -[n_cap].
  rewrite <- (tensor_of_matrix_of_tensor (ZX_tensor_semantics _)).
  rewrite ZX_tensor_semantics_correct.
  unfold n_cap.
  rewrite semantics_transpose_comm.
  rewrite tensor_of_matrix_transpose.
  intros v w Hv Hw.
  rewrite tensor_of_matrix_n_cup_semantics by done.
  done.
Qed. *)


Lemma zx_denote_symm_cup : Denote ⊂ (Pgen 0 2 (inl (Some (inl (false, 0%R))))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

Lemma zx_denote_symm_cap : Denote ⊃ (Pgen 2 0 (inl (Some (inl (false, 0%R))))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.


#[export] Instance zx_denote_symm_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_denote_symm_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_denote_symm_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Denote zx ap ->
  Denote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_denote_symm_Z n m α : Denote (Z n m α) (Pgen n m (inl (Some (inl (false, α))))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_symm_X n m α : Denote (X n m α) (Pgen n m (inl (Some (inl (true, α))))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_symm_H : Denote (Box) (Pgen 1 1 (inl None)).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_denote_symm_const c : Denote (zx_of_const c) (Pgen 0 0 (inl (Some (inr c)))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_symm_scale c {n m} (zx : ZX n m) ap :
  Denote zx ap -> Denote (zx_scale c zx) (Pgen 0 0 (inl (Some (inr c))) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_denote_symm_stack 0 0); apply _.
Qed.

Lemma zx_denote_symm_abs {n m} (zx : ZX n m) :
  Denote zx (Pgen n m (inr (bundleDiagram zx))).
Proof.
  apply DiagramQuote_iff_DiagramDenote.
  apply _.
Qed.

Lemma zx_denote_symm_abs' {n m} (zx : ZX n m) :
  Denote zx (Pgen n m (inr (existT (n, m) zx))).
Proof.
  apply DiagramQuote_iff_DiagramDenote.
  apply _.
Qed.

Lemma zx_denote_symm_abs_casted {n m n' m'} (zx : ZX n m) Hn Hm :
  Denote (cast _ _ Hn Hm zx) (Pgen n' m' (inr (bundleDiagram zx))).
Proof.
  subst.
  rewrite cast_id_eq.
  apply zx_denote_symm_abs.
Qed.

Lemma zx_denote_symm_abs'_casted {n m n' m'} (zx : ZX n m) Hn Hm :
  Denote (cast _ _ Hn Hm zx) (Pgen n' m' (inr (existT (n, m) zx))).
Proof.
  apply zx_denote_symm_abs_casted.
Qed.


End ZXdenote_symm.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pgen 0 2 (Some (inl (false, 0%R))))) =>
  exact (zx_denote_symm_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pgen 2 0 (Some (inl (false, 0%R))))) =>
  exact (zx_denote_symm_cap) : typeclass_instances.

(*
#[export] Hint Extern 0 (DiagramDenote (n_cup ?n) _) =>
  exact (zx_denote_symm_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (n_cap ?n) _) =>
  exact (zx_denote_symm_cup n) : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pstack ?p ?p')) =>
  notypeclasses refine (zx_denote_symm_stack _ _ p p' _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pcompose ?p ?p')) =>
  notypeclasses refine (zx_denote_symm_compose _ _ p p' _ _) : typeclass_instances.

(* #[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike)
  (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_denote_symm_scale c n m val _ _): typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pswap 1 1)) =>
  exact (zx_denote_symm_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ (Pswap ?n ?m)) =>
  exact (zx_denote_symm_zx_comm n m) : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ ([str inr (Swap 1 1)])) =>
  exact (zx_denote_symm_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_SymmetricG_ProLike) _ ([str inr (Swap ?n ?m)])) =>
  exact (zx_denote_symm_zx_comm n m) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (Struct:=SymmetricG) (D:=ZX) _ (Pgen ?n' ?m' (inr (@bundleDiagram _ ?n ?m ?zx)))) =>
  tryif (timeout 1 (unify n n'; unify m m')) then
    exact (zx_denote_symm_abs zx)
  else
    exact (zx_denote_symm_abs_casted zx (ltac:(lia) : n' = n) (ltac:(lia) : m' = m))
  : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (Struct:=SymmetricG) (D:=ZX) _ (Pgen ?n' ?m' (inr (existT (?n, ?m) ?zx)))) =>
  tryif (timeout 1 (unify n n'; unify m m')) then
    exact (zx_denote_symm_abs' zx)
  else
    exact (zx_denote_symm_abs'_casted zx (ltac:(lia) : n' = n) (ltac:(lia) : m' = m))
  : typeclass_instances.


Ltac zx_symm_simplify_quote_tac :=
  let rec go zx :=
    lazymatch zx with
    | @Compose ?n ?m ?o ?zxl ?zxr =>
      eapply (@zx_quote_symm_compose n m o zxl zxr _ _);
      [go zxl|go zxr]
    | @Stack ?n ?m ?n' ?m' ?zxl ?zxr =>
      eapply (@zx_quote_symm_stack n m n' m' zxl zxr _ _);
      [go zxl|go zxr]
    | _ => idtac
    end in
  lazymatch goal with
  |- DiagramQuote ?zx _ =>
    go zx
  end.

Ltac zx_symm_simplify_denote_tac :=
  let rec go zx :=
    lazymatch zx with
    | @Compose ?n ?m ?o ?zxl ?zxr =>
      eapply (@zx_denote_symm_compose n m o zxl zxr _ _);
      [go zxl|go zxr]
    | @Stack ?n ?m ?n' ?m' ?zxl ?zxr =>
      eapply (@zx_denote_symm_stack n m n' m' zxl zxr _ _);
      [go zxl|go zxr]
    | _ => idtac
    end in
  lazymatch goal with
  |- DiagramDenote ?zx _ =>
    go zx
  end.


Ltac zxsbypro_setup :=
  eapply (DiagramQuote_correct _ _ (LawProD:=ZX_SymmetricG_lawpro)).

Ltac zxsbypro :=
  zxsbypro_setup; [tryif timeout 3 (typeclasses eauto) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?"..|].



Ltac setup_zxsrw_lhs lem match_number :=
  etransitivity; [
    (
    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXCVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (LawfulProLike_PRO_monog_quote_rewrite_correct
          _ _ _ _ _  (ZX_SymmetricG_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number lem) as Hrw
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end))|].


Ltac zxsviz_internal :=
  SizedProQuote.prop_visualize_goal ZX_SymmetricG_ProLike.

Ltac zxsviz_lhs_internal :=
  SizedProQuote.prop_visualize_lhs ZX_SymmetricG_ProLike.

Ltac zxsviz_rhs_internal :=
  SizedProQuote.prop_visualize_rhs ZX_SymmetricG_ProLike.


Ltac zxsviz :=
  tryif visualize_flag then
    zxsviz_internal
  else idtac.

Ltac zxsviz_lhs :=
  tryif visualize_flag then
    zxsviz_lhs_internal
  else idtac.

Ltac zxsviz_rhs :=
  tryif visualize_flag then
    zxsviz_rhs_internal
  else idtac.




Definition zxscat_lemma := LawfulProLike_PRO_quote_test_correct
  (T':=positive) _ _ _ _ _  (ZX_SymmetricG_lawpro).

Definition zxsrw_lhs_lemma := LawfulProLike_PRO_monog_quote_rewrite_correct
  (T':=positive) _ _ _ _ _  (ZX_SymmetricG_lawpro).

Definition zxsclean_lhs_lemma := LawfulProLike_PRO_monog_quote_clean_correct
  (T':=positive) _ _ _ _ _  (ZX_SymmetricG_lawpro).

(* Redefine this to enable/disable printing after rewriting *)
Ltac zxsrw_visualize_after :=
  zxsviz.


Ltac zxsrw_lhs_parse Hrw l lem match_number :=
  evar (l : list ZXDVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?tgt _ =>
    lazymatch type of lem with
    | ?R ?lhs ?rhs =>
      specialize (zxsrw_lhs_lemma
        (interp_discrete_hg_inhab lv) _ _ lhs rhs _ _ tgt match_number lem) as Hrw
      (* specialize (LawfulProLike_PRO_monog_quote_rewrite_correct
        _ _ _ _ _  (ZX_SymmetricG_lawpro)
        (interp_discrete_hg_inhab lv) lhs rhs tgt match_number lem) as Hrw *)
    | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
    end
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end.

Ltac zxsrw_lhs_quote_tac :=
  zx_symm_simplify_quote_tac; once typeclasses eauto.

Ltac zxsrw_lhs_quote Hrw :=
  epose proof (Hrw _ _ _) as Hrw;
  (tryif timeout 3 (do 3 tspecialize Hrw by zxsrw_lhs_quote_tac) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?").


Ltac zxsrw_lhs_to_pos_tac :=
  once typeclasses eauto.

Ltac zxsrw_lhs_to_pos Hrw l :=
  epose proof (Hrw _ _ _) as Hrw;
  (timeout 3 (
    do 3 (tspecialize Hrw by zxsrw_lhs_to_pos_tac)
   ) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
  let lv := eval unfold l in l in
  SizedProQuote.close_evar_ended_list lv.


Ltac zxsrw_lhs_compute Hrw :=
  tspecialize Hrw by (
    vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end).

Ltac zxsrw_lhs_from_pos_tac :=
  once typeclasses eauto.

Ltac zxsrw_lhs_from_pos Hrw :=
  epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by zxsrw_lhs_from_pos_tac) then idtac else
    fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.").

Ltac zxsrw_lhs_denote_tac :=
  zx_symm_simplify_denote_tac; once typeclasses eauto.

Ltac zxsrw_lhs_denote Hrw :=
  epose proof (Hrw _) as Hrw;
  (tryif timeout 3 (tspecialize Hrw by zxsrw_lhs_denote_tac) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?").

Ltac zxsrw_lhs_final Hrw :=
  etransitivity; [apply Hrw|clear Hrw].

Ltac zxsrw_lhs lem match_number :=

  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  zxsrw_lhs_parse Hrw l lem match_number;
  zxsrw_lhs_quote Hrw;
  zxsrw_lhs_to_pos Hrw l;
  epose proof (Hrw _) as Hrw;
  zxsrw_lhs_compute Hrw;
  zxsrw_lhs_from_pos Hrw;
  zxsrw_lhs_denote Hrw;
  zxsrw_lhs_final Hrw.

Ltac zxsrw_rhs lem match_number :=
  symmetry;
  zxsrw_lhs lem match_number;
  symmetry.

Ltac zxsrw lem match_number :=
  zxsrw_lhs lem match_number || zxsrw_rhs lem match_number.


Tactic Notation "zxsrw_lhs" uconstr(lem) "at" constr(n) :=
  zxsrw_lhs lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw_lhs" uconstr(lem) :=
  zxsrw_lhs lem at O.

Tactic Notation "zxsrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw_lhs (symmetry lem) at n.

Tactic Notation "zxsrw_lhs" "<-" uconstr(lem) :=
  zxsrw_lhs (symmetry lem).

Tactic Notation "zxsrw_rhs" uconstr(lem) "at" constr(n) :=
  zxsrw_rhs lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw_rhs" uconstr(lem) :=
  zxsrw_rhs lem at O.

Tactic Notation "zxsrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw_rhs (symmetry lem) at n.

Tactic Notation "zxsrw_rhs" "<-" uconstr(lem) :=
  zxsrw_rhs (symmetry lem).

Tactic Notation "zxsrw" uconstr(lem) "at" constr(n) :=
  zxsrw lem n;
  zxsrw_visualize_after.

Tactic Notation "zxsrw" uconstr(lem) :=
  zxsrw lem at O.

Tactic Notation "zxsrw" "<-" uconstr(lem) "at" constr(n) :=
  zxsrw (symmetry lem) at n.

Tactic Notation "zxsrw" "<-" uconstr(lem) :=
  zxsrw (symmetry lem).

  (* Redefine this to enable/disable printing after cleaning *)
Ltac zxsclean_visualize_after :=
  zxsviz.

Ltac zxsclean_lhs_aux :=
  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXDVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (zxsclean_lhs_lemma
          (interp_discrete_hg_inhab lv) _ _ tgt) as Hrw
      (* specialize (LawfulProLike_PRO_monog_quote_clean_correct
          _ _ _ _ _  (ZX_SymmetricG_lawpro)
          (interp_discrete_hg_inhab lv) tgt) as Hrw *)
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "simplified term could not be extracted from graph! Please report this error. "
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxsclean_lhs :=
  zxsclean_lhs_aux;
  zxsclean_visualize_after.

Ltac zxsclean_rhs :=
  symmetry; zxsclean_lhs_aux; symmetry;
  zxsclean_visualize_after.

Ltac zxsclean := zxsclean_lhs_aux; zxsclean_rhs.

Ltac zxscat_visualize_before :=
  zxsviz.

Ltac zxscat :=
  zxscat_visualize_before;
  (unshelve

  (
  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  evar (l : list ZXDVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    specialize (zxscat_lemma (interp_discrete_hg_inhab lv) _ _ lhs rhs) as Hrw
  | |- ?G => fail "cannot recognize goal as the application of a relation: " G
  end;
  (tryif timeout 3 (specialize (Hrw _ _ _ _)) then idtac else
    fail "Timed out trying to quote goal! Have you declared all necessary instances?");
  epose proof (Hrw _ _) as Hrw;
  (do 2 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
  tspecialize Hrw;
  [vm_compute;
  lazymatch goal with
  | |- true = true => reflexivity
  | |- false = true => fail "terms are not isomorphic! (as hypergraphs)"
  end
  | ];
  apply Hrw)); exact nil.





Module Examples.




Theorem hopf_rule_Z_X :
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  apply prop_by_iff_zx_scale.
  split; [|intros ?%(f_equal fst); cbn in *; lra].
  zxsviz.
  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r_fwd.
  rewrite cast_id_eq.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  zxsrw <- (@Z_spider_1_1_fusion 0 2 0 0).
  replace (0%R) with (0 + 0)%R by lra.
  rewrite <- X_spider_1_1_fusion.
  zxsrw (to_gadget (proportional_by_sym bi_algebra_rule_Z_X)).

  unshelve (rewrite (X_wrap_under_bot_right 1)); [lia..|].



  (* zxsclean_lhs. *)
  (* rewrite cup_Z. *)


  zxsrw_lhs (to_gadget Z_state_0_copy 2 eq_refl eq_refl).

  rewrite <- Z_0_is_wire at 1.
  zxsrw (symmetry (@Z_add_l 0 1 0 0 0 0)).
  zxsrw (@Z_spider_1_1_fusion 0 2 0 0).
  zxsrw (cup_pullthrough_top (X 1 0 0) —).
  rewrite <- zx_of_const_mult'.
  replace (zx_of_const _)%C with (zx_of_const (/ C2))%C
    by (apply (f_equal zx_of_const); cbn; autorewrite with RtoC_db; C_field).
  zxscat.
Qed.


Theorem hopf_rule_Z_X_vert n m top bot α β prf :
  Z n (top + 2) α ↕ n_wire bot ⟷
  cast _ _ prf eq_refl
    (n_wire top ↕ X (2 + bot) m β) ∝[/ C2] Z n top α ↕ X bot m β.
Proof.
  Admitted.

Theorem bi_algebra_rule_X_over_Z :
  X 1 2 0 ↕ — ⟷ (— ↕ Z 2 1 0) ⟷ ⨉
  ⟷ (X 1 2 0 ↕ —) ⟷ (— ↕ Z 2 1 0) ∝[/ (√2)%R]
  Z 1 2 0 ↕ — ⟷ (— ↕ X 2 1 0).
Proof.
  zxsymmetry.
  apply prop_by_iff_zx_scale.
  split; [|nonzero].

  rewrite (Z_wrap_over_top_right).
  rewrite (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl).

  zxsrw_lhs (to_gadget bi_algebra_rule_X_Z).

  assert (Hrw1 : X 1 2 0 ∝= — ↕ ⊂ ⟷ (— ↕ X 1 2 0 ↕ —) ⟷ (⊃ ↕ n_wire 2)). 1:{
    rewrite cup_X, cap_X.
    zxsrw (dominated_X_spider_fusion_top_left 2 0 1 0 0 0).
    zxsrw (X_spider_fusion_bot_left_top_right 1 0 2 0 0 0 0 eq_refl eq_refl).
    done.
  }
  (* rewrite <- cap_Z, <- cup_Z. *)
  assert (Hrw2 : Z 2 1 0 ∝= (n_wire 2 ↕ ⊂) ⟷ (— ↕ Z 2 1 0 ↕ —) ⟷ (⊃ ↕ —)). 1:{
    zxsrw (Z_spider_fusion_bot_left_top_right 1 0 1 0 1 0 0 eq_refl eq_refl).
    zxsrw_rhs (Z_spider_fusion_bot_left_top_right 1 0 1 1 0 0 0 eq_refl eq_refl).
    done.
  }
  rewrite Hrw1 at 1.
  rewrite Hrw2 at 2.
  Fail zxscat.
Admitted.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  rewrite notc_is_swapp_cnot.
  zxscat.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxscat.
Qed.

Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split. 2:{
    apply nonzero_div_nonzero, Cmult_neq_0; nonzero.
  }

  rewrite cnot_is_swapp_notc at 2.
  rewrite notc_is_notc_r.
  zxsrw (to_gadget bi_algebra_rule_X_over_Z).

  zxsrw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  zxsrw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  zxsrw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxsrw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr.
  zxscat.
Qed.

End Examples.

End ZXsymm.