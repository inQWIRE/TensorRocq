From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.
From TensorRocqEx Require Export ZXrw_base.
From TensorRocqEx Require Export ZXrwsymm ZXrwauto.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)

Import Props.


Module ZXfrob.

Section ZXquote_frob.

Local Set Typeclasses Unique Instances.

Local Notation Quote := (DiagramQuote (ProD:=ZX_Frobenius_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_quote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_quote_frob_n_wire n : Quote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_frob_wire : Quote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_quote_frob_empty : Quote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_quote_frob_zx_comm n m : Quote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_quote_frob_swap : Quote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.


Lemma zx_quote_frob_n_cap n : Quote (n_cup n) (Pcap n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcap].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv].
  - now rewrite n_cup_0_empty.
  - now rewrite n_cup_1_cup.
  - done.
Qed.

Lemma zx_quote_frob_n_cup n : Quote (n_cap n) (Pcup n).
Proof.
  constructor.
  cbn [PRO_to_diagram Pcup].
  f_equiv.
  destruct n as [|[|n]]; cbn -[equiv n_cap].
  - now rewrite n_cap_0_empty.
  - now rewrite n_cap_1_cap.
  - done.
Qed.


Lemma zx_quote_frob_cup : Quote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_quote_frob_cap : Quote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


Lemma zx_quote_frob_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_frob_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Quote zx ap -> Quote zx' ap' ->
  Quote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_quote_frob_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.



Lemma zx_quote_frob_cast_lr {n m n' m'} (Hn : n = n') (Hm : m = m')
  (zx : ZX n' m') (ap : FPROP ZXDVERT n' m')
  (apl : FPROP ZXDVERT n n') (apr : FPROP ZXDVERT m' m) :
  Quote zx ap ->
  Quote (cast _ _ Hn eq_refl (n_wire _)) apl ->
  Quote (cast _ _ eq_refl Hm (n_wire _)) apr ->
  Quote (cast _ _ Hn Hm zx) (apl ;; ap ;; apr).
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

Lemma zx_quote_frob_cast_l {n m n'} (Hn : n = n') (Hm : m = m)
  (zx : ZX n' m) (ap : FPROP ZXDVERT n' m)
  (apl : FPROP ZXDVERT n n') :
  Quote zx ap ->
  Quote (cast _ _ Hn eq_refl (n_wire _)) apl ->
  Quote (cast _ _ Hn Hm zx) (apl ;; ap).
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

Lemma zx_quote_frob_cast_r {n m m'} (Hn : n = n) (Hm : m = m')
  (zx : ZX n m') (ap : FPROP ZXDVERT n m')
  (apr : FPROP ZXDVERT m' m) :
  Quote zx ap ->
  Quote (cast _ _ eq_refl Hm (n_wire _)) apr ->
  Quote (cast _ _ Hn Hm zx) (ap ;; apr).
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

Lemma zx_quote_frob_cast_id {n m} (Hn : n = n) (Hm : m = m)
  (zx : ZX n m) (ap : FPROP ZXDVERT n m) :
  Quote zx ap ->
  Quote (cast _ _ Hn Hm zx) (ap).
Proof.
  rewrite CastRules.cast_id_eq.
  done.
Qed.

Lemma zx_quote_frob_cast_n_wire {n m k} (Hn : n = k) (Hm : m = k) :
  Quote (cast n m Hn Hm (n_wire k))
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


Lemma PRO_to_diagram_Pdelta_1 n m : n + m <> O ->
  PRO_to_diagram (Pdelta 1 n m) ≡ Some (Z _ _ 0).
Proof.
  cbn.
  intros Hnm.
  f_equiv.
  rewrite ZX_copy_1.
  rewrite cast_Z.
  done.
Qed.

Lemma PRO_to_diagram_Pdelta1 n m :
  PRO_to_diagram (Pdelta1 n m) ≡ Some (Z _ _ 0).
Proof.
  done.
Qed.

Lemma zx_quote_frob_Z_0 n m : Quote (Z n m 0) (Pdelta1 n m).
Proof.
  constructor.
  now apply PRO_to_diagram_Pdelta1.
Qed.

Lemma zx_quote_frob_Z_add (n m : nat) α β d d' :
  Quote (Z 1 0 β) d -> Quote (Z 1 0 α) d' ->
  Quote (Z n m (α + β))
  (Pdelta1 n (S (S m)) ;; d * d' * Pid m).
Proof.
  intros Hd Hd'.
  rewrite Z_push_out_phase_gadget'.
  rewrite (Z_push_out_phase_gadget n).
  rewrite ComposeRules.compose_assoc.
  rewrite <- (pull_out_top (Z 1 0 β)).
  rewrite (stack_assoc_back_fwd (Z 1 0 β) (Z 1 0 α)), cast_id_eq.
  apply zx_quote_frob_compose.
  - apply zx_quote_frob_Z_0.
  - apply (@zx_quote_frob_stack (1 + 1) (0 + 0) m m); typeclasses eauto.
Qed.

Lemma zx_quote_frob_Z_phase α :
  Quote (Z 1 0 α) ([gen (inl (Some (inl (false, α)))) 1 0]).
Proof.
  done.
Qed.

Lemma zx_quote_frob_Z n m α : DiagramQuote (Z n m α)
  (Pdelta1 n (S m) ;; [gen (inl (Some (inl (false, α)))) 1 0] * Pid m).
Proof.
  rewrite Z_push_out_phase_gadget.
  pose proof zx_quote_frob_Z_phase.
  pose proof zx_quote_frob_Z_0.
  change (S m) with (1 + m).
  eauto with zarith typeclass_instances.
Qed.

#[export] Instance zx_quote_frob_h_stack n : Quote (n_stack1 n Box)
  ([gen (inl None) n n]) | 1.
Proof.
  constructor.
  cbn.
  case_decide; [|done].
  rewrite cast_id_eq.
  done.
Qed.

#[export] Instance zx_quote_frob_h : Quote Box
  ([gen (inl None) 1 1]).
Proof.
  rewrite <- nstack1_1.
  apply _.
Qed.

Lemma zx_quote_frob_X n m α d :
  Quote (n_stack1 n Box ⟷ (Z n m α ⟷ n_stack1 m Box))
    d -> Quote (X n m α) d.
Proof.
  apply DiagramQuote_proper_equiv, reflexivity.
  rewrite <- colorswap_is_bihadamard.
  done.
Qed.











#[export] Instance zx_quote_frob_Z_cup :
  Quote (Z 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_Z.
  done.
Qed.

#[export] Instance zx_quote_frob_Z_cap :
  Quote (Z 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_Z.
  done.
Qed.
(*
#[export] Instance zx_quote_frob_X_cup :
  Quote (X 0 2 0) (Pcup 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cap_X.
  done.
Qed.

#[export] Instance zx_quote_frob_X_cap :
  Quote (X 2 0 0) (Pcap 1) | 0.
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite cup_X.
  done.
Qed. *)

#[export] Instance zx_quote_frob_Z_wire :
  Quote (Z 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite Z_0_is_wire, <- wire_to_n_wire.
Qed.

(* #[export] Instance zx_quote_frob_X_wire :
  Quote (X 1 1 0) (Pid 1) | 0.
Proof.
  constructor.
  cbn -[n_wire].
  f_equiv.
  now rewrite X_0_is_wire, <- wire_to_n_wire.
Qed. *)


#[export] Instance zx_quote_frob_const c : Quote (zx_of_const c) (Pgen 0 0 (inl (Some (inr c)))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_quote_frob_scale c {n m} (zx : ZX n m) ap :
  Quote zx ap -> Quote (zx_scale c zx) (Pgen 0 0 (inl (Some (inr c))) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_quote_frob_stack 0 0); apply _.
Qed.

Lemma zx_quote_frob_Z_gen n m α :
  Quote (Z n m α) (Pdelta1 n (S m) ;; Pgen 1 0 (inl (Some (inl (false, α)))) * Pid m).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite <- Z_push_out_phase_gadget.
  done.
Qed.

#[export] Instance zx_quote_frob_abs {n m} (zx : ZX n m) :
  Quote zx (Pgen n m (inr (bundleDiagram zx))) | 50.
Proof.
  constructor.
  cbn -[nat_pair_eq_dec_eval].
  case_match; [|done].
  rewrite (proof_irrel _ eq_refl); done.
Qed.

End ZXquote_frob.


Ltac zx_quote_frob_Z_tac_step :=
  match goal with
  | |- DiagramQuote (Z ?n ?m (?alpha + ?beta)) _ =>
    notypeclasses refine (zx_quote_frob_Z_add n m alpha beta _ _ _ _)
  | |- DiagramQuote (Z ?n ?m 0) _ =>
    notypeclasses refine (zx_quote_frob_Z_0 n m _); lia
  | |- DiagramQuote (Z 1 0 ?alpha)_  =>
    notypeclasses refine (zx_quote_frob_Z_phase alpha)
  | |- DiagramQuote (Z ?n ?m ?alpha) _ =>
    exact (zx_quote_frob_Z n m alpha)
  end.

Ltac zx_quote_frob_Z_tac := zx_quote_frob_Z_tac_step; repeat zx_quote_frob_Z_tac_step.

(*
#[export] Hint Extern 0 (DiagramQuote (Z ?n ?m ?alpha) _) =>
  solve [zx_quote_frob_Z_tac|let _ := match goal with
    |- ?G => idtac "FAIL ON" G end in idtac] : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (Z ?n ?m 0) _) =>
  exact (zx_quote_frob_Z_0 n m) : typeclass_instances.


#[export] Hint Extern 1 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (Z ?n ?m ?alpha) _) =>
  exact (zx_quote_frob_Z_gen n m alpha) : typeclass_instances.

#[export] Hint Extern 3 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (X ?n ?m ?α) _) =>
  notypeclasses refine (zx_quote_frob_X n m α _ _);
  cbn : typeclass_instances.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) ⊂ _) =>
  exact (zx_quote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) ⊃ _) =>
  exact (zx_quote_frob_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (n_cup ?n) _) =>
  exact (zx_quote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (n_cap ?n) _) =>
  exact (zx_quote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (?zx ↕ ?zx') _) =>
  notypeclasses refine (zx_quote_frob_stack zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (?zx ⟷ ?zx') _) =>
  notypeclasses refine (zx_quote_frob_compose zx zx' _ _ _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_quote_frob_scale c n m val _ _): typeclass_instances.

(* #[export] Hint Extern 10 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (?val) _) =>
  progress first [unfold val|simpl] : typeclass_instances. *)

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX) (zx_comm ?n ?m) _) =>
  exact (zx_quote_frob_zx_comm n m) : typeclass_instances.


Module QuoteCast.

Import Ltac2 ConstrExtra BWQuote.

(* In the non-parametric case, this will _always_ serve to simply eliminate
  casts (which must be definitional equalities). However, writing it this
  way allows for proper handling of parametric sizes via monoidal paths *)
Ltac2 solve_zx_frob_quote_cast_nonmonoidal () : unit :=
  lazy_match! goal with
  | [|- DiagramQuote (@cast ?n ?m ?n' ?m' ?hn ?hm ?zx) ?ap] =>
    let n_id := quote_constr_eq_timeout 1 n n' in
    let m_id := quote_constr_eq_timeout 1 m m' in
    match n_id, m_id with
    | true, true =>
      let prf := '(@zx_quote_frob_cast_id $n' $m' $hn $hm $zx $ap) in
      apply $prf
    | true, false =>
      let prf := '(@zx_quote_frob_cast_r $n $m $m' $hn $hm $zx _ _ (* _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()] *)
    | false, true =>
      let prf := '(@zx_quote_frob_cast_l $n $m $n' $hn $hm $zx _ _ (* _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()] *)
    | false, false =>
      let prf := '(@zx_quote_frob_cast_lr $n $m $n' $m' $hn $hm $zx _ _ _  (* _ _ _ *)) in
      apply $prf
      (* > [|solve_zx_symm_quote_cast_n_wire()|solve_zx_symm_quote_cast_n_wire()] *)
    end
  end.

End QuoteCast.

#[export] Hint Extern 0 (DiagramQuote (Struct:=Frobenius) (D:=ZX)
  (cast ?n ?m ?hn ?hm ?zx) _) =>
  lazymatch zx with
  | n_wire ?k => tryif (timeout 1 (unify n m; unify k m)) then
      apply (zx_quote_frob_cast_id hn hm)
      else refine (zx_quote_frob_cast_n_wire hn hm)
  | ⦰ => tryif (timeout 1 (unify n m; unify O m)) then
      apply (zx_quote_frob_cast_id hn hm)
      else refine (zx_quote_frob_cast_n_wire hn hm)
  | _ =>
    ltac2:(QuoteCast.solve_zx_frob_quote_cast_nonmonoidal())
  end : typeclass_instances.

#[export] Hint Extern 20 (DiagramQuote (Struct:=Frobenius) (D:=ZX)
  (cast ?n ?m ?hn ?hm (n_wire _)) _) =>
  refine (zx_quote_frob_cast_n_wire hn hm) : typeclass_instances.



Section ZXdenote_frob.

Local Set Typeclasses Unique Instances.

Local Notation Denote := (DiagramDenote (ProD:=ZX_Frobenius_ProLike)).

(* We make some of these lemmas and use hints to solve issues with typeclass search
  in the case of explicit sizes (e.g., typeclass search won't always apply
  zx_denote_swap to [Aswap 2 2], at least when [2 + 2] has been reduced
  to [4], which is hard to systematically avoid)*)

#[export] Instance zx_denote_frob_n_wire n : Denote (n_wire n) (Pid n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_frob_wire : Denote (Wire) (Pid 1).
Proof.
  constructor.
  cbn.
  f_equiv.
  apply symmetry, wire_to_n_wire.
Qed.

#[export] Instance zx_denote_frob_empty : Denote (⦰) (Pid 0).
Proof.
  constructor.
  done.
Qed.

#[export] Instance zx_denote_frob_zx_comm n m : Denote (zx_comm n m) (Pswap n m).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_frob_swap : Denote (⨉) (Pswap 1 1).
Proof.
  constructor; cbn.
  f_equiv.
  apply zx_comm_1_1_swap.
Qed.

Lemma zx_denote_frob_n_cap n : Denote (n_cup n) (Pcap n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_frob_n_cap.
Qed.

Lemma zx_denote_frob_n_cup n : Denote (n_cap n) (Pcup n).
Proof.
  apply DiagramQuote_iff_DiagramDenote, zx_quote_frob_n_cup.
Qed.


Lemma zx_denote_frob_cup : Denote ⊂ (Pcup 1).
Proof.
  constructor.
  done.
Qed.

Lemma zx_denote_frob_cap : Denote ⊃ (Pcap 1).
Proof.
  constructor.
  done.
Qed.


#[export] Instance zx_denote_frob_compose {n m o} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ m o) : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ⟷ zx') (Pcompose ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

Lemma zx_denote_frob_stack {n m n' m'} zx zx' (ap : PRO _ _ n m)
  (ap' : PRO _ _ n' m') : Denote zx ap -> Denote zx' ap' ->
  Denote (zx ↕ zx') (Pstack ap ap').
Proof.
  intros [Heq1] [Heq2].
  constructor; cbn.
  rewrite Heq1, Heq2.
  done.
Qed.

#[export] Instance zx_denote_frob_cast {n m n' m'} (Hn : n = n') (Hm : m = m')
  zx ap : Denote zx ap ->
  Denote (cast _ _ Hn Hm zx) (cast_PRO (eq_sym Hn) (eq_sym Hm) ap).
Proof.
  subst.
  now rewrite cast_PRO_id, cast_id_eq.
Qed.

#[export] Instance zx_denote_frob_Z n m α : Denote (Z n m α) (Pgen n m (inl (Some (inl (false, α))))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_frob_X n m α : Denote (X n m α) (Pgen n m (inl (Some (inl (true, α))))).
Proof.
  constructor; done.
Qed.

#[export] Instance zx_denote_frob_H : Denote (Box) (Pgen 1 1 (inl None)).
Proof.
  constructor.
  cbn.
  constructor.
  rewrite stack_empty_r_fwd, cast_contract_eq', cast_id_eq.
  done.
Qed.

#[export] Instance zx_denote_frob_const c : Denote (zx_of_const c) (Pgen 0 0 (inl (Some (inr c)))).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_frob_scale c {n m} (zx : ZX n m) ap :
  Denote zx ap -> Denote (zx_scale c zx) (Pgen 0 0 (inl (Some (inr c))) * ap).
Proof.
  rewrite zx_scale_defn.
  intros.
  apply (@zx_denote_frob_stack 0 0); apply _.
Qed.


Lemma zx_denote_frob_Pdelta_1 n m : n + m <> O ->
  Denote (Z (n * 1) (m * 1) 0)
  (Pstruct _ _ (inr (Delta 1 n m))).
Proof.
  constructor.
  rewrite PRO_to_diagram_Pdelta_1 by done.
  done.
Qed.

Lemma zx_denote_frob_Pdelta_0 :
  Denote (Z 0 0 0)
  (Pstruct _ _ (inr (Delta 1 0 0))).
Proof.
  constructor.
  cbn.
  f_equiv.
  rewrite ZX_copy_1, cast_id_eq.
  done.
Qed.

Lemma zx_denote_frob_Pdelta1 n m : Denote (Z n m 0) (Pdelta1 n m).
Proof.
  constructor; done.
Qed.


#[export] Instance zx_denote_frob_abs {n m} (zx : ZX n m) :
  Denote zx (Pgen n m (inr (bundleDiagram zx))).
Proof.
  apply DiagramQuote_iff_DiagramDenote.
  apply _.
Qed.

#[export] Instance zx_denote_frob_abs' {n m} (zx : ZX n m) :
  Denote zx (Pgen n m (inr (bundleDiagram zx))).
Proof.
  apply DiagramQuote_iff_DiagramDenote.
  apply _.
Qed.

End ZXdenote_frob.

(* A few of these instances don't resolve nicely when sizes simplify,
  so we help typeclass resolution apply them with these hints. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcup 1)) =>
  exact (zx_denote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcap 1)) =>
  exact (zx_denote_frob_cap) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cup 1))])) =>
  exact (zx_denote_frob_cup) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cap 1))])) =>
  exact (zx_denote_frob_cap) : typeclass_instances.


#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcup ?n)) =>
  exact (zx_denote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcap ?n)) =>
  exact (zx_denote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cup ?n))])) =>
  exact (zx_denote_frob_n_cup n) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inr (Cap ?n))])) =>
  exact (zx_denote_frob_n_cap n) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pstack ?p ?p')) =>
  notypeclasses refine (zx_denote_frob_stack _ _ p p' _ _) : typeclass_instances.

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pcompose ?p ?p')) =>
  notypeclasses refine (zx_denote_frob_compose _ _ p p' _ _) : typeclass_instances.

(* #[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike)
  (@zx_scale ?n ?m ?c ?val) _) =>
  notypeclasses refine (@zx_denote_frob_scale c n m val _ _): typeclass_instances. *)

#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pswap 1 1)) =>
  exact (zx_denote_frob_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ (Pswap ?n ?m)) =>
  exact (zx_denote_frob_zx_comm n m) : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inl (inr (Swap 1 1)))])) =>
  exact (zx_denote_frob_swap) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inl (inl (inr (Swap ?n ?m)))])) =>
  exact (zx_denote_frob_zx_comm n m) : typeclass_instances.

#[export] Hint Extern 1 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta 1 ?n ?m)])) =>
  let H := fresh in
  tryif assert (H : n + m <> O) by lia then
    exact (zx_denote_frob_Pdelta_1 n m H)
  else fail : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta 1 0 0)])) =>
  exact zx_denote_frob_Pdelta_0 : typeclass_instances.


#[export] Hint Extern 0 (DiagramDenote (ProD:=ZX_Frobenius_ProLike) _ ([str inr (Delta1 ?n ?m)])) =>
  exact (zx_denote_frob_Pdelta1 n m) : typeclass_instances.


Ltac zxfbypro_setup :=
  eapply (DiagramQuote_correct _ _ (LawProD:=ZX_Frobenius_lawpro)).

Ltac zxfbypro :=
  zxfbypro_setup; [tryif timeout 3 (typeclasses eauto) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?"..|].


Definition zxfcat_lemma := LawfulProLike_PRO_quote_test_correct
  (T':=positive) _ _ _ _ _  (ZX_Frobenius_lawpro).

Definition zxfrw_lhs_lemma := LawfulProLike_PRO_frobenius_quote_rewrite_correct
  (T':=positive) _ _ _ _ _  (ZX_Frobenius_lawpro).

Definition zxfclean_lhs_lemma := LawfulProLike_PRO_frobenius_quote_clean_correct
  (T':=positive) _ _ _ _ _  (ZX_Frobenius_lawpro).

Ltac setup_zxfrw_lhs lem match_number quotient_number :=
  etransitivity; [
    (
    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXDVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (zxfrw_lhs_lemma
          (interp_discrete_hg_inhab lv) _ _ lhs rhs _ _ tgt match_number quotient_number lem) as Hrw
        (* specialize (LawfulProLike_PRO_frobenius_quote_rewrite_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw *)
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end))|].

Ltac zxfrw_lhs lem match_number quotient_number :=

  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXDVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      lazymatch type of lem with
      | ?R ?lhs ?rhs =>
        specialize (zxfrw_lhs_lemma
          (interp_discrete_hg_inhab lv) _ _ lhs rhs _ _ tgt match_number quotient_number lem) as Hrw
        (* specialize (LawfulProLike_PRO_frobenius_quote_rewrite_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
          (interp_discrete_hg_inhab lv) lhs rhs tgt match_number quotient_number lem) as Hrw *)
      | ?lemT => fail "cannot recognize lemma (type) as the application of a relation: " lemT
      end
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _ _ _ _ _)) then idtac else
      fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _ _ _) as Hrw;
    (do 3 (tspecialize Hrw by typeclasses eauto) || fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw;
    [vm_compute;
    lazymatch goal with
    | |- ?R (Some _) (Some _) => reflexivity
    | |- ?R None _ => fail "could not find the specified rewrite!"
    end
    | ];
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this.");

    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
      fail "Timed out trying to denote result! Have you declared all necessary instances?");

    apply Hrw)); exact nil|].

Ltac zxfrw_rhs lem match_number quotient_number :=
  symmetry;
  zxfrw_lhs lem match_number quotient_number;
  symmetry.

Ltac zxfrw lem match_number quotient_number :=
  zxfrw_lhs lem match_number quotient_number || zxfrw_rhs lem match_number quotient_number.


Tactic Notation "zxfrw_lhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_lhs lem n q.

Tactic Notation "zxfrw_lhs" uconstr(lem) "at" constr(n) :=
  zxfrw_lhs lem at n quotient O.

Tactic Notation "zxfrw_lhs" uconstr(lem) :=
  zxfrw_lhs lem at O.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_lhs (symmetry lem) at n quotient q.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw_lhs (symmetry lem) at n.

Tactic Notation "zxfrw_lhs" "<-" uconstr(lem) :=
  zxfrw_lhs (symmetry lem).


Tactic Notation "zxfrw_rhs" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_rhs lem n q.

Tactic Notation "zxfrw_rhs" uconstr(lem) "at" constr(n) :=
  zxfrw_rhs lem at n quotient O.

Tactic Notation "zxfrw_rhs" uconstr(lem) :=
  zxfrw_rhs lem at O.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw_rhs (symmetry lem) at n quotient q.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw_rhs (symmetry lem) at n.

Tactic Notation "zxfrw_rhs" "<-" uconstr(lem) :=
  zxfrw_rhs (symmetry lem).


Tactic Notation "zxfrw" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw lem n q.

Tactic Notation "zxfrw" uconstr(lem) "at" constr(n) :=
  zxfrw lem at n quotient O.

Tactic Notation "zxfrw" uconstr(lem) :=
  zxfrw lem at O.

Tactic Notation "zxfrw" "<-" uconstr(lem) "at" constr(n) "quotient" constr(q) :=
  zxfrw (symmetry lem) at n quotient q.

Tactic Notation "zxfrw" "<-" uconstr(lem) "at" constr(n) :=
  zxfrw (symmetry lem) at n.

Tactic Notation "zxfrw" "<-" uconstr(lem) :=
  zxfrw (symmetry lem).


Ltac zxfmrw_lhs rwe :=
  (* let rwe := constr:(![rw {box_compose}]) in *)

  etransitivity; [
    (unshelve
    (
    etransitivity;
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXDVERT);
    let lv := eval unfold l in l in
    specialize (LawfulProLike_PRO_frobenius_quote_multi_rewrite_correct
      (ZX_Frobenius_lawpro)
      (interp_discrete_hg_inhab lv)) as Hrw;
    epose proof (Hrw rwe _ _ _) as Hrw;
    (tryif timeout 3 (tspecialize Hrw by typeclasses eauto) then idtac else
      fail "Timed out trying to quote the rewrite rule!");

    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (Hrw _ _ tgt)
    | |- ?G => fail "cannot recognize goal as the application of a relation: " G
    end;
    (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Timed out trying to quote goal! Have you declared all necessary instances?");
    epose proof (Hrw _) as Hrw;
    ((tspecialize Hrw by typeclasses eauto) ||
      fail "Failed to perform PRO quotation (to convert to computational domain)! Please report this." );
    epose proof (Hrw _) as Hrw;
    tspecialize Hrw; [
      vm_compute;
      lazymatch goal with
      | |- ?R (inl _) (inl _) => reflexivity
      | |- ?R (inr ?e) _ => fail
        "rewriting failed, with the following error: " e
      end
      | ];
      (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Failed to perform PRO unquotation (to convert from computational domain)! Please report this error. ");

      (tryif timeout 3 (specialize (Hrw _ _)) then idtac else
        fail "Timed out trying to denote result! Have you declared all necessary instances?");

      apply Hrw)); exact nil|].

Ltac zxfmrw_rhs rwe :=
  symmetry;
  zxfmrw_lhs rwe;
  symmetry.

Ltac zxfmrw rwe :=
  zxfmrw_lhs rwe + zxfmrw_rhs rwe.


Tactic Notation "zxfmrw_lhs" uconstr(rwe) :=
  zxfmrw_lhs rwe.

Tactic Notation "zxfmrw_rhs" uconstr(rwe) :=
  zxfmrw_rhs rwe.

Tactic Notation "zxfmrw" uconstr(rwe) :=
  zxfmrw rwe.


Ltac zxfclean_lhs :=
  etransitivity; [
    (unshelve

    (
    let l := fresh "l" in
    let Hrw := fresh "Hrw" in
    evar (l : list ZXDVERT);
    let lv := eval unfold l in l in
    lazymatch goal with
    | |- ?R ?tgt _ =>
      specialize (zxfclean_lhs_lemma
          (interp_discrete_hg_inhab lv) _ _ tgt) as Hrw
      (* specialize (LawfulProLike_PRO_frobenius_quote_clean_correct
          _ _ _ _ _  (ZX_Frobenius_lawpro)
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

Ltac zxfclean_rhs :=
  symmetry; zxfclean_lhs; symmetry.

Ltac zxfclean := zxfclean_lhs; zxfclean_rhs.

Ltac zxfcat :=
  (unshelve

  (
  let l := fresh "l" in
  let Hrw := fresh "Hrw" in
  evar (l : list ZXDVERT);
  let lv := eval unfold l in l in
  lazymatch goal with
  | |- ?R ?lhs ?rhs =>
    specialize (zxfcat_lemma
        (interp_discrete_hg_inhab lv) _ _ lhs rhs) as Hrw
    (* specialize (LawfulProLike_PRO_quote_test_correct
        _ _ _ _ _  (ZX_Frobenius_lawpro)
        (interp_discrete_hg_inhab lv) lhs rhs) as Hrw *)
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


Lemma bi_algebra_rule_X_Z_gen n n' m m' α α' β β' :
  Z (n + n') 1 (α + α') ⟷ X 1 (m + m') (β + β') ∝[√ 2]
  (Z n 1 α ↕ Z n' 1 α') ⟷ (
    (X 1 2 0 ↕ X 1 2 0 ⟷ (— ↕ ⨉ ↕ —) ⟷ (Z 2 1 0 ↕ Z 2 1 0))
  ) ⟷ (X 1 m β ↕ X 1 m' β').
Proof.
  rewrite <- (Rplus_0_r α).
  rewrite Z_add_l.
  rewrite <- (Rplus_0_r β).
  rewrite X_add_r.
  rewrite ComposeRules.compose_assoc, <- (ComposeRules.compose_assoc (Z 2 1 0)).
  zxrewrite bi_algebra_rule_X_Z.
  zxrefl.
  rewrite 2 Rplus_0_r.
  rewrite <- !ComposeRules.compose_assoc.
  f_equiv.
  rewrite !ComposeRules.compose_assoc.
  f_equiv.
  rewrite <- !ComposeRules.compose_assoc.
  done.
Qed.

Lemma bi_algebra_rule_Z_X_gen n n' m m' α α' β β' :
  X (n + n') 1 (α + α') ⟷ Z 1 (m + m') (β + β') ∝[√ 2]
  (X n 1 α ↕ X n' 1 α') ⟷ (
    (Z 1 2 0 ↕ Z 1 2 0 ⟷ (— ↕ ⨉ ↕ —) ⟷ (X 2 1 0 ↕ X 2 1 0))
  ) ⟷ (Z 1 m β ↕ Z 1 m' β').
Proof.
  colorswap_of (bi_algebra_rule_X_Z_gen n n' m m' α α' β β').
Qed.


Lemma zx_of_const_mult' (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ⟷ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxfcat.
Qed.

Import ZXsymm ZXauto.

Lemma box_to_transpose : □ ∝= (⊂ ⟷ (— ↕ □)) ↕ — ⟷ (— ↕ ⊃).
Proof.
  rewrite cup_pullthrough_bot_1.
  zxfcat.
Qed.

Theorem hopf_rule_Z_X :
  (Z_Spider 1 2 0) ⟷ (X_Spider 2 1 0) ∝[/C2] (Z_Spider 1 0 0) ⟷ (X_Spider 0 1 0).
Proof.
  apply prop_by_iff_zx_scale.
  split; [|intros ?%(f_equal fst); cbn in *; lra].


  rewrite <- (@nwire_removal_r 2).
  cbv delta [n_wire]; simpl.
  rewrite stack_empty_r_fwd.
  rewrite cast_id_eq.
  rewrite wire_loop at 1.
  rewrite cap_Z.
  rewrite cup_X.
  rewrite <- (Rplus_0_l 0).
  zxsclean_lhs.
  rewrite <- X_spider_1_1_fusion, <- Z_spider_1_1_fusion.
  rewrite Rplus_0_l.
  zxfrw_lhs (to_gadget (proportional_by_sym bi_algebra_rule_Z_X)) at 0.
  zxfrw_lhs (X_wrap_under_bot_right 1 1 0 eq_refl eq_refl) at 1.
  zxfrw_lhs (to_gadget Z_state_0_copy 2 eq_refl eq_refl).
  cbn.
  rewrite <- zx_of_const_mult'.
  replace (_ * / √ 2)%C with (/ C2)%C by (autorewrite with RtoC_db; C_field).
  rewrite box_to_transpose.
  zxfcat.
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
    apply colorswap_diagrams_eq.
    cbn.
    zxfcat.
  }
  rewrite Hrw1 at 1.
  zxfcat.
Qed.

Lemma cnot_is_swapp_notc : _CNOT_ ∝= ⨉ ⟷ _NOTC_ ⟷ ⨉.
Proof.
  zxfcat.
Qed.


Lemma zx_of_const_mult (c d : C) : zx_of_const (c * d) ∝=
  zx_of_const c ↕ zx_of_const d.
Proof.
  rewrite 3 zx_of_const_to_scaled_empty.
  distribute_zxscale.
  rewrite Cmult_comm.
  zxfcat.
Qed.

Lemma _3_cnot_swap_is_swap : _3_CNOT_SWAP_ ∝[/ (C2 * √2)] ⨉.
Proof.
  apply prop_by_iff_zx_scale.
  split. 2:{
    apply nonzero_div_nonzero, Cmult_neq_0; nonzero.
  }

  rewrite cnot_is_swapp_notc at 2.
  rewrite notc_is_notc_r.
  zxfrw (to_gadget bi_algebra_rule_X_over_Z).

  zxfrw (@dominated_Z_spider_fusion_top_left 2 0 1 1 0 0).
  (* rewrite Rplus_0_l. *)
  zxfrw (@dominated_X_spider_fusion_bot_right 2 0 1 1 0 0).
  rewrite Rplus_0_l.
  zxfrw (to_gadget hopf_rule_Z_X_vert 1 1 1 1 0 0 eq_refl).
  zxfrw (symmetry (zx_of_const_mult (/ C2) (/ √ 2))).
  rewrite Cinv_mult_distr.
  zxfrw box_compose.
  zxfcat.
Qed.

End Examples.

End ZXfrob.

