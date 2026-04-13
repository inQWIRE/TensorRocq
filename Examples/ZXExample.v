From TensorRocq Require Export AbstractReasoning.

From TensorRocq Require Import MProp.Automation.

Require Import QArith Qcanon.


#[export] Instance Qc_inhabited : Inhabited Qc := populate 0%Qc.

Declare Custom Entry print_qc.

Notation "q" := (q%Qc%Q) (only printing, q constr at level 9, in custom print_qc at level 0).

Notation "q " := (Qcmake q%Q _) (only printing, q constr at level 9, in custom print_qc at level 0).

Notation " q" := (Q2Qc q%Q) (only printing, q constr  at level 9, in custom print_qc at level 0).


Local Open Scope aprop_scope.

Definition ZX n m := AProp (fin 3 * Qc) n m.

Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 3) n m * AProp (fin 3) n m)%type}})
  (at level 70).

Notation Z n m q := (Agen (0%fin :> fin 3, q%Qc) n m) (only parsing).
Notation X n m q := (Agen (1%fin :> fin 3, q%Qc) n m) (only parsing).
Notation H n     := (Agen (2%fin :> fin 3, 0)    n n) (only parsing).

Notation "'Z' n m q" := (Agen (0%fin, q) n m) (only printing,
  n at level 9, m at level 9,
  q custom print_qc, at level 10).
Notation "'X' n m q" := (Agen (1%fin, q) n m) (only printing,
  n at level 9, m at level 9,
  q custom print_qc, at level 10).
Notation "'H' n"     := (Agen (2%fin, _) n n) (only printing,
  n at level 9, at level 10).

Inductive ZXEq : forall {n m}, relation (ZX n m) :=
  | ZXEq_Z_add_2 n m q :
    ZXEq (Z n m q) (Z n m (2 + q))
  | ZXEq_X_add_2 n m q :
    ZXEq (X n m q) (X n m (2 + q))
  | ZXEq_Z_0_id :
    ZXEq (Z 1 1 0) (id)
  | ZXEq_X_0_id :
    ZXEq (X 1 1 0) (id)
  | ZXEq_fuseZ n m o q q' :
    ZXEq (Z n m q ;' Z m o q') (Z n o (q + q'))
  | ZXEq_fuseX n m o q q' :
    ZXEq (X n m q ;' X m o q') (X n o (q + q'))
  | ZXEq_Z_colorswap n m q :
    ZXEq (Z n m q) (H n ;' X n m q ;' H m)
  | ZXEq_H_idempotent n :
    ZXEq (H n ;' H n) ([[ id n ]])
  | ZXEq_Z_add_r n m m' q q' q'' :
    ZXEq (Z n (m + m') (q + q' + q''))
         (Z n 2 q ;' Z 1 m q' * Z 1 m' q'')
  | ZXEq_Z_add_l n n' m q q' q'' :
    ZXEq (Z (n + n') m (q + q' + q''))
         (Z n 1 q * Z n' 1 q' ;' Z 2 m q'')
  | ZXEq_X_add_r n m m' q q' q'' :
    ZXEq (X n (m + m') (q + q' + q''))
         (X n 2 q ;' X 1 m q' * X 1 m' q'')
  | ZXEq_X_add_l n n' m q q' q'' :
    ZXEq (X (n + n') m (q + q' + q''))
         (X n 1 q * X n' 1 q' ;' X 2 m q'').


Definition ZX_sig : Signature bool := {|
  gens := fin 3 * Qc;
  gens_equiv := eq;
  rules n m := ZXEq
|}.

Notation "x == y" :=
  (x ≡ᵣ@{ZX_sig} y)
  (at level 70).

Lemma X_add_2 n m q : X n m q == X n m (2 + q).
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_2 n m q : Z n m q == Z n m (2 + q).
Proof. apply rules_hold; constructor. Qed.

Lemma X_id : X 1 1 0 == id.
Proof. apply rules_hold; constructor. Qed.

Lemma Z_id : Z 1 1 0 == id.
Proof. apply rules_hold; constructor. Qed.

Lemma fuseZ n m o q q' : Z n m q ;' Z m o q' == Z n o (q + q').
Proof. apply rules_hold; constructor. Qed.

Lemma colorswap n m q : Z n m q == H n ;' X n m q ;' H m.
Proof. apply rules_hold; constructor. Qed.

Lemma fuseX n m o q q' : X n m q ;' X m o q' == X n o (q + q').
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_r n m m' q q' q'' :
  Z n (m + m') (q + q' + q'') == Z n 2 q ;' Z 1 m q' * Z 1 m' q''.
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_l n n' m q q' q'' :
  Z (n + n') m (q + q' + q'') == Z n 1 q * Z n' 1 q' ;' Z 2 m q''.
Proof. apply rules_hold; constructor. Qed.

Lemma X_add_r n m m' q q' q'' :
  X n (m + m') (q + q' + q'') == X n 2 q ;' X 1 m q' * X 1 m' q''.
Proof. apply rules_hold; constructor. Qed.

Lemma X_add_l n n' m q q' q'' :
  X (n + n') m (q + q' + q'') == X n 1 q * X n' 1 q' ;' X 2 m q''.
Proof. apply rules_hold; constructor. Qed.

Example test_fuse : Z 1 2 0 * X 2 1 0 ;' Z 2 1 1 * id ==
  Z 1 1 1 * X 2 1 0.
Proof.
  srw_lhs (fuseZ 1 2 1 0 1).
  smcat.
Qed.

Definition cnot : ZX 2 2 := [[ Z 1 2 0 * id ; id * X 2 1 0 ]].

Definition zmeas (b : bool) := Z 1 0 (if b then 1%Qc else 0).
Definition zcorr (b : bool) := Z 1 1 (if b then 1%Qc else 0).
Definition xmeas (b : bool) := X 1 0 (if b then 1%Qc else 0).
Definition xcorr (b : bool) := X 1 1 (if b then 1%Qc else 0).

Lemma teleportation : forall b,
  id * X 0 1 0 ;' cnot ;' zmeas b * zcorr b == id.
Proof.
  intros [].
  - srw (Z_add_r 1 1 1 0 0 0).
    srw (fuseZ 1 1 0 0 1).
    srw <- (Z_add_r 1 0 1 0 1 0).
    srw (X_add_l 1 1 1 0 0 0).
    srw (fuseX 0 1 1 0 0).
    srw <- (X_add_l 1 0 1 0 0 0).
    srw X_id.
    srw (fuseZ 1 1 1 1 1).
    srw <- (Z_add_2 1 1 0).
    now srw Z_id.
  - srw (Z_add_r 1 1 1 0 0 0).
    srw (fuseZ 1 1 0 0 0).
    srw <- (Z_add_r 1 0 1 0 0 0).
    srw (X_add_l 1 1 1 0 0 0).
    srw (fuseX 0 1 1 0 0).
    srw <- (X_add_l 1 0 1 0 0 0).
    srw X_id.
    now repeat srw Z_id.
Qed.

Lemma test n m o α :
   X n m α * Aid m ;' Aid m * Z m o 2 ==
  Aid n * Z m o 2 ;' X n m α * Aid o.
Proof.
  psmcat.
Qed.

  #[global] Arguments free_monoid_meq_dec_subproof {_ _ _ _ _ _ _ _ _ _} : assert.
  #[global] Arguments free_monoid_meq_dec_subproof0 {_ _ _ _ _ _ _ _ _ _ _} : assert.

Notation "[≈]" := (Massoc _ _ _) (only printing) : mprop_scope.

Lemma SigTensAProp_eq_AProp_semantic_eq
  {A : Type} `{SA : Summable A, EqA : EqDecision A} {Sig : Signature A}
  {n m} {ap ap' : AProp Sig.(gens) n m} :
  SigTensAProp_eq Sig ap ap' ->
  AProp_semantic_eq (TensT:=SignatureTensorLike Sig) ap ap'.
Proof.
  intros Heq.
  unfold SigTensAProp_eq in Heq.
  rewrite 2 SignatureTensorLike_base_correct in Heq.
  apply Heq.
Qed.

Lemma AProp_semantic_eq_SigTensAProp_eq
  {A : Type} `{SA : Summable A, EqA : EqDecision A} {Sig : Signature A}
  {n m} {ap ap' : AProp Sig.(gens) n m} :
  AProp_semantic_eq (TensT:=SignatureTensorLike Sig) ap ap' ->
  SigTensAProp_eq Sig ap ap'.
Proof.
  unfold SigTensAProp_eq.
  rewrite 2 SignatureTensorLike_base_correct.
  easy.
Qed.

Lemma map_aprop_cast {T T'} (f : T -> T')
  {n m n' m'} (Hn : n = n') (Hm : m = m') (ap : AProp T n m) :
  map_aprop f (cast_aprop Hn Hm ap) = cast_aprop Hn Hm (map_aprop f ap).
Proof.
  now subst; rewrite 2 cast_aprop_id.
Qed.

Lemma mprop_of_aprop_cast

Ltac quote_msize :=
  try typeclasses eauto.

Ltac quote_MP :=
  lazymatch goal with
  | |- MProp_of_AProp _ ?apv =>
    lazymatch apv with
    | Agen ?t ?n ?m =>
      notypeclasses refine (mprop_of_aprop_gen _ _ _ _ _ _);
      quote_msize
      (* first [quote_discrete|typeclasses eauto|idtac] *)
    | Acompose ?apv1 ?apv2 =>
      notypeclasses refine (mprop_of_aprop_compose _ _ apv1 apv2 _ _);
      (* notypeclasses refine (aprop_quote_compose f ctx _ _ apv1 apv2 _ _); *)
      quote_MP
    | Astack ?apv1 ?apv2 =>
      notypeclasses refine (mprop_of_aprop_stack _ _ apv1 apv2 _ _);
      quote_MP
    | Aid ?n =>
      notypeclasses refine (mprop_of_aprop_id _ n _);
      quote_msize
    | Acup ?n =>
      notypeclasses refine (mprop_of_aprop_cup _ n _);
      quote_msize
    | Acap ?n =>
      notypeclasses refine (mprop_of_aprop_cap _ n _);
      quote_msize
    | Aswap ?n ?m =>
      notypeclasses refine (mprop_of_aprop_swap _ _ n m _ _);
      quote_msize
    | cast_aprop ?Hn ?Hm ?ap =>
      notypeclasses refine (mprop_of_aprop_cast _ ap Hn Hm _);
      quote_MP
    end
  end.


Ltac quote_MP_step :=
  lazymatch goal with
  | |- MProp_of_AProp _ ?apv =>
    lazymatch apv with
    | Agen ?t ?n ?m =>
      notypeclasses refine (mprop_of_aprop_gen _ _ _ _ _ _);
      quote_msize
      (* first [quote_discrete|typeclasses eauto|idtac] *)
    | Acompose ?apv1 ?apv2 =>
      notypeclasses refine (mprop_of_aprop_compose _ _ apv1 apv2 _ _);
      (* notypeclasses refine (aprop_quote_compose f ctx _ _ apv1 apv2 _ _); *)
      idtac (* quote_MP *)
    | Astack ?apv1 ?apv2 =>
      notypeclasses refine (mprop_of_aprop_stack _ _ apv1 apv2 _ _);
      idtac (* quote_MP *)
    | Aid ?n =>
      notypeclasses refine (mprop_of_aprop_id _ n _);
      quote_msize
    | Acup ?n =>
      notypeclasses refine (mprop_of_aprop_cup _ n _);
      quote_msize
    | Acap ?n =>
      notypeclasses refine (mprop_of_aprop_cap _ n _);
      quote_msize
    | Aswap ?n ?m =>
      notypeclasses refine (mprop_of_aprop_swap _ _ n m _ _);
      quote_msize
    | cast_aprop ?Hn ?Hm ?ap =>
      notypeclasses refine (mprop_of_aprop_cast _ ap Hn Hm _);
      idtac (* quote_MP *)
    end
  end.

Lemma test' n m o α β :
  Z n m α * Aid m ;' Aswap m m ;' Aid m * Z m o β ==
  Z n o (α + β) * Aid m ;' Aswap o m.
Proof.
  pose proof (fuseZ n m o α β) as Hrw.
  unshelve (
  epose proof (APROPlike_para_rewrite_helper_correctness
    (TensT:=SignatureTensorLike ZX_sig)
    (APROPlikeD:=(APROPlike_AProp (TensT:=SignatureTensorLike ZX_sig))) 0 ?[ctx] ?[l] _ _

    (Z n m α * Aid m ;' Aswap m m ;' Aid m * Z m o β) (* Targ *)

    (SigTensAProp_eq_AProp_semantic_eq Hrw) (* lem *)

    _ _ _ _ _ _ _

    ) as Hrew;
  do 3 tspecialize Hrew by typeclasses eauto; (* DiagramQuote *)
  do 2 tspecialize Hrew by typeclasses eauto; (* APropQuote *)
  do 2 tspecialize Hrew by typeclasses eauto);
  [exact nil|exact nil|]. (* MProp_of_AProp *)
  vm_eval (sized_term_rewrite_helper _ _ _).
  vm_eval (sized_graph_iso_partial_test _ _).
  specialize (Hrew _ _ _ _ _ _).
  specialize (Hrew eq_refl eq_refl eq_refl eq_refl).
  rewrite 2? cast2_id in Hrew.
  etransitivity; [apply (AProp_semantic_eq_SigTensAProp_eq Hrew)|].
  cbn.
  rewrite ?cast_aprop_id, ?map_aprop_cast.
  cbn.

  (* psmcat. *)
  apply SigTens_graph_semantics_syntactic_eq.
  unshelve (eapply (APropQuote_correct_syntactic_eq'
    interp_discrete_hg_inhab _);
  [quote_AP..|]); [exact nil|].


  eapply (AProp_syntax_eq_by_MProp_syntax_eq_correct_denote_nat_bw _).
  repeat try quote_MP_step.
  Print Instances QuoteMonoidSize.
  typeclasses eauto.
  quote_MP_step.
  quote_MP_step.
  quote_MP_step.
  quote_MP_step.
  quote_MP_step.


  [quote_MP..|].
  [try apply _..|]).
  3:{
    eapply mprop_of_aprop_compose.
  }
  apply sized_graph_iso_partial_test_correct;
  vm_compute; exact (eq_refl true)); exact (@nil nat).
  psmcat.

  cbn.
  psmcat.
  clear Hrew.


  free_monoid_meq_dec

  (* unfold SigTensAProp_eq. *)
  assert ({P : Type & P}).
  econstructor.
  (* FSR_eqg *)
  refine .
  5:{

    (* refine Hrw. *)
    unfold SigTensAProp_eq in Hrw.
    rewrite 2 SignatureTensorLike_base_correct in Hrw.
    refine Hrw.
  }.

    unfold base.equiv in *.
    unfold AProp_semantic_eq.
    refine Hrw.

    refine Hrw.
    SigTens SignatureTensorLike_base
    refine Hrw.
  }
    Hrw). as Hrew.

    _ _ _ _ _ _ _ ) as Hrew.

  MProp_of_AProp
  (* apply SigTens_graph_semantics_syntactic_eq.
  unshelve (eapply (APropQuote_correct_syntactic_eq'
    interp_discrete_hg_inhab _);
  [quote_AP..|]); [exact nil|];
  unshelve (eapply (AProp_syntax_eq_by_MProp_syntax_eq_correct_denote_nat_bw _);
  [apply _..|];
  apply sized_graph_iso_partial_test_correct;
  vm_compute; exact (eq_refl true)); exact (@nil nat). *)
  psmcat.
Qed.

  apply SigTens_graph_semantics_syntactic_eq;
  unshelve (eapply (APropQuote_correct_syntactic_eq'
    interp_discrete_hg_inhab _);
  [quote_AP..|]); [exact nil|];
  unshelve (eapply (AProp_syntax_eq_by_MProp_syntax_eq_correct_denote_nat_bw _);
  [apply _..|];
  apply sized_graph_iso_partial_test_correct;
  vm_compute; exact (eq_refl true)); exact (@nil nat).
