Require Import Aux_pos.
Require Import Tensor.
From stdpp Require Import list fin_maps.
From stdpp Require Import pmap gmap.
Require Import TensorExprDBSyntax TensorExprDBSemantics.
Require Import ZXCore.
Require ZifyBool.
Require Import TensorGraphExpr TensorGraphSemantics.

#[local] Coercion pos_to_nat_pred : positive >-> nat.

Open Scope nat_scope.

(* FIXME: Move *)
Lemma forall_var (P : var -> Prop) :
  (forall v, P v) <-> (forall r, P (rel r)) /\ (forall l, P (loc l)) /\
    (forall g, P (glob g)).
Proof.
  split; [auto|].
  now intros (?&?&?) [].
Qed.
Lemma fmap_to_map_imap `{FinMap K M} `(f : A -> B) (m : M A) :
  f <$> m =@{M B} map_imap (λ _ a, Some (f a)) m.
Proof.
  apply map_eq.
  intros k.
  rewrite lookup_fmap, map_lookup_imap.
  now destruct (m !! k).
Qed.
Lemma map_fmap_imap `{FinMap K M} `(f : K -> A -> option B) `(g : B -> C) (m : M A) :
  g <$> map_imap f m =@{M C} map_imap (λ k a, g <$> (f k a)) m.
Proof.
  rewrite fmap_to_map_imap, map_imap_compose.
  reflexivity.
Qed.

#[export] Instance from_option_dec {A} (P : Prop) (Q : A -> Prop) (ma : option A) :
  Decision P -> (forall a, Decision (Q a)) -> Decision (from_option Q P ma) :=
  fun HP HQ =>
  match ma with
  | Some a => (HQ a)
  | None => HP
  end.

Lemma filter_snd_imap_pair_compose {A B} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (f : nat -> B) (l : list A) :
  filter (P ∘ snd) (imap (pair ∘ f) l) =
  (prod_map f id) <$> filter (P ∘ snd) (imap pair l).
Proof.
  revert B f;
  induction l; intros B f; [reflexivity|].
  cbn.
  case_decide as HPa.
  - cbn.
    f_equal.
    rewrite Combinators.compose_assoc, 2 IHl.
    rewrite <- list_fmap_compose.
    reflexivity.
  - rewrite Combinators.compose_assoc, 2 IHl.
    rewrite <- list_fmap_compose.
    reflexivity.
Qed.

Lemma from_option_fmap {A B C} (f : A -> B) (g : B -> C) (d : C) (ma : option A) :
  from_option g d (f <$> ma) = from_option (g ∘ f) d ma.
Proof.
  now destruct ma.
Qed.


Lemma filter_snd_imap_pair {A} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  filter (P ∘ snd) (imap pair l) =
  imap (λ idx v, ((filter (λ i, from_option P False (l !! i)) (seq 0 (length l))) !!! idx, v))
    (filter P l).
Proof.
  induction l; [reflexivity|].
  cbn.
  eenough (Hen : _).
  - case_decide as HPa; [|exact Hen].
    cbn.
    f_equal.
    apply Hen.
  - rewrite (filter_snd_imap_pair_compose P S).
    rewrite IHl.
    rewrite fmap_imap.
    apply imap_ext.
    intros i x Hi.
    cbn.
    f_equal.
    rewrite <- fmap_S_seq.
    symmetry.
    rewrite (list_filter_fmap S).
    unfold compose; cbn.
    apply list_lookup_total_fmap.
    apply lookup_lt_Some in Hi as Hilt.
    eapply Nat.lt_le_trans; [apply Hilt|].
    apply eq_reflexivity.
    clear.
    induction l; [reflexivity|].
    cbn.
    eenough (Heq : _).
    + case_decide as HPa; [|exact Heq].
      cbn.
      rewrite Heq.
      reflexivity.
    + rewrite <- fmap_S_seq, (list_filter_fmap S).
      rewrite length_fmap.
      apply IHl.
Qed.


Lemma length_filter_snd_imap_pair {A} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  length (filter (P ∘ snd) (imap pair l)) =
  length (filter P l).
Proof.
  now rewrite filter_snd_imap_pair, length_imap.
Qed.



Section TensorGraphFacts.

Context `{TensT : TensorLike R A T}.

Context `{SR : SemiRing R rO rI radd rmul req}.

(* Notation "0" := rO.
Notation "1" := rI. *)
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







Let TensorGraph := @TensorGraph T.

Definition graph_tabs (tg : TensorGraph) : abstypecontext :=
  kmap (Pos.of_succ_nat) $ map_imap (fun k (dt : T) =>
    let inarity := in_arity tg.2 k in
    let outarity := out_arity tg.2 k in
    Some (replicate (inarity + outarity) O)
    ) tg.1.

Definition graph_tl (tg : TensorGraph) : vartypecontext :=
  (gmaps_to_Pmap (set_to_map (fun k => (k, 0)) (inputs tg))
    (set_to_map (fun k => (k, 0)) (outputs tg))).

Definition graph_type_context (tg : TensorGraph) : typecontext :=
  mk_tc (graph_tabs tg) ∅ (graph_tl tg) [].



Lemma graph_semantics_WT tg :
  well_typed (graph_type_context tg) (graph_tensorlist_semantics tg).
Proof.
  apply tl_well_typed_correct.
  cbn.
  unfold tl_well_typed_aux.
  rewrite 2 Forall_fmap, Forall_forall.
  intros (n & dt) Hn%elem_of_map_to_list.
  cbn.
  unfold graph_tabs.
  rewrite lookup_kmap by apply _.
  rewrite map_lookup_imap.
  cbn.
  rewrite Hn.
  cbn.
  f_equal.
  rewrite fmap_const, reverse_replicate.
  unfold input_edges, output_edges.
  (* rewrite !length_app, !length_fmap. *)
  apply (fun H => list_eq_same_length _ _ _ H eq_refl).
  - unfold node_input_edges, node_output_edges.
    (* rewrite Permutation_swap_app_app. *)

    rewrite !length_fmap, length_replicate.
    rewrite !length_app, !length_fmap, <- 3 length_app, length_app.
    f_equal.
    + rewrite length_app, 2 length_filter_snd_imap_pair, <- length_app.
      rewrite <- filter_app.
      eapply Permutation_length.
      eapply filter_Permutation.
      apply filter_with_neg_Permutation.
    + rewrite length_app, 2 length_filter_snd_imap_pair, <- length_app.
      rewrite <- filter_app.
      eapply Permutation_length.
      eapply filter_Permutation.
      apply filter_with_neg_Permutation.
  - rewrite length_fmap, length_replicate.
    intros i x y Hi.
    rewrite list_lookup_fmap.
    destruct (replicate _ _ !! _) as [ri|] eqn:Hri; [|easy].
    apply lookup_replicate in Hri as [-> _].
    cbn.
    intros [= <-].
    intros Hhyp; symmetry; revert Hhyp.
    refine ((Forall_lookup (.= Some 0) _).1 _ i y).
    clear i Hi.
    rewrite Forall_fmap.
    rewrite 3 Forall_app, 4 ! Forall_fmap.
    unfold compose; cbn.
    unfold node_input_edges, node_output_edges.
    rewrite 4 Forall_filter.
    unfold i_internal_edges, i_external_edges.
    rewrite app_nil_r.
    split; (split; apply Forall_forall; intros (k, e) Hke%elem_of_enumerate;
      intros [= Hen];
      [apply lookup_replicate, (conj eq_refl); cbn;
        apply lookup_lt_Some in Hke; lia|]);
    unfold graph_tl; rewrite lookup_gmaps_to_Pmap, lookup_set_to_map by easy;
    [exists e.1|exists e.2]; (split; [|cbn; f_equal; lia]);
    unfold inputs, outputs;
    rewrite elem_of_filter, elem_of_list_to_set;
    apply elem_of_list_lookup_2 in Hke;
    unfold external_edges in Hke;
    apply elem_of_list_filter in Hke;
    pose proof (mk_is_Some _ _ Hn : is_key tg.1 n) as Hkey;
    unfold not_internal, is_internal in Hke;
    cbn in *;
    (split; [subst n; tauto|]);
    now apply elem_of_list_fmap_1.
Qed.

Context `{Summable A}.



(* Lemma mk_node_perm_eq lint lext lint' lext' k :
  lint ≡ₚ lint' ->
  lext ≡ₚ lext' ->
  abs_perm_eq (mk_node lint lext k) (mk_node lint' lext' k).
Proof.
  intros Hlint Hlext.
  split; [easy|]; cbn.
  unfold input_edges, output_edges, node_input_edges, node_output_edges.
  now rewrite Hlint, Hlext.
Qed. *)



(*

Definition num_internals (tg : TensorGraph) : nat :=
  length (filter (is_internal tg) tg.2).

Definition num_externals (tg : TensorGraph) : nat :=
  length (filter (not_internal tg) tg.2).

Lemma fold_num_internals' tm es es' :
  length (filter (is_internal (mk_tg tm es')) es) =
  num_internals (mk_tg tm es).
Proof. reflexivity. Qed.

Definition abs_length_eq {A} : relation (Idx * list A * list A) :=
  fun '(f, low, up) '(f', low', up') =>
  f = f' /\ length low = length low' /\ length up = length up'.

Lemma mk_node_perm_eq_lengths (tm : TensorMap R A) es es' k :
  es ≡ₚ es' ->
  length (mk_node (mk_tg tm es) k).1.2 =
  length (mk_node (mk_tg tm es') k).1.2 /\
  length (mk_node (mk_tg tm es) k).2 =
  length (mk_node (mk_tg tm es') k).2.
Proof.
  intros Hes.
  cbn.
  change (is_internal (mk_tg tm es')) with (is_internal (mk_tg tm es)).
  change (not_internal (mk_tg tm es')) with (not_internal (mk_tg tm es)).
  rewrite 4 length_app.
  split; f_equal; rewrite 2 length_fmap;
      (rewrite <- (length_fmap snd);
      (change (λ e : Ty * (Ty * Ty), e.2.2 = k) with
        ((λ e : Ty * Ty, e.2 = k) ∘ @snd Ty _) ||
        change (λ e : Ty * (Ty * Ty), e.2.1 = k) with
        ((λ e : Ty * Ty, e.1 = k) ∘ @snd Ty _));
      etransitivity; [symmetry; apply (f_equal length);
        refine (list_filter_fmap snd _)|];
      rewrite fmap_imap; unfold compose at 1; cbn -[compose];
      rewrite imap_to_fmap, list_fmap_id;

      (* rewrite imap_snds by (now rewrite length_fmap, length_seq); *)
      rewrite <- (length_fmap (@snd _ (_*_)));
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)];
      rewrite fmap_imap; unfold compose at 1; cbn -[compose];
      rewrite imap_to_fmap, list_fmap_id);
    rewrite <- Hes;
    reflexivity.
Qed.

*)




(*
Lemma mk_node_perm_eq (tm : TensorMap R A) es es' fint fext k :
  posperm (lengthP (filter (is_internal (mk_tg tm es)) es)) fint ->
  ppermute fint (filter (is_internal (mk_tg tm es)) es) =
  filter (is_internal (mk_tg tm es')) es' ->

  posperm (lengthP (filter (not_internal (mk_tg tm es')) es')) fext ->
  ppermute fext (filter (not_internal (mk_tg tm es)) es) =
  filter (not_internal (mk_tg tm es')) es' ->
  abs_perm
    ((mk_node (mk_tg tm es) k))
    (relabel_abs (var_map fint fext Datatypes.id) (mk_node (mk_tg tm es') k)).
Proof.
  intros Hfint Hfint_pperm Hfext Hfext_pperm.
  cbn.
  split; [reflexivity|].
  rewrite 2 fmap_app.
  split; f_equiv.
  - apply posperm_imap_eq' in Hfint as Hfint'.
    unfold EdgeSet in *.
    setoid_rewrite Hfint'.
    rewrite ppermute_permutation. 2:{
      rewrite lengthN_correct_rev, length_zip, length_fmap,
        length_seq, length_ppermute, Nat.min_id, <- lengthN_correct_rev.
      now apply posperm_inv_posperm.
    }
    setoid_rewrite <- Hfint_pperm.
    rewrite posperm_imap_eq by easy.
    symmetry.
    rewrite ppermute_permutation. 2:{
      now rewrite lengthN_correct_rev, length_zip, length_fmap,
        length_seq, Nat.min_id, <- lengthN_correct_rev.
    }
    rewrite zip_with_ppermute_r by now
      rewrite ?lengthN_correct_rev, length_fmap, length_seq,
        <- ?lengthN_correct_rev.


    apply eq_reflexivity.


    apply list_eq_Forall2.
    rewrite 2 Forall2_fmap_l, Forall2_fmap_r.
    apply Forall2







    symmetry.
    rewrite lengthN_correct_rev, length_fmap, length_seq, <- lengthN_correct_rev.
    symmetry.

    apply (list_eq_same_length _ _ _ eq_refl). 1:{
      rewrite !length_fmap.
      rewrite <- (length_fmap snd).
      change (@filter (Ty * (Ty * Ty)) ?B ?H _) with
        (@filter (Ty * (Ty * Ty)) B H ((λ e, e.2 = k) ∘ snd)).
      etransitivity; [symmetry; apply (f_equal length);
        refine (list_filter_fmap snd _)|].
      rewrite snd_zip by now rewrite length_fmap, length_seq.
      rewrite <- (length_fmap (@snd _ (_*_))).
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)].
      rewrite <- ppermute_fmap.
      rewrite snd_zip by now rewrite length_ppermute, length_fmap, length_seq.
      now rewrite ppermute_permutation by easy.
    }

    intros i x y Hi.
    rewrite ! list_lookup_fmap.


    rewrite <- list_fmap_compose.
    unfold compose; cbn.
    evar (n : nat);
    replace (length _) with n. 2:{

      rewrite length_fmap.
      rewrite <- (length_fmap snd).
      change (@filter (Ty * (Ty * Ty)) ?B ?H _) with
        (@filter (Ty * (Ty * Ty)) B H ((λ e, e.2 = k) ∘ snd)).
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)].
      rewrite snd_zip by now rewrite length_fmap, length_seq, length_ppermute.
      rewrite ppermute_permutation by easy.
      unfold n; reflexivity.
    }
    subst n.
    intros i x y Hi.
    rewrite 2 list_lookup_fmap.

    list_lookup filter

  intros Hes.
  cbn.
  rewrite !length_app, !length_fmap.
  split; f_equal.

  erewrite <- (length_fmap snd).
  epose proof (fun l => list_filter_fmap snd (P:= λ e, e.2 = k)
    l) as Hrw.
  etransitivity; [apply (f_equal length); symmetry; apply Hrw|].

  rewrite <- Hrw.

  1, 3: rewrite <- Hes at 2.
  cbv delta [mk_node] beta.
*)

Add Parametric Morphism : in_arity with signature
  (≡ₚ) ==> eq ==> eq as in_arity_mor.
Proof.
  intros es es' Hes k.
  unfold in_arity.
  now rewrite Hes.
Qed.

Add Parametric Morphism : out_arity with signature
  (≡ₚ) ==> eq ==> eq as out_arity_mor.
Proof.
  intros es es' Hes k.
  unfold out_arity.
  now rewrite Hes.
Qed.


Lemma graph_mabs_perm_eq (tm : gmap nat T) es es' :
  es ≡ₚ es' ->
  graph_mabs (mk_tg tm es) = graph_mabs (mk_tg tm es').
Proof.
  intros Hes.
  unfold graph_mabs.
  cbn [TensorGraph2pair fst snd edges nodes].
  erewrite map_imap_ext. 2:{
    intros k.
    specialize (in_arity_mor _ _ Hes k k eq_refl) as Hiar.
    rewrite Hiar.
    specialize (out_arity_mor _ _ Hes k k eq_refl) as Hoar.
    rewrite Hoar.
    reflexivity.
  }
  reflexivity.
Qed.



(*
Definition type {A} (a : A) : Type := A.
Definition domtype {A B} (f : A -> B) : Type := A.
Definition codomtype {A B} (f : A -> B) : Type := B.
#[global] Arguments type /.
#[global] Arguments domtype /.
#[global] Arguments codomtype /.

Ltac2 empty_flags () : Std.red_flags := {
  Std.rStrength := Std.Norm;
  Std.rBeta := Init.false;
  Std.rMatch := Init.false;
  Std.rFix := Init.false;
  Std.rCofix := Init.false;
  Std.rZeta := Init.false;
  Std.rDelta := Init.false;
  Std.rConst := [];
}.

Import Ltac2.Notations.

Notation "'right_uncompose' fg g" :=
  ((* let fpat :=  *)
    ltac2:(
      let fg := Constr.pretype fg in
      let g := Constr.pretype g in  (* TODO: Improve with expected type from fg *)
      let tf := match! Constr.type fg with
        | ?a -> _ => a
        end in
      let res := Constr.in_context ident:(x) tf (fun () =>
        let fg' := Std.eval_hnf fg in
        let fgx := Std.eval_cbv {(empty_flags()) with Std.rBeta := Init.true}
            '($fg' &x) in
        let pat := Std.eval_pattern [('($g &x), Std.AllOccurrences)] fgx in
        match! pat with
        | ?f _ => exact $f
        end) in
      match Constr.Unsafe.kind res with
      | Constr.Unsafe.Lambda _ body =>
        ltac1:(r |- let r' := eval cbn in r in exact r') (Ltac1.of_constr body)
      | _ => Control.throw (Init.Tactic_failure Init.None)
      end
        )) (at level 10, fg at level 0, g at level 0).
*)
(* Goal True.
Check (right_uncompose (λ (x : nat * (nat * nat)), x.2.2) (@snd nat (nat * nat))). *)

(* Lemma graph_semantics_abstracts_is_Some (tm : gmap nat T) es mi mo k
  (mr': Vlist graph_V (replicate (num_internals (mk_tg tm es)) 0))
  (Hmr': WF_Vlist graph_V mr') :
  k ∈ dom tm ->
  is_Some
  (join_list
     (get_var graph_V ∅ (graph_ml mi mo) (reverse mr') <$>
      ((mk_internal_var <$>
        filter (λ e : Ty * (Ty * Ty), e.2.2 = k)
          (imap pair
             (filter (is_internal (mk_tg tm es)) es))) ++
       (mk_external_var false <$>
        filter (λ e : Ty * (Ty * Ty), e.2.2 = k)
          (imap pair
             (filter (not_internal (mk_tg tm es)) es)))) ++
      (mk_internal_var <$>
       filter (λ e : Ty * (Ty * Ty), e.2.1 = k)
         (imap pair (filter (is_internal (mk_tg tm es)) es))) ++
      (mk_external_var true <$>
       filter (λ e : Ty * (Ty * Ty), e.2.1 = k)
         (imap pair
            (filter (not_internal (mk_tg tm es)) es))))
   ≫= λ args : list (Vval graph_V),
        graph_mabs (mk_tg tm es) !! Pos.of_succ_nat k
        ≫= λ fval : Vfunc graph_V,
             Vapplys graph_V fval args) <->
  ((forall i, i ∈ (filter (λ e, e.2 = k /\ ~ is_key (mk_tg tm es) e.1) es).*1 ->
    (i:>nat) ∈ dom mi) /\
  (forall o, o ∈ (filter (λ e, e.1 = k /\ ~ is_key (mk_tg tm es) e.2) es).*2 ->
    (o:>nat) ∈ dom mo)) /\ True.
Proof.
  intros Hkdom.
  unfold graph_mabs.
  rewrite lookup_kmap by apply _.
  rewrite map_lookup_imap.
  apply elem_of_dom in Hkdom as [fk Hfk].
  cbn [fst mk_tg].
  rewrite Hfk.
  cbn [mbind option_bind].
  rewrite bind_is_Some.
  rewrite join_list_is_Some.
  apply and_iff_from_l.
  - rewrite not_elem_of_list_fmap.
    rewrite <- Forall_forall.
    rewrite Permutation_swap_app_app.
    rewrite <- fmap_app.
    change (mk_external_var false) with
      (loc ∘ (λ e : Ty * (Ty * Ty), bcons false (Pos.of_succ_nat e.2.1))).
    change (mk_external_var true) with
      (loc ∘ (λ e : Ty * (Ty * Ty), bcons true (Pos.of_succ_nat e.2.2))).
    rewrite 2 list_fmap_compose, <- fmap_app.
    rewrite Forall_app.
    rewrite and_is_True_l. 2:{
      rewrite Forall_fmap, Forall_forall.
      intros x.
      rewrite elem_of_app, 2 elem_of_list_filter.
      rewrite <- and_or_distr_r.
      intros [Hxk (i & e & -> & Hlook)%elem_of_lookup_imap].
      cbn.
      apply not_eq_None_Some.
      apply lookup_lt_is_Some.
      rewrite length_reverse.
      apply Forall2_length in Hmr' as Hlen.
      unfold Vval.
      rewrite <- Hlen, length_replicate.
      unfold num_internals.
      apply lookup_lt_Some in Hlook.
      cbn; lia.
    }
    rewrite Forall_fmap.
    rewrite Forall_app, 2 Forall_fmap.
    unfold compose; cbn.
    unfold graph_ml.
    setoid_rewrite lookup_fmap.
    setoid_rewrite lookup_gmaps_to_Pmap.
    setoid_rewrite pos_to_nat_pred_of_nat.
    f_equiv.
    + change (Forall _ ?l) with
        (Forall (((λ x : Ty,
        @mk_Vval graph_V 0 <$> mi !! x ≠ None)∘ fst) ∘ snd) l) at 1.
      rewrite <- Forall_fmap.
      change (filter (H:=?H) _ ?l) with
        (filter (H:=H) ((λ e, e.2 = k) ∘ snd) l) at 1.
      remember (filter _ _).*2 as l eqn:Hl.
      pose proof (eq_trans Hl (eq_sym (list_filter_fmap snd _))) as Hl'.
      clear Hl.
      subst l.
      rewrite fmap_imap.
      unfold compose at 2.
      cbn.
      rewrite imap_to_fmap, list_fmap_id.
      rewrite <- Forall_fmap.
      rewrite <- Forall_forall.
      setoid_rewrite list_filter_filter.
      erewrite list_filter_iff; [apply Forall_iff|].
      * intros x.
        now rewrite not_eq_None_Some, fmap_is_Some, elem_of_dom.
      * intros (i, j).
        cbn.
        unfold not_internal, is_internal.
        cbn.
        apply and_iff_from_l; [easy|].
        intros -> _.
        enough (is_key (mk_tg tm es) k) by tauto.
        apply elem_of_dom.
        refine (elem_of_dom_2 _ _ _ Hfk).
    + change (Forall _ ?l) with
        (Forall (((λ x : Ty,
        @mk_Vval graph_V 0 <$> mo !! x ≠ None) ∘ snd) ∘ snd) l) at 1.
      rewrite <- Forall_fmap.
      change (filter (H:=?H) _ ?l) with
        (filter (H:=H) ((λ e, e.1 = k) ∘ snd) l) at 1.
      remember (filter _ _).*2 as l eqn:Hl.
      pose proof (eq_trans Hl (eq_sym (list_filter_fmap snd _))) as Hl'.
      clear Hl.
      subst l.
      rewrite fmap_imap.
      unfold compose at 2.
      cbn.
      rewrite imap_to_fmap, list_fmap_id.
      rewrite <- Forall_fmap.
      rewrite <- Forall_forall.
      setoid_rewrite list_filter_filter.
      erewrite list_filter_iff; [apply Forall_iff|].
      * intros x.
        now rewrite not_eq_None_Some, fmap_is_Some, elem_of_dom.
      * intros (i, j).
        cbn.
        unfold not_internal, is_internal.
        cbn.
        apply and_iff_from_l; [easy|].
        intros -> _.
        enough (is_key (mk_tg tm es) k) by tauto.
        apply elem_of_dom.
        refine (elem_of_dom_2 _ _ _ Hfk).
  - intros Hnone_nin [Hmi Hmo].
    apply iff_True_1.
    intros vs Hvs%join_list_Some.
    apply Vapplys_is_Some.
    cbn -[mk_node].
    apply (list_eq_same_length _ _ _ eq_refl).
    1: {
      apply (f_equal length) in Hvs.
      rewrite 2 length_fmap in Hvs.
      rewrite length_fmap, length_replicate.
      unfold Vval in *.
      rewrite <- Hvs.
      cbn.
      rewrite <- length_app.
      reflexivity.
    }
    intros i x y Hi.
    rewrite length_fmap in Hi.
    rewrite lookup_replicate.
    rewrite list_lookup_fmap.
    intros [-> Hi'].
    apply (f_equal (.!! i)) in Hvs.
    rewrite ! list_lookup_fmap in Hvs.
    unfold Vval in *.
    destruct (vs !! i) as [vi|] eqn:Hvi in *; [|easy].
    cbn.
    intros [= <-].
    symmetry.
    cbn in Hvs.
    rewrite fmap_Some in Hvs.
    destruct Hvs as (v & Hv & HSvi).
    change (projT1 vi) with (from_option projT1 0 (Some vi)).
    rewrite HSvi.
    apply elem_of_list_lookup_2 in Hv as Hin.
    rewrite Permutation_swap_app_app, <- fmap_app in Hin.
    rewrite 2 elem_of_app, 3 elem_of_list_fmap in Hin.
    destruct Hin as [((n&?&?) & -> & Hin) |[((?&?&?) & -> & Hin) | ((?&?&?) & -> & Hin)]].
    + cbn.
      rewrite pos_to_nat_pred_of_nat.
      destruct (reverse _ !! _) as [mr'i|] eqn:Hmr'i; [|easy].
      apply elem_of_list_lookup_2 in Hmr'i as Hn.
      pose proof Hmr' as HWF.
      unfold WF_Vlist in HWF.
      rewrite Forall2_lookup in HWF.
      specialize (HWF (length mr' - S n)).
      pose proof Hmr'i as Hmri.
      rewrite reverse_lookup in Hmri by
        now apply lookup_lt_Some in Hmr'i; rewrite length_reverse in Hmr'i.
      setoid_rewrite Hmri in HWF.
      destruct (replicate _ _ !! _) as [ri|] eqn:Hrep in HWF; [|easy].
      apply lookup_replicate in Hrep as [-> ?].
      inversion HWF; subst.
      cbn.
      easy.
    + cbn.
      unfold graph_ml.
      rewrite lookup_fmap.
      destruct (_ !! _) in |- *; reflexivity.
    + cbn.
      unfold graph_ml.
      rewrite lookup_fmap.
      destruct (_ !! _) in |- *; reflexivity.
Qed. *)

Lemma num_internals_perm_eq tm es es' : es ≡ₚ es' ->
  @num_internals T (mk_tg tm es) = num_internals (mk_tg tm es').
Proof.
  intros Hes.
  unfold num_internals.
  cbn.
  rewrite <- Hes.
  reflexivity.
Qed.

Lemma graph_tensorlist_semantics_to_named
  (tg : TensorGraph) mi mo (K : R) :
  graph_map_semantics tg mi mo ==
  ntl_total_semantics graph_V (graph_mabs tg) ∅ (graph_ml mi mo)
  (graph_namedtensorlist_semantics tg (seq 0 (num_internals tg))
     (seq 0 (num_externals tg))).
Proof.
  pose proof (graph_namedtensorlist_semantics_seq_correct tg)
    as Hcorr.
  unfold graph_map_semantics.
  rewrite <- tl2ntl_correct
    by apply graph_tensorlist_semantics_WF.
  now rewrite <- Hcorr.
Qed.

(* FIXME: Move *)
Definition graph_mabst (tg : TensorGraph) :
  Pmap {knm & Tensor (R:=R) knm.2.1 knm.2.2 (graph_V knm.1)} :=
  kmap Pos.of_succ_nat $ map_imap (λ k (dt : T),
    Some (existT (0, (in_arity tg.(edges) k, out_arity tg.(edges) k))
          (interpretTensor dt _ _))) tg.(nodes).

Lemma graph_mabs_to_mabst (tg : TensorGraph) :
  graph_mabs tg =
  mabs_of_tensor_map graph_V (graph_mabst tg).
Proof.
  unfold graph_mabs, mabs_of_tensor_map, graph_mabst.
  rewrite <- (kmap_fmap _).
  f_equal.
  rewrite map_fmap_imap.
  reflexivity.
Qed.

Lemma graph_tabst_to_mabst (tg : TensorGraph) :
  graph_tabst tg = snd ∘ projT1 <$> graph_mabst tg.
Proof.
  unfold graph_tabst, graph_mabst.
  rewrite <- (kmap_fmap _).
  rewrite map_fmap_imap.
  reflexivity.
Qed.

Lemma graph_semantics_perm_eq_aux (tm : gmap nat T) es es' :
  (forall k t, tm !! k = Some t ->
    permutative_tensor (R:=R) (req:=req) (interpretTensor t
      (in_arity es k) (out_arity es k))) ->
  es ≡ₚ es' ->
  forall mi mo,
  graph_map_semantics (mk_tg tm es) mi mo ==
  graph_map_semantics (mk_tg tm es') mi mo.
Proof.
  intros Hperm Hes mi mo.
  (* rewrite graph_tensorlist_semantics_to_named *)
  unfold graph_map_semantics.
  rewrite <- 2 tl2ntl_correct by apply graph_tensorlist_semantics_WF.
  apply (graph_tensorlist_semantics_perm_eq_pairs_elab tm) in Hes as Hex.
  destruct Hex as (idxs & idxs' & Hidxs & Hidxs' & Heqmid & Hmideq).
  etransitivity.
  - rewrite graph_mabs_to_mabst.
    eapply ntl_perm_eq'_correct_permutative;
    [| | apply Heqmid|..].
    + apply tl2ntl_WF, graph_tensorlist_semantics_WF.
    + rewrite <- graph_namedtensorlist_semantics_to_aux.
      apply graph_namedtensorlist_semantics_WF.
      * rewrite Hidxs; apply NoDup_seq.
      * rewrite Hidxs, length_seq.
        now apply num_internals_perm_eq.
    + cbn.
      rewrite Forall_fmap, Forall_forall.
      intros k Hk%(elem_of_list_to_set (C:=gset nat))%dom_alt.
      cbn.
      rewrite <- graph_tabst_to_mabst.
      now apply mk_node_abst_WT'_imap_pair.
    + cbn.
      intros f.
      rewrite <- list_fmap_compose.
      unfold compose; cbn.
      rewrite <- (set_map_list_to_set_L (SA:=gset nat)).
      rewrite <- dom_alt.
      intros (k & -> & Hk)%elem_of_map.
      apply elem_of_dom in Hk as [t Ht].
      intros t'.
      unfold graph_mabst.
      rewrite (lookup_kmap _), map_lookup_imap.
      cbn.
      rewrite Ht.
      cbn.
      intros [= <-].
      now apply Hperm.
  - rewrite <- (graph_mabs_perm_eq tm _ _ Hes), <- graph_mabs_to_mabst.
    eapply ntl_aeq_correct.
    + rewrite <- graph_namedtensorlist_semantics_to_aux.
      apply graph_namedtensorlist_semantics_WF.
      * rewrite Hidxs; apply NoDup_seq.
      * rewrite Hidxs, length_seq.
        now apply num_internals_perm_eq.
    + apply tl2ntl_WF.
      apply graph_tensorlist_semantics_WF.
    + easy.
Qed.

(*
Lemma graph_semantics_perm_eq_aux (tm : TensorMap R A) es es' :
  es ≡ₚ es' ->
  forall mi mo,
  graph_tensorlist_semantics (mk_tg tm es) =tl=
  graph_tensorlist_semantics (mk_tg tm es').
Proof.
  intros Hes.
  eexists; cbn -[reverse].
  rewrite !fmap_const.
  remember (num_internals (mk_tg tm es)) as x eqn:Hx.
  pose proof Hx as Hx'.
  cbn in Hx'.
  rewrite <- Hx', Hx.
  unfold is_internal, is_key in Hx' |- *.
  cbn -[reverse num_internals] in Hx' |- *.
  rewrite <- Hes at 1.
  rewrite <- Hx', Hx.
  clear x Hx Hx'.
  rewrite reverse_replicate, lengthN_correct_rev, length_replicate.
  replace (N.succ_pos _) with (Pos.of_succ_nat (num_internals (mk_tg tm es)))
    by lia.
  apply (filter_Permutation (is_internal (mk_tg tm es))) in Hes as Hesint.




*)

End TensorGraphFacts.