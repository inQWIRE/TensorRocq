Require Import Aux_pos.
Require Import Tensor.
From stdpp Require Import list fin_maps.
From stdpp Require Import pmap gmap.
Require Import ZXCore.
Require ZifyBool.
Require Import TensorGraphExpr TensorGraphSemantics.

#[local] Coercion pos_to_nat_pred : positive >-> nat.

Open Scope nat_scope.

(* FIXME: Move *)
Lemma forall_var (P : var -> Prop) :
  (forall v, P v) <-> (forall r, P (bound r)) /\ (forall l, P (free l)).
Proof.
  split; [auto|].
  now intros (?&?) [].
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







Let TensorGraph := @CospanHyperGraph T.
(*
Definition graph_tabs (tg : TensorGraph n m) : abstypecontext :=
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
Qed. *)

Context `{Summable A, EqDecision A}.


#[global] Hint Mode TensorLike - - + : typeclass_instances.


Lemma ntl_relabel_absidx_WF
  (f : Idx -> Idx) (ntl : namedtensorlist) :
  WF_ntl ntl -> WF_ntl (ntl_relabel_absidx f ntl).
Proof.
  unfold WF_ntl.
  rewrite abstracts_bound_vars_ntl_relabel_absidx,
    deltas_bound_vars_ntl_relabel_absidx.
  easy.
Qed.

Lemma graph_semantics_isomorphic {n m} (tg tg' : TensorGraph n m) :
  isomorphic tg tg' ->
  graph_semantics tg ≡@{@Tensor R n m A} graph_semantics tg'.
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%isomorphic_exists.
  intros v w Hv Hw.
  (* rewrite <- reindex_relabel_graph. *)
  unfold graph_semantics, namedtensorlist_to_tensor.
  cbn -[ntl_total_semantics make_ml graph_mabs].
  symmetry.
  erewrite ntl_aeq_correct;
  [|apply graph_namedtensorlist_semantics_WF|].
  2: apply (graph_namedtensorlist_semantics_relabel_graph _).
  unfold graph_mabs.
  (* rewrite <- 2 (kmap_fmap _).
  rewrite (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ _).
  fold (graph_mabs (relabel_abs fe <$> tg.(hedges)))
    (graph_mabs tg.(hedges)). *)
  erewrite ntl_aeq_correct;
  [|apply graph_namedtensorlist_semantics_WF|].
  2: apply (graph_namedtensorlist_semantics_reindex_graph _).
  unfold graph_mabs.
  rewrite <- 2 kmap_fmap'.
  rewrite (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ _).
  rewrite 2 ntl_total_semantics_alt by apply graph_namedtensorlist_semantics_WF.
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  f_equiv.
  apply Rlist_prod_ext.
  apply Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros [[f' low'] up'] Hflu.
  unfold abstract_semantics_alt.
  rewrite 3 lookup_fmap.
  cbn in Hflu.
  unfold tg_abstracts in Hflu.
  rewrite elem_of_list_fmap in Hflu.
  destruct Hflu as ([f [[t low] up]] & [= -> -> ->] & Hflu).
  rewrite <- 2 list_fmap_compose.
  unfold compose; cbn.
  destruct (hedges tg !! f) as [[[]]|]; [|done].
  done.
Qed.

Lemma graph_semantics_WT {n m} (tg : TensorGraph n m) :
  WT_ntl (list_to_set (bcons false <$> pseq 1 (N.of_nat n)) ∪
    list_to_set (bcons true <$> pseq 1 (N.of_nat m))) (graph_namedtensorlist_semantics tg).
Proof.
  split; [|split; [|apply graph_namedtensorlist_semantics_WF]].
  - rewrite abstracts_free_vars_graph; done.
  - rewrite deltas_free_vars_graph.
    now rewrite list_to_set_app.
Qed.

Lemma tg_list_to_deltas_fmap b f ioputs :
  tg_list_to_deltas b (f <$> ioputs) =
  relabel_delt (relabel_bounds f) <$> tg_list_to_deltas b ioputs.
Proof.
  unfold tg_list_to_deltas.
  rewrite fmap_imap, imap_fmap.
  reflexivity.
Qed.


End TensorGraphFacts.