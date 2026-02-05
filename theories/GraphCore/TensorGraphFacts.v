Require Import Aux_pos.
Require Import Tensor.
From stdpp Require Import list fin_maps.
From stdpp Require Import pmap gmap.
Require Import ZXCore.
Require ZifyBool.
Require Import TensorGraphExpr TensorGraphSemantics.
Require TECospan.

#[local] Coercion pos_to_nat_pred : positive >-> nat.

Open Scope nat_scope.

(* FIXME: Move *)
Lemma forall_var (P : var -> Prop) :
  (forall v, P v) <-> (forall r, P (bound r)) /\ (forall l, P (free l)).
Proof.
  split; [auto|].
  now intros (?&?) [].
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
  destruct ((hedges tg).(hyperedges) !! f) as [[[]]|]; [|done].
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

Lemma vertices_cons_inputs {n m} i (ins : vec _ n) (outs : vec _ m)
  hedges :
  vertices ((i ::: ins -> hedges <- outs) :> TensorGraph (S n) m) =
  {[i]} ∪ vertices (ins -> hedges <- outs).
Proof.
  unfold vertices; cbn -[list_to_set union].
  symmetry.
  rewrite (union_comm_L _), <- (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.


Lemma vertices_cons_outputs {n m} o (ins : vec _ n) (outs : vec _ m)
  hedges :
  vertices ((ins -> hedges <- o ::: outs) :> TensorGraph n (S m)) =
  {[o]} ∪ vertices (ins -> hedges <- outs).
Proof.
  unfold vertices; cbn -[list_to_set union].
  symmetry.
  rewrite (union_comm_L _), <- (union_assoc_L _).
  f_equal.
  set_solver.
Qed.


Lemma vertices_cons {n m} i o (ins : vec _ n) (outs : vec _ m)
  hedges :
  vertices ((i ::: ins -> hedges <- o ::: outs) :> TensorGraph (S n) (S m)) =
  {[i; o]} ∪ vertices (ins -> hedges <- outs).
Proof.
  unfold vertices; cbn -[list_to_set union].
  symmetry.
  rewrite (union_comm_L _), <- (union_assoc_L _).
  f_equal.
  set_solver.
Qed.

(* Lemma elements_vertices_union2 i o (ins : vec _ n) (outs : vec _ m) hedges :
  {[i; o]} ∪ vertices ((ins -> hedges <- outs) :> TensorGraph n (S m)) =
   *)



Lemma vertices_add_top_loop_cup {n m} (tg : TensorGraph (S n) (S m)) :
  vertices (add_top_loop tg) =
  vertices tg ∖ {[Vector.hd tg.(outputs)]} ∪ {[Vector.hd tg.(inputs)]}.
Proof.
  destruct tg as [hes ins outs].
  induction ins as [i ins] using vec_S_inv.
  induction outs as [o outs] using vec_S_inv.
  unfold add_top_loop.
  rewrite vertices_relabel_graph; cbn -[union].
  unfold vertices.
  cbn -[union].
  rewrite vertices_hg_add_vertices.
  rewrite 2 list_to_set_app_L;
  cbn -[union].
  rewrite set_map_fn_singleton_L.
  generalize (vertices_hg hes) as vs; intros vs.
  case_decide as Hdec; [set_solver+|set_solver +Hdec].
Qed.

Import TECospan.

Definition graph_contl_semantics {n m} (tg : TensorGraph n m) :
  CospanNamedTensorList n m :=
  mk_contl (graph_namedtensorlist_semantics tg)
    (vmap (bcons false ∘ Pos.of_succ_nat) $ vseq 0 n)
    (vmap (bcons true ∘ Pos.of_succ_nat) $ vseq 0 m).



#[export] Instance ntl_eq_of_ntl_aeq tl : subrelation ntl_aeq (ntl_eq tl).
Proof.
  intros ntl ntl' Hntl.
  hnf.
  apply rtc_once.
  now left.
Qed.

#[export] Instance ntl_eq_of_ntl_delta_eq tl :
  subrelation (ntl_delta_eq tl) (ntl_eq tl).
Proof.
  intros ntl ntl' Hntl.
  hnf.
  apply rtc_once.
  now right.
Qed.

Add Parametric Morphism : mk_ntl with signature
  Permutation ==> Permutation ==> Permutation ==> ntl_aeq as mk_ntl_perm_eq.
Proof.
  intros; now apply ntl_aeq_of_perm.
Qed.

Lemma ntl_delta_eq_subst' tl lb r sums abs delt :
  lb ∉ sums -> r ∈ psets_to_varset (list_to_set sums) tl ->
  r <> bound lb ->
  ntl_delta_eq tl (mk_ntl (lb :: sums) abs ((bound lb, r) :: delt))
    (mk_ntl sums (relabel_abs {[bound lb := r]} <$> abs)
      (relabel_delt {[bound lb := r]} <$> delt)).
Proof.
  intros Hlb Hr Hrlb.
  eapply ntl_delta_eq_subst; try eassumption.
  easy.
Qed.



Lemma ntl_delta_eq_subst_NoDup tl lb r sums abs delt :
  NoDup sums -> r ∈ psets_to_varset (list_to_set sums) tl ->
  r <> bound lb -> lb ∈ sums ->
  ntl_delta_eq tl (mk_ntl sums abs ((bound lb, r) :: delt))
    (mk_ntl (filter (.≠ lb) sums) (relabel_abs {[bound lb := r]} <$> abs)
      (relabel_delt {[bound lb := r]} <$> delt)).
Proof.
  intros Hsums Hr Hrlb Hlb.
  eapply (ntl_delta_eq_subst _ lb r).
  - cbn.
    now rewrite elem_of_list_filter.
  - rewrite elem_of_psets_to_varset in Hr |- *;
    destruct r as [r|r]; [|done].
    cbn.
    rewrite elem_of_list_to_set in Hr |- *.
    rewrite elem_of_list_filter.
    split; [congruence|easy].
  - split; [easy|split; [|easy]]; cbn.
    now apply NoDup_perm_filter_out.
Qed.

Lemma ntl_delta_eq_idemp' tl v sums abs delt :
  v ∈ psets_to_varset (list_to_set sums) tl ->
  ntl_delta_eq tl (mk_ntl sums abs ((v, v) :: delt))
    (mk_ntl sums abs delt).
Proof.
  intros Hv.
  symmetry.
  apply ntl_delta_eq_idemp with v; easy.
Qed.

Lemma tg_abstracts_relabel_abs (f : positive -> positive) (hg : HyperGraph T) :
  tg_abstracts (relabel_abs f <$> hg.(hyperedges)) =
  relabel_abs (relabel_bounds f) <$> tg_abstracts hg.
Proof.
  unfold tg_abstracts.
  rewrite map_to_list_fmap.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; intros _ [k [[? l] u]] _.
  cbn.
  f_equal; [f_equal|];
  rewrite <- 2 list_fmap_compose; done.
Qed.


Lemma graph_namedtensorlist_semantics_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  (* vhd tg.(inputs) <> vhd tg.(outputs) -> *)
  ntl_eq (list_to_set (((bcons false ∘ Pos.of_succ_nat) <$> seq 0 n)
     ++ ((bcons true ∘ Pos.of_succ_nat) <$> seq 0 m)))
     (graph_namedtensorlist_semantics (add_top_loop tg))
  (relabel_ntl_free (with_bcons Pos.pred)
    (add_loop_ntl_alt 2 3 (graph_namedtensorlist_semantics tg))).
Proof.
  (* intros Hio. *)

  unfold add_loop_ntl_alt.
  remember (fresh _) as x eqn:Hxeq.
  assert (Hx : x ∉ ntl_sums (graph_namedtensorlist_semantics tg)) by
    now rewrite Hxeq; apply infinite_is_fresh.
  clear Hxeq.

  destruct tg as [hes ins outs].
  destruct ins as [i ins] using vec_S_inv.
  destruct outs as [o outs] using vec_S_inv.
  (* cbn in Hio. *)
  unfold graph_namedtensorlist_semantics; cbn.
  rewrite vertices_add_top_loop_cup.

  unfold add_top_loop, relabel_graph, graph_namedtensorlist_semantics,
    add_loop_ntl_alt, relabel_ntl_free; cbn.
  rewrite fmap_app.
  cbn.
  rewrite decide_True by now left.
  rewrite decide_True by now right.
  cbn.
  rewrite vertices_cons.
  rewrite fmap_app.
  replace (_ <$> (_ <$> imap _ _)) with
    (imap ((λ idx input, (free (Pos.of_succ_nat idx)~0, bound input))) ins). 2:{
    rewrite <- list_fmap_compose.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap, 2 length_imap|].
    rewrite length_fmap.
    intros k v v' Hk.
    rewrite list_lookup_fmap, 2 list_lookup_imap, 2 fmap_Some.
    cbn.
    intros (ik & Hik & ->).
    intros (? & (ik' & Hik' & ->)%fmap_Some & ->).
    cbn.
    rewrite decide_False by lia.
    cbn.
    f_equal; [f_equal; lia|congruence].
  }
  cbn -[union].
  replace (_ <$> (_ <$> imap _ _)) with
    (imap ((λ idx input, (free (Pos.of_succ_nat idx)~1, bound input))) outs). 2:{
    rewrite <- list_fmap_compose.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap, 2 length_imap|].
    rewrite length_fmap.
    intros k v v' Hk.
    rewrite list_lookup_fmap, 2 list_lookup_imap, 2 fmap_Some.
    cbn.
    intros (ik & Hik & ->).
    intros (? & (ik' & Hik' & ->)%fmap_Some & ->).
    cbn.
    rewrite decide_False by lia.
    cbn.
    f_equal; [f_equal; lia|congruence].
  }
  rewrite <- Permutation_middle, Permutation_swap.
  assert (Hxo : x <> o) by now intros ->; revert Hx;
    cbn; rewrite vertices_cons; set_solver +.
  assert (Hxi : x <> i) by now intros ->; revert Hx;
    cbn; rewrite vertices_cons; set_solver +.
  rewrite ntl_delta_eq_subst' by first
    [now intros [= ->]|
    apply elem_of_psets_to_varset; set_solver +|
    now rewrite <- vertices_cons; apply Hx].

  cbn -[union].
  rewrite fn_lookup_singleton.
  rewrite fn_lookup_singleton_ne by congruence.
  rewrite (list_fmap_id' (relabel_abs (var_elim _ _))). 2:{
    intros flu' (flu & -> & Hflu)%elem_of_list_fmap.
    cbn.
    rewrite <- 2 list_fmap_compose; unfold compose.
    cbn.
    reflexivity.
  }
  rewrite (list_fmap_id' (relabel_abs (relabel_frees _))). 2:{
    intros flu' (flu & -> & Hflu)%elem_of_list_fmap.
    cbn.
    rewrite <- 2 list_fmap_compose; unfold compose.
    cbn.
    reflexivity.
  }
  rewrite (list_fmap_id' (relabel_abs {[bound x := bound o]})). 2:{
    intros flu' (k_flu & -> & Hflu)%elem_of_list_fmap.
    apply relabel_abs_id_strong.
    cbn.
    rewrite <- fmap_app, <- Forall_forall, Forall_fmap, Forall_forall.
    intros x' Hx'.
    cbn.
    apply fn_lookup_singleton_ne.
    intros [= <-].
    apply Hx.
    destruct k_flu as [k flu].
    cbn.
    apply elem_of_elements.
    apply elem_of_vertices.
    left.
    cbn.
    rewrite elem_of_app in Hx'.
    cbn in Hx'.
    apply elem_of_map_to_list in Hflu.
    eauto.
  }
  rewrite (list_fmap_id' (relabel_delt {[bound x := bound o]})). 2:{
    intros [l u] [Hlu|Hlu]%elem_of_app;
    apply elem_of_lookup_imap in Hlu as (? & ? & [= -> ->] & Hx'%elem_of_list_lookup_2);
    cbn;
    f_equal;
    apply fn_lookup_singleton_ne;
    set_solver + Hx' Hx.
  }
  symmetry.
  rewrite (union_comm_L {[i]}), <- (union_assoc_L {[o]}).
  destruct_decide (decide (i = o)) as Hio.
  1:{
    subst.
    rewrite ntl_delta_eq_idemp' by now
      apply elem_of_psets_to_varset, elem_of_list_to_set, elem_of_elements,
       elem_of_union_l, elem_of_singleton_2.
    apply ntl_eq_of_ntl_aeq, ntl_aeq_of_perm; cbn -[union].
    - f_equiv.
      remember (vertices _) as vs eqn:Hvs.
      clear Hvs.
      rewrite difference_union.
      set_solver +.
    - f_equiv.
      symmetry.
      etransitivity; [|apply map_fmap_id].
      apply map_fmap_ext.
      intros _ flu _.
      apply relabel_abs_id'.
      intros v.
      rewrite fn_lookup_singleton_case; now case_decide.
    - do 2 f_equiv; symmetry;
      rewrite vec_to_list_map;
      apply list_fmap_id'; intros v _;
      rewrite fn_lookup_singleton_case; now case_decide.
  }
  rewrite elements_union, elements_singleton.
  cbn [app].

  rewrite ntl_delta_eq_subst' by first [
    now intros ?%(inj bound)|
    apply elem_of_psets_to_varset; set_solver +Hio|
    now intros [? ?%not_elem_of_singleton]%elem_of_elements%elem_of_difference
  ].

  apply ntl_eq_of_ntl_aeq, ntl_aeq_of_perm; cbn -[union].
  - f_equiv.
    remember (vertices _) as vs eqn:Hvs.
    set_solver + Hio.
  - rewrite tg_abstracts_relabel_abs.
    apply eq_reflexivity, list_fmap_ext.
    intros _ flu _.
    apply relabel_abs_ext; intros [v|]; [|done].
    cbn.
    rewrite 2 fn_lookup_singleton_case;
    do 2 case_decide; congruence.
  - rewrite fmap_app, 2 fmap_imap, 2 vec_to_list_map, 2 imap_fmap.
    unfold compose; cbn.
    apply eq_reflexivity; f_equal;
    apply imap_ext; intros ? ? _; cbn; f_equal;
    rewrite 2 fn_lookup_singleton_case; do 2 case_decide; congruence.
Qed.


Lemma ntl_free_varset_graph {n m} (tg : TensorGraph n m) :
  ntl_free_varset (graph_namedtensorlist_semantics tg)
  = list_to_set
    (vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n) ++
     vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m)).
Proof.
  unfold ntl_free_varset.
  rewrite abstracts_free_vars_graph, deltas_free_vars_graph.
  rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
  rewrite 2 pseq_to_seq, <- 2 list_fmap_compose.
  rewrite union_empty_l_L.
  now rewrite 2 Nat2N.id.
Qed.

Lemma graph_contl_semantics_WT {n m} (tg : TensorGraph n m) :
  WT_contl (graph_contl_semantics tg).
Proof.
  unfold WT_contl.
  cbn.
  rewrite WT_ntl_alt_varset.
  rewrite ntl_free_varset_graph.
  split; [done|].
  apply graph_namedtensorlist_semantics_WF.
Qed.

Lemma graph_contl_semantics_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  contl_eq (graph_contl_semantics (add_top_loop tg))
  (add_top_loop_contl (graph_contl_semantics tg)).
Proof.
  rewrite (contl_mk_surj (graph_contl_semantics (add_top_loop tg))).
  etransitivity.
  - apply contl_eq_of_ntl_eq.
    cbn.
    rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
    apply graph_namedtensorlist_semantics_add_top_loop.
  - cbn.
    rewrite (@contl_eq_relabel_free (with_bcons Pos.succ) ltac:(hnf; intros [] []; cbn; lia)).
    apply eq_reflexivity.
    apply contl_ext.
    + cbn.
      rewrite relabel_ntl_free_compose.
      etransitivity; [|apply relabel_ntl_free_id].
      apply relabel_ntl_free_ext_strong.
      assert (HWT : WT_contl (add_top_loop_contl (graph_contl_semantics tg))). 1:{
        apply WT_add_top_loop_contl, graph_contl_semantics_WT.
      }
      apply WT_ntl_free_varset_subseteq in HWT.
      intros i Hi%HWT.
      cbn in Hi.
      rewrite 2 vec_to_list_map, 2 vec_to_list_seq,
        elem_of_list_to_set, elem_of_app,
          2 elem_of_list_fmap in Hi.
      setoid_rewrite elem_of_seq in Hi.
      clear HWT.
      cbn.
      naive_solver subst; cbn; lia.
    + cbn.
      apply vec_to_list_inj2.
      rewrite Vector.map_map.
      rewrite 2 vec_to_list_map, 2 vec_to_list_seq,
        <- fmap_S_seq, <- list_fmap_compose.
      apply list_fmap_ext; intros _ ? _; cbn.
      lia.
    + cbn.
      apply vec_to_list_inj2.
      rewrite Vector.map_map.
      rewrite 2 vec_to_list_map, 2 vec_to_list_seq,
        <- fmap_S_seq, <- list_fmap_compose.
      apply list_fmap_ext; intros _ ? _; cbn.
      lia.
Qed.






Lemma graph_semantics_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  graph_semantics (add_top_loop tg) ≡
  join_stack_1_tl_tr (graph_semantics (SR:=SR) tg).
Proof.
  intros v w Hv Hw.
  cbn -[graph_semantics].
  unfold graph_semantics, namedtensorlist_to_tensor.
  rewrite ntl_total_semantics_alt by now apply graph_namedtensorlist_semantics_WF.
  setoid_rewrite ntl_total_semantics_alt; last
    now apply graph_namedtensorlist_semantics_WF.
  destruct tg as [hedges ins outs].
  induction ins as [i ins] using vec_S_inv.
  induction outs as [o outs] using vec_S_inv.


  cbn -[abstracts_semantics_alt deltas_semantics_alt list_to_map vmap vseq].
Admitted.

Lemma graph_semantics_add_top_loops {n m o} (tg : TensorGraph (n + m) (n + o)) :
  graph_semantics (add_top_loops tg) ≡
  join_stack_tl_tr (graph_semantics (SR:=SR) tg).
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  apply join_stack_tl_tr_mor.
  apply graph_semantics_add_top_loop.
Qed.

(* #[export] Instance CospanHyperGraph_disj {n m} : Disjoint (CospanHyperGraph T n m) :=
  fun cohg cohg' =>
  vertices cohg ## vertices cohg' /\
  cohg.(hedges) ##ₘ cohg'.(hedges). *)

(* Lemma graph_semantics_swapped_stack_graphs {n m n' m'}
  (cohg : TensorGraph n m) (cohg' : TensorGraph n' m') :
  cohg ## cohg ->
  graph_semantics (SR:=SR) (swapped_stack_graphs cohg cohg') ≡
  swapped_stack_tensor (graph_semantics cohg)
    (graph_semantics cohg').
Proof.
  intros Hdisj.

Admitted. *)




(* Lemma graph_semantics_swapped_stack_graphs {n m n' m'}
  (cohg : TensorGraph n m) (cohg' : TensorGraph n' m') :
  graph_semantics (swapped_stack_graphs) *)



End TensorGraphFacts.