Require Import TensorGraphExpr TensorGraphSemantics.
Require Import Aux_pos.
Require Import Tensor.
From stdpp Require Import list fin_maps.
From stdpp Require Import pmap gmap.
Require Import ZXCore.
Require ZifyBool.
Require Import TECospan TEPerm.


#[local] Coercion pos_to_nat_pred : positive >-> nat.

Open Scope nat_scope.


(* FIXME: Move *)
Lemma forall_var (P : var -> Prop) :
  (forall v, P v) <-> (forall r, P (bound r)) /\ (forall l, P (free l)).
Proof.
  split; [auto|].
  now intros (?&?) [].
Qed.







Section TensorGraphFacts.

Context `{SR : SemiRing R rO rI radd rmul req,
  SA : Summable A, EQA : EqDecision A} `{Equiv T} `{Equivalence T equiv}.

Context `{TensT : !TensorLike R A T}.



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
  cbn -[ntl_total_semantics make_vecs_map graph_mabs].
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



Lemma graph_namedtensorlist_semantics_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  (* vhd tg.(inputs) <> vhd tg.(outputs) -> *)
  ntl_eq (list_to_set (((bcons false ∘ Pos.of_succ_nat) <$> seq 0 n)
     ++ ((bcons true ∘ Pos.of_succ_nat) <$> seq 0 m)))
     (graph_namedtensorlist_semantics (add_top_loop tg))
  (ntl_relabel_free (with_bcons Pos.pred)
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
    add_loop_ntl_alt, ntl_relabel_free; cbn.
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
      rewrite ntl_relabel_free_compose.
      etransitivity; [|apply ntl_relabel_free_id].
      apply ntl_relabel_free_ext_strong.
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





(* Lemma graph_contl_semantics_swapped_stack {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  contl_eq (graph_contl_semantics (swapped_stack_graphs tg tg'))
  (swapped_stack_contl
    ((graph_contl_semantics tg))
    ((graph_contl_semantics tg'))).
Proof.
  etransitivity. 1:{
    apply (fun H => @contl_eq_relabel_free
      (pos_elim (λ i, if decide (i < n') then i~0~1
        else (pos_sub_N i (N.of_nat n'))~0~0)
        (λ i, if decide (i < m) then i~1~0
          else (pos_sub_N i (N.of_nat m))~1~1) ) H).
    admit.
  }
  apply contl_eq_of_ntl_eq', ntl_eq_of_ntl_aeq, ntl_aeq_of_perm.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 3 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    + unfold compose.
      cbn.
      apply list_fmap_ext; intros _ ? Hx%elem_of_list_lookup_2%elem_of_seq;
      apply decide_True; lia.
    + unfold compose.
      cbn.
      apply list_fmap_ext; intros _ ? Hx%elem_of_list_lookup_2%elem_of_seq.
      rewrite decide_False by lia.
      lia.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 3 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    + unfold compose.
      cbn.
      apply list_fmap_ext; intros _ ? Hx%elem_of_list_lookup_2%elem_of_seq;
      apply decide_True; lia.
    + unfold compose.
      cbn.
      apply list_fmap_ext; intros _ ? Hx%elem_of_list_lookup_2%elem_of_seq.
      rewrite decide_False by lia.
      lia.
  - cbn.
    rewrite vertices_swapped_stack_graphs.
      rewrite elements_disj_union by set_solver.
      now rewrite <- 2 (fmap_elements _).
  - cbn.

    rewrite tg_abstracts_union by
      now apply map_disjoint_dom;
      rewrite 2 dom_fmap, 2 dom_kmap_L';
      set_solver.
    rewrite 2 tg_abstracts_relabel_abs.

    apply vec_to_list_inj2.
    rewrite 2 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    unfold compose.
    cbn.
    apply list_fmap_ext; lia.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 2 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    unfold compose.
    cbn.
    apply list_fmap_ext; lia.
  - cbn.
    unfold vertices; cbn. *)

(* Lemma graph_contl_semantics_swapped_stack {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  contl_eq (graph_contl_semantics (swapped_stack_graphs_aux tg tg'))
  (swapped_stack_contl_aux
    (relabel_contl_free (pos_map (λ p, pos_add_N p (N.of_nat n')) id)
      (graph_contl_semantics tg))
    (relabel_contl_free (pos_map id (λ p, pos_add_N p (N.of_nat m)))
      (graph_contl_semantics tg'))).
Proof.
  apply contl_eq_of_ntl_eq', ntl_eq_of_ntl_aeq, ntl_aeq_of_perm.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 2 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    unfold compose.
    cbn.
    apply list_fmap_ext; lia.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 2 Vector.map_map, vec_to_list_app, 3 vec_to_list_map,
      3 vec_to_list_seq, seq_app, fmap_app, (Nat.add_comm 0),
        <- (fmap_add_seq), <- list_fmap_compose.
    f_equal.
    unfold compose.
    cbn.
    apply list_fmap_ext; lia.
  - cbn.
    unfold vertices; cbn. *)


Lemma ntl_relabel_free_ntl_times f ntl ntl' :
  ntl_relabel_free f (ntl_times ntl ntl') =
  ntl_times (ntl_relabel_free f ntl) (ntl_relabel_free f ntl').
Proof.
  apply ntl_ext; cbn.
  - done.
  - rewrite fmap_app, <- 4 list_fmap_compose.
    f_equal;
    now apply list_fmap_ext; intros _ flu _; cbn;
    rewrite 2 relabel_abs_compose;
    apply relabel_abs_ext; intros [].
  - rewrite fmap_app, <- 4 list_fmap_compose.
    f_equal;
    now apply list_fmap_ext; intros _ lu _; cbn;
    rewrite 2 relabel_delt_compose;
    apply relabel_delt_ext; intros [].
Qed.

Lemma graph_namedtensorlist_semantics_swapped_stack_graphs {n m n' m'}
  (cohg : TensorGraph n m) (cohg' : TensorGraph n' m') :
  graph_namedtensorlist_semantics (swapped_stack_graphs cohg cohg') =ntl=
  ntl_times
    (ntl_relabel_absidx (bcons false)
      (graph_namedtensorlist_semantics_offset n' 0 cohg))
    (ntl_relabel_absidx (bcons true)
      (graph_namedtensorlist_semantics_offset 0 m cohg')).
Proof.
  apply ntl_aeq_of_perm.
  - cbn.
    rewrite vertices_swapped_stack_graphs.
    rewrite elements_disj_union by set_solver.
    now rewrite <- 2 (fmap_elements _).
  - cbn.
    rewrite tg_abstracts_union by
      now apply map_disjoint_dom;
      rewrite 2 dom_fmap, 2 dom_kmap_L';
      set_solver.
    rewrite 2 tg_abstracts_relabel_abs.
    rewrite 2 (tg_abstracts_kmap _).
    done.
  - cbn -[tg_list_to_deltas].
    rewrite 2 vec_to_list_app, 2 tg_list_to_deltas_app, 2 length_vec_to_list.
    rewrite 4 vec_to_list_map.
    rewrite 2 tg_list_to_deltas_fmap, 2 tg_list_to_deltas_offset_fmap.
    rewrite 2 fmap_app.
    solve_Permutation.
Qed.







Context `{!WFSummable A}.


Lemma graph_mabs_relabel_abs f (hg : Pmap (HyperEdge T)) :
  graph_mabs (relabel_abs f <$> hg) =
  graph_mabs hg.
Proof.
  unfold graph_mabs; cbn.
  rewrite <- map_fmap_compose.
  apply map_fmap_ext; intros _ [[]] _;
  done.
Qed.

Lemma graph_mabs_relabel_graph f {n m} (tg : TensorGraph n m) :
  graph_mabs (relabel_graph f tg).(hedges) = graph_mabs tg.(hedges).
Proof.
  apply graph_mabs_relabel_abs.
Qed.


Lemma graph_mabs_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  graph_mabs (add_top_loop tg).(hedges) = graph_mabs tg.(hedges).
Proof.
  apply (@graph_mabs_relabel_graph _ (S n) (S m)).
Qed.


Lemma graph_semantics_add_top_loop {n m} (tg : TensorGraph (S n) (S m)) :
  graph_semantics (add_top_loop tg) ≡
  join_stack_1_tl_tr (graph_semantics (SR:=SR) tg).
Proof.
  rewrite 2 graph_semantics_to_contl.
  rewrite <- contl_semantics_add_top_loop_gen.
  - rewrite graph_mabs_add_top_loop.
    apply contl_eq_correct, graph_contl_semantics_add_top_loop.
    apply graph_contl_semantics_WT.
  - apply graph_contl_semantics_WT.
  - cbn.
    rewrite vec_to_list_map, vec_to_list_seq.
    rewrite elem_of_list_fmap.
    intros (? & ? & _).
    cbn in *.
    lia.
Qed.

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



Lemma graph_namedtensorlist_semantics_offset_WF noff moff `(tg : TensorGraph n m) :
  WF_ntl (graph_namedtensorlist_semantics_offset noff moff tg).
Proof.
  rewrite graph_namedtensorlist_semantics_offset_correct.
  apply ntl_relabel_free_WF, graph_namedtensorlist_semantics_WF.
Qed.

Lemma graph_mabs_union (hg hg' : Pmap (HyperEdge T)) :
  graph_mabs (hg ∪ hg') =
  graph_mabs hg ∪ graph_mabs hg'.
Proof.
  unfold graph_mabs.
  rewrite map_fmap_union.
  done.
Qed.

Lemma graph_mabs_kmap f (hg : Pmap (HyperEdge T)) :
  graph_mabs (kmap f hg) = kmap f (graph_mabs hg).
Proof.
  symmetry;
  apply kmap_fmap'.
Qed.
Lemma ntl_free_varset_relabel_absidx f ntl :
  ntl_free_varset (ntl_relabel_absidx f ntl) = ntl_free_varset ntl.
Proof.
  unfold ntl_free_varset.
  cbn.
  f_equal.
  unfold abstracts_free_vars.
  rewrite list_fmap_bind.
  unfold compose.
  f_equal.
  apply list_bind_ext; [now intros [[]]|done].
Qed.


Lemma graph_semantics_swapped_stack_graphs {n m n' m'}
  (cohg : TensorGraph n m) (cohg' : TensorGraph n' m') :
  graph_semantics (SR:=SR) (swapped_stack_graphs cohg cohg') ≡
  swapped_stack_tensor (graph_semantics cohg) (graph_semantics cohg').
Proof.
  intros v w Hv Hw.

  induction v as [vl vr] using vec_add_inv.
  induction w as [wl wr] using vec_add_inv.
  rewrite 3 graph_semantics_to_contl.
  cbn -[ntl_total_semantics ntl_times graph_mabs].
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  unfold graph_contl_semantics, contl_semantics;
  cbn -[ntl_total_semantics ntl_times graph_mabs make_vecs_map].
  erewrite ntl_aeq_correct by first [apply graph_namedtensorlist_semantics_WF|
    apply graph_namedtensorlist_semantics_swapped_stack_graphs].
  rewrite ntl_total_semantics_ntl_times by now apply ntl_relabel_absidx_WF,
    graph_namedtensorlist_semantics_offset_WF.
  f_equiv.
  - rewrite graph_namedtensorlist_semantics_offset_correct.
    symmetry.
    rewrite <- (ntl_relabel_free_semantics_kmap _ _ (pos_map (pos_nat_add n') (pos_nat_add 0))).
    rewrite <- (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ (bcons false)).
    rewrite graph_mabs_union, 2 graph_mabs_relabel_abs, 2 graph_mabs_kmap.

    etransitivity; [apply ntl_total_semantics_absidxs_ext|
      apply ntl_total_semantics_free_varset_ext].
    + rewrite abstracts_indices_relabel_absidx.
      cbn -[abstracts_indices].
      rewrite abstracts_indices_relabel_abs.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite lookup_union.
      rewrite (lookup_kmap_None (bcons true) _ _).2 by lia.
      now rewrite (right_id None _).
    + rewrite ntl_free_varset_relabel_absidx, ntl_free_varset_ntl_relabel_free.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite (lookup_kmap _).
      unfold make_vecs_map.
      rewrite 4 vzip_map_l, 4 vec_to_list_map.
      rewrite <- 4 (kmap_list_to_map _).
      rewrite 2 lookup_union.
      destruct i as [i|i|].
      * replace (i~1) with ((bcons true ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons false ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        change (?x~1) with ((bcons true ∘ Pos.of_succ_nat) i).
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list wl) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        setoid_rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite 2option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        apply lookup_app_l.
        rewrite ntl_free_varset_graph in Hi.
        rewrite elem_of_list_to_set in Hi.
        rewrite 2 vec_to_list_map, 2 vec_to_list_seq in Hi.
        set_unfold in Hi.
        setoid_rewrite elem_of_seq in Hi.
        cbn in Hi.
        rewrite length_vec_to_list.
        destruct Hi as [[]|[]]; lia.
      * replace (i~0) with ((bcons false ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons true ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~0) with ((bcons false ∘ Pos.of_succ_nat) (n' + i)%nat) by now cbn; lia.
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list vr) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (vl +++ vr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite (lookup_list_to_map_imap id id _ (n' + i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        rewrite lookup_app_r; [f_equal; rewrite length_vec_to_list; lia|].
        rewrite length_vec_to_list.
        lia.
      * rewrite 4(lookup_kmap_None _ _ _).2 by now cbn; lia.
        done.
  - rewrite graph_namedtensorlist_semantics_offset_correct.
    symmetry.
    rewrite <- (ntl_relabel_free_semantics_kmap _ _ (pos_map (pos_nat_add 0) (pos_nat_add m))).
    rewrite <- (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ (bcons true)).
    rewrite graph_mabs_union, 2 graph_mabs_relabel_abs, 2 graph_mabs_kmap.

    etransitivity; [apply ntl_total_semantics_absidxs_ext|
      apply ntl_total_semantics_free_varset_ext].
    + rewrite abstracts_indices_relabel_absidx.
      cbn -[abstracts_indices].
      rewrite abstracts_indices_relabel_abs.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite lookup_union.
      rewrite (lookup_kmap_None (bcons false) _ _).2 by lia.
      now rewrite (left_id None _).
    + rewrite ntl_free_varset_relabel_absidx, ntl_free_varset_ntl_relabel_free.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite (lookup_kmap _).
      unfold make_vecs_map.
      rewrite 4 vzip_map_l, 4 vec_to_list_map.
      rewrite <- 4 (kmap_list_to_map _).
      rewrite 2 lookup_union.
      destruct i as [i|i|].
      * replace (i~1) with ((bcons true ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons false ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~1) with ((bcons true ∘ Pos.of_succ_nat) (m + i)%nat) by now cbn; lia.
        (* change (?x~1) with ((bcons true ∘ Pos.of_succ_nat) i). *)
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list wr) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite (lookup_list_to_map_imap id id _ (m + i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        rewrite lookup_app_r; [f_equal; rewrite length_vec_to_list; lia|].
        rewrite length_vec_to_list.
        lia.
      * replace (i~0) with ((bcons false ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons true ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~0) with ((bcons false ∘ Pos.of_succ_nat) (i)) by now cbn; lia.
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list vl) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (vl +++ vr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite 2 (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        apply lookup_app_l.
        rewrite ntl_free_varset_graph in Hi.
        rewrite elem_of_list_to_set in Hi.
        rewrite 2 vec_to_list_map, 2 vec_to_list_seq in Hi.
        set_unfold in Hi.
        setoid_rewrite elem_of_seq in Hi.
        cbn in Hi.
        rewrite length_vec_to_list.
        destruct Hi as [[]|[]]; lia.
      * rewrite 4(lookup_kmap_None _ _ _).2 by now cbn; lia.
        done.
Qed.

Lemma graph_semantics_compose_graphs_alt {n m o}
  (cohg : TensorGraph n m) (cohg' : TensorGraph m o) :
  graph_semantics (SR:=SR) (compose_graphs_alt cohg cohg') ≡
  compose_tensor (graph_semantics cohg) (graph_semantics cohg').
Proof.
  unfold compose_graphs_alt.
  rewrite graph_semantics_add_top_loops.
  erewrite join_stack_tl_tr_mor by now apply graph_semantics_swapped_stack_graphs.
  symmetry; apply compose_to_swapped_stack.
Qed.

Lemma graph_semantics_compose_graphs {n m o}
  (cohg : TensorGraph n m) (cohg' : TensorGraph m o) :
  graph_semantics (SR:=SR) (compose_graphs cohg cohg') ≡
  compose_tensor (graph_semantics cohg) (graph_semantics cohg').
Proof.
  rewrite <- graph_semantics_norm_verts.
  rewrite <- compose_graphs_alt_correct.
  rewrite graph_semantics_norm_verts.
  apply graph_semantics_compose_graphs_alt.
Qed.

Lemma graph_semantics_stack_graphs {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  graph_semantics (SR:=SR) (stack_graphs tg tg') ≡
  stack_tensor (graph_semantics tg) (graph_semantics tg').
Proof.
  intros v w Hv Hw.

  induction v as [vl vr] using vec_add_inv.
  induction w as [wl wr] using vec_add_inv.
  rewrite 3 graph_semantics_to_contl.
  cbn -[ntl_total_semantics ntl_times graph_mabs].
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  unfold graph_contl_semantics, contl_semantics;
  cbn -[ntl_total_semantics ntl_times graph_mabs make_vecs_map].
  erewrite ntl_aeq_correct by first [apply graph_namedtensorlist_semantics_WF|
    apply graph_namedtensorlist_semantics_stack].
  rewrite ntl_total_semantics_ntl_times by now apply ntl_relabel_absidx_WF;
    apply graph_namedtensorlist_semantics_WF ||
    apply graph_namedtensorlist_semantics_offset_WF.
  f_equiv.
  - (* rewrite graph_namedtensorlist_semantics_offset_correct. *)
    symmetry.
    (* rewrite <- (ntl_relabel_free_semantics_kmap _ _ (pos_map (pos_nat_add n') (pos_nat_add 0))). *)
    rewrite <- (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ (bcons false)).
    rewrite graph_mabs_union, 2 graph_mabs_relabel_abs, 2 graph_mabs_kmap.
    etransitivity; [apply ntl_total_semantics_absidxs_ext|
      apply ntl_total_semantics_free_varset_ext].
    + rewrite abstracts_indices_relabel_absidx.
      cbn -[abstracts_indices].
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite lookup_union.
      rewrite (lookup_kmap_None (bcons true) _ _).2 by lia.
      now rewrite (right_id None _).
    + rewrite ntl_free_varset_relabel_absidx.
      intros i Hi.

      (* intros _ (i & -> & Hi)%elem_of_map.
      rewrite (lookup_kmap _). *)
      unfold make_vecs_map.
      rewrite 4 vzip_map_l, 4 vec_to_list_map.
      rewrite <- 4 (kmap_list_to_map _).
      rewrite 2 lookup_union.
      destruct i as [i|i|].
      * replace (i~1) with ((bcons true ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons false ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        change (?x~1) with ((bcons true ∘ Pos.of_succ_nat) i).
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list wl) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        setoid_rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite 2option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        apply lookup_app_l.
        rewrite ntl_free_varset_graph in Hi.
        rewrite elem_of_list_to_set in Hi.
        rewrite 2 vec_to_list_map, 2 vec_to_list_seq in Hi.
        set_unfold in Hi.
        setoid_rewrite elem_of_seq in Hi.
        cbn in Hi.
        rewrite length_vec_to_list.
        destruct Hi as [[]|[]]; lia.
      * replace (i~0) with ((bcons false ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons true ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~0) with ((bcons false ∘ Pos.of_succ_nat) (i)) by now cbn; lia.
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list vl) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (vl +++ vr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite 2 (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        apply lookup_app_l.
        rewrite ntl_free_varset_graph in Hi.
        rewrite elem_of_list_to_set in Hi.
        rewrite 2 vec_to_list_map, 2 vec_to_list_seq in Hi.
        set_unfold in Hi.
        setoid_rewrite elem_of_seq in Hi.
        cbn in Hi.
        rewrite length_vec_to_list.
        destruct Hi as [[]|[]]; lia.
      * rewrite 4(lookup_kmap_None _ _ _).2 by now cbn; lia.
        done.
  - rewrite graph_namedtensorlist_semantics_offset_correct.
    symmetry.
    rewrite <- (ntl_relabel_free_semantics_kmap _ _ (pos_map (pos_nat_add n) (pos_nat_add m))).
    rewrite <- (ntl_total_semantics_kmap_ntl_relabel_absidx _ _ (bcons true)).
    rewrite graph_mabs_union, 2 graph_mabs_relabel_abs, 2 graph_mabs_kmap.

    etransitivity; [apply ntl_total_semantics_absidxs_ext|
      apply ntl_total_semantics_free_varset_ext].
    + rewrite abstracts_indices_relabel_absidx.
      cbn -[abstracts_indices].
      rewrite abstracts_indices_relabel_abs.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite lookup_union.
      rewrite (lookup_kmap_None (bcons false) _ _).2 by lia.
      now rewrite (left_id None _).
    + rewrite ntl_free_varset_relabel_absidx, ntl_free_varset_ntl_relabel_free.
      intros _ (i & -> & Hi)%elem_of_map.
      rewrite (lookup_kmap _).
      unfold make_vecs_map.
      rewrite 4 vzip_map_l, 4 vec_to_list_map.
      rewrite <- 4 (kmap_list_to_map _).
      rewrite 2 lookup_union.
      destruct i as [i|i|].
      * replace (i~1) with ((bcons true ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons false ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~1) with ((bcons true ∘ Pos.of_succ_nat) (m + i)%nat) by now cbn; lia.
        (* change (?x~1) with ((bcons true ∘ Pos.of_succ_nat) i). *)
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list wr) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite (lookup_list_to_map_imap id id _ (m + i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        rewrite lookup_app_r; [f_equal; rewrite length_vec_to_list; lia|].
        rewrite length_vec_to_list.
        lia.
      * replace (i~0) with ((bcons false ∘ Pos.of_succ_nat) i) by now cbn; lia.
        rewrite (lookup_kmap_None (bcons true ∘ _) _ _).2 by now cbn; lia.
        rewrite (lookup_kmap _).
        cbn.
        replace (_~0) with ((bcons false ∘ Pos.of_succ_nat) (n + i)%nat) by now cbn; lia.
        rewrite (lookup_kmap _).
        rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
        f_equal.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list vr) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite vec_to_list_zip_with, vec_to_list_seq.
        rewrite <- (length_vec_to_list (vl +++ vr)) at 1.
        rewrite <- imap_to_zip_with_seq.
        rewrite (lookup_list_to_map_imap id id _ (pos_to_nat_pred i)).
        rewrite (lookup_list_to_map_imap id id _ (n + i)).
        rewrite 2 option_fmap_id.
        rewrite vec_to_list_app.
        symmetry.
        rewrite lookup_app_r; [f_equal; rewrite length_vec_to_list; lia|].
        rewrite length_vec_to_list.
        lia.
      * rewrite 4(lookup_kmap_None _ _ _).2 by now cbn; lia.
        done.
Qed.


(* TODO: General for perm graph *)


Lemma graph_namedtensorlist_semantics_WT' {n m} (tg : TensorGraph n m) :
  WT_ntl (list_to_set
     (vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n) ++
      vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m)))
    (graph_namedtensorlist_semantics tg).
Proof.
  rewrite WT_ntl_alt_varset.
  split; [|apply graph_namedtensorlist_semantics_WF].
  now rewrite ntl_free_varset_graph.
Qed.

Lemma graph_namedtensorlist_semantics_WT {n m} (tg : TensorGraph n m)
  (v w : vec A _) :
  WT_ntl (dom $ make_vecs_map
    (vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n))
    (vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m))
    v w)
    (graph_namedtensorlist_semantics tg).
Proof.
  rewrite dom_make_vecs_map.
  apply graph_namedtensorlist_semantics_WT'.
Qed.


Lemma graph_namedtensorlist_semantics_WT'' {n m} (tg : TensorGraph n m) :
  WT_ntl (list_to_set
     (((bcons false ∘ Pos.of_succ_nat) <$> (seq 0 n)) ++
      ((bcons true ∘ Pos.of_succ_nat) <$> (seq 0 m))))
    (graph_namedtensorlist_semantics tg).
Proof.
  rewrite <- 2 vec_to_list_seq, <- 2 vec_to_list_map.
  apply graph_namedtensorlist_semantics_WT'.
Qed.

Lemma graph_namedtensorlist_semantics_id_graph n :
  ntl_eq (list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 n)))
    (graph_namedtensorlist_semantics (@id_graph T n))
    (mk_ntl [] []
      (((λ i, (free $ bcons false i, free $ bcons true i)) ∘ Pos.of_succ_nat)
      <$> seq 0 n)).
Proof.
  unfold graph_namedtensorlist_semantics; cbn.
  unfold vertices.
  cbn.
  rewrite simplify_ntl_deltas_app_right; [|apply NoDup_elements|].
  2:{
    pose proof (graph_namedtensorlist_semantics_WT'' (@id_graph T n))
    as HWT.
    rewrite WT_ntl_alt in HWT.
    rewrite <- HWT.2.
    rewrite <- union_subseteq_r.
    cbn.
    unfold deltas_vars.
    rewrite bind_app, list_to_set_app.
    apply union_subseteq_r.
  }
  erewrite simplify_ntl_deltas_aux_full_subst_r.
  5:{
    rewrite imap_to_zip_with_seq.
    rewrite vec_to_list_to_vec.
    rewrite length_vec_to_list.
    rewrite <- (zip_with_fmap_l (λ a b, (free a, bound b)) (λ n, (Pos.of_succ_nat n)~1)).
    reflexivity.
  }
  2:{
    apply (list_to_set_subseteq (C:=Pset)).
    rewrite list_to_set_elements.
    rewrite <- union_subseteq_r.
    rewrite list_to_set_app.
    apply union_subseteq_l.
  }
  2:{
    rewrite vec_to_list_map, vec_to_list_seq.
    rewrite (NoDup_fmap _); apply NoDup_seq.
  }
  2:{
    now rewrite length_vec_to_list, length_fmap, length_seq.
  }
  cbn.
  apply eq_reflexivity.
  f_equal.
  - apply list_filter_none.
    intros a.
    rewrite elem_of_elements.
    change (vertices_hg ∅) with (∅ :> Pset).
    rewrite union_empty_l_L.
    rewrite list_to_set_app, union_idemp_L.
    rewrite elem_of_list_to_set.
    easy.
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, length_imap, length_vec_to_list, length_seq|].
    intros i lu lu'.
    rewrite length_fmap, length_seq.
    intros Hi.
    rewrite 2 list_lookup_fmap, list_lookup_imap.
    rewrite vec_to_list_map, vec_to_list_seq.
    rewrite list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    rewrite zip_with_fmap_l, zip_with_fmap_r, zip_with_diag.
    cbn.
    rewrite gmap_map_idemp. 2:{
      rewrite dom_list_to_map.
      rewrite <- list_fmap_compose; unfold compose; cbn.
      set_solver +.
    }
    erewrite gmap_map_correct; [now intros [= <-] [= <-]; reflexivity|].
    apply elem_of_list_to_map.
    + rewrite <- list_fmap_compose; unfold compose; cbn.
      rewrite (NoDup_fmap _); apply NoDup_seq.
    + refine (elem_of_list_fmap_1 _ _ i _).
      now apply elem_of_seq; lia.
Qed.

Lemma imap_vec_to_list {B C} (f : nat -> B -> C) {n} (v : vec B n) :
  imap f v = fun_to_vec (λ i, f i (v !!! i)).
Proof.
  apply (list_eq_same_length _ _ _ eq_refl);
  [now rewrite length_imap, 2 length_vec_to_list|].
  rewrite length_vec_to_list.
  intros i a b Hi.
  rewrite list_lookup_imap.
  rewrite fmap_Some.
  intros (fia & (Hi' & Hvi)%vlookup_lookup' & ->).
  intros (Hi'' & <-)%vlookup_lookup'.
  rewrite lookup_fun_to_vec, fin_to_nat_to_fin.
  f_equal.
  rewrite <- Hvi.
  f_equal.
  apply fin_to_nat_inj.
  now rewrite 2 fin_to_nat_to_fin.
Qed.

Lemma graph_namedtensorlist_semantics_swap_graph n m :
  ntl_eq (list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 (n + m)) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 (m + n))))
    (graph_namedtensorlist_semantics (@swap_graph T n m))
    (mk_ntl [] []
      ((((λ i, (free $ bcons false (Pos.of_succ_nat i),
        free $ bcons true (Pos.of_succ_nat (m + i))))) <$> seq 0 n)
      ++ (((λ i, (free $ bcons false (Pos.of_succ_nat (n + i)),
        free $ bcons true (Pos.of_succ_nat i)))) <$> seq 0 m) )).
Proof.
  unfold graph_namedtensorlist_semantics; cbn.
  rewrite <- vseq_app.
  (* unfold vertices. *)
  (* cbn. *)
  rewrite simplify_ntl_deltas_app_right; [|apply NoDup_elements|].
  2:{
    pose proof (graph_namedtensorlist_semantics_WT'' (@swap_graph T n m))
    as HWT.
    rewrite WT_ntl_alt in HWT.
    rewrite <- HWT.2.
    rewrite <- union_subseteq_r.
    cbn.
    unfold deltas_vars.
    rewrite bind_app, list_to_set_app.
    apply union_subseteq_r.
  }
  erewrite simplify_ntl_deltas_aux_full_subst_r.
  5:{
    rewrite imap_to_zip_with_seq.
    rewrite vec_to_list_to_vec.
    rewrite length_vec_to_list.
    rewrite <- (zip_with_fmap_l (λ a b, (free a, bound b)) (λ n, (Pos.of_succ_nat n)~1)).
    reflexivity.
  }
  2:{
    apply (list_to_set_subseteq (C:=Pset)).
    rewrite list_to_set_elements.
    unfold vertices.
    rewrite <- union_subseteq_r.
    rewrite list_to_set_app, <- union_subseteq_l.
    cbn.
    rewrite 2 vec_to_list_map, 2 vec_to_list_app, Permutation_app_comm.
    done.
  }
  2:{
    rewrite vec_to_list_map, vec_to_list_app, Permutation_app_comm,
      2 vec_to_list_seq, <- seq_app.
    rewrite (NoDup_fmap _); apply NoDup_seq.
  }
  2:{
    now rewrite length_vec_to_list, length_fmap, length_seq.
  }
  cbn.
  apply eq_reflexivity.
  f_equal.
  - apply list_filter_none.
    intros a.
    unfold vertices.
    rewrite elem_of_elements.
    cbn.
    change (vertices_hg ∅) with (∅ :> Pset).
    rewrite union_empty_l_L.
    rewrite 2 vec_to_list_map, 2 vec_to_list_app, list_to_set_app,
      Permutation_app_comm.
    rewrite union_idemp_L.
    rewrite elem_of_list_to_set.
    easy.
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_app, 3 length_fmap, length_imap,
      length_vec_to_list, 2 length_seq|].
    intros i lu lu'.
    rewrite length_app, 2 length_fmap, 2 length_seq.
    intros Hi.
    rewrite list_lookup_fmap, list_lookup_imap.
    rewrite 2 vec_to_list_map, vec_to_list_seq, list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite gmap_map_idemp. 2:{
      rewrite dom_list_to_map.
      rewrite fmap_zip_with; cbn.
      rewrite elem_of_list_to_set.
      intros (?&?&[=]&_)%elem_of_zip_with.
    }
    intros [= <-].
    destruct_decide (decide (i < n)) as Hin.
    + rewrite lookup_app_l by now rewrite length_fmap, length_seq.
      rewrite list_lookup_fmap, lookup_seq_lt by done.
      cbn.
      intros [= <-].
      f_equal.
      apply gmap_map_correct.
      apply elem_of_list_to_map. 1:{
        rewrite fmap_zip_with; cbn.
        rewrite zip_with_to_fmap_l by
          now rewrite 2 length_fmap, length_vec_to_list, length_seq.
        rewrite 2 (NoDup_fmap _).
        rewrite vec_to_list_app, 2 vec_to_list_seq, Permutation_app_comm.
        rewrite <- seq_app.
        apply NoDup_seq.
      }
      apply elem_of_list_lookup.
      exists (m + i)%nat.
      rewrite lookup_zip_with.
      rewrite 2 list_lookup_fmap.
      rewrite vec_to_list_app, lookup_app_r by now rewrite length_vec_to_list; lia.
      rewrite length_vec_to_list.
      rewrite vec_to_list_seq, 2 lookup_seq_lt by lia.
      cbn.
      repeat first [lia|f_equal].
    + rewrite lookup_app_r by now rewrite length_fmap, length_seq; lia.
      rewrite length_fmap, length_seq.
      rewrite list_lookup_fmap, lookup_seq_lt by lia.
      cbn.
      intros [= <-].
      f_equal; [f_equal; lia|].
      apply gmap_map_correct.
      apply elem_of_list_to_map. 1:{
        rewrite fmap_zip_with; cbn.
        rewrite zip_with_to_fmap_l by
          now rewrite 2 length_fmap, length_vec_to_list, length_seq.
        rewrite 2 (NoDup_fmap _).
        rewrite vec_to_list_app, 2 vec_to_list_seq, Permutation_app_comm.
        rewrite <- seq_app.
        apply NoDup_seq.
      }
      apply elem_of_list_lookup.
      exists (i - n).
      rewrite lookup_zip_with.
      rewrite 2 list_lookup_fmap.
      rewrite lookup_seq_lt by lia.
      rewrite vec_to_list_app, lookup_app_l by now rewrite length_vec_to_list; lia.
      rewrite vec_to_list_seq, lookup_seq_lt by lia.
      cbn.
      repeat first [lia|f_equal].
Qed.

Lemma graph_namedtensorlist_semantics_cup_graph n :
  ntl_eq (list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 0) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 (n + n))))
    (graph_namedtensorlist_semantics (@cup_graph T n))
    (mk_ntl [] []
      (((λ i, (free $ bcons true (Pos.of_succ_nat i),
        free $ bcons true (Pos.of_succ_nat (n + i))))) <$> seq 0 n)
      ).
Proof.
  unfold graph_namedtensorlist_semantics; cbn.
  rewrite Vector.map_append, vec_to_list_app, imap_app.
  rewrite length_vec_to_list.
  (* unfold vertices. *)
  (* cbn. *)
  rewrite simplify_ntl_deltas_app_right; [|apply NoDup_elements|].
  2:{
    pose proof (graph_namedtensorlist_semantics_WT'' (@cup_graph T n))
    as HWT.
    rewrite WT_ntl_alt in HWT.
    rewrite <- HWT.2.
    rewrite <- union_subseteq_r.
    cbn.
    unfold deltas_vars.
    rewrite Vector.map_append, vec_to_list_app, imap_app.
    rewrite bind_app, list_to_set_app, length_vec_to_list.
    apply union_subseteq_r.
  }
  erewrite simplify_ntl_deltas_aux_full_subst_r.
  5:{
    rewrite imap_to_zip_with_seq.
    rewrite vec_to_list_to_vec.
    rewrite length_vec_to_list.
    rewrite <- (zip_with_fmap_l (λ a b, (free a, bound b)) (λ k, (Pos.of_succ_nat (n + k))~1)).
    reflexivity.
  }
  2:{
    apply (list_to_set_subseteq (C:=Pset)).
    rewrite list_to_set_elements.
    unfold vertices.
    rewrite <- union_subseteq_r.
    rewrite list_to_set_app, <- union_subseteq_r.
    cbn.
    rewrite Vector.map_append, vec_to_list_app, list_to_set_app.
    apply union_subseteq_l.
  }
  2:{
    rewrite vec_to_list_map, vec_to_list_seq.
    rewrite (NoDup_fmap _); apply NoDup_seq.
  }
  2:{
    now rewrite length_vec_to_list, length_fmap, length_seq.
  }
  cbn.
  apply eq_reflexivity.
  f_equal.
  - apply list_filter_none.
    intros a.
    unfold vertices.
    rewrite elem_of_elements.
    cbn.
    change (vertices_hg ∅) with (∅ :> Pset).
    rewrite union_empty_l_L.
    rewrite Vector.map_append, vec_to_list_app, list_to_set_app.
    rewrite union_idemp_L.
    rewrite elem_of_list_to_set.
    easy.
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, length_imap, length_vec_to_list, length_seq|].
    intros i lu lu'.
    rewrite length_fmap, length_seq.
    intros Hi.
    rewrite list_lookup_fmap, list_lookup_imap.
    rewrite vec_to_list_map, vec_to_list_seq, list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite gmap_map_idemp. 2:{
      rewrite dom_list_to_map.
      rewrite fmap_zip_with; cbn.
      rewrite elem_of_list_to_set.
      intros (?&?&[=]&_)%elem_of_zip_with.
    }
    intros [= <-].
    rewrite list_lookup_fmap, lookup_seq_lt by done.
    cbn.
    intros [= <-].
    f_equal.
    apply gmap_map_correct.
    apply elem_of_list_to_map. 1:{
      rewrite fmap_zip_with; cbn.
      rewrite zip_with_to_fmap_l by
        now rewrite 2 length_fmap.
      rewrite 2 (NoDup_fmap _).
      apply NoDup_seq.
    }
    apply elem_of_list_lookup.
    exists i%nat.
    rewrite lookup_zip_with.
    rewrite 2 list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    done.
Qed.

Lemma graph_namedtensorlist_semantics_cap_graph n :
  ntl_eq (list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 (n + n)) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 0)))
    (graph_namedtensorlist_semantics (@cap_graph T n))
    (mk_ntl [] []
      (((λ i, (free $ bcons false (Pos.of_succ_nat i),
        free $ bcons false (Pos.of_succ_nat (n + i))))) <$> seq 0 n)
      ).
Proof.
  unfold graph_namedtensorlist_semantics; cbn.
  rewrite Vector.map_append, vec_to_list_app, imap_app.
  rewrite length_vec_to_list, (app_nil_r (_ ++ _)).
  (* unfold vertices. *)
  (* cbn. *)
  rewrite simplify_ntl_deltas_app_right; [|apply NoDup_elements|].
  2:{
    pose proof (graph_namedtensorlist_semantics_WT'' (@cap_graph T n))
    as HWT.
    rewrite WT_ntl_alt in HWT.
    rewrite <- HWT.2.
    rewrite <- union_subseteq_r.
    cbn.
    unfold deltas_vars.
    rewrite app_nil_r.
    rewrite Vector.map_append, vec_to_list_app, imap_app.
    rewrite bind_app, list_to_set_app, length_vec_to_list.
    apply union_subseteq_r.
  }
  rewrite app_nil_r.
  erewrite simplify_ntl_deltas_aux_full_subst_r.
  5:{
    rewrite imap_to_zip_with_seq.
    rewrite vec_to_list_to_vec.
    rewrite length_vec_to_list.
    rewrite <- (zip_with_fmap_l (λ a b, (free a, bound b)) (λ k, (Pos.of_succ_nat (n + k))~0)).
    reflexivity.
  }
  2:{
    apply (list_to_set_subseteq (C:=Pset)).
    rewrite list_to_set_elements.
    unfold vertices.
    rewrite <- union_subseteq_r.
    rewrite list_to_set_app, <- union_subseteq_l.
    cbn.
    rewrite Vector.map_append, vec_to_list_app, list_to_set_app.
    apply union_subseteq_l.
  }
  2:{
    rewrite vec_to_list_map, vec_to_list_seq.
    rewrite (NoDup_fmap _); apply NoDup_seq.
  }
  2:{
    now rewrite length_vec_to_list, length_fmap, length_seq.
  }
  cbn.
  apply eq_reflexivity.
  f_equal.
  - apply list_filter_none.
    intros a.
    unfold vertices.
    rewrite elem_of_elements.
    cbn.
    change (vertices_hg ∅) with (∅ :> Pset).
    rewrite union_empty_l_L.
    rewrite Vector.map_append, vec_to_list_app, app_nil_r, list_to_set_app.
    rewrite union_idemp_L.
    rewrite elem_of_list_to_set.
    easy.
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, length_imap, length_vec_to_list, length_seq|].
    intros i lu lu'.
    rewrite length_fmap, length_seq.
    intros Hi.
    rewrite list_lookup_fmap, list_lookup_imap.
    rewrite vec_to_list_map, vec_to_list_seq, list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite gmap_map_idemp. 2:{
      rewrite dom_list_to_map.
      rewrite fmap_zip_with; cbn.
      rewrite elem_of_list_to_set.
      intros (?&?&[=]&_)%elem_of_zip_with.
    }
    intros [= <-].
    rewrite list_lookup_fmap, lookup_seq_lt by done.
    cbn.
    intros [= <-].
    f_equal.
    apply gmap_map_correct.
    apply elem_of_list_to_map. 1:{
      rewrite fmap_zip_with; cbn.
      rewrite zip_with_to_fmap_l by
        now rewrite 2 length_fmap.
      rewrite 2 (NoDup_fmap _).
      apply NoDup_seq.
    }
    apply elem_of_list_lookup.
    exists i%nat.
    rewrite lookup_zip_with.
    rewrite 2 list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    done.
Qed.


Lemma vertices_graph_of_tensor (t : T) n m :
  vertices (graph_of_tensor t n m) =
  list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 m)).
Proof.
  unfold vertices.
  cbn.
  unfold vertices_hg.
  rewrite hyperedges_singleton.
  rewrite map_to_list_singleton.
  cbn.
  rewrite app_nil_r.
  rewrite union_empty_r_L.
  rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
  apply union_idemp_L.
Qed.

Lemma graph_namedtensorlist_semantics_graph_of_tensor (t : T) n m :
  ntl_eq ((list_to_set ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 m))))
    (graph_namedtensorlist_semantics (graph_of_tensor t n m))
    (mk_ntl [] [(xH, (free ∘ bcons false ∘ Pos.of_succ_nat <$> seq 0 n),
      (free ∘ bcons true ∘ Pos.of_succ_nat <$> seq 0 m))] []).
Proof.
  unfold graph_namedtensorlist_semantics; cbn -[insert].
  rewrite hyperedges_singleton.
  rewrite <- simplify_ntl_deltas_correct by
    apply graph_namedtensorlist_semantics_WT''.
  rewrite (simplify_ntl_deltas_full_subst_r _
    ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 m))
    ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n) ++
    (bcons true ∘ Pos.of_succ_nat <$> seq 0 m))). 2:{
    cbn.
    rewrite zip_with_diag.
    rewrite 2 vec_to_list_map, 2 vec_to_list_seq,
      2 imap_fmap, 2 imap_to_zip_with_seq, 2 length_seq, 2 zip_with_diag.
    cbn.
    rewrite fmap_app.
    rewrite <- 2 list_fmap_compose.
    done.
  }
  2: done.
  2:{
    cbn.
    rewrite vertices_graph_of_tensor.
    intros x Hx.
    now rewrite elem_of_elements, elem_of_list_to_set.
  }
  2:{
    rewrite NoDup_app.
    split; [|split]; cycle 1; [|apply (NoDup_fmap _), NoDup_seq..].
    set_solver +.
  }
  cbn.
  apply eq_reflexivity.
  f_equal.
  - apply list_filter_none.
    rewrite vertices_graph_of_tensor.
    intros a.
    now rewrite elem_of_elements, elem_of_list_to_set.
  - unfold tg_abstracts.
    rewrite map_to_list_singleton.
    cbn.
    f_equal.
    rewrite zip_with_diag.
    f_equal; [f_equal|];
    rewrite <- 2 list_fmap_compose; apply list_fmap_ext;
    intros _ i [_ Hi]%elem_of_list_lookup_2%elem_of_seq;
    cbn; apply gmap_map_correct;
    (apply elem_of_list_to_map; [
        rewrite <- list_fmap_compose; unfold compose at 1; cbn;
        rewrite (NoDup_fmap _); apply NoDup_app;
        (split; [|split]; cycle 1; [set_solver|apply (NoDup_fmap _), NoDup_seq..])|]);
    refine (elem_of_list_fmap_1 _ _ _ _);
    rewrite elem_of_app; [left|right];
    refine (elem_of_list_fmap_1 _ _ _ _);
    rewrite elem_of_seq; lia.
Qed.






Lemma Rlist_prod_vec_if_eq `{EqA : EqDecision A} {n} (v w : vec A n) :
  Rlist_prod ((fun i => if decide (vec_to_list v !! i = vec_to_list w !! i)
  then rI else rO) <$> seq 0 n) == if decide (v = w) then rI else rO.
Proof.
  revert v w; induction n; [do 2 refine (vec_0_inv _ _); done|].
  refine (vec_S_inv _ _).
  intros vh v.
  refine (vec_S_inv _ _).
  intros wh w.
  cbn.
  rewrite <- fmap_S_seq, <- list_fmap_compose.
  unfold compose.
  cbn.
  rewrite IHn.
  symmetry.
  case_decide as Hboth.
  - apply Vector.cons_inj in Hboth as [-> ->].
    rewrite 2 decide_True by done.
    ring.
  - case_decide; [|ring].
    case_decide; [|ring].
    congruence.
Qed.

Lemma graph_semantics_id {n} :
  graph_semantics (SR:=SR) (@id_graph T n) ≡ delta_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics].
  unfold namedtensorlist_to_tensor.
  erewrite ntl_eq_correct; try first [
    now apply make_vecs_map_SummedElements|
    apply graph_namedtensorlist_semantics_WT|
    rewrite dom_make_vecs_map, 2 vec_to_list_map, vec_to_list_seq;
    try apply graph_namedtensorlist_semantics_id_graph].
  rewrite ntl_total_semantics_alt by now eapply ntl_eq_WF;
    [apply symmetry, graph_namedtensorlist_semantics_id_graph|
    apply graph_namedtensorlist_semantics_WF].
  cbn -[deltas_semantics_alt].
  rewrite sum_of_Vmap_nil.
  rewrite rmul_1_l.
  unfold deltas_semantics_alt.
  rewrite <- list_fmap_compose.
  rewrite <- Rlist_prod_vec_if_eq.
  apply Rlist_prod_ext.
  apply Forall2_fmap, Forall_Forall2_diag, Forall_seq.
  intros j [_ Hj].
  cbn.
  unfold make_vecs_map.
  rewrite 2 vec_to_list_zip_with, 2 vec_to_list_map, vec_to_list_seq,
    2 zip_fmap_l, <- 2 (kmap_list_to_map _).
  rewrite 2 lookup_union.
  change ((Pos.of_succ_nat j)~0) with ((bcons false ∘ Pos.of_succ_nat) j).
  rewrite (lookup_kmap _).
  rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
  rewrite (lookup_kmap_None (bcons true ∘ Pos.of_succ_nat) _
    ((bcons false ∘ Pos.of_succ_nat) j)).2 by now cbn; lia.
  rewrite (right_id_L None _), (left_id_L None _).
  change ((Pos.of_succ_nat j)~1) with ((bcons true ∘ Pos.of_succ_nat) j).
  rewrite (lookup_kmap _).

  rewrite <- (length_vec_to_list v) at 1.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ j).
  replace (seq 0 n) with (seq 0 (length w)) by now rewrite length_vec_to_list.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ j).
  rewrite 2 option_fmap_id.
  assert (Hjv : j < length v) by now rewrite length_vec_to_list.
  assert (Hjw : j < length w) by now rewrite length_vec_to_list.
  rewrite <- lookup_lt_is_Some in Hjv, Hjw.
  destruct Hjv as [jv Hjv].
  destruct Hjw as [jw Hjw].
  rewrite Hjv, Hjw.
  cbn.
  apply eq_reflexivity.
  apply decide_ext.
  split; now intros [= ->].
Qed.


Lemma graph_semantics_swap {n m} :
  graph_semantics (SR:=SR) (@swap_graph T n m) ≡ swap_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics].
  unfold namedtensorlist_to_tensor.
  erewrite ntl_eq_correct; try first [
    now apply make_vecs_map_SummedElements|
    apply graph_namedtensorlist_semantics_WT|
    rewrite dom_make_vecs_map, 2 vec_to_list_map, 2 vec_to_list_seq;
    try apply graph_namedtensorlist_semantics_swap_graph].
  rewrite ntl_total_semantics_alt by now eapply ntl_eq_WF;
    [apply symmetry, graph_namedtensorlist_semantics_swap_graph|
    apply graph_namedtensorlist_semantics_WF].
  cbn -[deltas_semantics_alt].
  rewrite sum_of_Vmap_nil.
  rewrite rmul_1_l.
  unfold deltas_semantics_alt.
  rewrite <- Rlist_prod_vec_if_eq.
  rewrite fmap_app, <- 2 list_fmap_compose, Rlist_prod_app.
  rewrite seq_app, fmap_app, Rlist_prod_app.
  f_equiv.
  - apply Rlist_prod_ext.
    apply Forall2_fmap, Forall_Forall2_diag, Forall_seq.
    intros j [_ Hj].
    cbn.
    unfold make_vecs_map.
    rewrite 2 vec_to_list_zip_with, 2 vec_to_list_map, 2 vec_to_list_seq,
      2 zip_fmap_l, <- 2 (kmap_list_to_map _).
    rewrite 2 lookup_union.
    change ((Pos.of_succ_nat j)~0) with ((bcons false ∘ Pos.of_succ_nat) j).
    rewrite (lookup_kmap _).
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite (lookup_kmap_None (bcons true ∘ Pos.of_succ_nat) _
      ((bcons false ∘ Pos.of_succ_nat) j)).2 by now cbn; lia.
    rewrite (right_id_L None _), (left_id_L None _).
    change ((Pos.of_succ_nat (m + j))~1) with ((bcons true ∘ Pos.of_succ_nat) (m + j)%nat).
    rewrite (lookup_kmap _).

    rewrite <- (length_vec_to_list v) at 1.
    rewrite <- imap_to_zip_with_seq.
    rewrite (lookup_list_to_map_imap id id _ j).
    replace (seq 0 (m + n)) with (seq 0 (length w)) by now rewrite length_vec_to_list.
    rewrite <- imap_to_zip_with_seq.
    rewrite (lookup_list_to_map_imap id id _ (m + j)).
    rewrite 2 option_fmap_id.
    induction w as [wl wr] using vec_add_inv.
    rewrite vsplitr_app, vsplitl_app.
    rewrite 2 vec_to_list_app.
    rewrite lookup_app_r by now rewrite length_vec_to_list; lia.
    rewrite length_vec_to_list.
    replace (m + j - m)%nat with j by lia.
    rewrite lookup_app_l by now rewrite length_vec_to_list; lia.
    
    assert (Hjv : j < length v) by now rewrite length_vec_to_list; lia.
    assert (Hjw : j < length wr) by now rewrite length_vec_to_list.
    rewrite <- lookup_lt_is_Some in Hjv, Hjw.
    destruct Hjv as [jv Hjv].
    destruct Hjw as [jw Hjw].
    rewrite Hjv, Hjw.
    cbn.
    apply eq_reflexivity.
    apply decide_ext.
    split; now intros [= ->].
  - apply Rlist_prod_ext.
    replace (0 + n)%nat with (n + 0)%nat by lia.
    rewrite <- fmap_add_seq, <- list_fmap_compose.
    apply Forall2_fmap, Forall_Forall2_diag, Forall_seq.
    intros j [_ Hj].
    cbn.
    unfold make_vecs_map.
    rewrite 2 vec_to_list_zip_with, 2 vec_to_list_map, 2 vec_to_list_seq,
      2 zip_fmap_l, <- 2 (kmap_list_to_map _).
    rewrite 2 lookup_union.
    change ((Pos.of_succ_nat j)~1) with ((bcons true ∘ Pos.of_succ_nat) j).
    rewrite (lookup_kmap _).
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite (lookup_kmap_None (bcons true ∘ Pos.of_succ_nat) _
      ((bcons false ∘ Pos.of_succ_nat) (n + j)%nat)).2 by now cbn; lia.
    rewrite (right_id_L None _), (left_id_L None _).
    change ((Pos.of_succ_nat (n + j))~0) with ((bcons false ∘ Pos.of_succ_nat) (n + j)%nat).
    rewrite (lookup_kmap _).

    rewrite <- (length_vec_to_list v) at 1.
    rewrite <- imap_to_zip_with_seq.
    rewrite (lookup_list_to_map_imap id id _ (n + j)).
    replace (seq 0 (m + n)) with (seq 0 (length w)) by now rewrite length_vec_to_list.
    rewrite <- imap_to_zip_with_seq.
    rewrite (lookup_list_to_map_imap id id _ j).
    rewrite 2 option_fmap_id.
    induction w as [wl wr] using vec_add_inv.
    rewrite vsplitr_app, vsplitl_app.
    rewrite 2 vec_to_list_app.
    rewrite lookup_app_l by now rewrite length_vec_to_list; lia.
    rewrite lookup_app_r by now rewrite length_vec_to_list; lia.
    rewrite length_vec_to_list.
    replace (n + j - n)%nat with j by lia.
    
    
    assert (Hjv : n + j < length v) by now rewrite length_vec_to_list; lia.
    assert (Hjw : j < length wl) by now rewrite length_vec_to_list.
    rewrite <- lookup_lt_is_Some in Hjv, Hjw.
    destruct Hjv as [jv Hjv].
    destruct Hjw as [jw Hjw].
    rewrite Hjv, Hjw.
    cbn.
    apply eq_reflexivity.
    apply decide_ext.
    split; now intros [= ->].
Qed.


Lemma graph_semantics_cup {n} :
  graph_semantics (SR:=SR) (@cup_graph T n) ≡ cup_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics make_vecs_map vseq].
  unfold namedtensorlist_to_tensor.
  erewrite ntl_eq_correct; try first [
    now apply make_vecs_map_SummedElements|
    apply (graph_namedtensorlist_semantics_WT (n:=0))|
    rewrite dom_make_vecs_map, 2 vec_to_list_map, 2 vec_to_list_seq;
    try apply (graph_namedtensorlist_semantics_cup_graph n)].
  rewrite ntl_total_semantics_alt by now eapply ntl_eq_WF;
    [apply symmetry, graph_namedtensorlist_semantics_cup_graph|
    apply graph_namedtensorlist_semantics_WF].
  cbn -[deltas_semantics_alt].
  rewrite sum_of_Vmap_nil.
  rewrite rmul_1_l.
  unfold deltas_semantics_alt.
  rewrite <- list_fmap_compose.
  rewrite <- Rlist_prod_vec_if_eq.
  apply Rlist_prod_ext.
  apply Forall2_fmap, Forall_Forall2_diag, Forall_seq.
  intros j [_ Hj].
  cbn.
  induction v using vec_0_inv.
  induction w as [wl wr] using vec_add_inv.
  rewrite vsplitl_app, vsplitr_app.
  cbn.
  rewrite 2 map_empty_union.
  rewrite vec_to_list_zip_with, vec_to_list_map, vec_to_list_seq,
    zip_fmap_l, <- (kmap_list_to_map _).
  change ((Pos.of_succ_nat j)~1) with ((bcons true ∘ Pos.of_succ_nat) j).
  rewrite (lookup_kmap _).
  change ((Pos.of_succ_nat (n + j))~1) with ((bcons true ∘ Pos.of_succ_nat) (n + j)%nat).
  rewrite (lookup_kmap _).

  rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ j).
  replace (seq 0 (n + n)) with (seq 0 (length (wl +++ wr))) by 
    now rewrite length_vec_to_list.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ (n + j)).
  rewrite 2 option_fmap_id.
  rewrite vec_to_list_app.
  rewrite (lookup_app_l _ _ j) by now rewrite length_vec_to_list; lia.
  rewrite lookup_app_r by now rewrite length_vec_to_list; lia.
  rewrite length_vec_to_list.
  replace (n + j - n)%nat with j by lia.
  assert (Hjv : j < length wl) by now rewrite length_vec_to_list.
  assert (Hjw : j < length wr) by now rewrite length_vec_to_list.
  rewrite <- lookup_lt_is_Some in Hjv, Hjw.
  destruct Hjv as [jv Hjv].
  destruct Hjw as [jw Hjw].
  rewrite Hjv, Hjw.
  cbn.
  apply eq_reflexivity.
  apply decide_ext.
  split; now intros [= ->].
Qed.

Lemma graph_semantics_cap {n} :
  graph_semantics (SR:=SR) (@cap_graph T n) ≡ cap_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics make_vecs_map vseq].
  unfold namedtensorlist_to_tensor.
  erewrite ntl_eq_correct; try first [
    now apply make_vecs_map_SummedElements|
    apply (graph_namedtensorlist_semantics_WT (m:=0))|
    rewrite dom_make_vecs_map, 2 vec_to_list_map, 2 vec_to_list_seq;
    try apply (graph_namedtensorlist_semantics_cap_graph n)].
  rewrite ntl_total_semantics_alt by now eapply ntl_eq_WF;
    [apply symmetry, graph_namedtensorlist_semantics_cap_graph|
    apply graph_namedtensorlist_semantics_WF].
  cbn -[deltas_semantics_alt].
  rewrite sum_of_Vmap_nil.
  rewrite rmul_1_l.
  unfold deltas_semantics_alt.
  rewrite <- list_fmap_compose.
  rewrite <- Rlist_prod_vec_if_eq.
  apply Rlist_prod_ext.
  apply Forall2_fmap, Forall_Forall2_diag, Forall_seq.
  intros j [_ Hj].
  cbn.
  induction w using vec_0_inv.
  induction v as [wl wr] using vec_add_inv.
  rewrite vsplitl_app, vsplitr_app.
  cbn.
  unfold make_vecs_map.
  cbn.
  rewrite 2 map_union_empty.
  rewrite vec_to_list_zip_with, vec_to_list_map, vec_to_list_seq,
    zip_fmap_l, <- (kmap_list_to_map _).
  change ((Pos.of_succ_nat j)~0) with ((bcons false ∘ Pos.of_succ_nat) j).
  rewrite (lookup_kmap _).
  change ((Pos.of_succ_nat (n + j))~0) with ((bcons false ∘ Pos.of_succ_nat) (n + j)%nat).
  rewrite (lookup_kmap _).

  rewrite <- (length_vec_to_list (wl +++ wr)) at 1.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ j).
  replace (seq 0 (n + n)) with (seq 0 (length (wl +++ wr))) by 
    now rewrite length_vec_to_list.
  rewrite <- imap_to_zip_with_seq.
  rewrite (lookup_list_to_map_imap id id _ (n + j)).
  rewrite 2 option_fmap_id.
  rewrite vec_to_list_app.
  rewrite (lookup_app_l _ _ j) by now rewrite length_vec_to_list; lia.
  rewrite lookup_app_r by now rewrite length_vec_to_list; lia.
  rewrite length_vec_to_list.
  replace (n + j - n)%nat with j by lia.
  assert (Hjv : j < length wl) by now rewrite length_vec_to_list.
  assert (Hjw : j < length wr) by now rewrite length_vec_to_list.
  rewrite <- lookup_lt_is_Some in Hjv, Hjw.
  destruct Hjv as [jv Hjv].
  destruct Hjw as [jw Hjw].
  rewrite Hjv, Hjw.
  cbn.
  apply eq_reflexivity.
  apply decide_ext.
  split; now intros [= ->].
Qed.

Lemma graph_semantics_swap_1_1 :
  graph_semantics (SR:=SR) (@swap_graph T 1 1) ≡ swap_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics make_vecs_map].
  unfold namedtensorlist_to_tensor.
  etransitivity; [apply ntl_eq_correct; [now apply make_vecs_map_SummedElements|
    refine (graph_namedtensorlist_semantics_WT _ _ _)|
    apply ntl_eq_of_ntl_delta_eq;
    symmetry; apply simplify_ntl_deltas_correct;
    refine (graph_namedtensorlist_semantics_WT _ _ _)]|].
  evar (sem : namedtensorlist).
  replace (simplify_ntl_deltas _) with sem by (vm_compute; reflexivity).
  subst sem.
  unfold Pos.succ;
  cbn -[ntl_total_semantics make_vecs_map].
  cbn in v, w.
  induction v as [v1 v] using vec_S_inv.
  induction v as [v2 v] using vec_S_inv.
  induction v using vec_0_inv.
  induction w as [w1 w] using vec_S_inv.
  induction w as [w2 w] using vec_S_inv.
  induction w using vec_0_inv.
  cbn.
  change (_ !! 5%positive) with (Some w2).
  change (_ !! 2%positive) with (Some v1).
  change (_ !! 3%positive) with (Some w1).
  change (_ !! 4%positive) with (Some v2).
  cbn.
  symmetry.
  case_decide as Heq; [revert Heq; intros [= -> ->]; now rewrite 2 decide_True by done; ring|].
  do 2 case_decide; [|ring..].
  congruence.
Qed.

Lemma graph_semantics_cup_1_1 :
  graph_semantics (SR:=SR) (@cup_graph T 1) ≡ cup_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics make_vecs_map].
  etransitivity; [apply ntl_eq_correct; [now apply make_vecs_map_SummedElements|
    refine (graph_namedtensorlist_semantics_WT _ _ _)|
    apply ntl_eq_of_ntl_delta_eq;
    symmetry; apply simplify_ntl_deltas_correct;
    refine (graph_namedtensorlist_semantics_WT _ _ _)]|].
  evar (sem : namedtensorlist).
  replace (simplify_ntl_deltas _) with sem by (vm_compute; reflexivity).
  subst sem.
  unfold Pos.succ;
  cbn -[ntl_total_semantics make_vecs_map].
  cbn in v, w.
  induction v using vec_0_inv.
  induction w as [w1 w] using vec_S_inv.
  induction w as [w2 w] using vec_S_inv.
  induction w using vec_0_inv.
  cbn.
  change (_ !! 5%positive) with (Some w2).
  change (_ !! 3%positive) with (Some w1).
  cbn.
  rewrite rmul_1_l, rmul_1_r.
  apply eq_reflexivity, decide_ext.
  done.
Qed.

Lemma graph_semantics_cap_1_1 :
  graph_semantics (SR:=SR) (@cap_graph T 1) ≡ cap_tensor.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics make_vecs_map].
  etransitivity; [apply ntl_eq_correct; [now apply make_vecs_map_SummedElements|
    refine (graph_namedtensorlist_semantics_WT _ _ _)|
    apply ntl_eq_of_ntl_delta_eq;
    symmetry; apply simplify_ntl_deltas_correct;
    refine (graph_namedtensorlist_semantics_WT _ _ _)]|].
  evar (sem : namedtensorlist).
  replace (simplify_ntl_deltas _) with sem by (vm_compute; reflexivity).
  subst sem.
  unfold Pos.succ;
  cbn -[ntl_total_semantics make_vecs_map].
  cbn in v, w.
  induction v as [v1 v] using vec_S_inv.
  induction v as [v2 v] using vec_S_inv.
  induction v using vec_0_inv.
  induction w using vec_0_inv.
  cbn.
  change (_ !! 2%positive) with (Some v1).
  change (_ !! 4%positive) with (Some v2).
  cbn.
  rewrite rmul_1_l, rmul_1_r.
  apply eq_reflexivity, decide_ext.
  done.
Qed.

Lemma graph_semantics_graph_of_tensor (t : T) n m :
  graph_semantics (SR:=SR) (graph_of_tensor t n m) ≡ interpretTensor t n m.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics insert].
  rewrite hyperedges_singleton.
  unfold namedtensorlist_to_tensor.
  etransitivity; [apply ntl_eq_correct; [now apply make_vecs_map_SummedElements|
    refine (graph_namedtensorlist_semantics_WT _ _ _)|
    rewrite dom_make_vecs_map, 2 vec_to_list_map, 2 vec_to_list_seq;
    apply graph_namedtensorlist_semantics_graph_of_tensor]|].

  cbn.
  rewrite 2 rmul_1_r.
  unfold abstract_semantics.
  change (_ !! xH) with (Some (interpretTensor t)).
  replace (join_list (fmap _ (fmap _ (fmap _ (seq 0 n))))) with (Some (vec_to_list v));
  [replace (join_list _) with (Some (vec_to_list w))|].
  - cbn.
    unfold Vapplys.
    rewrite 2 list_to_vec_to_list.
    case (eq_sym (length_vec_to_list v)).
    case (eq_sym (length_vec_to_list w)).
    done.
  - symmetry.
    apply join_list_Some.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 4 length_fmap, length_seq, length_vec_to_list|].
    rewrite length_fmap, length_vec_to_list.
    intros i x y Him.
    rewrite 4 list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    destruct ((vec_to_list w) !! i) as [wi|] eqn:Hwi; [|done].
    cbn.
    intros [= <-] [= <-].
    apply vlookup_lookup' in Hwi as Hwi'.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite 2 vec_to_list_zip_with, 2 vec_to_list_map, 2 zip_fmap_l,
      <- 2 (kmap_list_to_map _).
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite (left_id_L None union).
    change (_~1) with ((bcons true ∘ Pos.of_succ_nat) i).
    rewrite (lookup_kmap _).
    rewrite vec_to_list_seq.
    apply elem_of_list_to_map;
    [rewrite fst_zip by (now rewrite length_vec_to_list, length_seq);
      apply NoDup_seq|].
    apply elem_of_list_lookup.
    exists i.
    rewrite lookup_zip_with.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite Hwi.
    done.
  - symmetry.
    apply join_list_Some.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 4 length_fmap, length_seq, length_vec_to_list|].
    rewrite length_fmap, length_vec_to_list.
    intros i x y Him.
    rewrite 4 list_lookup_fmap.
    rewrite lookup_seq_lt by done.
    cbn.
    destruct ((vec_to_list v) !! i) as [vi|] eqn:Hvi; [|done].
    cbn.
    intros [= <-] [= <-].
    apply vlookup_lookup' in Hvi as Hvi'.
    unfold make_vecs_map.
    rewrite lookup_union.
    rewrite 2 vec_to_list_zip_with, 2 vec_to_list_map, 2 zip_fmap_l,
      <- 2 (kmap_list_to_map _).
    change (_~0) with ((bcons false ∘ Pos.of_succ_nat) i).
    rewrite (lookup_kmap _).
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite (right_id_L None union).
    rewrite vec_to_list_seq.
    apply elem_of_list_to_map;
    [rewrite fst_zip by (now rewrite length_vec_to_list, length_seq);
      apply NoDup_seq|].
    apply elem_of_list_lookup.
    exists i.
    rewrite lookup_zip_with.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite Hvi.
    done.
Qed.


Lemma graph_semantics_cohg_eq {n m} (cohg cohg' : TensorGraph n m) :
  cohg_eq cohg cohg' ->
  graph_semantics (SR:=SR) cohg ≡ graph_semantics cohg'.
Proof.
  intros Heq.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics].

  rewrite 2 ntl_total_semantics_alt by apply graph_namedtensorlist_semantics_WF.
  cbn -[abstracts_semantics_alt deltas_semantics_alt].
  apply vertices_cohg_eq in Heq as Heqv.
  rewrite <- Heqv.
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  rewrite <- Heq.1, <- Heq.2.1.
  f_equiv.
  pose proof Heq.2.2.1 as Hequ%map_to_list_equiv.
  unfold tg_abstracts.
  induction Hequ as [|k_tio k_tio' ? ? Hktio Heqls IHHequ]; [done|].
  cbn -[abstracts_semantics_alt].
  rewrite 2 abstracts_semantics_alt_cons.
  f_equiv; [|apply IHHequ].
  clear IHHequ.
  cbn -[abstract_semantics_alt].
  destruct Hktio as (Hk & [[Ht Hi] Ho]).
  rewrite <- Hi, <- Ho.
  apply abstract_semantics_alt_ext_tens.
  - pose proof Heq.2.2.1 as Hequ.
    unfold graph_mabs.
    rewrite 2 lookup_fmap.
    rewrite <- Hk.
    specialize (Hequ k_tio.1).
    induction Hequ as [t t' Htt'|]; [cbn|done].
    constructor.
    apply interpretTensorProper, Htt'.
  - eapply map_Forall_impl; [apply Hmr.2|].
    cbn.
    intros ? ?; apply SummedElement_iff.
  - now apply make_vecs_map_SummedElements.
Qed.


Lemma graph_semantics_equiv {n m} (cohg cohg' : TensorGraph n m) :
  cohg ≡ cohg' ->
  graph_semantics (SR:=SR) cohg ≡ graph_semantics cohg'.
Proof.
  intros Heq.
  induction Heq as [|cohg cohg' cohg'' Heq Heqs IH]; [done|].
  rewrite <- IH.
  destruct Heq.
  - now apply graph_semantics_cohg_eq.
  - now apply cohg_vert_eq_semantic_eq.
Qed.

Lemma graph_semantics_syntactic_eq {n m} (cohg cohg' : TensorGraph n m) :
  cohg ≡ₛ cohg' ->
  graph_semantics (SR:=SR) cohg ≡ graph_semantics cohg'.
Proof.
  intros Heq%(relation_equiv_iff.1 cohg_syntactic_eq_alt).
  induction Heq as [|cohg cohg' cohg'' Heq Heqs IH]; [done|].
  rewrite <- IH.
  destruct Heq as [[Hheq | Hiso] | Hveq].
  - now apply graph_semantics_cohg_eq.
  - now apply graph_semantics_isomorphic.
  - now apply cohg_vert_eq_semantic_eq.
Qed.

#[export] Instance cohg_syntactic_eq_semantic_eq {n m} : 
  subrelation (@cohg_syntactic_eq T _ n m) cohg_semantic_eq.
Proof.
  refine graph_semantics_syntactic_eq.
Qed.

#[export] Instance cohg_eq_semantic_eq {n m} : 
  subrelation (@cohg_eq T n m _) cohg_semantic_eq.
Proof.
  rewrite <- cohg_syntactic_eq_semantic_eq.
  apply _.
Qed.

#[export] Instance isomorphic_semantic_eq {n m} : 
  subrelation (@isomorphic T n m) cohg_semantic_eq.
Proof.
  rewrite <- cohg_syntactic_eq_semantic_eq.
  apply _.
Qed.

(* FIXME: Move *)
#[export] Instance struct_isomorphic_syntactic_eq {n m} : 
  subrelation (@struct_isomorphic T n m) cohg_syntactic_eq.
Proof.
  intros x y Heq.
  hnf in Heq.
  rewrite <- (norm_verts_vert_eq x), Heq.
  apply (subrel (norm_verts_vert_eq y)).
Qed.

#[export] Instance struct_isomorphic_semantic_eq {n m} : 
  subrelation (@struct_isomorphic T n m) cohg_semantic_eq.
Proof.
  rewrite <- cohg_syntactic_eq_semantic_eq.
  apply _.
Qed.

#[export] Instance compose_graphs_semantic_eq {n m o} : 
  Proper (cohg_semantic_eq ==> cohg_semantic_eq ==> cohg_semantic_eq)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold cohg_semantic_eq.
  rewrite 2 graph_semantics_compose_graphs.
  now apply compose_tensor_mor.
Qed.

#[export] Instance stack_graphs_semantic_eq {n1 m1 n2 m2} : 
  Proper (cohg_semantic_eq ==> cohg_semantic_eq ==> cohg_semantic_eq)
    (@stack_graphs T n1 m1 n2 m2).
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold cohg_semantic_eq.
  rewrite 2 graph_semantics_stack_graphs.
  now apply stack_tensor_mor.
Qed.

End TensorGraphFacts.

