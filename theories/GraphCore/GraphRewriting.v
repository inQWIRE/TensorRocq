From stdpp Require Export pmap gmap decidable.
Require Import TensorGraph.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.



(* An implementation of double pushout (DPO) rewriting *)


Local Open Scope nat_scope.

Section DPO.

  Context {T : Type}.

  Definition compose_graphs_aux {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs)
      (tgl.(inputs) ->
        hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set tgr.(inputs))
          <- tgr.(outputs)).

  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_graphs {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs :=
        propogate_subst (vzip (vmap (bcons false) tgl.(outputs)) (vmap (bcons true) tgr.(inputs))) in
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) ->
      hg_add_vertices (tgl.(hedges) ⊎ tgr.(hedges)) (list_to_set (vmap (bcons true) tgr.(inputs))) <- (vmap (bcons true) tgr.(outputs))).


  Definition compose_graphs_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set (tgr.(inputs))) <- tgr.(outputs).

Lemma compose_graphs_to_compose_graphs_aux {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  compose_graphs tgl tgr = compose_graphs_aux
    (reindex_graph (bcons false) (relabel_graph (bcons false) tgl))
    (reindex_graph (bcons true) (relabel_graph (bcons true) tgr)).
Proof.
  reflexivity.
Qed.


Lemma compose_graphs_aux_to_compose_graphs_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  compose_graphs_aux tgl tgr = compose_graphs_unsafe tgl tgr.
Proof.
  intros.
  unfold compose_graphs_aux.
  rewrite H.
  unfold relabel_graph.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite relabel_hg_id'.
  reflexivity.
  all: apply subst_by_vec_id.
Qed.


Lemma relabel_hg_union f (hg hg' : HyperGraph T) :
  relabel_hg f (hg ∪ hg') =
  relabel_hg f hg ∪ relabel_hg f hg'.
Proof.
  apply hg_ext; cbn.
  - now rewrite map_fmap_union.
  - now rewrite set_map_union_L.
Qed.

Lemma reindex_hg_union f `{Hf : !Inj eq eq f} (hg hg' : HyperGraph T) :
  reindex_hg f (hg ∪ hg') =
  reindex_hg f hg ∪ reindex_hg f hg'.
Proof.
  apply hg_ext; cbn.
  - apply (kmap_union _).
  - done.
Qed.



Lemma inputs_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(inputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (vsplitr tg.(inputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append].
  rewrite 2 vsplitl_app, vsplitr_app.
  cbn.
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite vsplitr_map, vsplitr_app.
  rewrite Vector.map_map.
  apply Vector.map_ext.
  intros p.
  apply susbt_by_vec_propogate_helper.
Qed.


Lemma outputs_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(outputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (vsplitr tg.(outputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append].
  rewrite 2 vsplitl_app, vsplitr_app.
  cbn.
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite vsplitr_map, vsplitr_app.
  rewrite Vector.map_map.
  apply Vector.map_ext.
  intros p.
  apply susbt_by_vec_propogate_helper.
Qed.

Lemma hg_add_vertices_empty (hg : HyperGraph T) :
  hg_add_vertices hg ∅ = hg.
Proof.
  apply hg_ext; [done|].
  cbn -[union].
  apply union_empty_l_L.
Qed.

Lemma hg_add_vertices_union (hg : HyperGraph T) vs vs' :
  hg_add_vertices (hg_add_vertices hg vs) vs' =
  hg_add_vertices hg (vs ∪ vs').
Proof.
  apply hg_ext; [done|].
  cbn -[union].
  rewrite (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

Lemma relabel_hg_add_vertices f (hg : HyperGraph T) vs :
  relabel_hg f (hg_add_vertices hg vs) =
  hg_add_vertices (relabel_hg f hg) (set_map f vs).
Proof.
  apply hg_ext; [done|].
  cbn.
  now rewrite set_map_union_L.
Qed.


Lemma hedges_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(hedges) =
  relabel_hg (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (hg_add_vertices tg.(hedges)
      (list_to_set (vsplitl tg.(inputs)))).
Proof.
  induction n; [cbn; now rewrite relabel_hg_id, hg_add_vertices_empty|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append union].
  rewrite 2 vsplitl_app.
  cbn -[union].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite 4 relabel_hg_add_vertices, hg_add_vertices_union.
  f_equal.
  - rewrite relabel_hg_compose.
    apply relabel_hg_ext.
    intros p; cbn.
    now rewrite susbt_by_vec_propogate_helper.
  - rewrite <- set_map_union_L.
    rewrite vec_to_list_map, <- (set_map_list_to_set_L (SA:=Pset)).
    rewrite <- set_map_union_L.
    rewrite set_map_compose_L.
    apply set_map_ext_L.
    intros ? _.
    cbn.
    apply susbt_by_vec_propogate_helper.
Qed.

Lemma add_top_loops_alt {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  add_top_loops tg =
  relabel_graph (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
    (vsplitr tg.(inputs) ->
      hg_add_vertices tg.(hedges) (list_to_set (vsplitl tg.(inputs)))
      <- vsplitr tg.(outputs)).
Proof.
  apply cohg_ext.
  - apply hedges_add_top_loops.
  - apply inputs_add_top_loops.
  - apply outputs_add_top_loops.
Qed.



Lemma compose_graphs_alt_aux_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs_aux tgl tgr) =
    compose_graphs_aux tgl tgr.
Proof.
  rewrite add_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  reflexivity.
Qed.

Lemma compose_graphs_alt_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs tgl tgr) =
    compose_graphs tgl tgr.
Proof.
  rewrite add_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  rewrite <- 2 reindex_relabel_hg.
  done.
Qed.


Lemma relabel_stack_graphs_aux {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') f :
  relabel_graph f (stack_graphs_aux cohg cohg') =
  stack_graphs_aux (relabel_graph f cohg) (relabel_graph f cohg').
Proof.
  apply cohg_ext.
  - cbn; apply relabel_hg_union.
  - cbn.
    now rewrite Vector.map_append.
  - cbn.
    now rewrite Vector.map_append.
Qed.


Lemma stack_graphs_relabel {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') ft fb :
  stack_graphs (relabel_graph ft cohg) (relabel_graph fb cohg') =
  relabel_graph (pos_map ft fb) (stack_graphs cohg cohg').
Proof.
  unfold stack_graphs.
  rewrite relabel_stack_graphs_aux.
  rewrite 2 reindex_relabel_graph, 4 relabel_graph_compose.
  done.
Qed.

Lemma reindex_stack_graphs_aux {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') f `{Hf : !Inj eq eq f} :
  reindex_graph f (stack_graphs_aux cohg cohg') =
  stack_graphs_aux (reindex_graph f cohg) (reindex_graph f cohg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  apply (reindex_hg_union _).
Qed.

Lemma stack_graphs_reindex {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') ft fb 
  `{Hft : !Inj eq eq ft, Hfb : !Inj eq eq fb} :
  stack_graphs (reindex_graph ft cohg) (reindex_graph fb cohg') =
  reindex_graph (pos_map ft fb) (stack_graphs cohg cohg').
Proof.
  unfold stack_graphs.
  rewrite (reindex_stack_graphs_aux _ _ _).
  rewrite 2 reindex_relabel_graph, 4 (reindex_graph_compose _ _).
  done.
Qed.

Lemma stack_graphs_isomorphic {n m n' m'} (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') : 
  isomorphic cohg1 cohg1' -> isomorphic cohg2 cohg2' ->
  isomorphic (stack_graphs cohg1 cohg2) (stack_graphs cohg1' cohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%isomorphic_exists.
  rewrite stack_graphs_relabel, (stack_graphs_reindex _ _ _ _).
  apply (iso_relabel_reindex _ _ _).
Qed.



Section Paths.

  Context (H : HyperGraph T).

  Definition successor (h h' : HyperEdge T) :=
    exists p, In p (h.1.2) /\ In p (h'.2).

  Definition predecessor (h h' : HyperEdge T) :=
    exists p, In p (h'.1.2) /\ In p (h.2).

  Lemma succ_pred_symm (h h' : HyperEdge T) :
    successor h h' <-> predecessor h' h.
  Proof.
    split;
      intros [x []];
      exists x;
      auto.
  Qed.

  Definition path (h h' : HyperEdge T) : Prop :=
    (tc successor) h h'.

  Definition pred_path (h h' : HyperEdge T) :=
    (tc predecessor) h h'.

  (* Definition path_pred_path_symm (h h' : HyperEdge T) :
    path h h' <-> pred_path h' h.
  Proof.
    split.
    intros.
    - induction H0.
      + apply tc_once.
        now rewrite succ_pred_symm in H0.
      +
        rewrite IHtc.
    - intros [x y | x y].
      +  *)


End Paths.

Definition decompose_left {n m} (G : CospanHyperGraph T n m) (L : HyperGraph T) : CospanHyperGraph T n m :=
  G.(inputs) -> {|
    hyperedges := ∅;
    hypervertices := ∅
  |} <- G.(outputs).


End DPO.


Add Parametric Morphism {T n m n' m'} : (@stack_graphs T n m n' m') with signature 
  isomorphic ==> isomorphic ==> isomorphic as stack_graphs_isomorphic_mor.
Proof.
  intros; now apply stack_graphs_isomorphic.
Qed.



Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs_aux T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_aux_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hin1 & Hout1 & He1)
    cohg2 cohg2' (Hin2 & Hout2 & He2).
  unfold compose_graphs_aux.
  rewrite <- Hin1, <- Hout1, <- Hin2, <- Hout2.
  f_equiv.
  apply mk_cohg_eq; [done..|].
  cbn.
  now do 2 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_cohg_eq.
Proof.
  intros cohg1 cohg1' Heq1
    cohg2 cohg2' Heq2.
  rewrite 2 compose_graphs_to_compose_graphs_aux.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs_unsafe T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_unsafe_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hin1 & Hout1 & He1)
    cohg2 cohg2' (Hin2 & Hout2 & He2).
  unfold compose_graphs_unsafe.
  rewrite <- Hin1, <- Hin2, <- Hout2.
  apply mk_cohg_eq; [done..|].
  cbn.
  now do 2 f_equiv.
Qed.