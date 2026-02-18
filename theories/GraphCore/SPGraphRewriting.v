From stdpp Require Export gmultiset pmap gmap decidable.
Require Import SPTensorGraph.
Require Import SPHyperGraph.
Require Import TESyntax.
Require Import Aux_pos.


(* An implementation of double pushout (DPO) rewriting *)


Local Open Scope nat_scope.

Section DPO.

  Context {T : Type}.


  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_spgraphs_aux {n m o} (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) : CospanSPHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(spoutputs)) (tgr.(spinputs))) in
    relabel_spgraph (subst_by_vec connected_substs)
      (tgl.(spinputs) ->
        sphg_add_vertices (tgl.(sphedges) ∪ tgr.(sphedges)) (list_to_set tgr.(spinputs))
          <- tgr.(spoutputs)).

  Definition compose_spgraphs {n m o} (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) : CospanSPHyperGraph T n o :=
    let connected_substs :=
        propogate_subst (vzip (vmap (bcons false) tgl.(spoutputs)) (vmap (bcons true) tgr.(spinputs))) in
     relabel_spgraph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(spinputs)) ->
      sphg_add_vertices (tgl.(sphedges) ⊎ tgr.(sphedges)) (list_to_set (vmap (bcons true) tgr.(spinputs))) <- (vmap (bcons true) tgr.(spoutputs))).


  Definition compose_spgraphs_unsafe {n m o} (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) : CospanSPHyperGraph T n o :=
    tgl.(spinputs) ->  sphg_add_vertices (tgl.(sphedges) ∪ tgr.(sphedges)) (list_to_set (tgr.(spinputs))) <- tgr.(spoutputs).

Lemma compose_spgraphs_to_compose_spgraphs_aux {n m o}
  (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) :
  compose_spgraphs tgl tgr = compose_spgraphs_aux
    (reindex_spgraph (bcons false) (relabel_spgraph (bcons false) tgl))
    (reindex_spgraph (bcons true) (relabel_spgraph (bcons true) tgr)).
Proof.
  reflexivity.
Qed.


Lemma compose_spgraphs_aux_to_compose_spgraphs_unsafe {n m o} (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) :
  tgl.(spoutputs) = tgr.(spinputs) ->
  compose_spgraphs_aux tgl tgr = compose_spgraphs_unsafe tgl tgr.
Proof.
  intros.
  unfold compose_spgraphs_aux.
  rewrite H.
  unfold relabel_spgraph.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite relabel_sphg_id'.
  reflexivity.
  all: apply subst_by_vec_id.
Qed.


Lemma relabel_sphg_union f (sphg sphg' : SPHyperGraph T) :
  relabel_sphg f (sphg ∪ sphg') =
  relabel_sphg f sphg ∪ relabel_sphg f sphg'.
Proof.
  apply sphg_ext; cbn.
  - now rewrite map_fmap_union.
  - now rewrite set_map_union_L.
Qed.

Lemma reindex_sphg_union f `{Hf : !Inj eq eq f} (sphg sphg' : SPHyperGraph T) :
  reindex_sphg f (sphg ∪ sphg') =
  reindex_sphg f sphg ∪ reindex_sphg f sphg'.
Proof.
  apply sphg_ext; cbn.
  - apply (kmap_union _).
  - done.
Qed.



Lemma spinputs_spadd_top_loops {n m m'}
  (tg : CospanSPHyperGraph T (n + m) (n + m')) :
  (spadd_top_loops tg).(spinputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(spoutputs))
      (vsplitl tg.(spinputs)))))
      (vsplitr tg.(spinputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [spadd_top_loops].
  rewrite IHn.
  destruct tg as [sphg ins outs].
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


Lemma spoutputs_spadd_top_loops {n m m'}
  (tg : CospanSPHyperGraph T (n + m) (n + m')) :
  (spadd_top_loops tg).(spoutputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(spoutputs))
      (vsplitl tg.(spinputs)))))
      (vsplitr tg.(spoutputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [spadd_top_loops].
  rewrite IHn.
  destruct tg as [sphg ins outs].
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

Lemma sphg_add_vertices_empty (sphg : SPHyperGraph T) :
  sphg_add_vertices sphg ∅ = sphg.
Proof.
  apply sphg_ext; [done|].
  cbn -[union].
  apply union_empty_l_L.
Qed.

Lemma sphg_add_vertices_union (sphg : SPHyperGraph T) vs vs' :
  sphg_add_vertices (sphg_add_vertices sphg vs) vs' =
  sphg_add_vertices sphg (vs ∪ vs').
Proof.
  apply sphg_ext; [done|].
  cbn -[union].
  rewrite (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

Lemma relabel_sphg_add_vertices f (sphg : SPHyperGraph T) vs :
  relabel_sphg f (sphg_add_vertices sphg vs) =
  sphg_add_vertices (relabel_sphg f sphg) (set_map f vs).
Proof.
  apply sphg_ext; [done|].
  cbn.
  now rewrite set_map_union_L.
Qed.


Lemma sphedges_spadd_top_loops {n m m'}
  (tg : CospanSPHyperGraph T (n + m) (n + m')) :
  (spadd_top_loops tg).(sphedges) =
  relabel_sphg (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(spoutputs))
      (vsplitl tg.(spinputs)))))
      (sphg_add_vertices tg.(sphedges)
      (list_to_set (vsplitl tg.(spinputs)))).
Proof.
  induction n; [cbn; now rewrite relabel_sphg_id, sphg_add_vertices_empty|].
  cbn [spadd_top_loops].
  rewrite IHn.
  destruct tg as [sphg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append union].
  rewrite 2 vsplitl_app.
  cbn -[union].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite 4 relabel_sphg_add_vertices, sphg_add_vertices_union.
  f_equal.
  - rewrite relabel_sphg_compose.
    apply relabel_sphg_ext.
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

Lemma spadd_top_loops_alt {n m m'}
  (tg : CospanSPHyperGraph T (n + m) (n + m')) :
  spadd_top_loops tg =
  relabel_spgraph (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(spoutputs))
      (vsplitl tg.(spinputs)))))
    (vsplitr tg.(spinputs) ->
      sphg_add_vertices tg.(sphedges) (list_to_set (vsplitl tg.(spinputs)))
      <- vsplitr tg.(spoutputs)).
Proof.
  apply cosphg_ext.
  - apply sphedges_spadd_top_loops.
  - apply spinputs_spadd_top_loops.
  - apply spoutputs_spadd_top_loops.
Qed.



Lemma compose_spgraphs_aux_spgraphs_alt_aux_correct {n m o}
  (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) :
  spadd_top_loops (swapped_stack_spgraphs_aux tgl tgr) =
    compose_spgraphs_aux tgl tgr.
Proof.
  rewrite spadd_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  reflexivity.
Qed.

Lemma compose_spgraphs_aux_spgraphs_alt_correct {n m o}
  (tgl : CospanSPHyperGraph T n m) (tgr : CospanSPHyperGraph T m o) :
  spadd_top_loops (swapped_stack_spgraphs tgl tgr) =
    compose_spgraphs tgl tgr.
Proof.
  rewrite spadd_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  rewrite <- 2 reindex_relabel_sphg.
  done.
Qed.


Lemma relabel_stack_spgraphs_aux {n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') f :
  relabel_spgraph f (stack_spgraphs_aux cosphg cosphg') =
  stack_spgraphs_aux (relabel_spgraph f cosphg) (relabel_spgraph f cosphg').
Proof.
  apply cosphg_ext.
  - cbn; apply relabel_sphg_union.
  - cbn.
    now rewrite Vector.map_append.
  - cbn.
    now rewrite Vector.map_append.
Qed.


Lemma stack_spgraphs_relabel {n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') ft fb :
  stack_spgraphs (relabel_spgraph ft cosphg) (relabel_spgraph fb cosphg') =
  relabel_spgraph (pos_map ft fb) (stack_spgraphs cosphg cosphg').
Proof.
  unfold stack_spgraphs.
  rewrite relabel_stack_spgraphs_aux.
  rewrite 2 reindex_relabel_spgraph, 4 relabel_spgraph_compose.
  done.
Qed.

Lemma reindex_stack_spgraphs_aux {n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') f `{Hf : !Inj eq eq f} :
  reindex_spgraph f (stack_spgraphs_aux cosphg cosphg') =
  stack_spgraphs_aux (reindex_spgraph f cosphg) (reindex_spgraph f cosphg').
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  apply (reindex_sphg_union _).
Qed.

Lemma stack_spgraphs_reindex {n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') ft fb 
  `{Hft : !Inj eq eq ft, Hfb : !Inj eq eq fb} :
  stack_spgraphs (reindex_spgraph ft cosphg) (reindex_spgraph fb cosphg') =
  reindex_spgraph (pos_map ft fb) (stack_spgraphs cosphg cosphg').
Proof.
  unfold stack_spgraphs.
  rewrite (reindex_stack_spgraphs_aux _ _ _).
  rewrite 2 reindex_relabel_spgraph, 4 (reindex_spgraph_compose _ _).
  done.
Qed.

Lemma stack_spgraphs_spisomorphic {n m n' m'} (cosphg1 cosphg1' : CospanSPHyperGraph T n m)
  (cosphg2 cosphg2' : CospanSPHyperGraph T n' m') : 
  spisomorphic cosphg1 cosphg1' -> spisomorphic cosphg2 cosphg2' ->
  spisomorphic (stack_spgraphs cosphg1 cosphg2) (stack_spgraphs cosphg1' cosphg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%spisomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%spisomorphic_exists.
  rewrite stack_spgraphs_relabel, (stack_spgraphs_reindex _ _ _ _).
  apply (spiso_relabel_reindex _ _ _).
Qed.





End DPO.


Add Parametric Morphism {T n m n' m'} : (@stack_spgraphs T n m n' m') with signature 
  spisomorphic ==> spisomorphic ==> spisomorphic as stack_spgraphs_spisomorphic_mor.
Proof.
  intros; now apply stack_spgraphs_spisomorphic.
Qed.
  