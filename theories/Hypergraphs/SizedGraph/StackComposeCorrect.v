From stdpp Require Export pmap gmap decidable.
From TensorRocq Require Import SizedGraph.Definitions HyperGraph Aux_pos Syntax Aux_stdpp.


Section StackCompose.


  Context {N T : Type}.

Lemma relabel_stack_sized_graphs_aux {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') f {Hf : Inj eq eq f} :
  relabel_sized_graph f (stack_sized_graphs_aux scohg scohg') =
  stack_sized_graphs_aux (relabel_sized_graph f scohg) (relabel_sized_graph f scohg').
Proof.
  apply scohg_ext; [apply relabel_stack_graphs_aux|].
  cbn.
  rewrite (kmap_union f); done.
Qed.


Lemma stack_sized_graphs_relabel {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') ft fb {Hft : Inj eq eq ft} {Hfb : Inj eq eq fb} :
  stack_sized_graphs (relabel_sized_graph ft scohg) (relabel_sized_graph fb scohg') =
  relabel_sized_graph (pos_map ft fb) (stack_sized_graphs scohg scohg').
Proof.
  unfold stack_sized_graphs.
  rewrite relabel_stack_sized_graphs_aux by apply _.
  rewrite 2 reindex_relabel_sized_graph, 4 relabel_sized_graph_compose by apply _.
  done.
Qed.

Lemma reindex_stack_sized_graphs_aux {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') f `{Hf : !Inj eq eq f} :
  reindex_sized_graph f (stack_sized_graphs_aux scohg scohg') =
  stack_sized_graphs_aux (reindex_sized_graph f scohg) (reindex_sized_graph f scohg').
Proof.
  apply scohg_ext; [|done..].
  now apply reindex_stack_graphs_aux.
Qed.

Lemma stack_sized_graphs_reindex {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') ft fb
  `{Hft : !Inj eq eq ft, Hfb : !Inj eq eq fb} :
  stack_sized_graphs (reindex_sized_graph ft scohg) (reindex_sized_graph fb scohg') =
  reindex_sized_graph (pos_map ft fb) (stack_sized_graphs scohg scohg').
Proof.
  unfold stack_sized_graphs.
  rewrite (reindex_stack_sized_graphs_aux _ _ _).
  rewrite 2 reindex_relabel_sized_graph, 4 (reindex_sized_graph_compose _ _).
  done.
Qed.

#[export] Instance stack_sized_graphs_sized_isomorphic {n m n' m'} :
  Proper (sized_isomorphic ==> sized_isomorphic ==> sized_isomorphic)
    (@stack_sized_graphs N T n m n' m').
Proof.
  intros scohg1 scohg1' (fv1 & fe1 & Hfv1 & Hfe1 & ->)%sized_isomorphic_exists
    scohg2 scohg2' (fv2 & fe2 & Hfv2 & Hfe2 & ->)%sized_isomorphic_exists.
  rewrite stack_sized_graphs_relabel, (stack_sized_graphs_reindex _ _ _ _) by apply _.
  apply (sized_iso_relabel_reindex _ _ _).
Qed.

(* FIXME: Move *)

#[export] Instance stack_graphs_cohg_vert_eq_Proper {n m n' m'} :
  Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@stack_graphs T n m n' m').
Proof.
  intros scohg1 scohg1' Heq1 scohg2 scohg2' Heq2.
  unfold cohg_vert_eq in *.
  rewrite 2 norm_verts_stack_graphs.
  now f_equal.
Qed.

#[export] Instance swapped_stack_graphs_cohg_vert_eq_Proper {n m n' m'} :
  Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@swapped_stack_graphs T n m n' m').
Proof.
  intros scohg1 scohg1' Heq1 scohg2 scohg2' Heq2.
  unfold cohg_vert_eq in *.
  rewrite 2 norm_verts_swapped_stack_graphs.
  now f_equal.
Qed.


#[export] Instance stack_sized_graphs_scohg_vert_eq_Proper {n m n' m'} :
  Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq)
    (@stack_sized_graphs N T n m n' m').
Proof.
  intros scohg1 scohg1' Heq1 scohg2 scohg2' Heq2.
  split; [now apply stack_graphs_cohg_vert_eq_Proper; [apply Heq1.1|apply Heq2.1]|].
  change (vertices _) with (vertices (stack_graphs scohg1 scohg2)).
  rewrite vertices_stack_graphs.
  apply proj2 in Heq1, Heq2.
  cbn.
  intros v.
  rewrite 2 lookup_union.
  rewrite elem_of_union.
  intros [(k & -> & Hk)%elem_of_map|(k & -> & Hk)%elem_of_map];
  rewrite 2 (lookup_kmap _), 2 (lookup_kmap_None _ _ _).2,
    2?(left_id_L None _), 2?(right_id_L None _) by lia; auto.
Qed.

#[export] Instance stack_sized_graphs_struct_sized_isomorphic_Proper {n m n' m'} :
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic)
    (@stack_sized_graphs N T n m n' m').
Proof.
  apply proper_struct_sized_isomorphic_of_vert_eq_binary.
  - apply _.
  - intros ? ? ? ? ? ?.
    now apply stack_sized_graphs_sized_isomorphic.
Qed.


Lemma stack_sized_graphs_struct_sized_isomorphic {n m n' m'} (scohg1 scohg1' : SizedCospanHyperGraph N T n m)
  (scohg2 scohg2' : SizedCospanHyperGraph N T n' m') :
  scohg1 ≡ᵢ scohg1' -> scohg2 ≡ᵢ scohg2' ->
  stack_sized_graphs scohg1 scohg2 ≡ᵢ stack_sized_graphs scohg1' scohg2'.
Proof.
  now intros; apply stack_sized_graphs_struct_sized_isomorphic_Proper.
Qed.


Lemma relabel_swapped_stack_sized_graphs_aux {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') f {Hf : Inj eq eq f} :
  relabel_sized_graph f (swapped_stack_sized_graphs_aux scohg scohg') =
  swapped_stack_sized_graphs_aux (relabel_sized_graph f scohg) (relabel_sized_graph f scohg').
Proof.
  apply scohg_ext; [apply relabel_swapped_stack_graphs_aux|].
  cbn.
  rewrite (kmap_union f); done.
Qed.

Lemma swapped_stack_sized_graphs_relabel {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') ft fb {Hft : Inj eq eq ft} {Hfb : Inj eq eq fb} :
  swapped_stack_sized_graphs (relabel_sized_graph ft scohg) (relabel_sized_graph fb scohg') =
  relabel_sized_graph (pos_map ft fb) (swapped_stack_sized_graphs scohg scohg').
Proof.
  unfold swapped_stack_sized_graphs.
  rewrite relabel_swapped_stack_sized_graphs_aux by apply _.
  rewrite 2 reindex_relabel_sized_graph, 4 relabel_sized_graph_compose by apply _.
  done.
Qed.

Lemma reindex_swapped_stack_sized_graphs_aux {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') f `{Hf : !Inj eq eq f} :
  reindex_sized_graph f (swapped_stack_sized_graphs_aux scohg scohg') =
  swapped_stack_sized_graphs_aux (reindex_sized_graph f scohg) (reindex_sized_graph f scohg').
Proof.
  apply scohg_ext; [apply reindex_swapped_stack_graphs_aux, _|done].
Qed.

Lemma swapped_stack_sized_graphs_reindex {n m n' m'} (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') ft fb
  `{Hft : !Inj eq eq ft, Hfb : !Inj eq eq fb} :
  swapped_stack_sized_graphs (reindex_sized_graph ft scohg) (reindex_sized_graph fb scohg') =
  reindex_sized_graph (pos_map ft fb) (swapped_stack_sized_graphs scohg scohg').
Proof.
  unfold swapped_stack_sized_graphs.
  rewrite (reindex_swapped_stack_sized_graphs_aux _ _ _) by apply _.
  rewrite 2 reindex_relabel_sized_graph, 4 (reindex_sized_graph_compose _ _) by apply _.
  done.
Qed.

Lemma swapped_stack_sized_graphs_sized_isomorphic {n m n' m'} (scohg1 scohg1' : SizedCospanHyperGraph N T n m)
  (scohg2 scohg2' : SizedCospanHyperGraph N T n' m') :
  sized_isomorphic scohg1 scohg1' -> sized_isomorphic scohg2 scohg2' ->
  sized_isomorphic (swapped_stack_sized_graphs scohg1 scohg2) (swapped_stack_sized_graphs scohg1' scohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%sized_isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%sized_isomorphic_exists.
  rewrite swapped_stack_sized_graphs_relabel, (swapped_stack_sized_graphs_reindex _ _ _ _) by apply _.
  apply (sized_iso_relabel_reindex _ _ _).
Qed.


#[export] Instance swapped_stack_sized_graphs_scohg_vert_eq_Proper {n m n' m'} :
  Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq)
    (@swapped_stack_sized_graphs N T n m n' m').
Proof.
  intros scohg1 scohg1' Heq1 scohg2 scohg2' Heq2.
  split; [now apply swapped_stack_graphs_cohg_vert_eq_Proper; [apply Heq1.1|apply Heq2.1]|].
  change (vertices _) with (vertices (swapped_stack_graphs scohg1 scohg2)).
  rewrite vertices_swapped_stack_graphs.
  apply proj2 in Heq1, Heq2.
  cbn.
  intros v.
  rewrite 2 lookup_union.
  rewrite elem_of_union.
  intros [(k & -> & Hk)%elem_of_map|(k & -> & Hk)%elem_of_map];
  rewrite 2 (lookup_kmap _), 2 (lookup_kmap_None _ _ _).2,
    2?(left_id_L None _), 2?(right_id_L None _) by lia; auto.
Qed.

Lemma swapped_stack_sized_graphs_struct_sized_isomorphic_Proper {n m n' m'} :
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic)
    (@swapped_stack_sized_graphs N T n m n' m').
Proof.
  apply proper_struct_sized_isomorphic_of_vert_eq_binary.
  - apply _.
  - intros ? ? ? ? ? ?.
    now apply swapped_stack_sized_graphs_sized_isomorphic.
Qed.


Lemma swapped_stack_sized_graphs_struct_sized_isomorphic {n m n' m'} (scohg1 scohg1' : SizedCospanHyperGraph N T n m)
  (scohg2 scohg2' : SizedCospanHyperGraph N T n' m') :
  scohg1 ≡ᵢ scohg1' -> scohg2 ≡ᵢ scohg2' ->
  swapped_stack_sized_graphs scohg1 scohg2 ≡ᵢ swapped_stack_sized_graphs scohg1' scohg2'.
Proof.
  now intros; apply swapped_stack_sized_graphs_struct_sized_isomorphic_Proper.
Qed.

Lemma sized_add_top_loop_relabel_sized_graph {n m} f `{Hf : !Inj eq eq f} (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  sized_add_top_loop (relabel_sized_graph f scohg) =
  relabel_sized_graph f (sized_add_top_loop scohg).
Proof.
  apply scohg_ext; [apply (add_top_loop_relabel_graph _)|].
  cbn.
  unfold map_relabel_one.
  rewrite (kmap_partial_alter _).
  rewrite 2 vhd_vmap.
  rewrite (lookup_kmap f).
  done.
Qed.

Lemma sized_add_top_loop_reindex_sized_graph {n m} f (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  sized_add_top_loop (reindex_sized_graph f scohg) =
  reindex_sized_graph f (sized_add_top_loop scohg).
Proof.
  apply scohg_ext; [apply (add_top_loop_reindex_graph f)|done].
Qed.

Lemma vertices_add_top_loop_subset {n m } (cohg : CospanHyperGraph T (S n) (S m)) :
  vertices (add_top_loop cohg) ⊆ vertices cohg.
Proof.
  unfold add_top_loop.
  rewrite vertices_relabel_graph.
  rewrite set_map_fn_singleton_L.
  destruct cohg as [hg ins outs].
  cbn.
  inv_all_vec_fin.
  cbn.
  rewrite 2 vertices_vertices_hg_decomp; cbn -[union].
  rewrite 2 list_to_set_app_L.
  cbn -[union].
  rewrite vertices_hg_add_vertices.
  apply union_least; [apply subseteq_union_r; set_solver +|].
  case_decide; set_solver +.
Qed.



Lemma norm_sized_verts_sized_add_top_loop {n m} (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  norm_sized_verts (sized_add_top_loop scohg) =
  norm_sized_verts (sized_add_top_loop (norm_sized_verts scohg)).
Proof.
  apply scohg_ext; [apply norm_verts_add_top_loop|].
  cbn.
  rewrite <- (vertices_norm_verts (add_top_loop (norm_verts scohg))).
  rewrite <- norm_verts_add_top_loop.
  rewrite vertices_norm_verts.
  apply map_eq.
  intros k.
  rewrite 2 map_lookup_filter.
  cbn.
  case_guard; cbn; [rewrite 2 bind_with_Some|unfold mbind, option_bind; now repeat case_match].
  rewrite 2 lookup_map_relabel_one.
  rewrite fn_lookup_singleton_case.
  case_decide; [subst|].
  - pose proof (vertices_add_top_loop_subset scohg).
    rewrite map_lookup_filter.
    cbn.
    enough (vhd scohg.(outputs) ∈ vertices scohg) by (
      case_guard; cbn; [now rewrite bind_with_Some|
      unfold mbind, option_bind; now repeat case_match]).
    rewrite vertices_vertices_hg_decomp, list_to_set_app_L.
    inv_vec (outputs scohg); cbn -[union]; set_solver +.
  - rewrite map_lookup_filter.
    cbn.
    enough (k ∈ vertices scohg) by (
      case_guard; cbn; [now rewrite bind_with_Some|
      unfold mbind, option_bind; now repeat case_match]).
    now apply vertices_add_top_loop_subset.
Qed.

Lemma norm_sized_verts_idemp {n m} (scohg : SizedCospanHyperGraph N T n m) :
  norm_sized_verts (norm_sized_verts scohg) = norm_sized_verts scohg.
Proof.
  apply scohg_ext; [apply norm_verts_idemp|].
  cbn.
  rewrite map_filter_filter.
  apply map_filter_ext.
  cbn.
  rewrite vertices_norm_verts.
  tauto.
Qed.

Lemma norm_sized_verts_sized_add_top_loops {n m o} (scohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  norm_sized_verts (sized_add_top_loops scohg) = norm_sized_verts (sized_add_top_loops (norm_sized_verts scohg)).
Proof.
  induction n; [cbn; now rewrite norm_sized_verts_idemp|].
  cbn.
  now rewrite IHn, norm_sized_verts_sized_add_top_loop, <- IHn.
Qed.

#[export] Instance sized_add_top_loop_proper {n m} :
  Proper (@scohg_vert_eq N T (S n) (S m) ==> scohg_vert_eq) sized_add_top_loop.
Proof.
  intros cohg cohg' Heq.
  rewrite <- norm_sized_verts_vert_eq.
  rewrite norm_sized_verts_sized_add_top_loop.
  rewrite (norm_sized_verts_of_vert_eq _ _ Heq).
  rewrite <- norm_sized_verts_sized_add_top_loop.
  rewrite norm_sized_verts_vert_eq.
  done.
Qed.


Lemma sized_add_top_loop_struct_sized_isomorphic {n m} (scohg scohg' : SizedCospanHyperGraph N T (S n) (S m)) :
  scohg ≡ᵢ scohg' ->
  sized_add_top_loop scohg ≡ᵢ sized_add_top_loop scohg'.
Proof.
  intros (fv & fe & Hfv & Hfe & Heq)%sized_isomorphic_exists.
  rewrite <- norm_sized_verts_vert_eq, norm_sized_verts_sized_add_top_loop.
  rewrite <- (norm_sized_verts_vert_eq (sized_add_top_loop scohg')),
    (norm_sized_verts_sized_add_top_loop scohg').
  rewrite Heq.
  rewrite (sized_add_top_loop_relabel_sized_graph _), sized_add_top_loop_reindex_sized_graph.
  rewrite (norm_sized_verts_vert_eq (sized_add_top_loop _)),
    (norm_sized_verts_vert_eq (relabel_sized_graph _ _)).
  apply (subrel' sized_isomorphic).
  now constructor.
Qed.

Definition relabel_sized_graph_one {n m} (k k' : positive) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph N T n m :=
  mk_scohg (relabel_graph {[k := k']} scohg) (map_relabel_one k' k scohg.(sized_map)).


Definition relabels_sized_graph_r {n m} {l} (ks : vec (positive * positive) l)
  (scohg : SizedCospanHyperGraph N T n m) : SizedCospanHyperGraph N T n m :=
  mk_scohg (relabel_graph (subst_by_vec (propogate_subst ks)) scohg)
    (map_relabels_r ks (scohg.(sized_map))).

Lemma sized_add_top_loop_eq_relabel_one {n m} (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  sized_add_top_loop scohg =
  sized_add_top_loop (relabel_sized_graph_one (vhd (outputs scohg)) (vhd (inputs scohg)) scohg).
Proof.
  apply scohg_ext; [apply add_top_loop_eq_relabel|].
  cbn.
  rewrite 2 vhd_vmap.
  rewrite fn_lookup_singleton, fn_lookup_singleton_r.
  apply map_eq.
  intros i.
  rewrite 3 lookup_map_relabel_one.
  rewrite fn_lookup_singleton_id.
  done.
Qed.

Lemma sized_add_top_loop_struct_sized_isomorphic_strong {n m} (scohg scohg' : SizedCospanHyperGraph N T (S n) (S m)) :
  relabel_sized_graph_one (vhd (outputs scohg)) (vhd (inputs scohg)) scohg ≡ᵢ
  relabel_sized_graph_one (vhd (outputs scohg')) (vhd (inputs scohg')) scohg' ->
  sized_add_top_loop scohg ≡ᵢ sized_add_top_loop scohg'.
Proof.
  intros Hiso.
  rewrite sized_add_top_loop_eq_relabel_one.
  erewrite sized_add_top_loop_struct_sized_isomorphic by apply Hiso.
  rewrite <- sized_add_top_loop_eq_relabel_one.
  done.
Qed.




Lemma sized_add_top_loops_struct_sized_isomorphic {n m o}
  (scohg scohg' : SizedCospanHyperGraph N T (n + m) (n + o)) :
  scohg ≡ᵢ scohg' ->
  sized_add_top_loops scohg ≡ᵢ sized_add_top_loops scohg'.
Proof.
  intros Hiso.
  induction n; [done|].
  cbn.
  apply IHn.
  now apply sized_add_top_loop_struct_sized_isomorphic.
Qed.

Lemma compose_sized_graphs_struct_sized_isomorphic {n m o}
  (scohg1 scohg1' : SizedCospanHyperGraph N T n m) (scohg2 scohg2' : SizedCospanHyperGraph N T m o) :
  scohg1 ≡ᵢ scohg1' -> scohg2 ≡ᵢ scohg2' ->
  compose_sized_graphs scohg1 scohg2 ≡ᵢ compose_sized_graphs scohg1' scohg2'.
Proof.
  intros Heq1 Heq2.
  rewrite <- 2 compose_sized_graphs_alt_correct.
  apply sized_add_top_loops_struct_sized_isomorphic.
  now apply swapped_stack_sized_graphs_struct_sized_isomorphic.
Qed.





#[export] Instance sized_add_top_loops_scohg_vert_eq {n m o} :
  Proper (scohg_vert_eq ==> scohg_vert_eq)
    (@sized_add_top_loops N T n m o).
Proof.
  induction n; [easy|].
  intros scohg scohg' Hscohg.
  cbn.
  now apply IHn, sized_add_top_loop_proper.
Qed.



#[export] Instance compose_sized_graphs_alt_scohg_vert_eq
  {n m o} : Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq)
    (@compose_sized_graphs_alt N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  unfold compose_sized_graphs_alt.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_sized_graphs_alt_struct_sized_isomorphic `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic)
    (@compose_sized_graphs_alt N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  unfold compose_sized_graphs_alt.
  apply sized_add_top_loops_struct_sized_isomorphic.
  now apply swapped_stack_sized_graphs_struct_sized_isomorphic.
Qed.

(* FIXME: Move *)
#[export] Instance struct_sized_isomorphic_syntactic_eq {T'} `{Equiv T', Equivalence T' equiv} {n m} :
  subrelation (@struct_sized_isomorphic N T' n m) scohg_syntactic_eq.
Proof.
  intros x y Heq.
  hnf in Heq.
  rewrite <- (norm_sized_verts_vert_eq x), Heq.
  apply (subrel (norm_sized_verts_vert_eq y)).
Qed.

(*
#[export] Instance scohg_vert_eq_struct_sized_isomorphic {n m} :
  subrelation (@scohg_vert_eq N T n m) struct_sized_isomorphic.
  apply _.
Proof.
  now intros ? ? <-.
Qed. *)


Lemma proper_scohg_syntactic_eq_of_struct_sized_iso_eq_binary `{Equiv T1, Equivalence T1 equiv,
  Equiv T2, Equivalence T2 equiv, Equiv T3, Equivalence T3 equiv} {n1 m1 n2 m2 n3 m3}
  (f : SizedCospanHyperGraph N T1 n1 m1 -> SizedCospanHyperGraph N T2 n2 m2 ->
    SizedCospanHyperGraph N T3 n3 m3) :
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic) f ->
  Proper (scohg_eq ==> scohg_eq ==> scohg_eq) f ->
  Proper (scohg_syntactic_eq ==> scohg_syntactic_eq ==> scohg_syntactic_eq) f.
Proof.
  intros Hfiso Hfscohg.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  induction Hscohg1 as [scohg1 scohg1' fv1 fe1 Hfv1 Hfe1 Hverteq1].
  rewrite <- (subrel'' struct_sized_isomorphic (norm_sized_verts_vert_eq scohg1)).
  rewrite (Hverteq1).
  rewrite (subrel'' struct_sized_isomorphic (norm_sized_verts_vert_eq _)).
  rewrite <- (subrel'' struct_sized_isomorphic (sized_iso_relabel_reindex _ _ _)) by done.
  induction Hscohg2 as [scohg2 scohg2' fv2 fe2 Hfv2 Hfe2 Hverteq2].
  rewrite <- (subrel'' struct_sized_isomorphic (norm_sized_verts_vert_eq scohg2)).
  rewrite (Hverteq2).
  rewrite (subrel'' struct_sized_isomorphic (norm_sized_verts_vert_eq _)).
  rewrite <- (subrel'' struct_sized_isomorphic (sized_iso_relabel_reindex _ _ _)) by done.
  done.
Qed.

#[export] Instance compose_sized_graphs_alt_scohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (scohg_syntactic_eq ==> scohg_syntactic_eq ==> scohg_syntactic_eq)
    (@compose_sized_graphs_alt N T n m o).
Proof.
  apply proper_scohg_syntactic_eq_of_struct_sized_iso_eq_binary; apply _.
Qed.

#[export] Instance compose_sized_graphs_scohg_vert_eq
  {n m o} : Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq)
    (@compose_sized_graphs N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  do 2 rewrite <- compose_sized_graphs_alt_correct.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_sized_graphs_struct_sized_isomorphic_mor `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic)
    (@compose_sized_graphs N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  do 2 rewrite <- compose_sized_graphs_alt_correct.
  now apply compose_sized_graphs_alt_struct_sized_isomorphic.
Qed.

#[export] Instance compose_sized_graphs_scohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (scohg_syntactic_eq ==> scohg_syntactic_eq ==> scohg_syntactic_eq)
    (@compose_sized_graphs N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  rewrite <- 2 compose_sized_graphs_alt_correct.
  now apply compose_sized_graphs_alt_scohg_syntactic_eq.
Qed.

#[export] Instance stack_sized_graphs_scohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o p} : Proper (scohg_syntactic_eq ==> scohg_syntactic_eq ==> scohg_syntactic_eq)
    (@stack_sized_graphs N T n m o p).
Proof.
  apply proper_scohg_syntactic_eq_of_struct_sized_iso_eq_binary; apply _.
Qed.

#[export] Instance compose_sized_graphs_aux_scohg_eq `{Equiv T} {n m o} :
  Proper (scohg_eq ==> scohg_eq ==> scohg_eq) (@compose_sized_graphs_aux N T n m o).
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  split; [apply compose_graphs_aux_cohg_eq, Heq2.1; apply Heq1.1|].
  cbn.
  f_equal; (f_equal; [apply Heq1|apply Heq2]).
Qed.


#[export] Instance compose_sized_graphs_scohg_eq `{Equiv T} {n m o} :
  Proper (scohg_eq ==> scohg_eq ==> scohg_eq) (@compose_sized_graphs N T n m o).
Proof.
  intros scohg1 scohg1' Hscohg1 scohg2 scohg2' Hscohg2.
  rewrite 2 compose_sized_graphs_to_compose_sized_graphs_aux.
  now apply compose_sized_graphs_aux_scohg_eq; do 2 f_equiv.
Qed.












(* 










Lemma sized_add_top_loops_eq_relabels {n m m'}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + m')) :
  sized_add_top_loops scohg =
  sized_add_top_loops (relabels_sized_graph_r
    (vzip (vsplitl (outputs scohg)) (vsplitl (inputs scohg))) scohg).
Proof.
  apply scohg_ext; [
    rewrite 2 sized_cospan_sized_add_top_loops; apply add_top_loops_eq_relabel|].
  rewrite 2 sized_map_sized_add_top_loops.
  cbn.
  destruct scohg as [[hg ins outs] smap].
  cbn.
  induction ins as [lins rins] using vec_add_inv.
  induction outs as [louts routs] using vec_add_inv.
  rewrite 2 vsplitl_app, 2 vsplitl_map, 2 vsplitl_app.
  clear.


  unfold sized_add_top_loops.
  induction n; [cbn; now rewrite relabel_sized_graph_id|].
  cbn -[propogate_subst].
  rewrite IHn.
  f_equal.
  destruct scohg as [hg ins outs].
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[propogate_subst Vector.append].
  rewrite 2 vsplitl_app.
  cbn -[propogate_subst].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  apply scohg_ext.
  - cbn.
    rewrite relabel_hg_compose, 2 relabel_hg_add_vertices, relabel_hg_compose.
    f_equal. 2:{
      rewrite 2 set_map_singleton_L.
      rewrite fn_lookup_singleton_r.
      cbn.
      rewrite vzip_map.
      done.
    }
    apply relabel_hg_ext.
    intros k.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    rewrite vzip_map.
    done.
  - cbn -[Vector.append propogate_subst].
    rewrite 2 Vector.map_map.
    apply Vector.map_ext.
    intros k.
    rewrite vzip_map.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    done.
  - cbn -[Vector.append propogate_subst].
    rewrite 2 Vector.map_map.
    apply Vector.map_ext.
    intros k.
    rewrite vzip_map.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    done.
Qed.


Lemma sized_add_top_loops_eq_relabel {n m m'}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + m')) :
  sized_add_top_loops scohg =
  sized_add_top_loops (relabel_sized_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs scohg)) (vsplitl (inputs scohg)))) scohg).
Proof.
  induction n; [cbn; now rewrite relabel_sized_graph_id|].
  cbn -[propogate_subst].
  rewrite IHn.
  f_equal.
  destruct scohg as [hg ins outs].
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[propogate_subst Vector.append].
  rewrite 2 vsplitl_app.
  cbn -[propogate_subst].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  apply scohg_ext.
  - cbn.
    rewrite relabel_hg_compose, 2 relabel_hg_add_vertices, relabel_hg_compose.
    f_equal. 2:{
      rewrite 2 set_map_singleton_L.
      rewrite fn_lookup_singleton_r.
      cbn.
      rewrite vzip_map.
      done.
    }
    apply relabel_hg_ext.
    intros k.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    rewrite vzip_map.
    done.
  - cbn -[Vector.append propogate_subst].
    rewrite 2 Vector.map_map.
    apply Vector.map_ext.
    intros k.
    rewrite vzip_map.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    done.
  - cbn -[Vector.append propogate_subst].
    rewrite 2 Vector.map_map.
    apply Vector.map_ext.
    intros k.
    rewrite vzip_map.
    cbn.
    rewrite fn_lookup_singleton, fn_lookup_singleton_r.
    rewrite fn_lookup_singleton_id.
    done.
Qed.

Lemma sized_add_top_loops_struct_sized_isomorphic_strong {n m o}
  (scohg scohg' : SizedCospanHyperGraph N T (n + m) (n + o)) :
  relabel_sized_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs scohg)) (vsplitl (inputs scohg)))) scohg ≡ᵢ
  relabel_sized_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs scohg')) (vsplitl (inputs scohg')))) scohg' ->
  sized_add_top_loops scohg ≡ᵢ sized_add_top_loops scohg'.
Proof.
  intros Hiso.
  rewrite sized_add_top_loops_eq_relabel.
  erewrite sized_add_top_loops_struct_sized_isomorphic by apply Hiso.
  rewrite <- sized_add_top_loops_eq_relabel.
  done.
Qed.




Lemma relabel_sized_graph_to_fun_to_map {n m} f (scohg : SizedCospanHyperGraph N T n m) :
  relabel_sized_graph f scohg = relabel_sized_graph (Pmap_map (fun_to_map f (vertices scohg))) scohg.
Proof.
  apply relabel_sized_graph_ext_strong.
  intros i Hi.
  symmetry.
  unfold Pmap_map.
  now rewrite lookup_fun_to_map_Some_1.
Qed.

Lemma relabel_sized_graph_Pmap_map_to_union_l {n m} ml mr (scohg : SizedCospanHyperGraph N T n m) :
  vertices scohg ⊆ dom ml ->
  relabel_sized_graph (Pmap_map ml) scohg =
  relabel_sized_graph (Pmap_map (ml ∪ mr)) scohg.
Proof.
  intros Hvert.
  apply relabel_sized_graph_ext_strong.
  intros i [mli Hmli]%Hvert%elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hmli.
  now destruct (mr !! i).
Qed.

Lemma relabel_sized_graph_Pmap_map_to_union_r {n m} ml mr (scohg : SizedCospanHyperGraph N T n m) :
  vertices scohg ## dom ml ->
  relabel_sized_graph (Pmap_map mr) scohg =
  relabel_sized_graph (Pmap_map (ml ∪ mr)) scohg.
Proof.
  intros Hvert.
  apply relabel_sized_graph_ext_strong.
  intros i Hi%Hvert%not_elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hi.
  now rewrite (left_id_L None _).
Qed.

Lemma relabel_sized_graph_Pmap_map_to_Pmap_injmap {n m} mv (scohg : SizedCospanHyperGraph N T n m) :
  vertices scohg ⊆ dom mv ->
  relabel_sized_graph (Pmap_map mv) scohg =
  relabel_sized_graph (Pmap_injmap mv) scohg.
Proof.
  intros Hvert.
  apply relabel_sized_graph_ext_strong.
  intros i Hi%Hvert.
  symmetry.
  now apply Pmap_injmap_correct_dom.
Qed.

Lemma reindex_sized_graph_to_fun_to_map {n m} f (scohg : SizedCospanHyperGraph N T n m) :
  reindex_sized_graph f scohg = reindex_sized_graph (Pmap_map (fun_to_map f (dom (hyperedges scohg)))) scohg.
Proof.
  apply reindex_sized_graph_ext_strong.
  intros i _ Hi%elem_of_dom_2.
  symmetry.
  unfold Pmap_map.
  now rewrite lookup_fun_to_map_Some_1.
Qed.

Lemma reindex_sized_graph_Pmap_map_to_union_l {n m} ml mr (scohg : SizedCospanHyperGraph N T n m) :
  dom $ hyperedges scohg ⊆ dom ml ->
  reindex_sized_graph (Pmap_map ml) scohg =
  reindex_sized_graph (Pmap_map (ml ∪ mr)) scohg.
Proof.
  intros Hvert.
  apply reindex_sized_graph_ext_strong.
  intros i _ [mli Hmli]%elem_of_dom_2%Hvert%elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hmli.
  now destruct (mr !! i).
Qed.

Lemma reindex_sized_graph_Pmap_map_to_union_r {n m} ml mr (scohg : SizedCospanHyperGraph N T n m) :
  dom $ hyperedges scohg ## dom ml ->
  reindex_sized_graph (Pmap_map mr) scohg =
  reindex_sized_graph (Pmap_map (ml ∪ mr)) scohg.
Proof.
  intros Hvert.
  apply reindex_sized_graph_ext_strong.
  intros i _ Hi%elem_of_dom_2%Hvert%not_elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hi.
  now rewrite (left_id_L None _).
Qed.

Lemma reindex_sized_graph_Pmap_map_to_Pmap_injmap {n m} mv (scohg : SizedCospanHyperGraph N T n m) :
  dom $ hyperedges scohg ⊆ dom mv ->
  reindex_sized_graph (Pmap_map mv) scohg =
  reindex_sized_graph (Pmap_injmap mv) scohg.
Proof.
  intros Hvert.
  apply reindex_sized_graph_ext_strong.
  intros i _ Hi%elem_of_dom_2%Hvert.
  symmetry.
  now apply Pmap_injmap_correct_dom.
Qed.

(* FIXME: Move *)
Lemma map_inj_disj_union `{FinMap K M} {A}
  (m1 m2 : M A) :
  m1 ##ₘ m2 ->
  map_inj m1 -> map_inj m2 ->
  (forall i j a b, m1 !! i = Some a -> m2 !! j = Some b -> a <> b) ->
  map_inj (m1 ∪ m2).
Proof.
  intros Hdisj Hinj1 Hinj2 Hdisjimg.
  intros i j a.
  rewrite 2 lookup_union_Some by done.
  intros [Hm1i|Hm2i] [Hm1j|Hm2j]; [now eauto|..|now eauto];
  exfalso; eapply (Hdisjimg _ _ a); eauto.
Qed.
Lemma fun_to_map_inj `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) `{Hf : !Inj eq eq f} (X : SK) :
  map_inj (fun_to_map f X :> M A).
Proof.
  intros i j a.
  rewrite 2 lookup_fun_to_map_Some.
  now intros [Hi <-] [Hj ?%Hf].
Qed.
Lemma map_img_fun_to_map `{FinMap K M, FinSet K SK, SemiSet A SA}
  (f : K -> A) (X : SK) :
  map_img (fun_to_map f X :> M A) ≡@{SA} set_map f X.
Proof.
  intros k.
  rewrite elem_of_map, elem_of_map_img.
  setoid_rewrite lookup_fun_to_map_Some.
  firstorder.
Qed.
Lemma map_img_fun_to_map_L `{FinMap K M, FinSet K SK, SemiSet A SA, !LeibnizEquiv SA}
  (f : K -> A) (X : SK) :
  map_img (fun_to_map f X :> M A) =@{SA} set_map f X.
Proof.
  apply leibniz_equiv_iff, map_img_fun_to_map.
Qed.


Lemma stack_sized_graphs_aux_relabel_disjoint {n m n' m'} f1 f2
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  vertices scohg1 ## vertices scohg2 ->
  stack_sized_graphs_aux (relabel_sized_graph f1 scohg1) (relabel_sized_graph f2 scohg2) =
  relabel_sized_graph (Pmap_map (fun_to_map f1 (vertices scohg1) ∪ fun_to_map f2 (vertices scohg2)))
    (stack_sized_graphs_aux scohg1 scohg2).
Proof.
  intros Hdisj.
  rewrite relabel_stack_sized_graphs_aux.
  f_equal.
  - rewrite (relabel_sized_graph_to_fun_to_map f1).
    apply relabel_sized_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (relabel_sized_graph_to_fun_to_map f2).
    apply relabel_sized_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
Qed.

Lemma stack_sized_graphs_aux_reindex_disjoint {n m n' m'} f1 f2
  `{Hf1 : !Inj eq eq f1, Hf2 : !Inj eq eq f2}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  dom $ hyperedges scohg1 ## dom $ hyperedges scohg2 ->
  set_map f1 $ dom $ hyperedges scohg1 ##@{Pset} set_map f2 $ dom $ hyperedges scohg2 ->
  stack_sized_graphs_aux (reindex_sized_graph f1 scohg1) (reindex_sized_graph f2 scohg2) =
  reindex_sized_graph (Pmap_map (fun_to_map f1 (dom $ hyperedges scohg1) ∪
    fun_to_map f2 (dom $ hyperedges scohg2)))
    (stack_sized_graphs_aux scohg1 scohg2).
Proof.
  intros Hdisj Hdisjran.
  rewrite reindex_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
    done.
  }
  rewrite reindex_stack_sized_graphs_aux; [f_equal|].
  - rewrite (reindex_sized_graph_to_fun_to_map f1).
    rewrite <- reindex_sized_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_l'.
    apply reindex_sized_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (reindex_sized_graph_to_fun_to_map f2).
    rewrite <- reindex_sized_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_r'.
    apply reindex_sized_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L.
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      intros ->.
      apply Hdisjran in Ha.
      now apply Ha in Hb.
Qed.


Lemma stack_sized_graphs_aux_sized_isomorphic {n m n' m'}
  (scohg1 scohg1' : SizedCospanHyperGraph N T n m)
  (scohg2 scohg2' : SizedCospanHyperGraph N T n' m') :
  sized_isomorphic scohg1 scohg1' -> sized_isomorphic scohg2 scohg2' ->
  hyperedges scohg1 ##ₘ hyperedges scohg2 -> hyperedges scohg1' ##ₘ hyperedges scohg2' ->
  vertices scohg1 ## vertices scohg2 -> vertices scohg1' ## vertices scohg2' ->
  sized_isomorphic (stack_sized_graphs_aux scohg1 scohg2) (stack_sized_graphs_aux scohg1' scohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%sized_isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%sized_isomorphic_exists.
  intros Hdisj Hdisj' Hvdisj Hvdisj'.
  rewrite stack_sized_graphs_aux_relabel_disjoint by now rewrite 2 (vertices_reindex_sized_graph _).
  rewrite (stack_sized_graphs_aux_reindex_disjoint _ _ _); [|now apply map_disjoint_dom|].
  2:{
    rewrite map_disjoint_dom in Hdisj'.
    cbn in Hdisj'.
    rewrite 2 dom_fmap_L in Hdisj'.
    rewrite 2 dom_kmap_L' in Hdisj'.
    done.
  }
  rewrite reindex_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    now rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
  }
  assert (Hinjidx : Inj eq eq (Pmap_injmap
           (fun_to_map fe1 (dom (hyperedges scohg1) :> Pset) ∪
           fun_to_map fe2 (dom (hyperedges scohg2) :> Pset)))). 1:{
    apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L; rewrite map_disjoint_dom in Hdisj.
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite map_disjoint_dom in Hdisj'.
      cbn in Hdisj'.
      rewrite 2 dom_fmap, 2 dom_kmap_L' in Hdisj'.
      intros ->.
      now apply Hdisj' in Hb.
  }
  rewrite relabel_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    rewrite 3 (vertices_reindex_sized_graph _).
    rewrite vertices_stack_sized_graphs_aux by done.
    now rewrite dom_union_L, 2 dom_fun_to_map_L.
  }
  constructor.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L,
      2 (vertices_reindex_sized_graph _).
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite (vertices_reindex_sized_graph _) in Ha.
      rewrite (vertices_reindex_sized_graph _) in Hb.
      rewrite 2 vertices_relabel_sized_graph, 2 (vertices_reindex_sized_graph _) in Hvdisj'.
      intros ->.
      now apply Hvdisj' in Hb.
  - apply _.
Qed.


Lemma stack_sized_graphs_aux_to_stack_sized_graphs_disjoint {n m n' m'}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  hyperedges scohg1 ##ₘ hyperedges scohg2 ->
  vertices scohg1 ## vertices scohg2 ->
  sized_isomorphic (stack_sized_graphs_aux scohg1 scohg2) (stack_sized_graphs scohg1 scohg2).
Proof.
  intros Hdisj Hvdisj.
  unfold stack_sized_graphs.
  apply stack_sized_graphs_aux_sized_isomorphic.
  - constructor; apply _.
  - constructor; apply _.
  - done.
  - cbn.
    apply map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
  - done.
  - rewrite 2 vertices_relabel_sized_graph, 2 (vertices_reindex_sized_graph _).
    set_solver +.
Qed.


Lemma swapped_stack_sized_graphs_aux_relabel_disjoint {n m n' m'} f1 f2
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  vertices scohg1 ## vertices scohg2 ->
  swapped_stack_sized_graphs_aux (relabel_sized_graph f1 scohg1) (relabel_sized_graph f2 scohg2) =
  relabel_sized_graph (Pmap_map (fun_to_map f1 (vertices scohg1) ∪ fun_to_map f2 (vertices scohg2)))
    (swapped_stack_sized_graphs_aux scohg1 scohg2).
Proof.
  intros Hdisj.
  rewrite relabel_swapped_stack_sized_graphs_aux.
  f_equal.
  - rewrite (relabel_sized_graph_to_fun_to_map f1).
    apply relabel_sized_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (relabel_sized_graph_to_fun_to_map f2).
    apply relabel_sized_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
Qed.

Lemma swapped_stack_sized_graphs_aux_reindex_disjoint {n m n' m'} f1 f2
  `{Hf1 : !Inj eq eq f1, Hf2 : !Inj eq eq f2}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  dom $ hyperedges scohg1 ## dom $ hyperedges scohg2 ->
  set_map f1 $ dom $ hyperedges scohg1 ##@{Pset} set_map f2 $ dom $ hyperedges scohg2 ->
  swapped_stack_sized_graphs_aux (reindex_sized_graph f1 scohg1) (reindex_sized_graph f2 scohg2) =
  reindex_sized_graph (Pmap_map (fun_to_map f1 (dom $ hyperedges scohg1) ∪
    fun_to_map f2 (dom $ hyperedges scohg2)))
    (swapped_stack_sized_graphs_aux scohg1 scohg2).
Proof.
  intros Hdisj Hdisjran.
  rewrite reindex_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
    done.
  }
  rewrite reindex_swapped_stack_sized_graphs_aux; [f_equal|].
  - rewrite (reindex_sized_graph_to_fun_to_map f1).
    rewrite <- reindex_sized_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_l'.
    apply reindex_sized_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (reindex_sized_graph_to_fun_to_map f2).
    rewrite <- reindex_sized_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_r'.
    apply reindex_sized_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L.
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      intros ->.
      apply Hdisjran in Ha.
      now apply Ha in Hb.
Qed.

Lemma vertices_swapped_stack_sized_graphs_aux {n m n' m'}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  hyperedges scohg1 ##ₘ hyperedges scohg2 ->
  vertices (swapped_stack_sized_graphs_aux scohg1 scohg2) =
  vertices scohg1 ∪ vertices scohg2.
Proof.
  intros Hdisj.
  unfold vertices.
  cbn.
  rewrite vertices_hg_union by done.
  rewrite 2 vec_to_list_app, 5 list_to_set_app_L.
  apply set_eq.
  intros k.
  rewrite !elem_of_union.
  tauto.
Qed.

Lemma swapped_stack_sized_graphs_aux_sized_isomorphic {n m n' m'}
  (scohg1 scohg1' : SizedCospanHyperGraph N T n m)
  (scohg2 scohg2' : SizedCospanHyperGraph N T n' m') :
  sized_isomorphic scohg1 scohg1' -> sized_isomorphic scohg2 scohg2' ->
  hyperedges scohg1 ##ₘ hyperedges scohg2 -> hyperedges scohg1' ##ₘ hyperedges scohg2' ->
  vertices scohg1 ## vertices scohg2 -> vertices scohg1' ## vertices scohg2' ->
  sized_isomorphic (swapped_stack_sized_graphs_aux scohg1 scohg2) (swapped_stack_sized_graphs_aux scohg1' scohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%sized_isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%sized_isomorphic_exists.
  intros Hdisj Hdisj' Hvdisj Hvdisj'.
  rewrite swapped_stack_sized_graphs_aux_relabel_disjoint by now rewrite 2 (vertices_reindex_sized_graph _).
  rewrite (swapped_stack_sized_graphs_aux_reindex_disjoint _ _ _); [|now apply map_disjoint_dom|].
  2:{
    rewrite map_disjoint_dom in Hdisj'.
    cbn in Hdisj'.
    rewrite 2 dom_fmap_L in Hdisj'.
    rewrite 2 dom_kmap_L' in Hdisj'.
    done.
  }
  rewrite reindex_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    now rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
  }
  assert (Hinjidx : Inj eq eq (Pmap_injmap
           (fun_to_map fe1 (dom (hyperedges scohg1) :> Pset) ∪
           fun_to_map fe2 (dom (hyperedges scohg2) :> Pset)))). 1:{
    apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L; rewrite map_disjoint_dom in Hdisj.
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite map_disjoint_dom in Hdisj'.
      cbn in Hdisj'.
      rewrite 2 dom_fmap, 2 dom_kmap_L' in Hdisj'.
      intros ->.
      now apply Hdisj' in Hb.
  }
  rewrite relabel_sized_graph_Pmap_map_to_Pmap_injmap. 2:{
    rewrite 3 (vertices_reindex_sized_graph _).
    rewrite vertices_swapped_stack_sized_graphs_aux by done.
    now rewrite dom_union_L, 2 dom_fun_to_map_L.
  }
  constructor.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L,
      2 (vertices_reindex_sized_graph _).
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite (vertices_reindex_sized_graph _) in Ha.
      rewrite (vertices_reindex_sized_graph _) in Hb.
      rewrite 2 vertices_relabel_sized_graph, 2 (vertices_reindex_sized_graph _) in Hvdisj'.
      intros ->.
      now apply Hvdisj' in Hb.
  - apply _.
Qed.


Lemma swapped_stack_sized_graphs_aux_to_swapped_stack_sized_graphs_disjoint {n m n' m'}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T n' m') :
  hyperedges scohg1 ##ₘ hyperedges scohg2 ->
  vertices scohg1 ## vertices scohg2 ->
  sized_isomorphic (swapped_stack_sized_graphs_aux scohg1 scohg2) (swapped_stack_sized_graphs scohg1 scohg2).
Proof.
  intros Hdisj Hvdisj.
  unfold swapped_stack_sized_graphs.
  apply swapped_stack_sized_graphs_aux_sized_isomorphic.
  - constructor; apply _.
  - constructor; apply _.
  - done.
  - cbn.
    apply map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
  - done.
  - rewrite 2 vertices_relabel_sized_graph, 2 (vertices_reindex_sized_graph _).
    set_solver +.
Qed.

Lemma compose_sized_graphs_aux_to_compose_sized_graphs_disjoint {n m o}
  (scohg1 : SizedCospanHyperGraph N T n m) (scohg2 : SizedCospanHyperGraph N T m o) :
  hyperedges scohg1 ##ₘ hyperedges scohg2 ->
  vertices scohg1 ## vertices scohg2 ->
  compose_sized_graphs_aux scohg1 scohg2 ≡ᵢ compose_sized_graphs scohg1 scohg2.
Proof.
  intros Hdisj Hvdisj.
  rewrite <- compose_sized_graphs_alt_correct, <- compose_sized_graphs_alt_aux_correct by done.
  apply sized_add_top_loops_struct_sized_isomorphic.
  apply (subrel' sized_isomorphic).
  now apply swapped_stack_sized_graphs_aux_to_swapped_stack_sized_graphs_disjoint.
Qed.

Lemma sized_isomorphic_reindex_sized_graph {n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (scohg : SizedCospanHyperGraph N T n m) :
  sized_isomorphic scohg (reindex_sized_graph f scohg).
Proof.
  apply sized_isomorphic_exists.
  exists id, f.
  rewrite relabel_sized_graph_id.
  split_and!; [apply _..|done].
Qed.

Lemma sized_isomorphic_relabel_sized_graph {n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (scohg : SizedCospanHyperGraph N T n m) :
  sized_isomorphic scohg (relabel_sized_graph f scohg).
Proof.
  apply sized_isomorphic_exists.
  exists f, id.
  rewrite reindex_sized_graph_id.
  split_and!; [apply _..|done].
Qed.


Lemma subst_by_vec_notin {n} (v : vec _ n) p :
  p ∉ v.*1 ->
  subst_by_vec v p = p.
Proof.
  revert p; induction v as [|(i, o) n v IHv]; intros p; [done|].
  cbn.
  intros Hp.
  rewrite fn_lookup_singleton_ne by now intros ->; apply Hp; left.
  apply IHv.
  eauto using elem_of_list.
Qed.

(* FIXME: Move *)
Lemma Pmap_map_insert k v m p :
  Pmap_map (<[k := v]> m) p = <[k := v]> (Pmap_map m) p.
Proof.
  unfold Pmap_map.
  rewrite lookup_insert_case, fn_lookup_insert_case.
  case_decide; done.
Qed.

Lemma subst_by_vec_disj {n} (v : vec _ n) p :
  v.*1 ## v.*2 ->
  subst_by_vec v p =
  Pmap_map (list_to_map v :> Pmap positive) p.
Proof.
  revert p; induction v as [|(i, o) n v IHv]; intros p.
  - cbn.
    unfold Pmap_map.
    now rewrite lookup_empty.
  - cbn.
    intros Hdisj.
    rewrite fn_lookup_singleton_case.
    rewrite Pmap_map_insert, fn_lookup_insert_case.
    case_decide as Hip.
    + subst p.
      now rewrite subst_by_vec_notin by set_solver +Hdisj.
    + apply IHv.
      intros k Hk1 Hk2.
      apply (Hdisj k); now constructor.
Qed.


Lemma subst_by_vec_case {n} (v : vec _ n) p :
  (p ∈ v.*1 /\ subst_by_vec v p ∈ v.*2) \/
  (p ∉ v.*1 /\ subst_by_vec v p = p).
Proof.
  revert p.
  induction n as [|n IHn]; [induction v using vec_0_inv; right; split; easy|].
  intros p.
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite fn_lookup_singleton_case.
  case_decide as Hip.
  - left.
    subst p.
    split; [constructor|].
    destruct (IHn v o) as [[? ?]|[? ->]];
    eauto using elem_of_list.
  - destruct (IHn v p) as [[? ?]|[? ->]];
    [eauto using elem_of_list|].
    right.
    split; [|done].
    now rewrite not_elem_of_cons.
Qed.

(* FIXME: Move *)
Lemma fn_lookup_singleton_ne_strong `{EqDecision A} (a b c : A) :
  (a <> b -> a <> c) ->
  {[a := b]} c = c.
Proof.
  rewrite fn_lookup_singleton_case.
  case_decide; [|done].
  destruct_decide (decide (a = b)); [now subst|tauto].
Qed.
Lemma fn_lookup_singleton_idemp `{EqDecision A} (a b c : A) :
  {[a := b]} ({[a := b]} c) =@{A} {[a := b]} c.
Proof.
  rewrite 2 fn_lookup_singleton_case.
  destruct_decide (decide (a = c)); case_decide; congruence.
Qed.


Lemma snds_propogate_subst_subseteq {n} (v : vec _ n) :
  (propogate_subst v).*2 ⊆ v.*2.
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite list_subseteq_cons_iff.
  split; [constructor|].
  rewrite IHn.
  rewrite vec_to_list_map.
  rewrite snds_prod_map.
  intros _k (k & -> & Hk)%elem_of_list_fmap.
  rewrite fn_lookup_singleton_case.
  case_decide; [constructor|].
  now constructor.
Qed.


Lemma subst_by_vec_propogate_subst_idemp {n} (v : vec _ n) p :
  subst_by_vec (propogate_subst v) (subst_by_vec (propogate_subst v) p) =
  subst_by_vec (propogate_subst v) p.
Proof.
  revert p;
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  intros p.
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite (fn_lookup_singleton_case _ _ p).
  case_decide as Hip.
  - subst p.
    rewrite fn_lookup_singleton_ne_strong; [apply IHn|].
    intros Hio.
    symmetry.
    destruct (subst_by_vec_case
      (propogate_subst (vmap (prod_map {[i := o]} {[i := o]}) v)) o)
      as [[_ Hin]|[_ ->]]; [|done].
    intros Heq.
    rewrite Heq in Hin.
    apply snds_propogate_subst_subseteq in Hin.
    rewrite vec_to_list_map, snds_prod_map in Hin.
    apply elem_of_list_fmap in Hin as (k & Hk & _).
    rewrite fn_lookup_singleton_case in Hk.
    case_decide; done.
  - rewrite fn_lookup_singleton_ne_strong; [apply IHn|].
    intros Hio.
    symmetry.
    destruct (subst_by_vec_case
      (propogate_subst (vmap (prod_map {[i := o]} {[i := o]}) v)) p)
      as [[_ Hin]|[_ ->]]; [|done].
    intros Heq.
    rewrite Heq in Hin.
    apply snds_propogate_subst_subseteq in Hin.
    rewrite vec_to_list_map, snds_prod_map in Hin.
    apply elem_of_list_fmap in Hin as (k & Hk & _).
    rewrite fn_lookup_singleton_case in Hk.
    case_decide; done.
Qed.

(* Lemma subst_by_vec_propogate_subst_do_subst {n} (v : vec (positive * positive) n)
  i o p :
  (i, o) ∈ vec_to_list v ->
  subst_by_vec (propogate_subst v) p =
  subst_by_vec (propogate_subst v) ({[i := o]} p).
Proof.
  revert i o p;
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i', o') v] using vec_S_inv.
  intros i o p.
  cbn [vec_to_list].
  rewrite elem_of_cons.
  intros [[= <- <-]| Hio];
  [cbn; now rewrite fn_lookup_singleton_idemp|].
   *)

Lemma subst_by_vec_filter_not_id {n} (v : vec _ n) p :
  subst_by_vec v p =
  subst_by_vec (list_to_vec (filter (λ io, io.1 <> io.2) (vec_to_list v))) p.
Proof.
  revert p; induction v as [|(i, o) n v IHv]; [done|].
  intros p.
  cbn.
  case_decide; [cbn; apply IHv|].
  subst.
  rewrite fn_lookup_singleton_id.
  apply IHv.
Qed.

Lemma subst_by_vec_helper_bcons_true_id {n}
  (v : vec _ n) p :
  Forall (fun io =>
    io.1 = io.2 \/ (io.1 = bcons false (pos_tail io.1)
      /\ io.2 = bcons true (pos_tail io.1))) v ->
  subst_by_vec v (bcons true p) = bcons true p.
Proof.
  intros Hall.
  rewrite subst_by_vec_filter_not_id.
  apply subst_by_vec_notin.
  rewrite not_elem_of_list_fmap.
  intros io Hio.
  rewrite vec_to_list_to_vec in Hio.
  apply elem_of_list_filter in Hio as [Hio Hiov].
  rewrite Forall_forall in Hall.
  apply Hall in Hiov as [|[Hio1 Hio2]]; [done|].
  rewrite Hio1.
  lia.
Qed.

(* Lemma propogate_subst_disj_alt {n} (v : vec _ n) :
  Forall (λ io, io.1 = io.2 \/ io.1 ∉ v.*2) v ->
  propogate_subst v =
  fun_to_vec (λ i,
  match list_find (λ io, io.1 = (v !!! i).1) (take i v) with
  | Some (_, io) => io
  | None => v !!! i
  end).
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn [vec_to_list].
  rewrite Forall_cons.
  intros [Hio Hv].
  cbn.
  f_equal.
  rewrite IHn.
  - apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    rewrite vec_to_list_map.
    rewrite <- fmap_take, list_find_fmap.
    cbn.
  - rewrite vec_to_list_map.
    rewrite Forall_fmap.
    rewrite snds_prod_map.
    rewrite Forall_forall in Hv |- *.
    intros io' Hio'v.
    apply Hv in Hio'v as Hio'.
    cbn in *.
    simpl.
    destruct Hio as [-> | Hio].
    + rewrite 2 fn_lookup_singleton_id.
      rewrite list_fmap_id' by now intros; rewrite fn_lookup_singleton_id.
      destruct Hio' as [?|Hio']; [now left|].
      right.
      eauto using elem_of_list.
    + destruct Hio' as [Hio'|Hio']; [now left; f_equal|].

      rewrite fn_lookup_singleton_case.

      case_decide as Hii'.
      *
      split; [done|].

    simpl in *.
    simpl. *)

Lemma vzip_like_vmap {n} i o (v : vec _ n) :
  Forall (λ io, io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1)
       ∧ io.2 = bcons true (pos_tail io.1)) ((i, o) :: v) ->
  Forall (λ io, io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1)
       ∧ io.2 = bcons true (pos_tail io.1))
  (vmap (prod_map {[i := o]} {[i := o]}) v).
Proof.
  rewrite Forall_cons.
  intros [Hio Hv].
  cbn in *.
  rewrite vec_to_list_map, Forall_fmap.
  apply (Forall_impl _ _ _ Hv).
  intros [i' o'].
  cbn.
  intros [->|Hio']; [now left; f_equal|].
  destruct i'; try easy.
  cbn in *.
  destruct Hio' as [_ ->].
  destruct Hio as [->|Hio]; [right; now rewrite 2 fn_lookup_singleton_id|].
  destruct i; try easy.
  cbn in Hio.
  destruct Hio as [_ ->].
  rewrite fn_lookup_singleton_case.
  rewrite fn_lookup_singleton_ne by lia.
  case_decide as Hi; [|by auto].
  revert Hi.
  intros [= <-].
  now left.
Qed.


Lemma propogate_subst_vmap_bcons_false_true_vzip_like {n}
  (v : vec _ n) :
  Forall (fun io =>
    io.1 = io.2 \/ (io.1 = bcons false (pos_tail io.1)
      /\ io.2 = bcons true (pos_tail io.1))) v ->
  Forall (fun io =>
    io.1 = io.2 \/ (io.1 = bcons false (pos_tail io.1)
      /\ io.2 = bcons true (pos_tail io.1)))
    (propogate_subst v).
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite 2 Forall_cons.
  cbn.
  intros [Hio Hv].
  split; [exact Hio|].
  apply IHn.
  clear IHn.
  now apply vzip_like_vmap, Forall_cons.
Qed.





(*
Lemma propogate_subst_vmap_bcons_false_true_vzip {n}
  (v : vec positive n) :
  propogate_subst
    (vmap (prod_map (bcons false) (bcons true))
      (vzip v v)) =
  fun_to_vec (λ i,
  if decide (v !!! i ∈ take i v) then
    (bcons true $ Pos.of_succ_nat i, bcons true $ Pos.of_succ_nat i)
  else
    (bcons false $ Pos.of_succ_nat i, bcons true $ Pos.of_succ_nat i)).
Proof. *)



Lemma vzip_like_vmap_strong {n} i o (v : vec _ n) :
  Forall (λ io, (io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1))
       ∧ io.2 = bcons true (pos_tail io.1)) ((i, o) :: v) ->
  Forall (λ io, (io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1))
       ∧ io.2 = bcons true (pos_tail io.1))
  (vmap (prod_map {[i := o]} {[i := o]}) v).
Proof.
  rewrite Forall_cons.
  intros [Hio Hv].
  cbn in *.
  rewrite vec_to_list_map, Forall_fmap.
  apply (Forall_impl _ _ _ Hv).
  intros [i' o'].
  cbn.
  intros [[->|Hio'] Ho'].
  - split; [now left; f_equal|].
    destruct Hio as [[-> | ->] Ho]; [now rewrite fn_lookup_singleton_id|].
    cbn.
    rewrite Ho'.
    rewrite fn_lookup_singleton_ne by lia.
    done.
  - destruct i'; try easy.
    cbn in *.
    subst o'.
    destruct Hio as [[-> | Hi] Hio]; [now rewrite !fn_lookup_singleton_id; auto|].
    destruct i; try easy.
    cbn in Hio.
    subst o.
    rewrite fn_lookup_singleton_case.
    rewrite fn_lookup_singleton_ne by lia.
    case_decide as Hii'; [|by auto].
    revert Hii'.
    intros [= <-].
    auto.
Qed.


Lemma propogate_subst_vmap_bcons_false_true_vzip_like_strong {n}
  (v : vec _ n) :
  Forall (λ io, (io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1))
       ∧ io.2 = bcons true (pos_tail io.1)) v ->
  Forall (λ io, (io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1))
       ∧ io.2 = bcons true (pos_tail io.1))
    (propogate_subst v).
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite 2 Forall_cons.
  cbn.
  intros [Hio Hv].
  split; [exact Hio|].
  apply IHn.
  clear IHn.
  now apply vzip_like_vmap_strong, Forall_cons.
Qed.


Lemma propogate_subst_vmap_bcons_false_true_vzip {n}
  (v : vec positive n) :
  Forall (fun io =>
    io.1 = io.2 \/ (io.1 = bcons false (pos_tail io.1)
      /\ io.2 = bcons true (pos_tail io.1)))
    (propogate_subst
    (vmap (prod_map (bcons false) (bcons true))
      (vzip v v))).
Proof.
  apply propogate_subst_vmap_bcons_false_true_vzip_like.
  rewrite vec_to_list_map, vec_to_list_zip_with.
  rewrite Forall_fmap, Forall_lookup.
  intros k (i, o) Hio%lookup_zip_Some.
  assert (i = o) as -> by now destruct Hio; congruence.
  simpl.
  now right.
Qed.


Lemma subst_by_vec_helper_bcons_false {n}
  (v : vec _ n) p :
  Forall (λ io, (io.1 = io.2
     ∨ io.1 = bcons false (pos_tail io.1))
       ∧ io.2 = bcons true (pos_tail io.1)) v ->
  subst_by_vec v (bcons false p) =
  if decide (bcons false p ∈ (vec_to_list v).*1)
    then bcons true p else bcons false p.
Proof.
  intros Hall.
  revert p; induction n as [|n IHn]; [now induction v using vec_0_inv|].
  intros p.
  induction v as [(i, o) v] using vec_S_inv.
  cbn in *.
  apply Forall_cons in Hall as Hall'.
  destruct Hall' as [Hio Hv].
  cbn in Hio.
  destruct Hio as [[<-|Hi] Ho].
  - rewrite fn_lookup_singleton_id.
    rewrite IHn by done.
    apply decide_ext.
    rewrite elem_of_cons.
    enough(p~0 <> i) by tauto.
    now destruct i.
  - subst o.
    destruct i; try now contradict Hi.
    cbn.
    rewrite fn_lookup_singleton_case.
    rewrite (decide_ext _ _ _ _ (inj_iff xO i p)).
    case_decide as Hip.
    + subst p.
      rewrite decide_True by constructor.
      apply subst_by_vec_helper_bcons_true_id.
      apply (Forall_impl _ _ _ Hv).
      intros [i' o'].
      cbn.
      destruct o'; try easy.
      cbn.
      destruct i'; cbn; firstorder congruence.
    + rewrite IHn by done.
      apply decide_ext.
      rewrite elem_of_cons.
      enough(p~0 <> i~0) by tauto.
      congruence.
Qed.

(* FIXME: Move *)
Lemma list_subseteq_antisymm {A} (l l' : list A) :
  l ⊆ l' -> l' ⊆ l -> l ≡ l'.
Proof.
  firstorder.
Qed.

Lemma fsts_propogate_subst_subseteq {n} (v : vec _ n) :
  (propogate_subst v).*1 ⊆ v.*1 ++ v.*2.
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite list_subseteq_cons_iff.
  split; [now constructor|].
  rewrite IHn.
  rewrite vec_to_list_map, fsts_prod_map, snds_prod_map.
  clear IHn.
  intros k.
  rewrite elem_of_app.
  rewrite 2 elem_of_list_fmap.
  setoid_rewrite fn_lookup_singleton_case.
  firstorder case_decide; set_solver.
Qed.

Lemma fsts_propogate_subst_supseteq {n} (v : vec _ n) :
  v.*1 ⊆ (propogate_subst v).*1.
Proof.
  induction n as [|n IHn]; [now induction v using vec_0_inv|].
  induction v as [(i, o) v] using vec_S_inv.
  cbn.
  rewrite list_subseteq_cons_iff.
  split; [now constructor|].
  etransitivity. 2:{
    apply list_subseteq_skip.
    apply IHn.
  }
  rewrite vec_to_list_map, fsts_prod_map.
  intros k.
  rewrite elem_of_cons.
  rewrite (elem_of_list_fmap {[_:=_]}).
  setoid_rewrite fn_lookup_singleton_case.
  intros Hk.
  destruct_decide (decide (k = i)); [now left|].
  right.
  exists k.
  rewrite decide_False by done.
  done.
Qed.

Lemma subst_by_vec_propogate_subst_vmap_bcons_false_true_vzip {n}
  (v : vec positive n) p :
  subst_by_vec (propogate_subst
    (vmap (prod_map (bcons false) (bcons true)) (vzip v v)))
    (bcons false p) =
  if decide (p ∈ vec_to_list v) then bcons true p else bcons false p.
Proof.
  rewrite subst_by_vec_helper_bcons_false.
  - apply decide_ext.
    split. 2:{
      intros Hp.
      apply fsts_propogate_subst_supseteq.
      rewrite vec_to_list_map, fsts_prod_map.
      apply elem_of_list_fmap_1.
      rewrite vec_to_list_zip_with.
      now rewrite fst_zip by done.
    }
    intros Hp%fsts_propogate_subst_subseteq.
    rewrite vec_to_list_map, fsts_prod_map, snds_prod_map,
      vec_to_list_zip_with, fst_zip, snd_zip in Hp by done.
    set_solver.
  - apply propogate_subst_vmap_bcons_false_true_vzip_like_strong.
    rewrite vec_to_list_map, Forall_fmap.
    rewrite vec_to_list_zip_with.
    rewrite Forall_zip_with by done.
    apply Forall_Forall2_diag.
    rewrite Forall_forall.
    auto.
Qed.

Lemma compose_sized_graphs_unsafe_to_compose_sized_graphs {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  vertices tgl ∖ list_to_set (outputs tgl) ##
  vertices tgr ∖ list_to_set (inputs tgr) ->
  hyperedges tgl ##ₘ hyperedges tgr ->
  compose_sized_graphs_unsafe tgl tgr ≡ᵢ compose_sized_graphs tgl tgr.
Proof.
  intros Hoi Hvdisj Hdisj.
  rewrite <- compose_sized_graphs_aux_to_compose_sized_graphs_unsafe by done.
  rewrite <- compose_sized_graphs_alt_aux_correct by done.
  rewrite <- compose_sized_graphs_alt_correct.
  apply sized_add_top_loops_struct_sized_isomorphic_strong.
  cbn.
  rewrite 4 vsplitl_app.
  transitivity (relabel_sized_graph
     (subst_by_vec
        (propogate_subst
           (vzip (vmap (bcons false) (outputs tgl))
              (vmap (bcons true) (inputs tgr)))))
     (swapped_stack_sized_graphs_aux (relabel_sized_graph (bcons false) tgl)
      (relabel_sized_graph (bcons true) tgr))). 2:{
    set (f := (fun i => if decide (i ∈ dom (hyperedges tgl)) then bcons false i else bcons true i)).
    assert (Hf : Inj eq eq f). 1:{
      intros i j.
      unfold f.
      do 2 case_decide; now intros ?%(inj2 bcons).
    }
    rewrite (sized_isomorphic_reindex_sized_graph f).
    apply eq_reflexivity.
    rewrite reindex_relabel_sized_graph.
    rewrite reindex_swapped_stack_sized_graphs_aux by apply _.
    f_equal.
    unfold swapped_stack_sized_graphs.
    rewrite 2 reindex_relabel_sized_graph.
    f_equal; f_equal.
    - apply reindex_sized_graph_ext_strong.
      intros i _ Hi%elem_of_dom_2.
      unfold f.
      now rewrite decide_True by done.
    - apply reindex_sized_graph_ext_strong.
      intros i _ Hi%elem_of_dom_2.
      unfold f.
      rewrite map_disjoint_dom in Hdisj.
      now rewrite decide_False by now intros ?%Hdisj.
  }
  set (f := (fun i =>
    if decide (i ∈ vertices tgl ∖ list_to_set (outputs tgl)) then
    bcons false i else bcons true i)).
  assert (Hf : Inj eq eq f). 1:{
    intros i j.
    unfold f.
    do 2 case_decide; now intros ?%(inj2 bcons).
  }
  rewrite (sized_isomorphic_relabel_sized_graph f).
  rewrite relabel_sized_graph_compose, 2 relabel_swapped_stack_sized_graphs_aux,
    2 relabel_sized_graph_compose.
  apply eq_reflexivity.
  f_equal.
  - apply relabel_sized_graph_ext_strong.
    intros i Hi.
    cbn.
    rewrite Hoi.
    rewrite vzip_map.
    rewrite subst_by_vec_id.
    rewrite subst_by_vec_propogate_subst_vmap_bcons_false_true_vzip.
    case_decide as Hii.
    + cbn.
      unfold f.
      now rewrite Hoi, decide_False by now rewrite elem_of_difference, elem_of_list_to_set.
    + unfold f.
      now rewrite Hoi, decide_True by now rewrite elem_of_difference, elem_of_list_to_set.
  - apply relabel_sized_graph_ext_strong.
    intros i Hi.
    cbn.
    rewrite Hoi.
    rewrite vzip_map.
    rewrite subst_by_vec_id.
    rewrite subst_by_vec_helper_bcons_true_id by
      apply propogate_subst_vmap_bcons_false_true_vzip.
    unfold f.
    case_decide as Hii; [|done].
    apply Hvdisj in Hii as Hii'.
    rewrite elem_of_difference in Hii, Hii'.
    rewrite Hoi in Hii.
    tauto.
Qed.


Lemma compose_sized_graphs_unsafe'_to_compose_sized_graphs {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  vertices tgl ∖ list_to_set (outputs tgl) ##
  vertices tgr ∖ list_to_set (inputs tgr) ->
  hyperedges tgl ##ₘ hyperedges tgr ->
  compose_sized_graphs_unsafe' tgl tgr ≡ᵢ compose_sized_graphs tgl tgr.
Proof.
  intros.
  etransitivity.
  - apply (subrel' scohg_vert_eq).
    apply compose_sized_graphs_unsafe'_correct.
  - now apply compose_sized_graphs_unsafe_to_compose_sized_graphs.
Qed.




Lemma stack_sized_graphs_id_0_l {n m} (scohg : SizedCospanHyperGraph N T n m) :
  stack_sized_graphs (id_sized_graph 0) scohg ≡ᵢ scohg.
Proof.
  symmetry.
  rewrite (sized_iso_relabel_reindex _ xI xI) at 1.
  apply eq_reflexivity.
  unfold stack_sized_graphs, stack_sized_graphs_aux.
  cbn.
  change (relabel_hg (bcons false) _) with (∅ :> HyperGraph T).
  apply scohg_ext; [|done..].
  cbn.
  apply hg_ext; [|set_solver].
  symmetry.
  apply map_empty_union.
Qed.

Lemma empty_sized_graph_0_0_eq {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg.(hedges) = ∅ ->
  scohg'.(hedges) = ∅ ->
  n = 0 -> m = 0 ->
  scohg = scohg'.
Proof.
  destruct scohg, scohg'; cbn.
  intros; subst.
  inv_all_vec_fin; f_equal; done.
Qed.

Lemma delta_spider_sized_graph_alt n m k :
  sized_isomorphic (T:=T) (delta_spider_sized_graph n m)
    (mk_scohg (mk_hg ∅ {[k]}) (fun_to_vec (λ _, k)) (fun_to_vec (λ _, k))).
Proof.
  rewrite (sized_iso_relabel_reindex (delta_spider_sized_graph n m) (λ p, pos_add_N p (Pos.pred_N k)) id
    (Hfe:=(ltac:(intros ? ?; lia)))).
  apply eq_reflexivity.
  apply scohg_ext.
  - apply hg_ext; [done|].
    cbn -[set_map].
    rewrite set_map_singleton_L.
    f_equal; lia.
  - apply vec_eq; intros i.
    cbn.
    rewrite vlookup_map, 2 lookup_fun_to_vec.
    lia.
  - apply vec_eq; intros i.
    cbn.
    rewrite vlookup_map, 2 lookup_fun_to_vec.
    lia.
Qed.

Lemma n_stack_delta_spider_sized_graph_alt k n m :
  forall offset,
  n_stack_sized_graphs k (delta_spider_sized_graph (T:=T) n m) ≡ᵢ
  mk_scohg (mk_hg ∅ (list_to_set (Pos.of_succ_nat <$> seq offset k)))
    (fun_to_vec (λ i, Pos.of_succ_nat (offset + i / n)))
    (fun_to_vec (λ i, Pos.of_succ_nat (offset + i / m))).
Proof.
  induction k; [done|].
  cbn.
  intros offset.
  rewrite (delta_spider_sized_graph_alt n m (Pos.of_succ_nat offset)) at 1.
  rewrite (IHk (S offset)).
  rewrite <- stack_sized_graphs_aux_to_stack_sized_graphs_disjoint; [|done|].
  2:{
    rewrite vertices_almost_empty_sized_graph.
    rewrite vec_to_list_app, 2 (vec_to_list_fun_to_vec (λ _, Pos.of_succ_nat offset)).
    rewrite list_to_set_app.
    rewrite 2 (fmap_const _ (Pos.of_succ_nat offset)).
    rewrite vertices_almost_empty_sized_graph.
    rewrite vec_to_list_app, 2 (vec_to_list_fun_to_vec (λ i, Pos.of_succ_nat (_ + (i / _)))).
    set_unfold.
    intros ?.
    rewrite 2 elem_of_replicate.
    setoid_rewrite elem_of_seq.
    set_unfold; naive_solver lia.
  }
  apply eq_reflexivity.
  apply scohg_ext.
  - done.
  - cbn.
    rewrite fun_to_vec_plus.
    f_equal.
    + apply fun_to_vec_ext_mor.
      intros i.
      cbn.
      rewrite fin_to_nat_L.
      rewrite Nat.div_small by apply fin_to_nat_lt.
      lia.
    + apply fun_to_vec_ext_mor.
      intros i.
      cbn.
      rewrite fin_to_nat_R.
      rewrite <- (Nat.mul_1_l n) at 3.
      rewrite Nat.div_add_l by (pose proof (fin_to_nat_lt i); lia).
      lia.
  - cbn.
    rewrite fun_to_vec_plus.
    f_equal.
    + apply fun_to_vec_ext_mor.
      intros i.
      cbn.
      rewrite fin_to_nat_L.
      rewrite Nat.div_small by apply fin_to_nat_lt.
      lia.
    + apply fun_to_vec_ext_mor.
      intros i.
      cbn.
      rewrite fin_to_nat_R.
      rewrite <- (Nat.mul_1_l m) at 3.
      rewrite Nat.div_add_l by (pose proof (fin_to_nat_lt i); lia).
      lia.
Qed.

Lemma permute_sized_graph_relabel_sized_graph {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') f (scohg : SizedCospanHyperGraph N T n m) :
  permute_sized_graph fl fr (relabel_sized_graph f scohg) = relabel_sized_graph f (permute_sized_graph fl fr scohg).
Proof.
  subst.
  rewrite 2 (permute_sized_graph_alt fl fr).
  apply scohg_ext; [done|..].
  - cbn.
    apply vec_eq.
    intros i.
    rewrite vlookup_map, 2 lookup_permute_vec, vlookup_map.
    done.
  - cbn.
    apply vec_eq.
    intros i.
    rewrite vlookup_map, 2 lookup_permute_vec, vlookup_map.
    done.
Qed.

Lemma permute_sized_graph_reindex_sized_graph {n m n' m'}
  (fl : fin n -> fin n')
  (fr : fin m -> fin m')  f (scohg : SizedCospanHyperGraph N T n m) :
  permute_sized_graph fl fr (reindex_sized_graph f scohg) = reindex_sized_graph f (permute_sized_graph fl fr scohg).
Proof.
  done.
Qed.

Lemma permute_sized_graph_sized_isomorphic {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') : Proper (sized_isomorphic ==> sized_isomorphic) (permute_sized_graph (T:=T) fl fr).
Proof.
  subst.
  intros scohg scohg' Heq.
  induction Heq as [scohg fv fe Hfv Hfe].
  rewrite (permute_sized_graph_relabel_sized_graph fl fr), permute_sized_graph_reindex_sized_graph by done.
  now constructor.
Qed.

#[export] Instance permute_sized_graph_scohg_vert_eq {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') :
  Proper (scohg_vert_eq ==> scohg_vert_eq) (permute_sized_graph (T:=T) fl fr).
Proof.
  intros scohg scohg' Heq.
  rewrite scohg_vert_eq_alt_vertices in Heq.
  rewrite scohg_vert_eq_alt_vertices.
  subst.
  rewrite 2 (vertices_permute_sized_graph fl fr).
  cbn.
  destruct Heq as (<- & <- & <- & <-).
  done.
Qed.

#[export] Instance permute_sized_graph_struct_sized_isomorphic {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') :
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic) (permute_sized_graph (T:=T) fl fr).
Proof.
  apply proper_struct_sized_isomorphic_of_vert_eq_unary.
  - now apply permute_sized_graph_scohg_vert_eq.
  - now apply permute_sized_graph_sized_isomorphic.
Qed.

(* FIXME: Move *)
Lemma fin_perm_cancel_comm {n} (f g : fin n -> fin n)
  (Hfg : Cancel eq f g) : Cancel eq g f.
Proof.
  intros x.
  assert (Hg : Inj eq eq g) by apply cancel_inj.
  apply finite.finite_inj_surj in Hg as Hg'; [|done].
  destruct (Hg' x) as [y Hy].
  apply (f_equal f) in Hy as Hy'.
  rewrite Hfg in Hy'.
  congruence.
Qed.

Lemma fin_perm_inv_cancel {n} (f g : fin n -> fin n)
  {Hfg : Cancel eq f g} : Cancel eq (fin_perm_inv f) (fin_perm_inv g).
Proof.
  apply fin_perm_cancel_comm in Hfg as Hgf.
  assert (Hf : Inj eq eq f) by apply cancel_inj.
  assert (Hg : Inj eq eq g) by apply cancel_inj.
  intros i.
  rewrite (fin_perm_inv_spec _).
  symmetry.
  rewrite (fin_perm_inv_spec _).
  apply Hgf.
Qed.

Lemma permute_sized_graph_alt_cancel {n m n' m'}
  (fl : fin n -> fin n') (gl : fin n' -> fin n)
  (fr : fin m -> fin m') (gr : fin m' -> fin m)
  {Hfgl : Cancel eq fl gl} {Hfgr : Cancel eq fr gr}
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  permute_sized_graph fl fr scohg =
  mk_scohg scohg
    (permute_vec gl scohg.(inputs))
    (permute_vec gr scohg.(outputs)).
Proof.
  subst.
  pose proof @cancel_inj.
  apply fin_perm_cancel_comm in Hfgl as ?.
  apply fin_perm_cancel_comm in Hfgr as ?.
  rewrite (permute_sized_graph_alt fl fr).
  f_equal; apply permute_vec_ext, reflexivity.
  - intros i.
    apply (fin_perm_inv_spec fl).
    apply Hfgl.
  - intros i.
    apply (fin_perm_inv_spec fr).
    apply Hfgr.
Qed.



Lemma delta_spider_sized_graph_bundled_alt k n m :
  delta_spider_sized_graph_bundled (T:=T) k n m ≡ᵢ
  copy_sized_graph k (delta_spider_sized_graph n m).
Proof.
  unfold copy_sized_graph.
  erewrite (permute_sized_graph_struct_sized_isomorphic fin_prod_comm fin_prod_comm
    (Nat.mul_comm _ _) (Nat.mul_comm _ _) _) by
    (apply (n_stack_delta_spider_sized_graph_alt _ _ _ 0)).
  rewrite (permute_sized_graph_alt_cancel _ _ _ _) by lia.
  apply eq_reflexivity.
  apply scohg_ext.
  - done.
  - apply vec_eq.
    intros i.
    cbn.
    rewrite lookup_permute_vec, 2 lookup_fun_to_vec.
    pose proof fin_to_nat_lt i.
    induction i as [il ir] using fin_mul_ind.
    rewrite fin_prod_comm_prod.
    rewrite 2 fin_to_nat_prod.
    rewrite Nat.div_add_l by lia.
    rewrite (Nat.add_comm (_ * _) _), Nat.Div0.mod_add.
    pose proof fin_to_nat_lt il.
    pose proof fin_to_nat_lt ir.
    rewrite Nat.div_small, Nat.mod_small by lia.
    lia.
  - apply vec_eq.
    intros i.
    cbn.
    rewrite lookup_permute_vec, 2 lookup_fun_to_vec.
    pose proof fin_to_nat_lt i.
    induction i as [il ir] using fin_mul_ind.
    rewrite fin_prod_comm_prod.
    rewrite 2 fin_to_nat_prod.
    rewrite Nat.div_add_l by lia.
    rewrite (Nat.add_comm (_ * _) _), Nat.Div0.mod_add.
    pose proof fin_to_nat_lt il.
    pose proof fin_to_nat_lt ir.
    rewrite Nat.div_small, Nat.mod_small by lia.
    lia.
Qed.

End StackCompose.






Lemma hypergraph_empty_union {T} (hg : HyperGraph T) : ∅ ∪ hg = hg.
Proof.
  apply hg_ext.
  - apply map_empty_union.
  - unfold union, hypergraph_union.
    cbn -[union].
    apply union_empty_l_L.
Qed.

(* FIXME: Move *)
Lemma vmap_vzip_with {A B C D} (f : C -> D) (g : A -> B -> C) {n}
  (v w : vec _ n) :
  vmap f (vzip_with g v w) = vzip_with (λ a b, f (g a b)) v w.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.
Lemma fst_vzip {A} {n} (v w : vec A n) :
  vmap fst (vzip_with pair v w) = v.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.
Lemma snd_vzip {A} {n} (v w : vec A n) :
  vmap snd (vzip_with pair v w) = w.
Proof.
  induction n; inv_all_vec_fin; cbn in *; congruence.
Qed.

Lemma propogate_subst_vmap_bcons_false_true_NoDup_l
  {n} (v w : vec positive n) : NoDup v ->
  propogate_subst (vmap (prod_map (bcons false) (bcons true)) (vzip v w)) =
  vmap (prod_map (bcons false) (bcons true)) (vzip v w).
Proof.
  intros Hv.
  induction n; [inv_all_vec_fin; done|].
  inv_vec v; intros vh v.
  inv_vec w; intros wh w.
  cbn.
  intros [Hvh Hv]%NoDup_cons.
  f_equal.
  rewrite <- IHn at 2 by done.
  f_equal.
  apply vmap_id'.
  intros [k l].
  rewrite vec_to_list_map, vec_to_list_zip_with.
  rewrite elem_of_list_fmap.
  intros ([i j] & [= -> ->] & Hij).
  apply elem_of_zip_with in Hij as (i' & j' & [= <- <-] & Hi & Hj).
  cbn.
  rewrite fn_lookup_singleton_ne by set_solver.
  rewrite fn_lookup_singleton_ne by lia.
  done.
Qed.


Lemma compose_sized_graphs_id_sized_graph_l_aux {T n m} (scohg : SizedCospanHyperGraph N T n m) :
  compose_sized_graphs (id_sized_graph n) scohg ≡ᵥ relabel_sized_graph (bcons true) (reindex_sized_graph (bcons true) scohg).
Proof.
  unfold compose_sized_graphs.
  cbn.
  rewrite vzip_map.
  rewrite propogate_subst_vmap_bcons_false_true_NoDup_l by (rewrite vec_to_list_map, vec_to_list_seq;
    apply (NoDup_fmap _), NoDup_seq).
  rewrite <- vzip_map.
  erewrite relabel_sized_graph_ext. 2:{
    intros i.
    rewrite subst_by_vec_disj by (rewrite <- 2 vec_to_list_map,
      fst_vzip, snd_vzip, !vec_to_list_map; set_solver).
    done.
  }
  apply scohg_vert_eq_alt_vertices;
  split_and!.
  - cbn.
    apply vec_eq; intros i.
    rewrite vlookup_map.
    unfold Pmap_map.
    eenough (_ !! _ = Some _) as -> by done.
    apply elem_of_list_to_map.
    + rewrite <- vec_to_list_map, fst_vzip, 2 vec_to_list_map, vec_to_list_seq.
      apply (NoDup_fmap _), (NoDup_fmap _), NoDup_seq.
    + apply elem_of_vlookup.
      exists i.
      rewrite vlookup_zip_with.
      done.
  - cbn.
    apply vmap_id'.
    rewrite vec_to_list_map.
    intros _ (i & -> & Hi)%elem_of_list_fmap.
    unfold Pmap_map.
    enough (_ !! _ = None) as -> by done.
    apply not_elem_of_list_to_map.
    rewrite <- vec_to_list_map, fst_vzip, vec_to_list_map.
    set_solver.
  - cbn.
    rewrite fmap_empty, kmap_empty, map_empty_union.
    rewrite kmap_fmap'.
    erewrite map_fmap_ext; [apply map_fmap_id|].
    intros k [[t i] o].
    cbn.
    rewrite lookup_fmap.
    rewrite fmap_Some.
    intros ([[t' i'] o'] & _ & [= -> -> ->]).
    f_equal; [f_equal|]; apply list_fmap_id';
    intros _ (a & -> & _)%elem_of_list_fmap;
    unfold Pmap_map;
    enough (_ !! _ = None) as -> by done;
    apply not_elem_of_list_to_map;
    rewrite <- vec_to_list_map, fst_vzip, vec_to_list_map;
    set_solver.
  - rewrite vertices_relabel_sized_graph.
    rewrite 2 vertices_vertices_hg_decomp.
    cbn.
    rewrite vertices_hg_add_vertices.
    unfold disj_union, hypergraph_disjunion.
    cbn.
    change (reindex_hg _ (relabel_hg _ ∅)) with (∅ :> HyperGraph T).
    rewrite hypergraph_empty_union.
    change (vertices_hg ∅) with (∅ :> Pset).
    rewrite (union_empty_l_L _).
    rewrite (vertices_reindex_hg _), vertices_relabel_hg.
    rewrite (union_comm_L _ (_ ∖ _)).
    rewrite difference_union_L.
    rewrite 2 list_to_set_app_L.
    rewrite vertices_relabel_hg, (vertices_reindex_hg _).
    etransitivity.
    1:{
      apply (f_equal (set_map _)).
      rewrite (union_comm_L (list_to_set (vmap (bcons false) _))).
      rewrite union_assoc_L.
      rewrite (union_comm_L _ (set_map _ _)).
      rewrite <- (union_assoc_L (set_map _ _)).
      done.
    }
    rewrite set_map_union_L.
    etransitivity; [apply f_equal2|].
    1:{
      erewrite set_map_ext_L; [apply set_map_id_L|].
      intros x Hx.
      assert (exists i, x = i~1) as [i ->]. 1:{
        rewrite 2 vec_to_list_map in Hx.
        rewrite <- 2 (set_map_list_to_set_L (SA:=Pset)) in Hx.
        set_solver.
      }
      unfold Pmap_map.
      enough (_ !! _ = None) as -> by done.
      apply not_elem_of_list_to_map.
      rewrite <- vec_to_list_map, fst_vzip, vec_to_list_map; set_solver.
    }
    1:{
      instantiate (1:= (list_to_set (vmap (bcons true) (inputs scohg)))).
      apply set_eq; intros k.
      rewrite elem_of_list_to_set, elem_of_map.
      setoid_rewrite elem_of_list_to_set.
      rewrite Vector.map_map.
      setoid_rewrite elem_of_vlookup.

      split.
      - intros (_ & -> & (i & <-)).
        exists i.
        symmetry.
        unfold Pmap_map.
        eenough (_ !! _ = Some _) as -> by done.
        apply elem_of_list_to_map.
        + rewrite <- vec_to_list_map, fst_vzip, vec_to_list_map, vec_to_list_seq.
          apply (NoDup_fmap _), NoDup_seq.
        + apply elem_of_vlookup.
          exists i.
          rewrite vlookup_zip_with.
          done.
      - intros (i & <-).
        eexists.
        split; [|exists i; done].
        symmetry.
        unfold Pmap_map.
        eenough (_ !! _ = Some _) as -> by done.
        apply elem_of_list_to_map.
        + rewrite <- vec_to_list_map, fst_vzip, vec_to_list_map, vec_to_list_seq.
          apply (NoDup_fmap _), NoDup_seq.
        + apply elem_of_vlookup.
          exists i.
          rewrite vlookup_zip_with.
          done.
    }
    set_solver.
Qed.


Lemma compose_sized_graphs_id_sized_graph_l {T n m} (scohg : SizedCospanHyperGraph N T n m) :
  compose_sized_graphs (id_sized_graph n) scohg ≡ᵢ scohg.
Proof.
  rewrite compose_sized_graphs_id_sized_graph_l_aux.
  rewrite <- sized_iso_relabel_reindex; [done|apply _..].
Qed.

Lemma stack_sized_graphs_id_sized_graph {T} n m :
  sized_isomorphic (T:=T) (stack_sized_graphs (id_sized_graph n) (id_sized_graph m))
    (id_sized_graph (n + m)).
Proof.
  symmetry.
  apply sized_isomorphic_exists.
  exists (fun i => if decide (pos_to_nat_pred i < n) then i~0 else (pos_sub_N i (N.of_nat n))~1), id.
  split_and!.
  - intros i j; do 2 case_decide; lia.
  - apply _.
  - eenough (Hen : _) by (apply scohg_ext; [reflexivity|..]; apply Hen).
    cbn.
    apply vec_eq.
    intros i.
    induction i as [i|i] using fin_add_inv.
    + rewrite lookup_vapp_L.
      rewrite 4 vlookup_map, 2 vlookup_seq.
      pose proof (fin_to_nat_lt i).
      rewrite fin_to_nat_L.
      case_decide; [|lia].
      done.
    + rewrite lookup_vapp_R.
      rewrite 4 vlookup_map, 2 vlookup_seq.
      pose proof (fin_to_nat_lt i).
      rewrite fin_to_nat_R.
      case_decide; lia.
Qed.

 *)

End StackCompose.