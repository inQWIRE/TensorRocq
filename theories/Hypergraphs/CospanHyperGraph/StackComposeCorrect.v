From stdpp Require Export pmap gmap decidable.
From TensorRocq Require Import CospanHyperGraph.Definitions HyperGraph Aux_pos Syntax Aux_stdpp.


Section StackCompose.


  Context {T : Type}.

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

#[export] Instance stack_graphs_isomorphic {n m n' m'} :
  Proper (isomorphic ==> isomorphic ==> isomorphic)
    (@stack_graphs T n m n' m').
Proof.
  intros cohg1 cohg1' (fv1 & fe1 & Hfv1 & Hfe1 & ->)%isomorphic_exists
    cohg2 cohg2' (fv2 & fe2 & Hfv2 & Hfe2 & ->)%isomorphic_exists.
  rewrite stack_graphs_relabel, (stack_graphs_reindex _ _ _ _).
  apply (iso_relabel_reindex _ _ _).
Qed.


#[export] Instance stack_graphs_struct_isomorphic_Proper {n m n' m'} :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@stack_graphs T n m n' m').
Proof.
  apply proper_struct_isomorphic_of_vert_eq_binary.
  - apply _.
  - intros ? ? ? ? ? ?.
    now apply stack_graphs_isomorphic.
Qed.


Lemma stack_graphs_struct_isomorphic {n m n' m'} (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') :
  cohg1 ≡ᵢ cohg1' -> cohg2 ≡ᵢ cohg2' ->
  stack_graphs cohg1 cohg2 ≡ᵢ stack_graphs cohg1' cohg2'.
Proof.
  now intros; apply stack_graphs_struct_isomorphic_Proper.
Qed.


Lemma relabel_swapped_stack_graphs_aux {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') f :
  relabel_graph f (swapped_stack_graphs_aux cohg cohg') =
  swapped_stack_graphs_aux (relabel_graph f cohg) (relabel_graph f cohg').
Proof.
  apply cohg_ext.
  - cbn; apply relabel_hg_union.
  - cbn.
    now rewrite Vector.map_append.
  - cbn.
    now rewrite Vector.map_append.
Qed.

Lemma swapped_stack_graphs_relabel {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') ft fb :
  swapped_stack_graphs (relabel_graph ft cohg) (relabel_graph fb cohg') =
  relabel_graph (pos_map ft fb) (swapped_stack_graphs cohg cohg').
Proof.
  unfold swapped_stack_graphs.
  rewrite relabel_swapped_stack_graphs_aux.
  rewrite 2 reindex_relabel_graph, 4 relabel_graph_compose.
  done.
Qed.

Lemma reindex_swapped_stack_graphs_aux {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') f `{Hf : !Inj eq eq f} :
  reindex_graph f (swapped_stack_graphs_aux cohg cohg') =
  swapped_stack_graphs_aux (reindex_graph f cohg) (reindex_graph f cohg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  apply (reindex_hg_union _).
Qed.

Lemma swapped_stack_graphs_reindex {n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') ft fb
  `{Hft : !Inj eq eq ft, Hfb : !Inj eq eq fb} :
  swapped_stack_graphs (reindex_graph ft cohg) (reindex_graph fb cohg') =
  reindex_graph (pos_map ft fb) (swapped_stack_graphs cohg cohg').
Proof.
  unfold swapped_stack_graphs.
  rewrite (reindex_swapped_stack_graphs_aux _ _ _).
  rewrite 2 reindex_relabel_graph, 4 (reindex_graph_compose _ _).
  done.
Qed.

Lemma swapped_stack_graphs_isomorphic {n m n' m'} (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') :
  isomorphic cohg1 cohg1' -> isomorphic cohg2 cohg2' ->
  isomorphic (swapped_stack_graphs cohg1 cohg2) (swapped_stack_graphs cohg1' cohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%isomorphic_exists.
  rewrite swapped_stack_graphs_relabel, (swapped_stack_graphs_reindex _ _ _ _).
  apply (iso_relabel_reindex _ _ _).
Qed.

Lemma swapped_stack_graphs_struct_isomorphic_Proper {n m n' m'} :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@swapped_stack_graphs T n m n' m').
Proof.
  apply proper_struct_isomorphic_of_vert_eq_binary.
  - apply _.
  - intros ? ? ? ? ? ?.
    now apply swapped_stack_graphs_isomorphic.
Qed.


Lemma swapped_stack_graphs_struct_isomorphic {n m n' m'} (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') :
  cohg1 ≡ᵢ cohg1' -> cohg2 ≡ᵢ cohg2' ->
  swapped_stack_graphs cohg1 cohg2 ≡ᵢ swapped_stack_graphs cohg1' cohg2'.
Proof.
  now intros; apply swapped_stack_graphs_struct_isomorphic_Proper.
Qed.

Lemma add_top_loop_relabel_graph {n m} f `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T (S n) (S m)) :
  add_top_loop (relabel_graph f cohg) =
  relabel_graph f (add_top_loop cohg).
Proof.
  unfold add_top_loop.
  cbn.
  rewrite relabel_graph_compose.
  induction (inputs cohg) as [i ins] using vec_S_inv.
  induction (outputs cohg) as [o outs] using vec_S_inv.
  cbn.
  assert (Hfeq : forall x, ({[f o := f i]} ∘ f) x = (f ∘ {[o := i]}) x). 1:{
    intros p; cbn.
    rewrite 2 fn_lookup_singleton_case.
    rewrite (decide_ext _ _ _ _ (inj_iff f o p)).
    now case_decide.
  }
  apply cohg_ext'.
  - cbn.
    rewrite Vector.map_map.
    apply Vector.map_ext, Hfeq.
  - cbn.
    rewrite Vector.map_map.
    apply Vector.map_ext, Hfeq.
  - cbn.
    rewrite <- map_fmap_compose.
    apply map_fmap_ext.
    intros _ tio _.
    cbn.
    rewrite relabel_abs_compose.
    apply relabel_abs_ext, Hfeq.
  - cbn -[union].
    rewrite 2 set_map_union_L, 2 set_map_singleton_L.
    rewrite <- Hfeq.
    f_equal.
    rewrite set_map_compose_L.
    apply set_map_ext_L.
    intros; apply Hfeq.
Qed.

Lemma add_top_loop_reindex_graph {n m} f (cohg : CospanHyperGraph T (S n) (S m)) :
  add_top_loop (reindex_graph f cohg) =
  reindex_graph f (add_top_loop cohg).
Proof.
  unfold add_top_loop.
  rewrite reindex_relabel_graph.
  done.
Qed.

Lemma add_top_loop_struct_isomorphic {n m} (cohg cohg' : CospanHyperGraph T (S n) (S m)) :
  cohg ≡ᵢ cohg' ->
  add_top_loop cohg ≡ᵢ add_top_loop cohg'.
Proof.
  intros (fv & fe & Hfv & Hfe & Heq)%isomorphic_exists.
  rewrite <- norm_verts_vert_eq, norm_verts_add_top_loop.
  rewrite <- (norm_verts_vert_eq (add_top_loop cohg')),
    (norm_verts_add_top_loop cohg').
  rewrite Heq.
  rewrite (add_top_loop_relabel_graph _), add_top_loop_reindex_graph.
  rewrite (norm_verts_vert_eq (add_top_loop _)),
    (norm_verts_vert_eq (relabel_graph _ _)).
  apply (subrel' isomorphic).
  now constructor.
Qed.

(* FIXME: Move *)
Lemma vhd_vmap {A B} (f : A -> B) {n} (v : vec A (S n)) :
  vhd (vmap f v) = f (vhd v).
Proof.
  induction v using vec_S_inv.
  done.
Qed.
Lemma vtl_vmap {A B} (f : A -> B) {n} (v : vec A (S n)) :
  vtl (vmap f v) = vmap f (vtl v).
Proof.
  induction v using vec_S_inv.
  done.
Qed.

Lemma add_top_loop_eq_relabel {n m} (cohg : CospanHyperGraph T (S n) (S m)) :
  add_top_loop cohg =
  add_top_loop (relabel_graph {[vhd (outputs cohg) := vhd (inputs cohg)]} cohg).
Proof.
  unfold add_top_loop.
  cbn.
  rewrite 2 vhd_vmap.
  rewrite fn_lookup_singleton, fn_lookup_singleton_r.
  symmetry.
  rewrite relabel_graph_id' by now intros; rewrite fn_lookup_singleton_case; case_decide.
  apply cohg_ext'.
  - cbn.
    now rewrite vtl_vmap.
  - cbn.
    now rewrite vtl_vmap.
  - done.
  - cbn -[union difference].
    rewrite set_map_union_L, set_map_singleton_L, fn_lookup_singleton_r.
    done.
Qed.

Lemma add_top_loop_struct_isomorphic_strong {n m} (cohg cohg' : CospanHyperGraph T (S n) (S m)) :
  relabel_graph {[vhd (outputs cohg) := vhd (inputs cohg)]} cohg ≡ᵢ
  relabel_graph {[vhd (outputs cohg') := vhd (inputs cohg')]} cohg' ->
  add_top_loop cohg ≡ᵢ add_top_loop cohg'.
Proof.
  intros Hiso.
  rewrite add_top_loop_eq_relabel.
  erewrite add_top_loop_struct_isomorphic by apply Hiso.
  rewrite <- add_top_loop_eq_relabel.
  done.
Qed.

(* FIXME: Move *)
Lemma fn_lookup_singleton_id `{EqDecision A} (a b : A) :
  {[a := a]} b = b.
Proof.
  now rewrite fn_lookup_singleton_case; case_decide.
Qed.

Lemma add_top_loops_eq_relabel {n m m'}
  (cohg : CospanHyperGraph T (n + m) (n + m')) :
  add_top_loops cohg =
  add_top_loops (relabel_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs cohg)) (vsplitl (inputs cohg)))) cohg).
Proof.
  induction n; [cbn; now rewrite relabel_graph_id|].
  cbn -[propogate_subst].
  rewrite IHn.
  f_equal.
  destruct cohg as [hg ins outs].
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[propogate_subst Vector.append].
  rewrite 2 vsplitl_app.
  cbn -[propogate_subst].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  apply cohg_ext.
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

Lemma add_top_loops_struct_isomorphic {n m o}
  (cohg cohg' : CospanHyperGraph T (n + m) (n + o)) :
  cohg ≡ᵢ cohg' ->
  add_top_loops cohg ≡ᵢ add_top_loops cohg'.
Proof.
  intros Hiso.
  induction n; [done|].
  cbn.
  apply IHn.
  now apply add_top_loop_struct_isomorphic.
Qed.

Lemma add_top_loops_struct_isomorphic_strong {n m o}
  (cohg cohg' : CospanHyperGraph T (n + m) (n + o)) :
  relabel_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs cohg)) (vsplitl (inputs cohg)))) cohg ≡ᵢ
  relabel_graph (subst_by_vec (propogate_subst
    $ vzip (vsplitl (outputs cohg')) (vsplitl (inputs cohg')))) cohg' ->
  add_top_loops cohg ≡ᵢ add_top_loops cohg'.
Proof.
  intros Hiso.
  rewrite add_top_loops_eq_relabel.
  erewrite add_top_loops_struct_isomorphic by apply Hiso.
  rewrite <- add_top_loops_eq_relabel.
  done.
Qed.



Lemma compose_graphs_struct_isomorphic {n m o}
  (cohg1 cohg1' : CospanHyperGraph T n m) (cohg2 cohg2' : CospanHyperGraph T m o) :
  cohg1 ≡ᵢ cohg1' -> cohg2 ≡ᵢ cohg2' ->
  compose_graphs cohg1 cohg2 ≡ᵢ compose_graphs cohg1' cohg2'.
Proof.
  intros Heq1 Heq2.
  rewrite <- 2 compose_graphs_alt_correct.
  apply add_top_loops_struct_isomorphic.
  now apply swapped_stack_graphs_struct_isomorphic.
Qed.

Lemma relabel_graph_to_fun_to_map {n m} f (cohg : CospanHyperGraph T n m) :
  relabel_graph f cohg = relabel_graph (Pmap_map (fun_to_map f (vertices cohg))) cohg.
Proof.
  apply relabel_graph_ext_strong.
  intros i Hi.
  symmetry.
  unfold Pmap_map.
  now rewrite lookup_fun_to_map_Some_1.
Qed.

Lemma relabel_graph_Pmap_map_to_union_l {n m} ml mr (cohg : CospanHyperGraph T n m) :
  vertices cohg ⊆ dom ml ->
  relabel_graph (Pmap_map ml) cohg =
  relabel_graph (Pmap_map (ml ∪ mr)) cohg.
Proof.
  intros Hvert.
  apply relabel_graph_ext_strong.
  intros i [mli Hmli]%Hvert%elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hmli.
  now destruct (mr !! i).
Qed.

Lemma relabel_graph_Pmap_map_to_union_r {n m} ml mr (cohg : CospanHyperGraph T n m) :
  vertices cohg ## dom ml ->
  relabel_graph (Pmap_map mr) cohg =
  relabel_graph (Pmap_map (ml ∪ mr)) cohg.
Proof.
  intros Hvert.
  apply relabel_graph_ext_strong.
  intros i Hi%Hvert%not_elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hi.
  now rewrite (left_id_L None _).
Qed.

Lemma relabel_graph_Pmap_map_to_Pmap_injmap {n m} mv (cohg : CospanHyperGraph T n m) :
  vertices cohg ⊆ dom mv ->
  relabel_graph (Pmap_map mv) cohg =
  relabel_graph (Pmap_injmap mv) cohg.
Proof.
  intros Hvert.
  apply relabel_graph_ext_strong.
  intros i Hi%Hvert.
  symmetry.
  now apply Pmap_injmap_correct_dom.
Qed.

Lemma reindex_graph_to_fun_to_map {n m} f (cohg : CospanHyperGraph T n m) :
  reindex_graph f cohg = reindex_graph (Pmap_map (fun_to_map f (dom (hyperedges cohg)))) cohg.
Proof.
  apply reindex_graph_ext_strong.
  intros i _ Hi%elem_of_dom_2.
  symmetry.
  unfold Pmap_map.
  now rewrite lookup_fun_to_map_Some_1.
Qed.

Lemma reindex_graph_Pmap_map_to_union_l {n m} ml mr (cohg : CospanHyperGraph T n m) :
  dom $ hyperedges cohg ⊆ dom ml ->
  reindex_graph (Pmap_map ml) cohg =
  reindex_graph (Pmap_map (ml ∪ mr)) cohg.
Proof.
  intros Hvert.
  apply reindex_graph_ext_strong.
  intros i _ [mli Hmli]%elem_of_dom_2%Hvert%elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hmli.
  now destruct (mr !! i).
Qed.

Lemma reindex_graph_Pmap_map_to_union_r {n m} ml mr (cohg : CospanHyperGraph T n m) :
  dom $ hyperedges cohg ## dom ml ->
  reindex_graph (Pmap_map mr) cohg =
  reindex_graph (Pmap_map (ml ∪ mr)) cohg.
Proof.
  intros Hvert.
  apply reindex_graph_ext_strong.
  intros i _ Hi%elem_of_dom_2%Hvert%not_elem_of_dom.
  unfold Pmap_map.
  rewrite lookup_union, Hi.
  now rewrite (left_id_L None _).
Qed.

Lemma reindex_graph_Pmap_map_to_Pmap_injmap {n m} mv (cohg : CospanHyperGraph T n m) :
  dom $ hyperedges cohg ⊆ dom mv ->
  reindex_graph (Pmap_map mv) cohg =
  reindex_graph (Pmap_injmap mv) cohg.
Proof.
  intros Hvert.
  apply reindex_graph_ext_strong.
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


Lemma stack_graphs_aux_relabel_disjoint {n m n' m'} f1 f2
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  vertices cohg1 ## vertices cohg2 ->
  stack_graphs_aux (relabel_graph f1 cohg1) (relabel_graph f2 cohg2) =
  relabel_graph (Pmap_map (fun_to_map f1 (vertices cohg1) ∪ fun_to_map f2 (vertices cohg2)))
    (stack_graphs_aux cohg1 cohg2).
Proof.
  intros Hdisj.
  rewrite relabel_stack_graphs_aux.
  f_equal.
  - rewrite (relabel_graph_to_fun_to_map f1).
    apply relabel_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (relabel_graph_to_fun_to_map f2).
    apply relabel_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
Qed.

Lemma stack_graphs_aux_reindex_disjoint {n m n' m'} f1 f2
  `{Hf1 : !Inj eq eq f1, Hf2 : !Inj eq eq f2}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  dom $ hyperedges cohg1 ## dom $ hyperedges cohg2 ->
  set_map f1 $ dom $ hyperedges cohg1 ##@{Pset} set_map f2 $ dom $ hyperedges cohg2 ->
  stack_graphs_aux (reindex_graph f1 cohg1) (reindex_graph f2 cohg2) =
  reindex_graph (Pmap_map (fun_to_map f1 (dom $ hyperedges cohg1) ∪
    fun_to_map f2 (dom $ hyperedges cohg2)))
    (stack_graphs_aux cohg1 cohg2).
Proof.
  intros Hdisj Hdisjran.
  rewrite reindex_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
    done.
  }
  rewrite reindex_stack_graphs_aux; [f_equal|].
  - rewrite (reindex_graph_to_fun_to_map f1).
    rewrite <- reindex_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_l'.
    apply reindex_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (reindex_graph_to_fun_to_map f2).
    rewrite <- reindex_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_r'.
    apply reindex_graph_Pmap_map_to_union_r.
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


Lemma stack_graphs_aux_isomorphic {n m n' m'}
  (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') :
  isomorphic cohg1 cohg1' -> isomorphic cohg2 cohg2' ->
  hyperedges cohg1 ##ₘ hyperedges cohg2 -> hyperedges cohg1' ##ₘ hyperedges cohg2' ->
  vertices cohg1 ## vertices cohg2 -> vertices cohg1' ## vertices cohg2' ->
  isomorphic (stack_graphs_aux cohg1 cohg2) (stack_graphs_aux cohg1' cohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%isomorphic_exists.
  intros Hdisj Hdisj' Hvdisj Hvdisj'.
  rewrite stack_graphs_aux_relabel_disjoint by now rewrite 2 (vertices_reindex_graph _).
  rewrite (stack_graphs_aux_reindex_disjoint _ _ _); [|now apply map_disjoint_dom|].
  2:{
    rewrite map_disjoint_dom in Hdisj'.
    cbn in Hdisj'.
    rewrite 2 dom_fmap_L in Hdisj'.
    rewrite 2 dom_kmap_L' in Hdisj'.
    done.
  }
  rewrite reindex_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    now rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
  }
  assert (Hinjidx : Inj eq eq (Pmap_injmap
           (fun_to_map fe1 (dom (hyperedges cohg1) :> Pset) ∪
           fun_to_map fe2 (dom (hyperedges cohg2) :> Pset)))). 1:{
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
  rewrite relabel_graph_Pmap_map_to_Pmap_injmap. 2:{
    rewrite 3 (vertices_reindex_graph _).
    rewrite vertices_stack_graphs_aux by done.
    now rewrite dom_union_L, 2 dom_fun_to_map_L.
  }
  constructor.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L,
      2 (vertices_reindex_graph _).
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite (vertices_reindex_graph _) in Ha.
      rewrite (vertices_reindex_graph _) in Hb.
      rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _) in Hvdisj'.
      intros ->.
      now apply Hvdisj' in Hb.
  - apply _.
Qed.


Lemma stack_graphs_aux_to_stack_graphs_disjoint {n m n' m'}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  hyperedges cohg1 ##ₘ hyperedges cohg2 ->
  vertices cohg1 ## vertices cohg2 ->
  isomorphic (stack_graphs_aux cohg1 cohg2) (stack_graphs cohg1 cohg2).
Proof.
  intros Hdisj Hvdisj.
  unfold stack_graphs.
  apply stack_graphs_aux_isomorphic.
  - constructor; apply _.
  - constructor; apply _.
  - done.
  - cbn.
    apply map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
  - done.
  - rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _).
    set_solver +.
Qed.


Lemma swapped_stack_graphs_aux_relabel_disjoint {n m n' m'} f1 f2
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  vertices cohg1 ## vertices cohg2 ->
  swapped_stack_graphs_aux (relabel_graph f1 cohg1) (relabel_graph f2 cohg2) =
  relabel_graph (Pmap_map (fun_to_map f1 (vertices cohg1) ∪ fun_to_map f2 (vertices cohg2)))
    (swapped_stack_graphs_aux cohg1 cohg2).
Proof.
  intros Hdisj.
  rewrite relabel_swapped_stack_graphs_aux.
  f_equal.
  - rewrite (relabel_graph_to_fun_to_map f1).
    apply relabel_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (relabel_graph_to_fun_to_map f2).
    apply relabel_graph_Pmap_map_to_union_r.
    now rewrite dom_fun_to_map_L.
Qed.

Lemma swapped_stack_graphs_aux_reindex_disjoint {n m n' m'} f1 f2
  `{Hf1 : !Inj eq eq f1, Hf2 : !Inj eq eq f2}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  dom $ hyperedges cohg1 ## dom $ hyperedges cohg2 ->
  set_map f1 $ dom $ hyperedges cohg1 ##@{Pset} set_map f2 $ dom $ hyperedges cohg2 ->
  swapped_stack_graphs_aux (reindex_graph f1 cohg1) (reindex_graph f2 cohg2) =
  reindex_graph (Pmap_map (fun_to_map f1 (dom $ hyperedges cohg1) ∪
    fun_to_map f2 (dom $ hyperedges cohg2)))
    (swapped_stack_graphs_aux cohg1 cohg2).
Proof.
  intros Hdisj Hdisjran.
  rewrite reindex_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
    done.
  }
  rewrite reindex_swapped_stack_graphs_aux; [f_equal|].
  - rewrite (reindex_graph_to_fun_to_map f1).
    rewrite <- reindex_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_l'.
    apply reindex_graph_Pmap_map_to_union_l.
    now rewrite dom_fun_to_map_L.
  - rewrite (reindex_graph_to_fun_to_map f2).
    rewrite <- reindex_graph_Pmap_map_to_Pmap_injmap by
      now rewrite dom_union_L, 2 dom_fun_to_map_L, <- union_subseteq_r'.
    apply reindex_graph_Pmap_map_to_union_r.
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

Lemma vertices_swapped_stack_graphs_aux {n m n' m'}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  hyperedges cohg1 ##ₘ hyperedges cohg2 ->
  vertices (swapped_stack_graphs_aux cohg1 cohg2) =
  vertices cohg1 ∪ vertices cohg2.
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

Lemma swapped_stack_graphs_aux_isomorphic {n m n' m'}
  (cohg1 cohg1' : CospanHyperGraph T n m)
  (cohg2 cohg2' : CospanHyperGraph T n' m') :
  isomorphic cohg1 cohg1' -> isomorphic cohg2 cohg2' ->
  hyperedges cohg1 ##ₘ hyperedges cohg2 -> hyperedges cohg1' ##ₘ hyperedges cohg2' ->
  vertices cohg1 ## vertices cohg2 -> vertices cohg1' ## vertices cohg2' ->
  isomorphic (swapped_stack_graphs_aux cohg1 cohg2) (swapped_stack_graphs_aux cohg1' cohg2').
Proof.
  intros (fv1 & fe1 & Hfv1 & Hfe1 & ->)%isomorphic_exists
    (fv2 & fe2 & Hfv2 & Hfe2 & ->)%isomorphic_exists.
  intros Hdisj Hdisj' Hvdisj Hvdisj'.
  rewrite swapped_stack_graphs_aux_relabel_disjoint by now rewrite 2 (vertices_reindex_graph _).
  rewrite (swapped_stack_graphs_aux_reindex_disjoint _ _ _); [|now apply map_disjoint_dom|].
  2:{
    rewrite map_disjoint_dom in Hdisj'.
    cbn in Hdisj'.
    rewrite 2 dom_fmap_L in Hdisj'.
    rewrite 2 dom_kmap_L' in Hdisj'.
    done.
  }
  rewrite reindex_graph_Pmap_map_to_Pmap_injmap. 2:{
    cbn.
    now rewrite 2 dom_union_L, 2 dom_fun_to_map_L.
  }
  assert (Hinjidx : Inj eq eq (Pmap_injmap
           (fun_to_map fe1 (dom (hyperedges cohg1) :> Pset) ∪
           fun_to_map fe2 (dom (hyperedges cohg2) :> Pset)))). 1:{
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
  rewrite relabel_graph_Pmap_map_to_Pmap_injmap. 2:{
    rewrite 3 (vertices_reindex_graph _).
    rewrite vertices_swapped_stack_graphs_aux by done.
    now rewrite dom_union_L, 2 dom_fun_to_map_L.
  }
  constructor.
  - apply Pmap_injmap_inj.
    apply map_inj_disj_union.
    + now rewrite map_disjoint_dom, 2 dom_fun_to_map_L,
      2 (vertices_reindex_graph _).
    + now apply fun_to_map_inj.
    + now apply fun_to_map_inj.
    + intros i j a b Ha%(elem_of_map_img_2 (SA:=Pset))
        Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite map_img_fun_to_map_L in Ha, Hb.
      rewrite (vertices_reindex_graph _) in Ha.
      rewrite (vertices_reindex_graph _) in Hb.
      rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _) in Hvdisj'.
      intros ->.
      now apply Hvdisj' in Hb.
  - apply _.
Qed.


Lemma swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint {n m n' m'}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T n' m') :
  hyperedges cohg1 ##ₘ hyperedges cohg2 ->
  vertices cohg1 ## vertices cohg2 ->
  isomorphic (swapped_stack_graphs_aux cohg1 cohg2) (swapped_stack_graphs cohg1 cohg2).
Proof.
  intros Hdisj Hvdisj.
  unfold swapped_stack_graphs.
  apply swapped_stack_graphs_aux_isomorphic.
  - constructor; apply _.
  - constructor; apply _.
  - done.
  - cbn.
    apply map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
  - done.
  - rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _).
    set_solver +.
Qed.

Lemma compose_graphs_aux_to_compose_graphs_disjoint {n m o}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T m o) :
  hyperedges cohg1 ##ₘ hyperedges cohg2 ->
  vertices cohg1 ## vertices cohg2 ->
  compose_graphs_aux cohg1 cohg2 ≡ᵢ compose_graphs cohg1 cohg2.
Proof.
  intros Hdisj Hvdisj.
  rewrite <- compose_graphs_alt_correct, <- compose_graphs_alt_aux_correct by done.
  apply add_top_loops_struct_isomorphic.
  apply (subrel' isomorphic).
  now apply swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint.
Qed.

Lemma isomorphic_reindex_graph {n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T n m) :
  isomorphic cohg (reindex_graph f cohg).
Proof.
  apply isomorphic_exists.
  exists id, f.
  rewrite relabel_graph_id.
  split_and!; [apply _..|done].
Qed.

Lemma isomorphic_relabel_graph {n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T n m) :
  isomorphic cohg (relabel_graph f cohg).
Proof.
  apply isomorphic_exists.
  exists f, id.
  rewrite reindex_graph_id.
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

Lemma compose_graphs_unsafe_to_compose_graphs {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  vertices tgl ∖ list_to_set (outputs tgl) ##
  vertices tgr ∖ list_to_set (inputs tgr) ->
  hyperedges tgl ##ₘ hyperedges tgr ->
  compose_graphs_unsafe tgl tgr ≡ᵢ compose_graphs tgl tgr.
Proof.
  intros Hoi Hvdisj Hdisj.
  rewrite <- compose_graphs_aux_to_compose_graphs_unsafe by done.
  rewrite <- compose_graphs_alt_aux_correct by done.
  rewrite <- compose_graphs_alt_correct.
  apply add_top_loops_struct_isomorphic_strong.
  cbn.
  rewrite 4 vsplitl_app.
  transitivity (relabel_graph
     (subst_by_vec
        (propogate_subst
           (vzip (vmap (bcons false) (outputs tgl))
              (vmap (bcons true) (inputs tgr)))))
     (swapped_stack_graphs_aux (relabel_graph (bcons false) tgl)
      (relabel_graph (bcons true) tgr))). 2:{
    set (f := (fun i => if decide (i ∈ dom (hyperedges tgl)) then bcons false i else bcons true i)).
    assert (Hf : Inj eq eq f). 1:{
      intros i j.
      unfold f.
      do 2 case_decide; now intros ?%(inj2 bcons).
    }
    rewrite (isomorphic_reindex_graph f).
    apply eq_reflexivity.
    rewrite reindex_relabel_graph.
    rewrite reindex_swapped_stack_graphs_aux by apply _.
    f_equal.
    unfold swapped_stack_graphs.
    rewrite 2 reindex_relabel_graph.
    f_equal; f_equal.
    - apply reindex_graph_ext_strong.
      intros i _ Hi%elem_of_dom_2.
      unfold f.
      now rewrite decide_True by done.
    - apply reindex_graph_ext_strong.
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
  rewrite (isomorphic_relabel_graph f).
  rewrite relabel_graph_compose, 2 relabel_swapped_stack_graphs_aux,
    2 relabel_graph_compose.
  apply eq_reflexivity.
  f_equal.
  - apply relabel_graph_ext_strong.
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
  - apply relabel_graph_ext_strong.
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


Lemma compose_graphs_unsafe'_to_compose_graphs {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  vertices tgl ∖ list_to_set (outputs tgl) ##
  vertices tgr ∖ list_to_set (inputs tgr) ->
  hyperedges tgl ##ₘ hyperedges tgr ->
  compose_graphs_unsafe' tgl tgr ≡ᵢ compose_graphs tgl tgr.
Proof.
  intros.
  etransitivity.
  - apply (subrel' cohg_vert_eq).
    apply compose_graphs_unsafe'_correct.
  - now apply compose_graphs_unsafe_to_compose_graphs.
Qed.




Lemma stack_graphs_id_0_l {n m} (cohg : CospanHyperGraph T n m) :
  stack_graphs (id_graph 0) cohg ≡ᵢ cohg.
Proof.
  symmetry.
  rewrite (iso_relabel_reindex _ xI xI) at 1.
  apply eq_reflexivity.
  unfold stack_graphs, stack_graphs_aux.
  cbn.
  change (relabel_hg (bcons false) _) with (∅ :> HyperGraph T).
  apply cohg_ext; [|done..].
  cbn.
  apply hg_ext; [|set_solver].
  symmetry.
  apply map_empty_union.
Qed.

Lemma empty_graph_0_0_eq {n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg.(hedges) = ∅ ->
  cohg'.(hedges) = ∅ ->
  n = 0 -> m = 0 ->
  cohg = cohg'.
Proof.
  destruct cohg, cohg'; cbn.
  intros; subst.
  inv_all_vec_fin; f_equal; done.
Qed.

Lemma delta_spider_graph_alt n m k :
  isomorphic (T:=T) (delta_spider_graph n m)
    (mk_cohg (mk_hg ∅ {[k]}) (fun_to_vec (λ _, k)) (fun_to_vec (λ _, k))).
Proof.
  rewrite (iso_relabel_reindex (delta_spider_graph n m) (λ p, pos_add_N p (Pos.pred_N k)) id
    (Hfe:=(ltac:(intros ? ?; lia)))).
  apply eq_reflexivity.
  apply cohg_ext.
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

Lemma n_stack_delta_spider_graph_alt k n m :
  forall offset,
  n_stack_graphs k (delta_spider_graph (T:=T) n m) ≡ᵢ
  mk_cohg (mk_hg ∅ (list_to_set (Pos.of_succ_nat <$> seq offset k)))
    (fun_to_vec (λ i, Pos.of_succ_nat (offset + i / n)))
    (fun_to_vec (λ i, Pos.of_succ_nat (offset + i / m))).
Proof.
  induction k; [done|].
  cbn.
  intros offset.
  rewrite (delta_spider_graph_alt n m (Pos.of_succ_nat offset)) at 1.
  rewrite (IHk (S offset)).
  rewrite <- stack_graphs_aux_to_stack_graphs_disjoint; [|done|].
  2:{
    rewrite vertices_almost_empty_graph.
    rewrite vec_to_list_app, 2 (vec_to_list_fun_to_vec (λ _, Pos.of_succ_nat offset)).
    rewrite list_to_set_app.
    rewrite 2 (fmap_const _ (Pos.of_succ_nat offset)).
    rewrite vertices_almost_empty_graph.
    rewrite vec_to_list_app, 2 (vec_to_list_fun_to_vec (λ i, Pos.of_succ_nat (_ + (i / _)))).
    set_unfold.
    intros ?.
    rewrite 2 elem_of_replicate.
    setoid_rewrite elem_of_seq.
    set_unfold; naive_solver lia.
  }
  apply eq_reflexivity.
  apply cohg_ext.
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

Lemma permute_graph_relabel_graph {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') f (cohg : CospanHyperGraph T n m) :
  permute_graph fl fr (relabel_graph f cohg) = relabel_graph f (permute_graph fl fr cohg).
Proof.
  subst.
  rewrite 2 (permute_graph_alt fl fr).
  apply cohg_ext; [done|..].
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

Lemma permute_graph_reindex_graph {n m n' m'}
  (fl : fin n -> fin n')
  (fr : fin m -> fin m')  f (cohg : CospanHyperGraph T n m) :
  permute_graph fl fr (reindex_graph f cohg) = reindex_graph f (permute_graph fl fr cohg).
Proof.
  done.
Qed.

Lemma permute_graph_isomorphic {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') : Proper (isomorphic ==> isomorphic) (permute_graph (T:=T) fl fr).
Proof.
  subst.
  intros cohg cohg' Heq.
  induction Heq as [cohg fv fe Hfv Hfe].
  rewrite (permute_graph_relabel_graph fl fr), permute_graph_reindex_graph by done.
  now constructor.
Qed.

#[export] Instance permute_graph_cohg_vert_eq {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') :
  Proper (cohg_vert_eq ==> cohg_vert_eq) (permute_graph (T:=T) fl fr).
Proof.
  intros cohg cohg' Heq.
  rewrite cohg_vert_eq_alt_vertices in Heq.
  rewrite cohg_vert_eq_alt_vertices.
  subst.
  rewrite 2 (vertices_permute_graph fl fr).
  cbn.
  destruct Heq as (<- & <- & <- & <-).
  done.
Qed.

#[export] Instance permute_graph_struct_isomorphic {n m n' m'}
  (fl : fin n -> fin n') {Hfl : Inj eq eq fl}
  (fr : fin m -> fin m') {Hfr : Inj eq eq fr}
  (Hn : n = n') (Hm : m = m') :
  Proper (struct_isomorphic ==> struct_isomorphic) (permute_graph (T:=T) fl fr).
Proof.
  apply proper_struct_isomorphic_of_vert_eq_unary.
  - now apply permute_graph_cohg_vert_eq.
  - now apply permute_graph_isomorphic.
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

Lemma permute_graph_alt_cancel {n m n' m'}
  (fl : fin n -> fin n') (gl : fin n' -> fin n)
  (fr : fin m -> fin m') (gr : fin m' -> fin m)
  {Hfgl : Cancel eq fl gl} {Hfgr : Cancel eq fr gr}
  (Hn : n = n') (Hm : m = m') (cohg : CospanHyperGraph T n m) :
  permute_graph fl fr cohg =
  mk_cohg cohg
    (permute_vec gl cohg.(inputs))
    (permute_vec gr cohg.(outputs)).
Proof.
  subst.
  pose proof @cancel_inj.
  apply fin_perm_cancel_comm in Hfgl as ?.
  apply fin_perm_cancel_comm in Hfgr as ?.
  rewrite (permute_graph_alt fl fr).
  f_equal; apply permute_vec_ext, reflexivity.
  - intros i.
    apply (fin_perm_inv_spec fl).
    apply Hfgl.
  - intros i.
    apply (fin_perm_inv_spec fr).
    apply Hfgr.
Qed.



Lemma delta_spider_graph_bundled_alt k n m :
  delta_spider_graph_bundled (T:=T) k n m ≡ᵢ
  copy_graph k (delta_spider_graph n m).
Proof.
  unfold copy_graph.
  erewrite (permute_graph_struct_isomorphic fin_prod_comm fin_prod_comm
    (Nat.mul_comm _ _) (Nat.mul_comm _ _) _) by
    (apply (n_stack_delta_spider_graph_alt _ _ _ 0)).
  rewrite (permute_graph_alt_cancel _ _ _ _) by lia.
  apply eq_reflexivity.
  apply cohg_ext.
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


Lemma propogate_subst_vzip_NoDup_r_aux
  {n} (v w : vec positive n) : NoDup w -> Forall (.∉ vec_to_list w) v ->
    propogate_subst (vzip v w) =
    vzip (vimap (λ i p,
      let prev_occs := filter (λ ip, ip.2 = p) (vtake i (vzip (vfinseq n) v) :> list _) in
      match last prev_occs with
      | None => (* First occurence *)
          p
      | Some ip =>
          w !!! ip.1
      end) v) w.
Proof.
  induction n; [inv_all_vec_fin; done|].
  inv_vec v; intros vh v.
  inv_vec w; intros wh w.
  cbn.
  intros [Hwh Hw]%NoDup_cons [Hvh Hv]%Forall_cons.
  pose proof Hv as Hvall.
  rewrite Forall_forall in Hvall.
  f_equal.
  rewrite <- vzip_map.
  rewrite (vmap_id' _ w) by (intros; apply fn_lookup_singleton_ne; set_solver - IHn).
  rewrite IHn; [|done|rewrite vec_to_list_map, Forall_fmap, Forall_forall;
    intros ? ?; cbn; rewrite fn_lookup_singleton_case; case_decide; set_solver - IHn].
  f_equal.
  rewrite vimap_vmap.
  apply vimap_ext.
  intros i.
  cbn.
  rewrite fn_lookup_singleton_case.
  case_decide as Hvh_eq.
  1:{
    subst vh.
    rewrite last_cons.
    set (precs := last _).
    set (precs' := last _).
    assert (precs' = prod_map FS id <$> (prod_map id {[wh := v !!! i]} <$> precs)) as Hprecs'. 1:{
      subst precs precs'.
      rewrite vzip_map_l, vzip_map_r.
      rewrite 2 vtake_vmap.
      rewrite 2 vec_to_list_map.
      assert (Hvi_elem : v !!! i ∈ vec_to_list v) by (apply elem_of_vlookup; eauto).
      rewrite <- 2 fmap_last.
      f_equal.
      etransitivity; [refine (filter_fmap_prod_map_id_r (.=v!!!i) _ _)|].
      f_equal.
      rewrite list_filter_fmap.
      set (filt := filter _ _).
      set (filt' := filter _ _).
      assert (filt' = filt) as ->. 1:{
        subst filt filt'.
        symmetry.
        apply list_filter_ext_lookup.
        cbn.
        apply Forall_Forall2_diag.
        rewrite Forall_vlookup.
        intros j.
        split.
        - simpl.
          set (jq := _ !!! j).
          assert (jq.2 ∈ vec_to_list v) as Hjq. 1:{
            assert (jq ∈ vec_to_list $ vtake i (vzip (vfinseq n) v)) as Hjq' by
              (subst jq; apply elem_of_vlookup; eauto).
            rewrite vec_to_list_take in Hjq'.
            apply subseteq_take in Hjq'.
            rewrite vec_to_list_zip_with in Hjq'.
            apply elem_of_zip_with in Hjq' as (? & ? & [= <-]%(f_equal snd) & _ & Hjq).
            done.
          }
          assert (jq.2 <> wh) by (apply Hvall in Hjq; set_solver + Hjq).
          rewrite fn_lookup_singleton_case.
          case_decide; naive_solver.
        - done.
      }
      rewrite <- list_fmap_compose.
      symmetry.
      apply list_fmap_id'.
      subst filt.
      rewrite vec_to_list_take, vec_to_list_zip_with.
      intros [j q] ([= ->] & _)%elem_of_list_filter.
      cbn.
      f_equal.
      rewrite 2 fn_lookup_singleton.
      done.
    }
    rewrite Hprecs'.
    clear precs' Hprecs'.
    rewrite <- option_fmap_compose.
    destruct precs as [[j q]|]; done.
  }
  
  1:{
    set (precs := last _).
    set (precs' := last _).
    assert (precs' = prod_map FS id <$> precs) as Hprecs'. 1:{
      subst precs precs'.
      rewrite vzip_map_l, vzip_map_r.
      rewrite 2 vtake_vmap.
      rewrite 2 vec_to_list_map.
      assert (Hvi_elem : v !!! i ∈ vec_to_list v) by (apply elem_of_vlookup; eauto).
      rewrite <- fmap_last.
      f_equal.
      etransitivity; [refine (filter_fmap_prod_map_id_r (.=v!!!i) _ _)|].
      cbn.
      f_equal.
      apply list_filter_ext_lookup.
      rewrite Forall2_fmap_r.
      apply Forall_Forall2_diag.
      rewrite Forall_vlookup.
      intros j.
      set (jq := _ !!! j).
      assert (jq.2 ∈ vec_to_list v) as Hjq. 1:{
        assert (jq ∈ vec_to_list $ vtake i (vzip (vfinseq n) v)) as Hjq' by
          (subst jq; apply elem_of_vlookup; eauto).
        rewrite vec_to_list_take in Hjq'.
        apply subseteq_take in Hjq'.
        rewrite vec_to_list_zip_with in Hjq'.
        apply elem_of_zip_with in Hjq' as (? & ? & [= <-]%(f_equal snd) & _ & Hjq).
        done.
      }
      assert (jq.2 <> wh) by (apply Hvall in Hjq; set_solver + Hjq).
      assert (v !!! i <> wh) by (apply Hvall in Hvi_elem; set_solver + Hvi_elem).

      split.
      - simpl.
        rewrite fn_lookup_singleton_case.
        case_decide; naive_solver.
      - intros Hsnd Hsndmap.
        destruct jq as [j' q']; cbn in *.
        f_equal.
        congruence.
      }
      rewrite Hprecs'.
      destruct precs; done. 
    }
Qed.


Lemma compose_graphs_id_graph_l_aux {T n m} (cohg : CospanHyperGraph T n m) :
  compose_graphs (id_graph n) cohg ≡ᵥ relabel_graph (bcons true) (reindex_graph (bcons true) cohg).
Proof.
  unfold compose_graphs.
  cbn.
  rewrite vzip_map.
  rewrite propogate_subst_vmap_bcons_false_true_NoDup_l by (rewrite vec_to_list_map, vec_to_list_seq;
    apply (NoDup_fmap _), NoDup_seq).
  rewrite <- vzip_map.
  erewrite relabel_graph_ext. 2:{
    intros i.
    rewrite subst_by_vec_disj by (rewrite <- 2 vec_to_list_map,
      fst_vzip, snd_vzip, !vec_to_list_map; set_solver).
    done.
  }
  apply cohg_vert_eq_alt_vertices;
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
  - rewrite vertices_relabel_graph.
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
      instantiate (1:= (list_to_set (vmap (bcons true) (inputs cohg)))).
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


Lemma compose_graphs_id_graph_l {T n m} (cohg : CospanHyperGraph T n m) :
  compose_graphs (id_graph n) cohg ≡ᵢ cohg.
Proof.
  rewrite compose_graphs_id_graph_l_aux.
  rewrite <- iso_relabel_reindex; [done|apply _..].
Qed.


Lemma stack_graphs_id_graph {T} n m :
  isomorphic (T:=T) (stack_graphs (id_graph n) (id_graph m))
    (id_graph (n + m)).
Proof.
  symmetry.
  apply isomorphic_exists.
  exists (fun i => if decide (pos_to_nat_pred i < n) then i~0 else (pos_sub_N i (N.of_nat n))~1), id.
  split_and!.
  - intros i j; do 2 case_decide; lia.
  - apply _.
  - eenough (Hen : _) by (apply cohg_ext; [reflexivity|..]; apply Hen).
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


#[export] Instance compose_graphs_alt_cohg_vert_eq {T}
  {n m o} : Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@compose_graphs_alt T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  unfold compose_graphs_alt.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_graphs_alt_struct_isomorphic `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@compose_graphs_alt T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  unfold compose_graphs_alt.
  apply add_top_loops_struct_isomorphic.
  now apply swapped_stack_graphs_struct_isomorphic.
Qed.

Import Facts.

Lemma proper_cohg_syntactic_eq_of_struct_iso_eq_binary `{Equiv T1, Equivalence T1 equiv,
  Equiv T2, Equivalence T2 equiv, Equiv T3, Equivalence T3 equiv} {n1 m1 n2 m2 n3 m3}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2 ->
    CospanHyperGraph T3 n3 m3) :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic) f ->
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) f ->
  Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq) f.
Proof.
  intros Hfiso Hfcohg.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  induction Hcohg1 as [cohg1 cohg1' fv1 fe1 Hfv1 Hfe1 Hverteq1].
  rewrite <- (subrel'' struct_isomorphic (norm_verts_vert_eq cohg1)).
  rewrite (Hverteq1).
  rewrite (subrel'' struct_isomorphic (norm_verts_vert_eq _)).
  rewrite <- (subrel'' struct_isomorphic (iso_relabel_reindex _ _ _)) by done.
  induction Hcohg2 as [cohg2 cohg2' fv2 fe2 Hfv2 Hfe2 Hverteq2].
  rewrite <- (subrel'' struct_isomorphic (norm_verts_vert_eq cohg2)).
  rewrite (Hverteq2).
  rewrite (subrel'' struct_isomorphic (norm_verts_vert_eq _)).
  rewrite <- (subrel'' struct_isomorphic (iso_relabel_reindex _ _ _)) by done.
  done.
Qed.

#[export] Instance compose_graphs_alt_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@compose_graphs_alt T n m o).
Proof.
  apply proper_cohg_syntactic_eq_of_struct_iso_eq_binary; apply _.
Qed.

#[export] Instance compose_graphs_cohg_vert_eq {T}
  {n m o} : Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  do 2 rewrite <- compose_graphs_alt_correct.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_graphs_struct_isomorphic_mor `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  do 2 rewrite <- compose_graphs_alt_correct.
  now apply compose_graphs_alt_struct_isomorphic.
Qed.

#[export] Instance compose_graphs_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  rewrite <- 2 compose_graphs_alt_correct.
  now apply compose_graphs_alt_cohg_syntactic_eq.
Qed.

#[export] Instance stack_graphs_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o p} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@stack_graphs T n m o p).
Proof.
  apply proper_cohg_syntactic_eq_of_iso_vert_eq_binary; apply _.
Qed.


(* FIXME: Move to Definitions *)
Lemma cohg_eq_ind `{Equiv T} {n m} (P : CospanHyperGraph T n m -> CospanHyperGraph T n m -> Prop)
  (HP : forall ins outs verts he he', map_equiv he he' ->
    P (mk_cohg (mk_hg he verts) ins outs) (mk_cohg (mk_hg he' verts) ins outs)) :
  forall cohg cohg', cohg ≡ₕ cohg' -> P cohg cohg'.
Proof.
  intros [[he verts] ins outs] [[he' verts'] ins' outs'] ([= <-] & [= <-] & [Hhe [= <-]]).
  apply HP, Hhe.
Qed.

Lemma cohg_eq_ind' `{Equiv T} {n m} (P : CospanHyperGraph T n m -> CospanHyperGraph T n m -> Prop)
  (HP : forall ins outs hg hg', hg ≡ hg' ->
    P (mk_cohg hg ins outs) (mk_cohg hg' ins outs)) :
  forall cohg cohg', cohg ≡ₕ cohg' -> P cohg cohg'.
Proof.
  intros [hg ins outs] [hg' ins' outs'] ([= <-] & [= <-] & Hhg).
  apply HP, Hhg.
Qed.

#[export] Instance compose_graphs_aux_cohg_eq `{Equiv T} {n m o} :
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (@compose_graphs_aux T n m o).
Proof.
  refine (cohg_eq_ind _ _).
  intros ins1 outs1 verts1 he1 he1' Hhe1.
  refine (cohg_eq_ind _ _).
  intros ins2 outs2 verts2 he2 he2' Hhe2.
  unfold compose_graphs_aux.
  cbn.
  f_equiv.
  split_and!; [done..|].
  cbn.
  split; cbn.
  - now apply fin_maps.union_proper.
  - do 3 f_equal;
    eapply vertices_hg_equiv; split; done.
Qed.


#[export] Instance compose_graphs_cohg_eq `{Equiv T} {n m o} :
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  rewrite 2 compose_graphs_to_compose_graphs_aux.
  now apply compose_graphs_aux_cohg_eq; do 2 f_equiv.
Qed.