From stdpp Require Export pmap gmap decidable.
Require Import TensorGraph TensorGraphSemantics TensorGraphFacts.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.


Local Open Scope nat_scope.

Section DPO.

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

Definition pos_tail (p : positive) := pos_elim id id p.

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

Lemma vertices_vertices_hg_decomp {n m} (cohg : CospanHyperGraph T n m) :
  vertices cohg = vertices_hg cohg ∪ list_to_set (inputs cohg ++ outputs cohg).
Proof.
  done.
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


(* Lemma compose_graphs_aux_struct_isomorphic {n m o}
  (cohg1 cohg1' : CospanHyperGraph T n m) (cohg2 cohg2' : CospanHyperGraph T m o) :
  cohg1 ≡ᵢ cohg1' -> cohg2 ≡ᵢ cohg2' ->
  hyperedges cohg1 ##ₘ hyperedges cohg2 -> hyperedges cohg1' ##ₘ hyperedges cohg2' ->
  compose_graphs_aux cohg1 cohg2 ≡ᵢ compose_graphs_aux cohg1' cohg2'.
Proof.
  intros Heq1 Heq2 Hdisj1 Hdisj2.
  rewrite <- 2 compose_graphs_alt_aux_correct by done.
  apply add_top_loops_struct_isomorphic.
  now apply swapped_stack_graphs_aux_struct_isomorphic.
Qed. *)


  Section Paths.

    Context (H : HyperGraph T).

    Definition successor (h h' : HyperEdge T) :=
      Exists (fun p => p ∈ (h'.2)) (h.1.2).

    Definition predecessor (h h' : HyperEdge T) :=
      Exists (fun p => p ∈ (h.2)) (h'.1.2).

    Instance successor_decide (h h' : HyperEdge T) : Decision (successor h h') := _.
    Instance predecessor_decide (h h' : HyperEdge T) : Decision (predecessor h h') := _.

    Definition successors (h : HyperEdge T) : Pmap (HyperEdge T) :=
      filter (fun ka => successor ka.2 h) H.(hyperedges).

    Definition predecessors (h : HyperEdge T) : Pmap (HyperEdge T) :=
      filter (fun ka => predecessor ka.2 h) H.(hyperedges).

    Definition all_successors (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) :=
      filter (fun kh' => Exists (fun kh => successor kh'.2 kh.2) (map_to_list G))
      H.(hyperedges).

    Definition all_predecessors (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) :=
      filter
      (fun kh' => Exists (fun kh => predecessor kh'.2 kh.2) (map_to_list G))
      H.(hyperedges).

    Fixpoint all_paths_aux
      (G : Pmap (HyperEdge T)) (n : nat) : Pmap (HyperEdge T) :=
    match n with
    | 0     => ∅
    | (S k) => let step := all_predecessors G in
      step ∪ all_paths_aux step k
    end.

    Definition all_paths (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) :=
      all_paths_aux G (length (map_to_list H.(hyperedges))) ∖ G.

    Definition all_paths_idx (pdx : list positive) : Pmap (HyperEdge T) :=
      all_paths (filter (fun ka => ka.1 ∈ pdx) (H.(hyperedges))).

    Fixpoint all_predpaths
      (G : Pmap (HyperEdge T)) (n : nat) : Pmap (HyperEdge T) :=
    match n with
    | 0     => ∅
    | (S k) => let step := all_successors G in
      step ∖ G ∪ all_predpaths step k
    end.

    Definition successor_idx (p p' : positive)
      (Sp : is_Some (H.(hyperedges) !! p)) (Sp' : is_Some (H.(hyperedges) !! p')) :=
      successor (is_Some_proj Sp) (is_Some_proj Sp').

    Definition predecessor_idx (p p' : positive)
      (Sp : is_Some (H.(hyperedges) !! p)) (Sp' : is_Some (H.(hyperedges) !! p')) :=
      predecessor (is_Some_proj Sp) (is_Some_proj Sp').

    Instance successor_idx_decide (p p' : positive) (Sp : is_Some (H.(hyperedges) !! p)) (Sp' : is_Some (H.(hyperedges) !! p'))
      : Decision (successor_idx p p' Sp Sp') := _.

    Instance predecessor_idx_decide (p p' : positive) (Sp : is_Some (H.(hyperedges) !! p)) (Sp' : is_Some (H.(hyperedges) !! p'))
      : Decision (predecessor_idx p p' Sp Sp') := _.

    Lemma succ_pred_symm (h h' : HyperEdge T) :
      successor h h' <-> predecessor h' h.
  Proof. auto. Qed.

    Definition path (h h' : HyperEdge T) : Prop :=
      (tc successor) h h'.

    Definition pred_path (h h' : HyperEdge T) :=
      (tc predecessor) h h'.


    Definition predecessors_idx (p : positive) : Pmap (HyperEdge T) :=
      match H.(hyperedges) !! p with
      | Some h => predecessors h
      | None => ∅
      end.

    Definition path_pred_path_symm (h h' : HyperEdge T) :
      path h h' <-> pred_path h' h.
    Proof.
      split; intros.
      - induction H0.
        + apply tc_once.
          now rewrite succ_pred_symm in H0.
        + rewrite succ_pred_symm in H0.
          apply tc_transitive with (y:=y).
          * auto.
          * now apply tc_once.
      - induction H0.
        + apply tc_once.
          now rewrite <- succ_pred_symm in H0.
        + rewrite <- succ_pred_symm in H0.
          apply tc_transitive with (y:=y).
          * auto.
          * now apply tc_once.
    Qed.

    Definition v_pred (v : positive) (h : HyperEdge T) :=
      v ∈ h.1.2.
    Definition v_succ (v : positive) (h : HyperEdge T) :=
      v ∈ h.2.
    Definition v_incident (v : positive) (h : HyperEdge T) :=
      v_pred v h /\ v_succ v h.

    Definition v_pred_decide (v : positive) (h : HyperEdge T) : Decision (v_pred v h).
    Proof.
      unfold v_pred.
      apply _.
    Defined.

    Definition v_succ_decide (v : positive) (h : HyperEdge T) : Decision (v_succ v h).
    Proof.
      unfold v_succ.
      apply _.
    Qed.

    Instance vpred_decide (v : positive) (h : HyperEdge T) : Decision (v_pred v h) := (_ : Decision (_ ∈ _)).

    Instance vsucc_decide (v : positive) (h : HyperEdge T) : Decision (v_succ v h) := (_ : Decision (_ ∈ _)).

    (* Definition all_incident_vertices :=
      (map_to_set (fun k v => list_to_set v.2) H.(hyperedges)). *)
  (* (fun pe => (pe.1, pe.2.1.2 ++ pe.2.2)) <$>  *)


  (* Need to produce : list (positive * (list positive * list positive)) *)
  (* Representing the Vertex Idx and the edge indices it is incident to *)
    Definition vertex_map : Pmap (list positive * list positive) :=
      list_to_map(map_to_list H.(hyperedges) ≫= (fun pe =>
      let label := pe.1 in
      (* Edge Idx *)
      let lefts := pe.2.1.2 in
      (* All the vertices where this edge is right-incident *)
      let rights := pe.2.2 in
      (* All the vertices where this edge is left-incident *)
      ((fun x => (x, (@nil positive, [label]))) <$> lefts) ++
      ((fun x => (x, ([label], @nil positive))) <$> rights))).

    Open Scope positive.

    Definition PredMap : Pmap (list positive) :=
      let hedges := H.(hyperedges) in
        (fun x => x.1.2) <$> hedges.

    Definition SuccMap : Pmap (list positive) :=
      let hedges := H.(hyperedges) in
        (fun x => x.2) <$> hedges.

    Definition vPredMap : Pmap (list positive) :=
      let predmap := PredMap in
      predmap.

  End Paths.

Definition decompose_left {n m} (G : CospanHyperGraph T n m) (L : HyperGraph T) : CospanHyperGraph T n m :=
  G.(inputs) -> {|
    hyperedges := ∅;
    hypervertices := ∅
  |} <- G.(outputs).

  Definition subgraph_index_aux (H : HyperGraph T) (L : list positive) : Pmap (HyperEdge T) :=
    filter (fun ka => (ka.1 ∈ L)) H.(hyperedges).

  Definition subgraph_index (H : HyperGraph T) (L : list positive) : HyperGraph T :=
  {| hyperedges := subgraph_index_aux H L;
     hypervertices := ∅ |}.

  Definition mk_sub_hg (H : HyperGraph T) (mh : Pmap (HyperEdge T)) : HyperGraph T :=
    mk_hg mh (hypervertices H ∩ referrenced_vertices_hg (mk_hg mh ∅)).

  Section decompose_defs.

  Context (H : HyperGraph T) (L : list positive).

  Definition decompose_L1 : HyperGraph T :=
    mk_sub_hg H (subgraph_index_aux H L).

  Definition decompose_C1 : HyperGraph T :=
    mk_sub_hg H (all_paths_idx H L).

  Definition decompose_C2 (C1 : HyperGraph T) (isolated : Pset) : HyperGraph T :=
    hg_add_vertices (mk_sub_hg H ((hyperedges H) ∖ (C1 ∪ subgraph_index H L)))
      isolated.

  Definition decompose_L1v : Pset :=
    vertices_hg decompose_L1.

  Definition decompose_C1v : Pset :=
    vertices_hg decompose_C1.

  Definition decompose_C2v C1 isolated : Pset :=
    vertices_hg (decompose_C2 C1 isolated).


  Definition decompose_iset (inputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C1v ∪ inputs).

  Definition decompose_jset C1 isolated (outputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C2v C1 isolated ∪ outputs).

  Definition decompose_kset C1 isolated (inputs outputs : Pset) : Pset :=
    ((decompose_C1v ∪ inputs) ∩ (decompose_C2v C1 isolated ∪ outputs) ∖ decompose_L1v).

  End decompose_defs.

  Definition decompose {n m} (H : CospanHyperGraph T n m) (L : list positive) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L in
    let C2 := decompose_C2 H L C1 isolated in

    let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs_unsafe (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs_unsafe (
      stack_graphs_aux (k -> ∅ <- k) (i -> L1 <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).

  (* Definition decompose {n m} (H : CospanHyperGraph T n m) (L : list positive) : CospanHyperGraph T n m :=
  let Hin := list_to_set (vec_to_list (H.(inputs))) in
  let Hout := list_to_set (vec_to_list (H.(outputs))) in
  let C1 := all_paths_idx H L in
  let L1 := subgraph_index H L in
  let C2 := H.(hedges).(hyperedges) ∖ (C1 ∪ L1) in
  let C1' := vertices_hg {| hyperedges := C1; hypervertices := ∅ |} in
  let L1' := vertices_hg L1 in
  let C2' := vertices_hg {| hyperedges := C2; hypervertices := isolated_vertices H |} in
  let i := list_to_vec(elements(L1' ∩ (C1' ∪ Hin ))) in
  let j := list_to_vec(elements(L1' ∩ (C2' ∪ Hout))) in
  let k := list_to_vec(elements(((C1' ∪ Hin) ∩ (C2' ∪ Hout) ∖ L1'))) in
  compose_graphs_unsafe (
  H.(inputs) -> {| hyperedges := C1; hypervertices := ∅ |}  <- (k +++ i)) (compose_graphs_unsafe ((k +++ i) -> L1 <- (k +++ j)) (
  k +++ j ->
    {| hyperedges := C2; hypervertices := isolated_vertices H |}
  <- H.(outputs)
  )). *)

  Lemma all_paths_aux_subset (H : HyperGraph T) L n :
    all_paths_aux H L n ⊆ H.
  Proof.
    revert L; induction n; intros L.
    - apply map_empty_subseteq.
    - simpl.
      apply map_union_least.
      + apply map_filter_subseteq.
      + apply (IHn (mk_hg (all_predecessors H L) ∅)).
  Qed.


  Lemma all_paths_subset (H : HyperGraph T) L :
    all_paths H L ⊆ H.
  Proof.
    apply map_subseteq_difference_l.
    apply all_paths_aux_subset.
  Qed.

  Lemma all_paths_disjoint H L :
    all_paths H L ##ₘ L.
  Proof.
    now apply map_disjoint_difference_l.
  Qed.

  Lemma all_paths_idx_subset H (L : list positive) : all_paths_idx H L ⊆ H.
  Proof.
    unfold all_paths_idx.
    refine (all_paths_subset H (mk_hg _ ∅)).
  Qed.

  (* FIXME: Move *)
  Lemma map_to_list_union_agree `{FinMap K M} {A} (m1 m2 : M A) : map_agree m1 m2 ->
    map_to_list (m1 ∪ m2) ≡ map_to_list m1 ++ map_to_list m2.
  Proof.
    intros Hagree.
    intros (k, v).
    rewrite elem_of_app, 3 elem_of_map_to_list.
    rewrite lookup_union.
    specialize (Hagree k).
    destruct (m1 !! k), (m2 !! k);
    naive_solver.
  Qed.
  Lemma elem_of_map_to_list_difference_agree `{FinMap K M} {A} (m1 m2 : M A) k v :
    map_agree m1 m2 ->
    (k, v) ∈ map_to_list (m1 ∖ m2) <->
    (k, v) ∈ map_to_list m1 /\ (k, v) ∉ map_to_list m2.
  Proof.
    intros Hagree.
    rewrite 3 elem_of_map_to_list.
    rewrite lookup_difference.
    specialize (Hagree k).
    destruct (m1 !! k), (m2 !! k);
    naive_solver.
  Qed.
  Lemma elem_of_map_to_list_difference `{FinMap K M} {A} (m1 m2 : M A) k v :
    (k, v) ∈ map_to_list (m1 ∖ m2) <->
    (k, v) ∈ map_to_list m1 /\ m2 !! k = None.
  Proof.
    rewrite 2 elem_of_map_to_list.
    rewrite lookup_difference.
    destruct (m1 !! k), (m2 !! k);
    naive_solver.
  Qed.
  Lemma TlRel_skip `(R : relation A) (l : list A) (a b : A) :
    l <> [] ->
    TlRel R a l -> TlRel R a (b :: l).
  Proof.
    intros Hl Hrel.
    induction Hrel; [done|].
    now apply (TlRel_cons _ _ _ (_ :: _)).
  Qed.
  Lemma TlRel_snoc `(R : relation A) (l : list A) a b :
    TlRel R b (l ++ [a]) <-> R a b.
  Proof.
    split; [|eauto using TlRel].
    remember (l ++ [a]) as la eqn:Hla.
    intros Hrel.
    induction Hrel; [now destruct l|].
    apply (f_equal last) in Hla.
    rewrite 2 last_app in Hla.
    cbn in Hla.
    congruence.
  Qed.
  Lemma Sorted_snoc_inv `(R : relation A) (l : list A) (x : A) :
    Sorted R (l ++ [x]) -> Sorted R l /\ TlRel R x l.
  Proof.
    induction l.
    - intros; repeat constructor.
    - cbn.
      intros [[Hl Hxl]%IHl Halx]%Sorted_inv.
      destruct l.
      + split; [repeat constructor|].
        refine  (TlRel_cons _ _ _ [] _).
        cbn in Halx.
        now apply HdRel_inv in Halx.
      + cbn in Halx.
        split.
        * constructor; [done|].
          apply HdRel_inv in Halx.
          now constructor.
        * now apply TlRel_skip; [done|].
  Qed.
  Lemma snoc_case `(P : list A -> Prop)
    (HPnil : P nil)
    (HPsnoc : forall l a, P (l ++ [a])) :
    forall l, P l.
  Proof.
    intros l.
    induction l using rev_ind; auto.
  Qed.
  Lemma difference_disjoint_same_r_2 `{Set_ A SA} (X Y Z : SA) :
    X ∩ Y ⊆ Z -> X ∖ Z ## Y ∖ Z.
  Proof.
    set_solver.
  Qed.
  Lemma difference_disjoint_same_r `{Set_ A SA, !RelDecision (∈@{SA})}
    (X Y Z : SA) : X ∖ Z ## Y ∖ Z <-> X ∩ Y ⊆ Z.
  Proof.
    split; [|apply difference_disjoint_same_r_2].
    intros Hdisj k.
    destruct_decide (decide (k ∈ Z)); set_solver.
  Qed.



  Lemma all_predecessors_spec H L i h :
    (i, h) ∈ map_to_list (all_predecessors H L) <->
    (i, h) ∈ map_to_list (H :> Pmap _) /\
    exists i' h', (i', h') ∈ map_to_list L /\
      predecessor h h'.
  Proof.
    rewrite elem_of_map_to_list.
    unfold all_predecessors.
    rewrite map_lookup_filter_Some.
    rewrite elem_of_map_to_list.
    f_equiv.
    rewrite Exists_exists, exists_pair.
    done.
  Qed.


  Lemma all_paths_aux_spec H L n i h :
    (i, h) ∈ map_to_list (all_paths_aux H L n) <->
    exists i' h' ihs, (i', h') ∈ map_to_list L /\
      (i, h) :: ihs ⊆ (map_to_list (H :> Pmap _)) /\
      Sorted predecessor (h :: ihs.*2 ++ [h']) /\
      length ihs < n.
  Proof.
    revert i h L;
    induction n; intros i h L. 1:{
      cbn.
      rewrite map_to_list_empty.
      rewrite elem_of_nil.
      split; [done|].
      firstorder lia.
    }
    cbn.
    rewrite map_to_list_union_agree. 2:{
      eapply map_agree_weaken, all_paths_aux_subset;
      [|apply map_filter_subseteq].
      reflexivity.
    }
    rewrite elem_of_app.
    rewrite IHn.
    rewrite all_predecessors_spec.
    split.
    - intros [[Hih (i' & h' & Hi'h' & Hhh')]|
      (i' & h' & ihs & Hi'h' & Hihs & Hsort & Hlen)].
      + exists i', h', [].
        split; [done|].
        split; [set_solver +Hih|].
        cbn.
        split; [|clear; lia].
        now repeat constructor.
      + apply all_predecessors_spec in Hi'h' as
        (Hi'h' & i'' & h'' & Hi''h'' & Hpred).
        exists i'', h'', (ihs ++ [(i', h')]).
        split; [done|].
        split; [set_solver +Hi'h' Hihs|].
        rewrite fmap_app; cbn.
        split; [|rewrite length_app; cbn; clear -Hlen; lia].
        apply (Sorted_snoc _ (_ :: (_ ++ [_]))); [done|].
        now apply (TlRel_cons _ _ _ (_ :: _)).
    - intros (i' & h' & ihs & Hi'h' & Hihs & Hsort & Hlen).

      induction ihs as [|ihs (i'', h'')] using snoc_case.
      + left.
        split; [apply Hihs; constructor|].
        cbn in Hsort.
        apply Sorted_inv in Hsort as [_ ?%HdRel_inv].
        eauto.
      + right.
        exists i'', h'', ihs.
        rewrite all_predecessors_spec.
        split_and!.
        * apply Hihs; set_solver +.
        * exists i', h'.
          split; [done|].
          rewrite fmap_app in Hsort.
          cbn in Hsort.
          apply Sorted_inv in Hsort as [Hsort _].
          now apply Sorted_snoc_inv in Hsort as [_ ?%TlRel_snoc].
        * rewrite <- Hihs.
          set_solver +.
        * apply (Sorted_snoc_inv _ (_ :: _)) in Hsort.
          rewrite fmap_app in Hsort.
          apply Hsort.1.
        * rewrite length_app in Hlen.
          revert Hlen.
          clear; cbn; lia.
  Qed.

  Lemma all_paths_dom_subseteq H L :
    dom (all_paths H L) ⊆ dom (hyperedges H) ∖ dom L.
  Proof.
    apply subseteq_difference_r.
    - apply map_disjoint_dom.
      apply all_paths_disjoint.
    - apply subseteq_dom.
      apply all_paths_subset.
  Qed.

  Lemma all_paths_idx_dom_disjoint H
    (L : list positive) :
    dom (all_paths_idx H L) ## list_to_set L.
  Proof.
    symmetry.
    intros k HkL.
    unfold all_paths_idx.
    intros Hk%all_paths_dom_subseteq.
    rewrite elem_of_difference in Hk.
    rewrite 2 elem_of_dom, map_lookup_filter in Hk.
    destruct Hk as [(hk & Hhk) Hk].
    rewrite Hhk in Hk.
    cbn in Hk.
    rewrite elem_of_list_to_set in HkL.
    case_guard; [|done].
    apply Hk.
    done.
  Qed.

  Lemma subgraph_index_aux_dom_subseteq H L :
    dom (subgraph_index_aux H L) ⊆ dom H.(hyperedges) ∩ list_to_set L.
  Proof.
    intros k Hk%elem_of_dom.
    unfold subgraph_index_aux in Hk.
    rewrite map_lookup_filter in Hk.
    destruct (H.(hyperedges) !! k) as [mk|] eqn:Hmk; [|cbn in *; now destruct Hk].
    cbn in Hk.
    apply guard_is_Some in Hk.
    rewrite elem_of_intersection, elem_of_dom.
    set_solver.
  Qed.

  Lemma decompose_L1_C1_disjoint H L :
    hyperedges $ decompose_L1 H L ##ₘ hyperedges $ decompose_C1 H L.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_dom.
    intros k Hk%all_paths_idx_dom_disjoint
      HkL%subgraph_index_aux_dom_subseteq%intersection_subseteq_r.
    auto.
  Qed.

  Lemma decompose_C1_C2_disjoint_gen H L C1 isolated :
    hyperedges $ C1 ##ₘ hyperedges $ decompose_C2 H L C1 isolated.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_difference_l.
    apply map_union_subseteq_l.
  Qed.

  Lemma decompose_L1_C2_disjoint H L C1 isolated :
    hyperedges $ decompose_L1 H L ##ₘ hyperedges $ decompose_C2 H L C1 isolated.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_dom.
    rewrite dom_difference_L, dom_union_L.
    set_solver.
  Qed.

  Lemma decompose_L1v_C1v_subseteq H L inputs :
    decompose_L1v H L ∩ decompose_C1v H L ⊆ decompose_iset H L inputs.
  Proof.
    set_solver.
  Qed.

  Lemma decompose_L1v_C2v_subseteq H L C1 isolated outputs :
    decompose_L1v H L ∩ decompose_C2v H L C1 isolated ⊆
      decompose_jset H L C1 isolated outputs.
  Proof.
    set_solver.
  Qed.

  Lemma decompose_L1_subseteq H L :
    hyperedges $ decompose_L1 H L ⊆ hyperedges H.
  Proof.
    cbn.
    apply map_filter_subseteq.
  Qed.

  Lemma decompose_C1_subseteq H L :
    hyperedges $ decompose_C1 H L ⊆ hyperedges H.
  Proof.
    cbn.
    apply all_paths_idx_subset.
  Qed.

  Lemma decompose_C2_subseteq H L C1 isolated :
    hyperedges $ decompose_C2 H L C1 isolated ⊆ hyperedges H.
  Proof.
    cbn.
    now apply map_subseteq_difference_l.
  Qed.

  Lemma referrenced_vertices_hg_subseteq (H G : HyperGraph T) :
    hyperedges H ⊆ hyperedges G ->
    referrenced_vertices_hg H ⊆ referrenced_vertices_hg G.
  Proof.
    unfold referrenced_vertices_hg.
    intros HHG.
    intros k (ktio & Hktio & HkH)%elem_of_list_to_set%elem_of_list_bind.
    apply map_to_list_submseteq in HHG.
    pose proof (elem_of_submseteq _ _ _ HkH HHG).
    rewrite elem_of_list_to_set, elem_of_list_bind.
    eauto.
  Qed.

  Lemma decompose_L1v_referrenced H L :
    decompose_L1v H L ⊆ referrenced_vertices_hg H.
  Proof.
    unfold decompose_L1v.
    rewrite vertices_hg_decomp.
    cbn.
    apply union_subseteq, conj.
    + apply referrenced_vertices_hg_subseteq.
      apply decompose_L1_subseteq.
    + rewrite intersection_subseteq_r.
      apply referrenced_vertices_hg_subseteq.
      cbn.
      apply map_filter_subseteq.
  Qed.

  Lemma decompose_C1v_referrenced H L :
    decompose_C1v H L ⊆ referrenced_vertices_hg H.
  Proof.
    unfold decompose_C1v.
    rewrite vertices_hg_decomp.
    cbn.
    apply union_subseteq, conj.
    + apply referrenced_vertices_hg_subseteq.
      apply decompose_C1_subseteq.
    + rewrite intersection_subseteq_r.
      apply referrenced_vertices_hg_subseteq.
      cbn.
      apply all_paths_idx_subset.
  Qed.

  Lemma hypervertices_mk_sub_hg H L :
    hypervertices (mk_sub_hg H L) = hypervertices H ∩ referrenced_vertices_hg (mk_hg L ∅).
  Proof.
    done.
  Qed.

  Lemma referrenced_vertices_hg_mk_sub_hg H L :
    referrenced_vertices_hg (mk_sub_hg H L) =
    referrenced_vertices_hg (mk_hg L ∅).
  Proof.
    done.
  Qed.

  (* FALSE!!!! *)
  (* Lemma decompose_C1v_C2v_subseteq H L isolated inputs outputs :
    isolated ## referrenced_vertices_hg H ->
    decompose_C1v H L ∩ decompose_C2v H L (decompose_C1 H L) isolated ⊆
      decompose_kset H L (decompose_C1 H L) isolated inputs outputs. *)


  Lemma list_to_set_list_to_vec {A B} `{SA : Singleton A B} `{EB : Empty B} `{UB : Union B}  (l : list A) : @list_to_set A B SA EB UB (list_to_vec l) = list_to_set l.
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      rewrite IHl; auto.
  Qed.

  Lemma list_to_vec_app {A B} {SA : Singleton A B} {UB : Union B} {EB : Empty B} {EAB : ElemOf A B} {LEQ : LeibnizEquiv B} {SSAB : SemiSet A B} (v u : list A) :
    @list_to_set A B SA EB UB (list_to_vec v +++ list_to_vec u) =
    @list_to_set A B SA EB UB (list_to_vec v) ∪ list_to_set (list_to_vec u).
  Proof.
    induction v.
    - simpl.
      rewrite (union_empty_l_L ).
      reflexivity.
    - simpl.
      rewrite IHv.
      rewrite union_assoc_L.
      reflexivity.
  Qed.

  Check hg_ext.

  Lemma decompose_is_graph {n m} (H : CospanHyperGraph T n m) (L : list positive) :
  H = decompose H L.
  Proof.
    apply cohg_ext; try reflexivity.
    apply hg_ext.
    - simpl.
      (* rewrite map_empty_union. *)
      rewrite map_union_assoc.
      rewrite map_difference_union; [reflexivity|].
      apply map_union_least.
      + apply all_paths_idx_subset.
      + apply map_filter_subseteq.
    - unfold decompose.
      remember (all_paths_idx H L) as C1.
      remember (subgraph_index H L) as L1.
      remember (H.(hedges).(hyperedges) ∖ (C1 ∪ L1)) as C2.
      simpl.
      repeat rewrite hg_empty_union.
      repeat rewrite union_empty_l_L.
      (* We rebuild the let expressions used in the decompose function.
         This helps alleviate the pain. *)
      remember ({| hyperedges := C1; hypervertices := ∅ |}) as C1'.
      remember ({| hyperedges := C2; hypervertices := isolated_vertices H |}) as C2'.
      remember (vertices_hg L1) as Lv.
      remember (vertices_hg C1') as C1v.
      remember (vertices_hg C2') as C2v.
      repeat rewrite union_empty_l_L.
      repeat rewrite hg_empty_union.
      repeat rewrite vec_to_list_app.
      repeat rewrite list_to_set_app_L.
      repeat rewrite list_to_vec_app.
      repeat rewrite list_to_set_list_to_vec.
      repeat rewrite list_to_set_elements_L.
      rewrite vertices_hg_add_vertices.
      rewrite vertices_hg_union.
      rewrite <- HeqLv, <- HeqC2v.
      remember (C1v ∩ C2v ∪ list_to_set (inputs H) ∩ list_to_set (outputs H)) as k.
      remember (Lv ∩ C1v ∪ Lv ∩ list_to_set (inputs H)) as i.
      remember ((Lv ∩ C2v ∪ Lv ∩ list_to_set (outputs H))) as j.
      replace (hypervertices L1) with (@empty Pset _) by (rewrite HeqL1; now unfold subgraph_index).
      rewrite union_empty_l_L.
      remember (C1v ∩ C2v) as c12.
      remember (list_to_set (inputs H)) as inpH.
      remember (list_to_set (outputs H)) as outH.
      remember (inpH ∩ outH) as passH.
      remember (Lv ∩ C1v) as lc1.
      remember (Lv ∩ inpH) as lin.
      remember (Lv ∩ C2v) as lc2.
      remember (Lv ∩ outH) as lout.
      remember (C1v ∪ inpH) as C1vin.
      remember (C2v ∪ outH) as C2vout.
      replace (C1vin ∩ C2vout ∖ Lv ∪ Lv ∩ C2vout) with
        ((C1vin ∪ Lv) ∩ C2vout). 2:{
          transitivity ((C1vin ∖ Lv) ∩ (C2vout ∖ Lv) ∪ Lv ∩ C2vout); [|set_solver].

          (* rewrite (difference_intersection_distr_l_L C1vin C2vout Lv).
          Unset Printing Notations. *)
          rewrite (union_intersection_r_L (_ ∖ _) (_ ∖ _) (Lv ∩ C2vout)).
          rewrite (intersection_comm_L Lv C2vout).
          rewrite (difference_union_intersection_L).
          transitivity ((C1vin ∖ Lv ∪ Lv) ∩ C2vout); [|set_solver].
          rewrite difference_union_L.
          reflexivity.

        }
      (* rewrite  *)

      rewrite (difference_intersection_distr_l_L _ _ (Lv)).

      replace ((C1vin ∪ Lv) ∩ C2vout ∖ (Lv ∪ C2v)) with
        ((C1vin ∩ outH) ∖ (Lv ∪ C2v)) by set_solver.
      rewrite (union_comm_L (Lv ∪ C2v)), difference_union_L.
      replace ((C1v ∪ (C1vin ∩ outH ∪ (Lv ∪ C2v)))) with
        ((C1v ∪ (inpH ∩ outH) ∪ Lv ∪ C2v)) by set_solver.
      replace (((C1vin ∖ Lv) ∩ C2vout ∖ Lv ∪ Lv ∩ C1vin)
        ∖ (C1v ∪ inpH ∩ outH ∪ Lv ∪ C2v)) with (∅ :> Pset) by set_solver.
      rewrite union_empty_l_L.
        2:{
        set_solver.
}
        subst C2vout.
        subst C1vin.

        set_solver.

        set_solver.
        set_solver.
      }

      apply leibniz_equiv_iff, set_subseteq_antisymm; cycle 1.
      + rewrite ?union_subseteq.
        split_and!; [..|set_solver].
        admit.
        rewrite <- subseteq_union_r.
        apply union_subseteq.
        split; [|set_solver].
        rewrite intersection_union_l_L.
        rewrite <- subseteq_union_r.
        apply union_subseteq; split; [set_solver|].

        set_solver.
        set_solver.
        2:{

        }


        set_solver.
        set_solver.
        rewrite (intersection_comm_L (C1v ∪ _) (_ ∪ _)).
        rewrite (difference_intersection_distr_l_L (C2v ∪ _)).
        rewrite difference_union_L.
        set_solver.


      admit.






      rewrite Heqi, Heqj, Heqk.
      rewrite (difference_union_distr_l_L (c12 ∪ passH) (lc2 ∪ lout)).
      rewrite (difference_union_distr_l_L lc2 lout).
      replace (lc2 ∖ (Lv ∪ C2v)) with (@empty Pset _) by set_solver.
      replace (lout ∖ (Lv ∪ C2v)) with (@empty Pset _) by set_solver.
      rewrite (difference_union_distr_l_L c12 passH (Lv ∪ C2v)).
      replace (c12 ∖ (Lv ∪ C2v)) with (@empty Pset _) by set_solver.
      rewrite 2 union_empty_l_L.
      rewrite union_empty_r_L.
      unfold isolated_vertices.
      apply leibniz_equiv_iff.
      apply set_subseteq_antisymm.
      + admit.
      + apply union_subseteq, conj.
        rewrite difference_union_distr_l_L.
        apply union_subseteq, conj.
        rewrite difference_union_distr_l_L.
        apply union_subseteq, conj.
        set_solver.
        2:
        set_solver.
        rewrite (union_comm_L (_ ∪ _)).
        rewrite difference_union_L.
        set_solver.
        apply union_subseteq, conj; [|set_solver +].
        apply subseteq_union_r.
      remember (passH ∖ (Lv ∪ C2v)) as passMinus.
      rewrite (difference_union_distr_l_L (Lv ∪ C2v) passH (Lv ∪ C2v)).
      repeat rewrite union_assoc_L.
      rewrite (difference_union_distr_l_L (C1v ∪ Lv ∪ C2v) passH (Lv ∪ C2v)).
      assert ((k ∪ i) ∖ (C1v ∪ Lv ∪ C2v ∪ (k ∪ j) ∖ (Lv ∪ C2v)) = ∅).
      {

        rewrite Heqi, Heqk.
        repeat rewrite difference_union_distr_l_L.
      }
      rewrite Heqi, Heqj, Heqk.
      remember (list_to_set (inputs H)) as inpH.
      remember (list_to_set (outputs H)) as outH.
      Search (_ ∪ _ ∖ _).
      rewrite difference_union_distr_l_L.

      Search (_ ⊆ _ -> _ = _ ∪ _).
      set_solver.
      Search (vertices_hg _).
      rewrite Heqi, Heqj, Heqk.
      set_solver.

      rewrite HeqL1 at 1.
      remember (vertices_hg L1) as Lv'.
      rewrite (subseteq_empty_difference_L _ (Lv' ∪ C2v)),
              (subseteq_empty_difference_L _ (C1v ∪ _)).
      + assert (hypervertices L1 = ∅).
        { rewrite HeqL1. simpl. reflexivity. }
        rewrite H0.
        repeat rewrite union_empty_l_L.
        done.
      + rewrite hg_add_vertices_empty.
        apply union_subseteq_l'.
        apply union_least.
        *
          apply intersection_subseteq_l.
        * apply intersection_subseteq_r.
      + apply union_least.
        * apply union_subseteq_r'.
          apply intersection_subseteq_r.
        * apply union_subseteq_r'.
          apply intersection_subseteq_r.
  Qed.

  Definition DoublePushout {n m} (H : CospanHyperGraph T n m) (G : HyperGraph T) (L : list positive) : CospanHyperGraph T n m :=
  let C1 := all_paths_idx H L in
  let L1 := subgraph_index H L in
  let C2 := H.(hedges).(hyperedges) ∖ (C1 ∪ L1) in
  let C1' := vertices_hg {| hyperedges := C1; hypervertices := ∅ |} in
  let L1' := vertices_hg L1 in
  let C2' := vertices_hg {| hyperedges := C2; hypervertices := H.(hypervertices) |} in
  let i := list_to_vec(elements(L1' ∩ C1')) in
  let j := list_to_vec(elements(L1' ∩ C2')) in
  let k := list_to_vec(elements(C1' ∩ C2')) in
  compose_graphs_unsafe (
  H.(inputs) -> {| hyperedges := C1; hypervertices := ∅ |}  <- (k +++ i)
  ) (compose_graphs_unsafe
  ( stack_graphs_aux (k -> ∅ <- k)
                 (i -> G <- j)
  ) (
  k +++ j -> {| hyperedges := C2; hypervertices := H.(hypervertices) |} <- H.(outputs)
  )).

  Locate cohg_semantic_eq.

End DPO.

Lemma reindex_is_isomorphic {T n m} (f : positive -> positive) (finj : Inj eq eq f) (cohg : CospanHyperGraph T n m) :
  isomorphic cohg (relabel_graph f (reindex_graph f cohg)).
Proof.
  rewrite isomorphic_exists.
  exists f, f; auto.
Qed.

#[export] Instance compose_graphs_struct_isomorphic_Proper {T n m o} :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@compose_graphs T n m o).
Proof.
  intros ? ? ? ? ? ?; now apply compose_graphs_struct_isomorphic.
Qed.

#[export] Instance stack_graphs_struct_isomorphic_Proper {T n1 m1 n2 m2} :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@stack_graphs T n1 m1 n2 m2).
Proof.
  intros ? ? ? ? ? ?.
  unfold struct_isomorphic.
  rewrite 2 norm_verts_stack_graphs.
  now apply stack_graphs_isomorphic.
Qed.

Lemma vertices_compose_graphs_unsafe {T n m o} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T m o) :
  outputs cohg = inputs cohg' ->
  hyperedges cohg ##ₘ hyperedges cohg' ->
  vertices (compose_graphs_unsafe cohg cohg') =
  vertices cohg ∪ vertices cohg'.
Proof.
  intros Hoi Hdisj.
  rewrite 3 vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_add_vertices.
  rewrite vertices_hg_union by done.
  rewrite <- Hoi.
  rewrite (union_comm_L (_ ∪ _) (_ ∖ _)).
  rewrite difference_union_L.
  set_solver.
Qed.

Lemma vertices_stack_graphs_aux {T n1 m1 n2 m2} (cohg : CospanHyperGraph T n1 m1)
  (cohg' : CospanHyperGraph T n2 m2) :
  hyperedges cohg ##ₘ hyperedges cohg' ->
  vertices (stack_graphs_aux cohg cohg') =
  vertices cohg ∪ vertices cohg'.
Proof.
  intros Hdisj.
  rewrite 3 vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_union by done.
  rewrite 2 vec_to_list_app, !list_to_set_app_L.
  set_solver.
Qed.

Lemma vertices_hg_empty {T} : @vertices_hg T ∅ = ∅.
Proof.
  done.
Qed.


Check all_paths_idx.
Check subgraph_index.
Print HyperGraph.

Open Scope positive.

Definition example_1 : CospanHyperGraph positive 1 1 :=
  [# 1 ] -> {| hyperedges := {[ 1 := (1, [],[]) ]};
     hypervertices := ∅
  |} <- [# 1].

  Lemma decompose_1 : example_1 = ([# 1] -> ∅ <- [# 1]).
  Proof.
    unfold example_1.
    rewrite (decompose_is_graph) with (L:=[]).
    unfold decompose.
    unfold inputs.
    unfold outputs.
    remember (all_paths_idx ([# 1] -> ∅ <- [# 1]) []) as C1.
    remember (subgraph_index ([# 1] -> ∅ <- [# 1]) []) as L1.
    remember ((([# 1] -> ∅ <- [# 1])).(hedges).(hyperedges) ∖ (C1 ∪ L1)) as C2.
    simpl.
    (* We rebuild the let expressions used in the decompose function.
       This helps alleviate the pain. *)
    remember ({| hyperedges := C1; hypervertices := ∅ |}) as C1'.
    remember ({| hyperedges := L1; hypervertices := ∅ |}) as L1'.
    remember ({| hyperedges := C2; hypervertices := ∅ |}) as C2'.
    remember (vertices_hg L1) as Lv.
    (* remember (all_vertices L1') as Lv'. *)
    remember (vertices_hg C1') as C1v.
    remember (vertices_hg C2') as C2v.
    rewrite HeqC1' in HeqC1v.
    unfold vertices_hg in HeqC1v.
    simpl.

Check all_paths_idx.
Check subgraph_index.
Print HyperGraph.

Open Scope positive.

Definition example_1 : CospanHyperGraph positive 1 1 :=
  [# 1 ] -> {| hyperedges := {[ 1 := (1, [],[]) ]};
     hypervertices := ∅
  |} <- [# 1].

  Lemma decompose_1 : example_1 = ([# 1] -> ∅ <- [# 1]).
  Proof.
    unfold example_1.
    rewrite (decompose_is_graph) with (L:=[]).
    unfold decompose.
    unfold inputs.
    unfold outputs.
    remember (all_paths_idx ([# 1] -> ∅ <- [# 1]) []) as C1.
    remember (subgraph_index ([# 1] -> ∅ <- [# 1]) []) as L1.
    remember ((([# 1] -> ∅ <- [# 1])).(hedges).(hyperedges) ∖ (C1 ∪ L1)) as C2.
    simpl.
    (* We rebuild the let expressions used in the decompose function.
       This helps alleviate the pain. *)
    remember ({| hyperedges := C1; hypervertices := ∅ |}) as C1'.
    remember ({| hyperedges := L1; hypervertices := ∅ |}) as L1'.
    remember ({| hyperedges := C2; hypervertices := ∅ |}) as C2'.
    remember (vertices_hg L1) as Lv.
    (* remember (all_vertices L1') as Lv'. *)
    remember (vertices_hg C1') as C1v.
    remember (vertices_hg C2') as C2v.
    rewrite HeqC1' in HeqC1v.
    unfold vertices_hg in HeqC1v.
    simpl.

Lemma DPO_equiv {n m} `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
  (Target : CospanHyperGraph T n m)
  (G : HyperGraph T) (L : list positive) :
    (forall {o p} (v0 : vec positive o) (v1 : vec positive p),
      (v0 -> G <- v1) ≡ₜ (v0 -> (subgraph_index Target L) <- v1))
      -> Target ≡ₜ (DoublePushout Target G L).
  Proof.
    intros.
    rewrite (decompose_is_graph Target L) at 1.
    unfold decompose, DoublePushout.
    remember (all_paths_idx Target L) as C1.
    remember (subgraph_index Target L) as L1.
    remember (Target.(hedges).(hyperedges) ∖ (C1 ∪ L1)) as C2.
    remember ({| hyperedges := C1; hypervertices := ∅ |}) as C1'.
    remember ({| hyperedges := C2; hypervertices := hypervertices Target |}) as C2'.
    remember (vertices_hg L1) as Lv.
    remember (vertices_hg C1') as C1v.
    remember (vertices_hg C2') as C2v.
    remember (list_to_vec (elements (Lv ∩ C1v))) as i.
    remember (list_to_vec (elements (Lv ∩ C2v))) as j.
    remember (list_to_vec (elements (C1v ∩ C2v))) as k.
    assert (L1 = {| hyperedges := L1; hypervertices := ∅ |}).
    { rewrite HeqL1; now apply hg_ext. }
    rewrite compose_graphs_unsafe_to_compose_graphs.
    2:{ reflexivity. }
    2:{ simpl.
        rewrite Heqi, Heqk.
        rewrite list_to_vec_app.
        repeat rewrite list_to_set_list_to_vec.
        repeat rewrite list_to_set_elements_L.
        rewrite <- Heqi, <- Heqk.
        unfold vertices.
        simpl.
        rewrite list_to_set_app_L.
        rewrite hg_empty_union.
        rewrite <- HeqC1v, <- HeqC2v, <- HeqLv.
        rewrite Heqi, Heqk, Heqj.
        rewrite list_to_set_app_L.
        repeat rewrite list_to_vec_app.
        repeat rewrite list_to_set_list_to_vec.
        repeat rewrite list_to_set_elements_L.
        remember  (C1v ∩ C2v ∪ Lv ∩ C1v) as intr.
        rewrite 3 difference_union_distr_l.
        rewrite  (difference_union_distr_l_L (intr) (list_to_set (outputs Target))).
        rewrite difference_diag.
        rewrite union_empty_l_L.
        rewrite union_empty_r_L.
        rewrite (subseteq_empty_difference_L ((C1v ∩ C2v ∪ Lv ∩ C2v))).
        rewrite hg_add_vertices_empty.
        rewrite vertices_hg_union.
        rewrite <- HeqC2v, <- HeqLv.
        rewrite (difference_union_distr_l_L Lv).
        rewrite disjoint_union_l.
        rewrite 4 disjoint_union_r.
        repeat split.
        - set_solver.
        - set_solver.
        - rewrite Heqintr.
          Search (_ ## _ ∖ _).
          set_solver.
          admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
    }
    rewrite compose_graphs_unsafe_to_compose_graphs by admit.
    rewrite compose_graphs_unsafe_to_compose_graphs by admit.
    rewrite compose_graphs_unsafe_to_compose_graphs by admit.
    refine (compose_graphs_semantic_eq _ _ _ _ _ _).
    1:{ reflexivity. }
    refine (compose_graphs_semantic_eq _ _ _ _ _ _); [|reflexivity].
    rewrite stack_graphs_aux_to_stack_graphs_disjoint by admit.
    rewrite stack_graphs_aux_to_stack_graphs_disjoint by admit.
    f_equiv.
    symmetry.
    auto.
Admitted.

  Open Scope positive.

  Print HyperEdge.

  Definition example : HyperGraph positive.
  Proof.
    constructor.
    - exact {[ 1 := (1, [], [2]) ; 2 := (2, [2], [4]) ; 3 := (3, [], [3]) ; 4 := (4, [3; 4], []) ]}.
    - exact ∅.
  Defined.

  Definition ex_1 : HyperGraph positive :=
    {| hyperedges := {[ 1 := (1, [2; 1], [3]) ]}; hypervertices := ∅ |}.

  Definition ex_2 : HyperGraph positive :=
    {| hyperedges := {[ 2 := (2, [1; 2; 3], []) ]}; hypervertices := ∅ |}.

  Definition ex_1cohg := [#1] -> ex_1 <- [#1; 2].

  Definition ex_2cohg := [#1;2] -> ex_2 <- [#3].

  Compute (compose_graphs_unsafe ex_1cohg ex_2cohg).

  Definition example' : HyperGraph positive.
  Proof.
    constructor.
    - exact {[ 4 := (5, [3; 4], []) ]}.
    - exact ∅.
  Defined.

  Check all_paths.

  Compute all_paths example ({[ 3 := (4, [], [3]) ; 4 := (5, [3; 4], []) ]}).
  Compute all_paths_idx example [4].

  Compute (predecessors example (5, [3; 4], [])).
  Compute (elements (dom (predecessors_idx example 4))).

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
  do 2 f_equiv; [done..|].
  now rewrite He1, He2.
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
  do 2 f_equiv; [done..|].
  now rewrite He1, He2.
Qed.
