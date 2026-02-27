From stdpp Require Export pmap gmap decidable.
Require Import TensorGraph.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.


Local Open Scope nat_scope.

Section DPO.

  Context {T : Type}.

  Definition all_vertices (H : HyperGraph T) : Pset := 
    map_fold (fun k h s => (list_to_set h.1.2 ∪ list_to_set h.2) ∪ s) 
    (H.(hypervertices)) (H.(hyperedges)).
  

  Definition compose_graphs_aux {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs)
      (tgl.(inputs) ->
        hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set tgr.(inputs) ∖ (all_vertices tgl ∪ all_vertices tgr))
          <- tgr.(outputs)).

  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_graphs {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs :=
        propogate_subst (vzip (vmap (bcons false) tgl.(outputs)) (vmap (bcons true) tgr.(inputs))) in
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) ->
      hg_add_vertices (tgl.(hedges) ⊎ tgr.(hedges)) 
        ((list_to_set (vmap (bcons true) tgr.(inputs)) ∖ 
          (all_vertices (reindex_graph (bcons false) (relabel_graph (bcons false) tgl)) ∪
           all_vertices (reindex_graph (bcons true) (relabel_graph (bcons true) tgr))))) 
           <- (vmap (bcons true) tgr.(outputs))).


  Definition compose_graphs_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set (tgr.(inputs)) ∖ (all_vertices tgl ∪ all_vertices tgr)) <- tgr.(outputs).

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
  unfold compose_graphs_aux.
  apply cohg_ext.
  - simpl.
    f_equal.
    
    admit.
  - f_equal.
  - f_equal.
  (* reflexivity. *)
Admitted.
  (* reflexivity. *)
(* Qed. *)

Lemma compose_graphs_alt_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs tgl tgr) =
    compose_graphs tgl tgr.
Proof.
  rewrite add_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  rewrite <- 2 reindex_relabel_hg.
  (* done.
Qed. *)
Admitted.

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
      Exists (fun p => p ∈ (h'.2)) (h.1.2).

    Definition predecessor (h h' : HyperEdge T) :=
      Exists (fun p => p ∈ (h.2)) (h'.1.2).

    Instance successor_decide (h h' : HyperEdge T) : Decision (successor h h') := _.
    Instance predecessor_decide (h h' : HyperEdge T) : Decision (predecessor h h') := _.

    Definition successors (h : HyperEdge T) : Pmap (HyperEdge T) :=
      map_filter (fun ka => successor ka.2 h) _ H.(hyperedges).

    Definition predecessors (h : HyperEdge T) : Pmap (HyperEdge T) :=
      map_filter (fun ka => predecessor ka.2 h) _ H.(hyperedges).

    Definition all_successors (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) := map_filter 
      (fun kh' => Exists (fun kh => successor kh'.2 kh.2) (map_to_list G)) 
      _ H.(hyperedges).
    
    Definition all_predecessors (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) := map_filter 
      (fun kh' => Exists (fun kh => predecessor kh'.2 kh.2) (map_to_list G)) 
      _ H.(hyperedges).

    Fixpoint all_paths_aux
      (G : Pmap (HyperEdge T)) (n : nat) : Pmap (HyperEdge T) :=
    match n with
    | 0     => ∅
    | (S k) => let step := all_predecessors G in
      step ∖ G ∪ all_paths_aux step k
    end.

    Definition all_paths (G : Pmap (HyperEdge T)) : Pmap (HyperEdge T) :=
      all_paths_aux G (length (map_to_list H.(hyperedges))).

    Definition all_paths_idx (pdx : list positive) : Pmap (HyperEdge T) :=
      all_paths (map_filter (fun ka => ka.1 ∈ pdx) _ (H.(hyperedges))).

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
      destruct h as [[]].
      simpl.
      induction l.
      - right. intros X.
        inversion X.
      - specialize (decide (v = a)) as [].
        + subst; left; left.
        + destruct IHl.
          * left; now right.
          * right. intros C.
            inversion C; auto. 
    Defined.

    Definition v_succ_decide (v : positive) (h : HyperEdge T) : Decision (v_succ v h).
    Proof.
      unfold v_succ.
      destruct h as [[]].
      simpl.
      induction l0.
      - right. intros X.
        inversion X.
      - specialize (decide (v = a)) as [].
        + subst; left; left.
        + destruct IHl0.
          * left; now right.
          * right. intros C.
            inversion C; auto. 
    Defined.

      Instance vpred_decide (v : positive) (h : HyperEdge T) : Decision (v_pred v h) := {
        decide := v_pred_decide v h
      }.
      Instance vsucc_decide (v : positive) (h : HyperEdge T) : Decision (v_succ v h) := {
        decide := v_succ_decide v h
      }.

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

    Instance elemof_hyperedge : ElemOf positive (HyperEdge T) :=
      (fun p he => p ∈ he.2 \/ p ∈ he.1.2).

    Instance elemof_pair : ElemOf positive (list positive * list positive) :=
      (fun p pr => p ∈ pr.1 \/ p ∈ pr.2).

    Instance elemof_option `{ElemOf A B} : ElemOf A (option B) :=
      fun a opb =>
        match opb with
        | Some x => a ∈ x
        | None => False
        end.

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
    map_filter (fun ka => (ka.1 ∈ L)) _ H.(hyperedges).

  Definition subgraph_index (H : HyperGraph T) (L : list positive) : HyperGraph T :=
  {| hyperedges := subgraph_index_aux H L; 
     hypervertices := ∅ |}.

  Definition decompose {n m} (H : CospanHyperGraph T n m) (L : list positive) : CospanHyperGraph T n m :=
  let C1 := all_paths_idx H L in
  let L1 := subgraph_index H L in
  let C2 := H.(hedges).(hyperedges) ∖ (C1 ∪ L1) in
  let C1' := all_vertices {| hyperedges := C1; hypervertices := ∅ |} in
  let L1' := all_vertices L1 in
  let C2' := all_vertices {| hyperedges := C2; hypervertices := H.(hypervertices) |} in
  let i := list_to_vec(elements(L1' ∩ C1')) in
  let j := list_to_vec(elements(L1' ∩ C2')) in
  let k := list_to_vec(elements(C1' ∩ C2')) in
  compose_graphs_unsafe (
  H.(inputs) -> {| hyperedges := C1; hypervertices := ∅ |}  <- (k +++ i)
  ) (compose_graphs_unsafe
  ( stack_graphs_aux (k -> ∅ <- k)
                 (i -> {| hyperedges := L1; hypervertices := ∅ |} <- j)
  ) (
  k +++ j -> {| hyperedges := C2; hypervertices := H.(hypervertices) |} <- H.(outputs)
  )).

  Lemma all_paths_subset (H L : HyperGraph T) :
    all_paths H L ⊆ H.
  Proof.
    generalize dependent L.
    unfold all_paths.
    induction (length (map_to_list H.(hyperedges))); intros.
    - apply map_empty_subseteq.
    - simpl.
      apply map_union_least.
      + apply map_subseteq_difference_l.
        apply map_filter_subseteq.
      + apply (IHn (mk_hg (all_predecessors H L) ∅)).
  Qed.

  Lemma all_paths_idx_subset {n m} (H : CospanHyperGraph T n m) (L : list positive) : all_paths_idx H L ⊆ H.
  Proof.
    unfold all_paths_idx.
    remember ((map_filter (λ ka : positive * HyperEdge T, ka.1 ∈ L) (λ x : positive * HyperEdge T, decide_rel elem_of x.1 L) H.(hyperedges))) as L'.
    apply (all_paths_subset H (mk_hg L' ∅)).
  Qed.

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
      rewrite map_empty_union.
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
      (* We rebuild the let expressions used in the decompose function.
         This helps alleviate the pain. *)
      remember ({| hyperedges := C1; hypervertices := ∅ |}) as C1'.
      remember ({| hyperedges := L1; hypervertices := ∅ |}) as L1'.
      remember ({| hyperedges := C2; hypervertices := hypervertices H |}) as C2'.
      remember (all_vertices L1) as Lv.
      (* remember (all_vertices L1') as Lv'. *)
      remember (all_vertices C1') as C1v.
      remember (all_vertices C2') as C2v.
      repeat rewrite union_empty_l_L.
      repeat rewrite hg_empty_union.
      repeat rewrite list_to_vec_app.
      repeat rewrite list_to_set_list_to_vec.
      repeat rewrite list_to_set_elements_L.
      remember (all_vertices L1') as Lv'.
      rewrite (subseteq_empty_difference_L _ (Lv' ∪ C2v)),
              (subseteq_empty_difference_L _ (C1v ∪ _)).
      + repeat rewrite union_empty_l_L.
        done.
      + rewrite hg_add_vertices_empty.
        apply union_subseteq_l'.
        apply union_least.
        * apply intersection_subseteq_l.
        * apply intersection_subseteq_r.
      + apply union_least.
        * apply union_subseteq_r'.
          apply intersection_subseteq_r.
        * apply union_subseteq_r'.
          apply intersection_subseteq_r. 
  Qed.

End DPO.

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