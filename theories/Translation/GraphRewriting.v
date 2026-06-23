From stdpp Require Export pmap gmap decidable.
From TensorRocq Require Import CospanHyperGraph StackComposeCorrect HyperGraph Aux_pos Syntax Aux_stdpp.

Local Open Scope nat_scope.



Section DPO.

Context {T : Type}.

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
    mk_hg mh (hypervertices H ∩ referenced_vertices_hg (mk_hg mh ∅)).

  Section decompose_defs.

  Context (H : HyperGraph T) (L : list positive).

  Definition decompose_L1 : HyperGraph T :=
    mk_sub_hg H (subgraph_index_aux H L).

  Definition decompose_C1 inputs : HyperGraph T :=
    hg_add_vertices (mk_sub_hg H (all_paths_idx H L)) (hypervertices H ∩ inputs).

  Definition decompose_C2 (C1 : HyperGraph T) (isolated : Pset)
    outputs : HyperGraph T :=
    hg_add_vertices (mk_sub_hg H ((hyperedges H) ∖ (C1 ∪ subgraph_index H L)))
      (hypervertices H ∩ outputs ∪ isolated).

  Definition decompose_L1v : Pset :=
    vertices_hg decompose_L1.

  Definition decompose_C1v inputs : Pset :=
    vertices_hg (decompose_C1 inputs).

  Definition decompose_C2v C1 isolated outputs : Pset :=
    vertices_hg (decompose_C2 C1 isolated outputs).


  Definition decompose_iset (inputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C1v inputs ∪ inputs).

  Definition decompose_jset C1 isolated (outputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C2v C1 isolated outputs ∪ outputs).

  Definition decompose_kset C1 isolated (inputs outputs : Pset) : Pset :=
    ((decompose_C1v inputs ∪ inputs) ∩ (decompose_C2v C1 isolated outputs ∪ outputs) ∖ decompose_L1v).

  End decompose_defs.

  Definition decompose {n m} (H : CospanHyperGraph T n m) (L : list positive) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs_unsafe' (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs_unsafe' (
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

  Lemma decompose_L1_C1_disjoint H L inputs :
    hyperedges $ decompose_L1 H L ##ₘ hyperedges $ decompose_C1 H L inputs.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_dom.
    intros k Hk%all_paths_idx_dom_disjoint
      HkL%subgraph_index_aux_dom_subseteq%intersection_subseteq_r.
    auto.
  Qed.

  Lemma decompose_C1_C2_disjoint_gen H L C1 isolated outputs :
    hyperedges $ C1 ##ₘ hyperedges $ decompose_C2 H L C1 isolated outputs.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_difference_l.
    apply map_union_subseteq_l.
  Qed.

  Lemma decompose_L1_C2_disjoint H L C1 isolated outputs :
    hyperedges $ decompose_L1 H L ##ₘ hyperedges $ decompose_C2 H L C1 isolated outputs.
  Proof.
    cbn.
    symmetry.
    apply map_disjoint_dom.
    rewrite dom_difference_L, dom_union_L.
    set_solver.
  Qed.

  Lemma decompose_L1v_C1v_subseteq H L inputs :
    decompose_L1v H L ∩ decompose_C1v H L inputs ⊆ decompose_iset H L inputs.
  Proof.
    set_solver.
  Qed.

  Lemma decompose_L1v_C2v_subseteq H L C1 isolated outputs :
    decompose_L1v H L ∩ decompose_C2v H L C1 isolated outputs ⊆
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

  Lemma decompose_C1_subseteq H L inputs :
    hyperedges $ decompose_C1 H L inputs ⊆ hyperedges H.
  Proof.
    cbn.
    apply all_paths_idx_subset.
  Qed.

  Lemma decompose_C2_subseteq H L C1 isolated outputs :
    hyperedges $ decompose_C2 H L C1 isolated outputs ⊆ hyperedges H.
  Proof.
    cbn.
    now apply map_subseteq_difference_l.
  Qed.

  Lemma referenced_vertices_hg_subseteq (H G : HyperGraph T) :
    hyperedges H ⊆ hyperedges G ->
    referenced_vertices_hg H ⊆ referenced_vertices_hg G.
  Proof.
    unfold referenced_vertices_hg.
    intros HHG.
    intros k (ktio & Hktio & HkH)%elem_of_list_to_set%elem_of_list_bind.
    apply map_to_list_submseteq in HHG.
    pose proof (elem_of_submseteq _ _ _ HkH HHG).
    rewrite elem_of_list_to_set, elem_of_list_bind.
    eauto.
  Qed.

  Lemma decompose_L1v_referenced H L :
    decompose_L1v H L ⊆ referenced_vertices_hg H.
  Proof.
    unfold decompose_L1v.
    rewrite vertices_hg_decomp.
    cbn.
    apply union_subseteq, conj.
    - apply referenced_vertices_hg_subseteq.
      apply decompose_L1_subseteq.
    - rewrite intersection_subseteq_r.
      apply referenced_vertices_hg_subseteq.
      cbn.
      apply map_filter_subseteq.
  Qed.

  Lemma decompose_C1v_referenced H L inputs :
    decompose_C1v H L inputs ⊆ referenced_vertices_hg H ∪ hypervertices H ∩ inputs.
  Proof.
    unfold decompose_C1v.
    rewrite vertices_hg_decomp.
    cbn.
    rewrite 2 union_subseteq; split_and!.
    - apply union_subseteq_l'.
      apply referenced_vertices_hg_subseteq.
      apply decompose_C1_subseteq.
    - apply union_subseteq_r.
    - rewrite intersection_subseteq_r.
      apply union_subseteq_l'.
      apply referenced_vertices_hg_subseteq.
      cbn.
      apply all_paths_idx_subset.
  Qed.

  Lemma decompose_C2v_referenced H L C1 isolated outputs :
    decompose_C2v H L C1 isolated outputs ⊆
    referenced_vertices_hg H ∪ hypervertices H ∩ outputs ∪ isolated.
  Proof.
    unfold decompose_C2v.
    rewrite vertices_hg_decomp.
    cbn.
    rewrite 2 union_subseteq; split_and!.
    - do 2 apply union_subseteq_l'.
      apply referenced_vertices_hg_subseteq.
      apply decompose_C2_subseteq.
    - rewrite <- union_assoc_L.
      apply union_subseteq_r.
    - rewrite intersection_subseteq_r.
      do 2 apply union_subseteq_l'.
      apply referenced_vertices_hg_subseteq.
      cbn.
      now apply map_subseteq_difference_l.
  Qed.


  Lemma hypervertices_mk_sub_hg H L :
    hypervertices (mk_sub_hg H L) = hypervertices H ∩ referenced_vertices_hg (mk_hg L ∅).
  Proof.
    done.
  Qed.

  Lemma referenced_vertices_hg_mk_sub_hg H L :
    referenced_vertices_hg (mk_sub_hg H L) =
    referenced_vertices_hg (mk_hg L ∅).
  Proof.
    done.
  Qed.

  (* FALSE!!!! *)
  (* Lemma decompose_C1v_C2v_subseteq H L isolated inputs outputs :
    isolated ## referenced_vertices_hg H ->
    decompose_C1v H L ∩ decompose_C2v H L (decompose_C1 H L) isolated ⊆
      decompose_kset H L (decompose_C1 H L) isolated inputs outputs. *)

  Lemma difference_intersection_distr_l' `{Set_ A SA} (X Y Z : SA) :
    X ∩ Y ∖ Z ≡ (X ∖ Z) ∩ (Y ∖ Z).
  Proof.
    set_solver.
  Qed.

  Lemma difference_intersection_distr_l'_L `{Set_ A SA, !LeibnizEquiv SA} (X Y Z : SA) :
    X ∩ Y ∖ Z = (X ∖ Z) ∩ (Y ∖ Z).
  Proof.
    unfold_leibniz.
    apply difference_intersection_distr_l'.
  Qed.

  Lemma decompose_iset_disjoint_kset H L C1 isolated inputs outputs :
    decompose_iset H L inputs ## decompose_kset H L C1 isolated inputs outputs.
  Proof.
    set_solver.
  Qed.

  Lemma decompose_jset_disjoint_kset H L C1 isolated inputs outputs :
    decompose_jset H L C1 isolated outputs ## decompose_kset H L C1 isolated inputs outputs.
  Proof.
    set_solver.
  Qed.

  (* Lemma decompose_iset_union_kset H L C1 isolated inputs outputs :
    decompose_iset H L inputs ∪ decompose_kset H L C1 isolated inputs outputs =
    decompose_C1v H L inputs ∪ inputs ∪
      decompose_L1v H L ∩ (decompose_C1v H L inputs ∪ inputs) ∪
      decompose_C2v H L C1 isolated outputs ∖ decompose_L1v H L.
  Proof.
    unfold decompose_iset, decompose_kset.
    rewrite (difference_intersection_distr_l'_L (_ ∪ _)).
    rewrite union_intersection_l_L.
    rewrite (union_comm_L (decompose_L1v H L ∩ _) (_ ∖ _)).
    rewrite (intersection_comm_L (decompose_L1v H L)).
    rewrite difference_union_intersection_L.
    rewrite intersection_union_l_L.
    rewrite (intersection_assoc_L _), (intersection_idemp_L _).
    (* set_solver.
    rewrite (union_intersection_l_L (_ ∩ _) (_ ∖ _) (_ ∖ _)).
    rewrite difference_union. *)
  Admitted. *)

  (* Lemma decompose_C1v_C2v_subseteq H L isolated inputs outputs :
    isolated ## referenced_vertices_hg H ∪ inputs ∪ outputs ->
    decompose_C1v H L ∩
      (decompose_L1v H L ∪ decompose_C2v H L (decompose_C1 H L) isolated) ⊆
      decompose_kset H L (decompose_C1 H L) isolated inputs outputs
      ∪ decompose_jset H L (decompose_C1 H L) isolated outputs.
  Proof.
    intros Hdisj.
    rewrite intersection_union_l_L.
    rewrite union_subseteq; split; try
    set_solver.
    - unfold decompose_kset, decompose_jset.
  Admitted. *)


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



  Lemma decompose_C1_L1_C2_total H L isolated inputs outputs :
    hyperedges (decompose_C1 H L inputs ∪ decompose_L1 H L ∪
      decompose_C2 H L (decompose_C1 H L inputs) isolated outputs) =
    hyperedges H.
  Proof.
    cbn -[decompose_C1].
    apply map_difference_union.
    apply map_union_least.
    - apply decompose_C1_subseteq.
    - apply decompose_L1_subseteq.
  Qed.

  Lemma referenced_vertices_hg_union (H G : HyperGraph T) :
    hyperedges H ##ₘ hyperedges G ->
    referenced_vertices_hg (H ∪ G) =
    referenced_vertices_hg H ∪ referenced_vertices_hg G.
  Proof.
    intros Hdisj.
    unfold referenced_vertices_hg.
    cbn.
    rewrite map_to_list_disj_union by done.
    now rewrite bind_app, list_to_set_app_L.
  Qed.

  Lemma decompose_C1_L1_C2_total_refererenced_vertices_hg H L isolated inputs outputs :
    referenced_vertices_hg (decompose_C1 H L inputs) ∪
      referenced_vertices_hg (decompose_L1 H L) ∪
      referenced_vertices_hg (decompose_C2 H L (decompose_C1 H L inputs) isolated outputs) =
    referenced_vertices_hg H.
  Proof.
    pose proof (decompose_L1_C1_disjoint H L inputs).
    pose proof (decompose_L1_C2_disjoint H L (decompose_C1 H L inputs) isolated outputs).
    pose proof (decompose_C1_C2_disjoint_gen H L (decompose_C1 H L inputs) isolated outputs).

    rewrite <- referenced_vertices_hg_union by done.
    rewrite <- referenced_vertices_hg_union by now apply map_disjoint_union_l.
    unfold referenced_vertices_hg.
    now rewrite decompose_C1_L1_C2_total.
  Qed.

  Lemma hypervertices_decomp_isolated_referenced {n m} (H : CospanHyperGraph T n m) :
    hypervertices H = isolated_vertices H ∪ (hypervertices H ∩ referenced_vertices H).
  Proof.
    unfold isolated_vertices.
    now rewrite difference_union_intersection_L.
  Qed.

  Lemma hypervertices_decompose {n m} (H : CospanHyperGraph T n m) (L : list positive) :
  hypervertices (decompose H L) = hypervertices H.
  Proof.
    cbv delta [decompose] beta.
    remember (list_to_set (inputs H)) as ins.
    remember (list_to_set (outputs H)) as outs.
    remember (isolated_vertices H) as isolated.
    remember (decompose_L1 H L) as L1.
    cbv zeta.
    remember (decompose_C1 H L _) as C1.
    remember (decompose_C2 H L C1 isolated _) as C2.
    remember (decompose_iset H L ins) as i.
    remember (decompose_jset H L C1 isolated outs) as j.
    remember (decompose_kset H L C1 isolated ins outs) as k.
    simpl.
    rewrite hg_empty_union.
    rewrite (union_empty_l_L (hypervertices L1)).
    rewrite vertices_hg_add_vertices.
    rewrite 2 list_to_vec_app.
    rewrite 3 list_to_set_list_to_vec.
    rewrite 3 list_to_set_elements_L.
    rewrite vertices_hg_union by now subst; apply decompose_L1_C2_disjoint.
    remember (vertices_hg C1) as C1v.
    remember (vertices_hg C2) as C2v.
    remember (vertices_hg L1) as Lv.
    replace (hypervertices C1) with (hypervertices H ∩ (referenced_vertices_hg C1 ∪ ins)) by (subst; set_solver +).
    replace (hypervertices L1) with (hypervertices H ∩ referenced_vertices_hg L1) by (subst; reflexivity).
    replace (hypervertices C2) with (isolated_vertices H ∪ hypervertices H ∩ (referenced_vertices_hg C2 ∪ outs)) by (subst; set_solver +).
    apply leibniz_equiv_iff.
    rewrite vec_to_list_app, 3 list_to_set_app_L, 2 vec_to_list_to_vec, 2 list_to_set_elements_L.
    apply set_subseteq_antisymm.
    - set_solver.
    - rewrite (union_difference
        ((hypervertices H) ∩ (referenced_vertices_hg C1 ∪ referenced_vertices_hg L1
        ∪ referenced_vertices_hg C2)) (hypervertices H)) at 1 by apply intersection_subseteq_l.
      rewrite union_subseteq.
      split. 1:{
        rewrite <- (union_subseteq_r ((k ∪ i) ∖ _)).
        set_solver +.
      }
      transitivity (isolated_vertices H ∪
        hypervertices H ∩ list_to_set (inputs H) ∪
        hypervertices H ∩ list_to_set (outputs H)). 1:{
        subst.
        rewrite decompose_C1_L1_C2_total_refererenced_vertices_hg.
        transitivity (hypervertices H ∖ referenced_vertices_hg H); [set_solver|].
        rewrite hypervertices_decomp_isolated_referenced at 1.
        set_solver +.
      }
      rewrite 2 union_subseteq; split_and!.
      + do 4 apply union_subseteq_r'.
        apply union_subseteq_l.
      + apply union_subseteq_r'.
        apply union_subseteq_l'.
        set_solver +Heqins.
      + do 5 apply union_subseteq_r'.
        set_solver +Heqouts.
  Qed.

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
    - symmetry. apply hypervertices_decompose.
  Qed.


  Definition DoublePushout_unsafe {n m} (H : CospanHyperGraph T n m) (G : HyperGraph T)
    (L : list positive) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs_unsafe' (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs_unsafe' (
      stack_graphs_aux (k -> ∅ <- k) (i -> G <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).


  Definition DoublePushout {n m} (H : CospanHyperGraph T n m) (G : HyperGraph T)
    (L : list positive) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs (
      stack_graphs (k -> ∅ <- k) (i -> G <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).

  Lemma decompose_is_DoublePushout_unsafe {n m} (H : CospanHyperGraph T n m) L :
    decompose H L = DoublePushout_unsafe H (decompose_L1 H L) L.
  Proof.
    done.
  Qed.

  (* Definition DoublePushout {n m} (H : CospanHyperGraph T n m) (G : HyperGraph T) (L : list positive) : CospanHyperGraph T n m :=
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
  )). *)



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




  Lemma vertices_compose_graphs_unsafe' {T n m o} (cohg : CospanHyperGraph T n m)
    (cohg' : CospanHyperGraph T m o) :
    outputs cohg = inputs cohg' ->
    hyperedges cohg ##ₘ hyperedges cohg' ->
    vertices (compose_graphs_unsafe' cohg cohg') =
    vertices cohg ∪ vertices cohg'.
  Proof.
    intros Hoi Hdisj.
    rewrite <- vertices_norm_verts.
    rewrite compose_graphs_unsafe'_correct, vertices_norm_verts.
    now apply vertices_compose_graphs_unsafe.
  Qed.

  Lemma decompose_vertices_C1_ins_C2_outs_subseteq {T} (H : HyperGraph T) L isolated ins outs :
    isolated ## referenced_vertices_hg H ∪ ins ∪ outs ->
    (vertices_hg (decompose_C1 H L ins) ∪ ins) ∩
    (vertices_hg (decompose_C2 H L (decompose_C1 H L ins) isolated outs) ∪ outs) ⊆
    decompose_kset H L (decompose_C1 H L ins) isolated ins outs ∪
    decompose_iset H L ins.
  Proof.
    intros Hisol.
    unfold decompose_kset.
    unfold decompose_iset.
    unfold decompose_C1v, decompose_C2v.
    replace (vertices_hg _ ∪ outs) with
      (referenced_vertices_hg (decompose_C2 H L (decompose_C1 H L ins) isolated outs) ∪
        outs ∪ isolated). 2:{
      rewrite <- union_assoc_L, (union_comm_L outs), union_assoc_L.
      apply leibniz_equiv_iff, set_subseteq_antisymm.
      - apply union_least, union_subseteq_r.
        rewrite vertices_hg_decomp.
        cbn.
        apply union_least, union_subseteq_l', union_subseteq_r', union_subseteq_l', union_subseteq_r.
        apply union_subseteq_l', union_subseteq_l.
      - apply union_least, union_subseteq_r.
        rewrite vertices_hg_decomp.
        apply union_least; [apply union_subseteq_l', union_subseteq_l|].
        cbn.
        rewrite (union_comm_L (_ ∪ isolated)), (union_assoc_L _).
        apply union_least, union_subseteq_l', union_subseteq_r.

        rewrite <- intersection_union_l_L.
        rewrite intersection_subseteq_r.
        apply union_least, union_subseteq_r.
        apply union_subseteq_l', union_subseteq_l.
    }
    rewrite intersection_union_l_L.
    rewrite (disjoint_intersection_L _ isolated).1. 2:{
      fold (decompose_C1v H L ins).
      pose proof (decompose_C1v_referenced H L ins).
      set_solver.
    }
    rewrite (union_empty_r_L _).
    replace (vertices_hg _ ∪ ins) with (referenced_vertices_hg (decompose_C1 H L ins) ∪ ins). 2:{
      apply leibniz_equiv_iff, set_subseteq_antisymm.
      - apply union_least, union_subseteq_r.
        rewrite vertices_hg_decomp.
        apply union_subseteq_l', union_subseteq_l.
      - apply union_least, union_subseteq_r.
        rewrite vertices_hg_decomp.
        apply union_least; [apply union_subseteq_l|].
        cbn.
        rewrite <- intersection_union_l_L.
        rewrite (union_comm_L ins).
        now rewrite intersection_subseteq_r.
    }
    rewrite intersection_union_l_L at 1.
    rewrite 2 (intersection_union_r_L _ ins) at 1.
    rewrite 3 union_subseteq.
    split_and!;
    intros k Hk;
    destruct_decide (decide (k ∈ decompose_L1v H L)) as Hk'; set_solver -Hisol.
  Qed.


  Lemma decompose_vertices_C1_C2_subseteq {T} (H : HyperGraph T) L isolated ins outs :
    isolated ## referenced_vertices_hg H ∪ ins ∪ outs ->
    vertices_hg (decompose_C1 H L ins) ∩
    vertices_hg (decompose_C2 H L (decompose_C1 H L ins) isolated outs) ⊆
    decompose_kset H L (decompose_C1 H L ins) isolated ins outs ∪
    decompose_iset H L ins.
  Proof.
    intros ?%(decompose_vertices_C1_ins_C2_outs_subseteq H L isolated ins outs).
    set_solver.
  Qed.

  Lemma decompose_vertices_C1_outs_subseteq {T} (H : HyperGraph T) L isolated ins outs :
    isolated ## referenced_vertices_hg H ∪ ins ∪ outs ->
    vertices_hg (decompose_C1 H L ins) ∩ outs ⊆
    decompose_kset H L (decompose_C1 H L ins) isolated ins outs ∪
    decompose_iset H L ins.
  Proof.
    intros ?%(decompose_vertices_C1_ins_C2_outs_subseteq H L isolated ins outs).
    set_solver.
  Qed.


  Lemma decompose_vertices_ins_C2_subseteq {T} (H : HyperGraph T) L isolated ins outs :
    isolated ## referenced_vertices_hg H ∪ ins ∪ outs ->
    ins ∩ vertices_hg (decompose_C2 H L (decompose_C1 H L ins) isolated outs) ⊆
    decompose_kset H L (decompose_C1 H L ins) isolated ins outs ∪
    decompose_iset H L ins.
  Proof.
    intros ?%(decompose_vertices_C1_ins_C2_outs_subseteq H L isolated ins outs).
    set_solver.
  Qed.

  Lemma decompose_vertices_ins_outs_subseteq {T} (H : HyperGraph T) L isolated ins outs :
    isolated ## referenced_vertices_hg H ∪ ins ∪ outs ->
    ins ∩ outs ⊆
    decompose_kset H L (decompose_C1 H L ins) isolated ins outs ∪
    decompose_iset H L ins.
  Proof.
    intros ?%(decompose_vertices_C1_ins_C2_outs_subseteq H L isolated ins outs).
    set_solver.
  Qed.

  Lemma decompose_iset_vertices {T n m} (H : CospanHyperGraph T n m) L :
    decompose_iset H L (list_to_set H.(inputs)) ⊆ vertices H.
  Proof.
    unfold decompose_iset.
    cbn.
    rewrite intersection_union_l_L.
    apply union_least; [|set_solver].
    transitivity (referenced_vertices_hg H); [|rewrite vertices_vertices_hg_decomp, vertices_hg_decomp; set_solver].
    rewrite intersection_subseteq_l.
    apply decompose_L1v_referenced.
  Qed.

  Lemma decompose_jset_vertices {T n m} (H : CospanHyperGraph T n m) L :
    decompose_jset H L (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(outputs)) ⊆ vertices H.
  Proof.
    unfold decompose_jset.
    cbn.
    rewrite intersection_union_l_L.
    apply union_least; [|set_solver].
    rewrite intersection_subseteq_l.
    rewrite decompose_L1v_referenced.
    rewrite vertices_vertices_hg_decomp, vertices_hg_decomp.
    set_solver.
  Qed.

  Lemma decompose_kset_vertices {T n m} (H : CospanHyperGraph T n m) L :
    decompose_kset H L (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(inputs)) (list_to_set H.(outputs)) ⊆ vertices H.
  Proof.
    unfold decompose_kset.
    apply subseteq_difference_l.
    rewrite intersection_subseteq_l.
    apply union_least; [|set_solver].
    rewrite decompose_C1v_referenced.
    rewrite vertices_vertices_hg_decomp, vertices_hg_decomp.
    set_solver.
  Qed.




  Lemma DoublePushout_unsafe_to_safe {T n m} (H : CospanHyperGraph T n m) G L :
    vertices_hg G ∖ vertices_hg (decompose_L1 H L) ## vertices H ->
    hyperedges G ∖ hyperedges (decompose_L1 H L) ##ₘ hyperedges H ->
    DoublePushout_unsafe H G L ≡ᵢ DoublePushout H G L.
  Proof.
    intros Hdisj Hmdisj.
    cbv delta [DoublePushout DoublePushout_unsafe] beta.

    remember (list_to_set (inputs H)) as ins.
    remember (list_to_set (outputs H)) as outs.
    remember (isolated_vertices H) as isolated.
    remember (decompose_L1 H L) as L1.
    cbv zeta.
    remember (decompose_C1 H L _) as C1.
    remember (decompose_C2 H L C1 isolated _) as C2.
    remember (decompose_iset H L ins) as i.
    remember (decompose_jset H L C1 isolated outs) as j.
    remember (decompose_kset H L C1 isolated ins outs) as k.
    assert (Hi : i ⊆ vertices H) by now subst; apply decompose_iset_vertices.
    assert (Hj : j ⊆ vertices H) by now subst; apply decompose_jset_vertices.
    assert (Hk : k ⊆ vertices H) by now subst; apply decompose_kset_vertices.
    assert (HC1v : vertices_hg C1 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H);
      etransitivity; [subst; apply decompose_C1v_referenced|];
      set_solver +).
    assert (HL1v : vertices_hg L1 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H);
      etransitivity; [subst; apply decompose_L1v_referenced|];
      set_solver +).
    assert (HC2v : vertices_hg C2 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H) in HC1v |- *;
      etransitivity; [subst; apply decompose_C2v_referenced|];
      set_solver + HC1v).
    assert (HL1dom : dom (hyperedges L1) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_L1_subseteq.
    assert (HC1dom : dom (hyperedges C1) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_C1_subseteq.
    assert (HC2dom : dom (hyperedges C2) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_C2_subseteq.
    assert (HGC1 : hyperedges G ##ₘ hyperedges C1). 1:{
      revert Hmdisj.
      rewrite 2 map_disjoint_dom, dom_difference_L.
      rewrite disjoint_difference_l.
      intros Hmdisj.
      intros x HxG HxC2.
      apply ((map_disjoint_dom _ _).1 (decompose_L1_C1_disjoint H L ins) x).
      + replace -> L1 in Hmdisj.
        apply Hmdisj.
        now apply elem_of_intersection, conj, HC1dom.
      + subst; apply HxC2.
    }
    assert (HGC2 : hyperedges G ##ₘ hyperedges C2). 1:{
      revert Hmdisj.
      rewrite 2 map_disjoint_dom, dom_difference_L.
      rewrite disjoint_difference_l.
      intros Hmdisj.
      intros x HxG HxC2.
      apply ((map_disjoint_dom _ _).1 (decompose_L1_C2_disjoint H L C1 isolated outs) x).
      + replace -> L1 in Hmdisj.
        apply Hmdisj.
        now apply elem_of_intersection, conj, HC2dom.
      + subst; apply HxC2.
    }

    simpl.
    rewrite 2 compose_graphs_unsafe'_to_compose_graphs,
      (fun H1 H2 => subrel (R2:=struct_isomorphic)
      (stack_graphs_aux_to_stack_graphs_disjoint _ _ H1 H2)).
    - done.
    - cbn.
      solve_map_disjoint.
    - rewrite 2 vertices_vertices_hg_decomp.
      cbn.
      rewrite vertices_hg_empty.
      rewrite 3 vec_to_list_to_vec.
      rewrite 2 list_to_set_app_L, (union_idemp_L _).
      rewrite 3 list_to_set_elements_L.
      rewrite (union_empty_l_L _).
      rewrite disjoint_union_r.
      split; [|subst; set_solver +].
      subst; set_solver +Hk Hdisj.
    - done.
    - cbn.
      rewrite vertices_stack_graphs_aux by now cbn; solve_map_disjoint.
      rewrite 3 vertices_vertices_hg_decomp.
      cbn.
      rewrite vertices_hg_empty.
      apply difference_disjoint_same_r.
      rewrite vec_to_list_app, 3 vec_to_list_to_vec.
      rewrite ! list_to_set_app_L, (union_idemp_L _).
      rewrite 3 list_to_set_elements_L.
      rewrite (union_empty_l_L k).
      rewrite intersection_union_r_L.
      apply union_least; [apply union_subseteq_l', intersection_subseteq_l|].
      rewrite (union_comm_L (k ∪ j)).
      rewrite union_assoc_L.
      rewrite intersection_union_r_L.
      apply union_least, union_subseteq_r', intersection_subseteq_l.
      rewrite union_assoc_L.
      rewrite intersection_union_l_L.
      apply union_least, intersection_subseteq_r.
      rewrite intersection_union_r_L.
      apply union_least; [|subst; set_solver +].
      transitivity (vertices_hg L1 ∩ (vertices_hg C2 ∪ list_to_set H.(outputs))); [|subst; set_solver +].
      apply intersection_greatest, intersection_subseteq_r.
      rewrite disjoint_difference_l in Hdisj.
      rewrite <- Hdisj.
      apply intersection_mono_l.
      apply union_least; [done|].
      set_solver +.
    - cbn.
      rewrite map_empty_union.
      done.
    - done.
    - cbn.
      apply difference_disjoint_same_r.
      rewrite vertices_compose_graphs_unsafe' by first [reflexivity|
        cbn; rewrite map_empty_union; done].
      rewrite vertices_stack_graphs_aux by now cbn; solve_map_disjoint.

      rewrite 4 vertices_vertices_hg_decomp.
      cbn.
      rewrite (@vertices_hg_empty T).
      rewrite 2 vec_to_list_app, 3 vec_to_list_to_vec.
      rewrite ! list_to_set_app_L, (union_idemp_L _).
      rewrite 3 list_to_set_elements_L.
      rewrite union_assoc_L.
      rewrite intersection_union_r_L.
      apply union_least, intersection_subseteq_l.
      rewrite (union_empty_l_L _).
      transitivity ((vertices_hg C1 ∪ list_to_set (inputs H)) ∩
        ((j ∪ (vertices_hg C2 ∪ vertices_hg G ∪ list_to_set (outputs H))) ∪ (k ∪ i)));
      [apply eq_reflexivity; set_solver +|].
      rewrite intersection_union_l_L.
      apply union_least, intersection_subseteq_r.
      rewrite intersection_union_r_L.
      assert (Hdisj' : isolated_vertices H ## referenced_vertices_hg H ∪
        list_to_set (inputs H) ∪ list_to_set (outputs H)) by set_solver +.
      apply union_least.
      + rewrite ! (intersection_union_l_L (vertices_hg C1)).
        rewrite 3 union_subseteq.
        split_and!.
        * subst; set_solver +.
        * now subst; apply decompose_vertices_C1_C2_subseteq.
        * pose proof (decompose_L1v_C1v_subseteq H L ins) as Hsubs.
          rewrite <- Heqi in Hsubs.
          apply union_subseteq_r'.
          rewrite <- Hsubs.
          apply intersection_greatest; [|subst; apply intersection_subseteq_l].
          unfold decompose_L1v.
          rewrite <- HeqL1.
          rewrite disjoint_difference_l in Hdisj.
          rewrite <- Hdisj.
          rewrite (intersection_comm_L _).
          apply intersection_mono_l.
          apply HC1v.
        * now subst; apply decompose_vertices_C1_outs_subseteq.
      + rewrite ! (intersection_union_l_L (list_to_set (inputs H))).
        rewrite 3 union_subseteq.
        split_and!.
        * subst; set_solver +.
        * now subst; apply decompose_vertices_ins_C2_subseteq.
        * rewrite disjoint_difference_l in Hdisj.
          subst; set_solver +Hdisj.
        * now subst; apply decompose_vertices_ins_outs_subseteq.
    - cbn.
      rewrite map_empty_union.
      apply map_disjoint_union_r.
      split.
      + done.
      + subst; apply decompose_C1_C2_disjoint_gen.
  Qed.



  Lemma DPO_equiv_aux {T n m} (H : CospanHyperGraph T n m) L :
    H ≡ᵢ DoublePushout H (decompose_L1 H L) L.
  Proof.
    rewrite (decompose_is_graph H L) at 1.
    rewrite decompose_is_DoublePushout_unsafe.
    apply DoublePushout_unsafe_to_safe.
    - set_solver.
    - rewrite map_difference_diag.
      solve_map_disjoint.
  Qed.


  Lemma DPO_equiv {n m} `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (Target : CospanHyperGraph T n m)
    (G : HyperGraph T) (L : list positive) :
      (forall {o p} (v0 : vec positive o) (v1 : vec positive p),
        (v0 -> G <- v1) ≡ₜ (v0 -> (subgraph_index Target L) <- v1))
        -> Target ≡ₜ (DoublePushout Target G L).
  Proof.
    intros Heq.
    rewrite (DPO_equiv_aux Target L) at 1.
    unfold DoublePushout.
    f_equiv.
    f_equiv.
    f_equiv.
    symmetry.
    rewrite Heq.
    apply (subrel' cohg_vert_eq).
    apply cohg_vert_eq_alt_vertices.
    split_and!; [done..|].
    rewrite 2 vertices_vertices_hg_decomp.
    cbn.
    rewrite 2 vertices_hg_decomp.
    cbn.
    f_equal.
    rewrite union_empty_r_L.
    apply leibniz_equiv_iff, set_subseteq_antisymm.
    - apply union_subseteq_l.
    - apply union_least, intersection_subseteq_r.
      done.
  Qed.

  Definition decompose_ilist {T n m} (H : CospanHyperGraph T n m) L : list positive :=
    elements (decompose_iset H L (list_to_set H.(inputs))).

  Definition decompose_jlist {T n m} (H : CospanHyperGraph T n m) L : list positive :=
    elements (decompose_jset H L (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(outputs))).

  Lemma DPO_equiv_unsafe {n m} `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (Target : CospanHyperGraph T n m)
    (G : HyperGraph T) (L : list positive) :
    vertices_hg G ∖ vertices_hg (decompose_L1 Target L) ## vertices Target ->
    hyperedges G ∖ hyperedges (decompose_L1 Target L) ##ₘ hyperedges Target ->
      ((list_to_vec (decompose_ilist Target L) -> G <- list_to_vec (decompose_jlist Target L)) ≡ₜ
        (list_to_vec (decompose_ilist Target L) ->
          decompose_L1 Target L <- list_to_vec (decompose_jlist Target L)))
        -> Target ≡ₜ (DoublePushout_unsafe Target G L).
  Proof.
    intros Hdisj Hmdisj Heq.
    rewrite (DPO_equiv_aux Target L) at 1.
    rewrite DoublePushout_unsafe_to_safe by done.
    unfold DoublePushout.
    f_equiv.
    f_equiv.
    f_equiv.
    symmetry.
    apply Heq.
  Qed.

  Definition DoublePushout_with_unsafe {T n m} (H : CospanHyperGraph T n m) (G : HyperGraph T)
    (L : list positive) {ni nj} (i : vec _ ni) (j : vec _ nj) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    (* let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in *)
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs_unsafe' (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs_unsafe' (
      stack_graphs_aux (k -> ∅ <- k) (i -> G <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).

  Definition DoublePushout_with {T n m} (H : CospanHyperGraph T n m) (G : HyperGraph T)
    (L : list positive) {ni nj} (i : vec _ ni) (j : vec _ nj) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    (* let i := list_to_vec(elements(decompose_iset H L ins)) in
    let j := list_to_vec(elements(decompose_jset H L C1 isolated outs)) in *)
    let k := list_to_vec(elements(decompose_kset H L C1 isolated ins outs)) in
    compose_graphs (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs (
      stack_graphs (k -> ∅ <- k) (i -> G <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).


  Lemma DoublePushout_with_unsafe_to_safe {T n m} (H : CospanHyperGraph T n m) G L
    {ni nj} (i : vec _ ni) (j : vec _ nj) :
    vertices_hg G ∖ vertices_hg (decompose_L1 H L) ## vertices H ->
    hyperedges G ∖ hyperedges (decompose_L1 H L) ##ₘ hyperedges H ->
    list_to_set i = decompose_iset H L (list_to_set H.(inputs)) ->
    list_to_set j = decompose_jset H L
      (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(outputs)) ->
    DoublePushout_with_unsafe H G L i j ≡ᵢ DoublePushout_with H G L i j.
  Proof.
    intros Hdisj Hmdisj Hi' Hj'.
    cbv delta [DoublePushout_with DoublePushout_with_unsafe] beta.

    rename i into i'.
    rename j into j'.

    remember (list_to_set (inputs H)) as ins.
    remember (list_to_set (outputs H)) as outs.
    remember (isolated_vertices H) as isolated.
    remember (decompose_L1 H L) as L1.
    cbv zeta.
    remember (decompose_C1 H L _) as C1.
    remember (decompose_C2 H L C1 isolated _) as C2.
    remember (decompose_iset H L ins) as i.
    remember (decompose_jset H L C1 isolated outs) as j.
    remember (decompose_kset H L C1 isolated ins outs) as k.
    assert (Hi : i ⊆ vertices H) by now subst; apply decompose_iset_vertices.
    assert (Hj : j ⊆ vertices H) by now subst; apply decompose_jset_vertices.
    assert (Hk : k ⊆ vertices H) by now subst; apply decompose_kset_vertices.
    assert (HC1v : vertices_hg C1 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H);
      etransitivity; [subst; apply decompose_C1v_referenced|];
      set_solver +).
    assert (HL1v : vertices_hg L1 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H);
      etransitivity; [subst; apply decompose_L1v_referenced|];
      set_solver +).
    assert (HC2v : vertices_hg C2 ⊆ vertices H) by (
      rewrite vertices_vertices_hg_decomp, (vertices_hg_decomp H) in HC1v |- *;
      etransitivity; [subst; apply decompose_C2v_referenced|];
      set_solver + HC1v).
    assert (HL1dom : dom (hyperedges L1) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_L1_subseteq.
    assert (HC1dom : dom (hyperedges C1) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_C1_subseteq.
    assert (HC2dom : dom (hyperedges C2) ⊆ dom (hyperedges H)) by
      now subst; apply subseteq_dom, decompose_C2_subseteq.
    assert (HGC1 : hyperedges G ##ₘ hyperedges C1). 1:{
      revert Hmdisj.
      rewrite 2 map_disjoint_dom, dom_difference_L.
      rewrite disjoint_difference_l.
      intros Hmdisj.
      intros x HxG HxC2.
      apply ((map_disjoint_dom _ _).1 (decompose_L1_C1_disjoint H L ins) x).
      + replace -> L1 in Hmdisj.
        apply Hmdisj.
        now apply elem_of_intersection, conj, HC1dom.
      + subst; apply HxC2.
    }
    assert (HGC2 : hyperedges G ##ₘ hyperedges C2). 1:{
      revert Hmdisj.
      rewrite 2 map_disjoint_dom, dom_difference_L.
      rewrite disjoint_difference_l.
      intros Hmdisj.
      intros x HxG HxC2.
      apply ((map_disjoint_dom _ _).1 (decompose_L1_C2_disjoint H L C1 isolated outs) x).
      + replace -> L1 in Hmdisj.
        apply Hmdisj.
        now apply elem_of_intersection, conj, HC2dom.
      + subst; apply HxC2.
    }

    rewrite 2 compose_graphs_unsafe'_to_compose_graphs,
      (fun H1 H2 => subrel (R2:=struct_isomorphic)
        (stack_graphs_aux_to_stack_graphs_disjoint _ _ H1 H2)).
    - done.
    - cbn.
      solve_map_disjoint.
    - rewrite 2 vertices_vertices_hg_decomp.
      cbn.
      rewrite vertices_hg_empty.
      rewrite vec_to_list_to_vec.
      rewrite 2 list_to_set_app_L, (union_idemp_L _).
      rewrite Hi', Hj'.
      rewrite list_to_set_elements_L.
      rewrite (union_empty_l_L _).
      rewrite disjoint_union_r.
      split; [|subst; set_solver +].
      subst; set_solver +Hk Hdisj.
    - done.
    - cbn.
      rewrite vertices_stack_graphs_aux by now cbn; solve_map_disjoint.
      rewrite 3 vertices_vertices_hg_decomp.
      cbn.
      rewrite vertices_hg_empty.
      apply difference_disjoint_same_r.
      rewrite vec_to_list_app, vec_to_list_to_vec.
      rewrite ! list_to_set_app_L, (union_idemp_L _).
      rewrite Hi', Hj'.
      rewrite list_to_set_elements_L.
      rewrite (union_empty_l_L k).
      rewrite intersection_union_r_L.
      apply union_least; [apply union_subseteq_l', intersection_subseteq_l|].
      rewrite (union_comm_L (k ∪ j)).
      rewrite union_assoc_L.
      rewrite intersection_union_r_L.
      apply union_least, union_subseteq_r', intersection_subseteq_l.
      rewrite union_assoc_L.
      rewrite intersection_union_l_L.
      apply union_least, intersection_subseteq_r.
      rewrite intersection_union_r_L.
      apply union_least; [|subst; set_solver +].
      transitivity (vertices_hg L1 ∩ (vertices_hg C2 ∪ list_to_set H.(outputs))); [|subst; set_solver +].
      apply intersection_greatest, intersection_subseteq_r.
      rewrite disjoint_difference_l in Hdisj.
      rewrite <- Hdisj.
      apply intersection_mono_l.
      apply union_least; [done|].
      set_solver +.
    - cbn.
      rewrite map_empty_union.
      done.
    - done.
    - cbn.
      apply difference_disjoint_same_r.
      rewrite vertices_compose_graphs_unsafe' by first [reflexivity|
        cbn; rewrite map_empty_union; done].
      rewrite vertices_stack_graphs_aux by now cbn; solve_map_disjoint.

      rewrite 4 vertices_vertices_hg_decomp.
      cbn.
      rewrite (@vertices_hg_empty T).
      rewrite 2 vec_to_list_app, vec_to_list_to_vec.
      rewrite ! list_to_set_app_L, (union_idemp_L _).
      rewrite Hi', Hj'.
      rewrite list_to_set_elements_L.
      rewrite union_assoc_L.
      rewrite intersection_union_r_L.
      apply union_least, intersection_subseteq_l.
      rewrite (union_empty_l_L _).
      transitivity ((vertices_hg C1 ∪ list_to_set (inputs H)) ∩
        ((j ∪ (vertices_hg C2 ∪ vertices_hg G ∪ list_to_set (outputs H))) ∪ (k ∪ i)));
      [apply eq_reflexivity; set_solver +|].
      rewrite intersection_union_l_L.
      apply union_least, intersection_subseteq_r.
      rewrite intersection_union_r_L.
      assert (Hdisj' : isolated_vertices H ## referenced_vertices_hg H ∪
        list_to_set (inputs H) ∪ list_to_set (outputs H)) by set_solver +.
      apply union_least.
      + rewrite ! (intersection_union_l_L (vertices_hg C1)).
        rewrite 3 union_subseteq.
        split_and!.
        * subst; set_solver +.
        * now subst; apply decompose_vertices_C1_C2_subseteq.
        * pose proof (decompose_L1v_C1v_subseteq H L ins) as Hsubs.
          rewrite <- Heqi in Hsubs.
          apply union_subseteq_r'.
          rewrite <- Hsubs.
          apply intersection_greatest; [|subst; apply intersection_subseteq_l].
          unfold decompose_L1v.
          rewrite <- HeqL1.
          rewrite disjoint_difference_l in Hdisj.
          rewrite <- Hdisj.
          rewrite (intersection_comm_L _).
          apply intersection_mono_l.
          apply HC1v.
        * now subst; apply decompose_vertices_C1_outs_subseteq.
      + rewrite ! (intersection_union_l_L (list_to_set (inputs H))).
        rewrite 3 union_subseteq.
        split_and!.
        * subst; set_solver +.
        * now subst; apply decompose_vertices_ins_C2_subseteq.
        * rewrite disjoint_difference_l in Hdisj.
          subst; set_solver +Hdisj.
        * now subst; apply decompose_vertices_ins_outs_subseteq.
    - cbn.
      rewrite map_empty_union.
      apply map_disjoint_union_r.
      split.
      + done.
      + subst; apply decompose_C1_C2_disjoint_gen.
  Qed.

  Lemma compose_graphs_unsafe'_boundary_indep {T n m m' o}
    (H G : HyperGraph T) (i : vec _ n) (jH j : vec _ m) (jH' j' : vec _ m') (k : vec _ o) :
    list_to_set j =@{Pset} list_to_set j' ->
    compose_graphs_unsafe' (i -> H <- jH) (j -> G <- k) =
    compose_graphs_unsafe' (i -> H <- jH') (j' -> G <- k).
  Proof.
    intros Hj.
    apply cohg_ext'; [done..|].
    cbn.
    now rewrite Hj.
  Qed.

  Lemma compose_graphs_unsafe'_boundary_indep' {T n m m' o}
    (H : CospanHyperGraph T n m) (G : CospanHyperGraph T m o)
    (H' : CospanHyperGraph T n m') (G' : CospanHyperGraph T m' o) :
    hedges H = hedges H' -> inputs H = inputs H' ->
    hedges G = hedges G' -> outputs G = outputs G' ->
    list_to_set G.(inputs) =@{Pset} list_to_set G'.(inputs) ->
    compose_graphs_unsafe' H G = compose_graphs_unsafe' H' G'.
  Proof.
    destruct H, G, H', G'.
    cbn.
    intros; subst.
    now apply compose_graphs_unsafe'_boundary_indep.
  Qed.

  Lemma compose_graphs_unsafe'_boundary_indep'' {T n m o n' m' o'}
    (H : CospanHyperGraph T n m) (G : CospanHyperGraph T m o)
    (H' : CospanHyperGraph T n' m') (G' : CospanHyperGraph T m' o') :
    hedges H = hedges H' -> list_to_set $ inputs H =@{Pset} list_to_set $ inputs H' ->
    hedges G = hedges G' -> list_to_set $ outputs G =@{Pset} list_to_set $ outputs G' ->
    list_to_set G.(inputs) =@{Pset} list_to_set G'.(inputs) ->
    hedges $ compose_graphs_unsafe' H G = hedges $ compose_graphs_unsafe' H' G'.
  Proof.
    destruct H, G, H', G'.
    cbn.
    intros <-.
    rewrite 2 list_to_set_app_L.
    intros <- <- <- <-.
    done.
  Qed.

  Lemma DoublePushout_with_unsafe_to_unsafe {T n m} (H : CospanHyperGraph T n m) G L
    {ni nj} (i : vec _ ni) (j : vec _ nj) :
    vertices_hg G ∖ vertices_hg (decompose_L1 H L) ## vertices H ->
    hyperedges G ∖ hyperedges (decompose_L1 H L) ##ₘ hyperedges H ->
    list_to_set i = decompose_iset H L (list_to_set H.(inputs)) ->
    list_to_set j = decompose_jset H L
      (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(outputs)) ->
    DoublePushout_with_unsafe H G L i j = DoublePushout_unsafe H G L.
  Proof.
    intros Hdisj Hmdisj Hi' Hj'.
    unfold DoublePushout_with_unsafe, DoublePushout_unsafe.
    apply compose_graphs_unsafe'_boundary_indep'; [try reflexivity..|].
    - f_equal.
      apply compose_graphs_unsafe'_boundary_indep''; [try reflexivity..|].
      + cbn.
        rewrite 2 vec_to_list_app.
        rewrite 2 vec_to_list_to_vec.
        rewrite 2 list_to_set_app_L.
        f_equal.
        now rewrite list_to_set_elements_L.
      + cbn.
        rewrite 2 vec_to_list_app.
        rewrite 2 vec_to_list_to_vec.
        rewrite 2 list_to_set_app_L.
        f_equal.
        now rewrite list_to_set_elements_L.
    - cbn.
      rewrite 2 vec_to_list_app.
      rewrite 2 vec_to_list_to_vec.
      rewrite 2 list_to_set_app_L.
      f_equal.
      now rewrite list_to_set_elements_L.
  Qed.

  Lemma DPO_with_equiv {n m} `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (Target : CospanHyperGraph T n m) (G : HyperGraph T) (L : list positive)
    {ni nj} (i : vec _ ni) (j : vec _ nj) :
    list_to_set i =@{Pset} list_to_set $ decompose_ilist Target L ->
    list_to_set j =@{Pset} list_to_set $ decompose_jlist Target L ->
    (i -> decompose_L1 Target L <- j) ≡ₜ (i -> G <- j) ->
    Target ≡ₜ DoublePushout_with Target G L i j.
  Proof.
    intros Hi Hj Heq.
    rewrite (decompose_is_graph Target L) at 1.
    rewrite decompose_is_DoublePushout_unsafe.
    assert (Haux1 : vertices_hg (decompose_L1 Target L) ∖
      vertices_hg (decompose_L1 Target L) ## vertices Target) by set_solver +.
    assert (Haux2 : (hyperedges $ decompose_L1 Target L) ∖
      (hyperedges $ decompose_L1 Target L) ##ₘ hyperedges Target) by
      now rewrite map_difference_diag; solve_map_disjoint.
    assert (Haux3 : list_to_set i = decompose_iset Target L (list_to_set (inputs Target))) by set_solver + Hi.
    assert (Haux4 : list_to_set j = decompose_jset Target L (decompose_C1 Target L (list_to_set (inputs Target)))
  (isolated_vertices Target) (list_to_set (outputs Target))) by set_solver + Hj.
    rewrite <- (DoublePushout_with_unsafe_to_unsafe Target (decompose_L1 Target L) L i j) by done.
    rewrite DoublePushout_with_unsafe_to_safe by done.
    unfold DoublePushout_with.
    f_equiv.
    f_equiv.
    f_equiv.
    done.
  Qed.











(*

  Definition graph_wrap_r_under {T n m o} (cohg : CospanHyperGraph T n (m + o)) :
    CospanHyperGraph T (n + o) m :=
    cohg.(inputs) +++ vsplitr cohg.(outputs) -> cohg <- vsplitl cohg.(outputs).

  Definition graph_wrap_l_under {T n m o} (cohg : CospanHyperGraph T (n + m) o) :
    CospanHyperGraph T n (o + m) :=
    vsplitl cohg.(inputs) -> cohg <- cohg.(outputs) +++ vsplitr cohg.(inputs).

  Lemma graph_wrap_l_r_under {T n m o} (cohg : CospanHyperGraph T n (m + o)) :
    graph_wrap_l_under (graph_wrap_r_under cohg) = cohg.
  Proof.
    apply cohg_ext; [done|..].
    - cbn.
      now rewrite vsplitl_app.
    - cbn.
      rewrite vsplitr_app.
      apply app_vsplit.
  Qed.

  Lemma graph_wrap_r_l_under {T n m o} (cohg : CospanHyperGraph T (n + m) o) :
    graph_wrap_r_under (graph_wrap_l_under cohg) = cohg.
  Proof.
    apply cohg_ext; [done|..].
    - cbn.
      rewrite vsplitr_app.
      apply app_vsplit.
    - cbn.
      now rewrite vsplitl_app.
  Qed.

  Lemma graph_semantics_wrap_r_under {n m o}
    `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (cohg : CospanHyperGraph T n (m + o)) :
    graph_semantics

  Lemma graph_wrap_r_under_semantic_eq {n m o}
    `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (cohg cohg' : CospanHyperGraph T n (m + o)) :
    cohg ≡ₜ cohg' -> graph_wrap_r_under cohg ≡ₜ graph_wrap_r_under cohg'.
  Proof.

  Lemma hg_equiv_pull_around_aux {n m}
    `{TensT : TensorLike R rO rI radd rmul req A T, !WFSummable A}
    (hgl hgr : HyperGraph T) (v : vec _ n) (w : vec _ m) :
    (v -> hgl <- w) ≡ₜ (v -> hgr <- w) <->

  Proof. *)




(* Section interface_decompose.
  Context {T : Type}.

  Section interface_decompose_defs.

  Context (H : HyperGraph T) (L : list positive).
  (*
  Definition decompose_L1 : HyperGraph T :=
    mk_sub_hg H (subgraph_index_aux H L).

  Definition decompose_C1 inputs : HyperGraph T :=
    hg_add_vertices (mk_sub_hg H (all_paths_idx H L)) (hypervertices H ∩ inputs).

  Definition decompose_C2 (C1 : HyperGraph T) (isolated : Pset)
    outputs : HyperGraph T :=
    hg_add_vertices (mk_sub_hg H ((hyperedges H) ∖ (C1 ∪ subgraph_index H L)))
      (hypervertices H ∩ outputs ∪ isolated).

  Definition decompose_L1v : Pset :=
    vertices_hg decompose_L1.

  Definition decompose_C1v inputs : Pset :=
    vertices_hg (decompose_C1 inputs).

  Definition decompose_C2v C1 isolated outputs : Pset :=
    vertices_hg (decompose_C2 C1 isolated outputs).


  Definition decompose_iset (inputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C1v inputs ∪ inputs).

  Definition decompose_jset C1 isolated (outputs : Pset) : Pset :=
    decompose_L1v ∩ (decompose_C2v C1 isolated outputs ∪ outputs). *)

  Definition interface_decompose_kset
    C1 isolated (inputs outputs : Pset) lin lout : Pset :=
    ((decompose_C1v H L inputs ∪ inputs) ∩ (decompose_C2v H L C1 isolated outputs ∪ outputs) ∖
      (list_to_set lin ∪ list_to_set lout)).

  End interface_decompose_defs.

  Definition interface_decompose {n m} (H : CospanHyperGraph T n m)
    (L : list positive) (lin lout : list positive) : CospanHyperGraph T n m :=
    let ins := list_to_set H.(inputs) in
    let outs := list_to_set H.(outputs) in
    let isolated := isolated_vertices H in
    let L1 := decompose_L1 H L in
    let C1 := decompose_C1 H L ins in
    let C2 := decompose_C2 H L C1 isolated outs in

    let i := list_to_vec lin in
    let j := list_to_vec lout in
    let k := list_to_vec (elements (interface_decompose_kset H L C1 isolated ins outs lin lout)) in

    compose_graphs_unsafe' (H.(inputs) -> C1 <- (k +++ i)) (compose_graphs_unsafe' (
      stack_graphs_aux (k -> ∅ <- k) (i -> L1 <- j)) (
    k +++ j ->
      C2
    <- H.(outputs)
    )).





  Lemma hypervertices_interface_decompose {n m}
    (H : CospanHyperGraph T n m) (L : list positive) lin lout :
    vertices_hg (decompose_L1 H L) ∩ (vertices_hg (decompose_C1 H L (list_to_set H.(inputs))) ∪
      vertices_hg (decompose_C2 H L (decompose_C1 H L (list_to_set H.(inputs)))
      (isolated_vertices H) (list_to_set H.(outputs)))) ⊆ list_to_set lin ∪ list_to_set lout ->
    hypervertices (interface_decompose H L lin lout) = hypervertices H.
  Proof.
    cbv delta [interface_decompose] beta.
    remember (list_to_set (inputs H)) as ins.
    remember (list_to_set (outputs H)) as outs.
    remember (isolated_vertices H) as isolated.
    remember (decompose_L1 H L) as L1.
    cbv zeta.
    remember (decompose_C1 H L _) as C1.
    remember (decompose_C2 H L C1 isolated _) as C2.
    (* remember (decompose_iset H L ins) as i.
    remember (decompose_jset H L C1 isolated outs) as j. *)
    remember (interface_decompose_kset H L C1 isolated ins outs lin lout) as k.



    simpl.

    intros Hsubs.

    rewrite hg_empty_union.
    rewrite (union_empty_l_L (hypervertices L1)).
    rewrite vertices_hg_add_vertices.
    rewrite 2 vec_to_list_app, 4 list_to_set_app_L.
    rewrite vec_to_list_to_vec, list_to_set_elements_L.

    rewrite vertices_hg_union by now subst; apply decompose_L1_C2_disjoint.
    remember (vertices_hg C1) as C1v.
    remember (vertices_hg C2) as C2v.
    remember (vertices_hg L1) as Lv.
    replace (hypervertices C1) with (hypervertices H ∩ (referenced_vertices_hg C1 ∪ ins)) by (subst; set_solver +).
    replace (hypervertices L1) with (hypervertices H ∩ referenced_vertices_hg L1) by (subst; reflexivity).
    replace (hypervertices C2) with (isolated_vertices H ∪ hypervertices H ∩ (referenced_vertices_hg C2 ∪ outs)) by (subst; set_solver +).
    apply leibniz_equiv_iff.
    rewrite 2 list_to_set_list_to_vec.
    (* rewrite vec_to_list_app, 3 list_to_set_app_L, 2 vec_to_list_to_vec, 2 list_to_set_elements_L. *)
    apply set_subseteq_antisymm.
    - repeat apply union_least; try timeout 2 set_solver.
      +
        enough (list_to_set lin ⊆ vertices H).

        enough (list_to_set lout ⊆ vertices H) by set_solver.
    - rewrite (union_difference
        ((hypervertices H) ∩ (referenced_vertices_hg C1 ∪ referenced_vertices_hg L1
        ∪ referenced_vertices_hg C2)) (hypervertices H)) at 1 by apply intersection_subseteq_l.
      rewrite union_subseteq.
      split. 1:{
        rewrite <- (union_subseteq_r ((k ∪ i) ∖ _)).
        set_solver +.
      }
      transitivity (isolated_vertices H ∪
        hypervertices H ∩ list_to_set (inputs H) ∪
        hypervertices H ∩ list_to_set (outputs H)). 1:{
        subst.
        rewrite decompose_C1_L1_C2_total_refererenced_vertices_hg.
        transitivity (hypervertices H ∖ referenced_vertices_hg H); [set_solver|].
        rewrite hypervertices_decomp_isolated_referenced at 1.
        set_solver +.
      }
      rewrite 2 union_subseteq; split_and!.
      + do 4 apply union_subseteq_r'.
        apply union_subseteq_l.
      + apply union_subseteq_r'.
        apply union_subseteq_l'.
        set_solver +Heqins.
      + do 5 apply union_subseteq_r'.
        set_solver +Heqouts.
  Qed.

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
    - symmetry. apply hypervertices_decompose.
  Qed.

  End interface_decompose. *)



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



Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs T n m o)
  with signature cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq
  as compose_graphs_cohg_syntactic_eq.
Proof.
  intros cohg1 cohg1' Heq1
    cohg2 cohg2' Heq2.
  induction Heq1 as [cohg1 cohg1' fv1 fe1 Hfv1 Hfe1 Heq1].
  induction Heq2 as [cohg2 cohg2' fv2 fe2 Hfv2 Hfe2 Heq2].
  etransitivity; [|etransitivity].
  - apply (subrel' struct_isomorphic).
    apply compose_graphs_struct_isomorphic_Proper; symmetry; apply (subrel (norm_verts_vert_eq _)).
  - apply (subrel' cohg_eq).
    apply compose_graphs_cohg_eq_Proper; [apply Heq1|apply Heq2].
  - apply (subrel' struct_isomorphic).
    apply compose_graphs_struct_isomorphic_Proper; rewrite (norm_verts_vert_eq _); 
    apply (subrel' isomorphic); constructor; done.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m n' m'} : (@stack_graphs T n m n' m')
  with signature cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq
  as stack_graphs_cohg_syntactic_eq.
Proof.
  intros cohg1 cohg1' Heq1
    cohg2 cohg2' Heq2.
  induction Heq1 as [cohg1 cohg1' fv1 fe1 Hfv1 Hfe1 Heq1].
  induction Heq2 as [cohg2 cohg2' fv2 fe2 Hfv2 Hfe2 Heq2].
  etransitivity; [|etransitivity].
  - apply (subrel' struct_isomorphic).
    apply stack_graphs_struct_isomorphic_Proper; symmetry; apply (subrel (norm_verts_vert_eq _)).
  - apply (subrel' cohg_eq).
    apply stack_graphs_cohg_eq_Proper; [apply Heq1|apply Heq2].
  - apply (subrel' struct_isomorphic).
    apply stack_graphs_struct_isomorphic_Proper; rewrite (norm_verts_vert_eq _); 
    apply (subrel' isomorphic); constructor; done.
Qed.


