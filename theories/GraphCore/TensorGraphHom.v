Require Export TensorGraph GraphRewriting TensorGraphExpr
  TensorGraphSemantics.







Definition hypergraph_apply_hom {T T'} (f : T -> T')
 (hg : HyperGraph T) : HyperGraph T' :=
  mk_hg (prod_map (prod_map f id) id <$> hg.(hyperedges)) hg.(hypervertices).

Definition graph_apply_hom {T T'} (f : T -> T')
  {n m} (cohg : CospanHyperGraph T n m) : CospanHyperGraph T' n m :=
  mk_cohg (hypergraph_apply_hom f cohg.(hedges)) cohg.(inputs) cohg.(outputs).

Lemma prod_map_proper `{RA : relation A, RB : relation B, RC : relation C,
  RD : relation D} (f : A -> C) (g : B -> D) :
  Proper (RA ==> RC) f -> Proper (RB ==> RD) g ->
  Proper (prod_relation RA RB ==> prod_relation RC RD) (prod_map f g).
Proof.
  firstorder.
Qed.

Lemma prod_map_proper_equiv `{Equiv A, Equiv B, Equiv C, Equiv D}
  (f : A -> C) (g : B -> D) :
  Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
  Proper (equiv ==> equiv) (prod_map f g).
Proof.
  apply prod_map_proper.
Qed.

Add Parametric Morphism `{Equiv T, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) :
  (hypergraph_apply_hom f) with signature equiv ==> equiv
  as hypergraph_apply_hom_proper.
Proof.
  intros hg hg' Heq.
  split; [|apply Heq].
  cbn.
  apply map_fmap_proper, Heq.
  apply prod_map_proper; [|apply _].
  apply prod_map_proper; [|apply _].
  apply _.
Qed.

Add Parametric Morphism `{Equiv T, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) {n m} :
  (graph_apply_hom f) with signature (@cohg_eq T n m _) ==> cohg_eq
  as graph_apply_hom_cohg_eq.
Proof.
  intros cohg cohg' Heq.
  apply mk_cohg_eq; [apply Heq..|].
  now apply hypergraph_apply_hom_proper_Proper, Heq.
Qed.



Section hypergraph_hom.

Context {T T' T'' : Type} (f : T -> T').

Implicit Types hg : HyperGraph T.

Lemma hypergraph_apply_hom_empty :
  hypergraph_apply_hom f (∅ :> HyperGraph T) = ∅.
Proof.
  done.
Qed.

Lemma hypergraph_apply_hom_union hg hg' :
  hypergraph_apply_hom f (hg ∪ hg') =
  hypergraph_apply_hom f hg ∪ hypergraph_apply_hom f hg'.
Proof.
  apply hg_ext; [|done].
  cbn.
  apply map_fmap_union.
Qed.

Lemma hypergraph_apply_hom_relabel g hg :
  hypergraph_apply_hom f (relabel_hg g hg) =
  relabel_hg g (hypergraph_apply_hom f hg).
Proof.
  apply hg_ext; [|done].
  cbn.
  rewrite <- 2 map_fmap_compose.
  apply map_fmap_ext.
  now intros _ [[]] _.
Qed.

Lemma hypergraph_apply_hom_reindex g hg :
  hypergraph_apply_hom f (reindex_hg g hg) =
  reindex_hg g (hypergraph_apply_hom f hg).
Proof.
  apply hg_ext; [|done].
  cbn.
  now rewrite kmap_fmap'.
Qed.

Lemma hypergraph_apply_hom_disj_union hg hg' :
  hypergraph_apply_hom f (hg ⊎ hg') =
  hypergraph_apply_hom f hg ⊎ hypergraph_apply_hom f hg'.
Proof.
  unfold disj_union, hypergraph_disjunion; cbn.
  now rewrite hypergraph_apply_hom_union, 2 hypergraph_apply_hom_reindex,
    2 hypergraph_apply_hom_relabel.
Qed.

Lemma map_to_list_hypergraph_apply_hom hg :
  map_to_list (hypergraph_apply_hom f hg).(hyperedges) =
  prod_map id (prod_map (prod_map f id) id) <$> map_to_list hg.(hyperedges).
Proof.
  apply map_to_list_fmap.
Qed.

Lemma vertices_hg_hypergraph_apply_hom hg :
  vertices_hg (hypergraph_apply_hom f hg) =
  vertices_hg hg.
Proof.
  unfold vertices_hg.
  rewrite map_to_list_hypergraph_apply_hom.
  rewrite list_fmap_bind.
  done.
Qed.

Lemma tg_abstracts_hypergraph_apply_hom hg :
  tg_abstracts (hypergraph_apply_hom f hg) =
  tg_abstracts hg.
Proof.
  unfold tg_abstracts.
  rewrite map_to_list_hypergraph_apply_hom.
  rewrite <- list_fmap_compose.
  done.
Qed.

Lemma hypergraph_apply_hom_compose (g : T' -> T'') hg :
  hypergraph_apply_hom g (hypergraph_apply_hom f hg) =
  hypergraph_apply_hom (g ∘ f) hg.
Proof.
  apply hg_ext; [|done].
  cbn.
  now rewrite <- map_fmap_compose.
Qed.

Lemma hypergraph_apply_hom_id hg :
  hypergraph_apply_hom id hg = hg.
Proof.
  apply hg_ext; [|done].
  cbn.
  now rewrite (map_fmap_ext _ id), map_fmap_id by now intros _ [[]] _.
Qed.

Lemma hypergraph_apply_hom_add_vertices hg vs :
  hypergraph_apply_hom f (hg_add_vertices hg vs) =
  hg_add_vertices (hypergraph_apply_hom f hg) vs.
Proof.
  done.
Qed.

#[export] Instance hypergraph_apply_hom_inj `{!Inj eq eq f} :
  Inj eq eq (hypergraph_apply_hom f).
Proof.
  intros hg hg' Heq.
  apply hg_ext; [|apply (f_equal hypervertices Heq)].
  apply (f_equal hyperedges) in Heq.
  cbn in Heq.
  revert Heq.
  apply (inj _).
Qed.

Lemma hypergraph_apply_hom_equiv_inv `{Equiv T, Equiv T'}
  `{!Inj equiv equiv f} hg hg' :
  (hypergraph_apply_hom f hg) ≡ (hypergraph_apply_hom f hg') ->
  hg ≡ hg'.
Proof.
  intros Heq.
  split; [|apply Heq.2].
  intros i.
  specialize (Heq.1 i).
  cbn.
  rewrite 2 lookup_fmap.
  unfold equiv, option_equiv.
  rewrite <- 2 option_relation_Forall2.
  destruct (hg.(hyperedges) !! i), (hg'.(hyperedges) !! i); [|done..].
  cbn.
  intros Htio.
  split; [|apply Htio].
  split; [|apply Htio].
  apply (inj f _ _ Htio.1.1).
Qed.


End hypergraph_hom.

Section graph_hom.

Context {T T'} (f : T -> T') .

Lemma graph_apply_hom_relabel_graph {n m} g (cohg : CospanHyperGraph T n m) :
  graph_apply_hom f (relabel_graph g cohg) =
  relabel_graph g (graph_apply_hom f cohg).
Proof.
  apply cohg_ext; [|done..].
  apply hypergraph_apply_hom_relabel.
Qed.

Lemma graph_apply_hom_reindex_graph {n m} g (cohg : CospanHyperGraph T n m) :
  graph_apply_hom f (reindex_graph g cohg) =
  reindex_graph g (graph_apply_hom f cohg).
Proof.
  apply cohg_ext; [|done..].
  apply hypergraph_apply_hom_reindex.
Qed.

Lemma graph_apply_hom_add_top_loop {n m} (cohg : CospanHyperGraph T (S n) (S m)) :
  graph_apply_hom f (add_top_loop cohg) =
  add_top_loop (graph_apply_hom f cohg).
Proof.
  unfold add_top_loop.
  rewrite graph_apply_hom_relabel_graph.
  done.
Qed.

Context {n m : nat}.

Implicit Types cohg : CospanHyperGraph T n m.

Lemma vertices_graph_apply_hom cohg :
  vertices (graph_apply_hom f cohg) =
  vertices cohg.
Proof.
  unfold vertices.
  f_equal.
  apply vertices_hg_hypergraph_apply_hom.
Qed.

Lemma graph_apply_hom_id_graph :
  graph_apply_hom f (@id_graph T n) = id_graph n.
Proof.
  done.
Qed.

Lemma graph_apply_hom_cup_graph :
  graph_apply_hom f (@cup_graph T n) = cup_graph n.
Proof.
  done.
Qed.

Lemma graph_apply_hom_cap_graph :
  graph_apply_hom f (@cap_graph T n) = cap_graph n.
Proof.
  done.
Qed.

Lemma graph_apply_hom_swap_graph :
  graph_apply_hom f (@swap_graph T n m) = swap_graph n m.
Proof.
  done.
Qed.

Lemma graph_apply_hom_graph_of_tensor t :
  graph_apply_hom f (graph_of_tensor t n m) =
  graph_of_tensor (f t) n m.
Proof.
  done.
Qed.

Lemma graph_apply_hom_swapped_stack_graphs_aux {n' m'} cohg (cohg' : CospanHyperGraph T n' m') :
  graph_apply_hom f (swapped_stack_graphs_aux cohg cohg') =
  swapped_stack_graphs_aux (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  apply cohg_ext; [|done..].
  apply hypergraph_apply_hom_union.
Qed.

Lemma graph_apply_hom_swapped_stack_graphs {n' m'} cohg (cohg' : CospanHyperGraph T n' m') :
  graph_apply_hom f (swapped_stack_graphs cohg cohg') =
  swapped_stack_graphs (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  unfold swapped_stack_graphs.
  rewrite graph_apply_hom_swapped_stack_graphs_aux, 2 graph_apply_hom_relabel_graph,
    2 graph_apply_hom_reindex_graph.
  done.
Qed.

Lemma graph_apply_hom_add_top_loops {o}
  (cohg : CospanHyperGraph T (o + n) (o + m)) :
  graph_apply_hom f (add_top_loops cohg) =
  add_top_loops (graph_apply_hom f cohg).
Proof.
  induction o as [|o IHo]; [done|].
  cbn.
  rewrite IHo, graph_apply_hom_add_top_loop.
  done.
Qed.

Lemma graph_apply_hom_stack_graphs_aux {n' m'} cohg (cohg' : CospanHyperGraph T n' m') :
  graph_apply_hom f (stack_graphs_aux cohg cohg') =
  stack_graphs_aux (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  apply cohg_ext; [|done..].
  apply hypergraph_apply_hom_union.
Qed.

Lemma graph_apply_hom_stack_graphs {n' m'} cohg (cohg' : CospanHyperGraph T n' m') :
  graph_apply_hom f (stack_graphs cohg cohg') =
  stack_graphs (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  unfold stack_graphs.
  rewrite graph_apply_hom_stack_graphs_aux, 2 graph_apply_hom_relabel_graph,
    2 graph_apply_hom_reindex_graph.
  done.
Qed.

Lemma graph_apply_hom_compose_graphs_aux {o} cohg (cohg' : CospanHyperGraph T m o) :
  graph_apply_hom f (compose_graphs_aux cohg cohg') =
  compose_graphs_aux (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  rewrite hypergraph_apply_hom_relabel, hypergraph_apply_hom_add_vertices,
    hypergraph_apply_hom_union.
  rewrite 2 vertices_hg_hypergraph_apply_hom.
  done.
Qed.

Lemma graph_apply_hom_compose_graphs {o} cohg (cohg' : CospanHyperGraph T m o) :
  graph_apply_hom f (compose_graphs cohg cohg') =
  compose_graphs (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  rewrite 2 compose_graphs_to_compose_graphs_aux.
  rewrite graph_apply_hom_compose_graphs_aux,
    2 graph_apply_hom_reindex_graph, 2 graph_apply_hom_relabel_graph.
  done.
Qed.

Lemma graph_apply_hom_compose_graphs_unsafe {o} cohg (cohg' : CospanHyperGraph T m o) :
  graph_apply_hom f (compose_graphs_unsafe cohg cohg') =
  compose_graphs_unsafe (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  rewrite hypergraph_apply_hom_add_vertices,
    hypergraph_apply_hom_union.
  rewrite 2 vertices_hg_hypergraph_apply_hom.
  done.
Qed.

Lemma graph_apply_hom_isomorphic cohg cohg' :
  isomorphic cohg cohg' ->
  isomorphic (graph_apply_hom f cohg) (graph_apply_hom f cohg').
Proof.
  intros [].
  rewrite graph_apply_hom_relabel_graph, graph_apply_hom_reindex_graph.
  now constructor.
Qed.

#[export] Instance graph_apply_hom_inj `{!Inj eq eq f} :
  Inj eq eq (@graph_apply_hom _ _ f n m).
Proof.
  intros cohg cohg' Heq.
  apply cohg_ext; [|apply (f_equal inputs Heq)|apply (f_equal outputs Heq)].
  generalize (f_equal hedges Heq).
  cbn.
  apply (inj _).
Qed.

Lemma graph_apply_hom_isomorphic_inv `{!Inj eq eq f} cohg cohg' :
  isomorphic (graph_apply_hom f cohg) (graph_apply_hom f cohg') ->
  isomorphic cohg cohg'.
Proof.
  intros (fe & fv & Hfe & Hfv & Heq)%isomorphic_exists.
  rewrite <- graph_apply_hom_reindex_graph, <- graph_apply_hom_relabel_graph in Heq.
  apply (inj _) in Heq.
  subst.
  now constructor.
Qed.

Lemma graph_apply_hom_cohg_eq_inv `{Equiv T, Equiv T'}
  `{!Inj equiv equiv f} cohg cohg' :
  cohg_eq (graph_apply_hom f cohg) (graph_apply_hom f cohg') ->
  cohg_eq cohg cohg'.
Proof.
  intros Heq.
  apply mk_cohg_eq; [apply Heq..|].
  apply (hypergraph_apply_hom_equiv_inv f), Heq.
Qed.


Lemma referrenced_vertices_graph_apply_hom cohg :
  referrenced_vertices (graph_apply_hom f cohg) =
  referrenced_vertices cohg.
Proof.
  unfold referrenced_vertices.
  f_equal.
  cbn.
  rewrite map_to_list_fmap, list_fmap_bind.
  done.
Qed.

Lemma isolated_vertices_graph_apply_hom cohg :
  isolated_vertices (graph_apply_hom f cohg) =
  isolated_vertices cohg.
Proof.
  unfold isolated_vertices.
  rewrite referrenced_vertices_graph_apply_hom.
  done.
Qed.

Lemma graph_apply_hom_norm_verts cohg :
  graph_apply_hom f (norm_verts cohg) = norm_verts (graph_apply_hom f cohg).
Proof.
  apply cohg_ext; [|done..].
  cbn.
  rewrite isolated_vertices_graph_apply_hom.
  done.
Qed.

Lemma graph_apply_hom_cohg_vert_eq cohg cohg' :
  cohg ≡ᵥ cohg' ->
  graph_apply_hom f cohg ≡ᵥ graph_apply_hom f cohg'.
Proof.
  intros Hnorm.
  unfold cohg_vert_eq.
  now rewrite <- graph_apply_hom_norm_verts, Hnorm, graph_apply_hom_norm_verts.
Qed.

Lemma graph_apply_hom_cohg_vert_eq_inv `{Hf : !Inj eq eq f} cohg cohg' :
  graph_apply_hom f cohg ≡ᵥ graph_apply_hom f cohg' ->
  cohg ≡ᵥ cohg'.
Proof.
  unfold cohg_vert_eq.
  intros Heq.
  rewrite <- 2 graph_apply_hom_norm_verts in Heq.
  revert Heq.
  apply graph_apply_hom_inj.
Qed.


Lemma graph_apply_hom_equiv_inv `{Equiv T, Equiv T',
  Equivalence T equiv, Equivalence T' equiv}
  `{!Inj equiv equiv f} cohg cohg' :
  (graph_apply_hom f cohg) ≡ (graph_apply_hom f cohg') ->
  cohg ≡ cohg'.
Proof.
  rewrite 2 (relation_equiv_iff.1 cohg_equiv_alt').
  unfold rel_preimage.
  rewrite <- 2 graph_apply_hom_norm_verts.
  apply graph_apply_hom_cohg_eq_inv.
Qed.

Lemma graph_apply_hom_struct_isomorphic cohg cohg' :
  cohg ≡ᵢ cohg' ->
  graph_apply_hom f cohg ≡ᵢ graph_apply_hom f cohg'.
Proof.
  unfold struct_isomorphic.
  rewrite <- 2 graph_apply_hom_norm_verts.
  apply graph_apply_hom_isomorphic.
Qed.


Lemma graph_apply_hom_struct_isomorphic_inv `{!Inj eq eq f} cohg cohg' :
  (graph_apply_hom f cohg) ≡ᵢ (graph_apply_hom f cohg') ->
  cohg ≡ᵢ cohg'.
Proof.
  unfold struct_isomorphic.
  rewrite <- 2 graph_apply_hom_norm_verts.
  apply graph_apply_hom_isomorphic_inv.
Qed.

Lemma graph_apply_hom_syntactic_eq `{Equiv T, Equiv T'}
  `{Hf : !Proper (equiv ==> equiv) f}
  cohg cohg' :
  cohg ≡ₛ cohg' ->
  graph_apply_hom f cohg ≡ₛ graph_apply_hom f cohg'.
Proof.
  intros Heq.
  induction Heq as [cohg cohg' fv fe Hfv Hfe Heq].
  rewrite graph_apply_hom_relabel_graph, graph_apply_hom_reindex_graph.
  constructor; [done..|].
  rewrite <- 2 graph_apply_hom_norm_verts.
  now apply graph_apply_hom_cohg_eq_Proper.
Qed.

Lemma graph_apply_hom_equiv `{Equiv T, Equiv T'}
  `{Hf : !Proper (equiv ==> equiv) f}
  cohg cohg' :
  cohg ≡ cohg' ->
  graph_apply_hom f cohg ≡ graph_apply_hom f cohg'.
Proof.
  refine ((relation_subseteq_iff (RA':=rel_preimage (graph_apply_hom _) _)).1 _ _ _).
  unfold equiv, CospanHyperGraph_equiv.
  rewrite <- rtc_rel_preimage_subseteq.
  apply rtc_subseteq.
  rewrite rel_preimage_union.
  apply rel_union_subseteq, conj.
  - rewrite <- rel_union_subseteq_l.
    apply relation_subseteq_iff.
    refine (graph_apply_hom_cohg_eq_Proper _ _).
  - rewrite <- rel_union_subseteq_r.
    apply relation_subseteq_iff.
    refine graph_apply_hom_cohg_vert_eq.
Qed.

(*
Lemma graph_apply_hom_syntactic_eq_inv `{Equiv T, Equiv T',
  Equivalence T equiv, Equivalence T' equiv}
  `{Hf : !Inj equiv equiv f, Hfeq : !Inj eq eq f}
  (Hfsurj : forall a b, f a ≡ b -> exists a', f a' = b) cohg cohg' :
  graph_apply_hom f cohg ≡ₛ graph_apply_hom f cohg' ->
  cohg ≡ₛ cohg'.
Proof.
  rewrite 2 (relation_equiv_iff.1 cohg_syntactic_eq_alt).
  refine ((relation_subseteq_iff (RA:=rel_preimage (graph_apply_hom _) _)).1 _ _ _).
  rewrite rel_preimage_rtc.
  
  intros (cohg'' & fv & fe & Hfv & Hfe & Hveq & Happl)%cohg_syntactic_eq_exists.

   *)

End graph_hom.

Add Parametric Morphism {T T'} (f : T -> T') {n m} :
  (graph_apply_hom f) with signature (@isomorphic T n m) ==> isomorphic
  as graph_apply_hom_isomorphic_mor.
Proof.
  apply graph_apply_hom_isomorphic.
Qed.

Add Parametric Morphism {T T'} (f : T -> T') {n m} :
  (graph_apply_hom f) with signature (@struct_isomorphic T n m) ==> struct_isomorphic
  as graph_apply_hom_struct_isomorphic_mor.
Proof.
  apply graph_apply_hom_struct_isomorphic.
Qed.

Add Parametric Morphism {T T'} (f : T -> T') {n m} :
  (graph_apply_hom f) with signature (@cohg_vert_eq T n m) ==> cohg_vert_eq
  as graph_apply_hom_cohg_vert_eq_mor.
Proof.
  apply graph_apply_hom_cohg_vert_eq.
Qed.


Add Parametric Morphism `{Equiv T, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) {n m} :
  (graph_apply_hom f) with signature (≡@{CospanHyperGraph T n m}) ==> equiv
  as graph_apply_hom_proper.
Proof.
  now apply graph_apply_hom_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) {n m} :
  (graph_apply_hom f) with signature (@cohg_syntactic_eq T _ n m) ==> cohg_syntactic_eq
  as graph_apply_hom_cohg_syntactic_eq_mor.
Proof.
  now apply graph_apply_hom_syntactic_eq.
Qed.




Section correctness.


Context `{SR : SemiRing R rO rI radd rmul req,
  SA : Summable A, EQA : EqDecision A} `{Equiv T} `{Equivalence T equiv}
    `{Equiv T'} `{Equivalence T' equiv}.

Context `{TensT : !TensorLike R A T, TensT' : !TensorLike R A T'}.



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

Lemma graph_apply_hom_correct (f : T -> T') `{Hf : !Proper (equiv ==> equiv) f}
  `{Hfhom : !TensorLikeHom R A f}
  {n m} (cohg : CospanHyperGraph T n m) :
  graph_semantics (SR:=SR) (graph_apply_hom f cohg) ≡ graph_semantics cohg.
Proof.
  intros v w Hv Hw.
  cbn -[ntl_total_semantics graph_mabs].

  rewrite 2 ntl_total_semantics_alt by apply graph_namedtensorlist_semantics_WF.
  cbn -[abstracts_semantics_alt deltas_semantics_alt].
  rewrite vertices_graph_apply_hom.
  apply sum_of_ext'; intros mr Hmr%elem_of_Vmap_elements_1.
  f_equiv; [|done].
  setoid_rewrite tg_abstracts_hypergraph_apply_hom.
  apply Rlist_prod_ext.
  apply Forall2_fmap, Forall_Forall2_diag.
  rewrite Forall_forall.
  intros [[t i] o] _.
  apply abstract_semantics_alt_ext_tens.
  - unfold graph_mabs.
    rewrite <- map_fmap_compose.
    rewrite 2 lookup_fmap.
    destruct ((hedges cohg).(hyperedges) !! t) as [dt|]; [|done].
    cbn.
    constructor.
    refine (interpretTensor_hom dt.1.1).
  - eapply map_Forall_impl; [apply Hmr.2|].
    cbn.
    intros ? ?; apply SummedElement_iff.
  - now apply make_vecs_map_SummedElements.
Qed.




End correctness.