Require Export SPTensorGraph SPGraphRewriting.


#[export] Instance cosphg_eq_subrelation `{Equiv T} {n m} :
  subrelation (@cosphg_eq T n m _) equiv.
Proof.
  intros ? ? ?; now apply rtc_once; right.
Qed.

#[export] Instance spisomorphic_subrelation `{Equiv T} {n m} :
  subrelation (@spisomorphic T n m) equiv.
Proof.
  intros ? ? ?; now apply rtc_once; left.
Qed.





Definition sphypergraph_apply_hom {T T'} (f : T -> T')
 (sphg : SPHyperGraph T) : SPHyperGraph T' :=
  mk_sphg (prod_map f id <$> sphg.(sphyperedges)) sphg.(sphypervertices).

Definition spgraph_apply_hom {T T'} (f : T -> T')
  {n m} (cosphg : CospanSPHyperGraph T n m) : CospanSPHyperGraph T' n m :=
  mk_cosphg (sphypergraph_apply_hom f cosphg.(sphedges)) cosphg.(spinputs) cosphg.(spoutputs).

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
  (sphypergraph_apply_hom f) with signature equiv ==> equiv
  as sphypergraph_apply_hom_proper.
Proof.
  intros sphg sphg' Heq.
  split; [|apply Heq].
  cbn.
  apply map_fmap_proper, Heq.
  apply prod_map_proper; [|apply _].
  apply _.
Qed.

Add Parametric Morphism `{Equiv T, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) {n m} :
  (spgraph_apply_hom f) with signature (@cosphg_eq T n m _) ==> cosphg_eq
  as spgraph_apply_hom_cosphg_eq.
Proof.
  intros cosphg cosphg' Heq.
  apply mk_cosphg_eq; [apply Heq..|].
  now apply sphypergraph_apply_hom_proper_Proper, Heq.
Qed.



Section sphypergraph_hom.

Context {T T' T'' : Type} (f : T -> T').

Implicit Types sphg : SPHyperGraph T.

Lemma sphypergraph_apply_hom_empty :
  sphypergraph_apply_hom f (∅ :> SPHyperGraph T) = ∅.
Proof.
  done.
Qed.

Lemma sphypergraph_apply_hom_union sphg sphg' :
  sphypergraph_apply_hom f (sphg ∪ sphg') =
  sphypergraph_apply_hom f sphg ∪ sphypergraph_apply_hom f sphg'.
Proof.
  apply sphg_ext; [|done].
  cbn.
  apply map_fmap_union.
Qed.

Lemma sphypergraph_apply_hom_relabel g sphg :
  sphypergraph_apply_hom f (relabel_sphg g sphg) =
  relabel_sphg g (sphypergraph_apply_hom f sphg).
Proof.
  apply sphg_ext; [|done].
  cbn.
  rewrite <- 2 map_fmap_compose.
  apply map_fmap_ext.
  now intros _ [] _.
Qed.

Lemma sphypergraph_apply_hom_reindex g sphg :
  sphypergraph_apply_hom f (reindex_sphg g sphg) =
  reindex_sphg g (sphypergraph_apply_hom f sphg).
Proof.
  apply sphg_ext; [|done].
  cbn.
  now rewrite kmap_fmap'.
Qed.

Lemma sphypergraph_apply_hom_disj_union sphg sphg' :
  sphypergraph_apply_hom f (sphg ⊎ sphg') =
  sphypergraph_apply_hom f sphg ⊎ sphypergraph_apply_hom f sphg'.
Proof.
  unfold disj_union, sphypergraph_disjunion; cbn.
  now rewrite sphypergraph_apply_hom_union, 2 sphypergraph_apply_hom_reindex,
    2 sphypergraph_apply_hom_relabel.
Qed.

Lemma map_to_list_sphypergraph_apply_hom sphg :
  map_to_list (sphypergraph_apply_hom f sphg).(sphyperedges) =
  prod_map id (prod_map f id) <$> map_to_list sphg.(sphyperedges).
Proof.
  apply map_to_list_fmap.
Qed.

Lemma vertices_sphg_sphypergraph_apply_hom sphg :
  vertices_sphg (sphypergraph_apply_hom f sphg) =
  vertices_sphg sphg.
Proof.
  unfold vertices_sphg.
  rewrite map_to_list_sphypergraph_apply_hom.
  rewrite list_fmap_bind.
  done.
Qed.

Lemma sphypergraph_apply_hom_compose (g : T' -> T'') sphg :
  sphypergraph_apply_hom g (sphypergraph_apply_hom f sphg) =
  sphypergraph_apply_hom (g ∘ f) sphg.
Proof.
  apply sphg_ext; [|done].
  cbn.
  now rewrite <- map_fmap_compose.
Qed.

Lemma sphypergraph_apply_hom_id sphg :
  sphypergraph_apply_hom id sphg = sphg.
Proof.
  apply sphg_ext; [|done].
  cbn.
  now rewrite (map_fmap_ext _ id), map_fmap_id by now intros _ [] _.
Qed.

Lemma sphypergraph_apply_hom_add_vertices sphg vs :
  sphypergraph_apply_hom f (sphg_add_vertices sphg vs) =
  sphg_add_vertices (sphypergraph_apply_hom f sphg) vs.
Proof.
  done.
Qed.

#[export] Instance sphypergraph_apply_hom_inj `{!Inj eq eq f} :
  Inj eq eq (sphypergraph_apply_hom f).
Proof.
  intros sphg sphg' Heq.
  apply sphg_ext; [|apply (f_equal sphypervertices Heq)].
  apply (f_equal sphyperedges) in Heq.
  cbn in Heq.
  revert Heq.
  apply (inj _).
Qed.

Lemma sphypergraph_apply_hom_equiv_inv `{Equiv T, Equiv T'}
  `{!Inj equiv equiv f} sphg sphg' :
  (sphypergraph_apply_hom f sphg) ≡ (sphypergraph_apply_hom f sphg') ->
  sphg ≡ sphg'.
Proof.
  intros Heq.
  split; [|apply Heq.2].
  intros i.
  specialize (Heq.1 i).
  cbn.
  rewrite 2 lookup_fmap.
  unfold equiv, option_equiv.
  rewrite <- 2 option_relation_Forall2.
  destruct (sphg.(sphyperedges) !! i), (sphg'.(sphyperedges) !! i); [|done..].
  cbn.
  intros Htio.
  split; [|apply Htio].
  apply (inj f _ _ Htio.1).
Qed.


End sphypergraph_hom.

Section spgraph_hom.

Context {T T'} (f : T -> T') .

Lemma spgraph_apply_hom_relabel_spgraph {n m} g (cosphg : CospanSPHyperGraph T n m) :
  spgraph_apply_hom f (relabel_spgraph g cosphg) =
  relabel_spgraph g (spgraph_apply_hom f cosphg).
Proof.
  apply cosphg_ext; [|done..].
  apply sphypergraph_apply_hom_relabel.
Qed.

Lemma spgraph_apply_hom_reindex_spgraph {n m} g (cosphg : CospanSPHyperGraph T n m) :
  spgraph_apply_hom f (reindex_spgraph g cosphg) =
  reindex_spgraph g (spgraph_apply_hom f cosphg).
Proof.
  apply cosphg_ext; [|done..].
  apply sphypergraph_apply_hom_reindex.
Qed.

Lemma spgraph_apply_hom_spadd_top_loop {n m} (cosphg : CospanSPHyperGraph T (S n) (S m)) :
  spgraph_apply_hom f (spadd_top_loop cosphg) =
  spadd_top_loop (spgraph_apply_hom f cosphg).
Proof.
  unfold spadd_top_loop.
  rewrite spgraph_apply_hom_relabel_spgraph.
  done.
Qed.

Context {n m : nat}.

Implicit Types cosphg : CospanSPHyperGraph T n m.

Lemma vertices_spgraph_apply_hom cosphg :
  vertices (spgraph_apply_hom f cosphg) =
  vertices cosphg.
Proof.
  unfold vertices.
  f_equal.
  apply vertices_sphg_sphypergraph_apply_hom.
Qed.

Lemma spgraph_apply_hom_id_spgraph :
  spgraph_apply_hom f (@id_spgraph T n) = id_spgraph n.
Proof.
  done.
Qed.

Lemma spgraph_apply_hom_cup_spgraph :
  spgraph_apply_hom f (@cup_spgraph T n) = cup_spgraph n.
Proof.
  done.
Qed.

Lemma spgraph_apply_hom_cap_spgraph :
  spgraph_apply_hom f (@cap_spgraph T n) = cap_spgraph n.
Proof.
  done.
Qed.

Lemma spgraph_apply_hom_swap_spgraph :
  spgraph_apply_hom f (@swap_spgraph T n m) = swap_spgraph n m.
Proof.
  done.
Qed.

Lemma spgraph_apply_hom_spgraph_of_tensor t :
  spgraph_apply_hom f (spgraph_of_tensor t n m) =
  spgraph_of_tensor (f t) n m.
Proof.
  done.
Qed.

Lemma spgraph_apply_hom_swapped_stack_spgraphs_aux {n' m'} cosphg (cosphg' : CospanSPHyperGraph T n' m') :
  spgraph_apply_hom f (swapped_stack_spgraphs_aux cosphg cosphg') =
  swapped_stack_spgraphs_aux (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  apply cosphg_ext; [|done..].
  apply sphypergraph_apply_hom_union.
Qed.

Lemma spgraph_apply_hom_swapped_stack_spgraphs {n' m'} cosphg (cosphg' : CospanSPHyperGraph T n' m') :
  spgraph_apply_hom f (swapped_stack_spgraphs cosphg cosphg') =
  swapped_stack_spgraphs (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  unfold swapped_stack_spgraphs.
  rewrite spgraph_apply_hom_swapped_stack_spgraphs_aux, 2 spgraph_apply_hom_relabel_spgraph,
    2 spgraph_apply_hom_reindex_spgraph.
  done.
Qed.

Lemma spgraph_apply_hom_spadd_top_loops {o}
  (cosphg : CospanSPHyperGraph T (o + n) (o + m)) :
  spgraph_apply_hom f (spadd_top_loops cosphg) =
  spadd_top_loops (spgraph_apply_hom f cosphg).
Proof.
  induction o as [|o IHo]; [done|].
  cbn.
  rewrite IHo, spgraph_apply_hom_spadd_top_loop.
  done.
Qed.

Lemma spgraph_apply_hom_stack_spgraphs_aux {n' m'} cosphg (cosphg' : CospanSPHyperGraph T n' m') :
  spgraph_apply_hom f (stack_spgraphs_aux cosphg cosphg') =
  stack_spgraphs_aux (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  apply cosphg_ext; [|done..].
  apply sphypergraph_apply_hom_union.
Qed.

Lemma spgraph_apply_hom_stack_spgraphs {n' m'} cosphg (cosphg' : CospanSPHyperGraph T n' m') :
  spgraph_apply_hom f (stack_spgraphs cosphg cosphg') =
  stack_spgraphs (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  unfold stack_spgraphs.
  rewrite spgraph_apply_hom_stack_spgraphs_aux, 2 spgraph_apply_hom_relabel_spgraph,
    2 spgraph_apply_hom_reindex_spgraph.
  done.
Qed.

Lemma spgraph_apply_hom_compose_spgraphs_aux {o} cosphg (cosphg' : CospanSPHyperGraph T m o) :
  spgraph_apply_hom f (compose_spgraphs_aux cosphg cosphg') =
  compose_spgraphs_aux (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  rewrite sphypergraph_apply_hom_relabel, sphypergraph_apply_hom_add_vertices,
    sphypergraph_apply_hom_union.
  done.
Qed.

Lemma spgraph_apply_hom_compose_spgraphs {o} cosphg (cosphg' : CospanSPHyperGraph T m o) :
  spgraph_apply_hom f (compose_spgraphs cosphg cosphg') =
  compose_spgraphs (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  rewrite 2 compose_spgraphs_to_compose_spgraphs_aux.
  rewrite spgraph_apply_hom_compose_spgraphs_aux,
    2 spgraph_apply_hom_reindex_spgraph, 2 spgraph_apply_hom_relabel_spgraph.
  done.
Qed.

Lemma spgraph_apply_hom_compose_spgraphs_unsafe {o} cosphg (cosphg' : CospanSPHyperGraph T m o) :
  spgraph_apply_hom f (compose_spgraphs_unsafe cosphg cosphg') =
  compose_spgraphs_unsafe (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  rewrite sphypergraph_apply_hom_add_vertices,
    sphypergraph_apply_hom_union.
  done.
Qed.

Lemma spgraph_apply_hom_spisomorphic cosphg cosphg' :
  spisomorphic cosphg cosphg' ->
  spisomorphic (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg').
Proof.
  intros [].
  rewrite spgraph_apply_hom_relabel_spgraph, spgraph_apply_hom_reindex_spgraph.
  now constructor.
Qed.

#[export] Instance spgraph_apply_hom_inj `{!Inj eq eq f} :
  Inj eq eq (@spgraph_apply_hom _ _ f n m).
Proof.
  intros cosphg cosphg' Heq.
  apply cosphg_ext; [|apply (f_equal spinputs Heq)|apply (f_equal spoutputs Heq)].
  generalize (f_equal sphedges Heq).
  cbn.
  apply (inj _).
Qed.

Lemma spgraph_apply_hom_spisomorphic_inv `{!Inj eq eq f} cosphg cosphg' :
  spisomorphic (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg') ->
  spisomorphic cosphg cosphg'.
Proof.
  intros (fe & fv & Hfe & Hfv & Heq)%spisomorphic_exists.
  rewrite <- spgraph_apply_hom_reindex_spgraph, <- spgraph_apply_hom_relabel_spgraph in Heq.
  apply (inj _) in Heq.
  subst.
  now constructor.
Qed.

Lemma spgraph_apply_hom_cosphg_eq_inv `{Equiv T, Equiv T'}
  `{!Inj equiv equiv f} cosphg cosphg' :
  cosphg_eq (spgraph_apply_hom f cosphg) (spgraph_apply_hom f cosphg') ->
  cosphg_eq cosphg cosphg'.
Proof.
  intros Heq.
  apply mk_cosphg_eq; [apply Heq..|].
  apply (sphypergraph_apply_hom_equiv_inv f), Heq.
Qed.


Lemma spgraph_apply_hom_equiv_inv `{Equiv T, Reflexive T equiv, Equiv T', 
  Equivalence T' equiv}
  `{!Inj equiv equiv f} cosphg cosphg' :
  (spgraph_apply_hom f cosphg) ≡ (spgraph_apply_hom f cosphg') ->
  cosphg ≡ cosphg'.
Proof.
  intros (cosphg'' & (fe & fv & Hfe & Hfv & ->)%spisomorphic_exists & Heq)%cosphg_equiv_alt.
  rewrite <- spgraph_apply_hom_reindex_spgraph, 
    <- spgraph_apply_hom_relabel_spgraph in Heq.
  apply spgraph_apply_hom_cosphg_eq_inv in Heq.
  etransitivity; [|apply cosphg_eq_subrelation, Heq].
  apply spisomorphic_subrelation.
  now constructor.
Qed.


Lemma spreferrenced_vertices_spgraph_apply_hom cosphg :
  spreferrenced_vertices (spgraph_apply_hom f cosphg) =
  spreferrenced_vertices cosphg.
Proof.
  unfold spreferrenced_vertices.
  f_equal.
  cbn.
  rewrite map_to_list_fmap, list_fmap_bind.
  done.
Qed.

Lemma spisolated_vertices_spgraph_apply_hom cosphg :
  spisolated_vertices (spgraph_apply_hom f cosphg) =
  spisolated_vertices cosphg.
Proof.
  unfold spisolated_vertices.
  rewrite spreferrenced_vertices_spgraph_apply_hom.
  done.
Qed.

Lemma spgraph_apply_hom_norm_spverts cosphg :
  spgraph_apply_hom f (norm_spverts cosphg) = norm_spverts (spgraph_apply_hom f cosphg).
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  rewrite spisolated_vertices_spgraph_apply_hom.
  done.
Qed.

End spgraph_hom.

Add Parametric Morphism {T T'} (f : T -> T') {n m} :
  (spgraph_apply_hom f) with signature (@spisomorphic T n m) ==> spisomorphic
  as spgraph_apply_hom_spisomorphic_mor.
Proof.
  apply spgraph_apply_hom_spisomorphic.
Qed.


Add Parametric Morphism `{Equiv T, Equivalence T equiv, Equiv T'}
  (f : T -> T') (Hf : Proper (equiv ==> equiv) f) {n m} :
  (spgraph_apply_hom f) with signature (≡@{CospanSPHyperGraph T n m}) ==> equiv
  as spgraph_apply_hom_proper.
Proof.
  refine (proper_cosphg_equiv_of_eq_iso_unary (spgraph_apply_hom f) _ _).
Qed.
