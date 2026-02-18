Require Import SPTensorGraph SPIsomorphismTesting SPGraphRewriting.
Require Import TEPerm TensorGraph TensorGraphSP GraphRewriting.

(* FIXME: Move *)


Definition abs2tv {A} `{Countable B} (abs : A * list B * list B) : A * gmultiset B :=
  (abs.1.1, list_to_set_disj (abs.1.2 ++ abs.2) :> gmultiset B).

Definition tv2abs {A} `{Countable B} (tv : A * gmultiset B) :
  A * list B * list B :=
  (tv.1, elements tv.2, []).

#[global] Arguments abs2tv {_ _ _ _} !_ / : assert.
#[global] Arguments tv2abs {_ _ _ _} !_ / : assert.

Lemma abs2tv2abs {A} `{Countable B} (abs : A * list B * list B) :
  abs_strongperm_eq (tv2abs (abs2tv abs)) abs.
Proof.
  destruct abs as [[a l] u].
  cbn.
  split; [done|].
  cbn.
  now rewrite elements_list_to_set_disj, app_nil_r.
Qed.

Lemma tv2abs2tv {A} `{Countable B} (tv : A * gmultiset B) :
  abs2tv (tv2abs tv) = tv.
Proof.
  destruct tv as [t v]; cbn;
  apply pair_eq.
  split; [done|].
  cbn.
  rewrite app_nil_r.
  apply list_to_set_disj_elements.
Qed.

Definition cohg2cosphg {T n m} (cohg : CospanHyperGraph T n m) :
  CospanSPHyperGraph T n m :=
  cohg.(inputs) ->
    mk_sphg (abs2tv <$> cohg.(hedges).(hyperedges))
      cohg.(hedges).(hypervertices)
    <- cohg.(outputs).

Definition cosphg2cohg {T n m} (cosphg : CospanSPHyperGraph T n m) :
  CospanHyperGraph T n m :=
  cosphg.(spinputs) ->
    mk_hg (tv2abs <$> cosphg.(sphedges).(sphyperedges))
      cosphg.(sphedges).(sphypervertices)
    <- cosphg.(spoutputs).

Lemma cohg2cosphg2cohg {T n m} (cohg : CospanHyperGraph T n m) :
  hg_strongperm_eq (cosphg2cohg (cohg2cosphg cohg)) cohg.
Proof.
  apply mk_hg_strongperm_eq'; [done..|].
  intros i.
  cbn.
  rewrite 2 lookup_fmap.
  destruct (_ !! i) as [hi|]; [cbn|done].
  apply abs2tv2abs.
Qed.

Lemma cosphg2cohg2cosphg {T n m} (cosphg : CospanSPHyperGraph T n m) :
  (cohg2cosphg (cosphg2cohg cosphg)) = cosphg.
Proof.
  apply cosphg_ext; [|done..].
  apply sphg_ext; [|done].
  cbn.
  apply map_eq.
  intros i.
  rewrite 2 lookup_fmap.
  destruct (_ !! i) as [hi|]; [cbn|done].
  now rewrite tv2abs2tv.
Qed.

Add Parametric Morphism {A} `{Countable B} : (@abs2tv A B _ _) with signature
  abs_strongperm_eq ==> eq as abs2tv_strongperm_mor.
Proof.
  intros [[t l] u] [[t' l'] u'].
  cbn.
  intros [[= <-] Hperm].
  cbn in Hperm.
  f_equal.
  now apply list_to_set_disj_perm.
Qed.

Add Parametric Morphism {T n m} : (@cohg2cosphg T n m) with signature
  hg_strongperm_eq ==> eq as cohg2cosphg_strongperm_mor.
Proof.
  intros cohg cohg' (Hins & Houts & Hverts & Hrel).
  apply cosphg_ext; [|done..].
  apply sphg_ext; [|done].
  cbn.
  apply map_eq; intros i.
  rewrite 2 lookup_fmap.
  specialize (Hrel i).
  apply option_relation_Forall2 in Hrel.
  induction Hrel; [|done].
  cbn.
  f_equal.
  now apply abs2tv_strongperm_mor.
Qed.



(* TODO: effect of translations on the various (sp)graph operations
  (relabel and reindex are what we need for isomorphism, but also want
  compose and stack for correctness) *)

Lemma abs2tv_relabel_abs {A} `{Countable B, Countable C}
  (f : B -> C) (abs : A * list B * list B) :
  abs2tv (relabel_abs f abs) = prod_map id (gmultiset_map f) (abs2tv abs).
Proof.
  destruct abs as [[a l] u]; cbn.
  f_equal.
  rewrite gmultiset_map_alt.
  now rewrite elements_list_to_set_disj, fmap_app.
Qed.

Lemma abs2tv_reindex {A B} `{Countable C}
  (f : A -> B) (abs : A * list C * list C) :
  abs2tv (prod_map (prod_map f id) id abs) = prod_map f id (abs2tv abs).
Proof.
  done.
Qed.

Lemma cohg2cosphg_relabel_graph {T n m} f (cohg : CospanHyperGraph T n m) :
  cohg2cosphg (relabel_graph f cohg) = relabel_spgraph f (cohg2cosphg cohg).
Proof.
  apply cosphg_ext; [|done..].
  apply sphg_ext; [|done].
  cbn.
  rewrite <- 2 map_fmap_compose.
  apply map_fmap_ext; intros _ he _.
  apply abs2tv_relabel_abs.
Qed.

Lemma cohg2cosphg_reindex_graph {T n m} f (cohg : CospanHyperGraph T n m) :
  cohg2cosphg (reindex_graph f cohg) = reindex_spgraph f (cohg2cosphg cohg).
Proof.
  apply cosphg_ext; [|done..].
  apply sphg_ext; [|done].
  cbn.
  now rewrite kmap_fmap'.
Qed.

Lemma cohg2cosphg_stack_graphs_aux {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  cohg2cosphg (stack_graphs_aux cohg cohg') =
  stack_spgraphs_aux (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.


Lemma cohg2cosphg_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  cohg2cosphg (stack_graphs cohg cohg') =
  stack_spgraphs (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  unfold stack_graphs.
  rewrite cohg2cosphg_stack_graphs_aux,
    2 cohg2cosphg_relabel_graph, 2 cohg2cosphg_reindex_graph.
  done.
Qed.

Lemma cohg2cosphg_compose_graphs_aux {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose_graphs_aux cohg cohg') =
  compose_spgraphs_aux (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  unfold compose_graphs_aux.
  rewrite cohg2cosphg_relabel_graph.
  unfold compose_spgraphs_aux.
  f_equal.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cohg2cosphg_compose_graphs {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose_graphs cohg cohg') =
  compose_spgraphs (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  rewrite compose_graphs_to_compose_graphs_aux,
    compose_spgraphs_to_compose_spgraphs_aux.
  rewrite cohg2cosphg_compose_graphs_aux, 2 cohg2cosphg_reindex_graph,
    2 cohg2cosphg_relabel_graph.
  reflexivity.
Qed.

Lemma cohg2cosphg_compose_graphs_unsafe {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose_graphs_unsafe cohg cohg') =
  compose_spgraphs_unsafe (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cohg2cosphg_isomorphic {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  isomorphic cohg cohg' ->
  spisomorphic (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%isomorphic_exists.
  rewrite cohg2cosphg_relabel_graph, cohg2cosphg_reindex_graph.
  now constructor.
Qed.

Lemma cohg2cosphg_id_graph {T n} :
  cohg2cosphg (@id_graph T n) = @id_spgraph T n.
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cohg2cosphg_swap_graph {T n m} :
  cohg2cosphg (@swap_graph T n m) = @swap_spgraph T n m.
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cohg2cosphg_cup_graph {T n} :
  cohg2cosphg (@cup_graph T n) = @cup_spgraph T n.
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cohg2cosphg_cap_graph {T n} :
  cohg2cosphg (@cap_graph T n) = @cap_spgraph T n.
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cohg2cosphg_graph_of_tensor {T} (t : T) n m :
  cohg2cosphg (@graph_of_tensor T t n m) =
  spgraph_of_tensor t n m.
Proof.
  apply cosphg_ext; [|done..].
  apply sphg_ext; [|done].
  cbn -[insert].
  etransitivity; [apply map_fmap_singleton|].
  done.
Qed.

Lemma spreferrenced_vertices_cohg2cosphg {T n m} (cohg : CospanHyperGraph T n m) :
  spreferrenced_vertices (cohg2cosphg cohg) =
  referrenced_vertices cohg.
Proof.
  unfold referrenced_vertices, spreferrenced_vertices.
  f_equal.
  cbn.
  rewrite map_to_list_fmap, list_fmap_bind.
  rewrite 2 list_to_set_bind_L.
  f_equal.
  apply list_fmap_ext.
  intros _ [k [[t l] u]] _.
  cbn.
  apply list_to_set_perm_L.
  apply elements_list_to_set_disj.
Qed.

Lemma spisolated_vertices_cohg2cosphg {T n m} (cohg : CospanHyperGraph T n m) :
  spisolated_vertices (cohg2cosphg cohg) =
  isolated_vertices cohg.
Proof.
  unfold isolated_vertices, spisolated_vertices.
  rewrite spreferrenced_vertices_cohg2cosphg.
  done.
Qed.

Lemma cohg2cosphg_norm_spverts {T n m} (cohg : CospanHyperGraph T n m) :
  cohg2cosphg (norm_verts cohg) =
  norm_spverts (cohg2cosphg cohg).
Proof.
  apply cosphg_ext; [|done..].
  apply sphg_ext; [done|].
  cbn.
  now rewrite spisolated_vertices_cohg2cosphg.
Qed.

Lemma abs2tv_equiv `{Equiv T} (hg hg' : HyperEdge T) :
  hg ≡ hg' -> abs2tv hg ≡ abs2tv hg'.
Proof.
  intros [[Ht Hi] Ho].
  split; [apply Ht|].
  unfold abs2tv; cbn.
  now rewrite <- Hi, <- Ho.
Qed.

Lemma cohg2cosphg_cohg_eq `{Equiv T} {n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg_eq cohg cohg' ->
  cosphg_eq (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  intros (Hins & Houts & Hhes).
  apply mk_cosphg_eq; [done..|].
  cbn.
  split; [|apply Hhes.2].
  intros i.
  cbn.
  rewrite 2 lookup_fmap.
  apply option_fmap_proper, Hhes.
  hnf; intros *; apply abs2tv_equiv.
Qed.

Lemma cohg2cosphg_equiv `{Equiv T} {n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ cohg' ->
  cohg2cosphg cohg ≡ cohg2cosphg cohg'.
Proof.
  intros Heq.
  induction Heq as [|cohg cohg' cohg'' Heq _ IHHeq]; [done|].
  rewrite <- IHHeq.
  apply rtc_once.
  destruct Heq as [Heq|Heq]; [left|right].
  - now apply cohg2cosphg_isomorphic.
  - now apply cohg2cosphg_cohg_eq.
Qed.






Lemma tv2abs_relabel {A} `{Countable B, Countable C}
  (f : B -> C) (tv : A * gmultiset B) :
  abs_strongperm_eq (tv2abs (prod_map id (gmultiset_map f) tv)) (relabel_abs f (tv2abs tv)).
Proof.
  split; [done|].
  destruct tv as [t v]; simpl.
  rewrite gmultiset_map_alt.
  now rewrite elements_list_to_set_disj.
Qed.

Lemma tv2abs_reindex {A B} `{Countable C}
  (f : A -> B) (tv : A * gmultiset C) :
  tv2abs (prod_map f id tv) =
    prod_map (prod_map f id) id (tv2abs tv).
Proof.
  done.
Qed.

Lemma cosphg2cohg_relabel_spgraph {T n m} f (cosphg : CospanSPHyperGraph T n m) :
  hg_strongperm_eq (cosphg2cohg (relabel_spgraph f cosphg))
    (relabel_graph f (cosphg2cohg cosphg)).
Proof.
  apply mk_hg_strongperm_eq'; [done..|].
  cbn.
  intros i.
  rewrite 4 lookup_fmap.
  destruct (_ !! _); [cbn|done].
  apply tv2abs_relabel.
Qed.


Lemma cosphg2cohg_reindex_spgraph {T n m} f (cosphg : CospanSPHyperGraph T n m) :
  cosphg2cohg (reindex_spgraph f cosphg) = reindex_graph f (cosphg2cohg cosphg).
Proof.
  apply cohg_ext; [|done..].
  apply hg_ext; [|done].
  cbn.
  now rewrite kmap_fmap'.
Qed.

Lemma cosphg2cohg_stack_spgraphs_aux {T n m n' m'}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T n' m') :
  cosphg2cohg (stack_spgraphs_aux cosphg cosphg') =
  stack_graphs_aux (cosphg2cohg cosphg) (cosphg2cohg cosphg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.


Lemma cosphg2cohg_stack_spgraphs {T n m n' m'}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T n' m') :
  hg_strongperm_eq (cosphg2cohg (stack_spgraphs cosphg cosphg'))
  (stack_graphs (cosphg2cohg cosphg) (cosphg2cohg cosphg')).
Proof.
  unfold stack_spgraphs.
  rewrite cosphg2cohg_stack_spgraphs_aux,
    2 cosphg2cohg_relabel_spgraph, 2 cosphg2cohg_reindex_spgraph.
  done.
Qed.

Lemma cosphg2cohg_compose_spgraphs_aux {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  hg_strongperm_eq (cosphg2cohg (compose_spgraphs_aux cosphg cosphg'))
    (compose_graphs_aux (cosphg2cohg cosphg) (cosphg2cohg cosphg')).
Proof.
  unfold compose_spgraphs_aux.
  rewrite cosphg2cohg_relabel_spgraph.
  unfold compose_graphs_aux.
  apply relabel_graph_strongperm_mor.
  apply eq_reflexivity.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cosphg2cohg_compose_spgraphs {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  hg_strongperm_eq (cosphg2cohg (compose_spgraphs cosphg cosphg'))
    (compose_graphs (cosphg2cohg cosphg) (cosphg2cohg cosphg')).
Proof.
  rewrite compose_graphs_to_compose_graphs_aux, compose_spgraphs_to_compose_spgraphs_aux.
  rewrite cosphg2cohg_compose_spgraphs_aux, 2 cosphg2cohg_reindex_spgraph,
    2 cosphg2cohg_relabel_spgraph.
  reflexivity.
Qed.

Lemma cosphg2cohg_compose_spgraphs_unsafe {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  cosphg2cohg (compose_spgraphs_unsafe cosphg cosphg') =
  compose_graphs_unsafe (cosphg2cohg cosphg) (cosphg2cohg cosphg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cosphg2cohg_spisomorphic_gen {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  spisomorphic cosphg cosphg' ->
  exists cohg,
  hg_strongperm_eq cohg (cosphg2cohg cosphg') /\
  isomorphic (cosphg2cohg cosphg) cohg.
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%spisomorphic_exists.
  eexists.
  rewrite cosphg2cohg_relabel_spgraph, cosphg2cohg_reindex_spgraph.
  split; [done|].
  now constructor.
Qed.

(* TODO: Make relation extending isomorphic for this to be true.

Lemma cohg2cosphg_spisomorphic {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  spisomorphic cosphg cosphg' ->
  isomorphic (cosphg2cohg cosphg) (cosphg2cohg cosphg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%spisomorphic_exists.
  rewrite cosphg2cohg_relabel_spgraph, cohg2cosphg_reindex_graph.
  now constructor.
Qed. *)

Lemma cosphg2cohg_id_spgraph {T n} :
  cosphg2cohg (@id_spgraph T n) = @id_graph T n.
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cosphg2cohg_swap_spgraph {T n m} :
  cosphg2cohg (@swap_spgraph T n m) = @swap_graph T n m.
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cosphg2cohg_cup_spgraph {T n} :
  cosphg2cohg (@cup_spgraph T n) = @cup_graph T n.
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cosphg2cohg_cap_spgraph {T n} :
  cosphg2cohg (@cap_spgraph T n) = @cap_graph T n.
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite fmap_empty.
Qed.

Lemma cosphg2cohg_spgraph_of_tensor {T} (t : T) n m :
  hg_strongperm_eq (cosphg2cohg (@spgraph_of_tensor T t n m))
  (graph_of_tensor t n m).
Proof.
  apply mk_hg_strongperm_eq'; try done.
  cbn -[insert].
  setoid_rewrite map_fmap_singleton.
  intros i.
  rewrite hyperedges_singleton.
  rewrite <- 2 insert_empty.
  rewrite 2 lookup_insert_case.
  case_decide; [|done].
  cbn.
  split; [done|].
  cbn.
  now rewrite elements_list_to_set_disj, app_nil_r.
Qed.

Lemma referrenced_vertices_cosphg2cohg {T n m} (cosphg : CospanSPHyperGraph T n m) :
  referrenced_vertices (cosphg2cohg cosphg) =
  spreferrenced_vertices cosphg.
Proof.
  unfold referrenced_vertices, spreferrenced_vertices.
  f_equal.
  cbn.
  rewrite map_to_list_fmap, list_fmap_bind.
  rewrite 2 list_to_set_bind_L.
  f_equal.
  apply list_fmap_ext.
  intros _ [k [t v]] _.
  cbn.
  now rewrite app_nil_r.
Qed.

Lemma isolated_vertices_cosphg2cohg {T n m} (cosphg : CospanSPHyperGraph T n m) :
  isolated_vertices (cosphg2cohg cosphg) =
  spisolated_vertices cosphg.
Proof.
  unfold isolated_vertices, spisolated_vertices.
  now rewrite referrenced_vertices_cosphg2cohg.
Qed.


Lemma cosphg2cohg_norm_spverts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  cosphg2cohg (norm_spverts cosphg) =
  norm_verts (cosphg2cohg cosphg).
Proof.
  apply cohg_ext; [|done..].
  apply hg_ext; [done|].
  cbn.
  now rewrite isolated_vertices_cosphg2cohg.
Qed.

Lemma tv2abs_equiv `{Equiv T} (hg hg' : SPHyperEdge T) :
  hg ≡ hg' -> tv2abs hg ≡ tv2abs hg'.
Proof.
  intros [Ht Hv].
  split; [split; [apply Ht|]|]; unfold tv2abs; cbn; now f_equal.
Qed.

Lemma cosphg2cohg_cosphg_eq `{Equiv T} {n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  cosphg_eq cosphg cosphg' ->
  cohg_eq (cosphg2cohg cosphg) (cosphg2cohg cosphg').
Proof.
  intros (Hins & Houts & Hhes).
  apply mk_cohg_eq; [done..|].
  cbn.
  split; [|apply Hhes.2].
  intros i.
  cbn.
  rewrite 2 lookup_fmap.
  apply option_fmap_proper, Hhes.
  hnf; intros *; apply tv2abs_equiv.
Qed.

Lemma cosphg2cohg_equiv_gen `{Equiv T, Equivalence T equiv}
  {n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  cosphg ≡ cosphg' ->
  exists cohg,
  hg_strongperm_eq cohg (cosphg2cohg cosphg) /\
  cosphg2cohg cosphg' ≡ cohg.
Proof.
  intros (cosphg'' & (cosphg''' &
    Hperm & Hiso)%spisomorphic_symm%cosphg2cohg_spisomorphic_gen & Hequiv)%cosphg_equiv_alt.
  exists cosphg'''.
  split; [easy|].
  etransitivity; [| apply rtc_once; left; apply Hiso].
  symmetry.
  apply rtc_once; right.
  now apply cosphg2cohg_cosphg_eq.
Qed.