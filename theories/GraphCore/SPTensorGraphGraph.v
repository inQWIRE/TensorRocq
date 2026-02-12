Require Import SPTensorGraph SPIsomorphismTesting SPGraphRewriting.
Require Import TEPerm TensorGraph TensorGraphSP GraphRewriting.


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

Lemma cohg2cosphg_compose {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose cohg cohg') =
  spcompose (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  unfold compose.
  rewrite cohg2cosphg_relabel_graph.
  unfold spcompose.
  f_equal.
  apply cosphg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cohg2cosphg_compose_safe {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose_safe cohg cohg') =
  spcompose_safe (cohg2cosphg cohg) (cohg2cosphg cohg').
Proof.
  rewrite compose_safe_to_compose, spcompose_safe_to_spcompose.
  rewrite cohg2cosphg_compose, 2 cohg2cosphg_reindex_graph,
    2 cohg2cosphg_relabel_graph.
  reflexivity.
Qed.

Lemma cohg2cosphg_compose_unsafe {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  cohg2cosphg (compose_unsafe cohg cohg') =
  spcompose_unsafe (cohg2cosphg cohg) (cohg2cosphg cohg').
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

Lemma cosphg2cohg_compose {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  hg_strongperm_eq (cosphg2cohg (spcompose cosphg cosphg'))
    (compose (cosphg2cohg cosphg) (cosphg2cohg cosphg')).
Proof.
  unfold spcompose.
  rewrite cosphg2cohg_relabel_spgraph.
  unfold compose.
  apply relabel_graph_strongperm_mor.
  apply eq_reflexivity.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.

Lemma cosphg2cohg_compose_safe {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  hg_strongperm_eq (cosphg2cohg (spcompose_safe cosphg cosphg'))
    (compose_safe (cosphg2cohg cosphg) (cosphg2cohg cosphg')).
Proof.
  rewrite compose_safe_to_compose, spcompose_safe_to_spcompose.
  rewrite cosphg2cohg_compose, 2 cosphg2cohg_reindex_spgraph,
    2 cosphg2cohg_relabel_spgraph.
  reflexivity.
Qed.

Lemma cosphg2cohg_compose_unsafe {T n m o}
  (cosphg : CospanSPHyperGraph T n m) (cosphg' : CospanSPHyperGraph T m o) :
  cosphg2cohg (spcompose_unsafe cosphg cosphg') =
  compose_unsafe (cosphg2cohg cosphg) (cosphg2cohg cosphg').
Proof.
  apply cohg_ext; [|done..].
  cbn.
  now rewrite map_fmap_union.
Qed.



