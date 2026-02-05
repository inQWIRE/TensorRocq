Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp Aux_pos.
Require Export HyperGraph.
Require Import TESyntax.

(* FIXME: Move *)

(* Basic definitions and structural operations on TensorGraphs *)

Declare Scope cohg_scope.

Record HyperGraph {T} := mk_hg {
  (* The edges of the hypergraph *)
  hyperedges : Pmap (T * list positive * list positive);
  (* Additional vertices of the hypergraph, which are often
    disjoint from the referrenced vertices of [hyperedges]
    (in practice, we only care about the subset of [hypervertices]
    not referrenced in [hyperedges], but do not enforce disjointness) *)
  hypervertices : Pset;
}.

#[global] Arguments HyperGraph (_) : clear implicits, assert.
#[global] Arguments mk_hg {_} _ _ : assert.

#[global] Coercion hyperedges : HyperGraph >-> Pmap.

Lemma hg_ext {T} (hg hg' : HyperGraph T) :
  hg.(hyperedges) = hg'.(hyperedges) ->
  hg.(hypervertices) = hg'.(hypervertices) ->
  hg = hg'.
Proof.
  destruct hg, hg'; cbn; congruence.
Qed.

#[export] Instance hypergraph_empty {T} :
  Empty (HyperGraph T) := mk_hg ∅ ∅.

#[export] Instance hypergraph_partialalter {T} :
  PartialAlter positive (T * list positive * list positive) (HyperGraph T) :=
  fun f i hg => mk_hg (partial_alter f i hg.(hyperedges)) hg.(hypervertices).

Definition reindex_hg {T} (f : positive -> positive) (hg : HyperGraph T) :
  HyperGraph T :=
  mk_hg (kmap f hg.(hyperedges)) hg.(hypervertices).

Definition relabel_hg {T} (f : positive -> positive) (hg : HyperGraph T) :
  HyperGraph T :=
  mk_hg (relabel_abs f <$> hg.(hyperedges)) (set_map f hg.(hypervertices)).

Definition vertices_hg {T} (hg : HyperGraph T) : Pset :=
  list_to_set (map_to_list (hg.(hyperedges)) ≫=
    λ k_flu : (positive*(T*list _*list _)), (k_flu.2.1.2 ++ k_flu.2.2)) ∪
  hg.(hypervertices).

#[export] Instance hypergraph_union {T} : Union (HyperGraph T) :=
  fun hg hg' =>
    mk_hg (hg.(hyperedges) ∪ hg'.(hyperedges))
      (hg.(hypervertices) ∪ hg'.(hypervertices)).

#[export] Instance hypergraph_disjunion {T} : DisjUnion (HyperGraph T) :=
  fun hg hg' =>
  reindex_hg (bcons false) (relabel_hg (bcons false) hg) ∪
  reindex_hg (bcons false) (relabel_hg (bcons false) hg').


(* A graph with h(yper)edges labeled by elements of [T] *)
Record CospanHyperGraph {T : Type} {n m : nat} := mk_cohg {
  hedges : HyperGraph T;
  inputs : vec positive n;
  outputs : vec positive m;
}.
#[global] Arguments CospanHyperGraph T : clear implicits.
#[global] Arguments mk_cohg {_} {_ _} (_ _ _) : assert.

Notation " ins -> hedges <- outs " := (mk_cohg hedges ins outs) : cohg_scope.

Open Scope cohg_scope.

Definition CospanHyperGraph2triple {T} {n m : nat} (tg : CospanHyperGraph T n m) :=
  (tg.(hedges), (tg.(inputs), tg.(outputs))).

#[global] Coercion CospanHyperGraph2triple : CospanHyperGraph >-> prod.

Definition CospanHyperGraph2HyperGraph {T} {n m} (tg : CospanHyperGraph T n m) := tg.(hedges).
#[global] Coercion CospanHyperGraph2HyperGraph : CospanHyperGraph >-> HyperGraph.

Lemma cohg_ext {T} {n m} (tg tg' : CospanHyperGraph T n m) :
  tg.(hedges) = tg'.(hedges) ->
  tg.(inputs) = tg'.(inputs) ->
  tg.(outputs) = tg'.(outputs) ->
  tg = tg'.
Proof.
  destruct tg, tg'; cbn; congruence.
Qed.

Section CospanHyperGraph.

  Context {T : Type}.
  Context {n m : nat}.

  Let CoHyGraph := (CospanHyperGraph T n m).

  Implicit Types chg : CoHyGraph.

  Definition add_vertex_r (n : positive) (v : positive) (tg : CoHyGraph) : CoHyGraph :=
  tg.(inputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) =>
        match tipop with
        | (t, ip, op) => (t, ip, v::op)
        end)
      n
      tg.(hedges))
  <- tg.(outputs).

  Definition add_vertex_l {T : Type} {o p} (n : positive) (v : positive) (tg : CospanHyperGraph T o p) : CospanHyperGraph T o p :=
  tg.(inputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) =>
        match tipop with
        | (t, ip, op) => (t, v::ip, op)
        end)
      n
      tg.1)
  <- tg.(outputs).

  Definition add_edge {T : Type} {o p} (n : positive) (t : T) (tg : CospanHyperGraph T o p) :
  CospanHyperGraph T o p :=
    tg.2.1 -> (<[ n := (t, [], []) ]> tg.1) <- tg.2.2.

  (* Instance insert_hg {T: Type} : Insert positive T (HyperGraph T) := {
    insert := add_edge
  }. *)

  #[global] Instance empty_cohg {T : Type} : Empty (CospanHyperGraph T 0 0) := {
    empty := Vector.nil -> ∅ <- Vector.nil
  }.

  Definition add_input {n m} (p : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T (S n) m :=
  Vector.cons p tg.2.1 -> tg.1 <- tg.2.2.

  Definition add_output {n m} (p : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T n (S m) :=
  tg.2.1 -> tg.1 <- Vector.cons p tg.2.2.

  (* Local Open Scope positive.
  Local Open Scope vector_scope.

  Definition example_cohg : CospanHyperGraph positive 0 0 :=
    ([#] -> {[ 1 := (1, [], []); 2:= (2, [], []) ]} <- [#]).

  Compute example_cohg. *)



(* Definition is_input (tm : gmap nat T) (nm : positive * positive) : Prop :=
  is_key tm (fst nm).

Definition is_output (tm : gmap nat T) (nm : edge) : Prop :=
  is_key tm (snd nm).

Definition is_internal tm (e : edge) :=
  is_key tm (fst e) /\ is_key tm (snd e).

Definition not_internal tm (e : edge) :=
  ~ is_internal tm e. *)

Definition wrapover_r {n m} (tg : CospanHyperGraph T n m) :=
  match tg with
  | l -> hg <- r => [#] -> hg <- l +++ r
  end.

Definition wrapover_l {n m} (tg : CospanHyperGraph T n m) :=
  match tg with
  | l -> hg <- r => r +++ l -> hg <- [#]
  end.

Definition wrapunder_r {n m} (tg : CospanHyperGraph T n m) :=
  match tg with
  | l -> hg <- r => [#]-> hg <- r +++ l
  end.

Definition wrapunder_l {n m} (tg : CospanHyperGraph T n m) :=
  match tg with
  | l -> hg <- r => l +++ r -> hg <- [#]
  end.

Notation "⌊ chg" := (wrapunder_r chg) (at level 50).
Notation "⌈ chg" := (wrapover_r chg) (at level 50).
Notation "chg ⌉" := (wrapover_l chg) (at level 50).
Notation "chg ⌋" := (wrapunder_l chg) (at level 50).

(* Definition internal_edges tg :=
  filter (is_internal tg.1) tg.2. *)

(* Definition external_edges tg :=
  tg.2.1 +++ tg.2.2. *)

(* Definition i_internal_edges tg :=
  enumerate (internal_edges tg). *)

(* Definition i_external_edges tg :=
  enumerate (external_edges tg). *)

(* Definition is_node_input (k : nat) (e : edge) : Prop :=
  e.2 = k.

#[export] Instance is_node_input_dec k e : Decision (is_node_input k e) :=
  decide_rel _ (e.2) k.

Definition is_node_output (k : nat) (e : edge) : Prop :=
  e.1 = k.

#[export] Instance is_node_output_dec k e : Decision (is_node_output k e) :=
  decide_rel _ (e.1) k.

Definition node_input_edges (k : nat) (les : list labedge) : list labedge :=
  filter (is_node_input k ∘ snd) les.

Definition node_output_edges (k : nat) (les : list labedge) : list labedge :=
  filter (is_node_output k ∘ snd) les.



Definition in_arity (es : list edge) (k : nat) :=
  length (filter (is_node_input k) es).

Definition out_arity (es : list edge) (k : nat) :=
  length (filter (is_node_output k) es). *)

(* Definition add_edge (n : positive) (t : T)
  (tg : TensorGraph) : TensorGraph :=
  tg.(inputs) -> (<[n := (t, [], [])]> tg.1) <- tg.(outputs). *)

(* Definition add_vertex_r (n : positive) (v : postiive) (tg : TensorGraph) :=
  mk_cohg () *)

(* Definition add_edge (e : edge)
  (tg : TensorGraph) : TensorGraph :=
  mk_cohg tg.1 (e :: tg.2). *)

(* Definition empty_graph : TensorGraph := mk_cohg ∅ []. *)

(* Definition graph_insize (tg : TensorGraph) : nat := size (inputs tg). *)
(* Definition graph_outsize (tg : TensorGraph) : nat := size (outputs tg). *)


(* Definition sorted_inputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (inputs tg). *)

(* Definition sorted_outputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (outputs tg). *)

Definition vertices (tg : CoHyGraph) : Pset :=
  vertices_hg (tg.(hedges)) ∪
  list_to_set (tg.(inputs) ++ tg.(outputs)).

Lemma elem_of_vertices_hg (hg : HyperGraph T) r :
  r ∈ vertices_hg hg <->
  (exists k flu, hg.(hyperedges) !! k = Some flu /\
      (r ∈ flu.1.2 \/ r ∈ flu.2)) \/
    r ∈ hg.(hypervertices).
Proof.
  unfold vertices_hg.
  rewrite elem_of_union.
  f_equiv.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  setoid_rewrite elem_of_app.
  rewrite exists_pair.
  cbn.
  setoid_rewrite elem_of_map_to_list.
  naive_solver.
Qed.


Lemma elem_of_vertices (tg : CoHyGraph) (r : positive) :
  r ∈ vertices tg <->
    (exists k flu, tg.(hedges).(hyperedges) !! k = Some flu /\
      (r ∈ flu.1.2 \/ r ∈ flu.2)) \/
    r ∈ tg.(hedges).(hypervertices) \/
    r ∈@{list _} tg.(inputs) \/ r ∈@{list _} tg.(outputs).
Proof.
  unfold vertices.
  rewrite elem_of_union, elem_of_list_to_set, elem_of_vertices_hg,
    elem_of_app.
  tauto.
Qed.


Definition relabel_graph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_cohg (relabel_hg f tg.(hedges)) (vmap f tg.(inputs)) (vmap f tg.(outputs)).

Definition reindex_graph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_cohg (reindex_hg f tg.(hedges)) tg.(inputs) tg.(outputs).

Inductive isomorphic : relation CoHyGraph :=
  | iso_relabel_reindex tg fedge fvert
    `{Hfe : !Inj eq eq fedge} `{Hfv : !Inj eq eq fvert} :
    isomorphic tg (relabel_graph fedge (reindex_graph fvert tg)).


Lemma isomorphic_exists (tg tg' : CoHyGraph) :
  isomorphic tg tg' <-> exists fedge fvert,
    Inj eq eq fedge /\ Inj eq eq fvert /\
    tg' = relabel_graph fedge (reindex_graph fvert tg).
Proof.
  split; [now intros []; eauto|].
  firstorder (subst; econstructor; eauto).
Qed.

Import TESyntax.

Section HyperGraphFacts.

Implicit Types (hg : HyperGraph T).

Lemma relabel_hg_ext_strong f g (hg : HyperGraph T) :
  (forall i, i ∈ vertices_hg hg -> f i = g i) ->
  relabel_hg f hg = relabel_hg g hg.
Proof.
  intros Hfg.
  apply hg_ext; cbn.
  - apply map_fmap_ext.
    intros i x Hix.
    apply relabel_abs_ext_strong; intros r Hr.
    apply Hfg.
    rewrite elem_of_vertices_hg.
    rewrite elem_of_app in Hr.
    left; eauto.
  - apply set_map_ext_L.
    intros i Hi; apply Hfg.
    unfold vertices_hg.
    now apply elem_of_union_r.
Qed.

Lemma relabel_hg_ext f g (hg : HyperGraph T) :
  (forall i, f i = g i) ->
  relabel_hg f hg = relabel_hg g hg.
Proof.
  intros; apply relabel_hg_ext_strong; auto.
Qed.

Lemma relabel_hg_id hg : relabel_hg id hg = hg.
Proof.
  apply hg_ext; cbn.
  - erewrite map_fmap_ext; [apply map_fmap_id|].
    intros; now apply relabel_abs_id.
  - apply set_map_id_L.
Qed.

Lemma relabel_hg_id_strong f hg :
  (forall i, i ∈ vertices_hg hg -> f i = i) ->
  relabel_hg f hg = hg.
Proof.
  intros ->%(relabel_hg_ext_strong f id hg).
  apply relabel_hg_id.
Qed.

Lemma relabel_hg_id' f hg :
  (forall i, f i = i) ->
  relabel_hg f hg = hg.
Proof.
  auto using relabel_hg_id_strong.
Qed.

Lemma relabel_hg_compose f g hg :
  relabel_hg g (relabel_hg f hg) =
  relabel_hg (g ∘ f) hg.
Proof.
  apply hg_ext; [|cbn; now rewrite set_map_compose_L].
  cbn.
  rewrite <- map_fmap_compose.
  apply map_fmap_ext.
  intros; apply relabel_abs_compose.
Qed.


Lemma reindex_hg_ext_strong f g hg :
  (forall i tabs, hg.(hyperedges) !! i = Some tabs -> f i = g i) ->
  reindex_hg f hg = reindex_hg g hg.
Proof.
  intros Hfg.
  apply hg_ext; [cbn|done].
  now apply kmap_ext.
Qed.

Lemma reindex_hg_ext f g hg :
  (forall i, f i = g i) -> reindex_hg f hg = reindex_hg g hg.
Proof.
  auto using reindex_hg_ext_strong.
Qed.

Lemma reindex_hg_id hg : reindex_hg id hg = hg.
Proof.
  apply hg_ext; cbn; [cbn|done].
  apply kmap_id.
Qed.

Lemma reindex_hg_id_strong f hg :
  (forall i tabs, hg.(hyperedges) !! i = Some tabs -> f i = i) ->
  reindex_hg f hg = hg.
Proof.
  intros ->%(reindex_hg_ext_strong f id hg).
  apply reindex_hg_id.
Qed.

Lemma reindex_hg_id' f hg :
  (forall i, f i = i) ->
  reindex_hg f hg = hg.
Proof.
  auto using reindex_hg_id_strong.
Qed.


Lemma reindex_hg_compose_strong' f g `{Hf : !Inj eq eq f} hg :
  (forall i j, i ∈ dom hg.(hyperedges) -> j ∈ dom hg.(hyperedges) ->
    g (f i) = g (f j) -> f i = f j) ->
  reindex_hg g (reindex_hg f hg) =
  reindex_hg (g ∘ f) hg.
Proof.
  intros Hg.
  apply hg_ext; [cbn|done].
  apply map_eq; intros i.
  apply option_eq; intros [[t low] up].
  rewrite lookup_kmap_Some_full_gen_dom by
    now rewrite dom_kmap', set_Forall2_map; exact Hg.
  rewrite lookup_kmap_Some_full_gen_dom by now intros ? ? ? ? ?%Hg%Hf.
  setoid_rewrite (lookup_kmap_Some _).
  naive_solver.
Qed.

Lemma reindex_hg_compose f g `{!Inj eq eq f, !Inj eq eq g} hg :
  reindex_hg g (reindex_hg f hg) =
  reindex_hg (g ∘ f) hg.
Proof.
  apply hg_ext; [cbn|done..].
  apply map_eq; intros i.
  apply option_eq; intros [[t low] up].
  rewrite 2 (lookup_kmap_Some _).
  setoid_rewrite (lookup_kmap_Some _).
  naive_solver.
Qed.


Lemma reindex_relabel_hg fvert fedge hg :
  reindex_hg fvert (relabel_hg fedge hg) =
  relabel_hg fedge (reindex_hg fvert hg).
Proof.
  apply hg_ext; [|done..].
  cbn.
  apply kmap_fmap'.
Qed.

Lemma vertices_relabel_hg f hg :
  vertices_hg (relabel_hg f hg) = set_map f (vertices_hg hg).
Proof.
  unfold vertices_hg.
  cbn.
  rewrite set_map_union_L, set_map_list_to_set_L.
  f_equiv.
  rewrite map_to_list_fmap, list_bind_fmap, list_fmap_bind.
  unfold compose; cbn.
  f_equal.
  apply list_bind_ext; [|done].
  intros [k [[idx low] up]].
  cbn.
  now rewrite fmap_app.
Qed.

Lemma vertices_reindex_hg f `{Hfint : !Inj eq eq f} hg :
  vertices_hg (reindex_hg f hg) = vertices_hg hg.
Proof.
  unfold vertices_hg.
  cbn.
  f_equal.
  unfold kmap.
  unfold_leibniz.
  apply list_to_set_perm.
  rewrite map_to_list_to_map by now
    rewrite fsts_prod_map, (NoDup_fmap _); apply NoDup_fst_map_to_list.
  rewrite list_fmap_bind.
  reflexivity.
Qed.

End HyperGraphFacts.

Lemma relabel_graph_ext_strong f g tg :
  (forall i, i ∈ vertices tg -> f i = g i) ->
  relabel_graph f tg = relabel_graph g tg.
Proof.
  intros Hfg.
  apply cohg_ext; cbn.
  - apply relabel_hg_ext_strong.
    intros i Hi.
    apply Hfg.
    unfold vertices.
    now apply elem_of_union_l.
  - apply vec_to_list_inj2; rewrite 2 vec_to_list_map.
    apply list_fmap_ext; intros _ i Hi%elem_of_list_lookup_2.
    apply Hfg, elem_of_union_r, elem_of_list_to_set, elem_of_app.
    now left.
  - apply vec_to_list_inj2; rewrite 2 vec_to_list_map.
    apply list_fmap_ext; intros _ i Hi%elem_of_list_lookup_2.
    apply Hfg, elem_of_union_r, elem_of_list_to_set, elem_of_app.
    now right.
Qed.

Lemma relabel_graph_ext f g tg :
  (forall i, f i = g i) -> relabel_graph f tg = relabel_graph g tg.
Proof.
  auto using relabel_graph_ext_strong.
Qed.

Lemma relabel_graph_id tg : relabel_graph id tg = tg.
Proof.
  apply cohg_ext; cbn; [|apply Vector.map_id..].
  apply relabel_hg_id.
Qed.

Lemma relabel_graph_id_strong f tg :
  (forall i, i ∈ vertices tg -> f i = i) ->
  relabel_graph f tg = tg.
Proof.
  intros ->%(relabel_graph_ext_strong f id tg).
  apply relabel_graph_id.
Qed.

Lemma relabel_graph_id' f tg :
  (forall i, f i = i) ->
  relabel_graph f tg = tg.
Proof.
  auto using relabel_graph_id_strong.
Qed.

Lemma relabel_graph_compose f g tg :
  relabel_graph g (relabel_graph f tg) =
  relabel_graph (g ∘ f) tg.
Proof.
  apply cohg_ext; [|cbn; now rewrite Vector.map_map..].
  apply relabel_hg_compose.
Qed.


Lemma reindex_graph_ext_strong f g tg :
  (forall i tabs, tg.(hedges).(hyperedges) !! i = Some tabs -> f i = g i) ->
  reindex_graph f tg = reindex_graph g tg.
Proof.
  intros Hfg.
  apply cohg_ext; [cbn|done..].
  now apply reindex_hg_ext_strong.
Qed.

Lemma reindex_graph_ext f g tg :
  (forall i, f i = g i) -> reindex_graph f tg = reindex_graph g tg.
Proof.
  auto using reindex_graph_ext_strong.
Qed.

Lemma reindex_graph_id tg : reindex_graph id tg = tg.
Proof.
  apply cohg_ext; cbn; [cbn|done..].
  apply reindex_hg_id.
Qed.

Lemma reindex_graph_id_strong f tg :
  (forall i tabs, tg.(hedges).(hyperedges) !! i = Some tabs -> f i = i) ->
  reindex_graph f tg = tg.
Proof.
  intros ->%(reindex_graph_ext_strong f id tg).
  apply reindex_graph_id.
Qed.

Lemma reindex_graph_id' f tg :
  (forall i, f i = i) ->
  reindex_graph f tg = tg.
Proof.
  auto using reindex_graph_id_strong.
Qed.


Lemma reindex_graph_compose_strong' f g `{Hf : !Inj eq eq f} tg :
  (forall i j, i ∈ dom tg.(hedges).(hyperedges) ->
    j ∈ dom tg.(hedges).(hyperedges) ->
    g (f i) = g (f j) -> f i = f j) ->
  reindex_graph g (reindex_graph f tg) =
  reindex_graph (g ∘ f) tg.
Proof.
  intros Hg.
  apply cohg_ext; [cbn|done..].
  now apply reindex_hg_compose_strong'.
Qed.

Lemma reindex_graph_compose f g `{!Inj eq eq f, !Inj eq eq g} tg :
  reindex_graph g (reindex_graph f tg) =
  reindex_graph (g ∘ f) tg.
Proof.
  apply cohg_ext; [cbn|done..].
  now apply reindex_hg_compose.
Qed.


Lemma reindex_relabel_graph fvert fedge tg :
  reindex_graph fvert (relabel_graph fedge tg) =
  relabel_graph fedge (reindex_graph fvert tg).
Proof.
  apply cohg_ext; [|done..].
  cbn.
  apply reindex_relabel_hg.
Qed.

Lemma vertices_relabel_graph f (tg : CoHyGraph) :
  vertices (relabel_graph f tg) = set_map f (vertices tg).
Proof.
  unfold vertices.
  cbn.
  rewrite vertices_relabel_hg.
  rewrite set_map_union_L, set_map_list_to_set_L.
  rewrite fmap_app, 2 vec_to_list_map.
  reflexivity.
Qed.

Lemma vertices_reindex_graph f `{Hfint : !Inj eq eq f} (tg : CoHyGraph) :
  vertices (reindex_graph f tg) = vertices tg.
Proof.
  unfold vertices.
  cbn.
  now rewrite (vertices_reindex_hg _).
Qed.

Lemma isomorphic_of_partial_inj tg fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(hedges).(hyperedges) !! i = Some tabs ->
    tg.(hedges).(hyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  isomorphic tg (relabel_graph fedge (reindex_graph fvert tg)).
Proof.
  intros Hfe Hfv.
  apply isomorphic_exists.
  destruct (partial_injection_extension' (vertices tg) _ Hfe)
    as (fe' & Hfe' & Hfe'_fe).
  pose proof (partial_injection_extension' (dom tg.(hedges).(hyperedges):>Pset) fvert)
    as Hfv'.
  tspecialize Hfv'. 1:{
    intros i j [tabs Htabs]%elem_of_dom [tabs' Htabs']%elem_of_dom.
    eauto.
  }
  destruct Hfv' as (fv' & Hfv' & Hfv'_fv).
  exists fe', fv'.
  split; [easy|].
  split; [easy|].
  symmetry.
  erewrite relabel_graph_ext_strong; [f_equal; apply reindex_graph_ext_strong|].
  - intros; apply Hfv'_fv, elem_of_dom; eauto.
  - rewrite (vertices_reindex_graph _).
    apply Hfe'_fe.
Qed.

Lemma isomorphic_of_partial_inj' tg tg' fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(hedges).(hyperedges) !! i = Some tabs ->
    tg.(hedges).(hyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_graph fedge (reindex_graph fvert tg) ->
  isomorphic tg tg'.
Proof.
  intros ? ? ->.
  eauto using isomorphic_of_partial_inj.
Qed.

Lemma isomorphic_of_partial_inj_dom' tg tg' fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j, i ∈@{Pset} dom tg.(hedges).(hyperedges) ->
    j ∈@{Pset} dom tg.(hedges).(hyperedges) ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_graph fedge (reindex_graph fvert tg) ->
  isomorphic tg tg'.
Proof.
  intros ? Hv ->.
  apply isomorphic_of_partial_inj; [easy|].
  intros ? ? ? ? ? ?; apply Hv; apply elem_of_dom; eauto.
Qed.


Lemma isomorphic_refl tg : isomorphic tg tg.
Proof.
  apply isomorphic_exists.
  exists id, id.
  split; [apply _|].
  split; [apply _|].
  now rewrite reindex_graph_id, relabel_graph_id.
Qed.

Lemma isomorphic_symm tg tg' : isomorphic tg tg' -> isomorphic tg' tg.
Proof.
  rewrite isomorphic_exists.
  intros (fedge & fvert & Hfe & Hfv & ->).
  apply (isomorphic_of_partial_inj_dom' _ _
    (invfun fedge (elements (vertices tg)))
    (invfun fvert (elements (dom tg.(hedges).(hyperedges))))).
  - intros fi fj.
    rewrite vertices_relabel_graph, (vertices_reindex_graph _).
    intros (i & -> & Hi)%elem_of_map (j & -> & Hj)%elem_of_map.
    rewrite 2 invfun_linv by
      first [intros ? ? ? ?; apply Hfe|now apply elem_of_elements].
    now intros ->.
  - intros fi fj.
    cbn.
    rewrite dom_fmap, dom_kmap'.
    intros (i & -> & Hi)%elem_of_map (j & -> & Hj)%elem_of_map.
    rewrite 2 invfun_linv by
      first [intros ? ? ? ?; apply Hfv|now apply elem_of_elements].
    now intros ->.
  - rewrite reindex_relabel_graph.
    rewrite (reindex_graph_compose_strong' _ _ _) by
      now intros ? ? ? ?; rewrite 2 invfun_linv by
        first [intros ????; apply Hfv|now apply elem_of_elements];
        intros ->.
    rewrite relabel_graph_compose.
    rewrite reindex_graph_id_strong. 2:{
      intros i _ Hi%elem_of_dom_2%elem_of_elements.
      now apply invfun_linv; try (intros ????; apply Hfv).
    }
    symmetry.
    apply relabel_graph_id_strong.
    intros i Hi%elem_of_elements.
    now apply invfun_linv; try (intros ????; apply Hfe).
Qed.

Lemma isomorphic_trans tg tg' tg'' :
  isomorphic tg tg' -> isomorphic tg' tg'' ->
  isomorphic tg tg''.
Proof.
  rewrite 3 isomorphic_exists.
  intros (fe & fv & Hfe & Hfv & ->)
    (fe' & fv' & Hfe' & Hfv' & ->).
  exists (fe' ∘ fe), (fv' ∘ fv).
  split; [apply _|].
  split; [apply _|].
  rewrite reindex_relabel_graph.
  rewrite (reindex_graph_compose _ _ _).
  now rewrite relabel_graph_compose.
Qed.

(* TODO: Show that if [f : A -> A] injective and [g : A -> A] any
  (maybe different types by inhab? like invfun),
  there is a *category theory word* [h : A -> A] such that
  (f ∘ g ≡ h ∘ f) *)

Lemma relabel_graph_isomorphic f `{Hf : !Inj eq eq f} tg tg' :
  isomorphic tg tg' ->
  isomorphic (relabel_graph f tg) (relabel_graph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%isomorphic_exists.
  (* apply isomorphic_symm. *)
  eapply (isomorphic_of_partial_inj_dom' _ _
    (f ∘ fe ∘ invfun f (elements (vertices tg))) fv).
  - rewrite vertices_relabel_graph.
    intros fi fj (i & -> & Hi%elem_of_elements)%elem_of_map
      (j & -> & Hj%elem_of_elements)%elem_of_map.
    cbn.
    rewrite 2invfun_linv by first [intros ????;apply Hf|easy].
    now intros ->%(inj f)%(inj fe).
  - cbn.
    intros ????; apply Hfv.
  - rewrite relabel_graph_compose, <- 2 reindex_relabel_graph.
    f_equal.
    rewrite relabel_graph_compose.
    apply relabel_graph_ext_strong.
    intros i Hi%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.


Lemma reindex_graph_isomorphic f `{Hf : !Inj eq eq f} tg tg' :
  isomorphic tg tg' ->
  isomorphic (reindex_graph f tg) (reindex_graph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%isomorphic_exists.
  (* apply isomorphic_symm. *)
  eapply (isomorphic_of_partial_inj_dom' _ _
    fe (f ∘ fv ∘ invfun f (elements (dom (hedges tg).(hyperedges))))).
  - cbn.
    intros ????; apply Hfe.
  - cbn.
    rewrite dom_kmap_L'.
    intros fi fj (i & -> & Hi%elem_of_elements)%elem_of_map
      (j & -> & Hj%elem_of_elements)%elem_of_map.
    cbn.
    rewrite 2 invfun_linv by first [intros ????;apply Hf|easy].
    now intros ->%(inj f)%(inj fv).
  - rewrite (reindex_graph_compose_strong' _ _ _). 2:{
      intros i j Hi%elem_of_elements Hj%elem_of_elements.
      cbn.
      rewrite 2 invfun_linv by first [intros ????;apply Hf|easy].
      now intros ->%(inj f)%(inj fv).
    }
    rewrite reindex_relabel_graph.
    f_equal.
    rewrite (reindex_graph_compose _ _ _).
    apply reindex_graph_ext_strong.
    intros i _ Hi%elem_of_dom_2%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.

End CospanHyperGraph.

Add Parametric Relation {T n m} : (CospanHyperGraph T n m) isomorphic
  reflexivity proved by isomorphic_refl
  symmetry proved by isomorphic_symm
  transitivity proved by isomorphic_trans
  as isomorphic_setoid.

Definition stack_graphs_aux {T n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') : CospanHyperGraph T (n + n') (m + m') :=
  cohg.(inputs) +++ cohg'.(inputs) -> cohg.(hedges) ∪ cohg'.(hedges) <-
    cohg.(outputs) +++ cohg'.(outputs).

Definition stack_graphs {T n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') : CospanHyperGraph T (n + n') (m + m') :=
  stack_graphs_aux
    (relabel_graph (bcons false) (reindex_graph (bcons false) cohg))
    (relabel_graph (bcons true) (reindex_graph (bcons true) cohg')).


(* Definition vremove {A n} (i : fin n) : vec A n -> vec A (pred n) :=
  (* match i in fin n return vec A n -> vec A (pred n) with
  | 0%fin => Vector.tl
  | FS i =>
    match i with
    | 0%fin => fun v => Vector.hd v ::: Vector.tl (Vector.tl v)
    | FS i => fun v => Vector.hd v ::: vremove (FS i) (Vector.tl v)
    end
  end. *)
  Fin.t_rect (fun n _ => vec A n -> vec A (pred n)) (fun _ => Vector.tl)
  (fun n i => match i with
    | 0%fin => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    | FS i' => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    end) n i. *)

Definition vremove {A n} (i : fin n) : vec A n -> vec A (pred n) :=
  Fin.t_rect (fun n _ => vec A n -> vec A (pred n)) (fun _ => Vector.tl)
  (fun n i => match i with
    | 0%fin => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    | FS i' => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    end) n i.

Lemma vec_to_list_vremove {A n} (i : fin n) (v : vec A n) :
  vec_to_list (vremove i v) = delete (i:>nat) (v:>list A).
Proof.
  unfold vremove.
  revert v; induction i.
  - cbn.
    now apply vec_S_inv.
  - apply vec_S_inv.
    intros x v.
    cbn.
    destruct i.
    + cbn.
      f_equal.
      now destruct v using vec_S_inv.
    + cbn.
      f_equal.
      apply IHi.
Qed.

Definition hg_add_vertices {T} (hg : HyperGraph T) (vs : Pset) : HyperGraph T :=
  mk_hg hg.(hyperedges) (vs ∪ hg.(hypervertices)).

Lemma vertices_hg_add_vertices {T} (hg : HyperGraph T) vs :
  vertices_hg (hg_add_vertices hg vs) = vertices_hg hg ∪ vs.
Proof.
  unfold vertices_hg; cbn.
  rewrite <- (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

(* TODO: Rewrite with a new Vector.remove function returning a [vec A (pred n)] *)
Definition add_top_loop {T n m} (cohg : CospanHyperGraph T (S n) (S m)) : CospanHyperGraph T n m :=
  relabel_graph {[Vector.hd cohg.(outputs) := Vector.hd cohg.(inputs)]} (
  Vector.tl cohg.(inputs) -> 
    hg_add_vertices cohg.(hedges) {[Vector.hd cohg.(inputs)]} 
      <- Vector.tl cohg.(outputs)).

Fixpoint add_top_loops {T n m o} : forall (cohg : CospanHyperGraph T (n + m) (n + o)),
  CospanHyperGraph T m o :=
  match n with
  | 0 => fun cohg => cohg
  | S n =>
    fun cohg => add_top_loops (add_top_loop cohg)
  end.



Definition swapped_stack_graphs_aux {T n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') : CospanHyperGraph T (n' + n) (m + m') :=
  cohg'.(inputs) +++ cohg.(inputs) -> cohg.(hedges) ∪ cohg'.(hedges) <-
    cohg.(outputs) +++ cohg'.(outputs).

Definition swapped_stack_graphs {T n m n' m'} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T n' m') : CospanHyperGraph T (n' + n) (m + m') :=
  swapped_stack_graphs_aux
    (relabel_graph (bcons false) (reindex_graph (bcons false) cohg))
    (relabel_graph (bcons true) (reindex_graph (bcons true) cohg')).

Definition compose_graphs_alt {T n m o} (cohg : CospanHyperGraph T n m)
  (cohg' : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
  add_top_loops (swapped_stack_graphs cohg cohg').


Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with CospanHyperGraph.
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_graph : graph_scope. *)

(* Open Scope graph_scope.
Open Scope nat. *)

