Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp Aux_pos.
Require Export HyperGraph.
Require Import TESyntax.


(* Basic definitions and structural operations on TensorGraphs *)


(* A graph with h(yper)edges labeled by elements of [T] *)
Record CospanHyperGraph {T : Type} {n m : nat} := mk_cohg {
  hedges : HyperGraph T;
  inputs : vec positive n;
  outputs : vec positive m;
}.
#[global] Arguments CospanHyperGraph T : clear implicits.
#[global] Arguments mk_cohg {_} {_ _} (_ _ _) : assert.

Declare Scope cohg_scope.
Delimit Scope cohg_scope with cohg.
Bind Scope cohg_scope with CospanHyperGraph.

Notation " ins -> hedges <- outs " := (mk_cohg hedges ins outs) : cohg_scope.

Open Scope cohg_scope.

Definition CospanHyperGraph2triple {T} {n m : nat} (tg : CospanHyperGraph T n m) :=
  (tg.(hedges), (tg.(inputs), tg.(outputs))).

#[global] Coercion CospanHyperGraph2triple : CospanHyperGraph >-> prod.

#[global] Coercion hedges : CospanHyperGraph >-> HyperGraph.

Lemma cohg_ext {T} {n m} (tg tg' : CospanHyperGraph T n m) :
  tg.(hedges) = tg'.(hedges) ->
  tg.(inputs) = tg'.(inputs) ->
  tg.(outputs) = tg'.(outputs) ->
  tg = tg'.
Proof.
  destruct tg, tg'; cbn; congruence.
Qed.

Lemma cohg_ext' {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  inputs cohg = inputs cohg' ->
  outputs cohg = outputs cohg' ->
  hyperedges cohg = hyperedges cohg' ->
  hypervertices cohg = hypervertices cohg' ->
  cohg = cohg'.
Proof.
  auto using cohg_ext, hg_ext.
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

Definition cohg_eq `{Equiv T} : relation CoHyGraph :=
  fun cohg cohg' =>
  cohg.(inputs) = cohg'.(inputs) /\
  cohg.(outputs) = cohg'.(outputs) /\
  cohg.(hedges) ≡ cohg'.(hedges).

#[export] Instance cohg_eq_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence cohg_eq.
Proof.
  apply rel_intersection_equiv, rel_intersection_equiv;
  refine (rel_preimage_equiv _ _ _).
Qed.

Lemma mk_cohg_eq `{Equiv T} cohg cohg' :
  cohg.(inputs) = cohg'.(inputs) ->
  cohg.(outputs) = cohg'.(outputs) ->
  cohg.(hedges) ≡ cohg'.(hedges) ->
  cohg_eq cohg cohg'.
Proof.
  easy.
Qed.



(* Lemma relabel_graph_cohg_eq f tg tg' : cohg_eq tg tg' ->
  cohg_eq (relabel_graph f ) *)


End CospanHyperGraph.


Add Parametric Morphism `{Equiv T} {n m} f :
  (@relabel_graph T n m f) with signature cohg_eq ==> cohg_eq as
  relabel_graph_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & Hhedge).
  apply mk_cohg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T} {n m} f :
  (@reindex_graph T n m f) with signature cohg_eq ==> cohg_eq as
  reindex_graph_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & Hhedge).
  apply mk_cohg_eq; [done..|].
  cbn.
  now f_equiv.
Qed.




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

Definition add_top_loop' {T n m} (cohg : CospanHyperGraph T (S n) (S m)) : CospanHyperGraph T n m :=
  relabel_graph {[Vector.hd cohg.(outputs) := Vector.hd cohg.(inputs)]} (
  Vector.tl cohg.(inputs) ->
    hg_add_vertices cohg.(hedges) ({[Vector.hd cohg.(inputs)]} ∖ vertices_hg cohg)
      <- Vector.tl cohg.(outputs)).

Fixpoint add_top_loops' {T n m o} : forall (cohg : CospanHyperGraph T (n + m) (n + o)),
  CospanHyperGraph T m o :=
  match n with
  | 0 => fun cohg => cohg
  | S n =>
    fun cohg => add_top_loops' (add_top_loop' cohg)
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


(* Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with CospanHyperGraph. *)
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_graph : graph_scope. *)

(* Open Scope graph_scope.
Open Scope nat. *)


Definition id_graph {T} (n : nat) : CospanHyperGraph T n n :=
  vmap (Pos.of_succ_nat) (vseq 0 n) -> ∅ <- vmap (Pos.of_succ_nat) (vseq 0 n).

Definition swap_graph {T} n m : CospanHyperGraph T (n + m) (m + n) :=
  vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq n m) -> ∅
    <- vmap (Pos.of_succ_nat) (vseq n m +++ vseq 0 n).

Definition cup_graph {T} n : CospanHyperGraph T 0 (n + n) :=
  [#] -> ∅ <- vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq 0 n).

Definition cap_graph {T} n : CospanHyperGraph T (n + n) 0 :=
  vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq 0 n) -> ∅ <- [#].

Definition graph_of_tensor {T} (t : T) (n m : nat) : CospanHyperGraph T n m :=
  vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n) ->
    {[xH := (t, (bcons false ∘ Pos.of_succ_nat) <$> (seq 0 n),
      (bcons true ∘ Pos.of_succ_nat) <$> (seq 0 m))]} <-
  vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m).


Add Parametric Morphism `{Equiv T, Equivalence T equiv} :
  (@hg_add_vertices T) with signature equiv ==> eq ==> equiv as
  hg_add_vertices_equiv.
Proof.
  intros hg hg' (He & Hv) vs.
  split; [|now cbn; f_equal].
  apply He.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_graphs_aux T n m n' m') with signature
  cohg_eq ==> cohg_eq ==> cohg_eq as stack_graphs_aux_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hins1 & Houts1 & He1)
    cohg2 cohg2' (Hins2 & Houts2 & He2).
  apply mk_cohg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_graphs T n m n' m') with signature
  cohg_eq ==> cohg_eq ==> cohg_eq as stack_graphs_cohg_eq.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold stack_graphs.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m} :
  (@add_top_loop T n m) with signature
  cohg_eq ==> cohg_eq as add_top_loop_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & Hes).
  apply mk_cohg_eq; [cbn; repeat first [assumption|f_equal]..|].
  cbn.
  rewrite <- Hins, <- Houts.
  apply (relabel_hg_proper _ _ _).
  f_equiv; done.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@add_top_loops T n m o) with signature
  cohg_eq ==> cohg_eq as add_top_loops_cohg_eq.
Proof.
  induction n; [done|].
  intros cohg cohg' Heq.
  cbn.
  apply IHn.
  now f_equiv.
Qed.


Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_graphs_aux T n m n' m') with signature
  cohg_eq ==> cohg_eq ==> cohg_eq as swapped_stack_graphs_aux_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hins1 & Houts1 & He1)
    cohg2 cohg2' (Hins2 & Houts2 & He2).
  apply mk_cohg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_graphs T n m n' m') with signature
  cohg_eq ==> cohg_eq ==> cohg_eq as swapped_stack_graphs_cohg_eq.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold swapped_stack_graphs.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@compose_graphs_alt T n m o) with signature
  cohg_eq ==> cohg_eq ==> cohg_eq as compose_graphs_alt_cohg_eq.
Proof.
  unfold compose_graphs_alt.
  intros; now do 2 f_equiv.
Qed.



Definition abs_vertices {T} (hg : (HyperEdge T)) : Pset :=
  list_to_set (hg.1.2 ++ hg.2).

Definition referenced_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  Pset :=
  list_to_set (cohg.(inputs) ++ cohg.(outputs))
    ∪ list_to_set (map_to_list cohg.(hedges).(hyperedges)
     ≫= λ k_flu, k_flu.2.1.2 ++ k_flu.2.2).

Definition isolated_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  Pset :=
  cohg.(hedges).(hypervertices)
    ∖ referenced_vertices cohg.

Lemma referenced_vertices_decomp {T n m} (cohg : CospanHyperGraph T n m) :
  referenced_vertices cohg =
  list_to_set (inputs cohg ++ outputs cohg) ∪
    referenced_vertices_hg cohg.
Proof.
  done.
Qed.

Lemma vertices_decomp {T n m} (cohg : CospanHyperGraph T n m) :
  vertices cohg = isolated_vertices cohg ∪ referenced_vertices cohg.
Proof.
  unfold vertices, isolated_vertices.
  rewrite difference_union_L.
  unfold vertices_hg, referenced_vertices.
  apply set_eq.
  intros ?.
  rewrite 4 elem_of_union; tauto.
Qed.

Lemma isolated_referenced_disjoint {T n m} (cohg : CospanHyperGraph T n m) :
  isolated_vertices cohg ## referenced_vertices cohg.
Proof.
  unfold isolated_vertices.
  now apply disjoint_difference_l1.
Qed.

Definition set_verts {T n m} (cohg : CospanHyperGraph T n m)
  (vs : Pset) : CospanHyperGraph T n m :=
  mk_cohg (mk_hg cohg.(hedges).(hyperedges) vs) cohg.(inputs) cohg.(outputs).

Definition norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  CospanHyperGraph T n m := set_verts cohg (isolated_vertices cohg).

Lemma referenced_vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  referenced_vertices (norm_verts cohg) = referenced_vertices cohg.
Proof.
  reflexivity.
Qed.

Lemma isolated_vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  isolated_vertices (norm_verts cohg) = isolated_vertices cohg.
Proof.
  unfold isolated_vertices.
  cbn.
  unfold isolated_vertices.
  rewrite referenced_vertices_norm_verts.
  apply difference_twice_L.
Qed.


Lemma vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  vertices (norm_verts cohg) = vertices cohg.
Proof.
  now rewrite 2 vertices_decomp,
    isolated_vertices_norm_verts, referenced_vertices_norm_verts.
Qed.


Lemma graph_of_tensor_cohg_eq `{Equiv T} (t t' : T) n m : t ≡ t' ->
  cohg_eq (graph_of_tensor t n m) (graph_of_tensor t' n m).
Proof.
  intros Ht.
  apply mk_cohg_eq; [done..|].
  cbn.
  split; [|done].
  rewrite 2 hyperedges_singleton.
  rewrite <- insert_empty.
  apply insert_proper; [|apply map_empty_equiv_eq; done].
  split; [split;[|done]|done].
  apply Ht.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@vertices T n m)
  with signature cohg_eq ==> eq as vertices_cohg_eq.
Proof.
  intros cohg cohg'.
  intros Heq.
  unfold vertices.
  f_equal; [now apply (vertices_hg_equiv _ _), Heq|].
  now rewrite Heq.1, Heq.2.1.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@referenced_vertices T n m)
  with signature cohg_eq ==> eq as referenced_vertices_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & [Heq Hverts]).
  unfold referenced_vertices.
  rewrite <- Hins, Houts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L (_++_)).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@isolated_vertices T n m)
  with signature cohg_eq ==> eq as isolated_vertices_cohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold isolated_vertices.
  f_equal; [|now rewrite Heq].
  apply Heq.2.2.2.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@set_verts T n m)
  with signature cohg_eq ==> eq ==> cohg_eq as set_verts_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & [Heq Hverts]) vs.
  apply mk_cohg_eq; [done..|].
  split; [done|].
  done.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@norm_verts T n m)
  with signature cohg_eq ==> cohg_eq as norm_verts_cohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold norm_verts.
  now apply set_verts_cohg_eq, isolated_vertices_cohg_eq_Proper.
Qed.

Lemma norm_verts_idemp {T n m} (cohg : CospanHyperGraph T n m) :
  norm_verts (norm_verts cohg) = norm_verts cohg.
Proof.
  unfold norm_verts at 1 3.
  now rewrite isolated_vertices_norm_verts.
Qed.


Definition cohg_vert_eq {T} {n m} (cohg cohg' : CospanHyperGraph T n m) :=
  norm_verts cohg = norm_verts cohg'.

#[export] Instance cohg_vert_equiv {T n m} : Equivalence (@cohg_vert_eq T n m) :=
  rel_preimage_equiv norm_verts _ _.

Notation "cohg '≡ᵥ' cohg'" := (cohg_vert_eq cohg%cohg cohg'%cohg)
  (at level 70) : cohg_scope.

Notation "cohg '≡ₕ' cohg'" := (cohg_eq cohg%cohg cohg'%cohg)
  (at level 70) : cohg_scope.



Lemma norm_verts_vert_eq {T n m} (cohg : CospanHyperGraph T n m) :
  norm_verts cohg ≡ᵥ cohg.
Proof.
  apply norm_verts_idemp.
Qed.

Lemma cohg_vert_eq_alt {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ᵥ cohg' <->
  inputs cohg = inputs cohg' /\
  outputs cohg = outputs cohg' /\
  hyperedges cohg = cohg' /\
  isolated_vertices cohg = isolated_vertices cohg'.
Proof.
  destruct cohg, cohg'; cbn.
  unfold cohg_vert_eq.
  unfold norm_verts, set_verts.
  cbn.
  naive_solver congruence.
Qed.


(* FIXME: Move *)
Lemma cohg_eq_trans `{Equiv T, Transitive T equiv} {n m} :
  Transitive (@cohg_eq T n m _).
Proof.
  apply rel_intersection_trans, rel_intersection_trans;
  refine (rel_preimage_trans _ _ _).
  apply rel_intersection_trans;
  refine (rel_preimage_trans _ _ _).
  intros m1 m2 m3 H12 H23 i.
  specialize (H12 i).
  specialize (H23 i).
  hnf in H12, H23 |- *.
  etransitivity; eauto.
Qed.
Lemma cohg_eq_symm `{Equiv T, Symmetric T equiv} {n m} :
  Symmetric (@cohg_eq T n m _).
Proof.
  apply rel_intersection_symm, rel_intersection_symm;
  refine (rel_preimage_symm _ _ _).
  apply rel_intersection_symm;
  refine (rel_preimage_symm _ _ _).
  intros m1 m2 H12 i.
  specialize (H12 i).
  hnf in H12 |- *.
  now symmetry.
Qed.
Lemma cohg_eq_refl `{Equiv T, Reflexive T equiv} {n m} :
  Reflexive (@cohg_eq T n m _).
Proof.
  apply rel_intersection_refl, rel_intersection_refl;
  refine (rel_preimage_refl _ _ _).
  apply rel_intersection_refl;
  refine (rel_preimage_refl _ _ _).
  intros m1 i.
  hnf.
  reflexivity.
Qed.


#[export] Instance CospanHyperGraph_equiv `{Equiv T} {n m} :
  Equiv (CospanHyperGraph T n m) :=
  rtc (cohg_eq ∪ cohg_vert_eq).

#[export] Instance CospanHyperGraph_equivalence `{Equiv T, Symmetric T equiv} {n m} :
  Equivalence (≡@{CospanHyperGraph T n m}).
Proof.
  apply rtc_equivalence.
  apply rel_union_symm, _.
  now apply cohg_eq_symm.
Qed.

#[export] Instance CospanHyperGraph_refl `{Equiv T} {n m} :
  Reflexive (≡@{CospanHyperGraph T n m}).
Proof.
  apply _.
Qed.

#[export] Instance CospanHyperGraph_trans `{Equiv T} {n m} :
  Transitive (≡@{CospanHyperGraph T n m}).
Proof.
  apply _.
Qed.

#[export] Instance cohg_eq_subrelation_equiv `{Equiv T} {n m} :
  subrelation (@cohg_eq T n m _) equiv.
Proof.
  apply _.
Qed.

#[export] Instance cohg_vert_eq_subrelation_equiv `{Equiv T} {n m} :
  subrelation (@cohg_vert_eq T n m) equiv.
Proof.
  apply _.
Qed.

#[export] Typeclasses Opaque CospanHyperGraph_equiv.

(* Definition cohg_equiv_alt_defn `{Equiv T} {n m} (cohg cohg' : CospanHyperGraph T n m) :=
  cohg_eq (norm_verts cohg) (norm_verts cohg').

#[export] Instance cohg_equiv_alt_defn_equiv `{Equiv T, Equivalence T equiv} {n m} :
  Equivalence (@cohg_equiv_alt_defn T _ n m) :=
  rel_preimage_equiv norm_verts _ _. *)

Lemma set_verts_id {T n m} (cohg : CospanHyperGraph T n m) :
  set_verts cohg (hypervertices cohg) = cohg.
Proof.
  now destruct cohg as [[]].
Qed.

Lemma referenced_vertices_set_verts {T n m} (cohg : CospanHyperGraph T n m) vs :
  referenced_vertices (set_verts cohg vs) = referenced_vertices cohg.
Proof.
  done.
Qed.

Lemma cohg_vert_eq_cohg_eq_commute `{Equiv T} {n m} :
  rel_compose cohg_vert_eq (@cohg_eq T n m _) ⊆
  rel_compose cohg_eq cohg_vert_eq.
Proof.
  apply relation_subseteq_iff.
  intros cohg cohg'' (cohg' & Hveq & Heq).
  apply cohg_vert_eq_alt in Hveq.
  exists (set_verts cohg'' (hypervertices cohg)). (* (mk_cohg (mk_hg (cohg'') (hypervertices cohg))
    (inputs cohg'') (outputs cohg'')). *)
  split.
  - apply mk_cohg_eq; cbn.
    + rewrite Hveq.1.
      apply Heq.
    + rewrite Hveq.2.1.
      apply Heq.
    + split; [cbn; rewrite Hveq.2.2.1; apply Heq|].
      done.
  - apply cohg_vert_eq_alt.
    split_and!; [done..|].
    cbn.
    unfold isolated_vertices; cbn.
    symmetry.
    rewrite <- Heq.2.2.2.
    rewrite referenced_vertices_set_verts.
    erewrite <- referenced_vertices_cohg_eq by apply Heq.
    symmetry.
    unfold referenced_vertices.
    etransitivity; [|apply Hveq.2.2.2].
    rewrite <- Hveq.1, <- Hveq.2.1, <- Hveq.2.2.1.
    done.
Qed.


Definition struct_isomorphic {T n m} (cohg cohg' : CospanHyperGraph T n m) :=
  isomorphic (norm_verts cohg) (norm_verts cohg').

Lemma referenced_vertices_relabel_graph {T n m} f (cohg : CospanHyperGraph T n m) :
  referenced_vertices (relabel_graph f cohg) =
  set_map f (referenced_vertices cohg).
Proof.
  unfold referenced_vertices.
  cbn.
  rewrite 2 vec_to_list_map, <- fmap_app.
  rewrite set_map_union_L, 2 set_map_list_to_set_L.
  f_equal.
  rewrite map_to_list_fmap.
  rewrite list_fmap_bind, list_bind_fmap.
  f_equal.
  apply list_bind_ext; [|done].
  intros [? [[]]]; now rewrite fmap_app.
Qed.


Lemma isolated_vertices_relabel_graph {T n m} f `{Hf : !Inj eq eq f}
  (cohg : CospanHyperGraph T n m) :
  isolated_vertices (relabel_graph f cohg) =
  set_map f (isolated_vertices cohg).
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_relabel_graph.
  cbn.
  now rewrite (set_map_difference_L _).
Qed.

Lemma norm_verts_relabel_graph {T n m} f `{Hf : !Inj eq eq f}
  (cohg : CospanHyperGraph T n m) :
  norm_verts (relabel_graph f cohg) = relabel_graph f (norm_verts cohg).
Proof.
  unfold norm_verts.
  rewrite (isolated_vertices_relabel_graph _).
  done.
Qed.

Lemma referenced_vertices_reindex_graph {T n m}
  f `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T n m) :
  referenced_vertices (reindex_graph f cohg) =
  referenced_vertices cohg.
Proof.
  unfold referenced_vertices.
  cbn.
  f_equal.
  rewrite (map_to_list_kmap _).
  rewrite list_fmap_bind.
  done.
Qed.


Lemma isolated_vertices_reindex_graph {T n m} f `{Hf : !Inj eq eq f}
  (cohg : CospanHyperGraph T n m) :
  isolated_vertices (reindex_graph f cohg) =
  isolated_vertices cohg.
Proof.
  unfold isolated_vertices.
  rewrite (referenced_vertices_reindex_graph _).
  done.
Qed.

Lemma norm_verts_reindex_graph {T n m} f `{Hf : !Inj eq eq f}
  (cohg : CospanHyperGraph T n m) :
  norm_verts (reindex_graph f cohg) = reindex_graph f (norm_verts cohg).
Proof.
  unfold norm_verts.
  rewrite (isolated_vertices_reindex_graph _).
  done.
Qed.




Lemma norm_verts_isomorphic {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  isomorphic cohg cohg' -> isomorphic (norm_verts cohg) (norm_verts cohg').
Proof.
  intros (fv & fe & Hfv & Hfe & ->)%isomorphic_exists.
  rewrite (norm_verts_relabel_graph _),
    (norm_verts_reindex_graph _).
  now constructor.
Qed.

#[export] Instance struct_isomorphic_equivalence {T n m} :
  Equivalence (@struct_isomorphic T n m) := rel_preimage_equiv _ _ _.


Notation "cohg '≡ᵢ' cohg'" := (struct_isomorphic cohg%cohg cohg'%cohg)
  (at level 70) : cohg_scope.

#[export] Instance isomorphic_struct_isomorphic {T n m} :
  subrelation (@isomorphic T n m) struct_isomorphic.
Proof.
  refine norm_verts_isomorphic.
Qed.

#[export] Instance cohg_vert_eq_struct_isomorphic {T n m} :
  subrelation (@cohg_vert_eq T n m) struct_isomorphic.
Proof.
  unfold struct_isomorphic.
  now intros ? ? <-.
Qed.

Lemma struct_isomorphic_alt {T n m} :
  @struct_isomorphic T n m ≡ rtc (cohg_vert_eq ∪ isomorphic).
Proof.
  apply relation_subseteq_antisymm; apply relation_subseteq_iff.
  - intros cohg cohg' Heq.
    transitivity (norm_verts cohg); [apply rtc_once; left; now rewrite norm_verts_vert_eq|].
    transitivity (norm_verts cohg'); [|apply rtc_once; left; now rewrite norm_verts_vert_eq].
    apply rtc_once; right; apply Heq.
  - intros cohg cohg' Heq.
    induction Heq as [|a b c Hab Hbc IH]; [done|].
    rewrite <- IH.
    destruct Hab as [Hab|Hab]; now rewrite Hab.
Qed.

Inductive cohg_syntactic_eq `{Equiv T} {n m} : relation (CospanHyperGraph T n m) :=
  | cohg_syntactic_eq_relabel_reindex cohg cohg' fv fe : Inj eq eq fv -> Inj eq eq fe ->
    cohg_eq (norm_verts cohg) (norm_verts cohg') ->
    cohg_syntactic_eq cohg (relabel_graph fv (reindex_graph fe cohg')).


Notation "cohg '≡ₛ' cohg'" := (cohg_syntactic_eq cohg%cohg cohg'%cohg)
  (at level 70) : cohg_scope.

Lemma cohg_syntactic_eq_exists `{Equiv T} {n m} (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ₛ cohg' <-> exists cohg'' fv fe, Inj eq eq fv /\ Inj eq eq fe /\
    cohg_eq (norm_verts cohg) (norm_verts cohg'') /\
      cohg' = relabel_graph fv (reindex_graph fe cohg'').
Proof.
  split; [|naive_solver eauto using cohg_syntactic_eq].
  intros Heq.
  induction Heq.
  eauto 7.
Qed.

#[export] Instance isomorphic_cohg_syntactic_eq `{Equiv T, Reflexive T equiv} {n m} :
  subrelation (@isomorphic T n m) cohg_syntactic_eq.
Proof.
  intros cohg cohg' (fv & fe & Hfv & Hfe & ->)%isomorphic_exists.
  constructor; [apply _..|].
  apply mk_cohg_eq; [done..|].
  split; [|done].
  intros i; hnf.
  reflexivity.
Qed.

#[export] Instance cohg_eq_cohg_syntactic_eq `{Equiv T} {n m} :
  subrelation (@cohg_eq T n m _) cohg_syntactic_eq.
Proof.
  intros cohg cohg' Heq.
  apply cohg_syntactic_eq_exists.
  exists cohg', id, id.
  do 3 (split; [apply id_inj||now apply norm_verts_cohg_eq|]).
  now rewrite relabel_graph_id, reindex_graph_id.
Qed.

#[export] Instance cohg_vert_eq_cohg_syntactic_eq `{Equiv T, Reflexive T equiv} {n m} :
  subrelation (@cohg_vert_eq T n m) cohg_syntactic_eq.
Proof.
  intros cohg cohg' Heq.
  apply cohg_syntactic_eq_exists.
  exists cohg', id, id.
  do 2 (split; [apply id_inj|]).
  split; [|now rewrite relabel_graph_id, reindex_graph_id].
  rewrite <- Heq.
  apply mk_cohg_eq; [done..|].
  split; [|done].
  intros i; hnf.
  reflexivity.
Qed.

Lemma relabel_graph_cohg_eq_inv_l `{Equiv T} f
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  relabel_graph f cohg ≡ₕ cohg' -> exists cohg'',
    cohg' = relabel_graph f cohg'' /\ cohg ≡ₕ cohg''.
Proof.
  intros Heq.
  exists (mk_cohg (mk_hg (union_with (λ tio tio',
    Some (tio.1.1, tio'.1.2, tio'.2)) (hyperedges cohg') cohg)
    (hypervertices cohg)) (inputs cohg) (outputs cohg)).
  split.
  - apply cohg_ext; [|symmetry; apply Heq..].
    cbn.
    apply hg_ext; [|symmetry; apply Heq].
    cbn.
    apply map_eq.
    intros i.
    specialize (Heq.2.2.1 i) as Hlook.
    cbn in Hlook.
    rewrite lookup_fmap in Hlook.
    rewrite lookup_fmap, lookup_union_with.
    apply option_relation_Forall2 in Hlook.
    destruct ((hyperedges cohg) !! i) as [hi|] eqn:Hhi,
      ((hyperedges cohg') !! i) as [hi'|] eqn:Hhi'; [cbn in *|done..].
    f_equal.
    rewrite (surjective_pairing hi'), (surjective_pairing hi'.1).
    cbn.
    rewrite <- (Hlook.1.2), <- Hlook.2.
    rewrite (surjective_pairing hi), (surjective_pairing hi.1).
    done.
  - apply mk_cohg_eq; [done..|].
    cbn.
    split; [|done].
    cbn.
    intros i.
    rewrite lookup_union_with.
    specialize (Heq.2.2.1 i) as Hlook.
    cbn in Hlook.
    rewrite lookup_fmap in Hlook.
    apply option_relation_Forall2 in Hlook.
    destruct ((hyperedges cohg) !! i) as [hi|] eqn:Hhi,
      ((hyperedges cohg') !! i) as [hi'|] eqn:Hhi'; [cbn in *|done..|constructor].
    f_equiv.
    split; [|done].
    split; [|done].
    cbn.
    rewrite (surjective_pairing hi), (surjective_pairing hi.1) in Hlook.
    apply Hlook.1.1.
Qed.

Lemma reindex_graph_cohg_eq_inv_l `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  reindex_graph f cohg ≡ₕ cohg' -> exists cohg'',
    cohg' = reindex_graph f cohg'' /\ cohg ≡ₕ cohg''.
Proof.
  intros Heq.
  set (finv' := invfun f (elements (dom (hyperedges cohg)))).
  specialize (partial_injection_extension _
    finv' (invfun_inj _ _ (fun _ _ _ _ => Hf _ _))) as Hfinv.
  destruct Hfinv as (finv & Hfinv & Hfinv_eq).

  exists (reindex_graph finv cohg').
  split.
  - rewrite reindex_graph_compose by apply _.
    symmetry.
    apply reindex_graph_id_strong.
    intros fi _ Hfi%elem_of_dom_2.
    cbn.
    specialize Heq.2.2.1 as Hdom%dom_proper.
    cbn in Hdom.
    rewrite dom_kmap' in Hdom.
    rewrite <- Hdom in Hfi.
    apply elem_of_map in Hfi as (i & -> & Hi).
    rewrite Forall_fmap, Forall_forall in Hfinv_eq.
    rewrite Hfinv_eq by now rewrite elem_of_elements.
    unfold finv'.
    now rewrite invfun_linv by now first [intros ? ? ? ? ?%Hf|apply elem_of_elements].
  - apply (reindex_graph_cohg_eq_Proper finv) in Heq.
    rewrite reindex_graph_compose in Heq by apply _.
    rewrite reindex_graph_id_strong in Heq; [done|].
    intros i _ Hi%elem_of_dom_2.
    cbn.
    rewrite Forall_fmap, Forall_forall in Hfinv_eq.
    rewrite Hfinv_eq by now apply elem_of_elements.
    apply invfun_linv, elem_of_elements, Hi.
    now intros ? ? ? ? ?%Hf.
Qed.


Lemma norm_verts_id {T n m} (cohg : CospanHyperGraph T n m) :
  hypervertices cohg = isolated_vertices cohg ->
  norm_verts cohg = cohg.
Proof.
  intros Heq.
  auto using cohg_ext, hg_ext.
Qed.

Lemma relabel_graph_set_verts {T n m} f (cohg : CospanHyperGraph T n m) vs :
  relabel_graph f (set_verts cohg vs) = set_verts (relabel_graph f cohg) (set_map f vs).
Proof.
  done.
Qed.

Lemma hypervertices_subseteq_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  hypervertices cohg ⊆ vertices cohg.
Proof.
  unfold vertices.
  rewrite <- union_subseteq_l.
  unfold vertices_hg.
  rewrite <- union_subseteq_r.
  done.
Qed.

Lemma relabel_graph_norm_verts_inv_l `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  norm_verts cohg = relabel_graph f cohg' -> exists cohg'',
    cohg' = norm_verts cohg'' /\ cohg = relabel_graph f cohg''.
Proof.
  set (finv' := invfun f (elements (vertices cohg'))).
  specialize (partial_injection_extension _
    finv' (invfun_inj f _ (fun _ _ _ _ => Hf _ _))) as Hfinv.
  destruct Hfinv as (finv & Hfinv & Hfinv_eq).
  intros Heq.
  exists (relabel_graph finv cohg).
  split.
  - apply (f_equal (relabel_graph finv)) in Heq.
    rewrite <- (norm_verts_relabel_graph _) in Heq.
    rewrite Heq.
    rewrite relabel_graph_compose.
    symmetry.
    apply relabel_graph_id_strong.
    intros k Hk.
    cbn.
    rewrite Forall_fmap, Forall_forall in Hfinv_eq.
    rewrite Hfinv_eq by now apply elem_of_elements.
    apply invfun_linv, elem_of_elements, Hk.
    now intros ? ? ? ? ?%Hf.
  - symmetry.
    rewrite relabel_graph_compose.
    apply relabel_graph_id_strong.
    intros k Hk.
    cbn.
    rewrite Forall_forall in Hfinv_eq.
    eenough (Hk' : _) by
    now rewrite Hfinv_eq; [apply invfun_rinv, Hk'|apply Hk'].

    apply (f_equal vertices) in Heq.
    rewrite vertices_norm_verts, vertices_relabel_graph in Heq.
    rewrite Heq in Hk.
    set_solver + Hk.
Qed.

Lemma reindex_graph_norm_verts_inv_l `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  norm_verts cohg = reindex_graph f cohg' -> exists cohg'',
    cohg' = norm_verts cohg'' /\ cohg = reindex_graph f cohg''.
Proof.
  set (finv' := invfun f (elements (dom $ hyperedges cohg'))).
  specialize (partial_injection_extension _
    finv' (invfun_inj f _ (fun _ _ _ _ => Hf _ _))) as Hfinv.
  destruct Hfinv as (finv & Hfinv & Hfinv_eq).
  intros Heq.
  exists (reindex_graph finv cohg).
  split.
  - apply (f_equal (reindex_graph finv)) in Heq.
    rewrite <- (norm_verts_reindex_graph _) in Heq.
    rewrite Heq.
    rewrite reindex_graph_compose by apply _.
    symmetry.
    apply reindex_graph_id_strong.
    intros k _ Hk%elem_of_dom_2.
    cbn.
    rewrite Forall_fmap, Forall_forall in Hfinv_eq.
    rewrite Hfinv_eq by now apply elem_of_elements.
    apply invfun_linv, elem_of_elements, Hk.
    now intros ? ? ? ? ?%Hf.
  - symmetry.
    rewrite reindex_graph_compose by apply _.
    apply reindex_graph_id_strong.
    intros k _ Hk%elem_of_dom_2.
    cbn.
    rewrite Forall_forall in Hfinv_eq.
    eenough (Hk' : _) by
    now rewrite Hfinv_eq; [apply invfun_rinv, Hk'|apply Hk'].

    apply (f_equal (dom ∘ hyperedges ∘ hedges)) in Heq.
    cbn in Heq.
    rewrite Heq in Hk.
    rewrite dom_kmap' in Hk.
    rewrite (fmap_elements (SB:=Pset) _).
    now apply elem_of_elements.
Qed.



Lemma cohg_syntactic_eq_trans `{Equiv T, Transitive T equiv} {n m} :
  Transitive (@cohg_syntactic_eq T _ n m).
Proof.
  intros cohg cohg' cohg'' Heq1 Heq2.
  (* induction Heq2 as [cohg' cohg'' fv2 fe2 Hfv2 Hfe2 Heq2]. *)
  apply cohg_syntactic_eq_exists in Heq2
    as (cohg23 & fv2 & fe2 & Hfv2 & Hfe2 & Hheq2 & Heq2).
  apply cohg_syntactic_eq_exists in Heq1
    as (cohg12 & fv1 & fe1 & Hfv1 & Hfe1 & Hheq1 & Heq1).
  subst cohg' cohg''.

  rewrite (norm_verts_relabel_graph _), (norm_verts_reindex_graph _) in Hheq2.

  apply relabel_graph_cohg_eq_inv_l in Hheq2 as Hheq2'.
  destruct Hheq2' as (cohg12' & Heq12 & Hrel).
  apply (reindex_graph_cohg_eq_inv_l _) in Hrel as Hheq2''.
  destruct Hheq2'' as (cohg12'' & -> & Hrel').

  apply cohg_syntactic_eq_exists.

  apply (relabel_graph_norm_verts_inv_l _) in Heq12 as
    (cohg23' & Heq12%eq_sym & ->).
  apply (reindex_graph_norm_verts_inv_l _) in Heq12 as
    (cohg12' & -> & ->).

  exists cohg12'.
  exists (fv2 ∘ fv1), (fe2 ∘ fe1).
  split; [apply _|].
  split; [apply _|].

  split.
  - eapply cohg_eq_trans; eauto.
  - rewrite <- relabel_graph_compose, <- (reindex_graph_compose _ _).
    rewrite <- (reindex_relabel_graph fe2 fv1).
    done.
Qed.


Lemma cohg_syntactic_eq_alt `{Equiv T, Reflexive T equiv,
  Transitive T equiv} {n m} :
  (@cohg_syntactic_eq T _ n m) ≡ rtc (cohg_eq ∪ isomorphic ∪ cohg_vert_eq).
Proof.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros cohg cohg' Hcohg.
    induction Hcohg as [cohg cohg' fv fe Hfv Hfe Heq].
    rewrite <- (iso_relabel_reindex _ _ _).
    rewrite <- (norm_verts_vert_eq cohg).
    rewrite <- (norm_verts_vert_eq cohg').
    apply (subrel Heq).
  - rewrite <- (rtc_id cohg_syntactic_eq);
    [|intros x; apply isomorphic_cohg_syntactic_eq; reflexivity|
    now apply cohg_syntactic_eq_trans].
    apply rtc_subseteq.
    rewrite 2  rel_union_subseteq.
    split_and!; apply relation_subseteq_iff; apply _.
Qed.

#[export] Instance cohg_syntactic_eq_equivalence `{Equiv T, Equivalence T equiv}
  {n m} : Equivalence (@cohg_syntactic_eq T _ n m).
Proof.
  erewrite Equivalence_equiv_proper by now apply cohg_syntactic_eq_alt.
  apply rtc_equivalence.
  apply _.
Qed.

Lemma cohg_equiv_alt_gen `{Equiv T} {n m} :
  (≡@{CospanHyperGraph T n m}) ≡ rel_compose (rtc cohg_eq) cohg_vert_eq.
Proof.
  unfold CospanHyperGraph_equiv, equiv at 2.
  rewrite rtc_union_commute by apply cohg_vert_eq_cohg_eq_commute.
  f_equiv.
  now rewrite rtc_id by apply _.
Qed.


Lemma cohg_equiv_alt'_gen `{Equiv T} {n m} :
  (≡@{CospanHyperGraph T n m}) ≡ rel_preimage norm_verts (rtc cohg_eq).
Proof.
  apply relation_subseteq_antisymm; [rewrite cohg_equiv_alt_gen|]; apply relation_subseteq_iff.
  - intros cohg cohg'' (cohg' & H12 & H23).
    unfold rel_preimage.
    rewrite <- H23.
    now apply (rtc_proper cohg_eq _ norm_verts norm_verts_cohg_eq_Proper).
  - intros cohg cohg' Heq12.
    unfold rel_preimage in Heq12.
    rewrite <- (norm_verts_vert_eq cohg).
    etransitivity; [|apply (subrel (norm_verts_vert_eq cohg'))].
    eapply rtc_subrelation, Heq12.
    apply _.
Qed.


Lemma cohg_equiv_alt `{Equiv T, Equivalence T equiv} {n m} :
  (≡@{CospanHyperGraph T n m}) ≡ rel_compose cohg_eq cohg_vert_eq.
Proof.
  rewrite cohg_equiv_alt_gen.
  now rewrite rtc_id by apply _.
Qed.

Lemma cohg_equiv_alt' `{Equiv T, Equivalence T equiv} {n m} :
  (≡@{CospanHyperGraph T n m}) ≡ rel_preimage norm_verts cohg_eq.
Proof.
  rewrite cohg_equiv_alt'_gen.
  now rewrite rtc_id by apply _.
Qed.

Lemma cohg_equiv_alt_rel `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ cohg' <-> exists cohg'', cohg ≡ₕ cohg'' /\ cohg'' ≡ᵥ cohg'.
Proof.
  apply (relation_equiv_iff.1 cohg_equiv_alt).
Qed.

Lemma cohg_equiv_alt'_rel `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ cohg' <-> norm_verts cohg ≡ₕ norm_verts cohg'.
Proof.
  apply (relation_equiv_iff.1 cohg_equiv_alt').
Qed.






Lemma proper_cohg_equiv_of_vert_eq_unary `{Equiv T1, Equiv T2} {n1 m1 n2 m2}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (cohg_eq ==> cohg_eq) f ->
  Proper (equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cohg cohg' (cohg'' & Heq%(rtc_proper _ _ _ Hfeq) & Hiso%Hfiso)%(relation_equiv_iff.1 cohg_equiv_alt_gen).
  etransitivity; [|apply (subrel Hiso)].
  eapply rtc_subrelation, Heq.
  apply _.
Qed.

Lemma proper_cohg_equiv_of_vert_eq_binary `{Equiv T1, Equiv T2, Equiv T3,
  HT1 : Reflexive T1 equiv, HT2 : Reflexive T2 equiv}
  {n1 m1 n2 m2 n3 m3}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2 ->
    CospanHyperGraph T3 n3 m3) :
  Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) f ->
  Proper (equiv ==> equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cohg1 cohg1' (cohg1'' & Hiso1 & Heq1)%(relation_equiv_iff.1 cohg_equiv_alt_gen).
  intros cohg2 cohg2' (cohg2'' & Hiso2 & Heq2)%(relation_equiv_iff.1 cohg_equiv_alt_gen).
  transitivity (f cohg1'' cohg2''); [|apply (subrel (Hfiso _ _ Heq1 _ _ Heq2))].
  apply (rtc_subrelation cohg_eq _ _).
  pose proof (@cohg_eq_refl T1 _ _ n1 m1) as Hrefl1.
  pose proof (@cohg_eq_refl T2 _ _ n2 m2) as Hrefl2.
  now apply (rtc_proper2 _ _ _ _ Hfeq).
Qed.

Lemma proper_cohg_equiv_of_vert_eq_binary' `{Equiv T1, Equiv T2, Equiv T3}
  {n1 m1 n2 m2 n3 m3}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2 ->
    CospanHyperGraph T3 n3 m3) :
  Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (cohg_eq ==> eq ==> cohg_eq) f ->
  Proper (eq ==> cohg_eq ==> cohg_eq) f ->
  Proper (equiv ==> equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq1 Hfeq2.
  intros cohg1 cohg1' (cohg1'' & Hiso1 & Heq1)%(relation_equiv_iff.1 cohg_equiv_alt_gen).
  intros cohg2 cohg2' (cohg2'' & Hiso2 & Heq2)%(relation_equiv_iff.1 cohg_equiv_alt_gen).
  transitivity (f cohg1'' cohg2''); [|apply (subrel (Hfiso _ _ Heq1 _ _ Heq2))].
  apply (rtc_subrelation cohg_eq _ _).
  now apply (rtc_proper2' _ _ _ _ Hfeq1 Hfeq2).
Qed.


Lemma struct_isomorphic_alt' {T n m} :
  @struct_isomorphic T n m ≡
    rel_compose cohg_vert_eq (rel_compose isomorphic cohg_vert_eq).
Proof.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros cohg cohg' Heq.
    exists (norm_verts cohg).
    split; [now rewrite norm_verts_vert_eq|].
    exists (norm_verts cohg').
    split; [|now rewrite norm_verts_vert_eq].
    done.
  - apply (rel_compose_subseteq_trans _ _ _ (relation_subseteq_iff.2 _)).
    apply (rel_compose_subseteq_trans _ _ _); now apply (relation_subseteq_iff.2 _).
Qed.



Lemma proper_struct_isomorphic_of_vert_eq_unary {T1 T2} {n1 m1 n2 m2}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (isomorphic ==> isomorphic) f ->
  Proper (struct_isomorphic ==> struct_isomorphic) f.
Proof.
  intros Hfeq Hfiso.
  intros cohg cohg' Heq%Hfiso.
  rewrite <- (norm_verts_vert_eq cohg), <- (norm_verts_vert_eq cohg').
  apply (subrel Heq).
Qed.

Lemma proper_struct_isomorphic_of_vert_eq_binary {T1 T2 T3} {n1 m1 n2 m2 n3 m3}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2 ->
    CospanHyperGraph T3 n3 m3) :
  Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (isomorphic ==> isomorphic ==> isomorphic) f ->
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic) f.
Proof.
  intros Hfeq Hfiso.
  intros cohg1 cohg1' Heq1%Hfiso.
  intros cohg2 cohg2' Heq2%Heq1.
  rewrite <- (norm_verts_vert_eq cohg1), <- (norm_verts_vert_eq cohg2).
  rewrite Heq2.
  now rewrite 2 norm_verts_vert_eq.
Qed.



Lemma proper_cohg_syntactic_eq_of_iso_vert_eq_unary `{Equiv T1, Reflexive T1 equiv,
  Transitive T1 equiv, Equiv T2, Reflexive T2 equiv, Transitive T2 equiv} {n1 m1 n2 m2}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (isomorphic ==> isomorphic) f ->
  Proper (cohg_eq ==> cohg_eq) f ->
  Proper (cohg_syntactic_eq ==> cohg_syntactic_eq) f.
Proof.
  intros Hfveq Hfiso Hfeq.
  pose proof (@Proper_equiv_proper).
  rewrite 2 cohg_syntactic_eq_alt.
  apply rtc_proper.
  apply rel_union_proper, _.
  now apply rel_union_proper.
Qed.

(*
Lemma proper_cohg_syntactic_eq_of_iso_vert_eq_binary `{Equiv T1, Reflexive T1 equiv,
  Transitive T1 equiv, Equiv T2, Reflexive T2 equiv, Transitive T2 equiv} {n1 m1 n2 m2}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (isomorphic ==> isomorphic) f ->
  Proper (cohg_eq ==> cohg_eq) f ->
  Proper (cohg_syntactic_eq ==> cohg_syntactic_eq) f. *)



Lemma referenced_vertices_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  referenced_vertices (stack_graphs cohg cohg') =
  set_map (bcons false) (referenced_vertices cohg) ∪
  set_map (bcons true) (referenced_vertices cohg').
Proof.
  unfold referenced_vertices.
  cbn.
  rewrite 2 set_map_union_L, 4 set_map_list_to_set_L.
  rewrite 2 vec_to_list_app, 4 vec_to_list_map.
  rewrite union_assoc_L, (union_comm_L (list_to_set _ ∪ _)).
  rewrite union_assoc_L, <- union_assoc_L.
  f_equal.
  - rewrite <- list_to_set_app_L. 
    apply list_to_set_perm_L.
    rewrite ! fmap_app.
    solve_Permutation.
  - rewrite <- list_to_set_app_L. 
    rewrite <- 2 kmap_fmap'.
    apply list_to_set_perm_L.
    rewrite map_to_list_disj_union by now apply (kmap_inj2_disjoint bcons).
    rewrite bind_app.
    rewrite 2 (map_to_list_kmap _), 2 map_to_list_fmap, 
      ! list_fmap_bind, ! list_bind_fmap.
    apply eq_reflexivity. 
    f_equal; apply (fun H => list_bind_ext _ _ _ _ H eq_refl);
    intros [? [[]]]; now rewrite fmap_app.
Qed.

Lemma isolated_vertices_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  isolated_vertices (stack_graphs cohg cohg') =
  set_map (bcons false) (isolated_vertices cohg) ∪
  set_map (bcons true) (isolated_vertices cohg').
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_stack_graphs.
  cbn.
  rewrite 2 (set_map_difference_L _).
  generalize (hypervertices cohg) (hypervertices cohg')
    (referenced_vertices cohg) (referenced_vertices cohg').
  set_solver.
Qed.

Lemma referenced_vertices_swapped_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  referenced_vertices (swapped_stack_graphs cohg cohg') =
  set_map (bcons false) (referenced_vertices cohg) ∪
  set_map (bcons true) (referenced_vertices cohg').
Proof.
  unfold referenced_vertices.
  cbn.
  rewrite 2 set_map_union_L, 4 set_map_list_to_set_L.
  rewrite 2 vec_to_list_app, 4 vec_to_list_map.
  rewrite union_assoc_L, (union_comm_L (list_to_set _ ∪ _)).
  rewrite union_assoc_L, <- union_assoc_L.
  f_equal.
  - rewrite <- list_to_set_app_L. 
    apply list_to_set_perm_L.
    rewrite ! fmap_app.
    solve_Permutation.
  - rewrite <- list_to_set_app_L. 
    rewrite <- 2 kmap_fmap'.
    apply list_to_set_perm_L.
    rewrite map_to_list_disj_union by now apply (kmap_inj2_disjoint bcons).
    rewrite bind_app.
    rewrite 2 (map_to_list_kmap _), 2 map_to_list_fmap, 
      ! list_fmap_bind, ! list_bind_fmap.
    apply eq_reflexivity. 
    f_equal; apply (fun H => list_bind_ext _ _ _ _ H eq_refl);
    intros [? [[]]]; now rewrite fmap_app.
Qed.

Lemma isolated_vertices_swapped_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  isolated_vertices (swapped_stack_graphs cohg cohg') =
  set_map (bcons false) (isolated_vertices cohg) ∪
  set_map (bcons true) (isolated_vertices cohg').
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_swapped_stack_graphs.
  cbn.
  rewrite 2 (set_map_difference_L _).
  generalize (hypervertices cohg) (hypervertices cohg')
    (referenced_vertices cohg) (referenced_vertices cohg').
  set_solver.
Qed.

Lemma norm_verts_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  norm_verts (stack_graphs cohg cohg') =
  stack_graphs (norm_verts cohg) (norm_verts cohg').
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  apply isolated_vertices_stack_graphs.
Qed.


Add Parametric Morphism {T n m n' m'} : (@stack_graphs T n m n' m') with signature
  cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq as stack_graphs_vert_eq_mor.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  hnf.
  rewrite 2 norm_verts_stack_graphs.
  now f_equal.
Qed.


Lemma norm_verts_swapped_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  norm_verts (swapped_stack_graphs cohg cohg') =
  swapped_stack_graphs (norm_verts cohg) (norm_verts cohg').
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  apply isolated_vertices_swapped_stack_graphs.
Qed.


Add Parametric Morphism {T n m n' m'} : (@swapped_stack_graphs T n m n' m') with signature
  cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq as swapped_stack_graphs_vert_eq_mor.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  hnf.
  rewrite 2 norm_verts_swapped_stack_graphs.
  now f_equal.
Qed.


Lemma relabel_graph_cohg_vert_eq {T n m} f (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ᵥ cohg' ->
  relabel_graph f cohg ≡ᵥ relabel_graph f cohg'.
Proof.
  intros Heq.
  apply cohg_ext'.
  - cbn.
    f_equal.
    apply (f_equal inputs Heq).
  - cbn.
    f_equal.
    apply (f_equal outputs Heq).
  - cbn.
    f_equal.
    apply (f_equal (hyperedges ∘ hedges) Heq).
  - cbn.
    unfold isolated_vertices.
    rewrite 2 referenced_vertices_relabel_graph.
    rewrite <- referenced_vertices_norm_verts, Heq, referenced_vertices_norm_verts.
    apply set_map_difference_respectful_l_L.
    apply eq_reflexivity.
    rewrite <- referenced_vertices_norm_verts at 1.
    rewrite <- (Heq : _ = _).
    rewrite referenced_vertices_norm_verts.
    apply (f_equal (hypervertices ∘ hedges) Heq).
Qed.

Add Parametric Morphism {T n m} f : (@relabel_graph T n m f) with signature
  cohg_vert_eq ==> cohg_vert_eq as relabel_graph_vert_eq_mor.
Proof.
  intros cohg cohg'.
  apply relabel_graph_cohg_vert_eq.
Qed.

Lemma reindex_graph_cohg_vert_eq {T n m} f `{!Inj eq eq f} (cohg cohg' : CospanHyperGraph T n m) :
  cohg ≡ᵥ cohg' ->
  reindex_graph f cohg ≡ᵥ reindex_graph f cohg'.
Proof.
  intros Heq.
  apply cohg_ext'.
  - cbn.
    apply (f_equal inputs Heq).
  - cbn.
    apply (f_equal outputs Heq).
  - cbn.
    f_equal.
    apply (f_equal (hyperedges ∘ hedges) Heq).
  - cbn.
    rewrite 2 (isolated_vertices_reindex_graph _).
    apply (f_equal (hypervertices ∘ hedges) Heq).
Qed.

Definition all_vertices {T} (H : HyperGraph T) : Pset :=
    map_fold (fun k h s => (list_to_set h.1.2 ∪ list_to_set h.2) ∪ s)
    (H.(hypervertices)) (H.(hyperedges)).

Section Compose.

  Context {T : Type}.

  Definition compose_graphs_aux {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs)
      (tgl.(inputs) ->
        hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set tgr.(inputs) ∖ (vertices_hg tgl ∪ vertices_hg tgr))
          <- tgr.(outputs)).

  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_graphs {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs :=
        propogate_subst (vzip (vmap (bcons false) tgl.(outputs)) (vmap (bcons true) tgr.(inputs))) in
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) ->
      hg_add_vertices (tgl.(hedges) ⊎ tgr.(hedges))
        ((list_to_set (vmap (bcons true) tgr.(inputs)) ∖
          (vertices_hg (reindex_graph (bcons false) (relabel_graph (bcons false) tgl)) ∪
           vertices_hg (reindex_graph (bcons true) (relabel_graph (bcons true) tgr)))))
           <- (vmap (bcons true) tgr.(outputs))).


  Definition compose_graphs_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set (tgr.(inputs)) ∖ (vertices_hg tgl ∪ vertices_hg tgr)) <- tgr.(outputs).

  
  Definition compose_graphs_unsafe' {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) 
      (list_to_set (tgr.(inputs)) ∖ (vertices_hg tgl ∪ vertices_hg tgr ∪ list_to_set (tgl.(inputs) ++ tgr.(outputs)))) <- tgr.(outputs).

Lemma isolated_vertices_alt_vertices {n m} (cohg : CospanHyperGraph T n m) : 
  isolated_vertices cohg = vertices cohg ∖ referenced_vertices cohg.
Proof.
  rewrite vertices_decomp.
  rewrite difference_union_distr_l_L.
  rewrite difference_diag_L.
  unfold isolated_vertices.
  rewrite union_empty_r_L.
  now rewrite difference_twice_L.
Qed.

Lemma cohg_vert_eq_alt_vertices {n m} (cohg cohg' : CospanHyperGraph T n m) : 
  cohg ≡ᵥ cohg' <->
  inputs cohg = inputs cohg' /\
  outputs cohg = outputs cohg' /\
  hyperedges cohg = hyperedges cohg' /\
  vertices cohg = vertices cohg'.
Proof.
  rewrite cohg_vert_eq_alt.
  apply and_iff_from_l; [done|].
  intros Hins _.
  apply and_iff_from_l; [done|].
  intros Houts _.
  apply and_iff_from_l; [done|].
  intros Hhe _.
  split.
  - intros Hisol.
    rewrite 2 vertices_decomp, Hisol.
    f_equal.
    unfold referenced_vertices.
    congruence.
  - rewrite 2 isolated_vertices_alt_vertices.
    intros ->.
    unfold referenced_vertices.
    congruence.
Qed.

Lemma compose_graphs_unsafe'_correct {n m o} 
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : 
  compose_graphs_unsafe' tgl tgr ≡ᵥ compose_graphs_unsafe tgl tgr.
Proof.
  apply cohg_vert_eq_alt_vertices.
  split_and!; [done..|].
  unfold vertices.
  cbn.
  rewrite 2 vertices_hg_add_vertices.
  rewrite <- (difference_difference_l_L (list_to_set tgr.(inputs))).
  rewrite <- (union_assoc_L _), difference_union_L.
  apply union_assoc_L.
Qed.

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
  rewrite Vector.map_ext with (g:=(λ x : _, x)) by apply subst_by_vec_id.
  rewrite Vector.map_id.
  simpl.
  rewrite Vector.map_ext with (g:=(λ x : _, x)) by apply subst_by_vec_id.
  rewrite Vector.map_id.
  simpl.
  rewrite relabel_hg_id' by apply subst_by_vec_id.
  reflexivity.
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



Lemma add_top_loop'_correct {n m}
  (tg : CospanHyperGraph T (S n) (S m)) :
  add_top_loop' tg ≡ᵥ add_top_loop tg.
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  unfold add_top_loop', add_top_loop.
  unfold isolated_vertices.
  rewrite 2 referenced_vertices_relabel_graph.
  cbn -[union difference].
  change (referenced_vertices _) with
    (referenced_vertices (vtl (inputs tg) -> hg_add_vertices tg {[vhd (inputs tg)]} <-
        vtl (outputs tg))).
  apply leibniz_equiv_iff, set_subseteq_antisymm. 1:{
    apply difference_mono; [|done].
    f_equiv.
    apply union_mono_r.
    set_solver.
  }
  apply (subseteq_union_r _ _ _).1.
  rewrite (union_comm _ (_ ∖ _)), difference_union.
  rewrite <- set_map_union.
  f_equiv.
  apply union_subseteq, conj, union_subseteq_l', union_subseteq_r.
  apply singleton_subseteq_l.
  rewrite (difference_singleton_l_case_L (vhd (inputs tg)) (vertices_hg tg)).
  case_decide as Hivert.
  - unfold vertices_hg in Hivert.
    set_solver.
  - apply elem_of_union_l, elem_of_union_l, elem_of_singleton.
    done.
Qed.


Lemma isolated_vertices_add_top_loop {n m} (cohg : CospanHyperGraph T (S n) (S m)) :
  isolated_vertices (add_top_loop cohg) =
  isolated_vertices cohg ∪ ({[(vhd (inputs cohg))]} ∖ referenced_vertices (add_top_loop cohg)).
Proof.
  unfold isolated_vertices, add_top_loop.
  rewrite referenced_vertices_relabel_graph.
  cbn -[difference union].
  unfold_leibniz.
  apply set_subseteq_antisymm.
  - intros fk [(k & -> & Hkih)%elem_of_map Hkr]%elem_of_difference.
    rewrite union_comm_L in Hkih.
    rewrite <- difference_union in Hkih.
    rewrite elem_of_union, elem_of_difference, elem_of_singleton in Hkih.
    destruct Hkih as [[Hkh Hkni] | ->].
    + rewrite fn_lookup_singleton_case in *.
      case_decide as Hok.
      * subst k.
        apply elem_of_union_r, elem_of_difference.
        split; [|done].
        now apply elem_of_singleton.
      * apply elem_of_union_l.
        apply elem_of_difference, (conj Hkh).
        intros Hk.
        apply Hkr.
        apply elem_of_map.
        exists k.
        split; [now rewrite fn_lookup_singleton_ne|].
        clear Hkh Hkr.
        unfold referenced_vertices in Hk.
        rewrite (Vector.eta (inputs cohg)), (Vector.eta (outputs cohg)) in Hk.
        cbn -[union] in *.
        set_solver.
    + rewrite fn_lookup_singleton_r in *.
      apply elem_of_union_r, elem_of_difference.
      split; [|done].
      now apply elem_of_singleton.
  - apply union_subseteq, conj.
    + intros k [Hkh Hkr]%elem_of_difference.
      unfold referenced_vertices in Hkr.
      rewrite (Vector.eta (inputs cohg)), (Vector.eta (outputs cohg)) in Hkr.
      cbn -[union] in *.
      apply elem_of_difference, conj.
      * apply elem_of_map.
        exists k.
        rewrite fn_lookup_singleton_ne by set_solver + Hkr.
        split; [done|].
        now apply elem_of_union_r.
      * intros (k' & -> & Hk')%elem_of_map.
        rewrite fn_lookup_singleton_case in *.
        case_decide as Hok'; [set_solver + Hkr|].
        apply Hkr.
        set_solver +Hk'.
    + rewrite <- subseteq_union_r.
      rewrite union_comm_L, difference_union.
      apply singleton_subseteq_l, elem_of_union_l.
      apply elem_of_map.
      exists (vhd (inputs cohg)).
      rewrite fn_lookup_singleton_r.
      split; [done|].
      now apply elem_of_union_l, elem_of_singleton.
Qed.



Lemma norm_verts_add_top_loop {n m} (cohg : CospanHyperGraph T (S n) (S m)) :
  norm_verts (add_top_loop cohg) = norm_verts (add_top_loop (norm_verts cohg)).
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  rewrite 2 isolated_vertices_add_top_loop.
  rewrite isolated_vertices_norm_verts.
  done.
Qed.

Lemma norm_verts_add_top_loops {n m o} (cohg : CospanHyperGraph T (n + m) (n + o)) :
  norm_verts (add_top_loops cohg) = norm_verts (add_top_loops (norm_verts cohg)).
Proof.
  induction n; [cbn; now rewrite norm_verts_idemp|].
  cbn.
  now rewrite IHn, norm_verts_add_top_loop, <- IHn.
Qed.

#[export] Instance add_top_loop_proper {n m} :
  Proper (@cohg_vert_eq T (S n) (S m) ==> cohg_vert_eq) add_top_loop.
Proof.
  intros cohg cohg' Heq.
  hnf.
  rewrite norm_verts_add_top_loop, Heq, <- norm_verts_add_top_loop.
  done.
Qed.

#[export] Instance add_top_loop'_proper {n m} :
  Proper (@cohg_vert_eq T (S n) (S m) ==> cohg_vert_eq) add_top_loop'.
Proof.
  intros cohg cohg' Heq.
  rewrite 2 add_top_loop'_correct.
  now f_equiv.
Qed.

#[export] Instance add_top_loops_proper {n m o} :
  Proper (@cohg_vert_eq T (n + m) (n + o) ==> cohg_vert_eq) add_top_loops.
Proof.
  intros cohg cohg' Heq.
  hnf.
  rewrite norm_verts_add_top_loops, Heq, <- norm_verts_add_top_loops.
  done.
Qed.

Lemma add_top_loops'_correct {n m o}
  (tg : CospanHyperGraph T (n + m) (n + o)) :
  add_top_loops' tg ≡ᵥ add_top_loops tg.
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  now rewrite add_top_loop'_correct.
Qed.


Lemma add_top_loops_alt_vert_eq {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  add_top_loops tg ≡ᵥ
  relabel_graph (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
    (vsplitr tg.(inputs) ->
      hg_add_vertices tg.(hedges)
      (list_to_set (vsplitl tg.(inputs)) ∖ vertices_hg tg)
      <- vsplitr tg.(outputs)).
Proof.
  rewrite add_top_loops_alt.
  apply relabel_graph_cohg_vert_eq.
  apply cohg_ext'; [done..|].
  cbn.
  unfold isolated_vertices.
  cbn.
  rewrite 2 referenced_vertices_decomp.
  cbn.
  rewrite vertices_hg_decomp.
  rewrite <- 3 difference_difference_l_L, difference_union_L.
  set_solver.
Qed.



Lemma compose_graphs_alt_aux_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  hyperedges tgl ##ₘ hyperedges tgr ->
  add_top_loops (swapped_stack_graphs_aux tgl tgr) ≡ᵥ
    compose_graphs_aux tgl tgr.
Proof.
  intros Hdisj.
  rewrite add_top_loops_alt_vert_eq.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  unfold compose_graphs_aux.
  rewrite vertices_hg_union by done.
  reflexivity.
Qed.

Lemma compose_graphs_alt_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs tgl tgr) ≡ᵥ
    compose_graphs tgl tgr.
Proof.
  rewrite compose_graphs_to_compose_graphs_aux.
  rewrite <- compose_graphs_alt_aux_correct; [rewrite 2 reindex_relabel_graph; done|].
  cbn.
  now apply (kmap_inj2_disjoint _).
Qed.

End Compose.