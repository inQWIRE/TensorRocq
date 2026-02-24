Require Export Tensor.
Require Export SPHyperGraph.
Require Import TESyntax.

(* FIXME: Move *)


(* Basic definitions and structural operations on TensorGraphs *)




(* A graph with h(yper)edges labeled by elements of [T] *)
Record CospanSPHyperGraph {T : Type} {n m : nat} := mk_cosphg {
  sphedges : SPHyperGraph T;
  spinputs : vec positive n;
  spoutputs : vec positive m;
}.
#[global] Arguments CospanSPHyperGraph T : clear implicits.
#[global] Arguments mk_cosphg {_} {_ _} (_ _ _) : assert.

Declare Scope cosphg_scope.
Delimit Scope cosphg_scope with cosphg.
Bind Scope cosphg_scope with CospanSPHyperGraph.

Notation " ins -> sphedges <- outs " := (mk_cosphg sphedges ins outs) : cosphg_scope.

Open Scope cosphg_scope.

Definition CospanSPHyperGraph2triple {T} {n m : nat} (tg : CospanSPHyperGraph T n m) :=
  (tg.(sphedges), (tg.(spinputs), tg.(spoutputs))).

#[global] Coercion CospanSPHyperGraph2triple : CospanSPHyperGraph >-> prod.

Definition CospanSPHyperGraph2SPHyperGraph {T} {n m} (tg : CospanSPHyperGraph T n m) := tg.(sphedges).
#[global] Coercion CospanSPHyperGraph2SPHyperGraph : CospanSPHyperGraph >-> SPHyperGraph.

Lemma cosphg_ext {T} {n m} (tg tg' : CospanSPHyperGraph T n m) :
  tg.(sphedges) = tg'.(sphedges) ->
  tg.(spinputs) = tg'.(spinputs) ->
  tg.(spoutputs) = tg'.(spoutputs) ->
  tg = tg'.
Proof.
  destruct tg, tg'; cbn; congruence.
Qed.

Section CospanSPHyperGraph.

  Context {T : Type}.
  Context {n m : nat}.

  Let CoHyGraph := (CospanSPHyperGraph T n m).

  Implicit Types csphg : CoHyGraph.
(*
  Definition add_vertex_r (n : positive) (v : positive) (tg : CoHyGraph) : CoHyGraph :=
  tg.(spinputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) =>
        match tipop with
        | (t, ip, op) => (t, ip, v::op)
        end)
      n
      tg.(sphedges))
  <- tg.(spoutputs).

  Definition add_vertex_l {T : Type} {o p} (n : positive) (v : positive) (tg : CospanSPHyperGraph T o p) : CospanSPHyperGraph T o p :=
  tg.(spinputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) =>
        match tipop with
        | (t, ip, op) => (t, v::ip, op)
        end)
      n
      tg.1)
  <- tg.(spoutputs). *)

  (* Definition add_edge {T : Type} {o p} (n : positive) (t : T) (tg : CospanSPHyperGraph T o p) :
  CospanSPHyperGraph T o p :=
    tg.2.1 -> (<[ n := (t, ∅) ]> tg.1) <- tg.2.2. *)

  (* Instance insert_sphg {T: Type} : Insert positive T (SPHyperGraph T) := {
    insert := add_edge
  }. *)

  #[global] Instance empty_cosphg {T : Type} : Empty (CospanSPHyperGraph T 0 0) := {
    empty := Vector.nil -> ∅ <- Vector.nil
  }.

  (* Definition add_input {n m} (p : positive) (tg : CospanSPHyperGraph T n m) : CospanSPHyperGraph T (S n) m :=
  Vector.cons p tg.2.1 -> tg.1 <- tg.2.2.

  Definition add_output {n m} (p : positive) (tg : CospanSPHyperGraph T n m) : CospanSPHyperGraph T n (S m) :=
  tg.2.1 -> tg.1 <- Vector.cons p tg.2.2. *)

  (* Local Open Scope positive.
  Local Open Scope vector_scope.

  Definition example_cosphg : CospanSPHyperGraph positive 0 0 :=
    ([#] -> {[ 1 := (1, [], []); 2:= (2, [], []) ]} <- [#]).

  Compute example_cosphg. *)



(* Definition is_input (tm : gmap nat T) (nm : positive * positive) : Prop :=
  is_key tm (fst nm).

Definition is_output (tm : gmap nat T) (nm : edge) : Prop :=
  is_key tm (snd nm).

Definition is_internal tm (e : edge) :=
  is_key tm (fst e) /\ is_key tm (snd e).

Definition not_internal tm (e : edge) :=
  ~ is_internal tm e. *)
(* 
Definition wrapover_r {n m} (tg : CospanSPHyperGraph T n m) :=
  match tg with
  | l -> sphg <- r => [#] -> sphg <- l +++ r
  end.

Definition wrapover_l {n m} (tg : CospanSPHyperGraph T n m) :=
  match tg with
  | l -> sphg <- r => r +++ l -> sphg <- [#]
  end.

Definition wrapunder_r {n m} (tg : CospanSPHyperGraph T n m) :=
  match tg with
  | l -> sphg <- r => [#]-> sphg <- r +++ l
  end.

Definition wrapunder_l {n m} (tg : CospanSPHyperGraph T n m) :=
  match tg with
  | l -> sphg <- r => l +++ r -> sphg <- [#]
  end.

Notation "⌊ csphg" := (wrapunder_r csphg) (at level 50).
Notation "⌈ csphg" := (wrapover_r csphg) (at level 50).
Notation "csphg ⌉" := (wrapover_l csphg) (at level 50).
Notation "csphg ⌋" := (wrapunder_l csphg) (at level 50). *)

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
  tg.(spinputs) -> (<[n := (t, [], [])]> tg.1) <- tg.(spoutputs). *)

(* Definition add_vertex_r (n : positive) (v : postiive) (tg : TensorGraph) :=
  mk_cosphg () *)

(* Definition add_edge (e : edge)
  (tg : TensorGraph) : TensorGraph :=
  mk_cosphg tg.1 (e :: tg.2). *)

(* Definition empty_spgraph : TensorGraph := mk_cosphg ∅ []. *)

(* Definition graph_insize (tg : TensorGraph) : nat := size (spinputs tg). *)
(* Definition graph_outsize (tg : TensorGraph) : nat := size (spoutputs tg). *)


(* Definition sorted_spinputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (spinputs tg). *)

(* Definition sorted_spoutputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (spoutputs tg). *)

Definition vertices (tg : CoHyGraph) : Pset :=
  vertices_sphg (tg.(sphedges)) ∪
  list_to_set (tg.(spinputs) ++ tg.(spoutputs)).

Lemma elem_of_vertices_sphg (sphg : SPHyperGraph T) r :
  r ∈ vertices_sphg sphg <->
  (exists k flu, sphg.(sphyperedges) !! k = Some flu /\
      r ∈ flu.2) \/
    r ∈ sphg.(sphypervertices).
Proof.
  unfold vertices_sphg.
  rewrite elem_of_union.
  f_equiv.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite exists_pair.
  apply exists_iff; intros k.
  apply exists_iff; intros tv.
  rewrite gmultiset_elem_of_elements, elem_of_map_to_list.
  cbn.
  easy.
Qed.


Lemma elem_of_vertices (tg : CoHyGraph) (r : positive) :
  r ∈ vertices tg <->
    (exists k flu, tg.(sphedges).(sphyperedges) !! k = Some flu /\
      r ∈ flu.2) \/
    r ∈ tg.(sphedges).(sphypervertices) \/
    r ∈@{list _} tg.(spinputs) \/ r ∈@{list _} tg.(spoutputs).
Proof.
  unfold vertices.
  rewrite elem_of_union, elem_of_list_to_set, elem_of_vertices_sphg,
    elem_of_app.
  tauto.
Qed.


Definition relabel_spgraph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_cosphg (relabel_sphg f tg.(sphedges)) (vmap f tg.(spinputs)) (vmap f tg.(spoutputs)).

Definition reindex_spgraph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_cosphg (reindex_sphg f tg.(sphedges)) tg.(spinputs) tg.(spoutputs).

Inductive spisomorphic : relation CoHyGraph :=
  | spiso_relabel_reindex tg fedge fvert
    `{Hfe : !Inj eq eq fedge} `{Hfv : !Inj eq eq fvert} :
    spisomorphic tg (relabel_spgraph fvert (reindex_spgraph fedge tg)).


Lemma spisomorphic_exists (tg tg' : CoHyGraph) :
  spisomorphic tg tg' <-> exists fedge fvert,
    Inj eq eq fedge /\ Inj eq eq fvert /\
    tg' = relabel_spgraph fedge (reindex_spgraph fvert tg).
Proof.
  split; [now intros []; eauto|].
  naive_solver (subst; econstructor; eauto).
Qed.

Import TESyntax.

Section SPHyperGraphFacts.

Implicit Types (sphg : SPHyperGraph T).

Lemma relabel_sphg_ext_strong f g (sphg : SPHyperGraph T) :
  (forall i, i ∈ vertices_sphg sphg -> f i = g i) ->
  relabel_sphg f sphg = relabel_sphg g sphg.
Proof.
  intros Hfg.
  apply sphg_ext; cbn.
  - apply map_fmap_ext.
    intros i (t & v) Hix.
    cbn.
    f_equal.
    apply gmultiset_map_ext; intros r Hr.
    apply Hfg.
    rewrite elem_of_vertices_sphg.
    left; eauto.
  - apply set_map_ext_L.
    intros i Hi; apply Hfg.
    unfold vertices_sphg.
    now apply elem_of_union_r.
Qed.

Lemma relabel_sphg_ext f g (sphg : SPHyperGraph T) :
  (forall i, f i = g i) ->
  relabel_sphg f sphg = relabel_sphg g sphg.
Proof.
  intros; apply relabel_sphg_ext_strong; auto.
Qed.

Lemma relabel_sphg_id sphg : relabel_sphg id sphg = sphg.
Proof.
  apply sphg_ext; cbn.
  - erewrite map_fmap_ext; [apply map_fmap_id|].
    intros _ [] _; f_equal/=.
    now apply gmultiset_map_id.
  - apply set_map_id_L.
Qed.

Lemma relabel_sphg_id_strong f sphg :
  (forall i, i ∈ vertices_sphg sphg -> f i = i) ->
  relabel_sphg f sphg = sphg.
Proof.
  intros ->%(relabel_sphg_ext_strong f id sphg).
  apply relabel_sphg_id.
Qed.

Lemma relabel_sphg_id' f sphg :
  (forall i, f i = i) ->
  relabel_sphg f sphg = sphg.
Proof.
  auto using relabel_sphg_id_strong.
Qed.

Lemma relabel_sphg_compose f g sphg :
  relabel_sphg g (relabel_sphg f sphg) =
  relabel_sphg (g ∘ f) sphg.
Proof.
  apply sphg_ext; [|cbn; now rewrite set_map_compose_L].
  cbn.
  rewrite <- map_fmap_compose.
  apply map_fmap_ext.
  intros _ [] _; f_equal/=; apply gmultiset_map_compose.
Qed.


Lemma reindex_sphg_ext_strong f g sphg :
  (forall i tabs, sphg.(sphyperedges) !! i = Some tabs -> f i = g i) ->
  reindex_sphg f sphg = reindex_sphg g sphg.
Proof.
  intros Hfg.
  apply sphg_ext; [cbn|done].
  now apply kmap_ext.
Qed.

Lemma reindex_sphg_ext f g sphg :
  (forall i, f i = g i) -> reindex_sphg f sphg = reindex_sphg g sphg.
Proof.
  auto using reindex_sphg_ext_strong.
Qed.

Lemma reindex_sphg_id sphg : reindex_sphg id sphg = sphg.
Proof.
  apply sphg_ext; cbn; [cbn|done].
  apply kmap_id.
Qed.

Lemma reindex_sphg_id_strong f sphg :
  (forall i tabs, sphg.(sphyperedges) !! i = Some tabs -> f i = i) ->
  reindex_sphg f sphg = sphg.
Proof.
  intros ->%(reindex_sphg_ext_strong f id sphg).
  apply reindex_sphg_id.
Qed.

Lemma reindex_sphg_id' f sphg :
  (forall i, f i = i) ->
  reindex_sphg f sphg = sphg.
Proof.
  auto using reindex_sphg_id_strong.
Qed.


Lemma reindex_sphg_compose_strong' f g `{Hf : !Inj eq eq f} sphg :
  (forall i j, i ∈ dom sphg.(sphyperedges) -> j ∈ dom sphg.(sphyperedges) ->
    g (f i) = g (f j) -> f i = f j) ->
  reindex_sphg g (reindex_sphg f sphg) =
  reindex_sphg (g ∘ f) sphg.
Proof.
  intros Hg.
  apply sphg_ext; [cbn|done].
  apply map_eq; intros i.
  apply option_eq; intros [t v].
  rewrite lookup_kmap_Some_full_gen_dom by
    now rewrite dom_kmap', set_Forall2_map; exact Hg.
  rewrite lookup_kmap_Some_full_gen_dom by now intros ? ? ? ? ?%Hg%Hf.
  setoid_rewrite (lookup_kmap_Some _).
  naive_solver.
Qed.

Lemma reindex_sphg_compose f g `{!Inj eq eq f, !Inj eq eq g} sphg :
  reindex_sphg g (reindex_sphg f sphg) =
  reindex_sphg (g ∘ f) sphg.
Proof.
  apply sphg_ext; [cbn|done..].
  apply map_eq; intros i.
  apply option_eq; intros [t v].
  rewrite 2 (lookup_kmap_Some _).
  setoid_rewrite (lookup_kmap_Some _).
  naive_solver.
Qed.


Lemma reindex_relabel_sphg fvert fedge sphg :
  reindex_sphg fvert (relabel_sphg fedge sphg) =
  relabel_sphg fedge (reindex_sphg fvert sphg).
Proof.
  apply sphg_ext; [|done..].
  cbn.
  apply kmap_fmap'.
Qed.

Lemma vertices_relabel_sphg f sphg :
  vertices_sphg (relabel_sphg f sphg) = set_map f (vertices_sphg sphg).
Proof.
  unfold vertices_sphg.
  cbn.
  rewrite set_map_union_L, set_map_list_to_set_L.
  f_equiv.
  rewrite map_to_list_fmap, list_bind_fmap, list_fmap_bind.
  unfold compose; cbn.
  apply list_to_set_perm_L.
  apply bind_pointwise_Permutation_strong; [|done].
  intros [k [t v]] _.
  cbn -[elements].
  now rewrite elements_gmultiset_map.
Qed.

Lemma vertices_reindex_sphg f `{Hfint : !Inj eq eq f} sphg :
  vertices_sphg (reindex_sphg f sphg) = vertices_sphg sphg.
Proof.
  unfold vertices_sphg.
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

End SPHyperGraphFacts.

Lemma relabel_spgraph_ext_strong f g tg :
  (forall i, i ∈ vertices tg -> f i = g i) ->
  relabel_spgraph f tg = relabel_spgraph g tg.
Proof.
  intros Hfg.
  apply cosphg_ext; cbn.
  - apply relabel_sphg_ext_strong.
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

Lemma relabel_spgraph_ext f g tg :
  (forall i, f i = g i) -> relabel_spgraph f tg = relabel_spgraph g tg.
Proof.
  auto using relabel_spgraph_ext_strong.
Qed.

Lemma relabel_spgraph_id tg : relabel_spgraph id tg = tg.
Proof.
  apply cosphg_ext; cbn; [|apply Vector.map_id..].
  apply relabel_sphg_id.
Qed.

Lemma relabel_spgraph_id_strong f tg :
  (forall i, i ∈ vertices tg -> f i = i) ->
  relabel_spgraph f tg = tg.
Proof.
  intros ->%(relabel_spgraph_ext_strong f id tg).
  apply relabel_spgraph_id.
Qed.

Lemma relabel_spgraph_id' f tg :
  (forall i, f i = i) ->
  relabel_spgraph f tg = tg.
Proof.
  auto using relabel_spgraph_id_strong.
Qed.

Lemma relabel_spgraph_compose f g tg :
  relabel_spgraph g (relabel_spgraph f tg) =
  relabel_spgraph (g ∘ f) tg.
Proof.
  apply cosphg_ext; [|cbn; now rewrite Vector.map_map..].
  apply relabel_sphg_compose.
Qed.


Lemma reindex_spgraph_ext_strong f g tg :
  (forall i tabs, tg.(sphedges).(sphyperedges) !! i = Some tabs -> f i = g i) ->
  reindex_spgraph f tg = reindex_spgraph g tg.
Proof.
  intros Hfg.
  apply cosphg_ext; [cbn|done..].
  now apply reindex_sphg_ext_strong.
Qed.

Lemma reindex_spgraph_ext f g tg :
  (forall i, f i = g i) -> reindex_spgraph f tg = reindex_spgraph g tg.
Proof.
  auto using reindex_spgraph_ext_strong.
Qed.

Lemma reindex_spgraph_id tg : reindex_spgraph id tg = tg.
Proof.
  apply cosphg_ext; cbn; [cbn|done..].
  apply reindex_sphg_id.
Qed.

Lemma reindex_spgraph_id_strong f tg :
  (forall i tabs, tg.(sphedges).(sphyperedges) !! i = Some tabs -> f i = i) ->
  reindex_spgraph f tg = tg.
Proof.
  intros ->%(reindex_spgraph_ext_strong f id tg).
  apply reindex_spgraph_id.
Qed.

Lemma reindex_spgraph_id' f tg :
  (forall i, f i = i) ->
  reindex_spgraph f tg = tg.
Proof.
  auto using reindex_spgraph_id_strong.
Qed.


Lemma reindex_spgraph_compose_strong' f g `{Hf : !Inj eq eq f} tg :
  (forall i j, i ∈ dom tg.(sphedges).(sphyperedges) ->
    j ∈ dom tg.(sphedges).(sphyperedges) ->
    g (f i) = g (f j) -> f i = f j) ->
  reindex_spgraph g (reindex_spgraph f tg) =
  reindex_spgraph (g ∘ f) tg.
Proof.
  intros Hg.
  apply cosphg_ext; [cbn|done..].
  now apply reindex_sphg_compose_strong'.
Qed.

Lemma reindex_spgraph_compose f g `{!Inj eq eq f, !Inj eq eq g} tg :
  reindex_spgraph g (reindex_spgraph f tg) =
  reindex_spgraph (g ∘ f) tg.
Proof.
  apply cosphg_ext; [cbn|done..].
  now apply reindex_sphg_compose.
Qed.


Lemma reindex_relabel_spgraph fvert fedge tg :
  reindex_spgraph fvert (relabel_spgraph fedge tg) =
  relabel_spgraph fedge (reindex_spgraph fvert tg).
Proof.
  apply cosphg_ext; [|done..].
  cbn.
  apply reindex_relabel_sphg.
Qed.

Lemma vertices_relabel_spgraph f (tg : CoHyGraph) :
  vertices (relabel_spgraph f tg) = set_map f (vertices tg).
Proof.
  unfold vertices.
  cbn.
  rewrite vertices_relabel_sphg.
  rewrite set_map_union_L, set_map_list_to_set_L.
  rewrite fmap_app, 2 vec_to_list_map.
  reflexivity.
Qed.

Lemma vertices_reindex_spgraph f `{Hfint : !Inj eq eq f} (tg : CoHyGraph) :
  vertices (reindex_spgraph f tg) = vertices tg.
Proof.
  unfold vertices.
  cbn.
  now rewrite (vertices_reindex_sphg _).
Qed.

Lemma spisomorphic_of_partial_inj tg fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(sphedges).(sphyperedges) !! i = Some tabs ->
    tg.(sphedges).(sphyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  spisomorphic tg (relabel_spgraph fedge (reindex_spgraph fvert tg)).
Proof.
  intros Hfe Hfv.
  apply spisomorphic_exists.
  destruct (partial_injection_extension' (vertices tg) _ Hfe)
    as (fe' & Hfe' & Hfe'_fe).
  pose proof (partial_injection_extension' (dom tg.(sphedges).(sphyperedges):>Pset) fvert)
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
  erewrite relabel_spgraph_ext_strong; [f_equal; apply reindex_spgraph_ext_strong|].
  - intros; apply Hfv'_fv, elem_of_dom; eauto.
  - rewrite (vertices_reindex_spgraph _).
    apply Hfe'_fe.
Qed.

Lemma spisomorphic_of_partial_inj' tg tg' fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(sphedges).(sphyperedges) !! i = Some tabs ->
    tg.(sphedges).(sphyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_spgraph fedge (reindex_spgraph fvert tg) ->
  spisomorphic tg tg'.
Proof.
  intros ? ? ->.
  eauto using spisomorphic_of_partial_inj.
Qed.

Lemma spisomorphic_of_partial_inj_dom' tg tg' fedge fvert :
  (forall i j, i ∈ vertices tg -> j ∈ vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j, i ∈@{Pset} dom tg.(sphedges).(sphyperedges) ->
    j ∈@{Pset} dom tg.(sphedges).(sphyperedges) ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_spgraph fedge (reindex_spgraph fvert tg) ->
  spisomorphic tg tg'.
Proof.
  intros ? Hv ->.
  apply spisomorphic_of_partial_inj; [easy|].
  intros ? ? ? ? ? ?; apply Hv; apply elem_of_dom; eauto.
Qed.


Lemma spisomorphic_refl tg : spisomorphic tg tg.
Proof.
  apply spisomorphic_exists.
  exists id, id.
  split; [apply _|].
  split; [apply _|].
  now rewrite reindex_spgraph_id, relabel_spgraph_id.
Qed.

Lemma spisomorphic_symm tg tg' : spisomorphic tg tg' -> spisomorphic tg' tg.
Proof.
  rewrite spisomorphic_exists.
  intros (fedge & fvert & Hfe & Hfv & ->).
  apply (spisomorphic_of_partial_inj_dom' _ _
    (invfun fedge (elements (vertices tg)))
    (invfun fvert (elements (dom tg.(sphedges).(sphyperedges))))).
  - intros fi fj.
    rewrite vertices_relabel_spgraph, (vertices_reindex_spgraph _).
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
  - rewrite reindex_relabel_spgraph.
    rewrite (reindex_spgraph_compose_strong' _ _ _) by
      now intros ? ? ? ?; rewrite 2 invfun_linv by
        first [intros ????; apply Hfv|now apply elem_of_elements];
        intros ->.
    rewrite relabel_spgraph_compose.
    rewrite reindex_spgraph_id_strong. 2:{
      intros i _ Hi%elem_of_dom_2%elem_of_elements.
      now apply invfun_linv; try (intros ????; apply Hfv).
    }
    symmetry.
    apply relabel_spgraph_id_strong.
    intros i Hi%elem_of_elements.
    now apply invfun_linv; try (intros ????; apply Hfe).
Qed.

Lemma spisomorphic_trans tg tg' tg'' :
  spisomorphic tg tg' -> spisomorphic tg' tg'' ->
  spisomorphic tg tg''.
Proof.
  rewrite 3 spisomorphic_exists.
  intros (fe & fv & Hfe & Hfv & ->)
    (fe' & fv' & Hfe' & Hfv' & ->).
  exists (fe' ∘ fe), (fv' ∘ fv).
  split; [apply _|].
  split; [apply _|].
  rewrite reindex_relabel_spgraph.
  rewrite (reindex_spgraph_compose _ _ _).
  now rewrite relabel_spgraph_compose.
Qed.

(* TODO: Show that if [f : A -> A] injective and [g : A -> A] any
  (maybe different types by inhab? like invfun),
  there is a *category theory word* [h : A -> A] such that
  (f ∘ g ≡ h ∘ f) *)

Lemma relabel_spgraph_spisomorphic f `{Hf : !Inj eq eq f} tg tg' :
  spisomorphic tg tg' ->
  spisomorphic (relabel_spgraph f tg) (relabel_spgraph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%spisomorphic_exists.
  (* apply spisomorphic_symm. *)
  eapply (spisomorphic_of_partial_inj_dom' _ _
    (f ∘ fe ∘ invfun f (elements (vertices tg))) fv).
  - rewrite vertices_relabel_spgraph.
    intros fi fj (i & -> & Hi%elem_of_elements)%elem_of_map
      (j & -> & Hj%elem_of_elements)%elem_of_map.
    cbn.
    rewrite 2invfun_linv by first [intros ????;apply Hf|easy].
    now intros ->%(inj f)%(inj fe).
  - cbn.
    intros ????; apply Hfv.
  - rewrite relabel_spgraph_compose, <- 2 reindex_relabel_spgraph.
    f_equal.
    rewrite relabel_spgraph_compose.
    apply relabel_spgraph_ext_strong.
    intros i Hi%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.


Lemma reindex_spgraph_spisomorphic f `{Hf : !Inj eq eq f} tg tg' :
  spisomorphic tg tg' ->
  spisomorphic (reindex_spgraph f tg) (reindex_spgraph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%spisomorphic_exists.
  (* apply spisomorphic_symm. *)
  eapply (spisomorphic_of_partial_inj_dom' _ _
    fe (f ∘ fv ∘ invfun f (elements (dom (sphedges tg).(sphyperedges))))).
  - cbn.
    intros ????; apply Hfe.
  - cbn.
    rewrite dom_kmap_L'.
    intros fi fj (i & -> & Hi%elem_of_elements)%elem_of_map
      (j & -> & Hj%elem_of_elements)%elem_of_map.
    cbn.
    rewrite 2 invfun_linv by first [intros ????;apply Hf|easy].
    now intros ->%(inj f)%(inj fv).
  - rewrite (reindex_spgraph_compose_strong' _ _ _). 2:{
      intros i j Hi%elem_of_elements Hj%elem_of_elements.
      cbn.
      rewrite 2 invfun_linv by first [intros ????;apply Hf|easy].
      now intros ->%(inj f)%(inj fv).
    }
    rewrite reindex_relabel_spgraph.
    f_equal.
    rewrite (reindex_spgraph_compose _ _ _).
    apply reindex_spgraph_ext_strong.
    intros i _ Hi%elem_of_dom_2%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.

Definition cosphg_eq `{Equiv T} : relation CoHyGraph :=
  fun cosphg cosphg' =>
  cosphg.(spinputs) = cosphg'.(spinputs) /\
  cosphg.(spoutputs) = cosphg'.(spoutputs) /\
  cosphg.(sphedges) ≡ cosphg'.(sphedges).

#[export] Instance cosphg_eq_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence cosphg_eq.
Proof.
  apply rel_intersection_equiv, rel_intersection_equiv;
  refine (rel_preimage_equiv _ _ _).
Qed.

Lemma mk_cosphg_eq `{Equiv T} cosphg cosphg' :
  cosphg.(spinputs) = cosphg'.(spinputs) ->
  cosphg.(spoutputs) = cosphg'.(spoutputs) ->
  cosphg.(sphedges) ≡ cosphg'.(sphedges) ->
  cosphg_eq cosphg cosphg'.
Proof.
  easy.
Qed.

End CospanSPHyperGraph.


Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m} f :
  (@relabel_spgraph T n m f) with signature cosphg_eq ==> cosphg_eq as
  relabel_spgraph_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & Hhedge).
  apply mk_cosphg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m} f :
  (@reindex_spgraph T n m f) with signature cosphg_eq ==> cosphg_eq as
  reindex_spgraph_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & Hhedge).
  apply mk_cosphg_eq; [done..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Relation {T n m} : (CospanSPHyperGraph T n m) spisomorphic
  reflexivity proved by spisomorphic_refl
  symmetry proved by spisomorphic_symm
  transitivity proved by spisomorphic_trans
  as spisomorphic_setoid.

Definition stack_spgraphs_aux {T n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') : CospanSPHyperGraph T (n + n') (m + m') :=
  cosphg.(spinputs) +++ cosphg'.(spinputs) -> cosphg.(sphedges) ∪ cosphg'.(sphedges) <-
    cosphg.(spoutputs) +++ cosphg'.(spoutputs).

Definition stack_spgraphs {T n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') : CospanSPHyperGraph T (n + n') (m + m') :=
  stack_spgraphs_aux
    (relabel_spgraph (bcons false) (reindex_spgraph (bcons false) cosphg))
    (relabel_spgraph (bcons true) (reindex_spgraph (bcons true) cosphg')).



Definition sphg_add_vertices {T} (sphg : SPHyperGraph T) (vs : Pset) : SPHyperGraph T :=
  mk_sphg sphg.(sphyperedges) (vs ∪ sphg.(sphypervertices)).

Lemma vertices_sphg_add_vertices {T} (sphg : SPHyperGraph T) vs :
  vertices_sphg (sphg_add_vertices sphg vs) = vertices_sphg sphg ∪ vs.
Proof.
  unfold vertices_sphg; cbn.
  rewrite <- (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

(* TODO: Rewrite with a new Vector.remove function returning a [vec A (pred n)] *)
Definition spadd_top_loop {T n m} (cosphg : CospanSPHyperGraph T (S n) (S m)) : CospanSPHyperGraph T n m :=
  relabel_spgraph {[Vector.hd cosphg.(spoutputs) := Vector.hd cosphg.(spinputs)]} (
  Vector.tl cosphg.(spinputs) ->
    sphg_add_vertices cosphg.(sphedges) {[Vector.hd cosphg.(spinputs)]}
      <- Vector.tl cosphg.(spoutputs)).

Fixpoint spadd_top_loops {T n m o} : forall (cosphg : CospanSPHyperGraph T (n + m) (n + o)),
  CospanSPHyperGraph T m o :=
  match n with
  | 0 => fun cosphg => cosphg
  | S n =>
    fun cosphg => spadd_top_loops (spadd_top_loop cosphg)
  end.



Definition swapped_stack_spgraphs_aux {T n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') : CospanSPHyperGraph T (n' + n) (m + m') :=
  cosphg'.(spinputs) +++ cosphg.(spinputs) -> cosphg.(sphedges) ∪ cosphg'.(sphedges) <-
    cosphg.(spoutputs) +++ cosphg'.(spoutputs).

Definition swapped_stack_spgraphs {T n m n' m'} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T n' m') : CospanSPHyperGraph T (n' + n) (m + m') :=
  swapped_stack_spgraphs_aux
    (relabel_spgraph (bcons false) (reindex_spgraph (bcons false) cosphg))
    (relabel_spgraph (bcons true) (reindex_spgraph (bcons true) cosphg')).

Definition compose_spgraphs_alt {T n m o} (cosphg : CospanSPHyperGraph T n m)
  (cosphg' : CospanSPHyperGraph T m o) : CospanSPHyperGraph T n o :=
  spadd_top_loops (swapped_stack_spgraphs cosphg cosphg').


(* Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with CospanSPHyperGraph. *)
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_spgraph : graph_scope. *)

(* Open Scope graph_scope.
Open Scope nat. *)


Definition id_spgraph {T} (n : nat) : CospanSPHyperGraph T n n :=
  vmap (Pos.of_succ_nat) (vseq 0 n) -> ∅ <- vmap (Pos.of_succ_nat) (vseq 0 n).

Definition swap_spgraph {T} n m : CospanSPHyperGraph T (n + m) (m + n) :=
  vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq n m) -> ∅
    <- vmap (Pos.of_succ_nat) (vseq n m +++ vseq 0 n).

Definition cup_spgraph {T} n : CospanSPHyperGraph T 0 (n + n) :=
  [#] -> ∅ <- vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq 0 n).

Definition cap_spgraph {T} n : CospanSPHyperGraph T (n + n) 0 :=
  vmap (Pos.of_succ_nat) (vseq 0 n +++ vseq 0 n) -> ∅ <- [#].

Definition spgraph_of_tensor {T} (t : T) (n m : nat) : CospanSPHyperGraph T n m :=
  vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n) ->
    {[xH := (t, list_to_set_disj ((bcons false ∘ Pos.of_succ_nat <$> seq 0 n)
      ++ (bcons true ∘ Pos.of_succ_nat <$> seq 0 m)))]} <-
  vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m).



Add Parametric Morphism `{Equiv T, Equivalence T equiv} :
  (@sphg_add_vertices T) with signature equiv ==> eq ==> equiv as
  sphg_add_vertices_equiv.
Proof.
  intros sphg sphg' (He & Hv) vs.
  split; [|now cbn; f_equal].
  apply He.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_spgraphs_aux T n m n' m') with signature
  cosphg_eq ==> cosphg_eq ==> cosphg_eq as stack_spgraphs_aux_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' (Hins1 & Houts1 & He1)
    cosphg2 cosphg2' (Hins2 & Houts2 & He2).
  apply mk_cosphg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_spgraphs T n m n' m') with signature
  cosphg_eq ==> cosphg_eq ==> cosphg_eq as stack_spgraphs_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' Heq1 cosphg2 cosphg2' Heq2.
  unfold stack_spgraphs.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m} :
  (@spadd_top_loop T n m) with signature
  cosphg_eq ==> cosphg_eq as spadd_top_loop_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & Hes).
  apply mk_cosphg_eq; [cbn; repeat first [assumption|f_equal]..|].
  cbn.
  rewrite <- Hins, <- Houts.
  apply (relabel_sphg_proper _ _ _).
  f_equiv; done.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@spadd_top_loops T n m o) with signature
  cosphg_eq ==> cosphg_eq as spadd_top_loops_cosphg_eq.
Proof.
  induction n; [done|].
  intros cosphg cosphg' Heq.
  cbn.
  apply IHn.
  now f_equiv.
Qed.


Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_spgraphs_aux T n m n' m') with signature
  cosphg_eq ==> cosphg_eq ==> cosphg_eq as swapped_stack_spgraphs_aux_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' (Hins1 & Houts1 & He1)
    cosphg2 cosphg2' (Hins2 & Houts2 & He2).
  apply mk_cosphg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_spgraphs T n m n' m') with signature
  cosphg_eq ==> cosphg_eq ==> cosphg_eq as swapped_stack_spgraphs_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' Heq1 cosphg2 cosphg2' Heq2.
  unfold swapped_stack_spgraphs.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@compose_spgraphs_alt T n m o) with signature
  cosphg_eq ==> cosphg_eq ==> cosphg_eq as compose_spgraphs_alt_cosphg_eq.
Proof.
  unfold compose_spgraphs_alt.
  intros; now do 2 f_equiv.
Qed.


#[export] Instance CospanSPHyperGraph_equiv `{Equiv T} {n m} :
  Equiv (CospanSPHyperGraph T n m) :=
  rtc (spisomorphic ∪ cosphg_eq).

#[export] Instance CospanSPHyperGraph_equivalence `{Equiv T, Equivalence T equiv} {n m} :
  Equivalence (≡@{CospanSPHyperGraph T n m}).
Proof.
  apply rtc_equivalence.
  apply _.
Qed.

Lemma cosphg_equiv_alt `{Equiv T, Equivalence T equiv} {n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) :
  cosphg ≡ cosphg' <-> exists cosphg'', spisomorphic cosphg cosphg'' /\ cosphg_eq cosphg'' cosphg'.
Proof.
  split; cycle 1.
  - intros (cosphg'' & Hiso & Heq).
    transitivity cosphg'';
    apply rtc_once; [now left|now right].
  - intros Hrtc.
    induction Hrtc as [cosphg|cosphg1 cosphg2 cosphg3 Heq12 Hrtc23 IH]; [now exists cosphg|].
    destruct IH as (cosphg2' & Hiso2 & Heq2'3).
    destruct Heq12 as [Hiso12|Heq12].
    + exists cosphg2'.
      split; [etransitivity; eauto|].
      done.
    + induction Hiso2 as [cosphg2 fv fe Hfe Hfv].
      exists (relabel_spgraph fe (reindex_spgraph fv cosphg1)).
      split; [now constructor|].
      now rewrite Heq12.
Qed.

Lemma proper_cosphg_equiv_of_eq_iso_unary `{Equiv T1, Equiv T2, 
  Equivalence T1 equiv} {n1 m1 n2 m2} 
  (f : CospanSPHyperGraph T1 n1 m1 -> CospanSPHyperGraph T2 n2 m2) : 
  Proper (spisomorphic ==> spisomorphic) f ->
  Proper (cosphg_eq ==> cosphg_eq) f ->
  Proper (equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cosphg cosphg' (cosphg'' & Hiso%Hfiso & Heq%Hfeq)%cosphg_equiv_alt.
  transitivity (f cosphg'');
  apply rtc_once; [now left|now right].
Qed.

Lemma proper_cosphg_equiv_of_eq_iso_binary `{Equiv T1, Equiv T2, Equiv T3,
  Equivalence T1 equiv, Equivalence T2 equiv} {n1 m1 n2 m2 n3 m3} 
  (f : CospanSPHyperGraph T1 n1 m1 -> CospanSPHyperGraph T2 n2 m2 ->
    CospanSPHyperGraph T3 n3 m3) : 
  Proper (spisomorphic ==> spisomorphic ==> spisomorphic) f ->
  Proper (cosphg_eq ==> cosphg_eq ==> cosphg_eq) f ->
  Proper (equiv ==> equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cosphg1 cosphg1' (cosphg1'' & Hiso1 & Heq1)%cosphg_equiv_alt.
  intros cosphg2 cosphg2' (cosphg2'' & Hiso2 & Heq2)%cosphg_equiv_alt.
  transitivity (f cosphg1'' cosphg2'');
  apply rtc_once; [now left; apply Hfiso|now right; apply Hfeq].
Qed.


Definition spreferrenced_vertices {T n m} (cosphg : CospanSPHyperGraph T n m) :
  Pset :=
  list_to_set (cosphg.(spinputs) ++ cosphg.(spoutputs))
    ∪ list_to_set (map_to_list (cosphg.(sphedges).(sphyperedges)) ≫=
    λ k_flu : (positive*(SPHyperEdge T)), (elements k_flu.2.2)).

Definition spisolated_vertices {T n m} (cosphg : CospanSPHyperGraph T n m) :
  Pset :=
  cosphg.(sphedges).(sphypervertices)
    ∖ spreferrenced_vertices cosphg.


Lemma vertices_decomp {T n m} (cosphg : CospanSPHyperGraph T n m) :
  vertices cosphg = spisolated_vertices cosphg ∪ spreferrenced_vertices cosphg.
Proof.
  unfold vertices, spisolated_vertices.
  rewrite difference_union_L.
  unfold vertices_sphg, spreferrenced_vertices.
  apply set_eq.
  intros ?.
  rewrite 4 elem_of_union; tauto.
Qed.

Lemma spisolated_referrenced_disjoint {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spisolated_vertices cosphg ## spreferrenced_vertices cosphg.
Proof.
  unfold spisolated_vertices.
  now apply disjoint_difference_l1.
Qed.

Definition set_spverts {T n m} (cosphg : CospanSPHyperGraph T n m)
  (vs : Pset) : CospanSPHyperGraph T n m :=
  mk_cosphg (mk_sphg cosphg.(sphedges).(sphyperedges) vs) cosphg.(spinputs) cosphg.(spoutputs).

Definition norm_spverts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  CospanSPHyperGraph T n m := set_spverts cosphg (spisolated_vertices cosphg).

Lemma spreferrenced_vertices_norm_spverts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spreferrenced_vertices (norm_spverts cosphg) = spreferrenced_vertices cosphg.
Proof.
  reflexivity.
Qed.

Lemma spisolated_vertices_norm_spverts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spisolated_vertices (norm_spverts cosphg) = spisolated_vertices cosphg.
Proof.
  unfold spisolated_vertices.
  cbn.
  unfold spisolated_vertices.
  rewrite spreferrenced_vertices_norm_spverts.
  apply difference_twice_L.
Qed.


Lemma vertices_norm_spverts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  vertices (norm_spverts cosphg) = vertices cosphg.
Proof.
  now rewrite 2 vertices_decomp,
    spisolated_vertices_norm_spverts, spreferrenced_vertices_norm_spverts.
Qed.



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



Add Parametric Morphism `{Equiv T} {n m} : (@spreferrenced_vertices T n m)
  with signature cosphg_eq ==> eq as spreferrenced_vertices_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & [Heq Hverts]).
  unfold spreferrenced_vertices.
  rewrite <- Hins, Houts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@spisolated_vertices T n m)
  with signature cosphg_eq ==> eq as spisolated_vertices_cosphg_eq.
Proof.
  intros cosphg cosphg' Heq.
  unfold spisolated_vertices.
  f_equal; [|now rewrite Heq].
  apply Heq.2.2.2.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@set_spverts T n m)
  with signature cosphg_eq ==> eq ==> cosphg_eq as set_spverts_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & [Heq Hverts]) vs.
  apply mk_cosphg_eq; [done..|].
  split; [done|].
  done.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@norm_spverts T n m)
  with signature cosphg_eq ==> cosphg_eq as norm_spverts_cosphg_eq.
Proof.
  intros cosphg cosphg' Heq.
  unfold norm_spverts.
  now apply set_spverts_cosphg_eq, spisolated_vertices_cosphg_eq_Proper.
Qed.