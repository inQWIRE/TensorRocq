Require Export Aux_relset Aux_pos Syntax.
Require Import SetoidList.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Import HyperGraph.Facts.

(* A hyper edge is an indicator for the edge type and the source and target vertices *)
Notation HyperEdge T := (T * list positive * list positive)%type.

#[export] Instance HyperEdge_equiv `{Equiv T} : Equiv (HyperEdge T) :=
  prod_relation (prod_relation (≡) (=)) (=).

Notation "x → t ← y" := (t, x, y). 

(* A [HyperGraph] representation where edges have a type [T] and the
  graph is represented as a map of positives to [HyperEdge]s
  (edge_data, input_vertices, output_vertices) *)
Record HyperGraph {T} := mk_hg {
  (* The edges of the hypergraph *)
  hyperedges : Pmap (T * list positive * list positive);
  (* Additional vertices of the hypergraph, which are often
    disjoint from the referenced vertices of [hyperedges]
    (in practice, we only care about the subset of [hypervertices]
    not referenced in [hyperedges], but do not enforce disjointness) *)
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

Definition hg_add_vertices {T} (hg : HyperGraph T) (vs : Pset) : HyperGraph T :=
  mk_hg hg.(hyperedges) (vs ∪ hg.(hypervertices)).

Definition referenced_vertices_hg {T} (hg : HyperGraph T) : Pset :=
  list_to_set $ map_to_list hg.(hyperedges)
    ≫= λ k_flu, k_flu.2.1.2 ++ k_flu.2.2.

Definition vertices_hg {T} (hg : HyperGraph T) : Pset :=
  list_to_set (map_to_list (hg.(hyperedges)) ≫=
    λ k_flu : (positive*(T*list _*list _)), (k_flu.2.1.2 ++ k_flu.2.2)) ∪
  hg.(hypervertices).

#[export] Instance hypergraph_union {T} : Union (HyperGraph T) :=
  fun hg hg' =>
    mk_hg (hg.(hyperedges) ∪ hg'.(hyperedges))
      (hg.(hypervertices) ∪ hg'.(hypervertices)).

  Lemma hg_empty_union {T} (H : HyperGraph T) : 
    ∅ ∪ H = H.
  Proof.
    unfold union.
    apply hg_ext.
    - simpl;
      rewrite (map_empty_union (H.(hyperedges))).
      reflexivity.
    - simpl; apply union_empty_l_L.
  Qed.

#[export] Instance hypergraph_disjunion {T} : DisjUnion (HyperGraph T) :=
  fun hg hg' =>
  reindex_hg (bcons false) (relabel_hg (bcons false) hg) ∪
  reindex_hg (bcons true) (relabel_hg (bcons true) hg').

#[export] Instance hypergraph_equiv `{Equiv T} : Equiv (HyperGraph T) :=
  fun hg hg' =>
  hg.(hyperedges) ≡ hg'.(hyperedges) /\
  hg.(hypervertices) = hg'.(hypervertices).

#[export] Instance hypergraph_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence (≡@{HyperGraph T}).
Proof.
  apply rel_intersection_equiv.
  - refine (rel_preimage_equiv hyperedges _ _).
  - refine (rel_preimage_equiv hypervertices _ _).
Qed.


Add Parametric Morphism `{Equiv T} : (@vertices_hg T) with signature
  (≡) ==> eq as vertices_hg_equiv.
Proof.
  intros hg hg' [Heq Hverts].
  unfold vertices_hg.
  rewrite <- Hverts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L (_++_)).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} f : (@relabel_abs T positive positive f) with signature
  (≡) ==> (≡) as relabel_abs_proper.
Proof.
  intros [[t i] o] [[t' i'] o'] [[? ?] ?]; split; [split|]; cbn; now f_equal.
Qed.

Add Parametric Morphism `{Equiv T} f : (@relabel_hg T f) with signature
  (≡) ==> (≡) as relabel_hg_proper.
Proof.
  intros hg hg' [Heq Hverts].
  split; [|cbn; now f_equal].
  cbn.
  apply (map_fmap_proper _ _); [|done].
  apply relabel_abs_proper_Proper.
Qed.

Add Parametric Morphism `{Equiv T} f : (@reindex_hg T f) with signature
  (≡) ==> (≡) as reindex_hg_proper.
Proof.
  intros hg hg' [Heq Hverts].
  split; [|apply Hverts].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T} : (@union (HyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as hypergraph_union_proper.
Proof.
  intros hg1 hg1' Hhg1 hg2 hg2' Hhg2.
  split; [|cbn; f_equal; [apply Hhg1|apply Hhg2]].
  cbn.
  apply union_proper; [apply Hhg1|apply Hhg2].
Qed.


Add Parametric Morphism `{Equiv T} : (@disj_union (HyperGraph T) _) with signature
  (≡) ==> (≡) ==> (≡) as hypergraph_disj_union_proper.
Proof.
  intros hg1 hg1' Hhg1 hg2 hg2' Hhg2.
  split; [|cbn; do 2 f_equal; [apply Hhg1|apply Hhg2]].
  cbn.
  apply union_proper; f_equiv; 
  (apply map_fmap_proper; [apply relabel_abs_proper_Proper|]); 
  [apply Hhg1|apply Hhg2].
Qed.


Lemma hyperedges_singleton {T} k abs :
  hyperedges (T:=T) {[k := abs]} = {[k := abs]}.
Proof.
  done.
Qed.


Import Syntax.


Section HyperGraphFacts.

Context {T : Type}.

Implicit Types (hg : HyperGraph T).

Lemma elem_of_vertices_hg hg r :
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



Lemma vertices_hg_union (hg hg' : HyperGraph T) :
  (hg :> Pmap _) ##ₘ (hg' :> Pmap _) ->
  vertices_hg (hg ∪ hg') =
  vertices_hg hg ∪ vertices_hg hg'.
Proof.
  intros Hdisj.
  apply set_eq.
  intros x.
  rewrite elem_of_union, 3 elem_of_vertices_hg.
  change (hypervertices (_ ∪ _)) with (hypervertices hg ∪ hypervertices hg').
  rewrite elem_of_union.
  setoid_rewrite lookup_union_Some; [|done].
  naive_solver.
Qed.

Lemma vertices_hg_add_vertices (hg : HyperGraph T) vs :
  vertices_hg (hg_add_vertices hg vs) = vertices_hg hg ∪ vs.
Proof.
  unfold vertices_hg; cbn.
  rewrite <- (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

Lemma referenced_vertices_hg_add_vertices (hg : HyperGraph T) vs :
  referenced_vertices_hg (hg_add_vertices hg vs) =
  referenced_vertices_hg hg.
Proof.
  done.
Qed.

Lemma vertices_hg_decomp (hg : HyperGraph T) :
  vertices_hg hg = referenced_vertices_hg hg ∪ hypervertices hg.
Proof.
  done.
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

End HyperGraphFacts.

