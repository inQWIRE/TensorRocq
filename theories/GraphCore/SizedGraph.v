Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp Aux_pos.
Require Export HyperGraph.
Require Import TESyntax.
Require Export TensorGraph.


(* FIXME: REMOVE!!! This is here to make sure N is always defined in lemmas,
  and can't inadvertently refer to the type N of binary naturals *)
Definition N : True := I.

(* Basic definitions and structural operations on sized TensorGraphs *)


(* A graph with h(yper)edges labeled by elements of [T] *)
Record SizedCospanHyperGraph {N T : Type} {n m : nat} := mk_scohg {
  sized_cospan :> CospanHyperGraph T n m;
  sized_map : Pmap N;
}.
#[global] Arguments SizedCospanHyperGraph N T : clear implicits.
#[global] Arguments mk_scohg {_ _} {_ _} (_ _) : assert.

Declare Scope scohg_scope.
Delimit Scope scohg_scope with scohg.
Bind Scope scohg_scope with SizedCospanHyperGraph.

Open Scope scohg_scope.

Lemma scohg_ext {N T} {n m} (tg tg' : SizedCospanHyperGraph N T n m) :
  tg.(sized_cospan) = tg'.(sized_cospan) ->
  tg.(sized_map) = tg'.(sized_map) ->
  tg = tg'.
Proof.
  destruct tg, tg'; cbn; congruence.
Qed.

Lemma cohg_ext' {N T n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  inputs cohg = inputs cohg' ->
  outputs cohg = outputs cohg' ->
  hyperedges cohg = hyperedges cohg' ->
  hypervertices cohg = hypervertices cohg' ->
  sized_map cohg = sized_map cohg' ->
  cohg = cohg'.
Proof.
  auto using scohg_ext, cohg_ext, hg_ext.
Qed.



Section SizedCospanHyperGraph.

Context {N T : Type}.
Context {n m : nat}.

Let CoHyGraph := (SizedCospanHyperGraph N T n m).

Implicit Types tg chg : CoHyGraph.



#[global] Instance empty_cohg {N T : Type} : Empty (SizedCospanHyperGraph N T 0 0) :=
  mk_scohg ∅ ∅.


Definition sized_vertices tg := vertices tg ∪ dom tg.(sized_map).


Definition relabel_sized_graph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_scohg (relabel_graph f tg) (kmap f tg.(sized_map)).

Definition reindex_sized_graph (f : positive -> positive) (tg : CoHyGraph) : CoHyGraph :=
  mk_scohg (reindex_graph f tg) tg.(sized_map).

Inductive sized_isomorphic : relation CoHyGraph :=
  | sized_iso_relabel_reindex tg fedge fvert
    `{Hfe : !Inj eq eq fedge} `{Hfv : !Inj eq eq fvert} :
    sized_isomorphic tg (relabel_sized_graph fedge (reindex_sized_graph fvert tg)).


Lemma sized_isomorphic_exists (tg tg' : CoHyGraph) :
  sized_isomorphic tg tg' <-> exists fedge fvert,
    Inj eq eq fedge /\ Inj eq eq fvert /\
    tg' = relabel_sized_graph fedge (reindex_sized_graph fvert tg).
Proof.
  split; [now intros []; eauto|].
  firstorder (subst; econstructor; eauto).
Qed.



Lemma relabel_sized_graph_ext_strong f g tg :
  (forall i, i ∈ sized_vertices tg -> f i = g i) ->
  relabel_sized_graph f tg = relabel_sized_graph g tg.
Proof.
  intros Hfg.
  apply scohg_ext; cbn.
  - apply relabel_graph_ext_strong.
    set_solver +Hfg.
  - apply kmap_ext.
    intros ? _ ?%elem_of_dom_2.
    apply Hfg; set_solver -Hfg.
Qed.

Lemma relabel_sized_graph_ext f g tg :
  (forall i, f i = g i) -> relabel_sized_graph f tg = relabel_sized_graph g tg.
Proof.
  auto using relabel_sized_graph_ext_strong.
Qed.

Lemma relabel_sized_graph_id tg : relabel_sized_graph id tg = tg.
Proof.
  apply scohg_ext; cbn; [apply relabel_graph_id|].
  apply kmap_id.
Qed.

Lemma relabel_sized_graph_id_strong f tg :
  (forall i, i ∈ sized_vertices tg -> f i = i) ->
  relabel_sized_graph f tg = tg.
Proof.
  intros ->%(relabel_sized_graph_ext_strong f id tg).
  apply relabel_sized_graph_id.
Qed.

Lemma relabel_sized_graph_id' f tg :
  (forall i, f i = i) ->
  relabel_sized_graph f tg = tg.
Proof.
  auto using relabel_sized_graph_id_strong.
Qed.

Lemma relabel_sized_graph_compose_strong' f g `{Hf : !Inj eq eq f} tg :
  (forall i j, i ∈ dom tg.(sized_map) -> j ∈ dom tg.(sized_map) ->
    g (f i) = g (f j) -> f i = f j) ->
  relabel_sized_graph g (relabel_sized_graph f tg) =
  relabel_sized_graph (g ∘ f) tg.
Proof.
  intros Hgf.
  apply scohg_ext; [apply relabel_graph_compose|].
  cbn.
  apply map_eq; intros i.
  apply option_eq; intros k.
  rewrite lookup_kmap_Some_full_gen_dom by
    now rewrite dom_kmap', set_Forall2_map; exact Hgf.
  rewrite lookup_kmap_Some_full_gen_dom by now intros ? ? ? ? ?%Hgf%Hf.
  setoid_rewrite (lookup_kmap_Some _).
  naive_solver.
Qed.

Lemma relabel_sized_graph_compose f g `{Hf : !Inj eq eq f, Hg : !Inj eq eq g} tg :
  relabel_sized_graph g (relabel_sized_graph f tg) =
  relabel_sized_graph (g ∘ f) tg.
Proof.
  apply (relabel_sized_graph_compose_strong' _ _).
  intros ? ? ? ?; apply Hg.
Qed.


Lemma reindex_sized_graph_ext_strong f g tg :
  (forall i tabs, tg.(hedges).(hyperedges) !! i = Some tabs -> f i = g i) ->
  reindex_sized_graph f tg = reindex_sized_graph g tg.
Proof.
  intros Hfg.
  apply scohg_ext; [now apply reindex_graph_ext_strong|done].
Qed.

Lemma reindex_sized_graph_ext f g tg :
  (forall i, f i = g i) -> reindex_sized_graph f tg = reindex_sized_graph g tg.
Proof.
  auto using reindex_sized_graph_ext_strong.
Qed.

Lemma reindex_sized_graph_id tg : reindex_sized_graph id tg = tg.
Proof.
  apply scohg_ext; cbn; [apply reindex_graph_id|].
  done.
Qed.

Lemma reindex_sized_graph_id_strong f tg :
  (forall i tabs, tg.(hedges).(hyperedges) !! i = Some tabs -> f i = i) ->
  reindex_sized_graph f tg = tg.
Proof.
  intros ->%(reindex_sized_graph_ext_strong f id tg).
  apply reindex_sized_graph_id.
Qed.

Lemma reindex_sized_graph_id' f tg :
  (forall i, f i = i) ->
  reindex_sized_graph f tg = tg.
Proof.
  auto using reindex_sized_graph_id_strong.
Qed.


Lemma reindex_sized_graph_compose_strong' f g `{Hf : !Inj eq eq f} tg :
  (forall i j, i ∈ dom tg.(hedges).(hyperedges) ->
    j ∈ dom tg.(hedges).(hyperedges) ->
    g (f i) = g (f j) -> f i = f j) ->
  reindex_sized_graph g (reindex_sized_graph f tg) =
  reindex_sized_graph (g ∘ f) tg.
Proof.
  intros Hg.
  apply scohg_ext; [now apply reindex_graph_compose_strong'|done].
Qed.

Lemma reindex_sized_graph_compose f g `{!Inj eq eq f, !Inj eq eq g} tg :
  reindex_sized_graph g (reindex_sized_graph f tg) =
  reindex_sized_graph (g ∘ f) tg.
Proof.
  apply scohg_ext; [now apply reindex_graph_compose|done].
Qed.


Lemma reindex_relabel_sized_graph fvert fedge tg :
  reindex_sized_graph fvert (relabel_sized_graph fedge tg) =
  relabel_sized_graph fedge (reindex_sized_graph fvert tg).
Proof.
  apply scohg_ext; [|done].
  apply reindex_relabel_graph.
Qed.

Lemma sized_vertices_relabel_sized_graph f (tg : CoHyGraph) :
  sized_vertices (relabel_sized_graph f tg) = set_map f (sized_vertices tg).
Proof.
  unfold sized_vertices.
  cbn.
  rewrite vertices_relabel_graph.
  rewrite dom_kmap_L'.
  now rewrite set_map_union_L.
Qed.

Lemma sized_vertices_reindex_sized_graph f `{Hfint : !Inj eq eq f} (tg : CoHyGraph) :
  sized_vertices (reindex_sized_graph f tg) = sized_vertices tg.
Proof.
  unfold sized_vertices.
  cbn.
  now rewrite (vertices_reindex_graph _).
Qed.

Lemma sized_isomorphic_of_partial_inj tg fedge fvert :
  (forall i j, i ∈ sized_vertices tg -> j ∈ sized_vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(hedges).(hyperedges) !! i = Some tabs ->
    tg.(hedges).(hyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  sized_isomorphic tg (relabel_sized_graph fedge (reindex_sized_graph fvert tg)).
Proof.
  intros Hfe Hfv.
  apply sized_isomorphic_exists.
  destruct (partial_injection_extension' (sized_vertices tg) _ Hfe)
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
  erewrite relabel_sized_graph_ext_strong; [f_equal; apply reindex_sized_graph_ext_strong|].
  - intros; apply Hfv'_fv, elem_of_dom; eauto.
  - rewrite (sized_vertices_reindex_sized_graph _).
    apply Hfe'_fe.
Qed.

Lemma sized_isomorphic_of_partial_inj' tg tg' fedge fvert :
  (forall i j, i ∈ sized_vertices tg -> j ∈ sized_vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j tabs tabs', tg.(hedges).(hyperedges) !! i = Some tabs ->
    tg.(hedges).(hyperedges) !! j = Some tabs' ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_sized_graph fedge (reindex_sized_graph fvert tg) ->
  sized_isomorphic tg tg'.
Proof.
  intros ? ? ->.
  eauto using sized_isomorphic_of_partial_inj.
Qed.

Lemma sized_isomorphic_of_partial_inj_dom' tg tg' fedge fvert :
  (forall i j, i ∈ sized_vertices tg -> j ∈ sized_vertices tg ->
    fedge i = fedge j -> i = j) ->
  (forall i j, i ∈@{Pset} dom tg.(hedges).(hyperedges) ->
    j ∈@{Pset} dom tg.(hedges).(hyperedges) ->
    fvert i = fvert j -> i = j) ->
  tg' = relabel_sized_graph fedge (reindex_sized_graph fvert tg) ->
  sized_isomorphic tg tg'.
Proof.
  intros ? Hv ->.
  apply sized_isomorphic_of_partial_inj; [easy|].
  intros ? ? ? ? ? ?; apply Hv; apply elem_of_dom; eauto.
Qed.


Lemma sized_isomorphic_refl tg : sized_isomorphic tg tg.
Proof.
  apply sized_isomorphic_exists.
  exists id, id.
  split; [apply _|].
  split; [apply _|].
  now rewrite reindex_sized_graph_id, relabel_sized_graph_id.
Qed.

Lemma sized_isomorphic_symm tg tg' : sized_isomorphic tg tg' -> sized_isomorphic tg' tg.
Proof.
  rewrite sized_isomorphic_exists.
  intros (fedge & fvert & Hfe & Hfv & ->).
  apply (sized_isomorphic_of_partial_inj_dom' _ _
    (invfun fedge (elements (sized_vertices tg)))
    (invfun fvert (elements (dom tg.(hedges).(hyperedges))))).
  - intros fi fj.
    rewrite sized_vertices_relabel_sized_graph, (sized_vertices_reindex_sized_graph _).
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
  - rewrite reindex_relabel_sized_graph.
    rewrite (reindex_sized_graph_compose_strong' _ _ _) by
      now intros ? ? ? ?; rewrite 2 invfun_linv by
        first [intros ????; apply Hfv|now apply elem_of_elements];
        intros ->.
    rewrite (relabel_sized_graph_compose_strong' _ _ _) by
      now intros ? ? ? ?; rewrite 2 invfun_linv by
        first [intros ????; apply Hfe|now apply elem_of_elements, elem_of_union_r];
        intros ->.
    rewrite reindex_sized_graph_id_strong. 2:{
      intros i _ Hi%elem_of_dom_2%elem_of_elements.
      now apply invfun_linv; try (intros ????; apply Hfv).
    }
    symmetry.
    apply relabel_sized_graph_id_strong.
    intros i Hi%elem_of_elements.
    now apply invfun_linv; try (intros ????; apply Hfe).
Qed.

Lemma sized_isomorphic_trans tg tg' tg'' :
  sized_isomorphic tg tg' -> sized_isomorphic tg' tg'' ->
  sized_isomorphic tg tg''.
Proof.
  rewrite 3 sized_isomorphic_exists.
  intros (fe & fv & Hfe & Hfv & ->)
    (fe' & fv' & Hfe' & Hfv' & ->).
  exists (fe' ∘ fe), (fv' ∘ fv).
  split; [apply _|].
  split; [apply _|].
  rewrite reindex_relabel_sized_graph.
  rewrite (reindex_sized_graph_compose _ _ _).
  now rewrite relabel_sized_graph_compose.
Qed.

(* TODO: Show that if [f : A -> A] injective and [g : A -> A] any
  (maybe different types by inhab? like invfun),
  there is a *category theory word* [h : A -> A] such that
  (f ∘ g ≡ h ∘ f) *)

Lemma relabel_sized_graph_sized_isomorphic f `{Hf : !Inj eq eq f} tg tg' :
  sized_isomorphic tg tg' ->
  sized_isomorphic (relabel_sized_graph f tg) (relabel_sized_graph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%sized_isomorphic_exists.
  (* apply sized_isomorphic_symm. *)
  eapply (sized_isomorphic_of_partial_inj_dom' _ _
    (f ∘ fe ∘ invfun f (elements (sized_vertices tg))) fv).
  - rewrite sized_vertices_relabel_sized_graph.
    intros fi fj (i & -> & Hi%elem_of_elements)%elem_of_map
      (j & -> & Hj%elem_of_elements)%elem_of_map.
    cbn.
    rewrite 2invfun_linv by first [intros ????;apply Hf|easy].
    now intros ->%(inj f)%(inj fe).
  - cbn.
    intros ????; apply Hfv.
  - rewrite (relabel_sized_graph_compose _ _), <- 2 reindex_relabel_sized_graph.
    f_equal.
    rewrite (relabel_sized_graph_compose_strong' _ _ _) by
      now intros ? ? ? ?; cbn; rewrite 2 invfun_linv; try
        first [intros ????; apply Hf|now apply elem_of_elements, elem_of_union_r] ||
        intros ->%(inj _)%(inj fe).
    apply relabel_sized_graph_ext_strong.
    intros i Hi%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.


Lemma reindex_sized_graph_sized_isomorphic f `{Hf : !Inj eq eq f} tg tg' :
  sized_isomorphic tg tg' ->
  sized_isomorphic (reindex_sized_graph f tg) (reindex_sized_graph f tg').
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%sized_isomorphic_exists.
  (* apply sized_isomorphic_symm. *)
  eapply (sized_isomorphic_of_partial_inj_dom' _ _
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
  - rewrite (reindex_sized_graph_compose_strong' _ _ _). 2:{
      intros i j Hi%elem_of_elements Hj%elem_of_elements.
      cbn.
      rewrite 2 invfun_linv by first [intros ????;apply Hf|easy].
      now intros ->%(inj f)%(inj fv).
    }
    rewrite reindex_relabel_sized_graph.
    f_equal.
    rewrite (reindex_sized_graph_compose _ _ _).
    apply reindex_sized_graph_ext_strong.
    intros i _ Hi%elem_of_dom_2%elem_of_elements.
    cbn.
    now rewrite invfun_linv by first [intros ????;apply Hf|easy].
Qed.

Definition scohg_eq `{Equiv T} : relation CoHyGraph :=
  fun cohg cohg' =>
  cohg_eq cohg cohg' /\ cohg.(sized_map) = cohg'.(sized_map).

#[export] Instance scohg_eq_equivalence `{Equiv T, Equivalence T equiv} :
  Equivalence scohg_eq := _.

(* Lemma mk_scohg_eq `{Equiv T} cohg cohg' :
  cohg.(inputs) = cohg'.(inputs) ->
  cohg.(outputs) = cohg'.(outputs) ->
  cohg.(hedges) ≡ cohg'.(hedges) ->
  scohg_eq cohg cohg'.
Proof.
  easy.
Qed. *)



(* Lemma relabel_sized_graph_scohg_eq f tg tg' : scohg_eq tg tg' ->
  scohg_eq (relabel_sized_graph f ) *)


End SizedCospanHyperGraph.


Add Parametric Morphism {N} `{Equiv T} {n m} f :
  (@relabel_sized_graph N T n m f) with signature scohg_eq ==> scohg_eq as
  relabel_sized_graph_scohg_eq.
Proof.
  intros cohg cohg' (Hcohg & Hmap).
  split.
  - cbn; now f_equiv.
  - cbn; now f_equal.
Qed.

Add Parametric Morphism {N} `{Equiv T} {n m} f :
  (@reindex_sized_graph N T n m f) with signature scohg_eq ==> scohg_eq as
  reindex_sized_graph_scohg_eq.
Proof.
  intros cohg cohg' (Hcohg & Hmap).
  split.
  - cbn; now f_equiv.
  - done.
Qed.




Add Parametric Relation {N T n m} : (SizedCospanHyperGraph N T n m) sized_isomorphic
  reflexivity proved by sized_isomorphic_refl
  symmetry proved by sized_isomorphic_symm
  transitivity proved by sized_isomorphic_trans
  as sized_isomorphic_setoid.

Definition stack_sized_graphs_aux {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') : SizedCospanHyperGraph N T (n + n') (m + m') :=
  mk_scohg (stack_graphs_aux cohg cohg') (cohg.(sized_map) ∪ cohg'.(sized_map)).

Definition stack_sized_graphs {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') : SizedCospanHyperGraph N T (n + n') (m + m') :=
  stack_sized_graphs_aux
    (relabel_sized_graph (bcons false) (reindex_sized_graph (bcons false) cohg))
    (relabel_sized_graph (bcons true) (reindex_sized_graph (bcons true) cohg')).



(*
(* TODO: Rewrite with a new Vector.remove function returning a [vec A (pred n)] *)
Definition add_top_loop {T n m} (cohg : SizedCospanHyperGraph N T (S n) (S m)) : SizedCospanHyperGraph N T n m :=
  relabel_sized_graph {[Vector.hd cohg.(outputs) := Vector.hd cohg.(inputs)]} (
  Vector.tl cohg.(inputs) ->
    hg_add_vertices cohg.(hedges) {[Vector.hd cohg.(inputs)]}
      <- Vector.tl cohg.(outputs)).

Fixpoint add_top_loops {T n m o} : forall (cohg : SizedCospanHyperGraph N T (n + m) (n + o)),
  SizedCospanHyperGraph N T m o :=
  match n with
  | 0 => fun cohg => cohg
  | S n =>
    fun cohg => add_top_loops (add_top_loop cohg)
  end.

Definition add_top_loop' {T n m} (cohg : SizedCospanHyperGraph N T (S n) (S m)) : SizedCospanHyperGraph N T n m :=
  relabel_sized_graph {[Vector.hd cohg.(outputs) := Vector.hd cohg.(inputs)]} (
  Vector.tl cohg.(inputs) ->
    hg_add_vertices cohg.(hedges) ({[Vector.hd cohg.(inputs)]} ∖ vertices_hg cohg)
      <- Vector.tl cohg.(outputs)).

Fixpoint add_top_loops' {T n m o} : forall (cohg : SizedCospanHyperGraph N T (n + m) (n + o)),
  SizedCospanHyperGraph N T m o :=
  match n with
  | 0 => fun cohg => cohg
  | S n =>
    fun cohg => add_top_loops' (add_top_loop' cohg)
  end. *)


(*
Definition swapped_stack_sized_graphs_aux {T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') : SizedCospanHyperGraph N T (n' + n) (m + m') :=
  cohg'.(inputs) +++ cohg.(inputs) -> cohg.(hedges) ∪ cohg'.(hedges) <-
    cohg.(outputs) +++ cohg'.(outputs).

Definition swapped_stack_sized_graphs {T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') : SizedCospanHyperGraph N T (n' + n) (m + m') :=
  swapped_stack_sized_graphs_aux
    (relabel_sized_graph (bcons false) (reindex_sized_graph (bcons false) cohg))
    (relabel_sized_graph (bcons true) (reindex_sized_graph (bcons true) cohg')).

Definition compose_sized_graphs_alt {T n m o} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T m o) : SizedCospanHyperGraph N T n o :=
  add_top_loops (swapped_stack_sized_graphs cohg cohg'). *)


(* Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with SizedCospanHyperGraph. *)
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_sized_graph : graph_scope. *)

(* Open Scope graph_scope.
Open Scope nat. *)


Definition id_sized_graph {N T} {n} (v : vec N n) : SizedCospanHyperGraph N T n n :=
  mk_scohg (id_graph n) (list_to_map (imap (λ i k, (Pos.of_succ_nat i, k)) v)).

Definition swap_sized_graph {N T} {n m}
  (v : vec N n) (w : vec N m) : SizedCospanHyperGraph N T (n + m) (m + n) :=
  mk_scohg (swap_graph n m) (list_to_map (imap (λ i k, (Pos.of_succ_nat i, k)) (v ++ w))).

Definition cup_sized_graph {N T} {n} (v : vec N n) :
  SizedCospanHyperGraph N T 0 (n + n) :=
  mk_scohg (cup_graph n) (list_to_map (imap (λ i k, (Pos.of_succ_nat i, k)) v)).

Definition cap_sized_graph {N T} {n} (v : vec N n) :
  SizedCospanHyperGraph N T (n + n) 0 :=
  mk_scohg (cap_graph n) (list_to_map (imap (λ i k, (Pos.of_succ_nat i, k)) v)).


Definition sized_graph_of_tensor {N T} (t : T) {n m} (v : vec N n) (w : vec N m) :
  SizedCospanHyperGraph N T n m :=
  mk_scohg (graph_of_tensor t n m)
    (list_to_map (imap (λ i k, (bcons false $ Pos.of_succ_nat i, k)) v) ∪
    list_to_map (imap (λ i k, (bcons true $ Pos.of_succ_nat i, k)) w)).


Add Parametric Morphism {N} `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_sized_graphs_aux N T n m n' m') with signature
  scohg_eq ==> scohg_eq ==> scohg_eq as stack_sized_graphs_aux_scohg_eq.
Proof.
  intros cohg1 cohg1' [] cohg2 cohg2' [].
  split.
  - cbn.
    now f_equiv.
  - cbn.
    now f_equal.
Qed.

Add Parametric Morphism {N} `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@stack_sized_graphs N T n m n' m') with signature
  scohg_eq ==> scohg_eq ==> scohg_eq as stack_sized_graphs_scohg_eq.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold stack_sized_graphs.
  now do 3 f_equiv.
Qed.

(* Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m} :
  (@add_top_loop T n m) with signature
  scohg_eq ==> scohg_eq as add_top_loop_scohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & Hes).
  apply mk_scohg_eq; [cbn; repeat first [assumption|f_equal]..|].
  cbn.
  rewrite <- Hins, <- Houts.
  apply (relabel_hg_proper _ _ _).
  f_equiv; done.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@add_top_loops T n m o) with signature
  scohg_eq ==> scohg_eq as add_top_loops_scohg_eq.
Proof.
  induction n; [done|].
  intros cohg cohg' Heq.
  cbn.
  apply IHn.
  now f_equiv.
Qed.


Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_sized_graphs_aux T n m n' m') with signature
  scohg_eq ==> scohg_eq ==> scohg_eq as swapped_stack_sized_graphs_aux_scohg_eq.
Proof.
  intros cohg1 cohg1' (Hins1 & Houts1 & He1)
    cohg2 cohg2' (Hins2 & Houts2 & He2).
  apply mk_scohg_eq; [now cbn; f_equal..|].
  cbn.
  now f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m n' m'} :
  (@swapped_stack_sized_graphs T n m n' m') with signature
  scohg_eq ==> scohg_eq ==> scohg_eq as swapped_stack_sized_graphs_scohg_eq.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  unfold swapped_stack_sized_graphs.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv} {n m o} :
  (@compose_sized_graphs_alt T n m o) with signature
  scohg_eq ==> scohg_eq ==> scohg_eq as compose_sized_graphs_alt_scohg_eq.
Proof.
  unfold compose_sized_graphs_alt.
  intros; now do 2 f_equiv.
Qed. *)

Definition map_sized_graph {N M} {T n m} (f : N -> M) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T n m :=
  mk_scohg scohg (f <$> scohg.(sized_map)).

(* FIXME: Move *)
Definition enlarge_hypergraph {T} (f : positive -> list positive)
  (hg : HyperGraph T) : HyperGraph T :=
  mk_hg ((λ tio, (tio.1.1, tio.1.2 ≫= f, tio.2 ≫= f)) <$> hg.(hyperedges))
    (set_bind (list_to_set ∘ f) hg.(hypervertices)).

Definition enlarge_graph {T n m} (f : positive -> list positive)
  (cohg : CospanHyperGraph T n m) : CospanHyperGraph T _ _ :=
  list_to_vec ((cohg.(inputs) :> list _) ≫= f) ->
    enlarge_hypergraph f cohg
    <- list_to_vec ((cohg.(outputs) :> list _) ≫= f).


Definition bind_sized_graph {N} {T n m} (scohg : SizedCospanHyperGraph (list N) T n m) :
  SizedCospanHyperGraph N T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : N), encode (k, i)) (scohg.(sized_map) !!! k))
    scohg)
    (list_to_map (map_to_list scohg.(sized_map) ≫=
      λ k_ns, imap (λ i v, (encode (k_ns.1, i), v)) k_ns.2)).

Definition map_list_sized_graph {N M} {T n m} (f : N -> list M) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : M), encode (k, i)) ((f <$> scohg.(sized_map)) !!! k)) scohg)
    (list_to_map (map_to_list scohg.(sized_map) ≫=
    λ k_n, imap (λ i v, (encode (k_n.1, i), v)) (f k_n.2))).

(*
Definition abs_vertices {N T} (hg : (HyperEdge T)) : Pset :=
  list_to_set (hg.1.2 ++ hg.2).

Definition referenced_vertices {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  Pset :=
  list_to_set (cohg.(inputs) ++ cohg.(outputs))
    ∪ list_to_set (map_to_list cohg.(hedges).(hyperedges)
     ≫= λ k_flu, k_flu.2.1.2 ++ k_flu.2.2).

Definition isolated_vertices {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  Pset :=
  cohg.(hedges).(hypervertices)
    ∖ referenced_vertices cohg.

Lemma referenced_vertices_decomp {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  referenced_vertices cohg =
  list_to_set (inputs cohg ++ outputs cohg) ∪
    referenced_vertices_hg cohg.
Proof.
  done.
Qed.

Lemma sized_vertices_decomp {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  sized_vertices cohg = isolated_vertices cohg ∪ referenced_vertices cohg.
Proof.
  unfold sized_vertices, isolated_vertices.
  rewrite difference_union_L.
  unfold vertices_hg, referenced_vertices.
  apply set_eq.
  intros ?.
  rewrite 4 elem_of_union; tauto.
Qed.

Lemma isolated_referenced_disjoint {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  isolated_vertices cohg ## referenced_vertices cohg.
Proof.
  unfold isolated_vertices.
  now apply disjoint_difference_l1.
Qed.

Definition set_verts {T n m} (cohg : SizedCospanHyperGraph N T n m)
  (vs : Pset) : SizedCospanHyperGraph N T n m :=
  mk_cohg (mk_hg cohg.(hedges).(hyperedges) vs) cohg.(inputs) cohg.(outputs).

Definition norm_verts {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph N T n m := set_verts cohg (isolated_vertices cohg).

Lemma referenced_vertices_norm_verts {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  referenced_vertices (norm_verts cohg) = referenced_vertices cohg.
Proof.
  reflexivity.
Qed.

Lemma isolated_vertices_norm_verts {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  isolated_vertices (norm_verts cohg) = isolated_vertices cohg.
Proof.
  unfold isolated_vertices.
  cbn.
  unfold isolated_vertices.
  rewrite referenced_vertices_norm_verts.
  apply difference_twice_L.
Qed.


Lemma sized_vertices_norm_verts {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  sized_vertices (norm_verts cohg) = sized_vertices cohg.
Proof.
  now rewrite 2 sized_vertices_decomp,
    isolated_vertices_norm_verts, referenced_vertices_norm_verts.
Qed. *)


Lemma sized_graph_of_tensor_scohg_eq {N} `{Equiv T}
  (t t' : T) {n m} (v : vec N n) (w : vec N m) : t ≡ t' ->
  scohg_eq (sized_graph_of_tensor t v w) (sized_graph_of_tensor t' v w).
Proof.
  intros Ht.
  split; [|done].
  cbn.
  now apply graph_of_tensor_cohg_eq.
Qed.


Add Parametric Morphism {N} `{Equiv T} {n m} : (@sized_vertices N T n m)
  with signature scohg_eq ==> eq as sized_vertices_scohg_eq.
Proof.
  intros cohg cohg'.
  intros [Heq Hmap].
  unfold sized_vertices.
  f_equal; [|now f_equal].
  now apply vertices_cohg_eq_Proper.
Qed.

(*
Add Parametric Morphism `{Equiv T} {n m} : (@referenced_vertices T n m)
  with signature scohg_eq ==> eq as referenced_vertices_scohg_eq.
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
  with signature scohg_eq ==> eq as isolated_vertices_scohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold isolated_vertices.
  f_equal; [|now rewrite Heq].
  apply Heq.2.2.2.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@set_verts T n m)
  with signature scohg_eq ==> eq ==> scohg_eq as set_verts_scohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & [Heq Hverts]) vs.
  apply mk_scohg_eq; [done..|].
  split; [done|].
  done.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@norm_verts T n m)
  with signature scohg_eq ==> scohg_eq as norm_verts_scohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold norm_verts.
  now apply set_verts_scohg_eq, isolated_vertices_scohg_eq_Proper.
Qed. *)

(* Lemma norm_verts_idemp {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  norm_verts (norm_verts cohg) = norm_verts cohg.
Proof.
  unfold norm_verts at 1 3.
  now rewrite isolated_vertices_norm_verts.
Qed. *)


Definition scohg_vert_eq {N T} {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :=
  cohg_vert_eq cohg cohg' /\
  forall v, v ∈ vertices cohg -> cohg.(sized_map) !! v = cohg'.(sized_map) !! v.



#[export] Instance cohg_vert_equiv {N T n m} : Equivalence (@scohg_vert_eq N T n m).
Proof.
  split.
  - done.
  - intros cohg cohg' [Heq Hmap].
    split; [now symmetry|].
    intros v Hv.
    symmetry.
    apply Hmap.
    now rewrite <- vertices_norm_verts, (Heq : _ = _), vertices_norm_verts.
  - intros cohg cohg' cohg'' [Heq1 Hmap1] [Heq2 Hmap2].
    split; [now etransitivity; eauto|].
    intros v Hv.
    rewrite Hmap1 by done.
    apply Hmap2.
    now rewrite <- vertices_norm_verts, <- (Heq1 : _ = _), vertices_norm_verts.
Qed.

Notation "cohg '≡ᵥ' cohg'" := (scohg_vert_eq cohg%scohg cohg'%scohg)
  (at level 70) : scohg_scope.

Notation "cohg '≡ₕ' cohg'" := (scohg_eq cohg%scohg cohg'%scohg)
  (at level 70) : scohg_scope.

Definition norm_sized_verts {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph N T n m :=
  mk_scohg (norm_verts cohg) (filter (λ kv, kv.1 ∈ vertices cohg) cohg.(sized_map)).

Lemma norm_sized_verts_vert_eq {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  norm_sized_verts cohg ≡ᵥ cohg.
Proof.
  split; [apply norm_verts_vert_eq|].
  cbn.
  intros v.
  rewrite vertices_norm_verts.
  intros Hv.
  rewrite map_lookup_filter.
  cbn.
  case_guard; [|done].
  cbn.
  apply bind_with_Some.
Qed.

#[export] Instance norm_sized_verts_of_vert_eq {N T n m} :
  Proper (scohg_vert_eq ==> eq) (@norm_sized_verts N T n m).
Proof.
  intros cohg cohg' [Heq Hmap].
  apply scohg_ext.
  - apply Heq.
  - cbn.
    apply map_eq.
    intros i.
    rewrite 2 map_lookup_filter.
    cbn.
    rewrite <- (vertices_norm_verts cohg'), <- (Heq : _ = _), vertices_norm_verts.
    case_guard; [|now cbn; rewrite 2 option_bind_None_r].
    cbn.
    now rewrite <- Hmap by done.
Qed.


Add Parametric Morphism {N} `{Equiv T} {n m} : (@norm_sized_verts N T n m)
  with signature scohg_eq ==> scohg_eq as norm_sized_verts_scohg_eq.
Proof.
  intros cohg cohg' Heq.
  split; [apply norm_verts_cohg_eq_Proper, Heq|].
  cbn.
  erewrite vertices_cohg_eq_Proper by apply Heq.
  now rewrite <- Heq.2.
Qed.



Lemma scohg_vert_eq_alt {N T n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ᵥ cohg' <->
  inputs cohg = inputs cohg' /\
  outputs cohg = outputs cohg' /\
  hyperedges cohg = cohg' /\
  isolated_vertices cohg = isolated_vertices cohg' /\
  forall v, v ∈ vertices cohg ∪ vertices cohg' ->
  cohg.(sized_map) !! v = cohg'.(sized_map) !! v.
Proof.
  split.
  - intros [Heq Hmap].
    apply cohg_vert_eq_alt in Heq as Heq'.
    split_and!; [apply Heq'..|].
    intros v [Hv|Hv]%elem_of_union; [auto|].
    rewrite <- vertices_norm_verts, <- (Heq : _ = _), vertices_norm_verts in Hv.
    auto.
  - unfold scohg_vert_eq.
    rewrite cohg_vert_eq_alt.
    intros Heq.
    split; [split_and!; apply Heq|].
    intros v Hv.
    apply Heq, elem_of_union_l, Hv.
Qed.


(* FIXME: Move *)
Lemma scohg_eq_trans {N} `{Equiv T, Transitive T equiv} {n m} :
  Transitive (@scohg_eq N T n m _).
Proof.
  apply rel_intersection_trans, _.
  notypeclasses refine (rel_preimage_trans _ _ _).
  apply cohg_eq_trans.
Qed.
Lemma scohg_eq_symm {N} `{Equiv T, Symmetric T equiv} {n m} :
  Symmetric (@scohg_eq N T n m _).
Proof.
  apply rel_intersection_symm, _.
  notypeclasses refine (rel_preimage_symm _ _ _).
  apply cohg_eq_symm.
Qed.
Lemma scohg_eq_refl {N} `{Equiv T, Reflexive T equiv} {n m} :
  Reflexive (@scohg_eq N T n m _).
Proof.
  apply rel_intersection_refl, _.
  notypeclasses refine (rel_preimage_refl _ _ _).
  apply cohg_eq_refl.
Qed.


#[export] Instance SizedCospanHyperGraph_equiv {N} `{Equiv T} {n m} :
  Equiv (SizedCospanHyperGraph N T n m) :=
  rtc (scohg_eq ∪ scohg_vert_eq).

#[export] Instance SizedCospanHyperGraph_equivalence {N} `{Equiv T, Symmetric T equiv} {n m} :
  Equivalence (≡@{SizedCospanHyperGraph N T n m}).
Proof.
  apply rtc_equivalence.
  apply rel_union_symm, _.
  now apply scohg_eq_symm.
Qed.

#[export] Instance SizedCospanHyperGraph_refl {N} `{Equiv T} {n m} :
  Reflexive (≡@{SizedCospanHyperGraph N T n m}).
Proof.
  apply _.
Qed.

#[export] Instance SizedCospanHyperGraph_trans {N} `{Equiv T} {n m} :
  Transitive (≡@{SizedCospanHyperGraph N T n m}).
Proof.
  apply _.
Qed.

#[export] Instance scohg_eq_subrelation_equiv {N} `{Equiv T} {n m} :
  subrelation (@scohg_eq N T n m _) equiv.
Proof.
  apply _.
Qed.

#[export] Instance cohg_vert_eq_subrelation_equiv {N} `{Equiv T} {n m} :
  subrelation (@scohg_vert_eq N T n m) equiv.
Proof.
  apply _.
Qed.

#[export] Typeclasses Opaque SizedCospanHyperGraph_equiv.

(* Definition scohg_equiv_alt_defn `{Equiv T} {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :=
  scohg_eq (norm_verts cohg) (norm_verts cohg').

#[export] Instance scohg_equiv_alt_defn_equiv `{Equiv T, Equivalence T equiv} {n m} :
  Equivalence (@scohg_equiv_alt_defn T _ n m) :=
  rel_preimage_equiv norm_verts _ _. *)
(*
Lemma set_verts_id {T n m} (cohg : SizedCospanHyperGraph N T n m) :
  set_verts cohg (hypervertices cohg) = cohg.
Proof.
  now destruct cohg as [[]].
Qed.

Lemma referenced_vertices_set_verts {T n m} (cohg : SizedCospanHyperGraph N T n m) vs :
  referenced_vertices (set_verts cohg vs) = referenced_vertices cohg.
Proof.
  done.
Qed. *)

Lemma scohg_vert_eq_scohg_eq_commute {N} `{Equiv T} {n m} :
  rel_compose scohg_vert_eq (@scohg_eq N T n m _) ⊆
  rel_compose scohg_eq scohg_vert_eq.
Proof.
  apply relation_subseteq_iff.
  intros scohg scohg'' (scohg' & Hveq & Heq).
  pose proof (relation_subseteq_iff.1 cohg_vert_eq_cohg_eq_commute scohg scohg'') as Hcomm.
  tspecialize Hcomm by now exists scohg'; split; [apply Hveq|apply Heq].
  destruct Hcomm as (cohg' & Hveq' & Heq').
  exists (mk_scohg cohg' (scohg.(sized_map))).
  split.
  - split; done.
  - split; [done|].
    cbn.
    intros v Hv.
    rewrite Hveq.2 by now erewrite vertices_cohg_eq_Proper by eassumption.
    now rewrite Heq.2.
Qed.


Definition struct_sized_isomorphic {N T n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :=
  sized_isomorphic (norm_sized_verts cohg) (norm_sized_verts cohg').

(* Lemma referenced_vertices_relabel_sized_graph {N T n m} f (cohg : SizedCospanHyperGraph N T n m) :
  referenced_vertices (relabel_sized_graph f cohg) =
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


Lemma isolated_vertices_relabel_sized_graph {N T n m} f `{Hf : !Inj eq eq f}
  (cohg : SizedCospanHyperGraph N T n m) :
  isolated_vertices (relabel_sized_graph f cohg) =
  set_map f (isolated_vertices cohg).
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_relabel_sized_graph.
  cbn.
  now rewrite (set_map_difference_L _).
Qed. *)

Lemma norm_sized_verts_relabel_sized_graph {N T n m} f `{Hf : !Inj eq eq f}
  (cohg : SizedCospanHyperGraph N T n m) :
  norm_sized_verts (relabel_sized_graph f cohg) = relabel_sized_graph f (norm_sized_verts cohg).
Proof.
  apply scohg_ext; [apply (norm_verts_relabel_graph _)|].
  cbn.
  apply map_eq.
  intros i.
  apply option_eq; intros k.
  rewrite map_lookup_filter_Some, 2 (lookup_kmap_Some _).
  setoid_rewrite map_lookup_filter_Some.
  cbn.
  rewrite (vertices_relabel_graph _).
  set_solver + Hf.
Qed.


Lemma norm_sized_verts_reindex_sized_graph {N T n m} f `{Hf : !Inj eq eq f}
  (cohg : SizedCospanHyperGraph N T n m) :
  norm_sized_verts (reindex_sized_graph f cohg) = reindex_sized_graph f (norm_sized_verts cohg).
Proof.
  apply scohg_ext; [apply (norm_verts_reindex_graph _)|].
  cbn.
  rewrite (vertices_reindex_graph _).
  done.
Qed.




Lemma norm_sized_verts_sized_isomorphic {N T n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  sized_isomorphic cohg cohg' -> sized_isomorphic (norm_sized_verts cohg) (norm_sized_verts cohg').
Proof.
  intros (fv & fe & Hfv & Hfe & ->)%sized_isomorphic_exists.
  rewrite (norm_sized_verts_relabel_sized_graph _),
    (norm_sized_verts_reindex_sized_graph _).
  now constructor.
Qed.

#[export] Instance struct_sized_isomorphic_equivalence {N T n m} :
  Equivalence (@struct_sized_isomorphic N T n m) := rel_preimage_equiv _ _ _.


Notation "cohg '≡ᵢ' cohg'" := (struct_sized_isomorphic cohg%scohg cohg'%scohg)
  (at level 70) : scohg_scope.

#[export] Instance sized_isomorphic_struct_sized_isomorphic {N T n m} :
  subrelation (@sized_isomorphic N T n m) struct_sized_isomorphic.
Proof.
  refine norm_sized_verts_sized_isomorphic.
Qed.

#[export] Instance cohg_vert_eq_struct_sized_isomorphic {N T n m} :
  subrelation (@scohg_vert_eq N T n m) struct_sized_isomorphic.
Proof.
  unfold struct_sized_isomorphic.
  now intros ? ? <-.
Qed.

Lemma struct_sized_isomorphic_alt {N T n m} :
  @struct_sized_isomorphic N T n m ≡ rtc (scohg_vert_eq ∪ sized_isomorphic).
Proof.
  apply relation_subseteq_antisymm; apply relation_subseteq_iff.
  - intros cohg cohg' Heq.
    transitivity (norm_sized_verts cohg); [apply rtc_once; left; now rewrite norm_sized_verts_vert_eq|].
    transitivity (norm_sized_verts cohg'); [|apply rtc_once; left; now rewrite norm_sized_verts_vert_eq].
    apply rtc_once; right; apply Heq.
  - intros cohg cohg' Heq.
    induction Heq as [|a b c Hab Hbc IH]; [done|].
    rewrite <- IH.
    destruct Hab as [Hab|Hab]; now rewrite Hab.
Qed.

Inductive scohg_syntactic_eq {N} `{Equiv T} {n m} : relation (SizedCospanHyperGraph N T n m) :=
  | scohg_syntactic_eq_relabel_reindex cohg cohg' fv fe : Inj eq eq fv -> Inj eq eq fe ->
    scohg_eq (norm_sized_verts cohg) (norm_sized_verts cohg') ->
    scohg_syntactic_eq cohg (relabel_sized_graph fv (reindex_sized_graph fe cohg')).


Notation "cohg '≡ₛ' cohg'" := (scohg_syntactic_eq cohg%scohg cohg'%scohg)
  (at level 70) : scohg_scope.

Lemma scohg_syntactic_eq_exists {N} `{Equiv T} {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ₛ cohg' <-> exists cohg'' fv fe, Inj eq eq fv /\ Inj eq eq fe /\
    scohg_eq (norm_sized_verts cohg) (norm_sized_verts cohg'') /\
      cohg' = relabel_sized_graph fv (reindex_sized_graph fe cohg'').
Proof.
  split; [|naive_solver eauto using scohg_syntactic_eq].
  intros Heq.
  induction Heq.
  eauto 7.
Qed.

#[export] Instance sized_isomorphic_scohg_syntactic_eq {N} `{Equiv T, Reflexive T equiv} {n m} :
  subrelation (@sized_isomorphic N T n m) scohg_syntactic_eq.
Proof.
  intros cohg cohg' (fv & fe & Hfv & Hfe & ->)%sized_isomorphic_exists.
  constructor; [apply _..|].
  now apply scohg_eq_refl.
Qed.

#[export] Instance scohg_eq_scohg_syntactic_eq {N} `{Equiv T} {n m} :
  subrelation (@scohg_eq N T n m _) scohg_syntactic_eq.
Proof.
  intros cohg cohg' Heq.
  apply scohg_syntactic_eq_exists.
  exists cohg', id, id.
  split_and!; [apply id_inj..|now apply norm_sized_verts_scohg_eq|].
  now rewrite relabel_sized_graph_id, reindex_sized_graph_id.
Qed.

#[export] Instance cohg_vert_eq_scohg_syntactic_eq {N} `{Equiv T, Reflexive T equiv} {n m} :
  subrelation (@scohg_vert_eq N T n m) scohg_syntactic_eq.
Proof.
  intros cohg cohg' Heq.
  apply scohg_syntactic_eq_exists.
  exists cohg', id, id.
  do 2 (split; [apply id_inj|]).
  split; [|now rewrite relabel_sized_graph_id, reindex_sized_graph_id].
  erewrite norm_sized_verts_of_vert_eq by eassumption.
  now apply scohg_eq_refl.
Qed.

Lemma relabel_sized_graph_scohg_eq_inv_l {N} `{Equiv T} f
  {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  relabel_sized_graph f cohg ≡ₕ cohg' -> exists cohg'',
    cohg' = relabel_sized_graph f cohg'' /\ cohg ≡ₕ cohg''.
Proof.
  intros Heq.
  specialize (relabel_graph_cohg_eq_inv_l f _ _ Heq.1) as (cohg'' & Heq'' & Hequiv).
  exists (mk_scohg cohg'' cohg.(sized_map)).
  split; [apply scohg_ext; [done|symmetry; apply Heq.2]|].
  split; [done|].
  done.
Qed.

Lemma reindex_sized_graph_scohg_eq_inv_l {N} `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  reindex_sized_graph f cohg ≡ₕ cohg' -> exists cohg'',
    cohg' = reindex_sized_graph f cohg'' /\ cohg ≡ₕ cohg''.
Proof.
  intros Heq.
  specialize (reindex_graph_cohg_eq_inv_l f _ _ Heq.1) as (cohg'' & Heq'' & Hequiv).
  exists (mk_scohg cohg'' cohg.(sized_map)).
  split; [apply scohg_ext; [done|symmetry; apply Heq.2]|].
  split; done.
Qed.


Lemma norm_sized_verts_id {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  hypervertices cohg = isolated_vertices cohg ->
  dom cohg.(sized_map) ⊆ vertices cohg ->
  norm_sized_verts cohg = cohg.
Proof.
  intros Heq Hdom.
  apply scohg_ext; [now apply norm_verts_id|].
  cbn.
  apply map_filter_id.
  now intros ? ? ?%elem_of_dom_2%Hdom.
Qed.

(* Lemma relabel_sized_graph_set_verts {N T n m} f (cohg : SizedCospanHyperGraph N T n m) vs :
  relabel_sized_graph f (set_verts cohg vs) = set_verts (relabel_sized_graph f cohg) (set_map f vs).
Proof.
  done.
Qed. *)

(* Lemma hypervertices_subseteq_vertices {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  hypervertices cohg ⊆ sized_vertices cohg.
Proof.
  unfold sized_vertices.
  rewrite <- union_subseteq_l.
  unfold vertices_hg.
  rewrite <- union_subseteq_r.
  done.
Qed. *)

Lemma sized_vertices_norm_sized_verts {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  sized_vertices (norm_sized_verts cohg) = vertices cohg.
Proof.
  apply set_eq, set_subseteq_antisymm, union_subseteq_l', eq_reflexivity, symmetry, vertices_norm_verts.
  apply union_subseteq, and_comm, conj, eq_reflexivity, vertices_norm_verts.
  cbn.
  etransitivity. 1:{
    apply eq_reflexivity.
    symmetry.
    refine (filter_dom_L (λ kv, kv ∈ vertices cohg) _).
  }
  now intros k [Hk _]%elem_of_filter.
Qed.

(* FIXME: Move *)
Lemma map_filter_union' `{FinMap K M} {A} (P : K -> Prop)
  `{HP : forall ka, Decision (P ka)} (m1 m2 : M A) :
  filter (λ kv, P kv.1) (m1 ∪ m2) =
  filter (λ kv, P kv.1) m1 ∪ filter (λ kv, P kv.1) m2.
Proof.
  apply map_eq; intros k.
  apply option_eq.
  intros a.
  rewrite map_lookup_filter_Some.
  rewrite 2 lookup_union.
  rewrite 2 map_lookup_filter.
  destruct (m1 !! k), (m2 !! k); cbn;
  try case_guard; cbn; naive_solver.
Qed.
Lemma kmap_kmap `{FinMap K1 M1, FinMap K2 M2, FinMap K3 M3} {A}
  (f : K1 -> K2) (g : K2 -> K3) `{Hf : !Inj eq eq f, Hg : !Inj eq eq g}
  (m : M1 A) :
  kmap g (kmap f m :> M2 A) =@{M3 A} kmap (g ∘ f) m.
Proof.
  apply map_eq.
  intros i.
  apply option_eq; intros v.
  rewrite 2 (lookup_kmap_Some _).
  setoid_rewrite (lookup_kmap_Some _).
  set_solver + Hf Hg.
Qed.

Lemma relabel_sized_graph_norm_sized_verts_inv_l {N} `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  norm_sized_verts cohg = relabel_sized_graph f cohg' -> exists f' cohg'',
    Inj eq eq f' /\
    (forall v, v ∈ sized_vertices cohg' -> f' v = f v) /\
    cohg' = norm_sized_verts cohg'' /\ cohg = relabel_sized_graph f' cohg''.
Proof.
  intros Hseq.

  set (to_add := filter (λ kv, kv.1 ∉ vertices cohg) cohg.(sized_map)).
  pose proof (partial_bijection_extension' (vertices cohg') f
    (fun _ _ _ _ => Hf _ _)) as (f' & f'inv & Hf' & Hf'inv & Hrinv & Hlinv & Hf'_f).
  exists f'.
(*
  set (f_range := set_map f (sized_vertices cohg') :> Pset).
  assert (Hrange : f_range = vertices cohg). 1:{
    subst f_range.
    rewrite <- sized_vertices_relabel_sized_graph.
    rewrite <- Hseq.
    apply sized_vertices_norm_sized_verts.
  }

  set (nthresh : max_list_with pos_to_nat_pred
  set (f' := fun k => if decide (k ∈ sized_vertices cohg') then f k else k).
  specialize (partial_injection_extension' )


  enough (exists cohg'', cohg' = norm_sized_verts cohg'' /\ exists f',
    Inj eq eq f' /\
    (forall v, v ∈ sized_vertices cohg' -> f' v = f v)
     /\ cohg = relabel_sized_graph f' cohg'') by naive_solver. *)

  assert (Hcohg'verts : sized_vertices cohg' = vertices cohg'). 1:{
    apply (f_equal sized_vertices) in Hseq as Hsized.
    rewrite sized_vertices_norm_sized_verts,
      (sized_vertices_relabel_sized_graph _) in Hsized.
    apply (f_equal (vertices ∘ sized_cospan)) in Hseq as Hverts.
    cbn in Hverts.
    rewrite vertices_norm_verts, vertices_relabel_graph in Hverts.
    rewrite Hsized in Hverts.
    set_solver +Hf Hverts.
  }

  specialize (relabel_graph_norm_verts_inv_l f _ _ (f_equal sized_cospan Hseq)) as (cohg'' & Hnorm & Heq).
  exists (mk_scohg cohg'' (cohg'.(sized_map) ∪ (kmap f'inv to_add))).
  split_and!; [apply _|..].
  - intros v.
    rewrite Hcohg'verts.
    apply Hf'_f.
  - apply scohg_ext; [done|].
    cbn.
    etransitivity; [|symmetry;
      refine (map_filter_union' (.∈ vertices cohg'') _ _)].
    rewrite map_filter_id. 2:{
      cbn.
      intros i _ Hi%elem_of_dom_2.
      rewrite <- vertices_norm_verts, <- Hnorm.
      rewrite <- Hcohg'verts.
      now apply elem_of_union_r.
    }
    rewrite map_empty_filter_2, (map_union_empty _); [done|].
    intros fk v.
    rewrite (lookup_kmap_Some _).
    intros (k & -> & Hiv).
    unfold to_add in Hiv.
    apply map_lookup_filter_Some in Hiv as [Hkv Hk].
    cbn in Hk |- *.
    rewrite <- vertices_norm_verts, <- Hnorm.
    rewrite <- Hcohg'verts.
    apply (f_equal sized_vertices) in Hseq.
    rewrite sized_vertices_norm_sized_verts,
      (sized_vertices_relabel_sized_graph _) in Hseq.
    intros Hin.
    apply Hk.
    rewrite Hseq.
    apply elem_of_map.
    exists (f'inv k).
    rewrite <- Hf'_f by now rewrite <- Hcohg'verts.
    rewrite (cancel _ _ _).
    done.
  - apply scohg_ext.
    + cbn.
      rewrite Heq.
      apply relabel_graph_ext_strong.
      intros v.
      rewrite <- vertices_norm_verts, <- Hnorm.
      now intros ?%Hf'_f.
    + cbn.
      rewrite (kmap_union _).
      apply (f_equal sized_map) in Hseq.
      cbn in Hseq.
      erewrite kmap_ext, <- Hseq. 2:{
        intros k _ Hk%elem_of_dom_2.
        apply Hf'_f.
        rewrite <- Hcohg'verts.
        now apply elem_of_union_r.
      }
      erewrite <- map_filter_union_complement at 1.
      f_equal.
      rewrite (kmap_kmap _ _).
      unfold to_add.
      rewrite (kmap_ext _ id) by now intros; apply cancel.
      rewrite kmap_id.
      done.
Qed.


(*
  (* intros Hseq.
  specialize (relabel_graph_norm_verts_inv_l f _ _ (f_equal sized_cospan Hseq)) as (cohg'' & Hnorm & Heq).
  exists (mk_scohg cohg'' (filter (λ kv, f kv.1 ∈ vertices cohg) cohg'.(sized_map))).
  split.
  - apply scohg_ext; [done|].
    cbn.
    rewrite Heq.
    rewrite (vertices_relabel_graph _).

  exists (mk_scohg cohg'' cohg.(sized_map)).
  split; [apply scohg_ext; [done|symmetry; apply Heq.2]|].
  split; done. *)

  set (finv' := invfun f (elements (sized_vertices cohg'))).
  specialize (partial_injection_extension _
    finv' (invfun_inj f _ (fun _ _ _ _ => Hf _ _))) as Hfinv.
  destruct Hfinv as (finv & Hfinv & Hfinv_eq).
  intros Heq.
  exists (relabel_sized_graph finv cohg).
  split.
  - apply (f_equal (relabel_sized_graph finv)) in Heq.
    rewrite <- (norm_sized_verts_relabel_sized_graph _) in Heq.
    rewrite Heq.
    rewrite (relabel_sized_graph_compose _ _).
    symmetry.
    apply relabel_sized_graph_id_strong.
    intros k Hk.
    cbn.
    rewrite Forall_fmap, Forall_forall in Hfinv_eq.
    rewrite Hfinv_eq by now apply elem_of_elements.
    apply invfun_linv, elem_of_elements, Hk.
    now intros ? ? ? ? ?%Hf.
  - symmetry.
    rewrite (relabel_sized_graph_compose _ _).
    apply relabel_sized_graph_id_strong.
    intros k Hk.
    cbn.
    rewrite Forall_forall in Hfinv_eq.
    eenough (Hk' : _) by
    now rewrite Hfinv_eq; [apply invfun_rinv, Hk'|apply Hk'].

    apply (f_equal sized_vertices) in Heq.
    rewrite sized_vertices_norm_sized_verts, sized_vertices_relabel_sized_graph in Heq.
    rewrite Heq in Hk.
    set_solver + Hk.
Qed. *)

Lemma reindex_sized_graph_norm_sized_verts_inv_l {N} `{Equiv T} f `{Hf : !Inj eq eq f}
  {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  norm_sized_verts cohg = reindex_sized_graph f cohg' -> exists cohg'',
    cohg' = norm_sized_verts cohg'' /\ cohg = reindex_sized_graph f cohg''.
Proof.
  intros Heq.
  specialize (reindex_graph_norm_verts_inv_l f _ _ (f_equal sized_cospan Heq))
    as (cohg'' & Heq'' & Hequiv).
  exists (mk_scohg cohg'' cohg.(sized_map)).
  split; [apply scohg_ext; [done|]|apply scohg_ext; done].
  cbn.
  symmetry.
  apply (f_equal vertices) in Hequiv.
  rewrite (vertices_reindex_graph _) in Hequiv.
  rewrite <- Hequiv.
  apply (f_equal sized_map Heq).
Qed.



Lemma scohg_syntactic_eq_trans {N} `{Equiv T, Transitive T equiv} {n m} :
  Transitive (@scohg_syntactic_eq N T _ n m).
Proof.
  intros cohg cohg' cohg'' Heq1 Heq2.
  (* induction Heq2 as [cohg' cohg'' fv2 fe2 Hfv2 Hfe2 Heq2]. *)
  apply scohg_syntactic_eq_exists in Heq2
    as (cohg23 & fv2 & fe2 & Hfv2 & Hfe2 & Hheq2 & Heq2).
  apply scohg_syntactic_eq_exists in Heq1
    as (cohg12 & fv1 & fe1 & Hfv1 & Hfe1 & Hheq1 & Heq1).
  subst cohg' cohg''.

  rewrite (norm_sized_verts_relabel_sized_graph _), (norm_sized_verts_reindex_sized_graph _) in Hheq2.

  apply relabel_sized_graph_scohg_eq_inv_l in Hheq2 as Hheq2'.
  destruct Hheq2' as (cohg12' & Heq12 & Hrel).
  apply (reindex_sized_graph_scohg_eq_inv_l _) in Hrel as Hheq2''.
  destruct Hheq2'' as (cohg12'' & -> & Hrel').

  apply scohg_syntactic_eq_exists.

  apply (relabel_sized_graph_norm_sized_verts_inv_l _) in Heq12 as
    (fv1' & cohg23' & Hfv' & Hfv'fv & Heq12%eq_sym & ->).

  apply (reindex_sized_graph_norm_sized_verts_inv_l _) in Heq12 as
    (cohg12' & -> & ->).



  exists cohg12'.
  exists (fv2 ∘ fv1'), (fe2 ∘ fe1).
  split; [apply _|].
  split; [apply _|].

  split.
  - eapply scohg_eq_trans; eauto.
  - rewrite <- (relabel_sized_graph_compose _ _), <- (reindex_sized_graph_compose _ _).
    rewrite <- (reindex_relabel_sized_graph fe2 fv1').
    done.
Qed.


Lemma scohg_syntactic_eq_alt {N} `{Equiv T, Reflexive T equiv,
  Transitive T equiv} {n m} :
  (@scohg_syntactic_eq N T _ n m) ≡ rtc (scohg_eq ∪ sized_isomorphic ∪ scohg_vert_eq).
Proof.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros cohg cohg' Hcohg.
    induction Hcohg as [cohg cohg' fv fe Hfv Hfe Heq].
    rewrite <- (sized_iso_relabel_reindex _ _ _).
    rewrite <- (norm_sized_verts_vert_eq cohg).
    rewrite <- (norm_sized_verts_vert_eq cohg').
    apply (subrel Heq).
  - rewrite <- (rtc_id scohg_syntactic_eq);
    [|intros x; apply sized_isomorphic_scohg_syntactic_eq; reflexivity|
    now apply scohg_syntactic_eq_trans].
    apply rtc_subseteq.
    rewrite 2  rel_union_subseteq.
    split_and!; apply relation_subseteq_iff; apply _.
Qed.

#[export] Instance scohg_syntactic_eq_equivalence {N} `{Equiv T, Equivalence T equiv}
  {n m} : Equivalence (@scohg_syntactic_eq N T _ n m).
Proof.
  erewrite Equivalence_equiv_proper by now apply scohg_syntactic_eq_alt.
  apply rtc_equivalence.
  apply _.
Qed.

Lemma scohg_equiv_alt_gen {N} `{Equiv T} {n m} :
  (≡@{SizedCospanHyperGraph N T n m}) ≡ rel_compose (rtc scohg_eq) scohg_vert_eq.
Proof.
  unfold SizedCospanHyperGraph_equiv, equiv at 2.
  rewrite rtc_union_commute by apply scohg_vert_eq_scohg_eq_commute.
  f_equiv.
  now rewrite rtc_id by apply _.
Qed.


Lemma scohg_equiv_alt'_gen {N} `{Equiv T} {n m} :
  (≡@{SizedCospanHyperGraph N T n m}) ≡ rel_preimage norm_sized_verts (rtc scohg_eq).
Proof.
  apply relation_subseteq_antisymm; [rewrite scohg_equiv_alt_gen|]; apply relation_subseteq_iff.
  - intros cohg cohg'' (cohg' & H12 & H23).
    unfold rel_preimage.
    rewrite <- H23.
    now apply (rtc_proper scohg_eq _ norm_sized_verts norm_sized_verts_scohg_eq_Proper).
  - intros cohg cohg' Heq12.
    unfold rel_preimage in Heq12.
    rewrite <- (norm_sized_verts_vert_eq cohg).
    etransitivity; [|apply (subrel (norm_sized_verts_vert_eq cohg'))].
    eapply rtc_subrelation, Heq12.
    apply _.
Qed.


Lemma scohg_equiv_alt {N} `{Equiv T, Equivalence T equiv} {n m} :
  (≡@{SizedCospanHyperGraph N T n m}) ≡ rel_compose scohg_eq scohg_vert_eq.
Proof.
  rewrite scohg_equiv_alt_gen.
  now rewrite rtc_id by apply _.
Qed.

Lemma scohg_equiv_alt' {N} `{Equiv T, Equivalence T equiv} {n m} :
  (≡@{SizedCospanHyperGraph N T n m}) ≡ rel_preimage norm_sized_verts scohg_eq.
Proof.
  rewrite scohg_equiv_alt'_gen.
  now rewrite rtc_id by apply _.
Qed.

Lemma scohg_equiv_alt_rel {N} `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ cohg' <-> exists cohg'', cohg ≡ₕ cohg'' /\ cohg'' ≡ᵥ cohg'.
Proof.
  apply (relation_equiv_iff.1 scohg_equiv_alt).
Qed.

Lemma scohg_equiv_alt'_rel {N} `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ cohg' <-> norm_sized_verts cohg ≡ₕ norm_sized_verts cohg'.
Proof.
  apply (relation_equiv_iff.1 scohg_equiv_alt').
Qed.






Lemma proper_scohg_equiv_of_vert_eq_unary {N1 N2} `{Equiv T1, Equiv T2} {n1 m1 n2 m2}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2) :
  Proper (scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (scohg_eq ==> scohg_eq) f ->
  Proper (equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cohg cohg' (cohg'' & Heq%(rtc_proper _ _ _ Hfeq) & Hiso%Hfiso)%(relation_equiv_iff.1 scohg_equiv_alt_gen).
  etransitivity; [|apply (subrel Hiso)].
  eapply rtc_subrelation, Heq.
  apply _.
Qed.

Lemma proper_scohg_equiv_of_vert_eq_binary {N1 N2 N3} `{Equiv T1, Equiv T2, Equiv T3,
  HT1 : Reflexive T1 equiv, HT2 : Reflexive T2 equiv}
  {n1 m1 n2 m2 n3 m3}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2 ->
    SizedCospanHyperGraph N3 T3 n3 m3) :
  Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (scohg_eq ==> scohg_eq ==> scohg_eq) f ->
  Proper (equiv ==> equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq.
  intros cohg1 cohg1' (cohg1'' & Hiso1 & Heq1)%(relation_equiv_iff.1 scohg_equiv_alt_gen).
  intros cohg2 cohg2' (cohg2'' & Hiso2 & Heq2)%(relation_equiv_iff.1 scohg_equiv_alt_gen).
  transitivity (f cohg1'' cohg2''); [|apply (subrel (Hfiso _ _ Heq1 _ _ Heq2))].
  apply (rtc_subrelation scohg_eq _ _).
  pose proof (@scohg_eq_refl N1 T1 _ _ n1 m1) as Hrefl1.
  pose proof (@scohg_eq_refl N2 T2 _ _ n2 m2) as Hrefl2.
  now apply (rtc_proper2 _ _ _ _ Hfeq).
Qed.

Lemma proper_scohg_equiv_of_vert_eq_binary' {N1 N2 N3} `{Equiv T1, Equiv T2, Equiv T3}
  {n1 m1 n2 m2 n3 m3}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2 ->
    SizedCospanHyperGraph N3 T3 n3 m3) :
  Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (scohg_eq ==> eq ==> scohg_eq) f ->
  Proper (eq ==> scohg_eq ==> scohg_eq) f ->
  Proper (equiv ==> equiv ==> equiv) f.
Proof.
  intros Hfiso Hfeq1 Hfeq2.
  intros cohg1 cohg1' (cohg1'' & Hiso1 & Heq1)%(relation_equiv_iff.1 scohg_equiv_alt_gen).
  intros cohg2 cohg2' (cohg2'' & Hiso2 & Heq2)%(relation_equiv_iff.1 scohg_equiv_alt_gen).
  transitivity (f cohg1'' cohg2''); [|apply (subrel (Hfiso _ _ Heq1 _ _ Heq2))].
  apply (rtc_subrelation scohg_eq _ _).
  now apply (rtc_proper2' _ _ _ _ Hfeq1 Hfeq2).
Qed.


Lemma struct_sized_isomorphic_alt' {N T n m} :
  @struct_sized_isomorphic N T n m ≡
    rel_compose scohg_vert_eq (rel_compose sized_isomorphic scohg_vert_eq).
Proof.
  apply relation_subseteq_antisymm.
  - apply relation_subseteq_iff.
    intros cohg cohg' Heq.
    exists (norm_sized_verts cohg).
    split; [now rewrite norm_sized_verts_vert_eq|].
    exists (norm_sized_verts cohg').
    split; [|now rewrite norm_sized_verts_vert_eq].
    done.
  - apply (rel_compose_subseteq_trans _ _ _ (relation_subseteq_iff.2 _)).
    apply (rel_compose_subseteq_trans _ _ _); now apply (relation_subseteq_iff.2 _).
Qed.



Lemma proper_struct_sized_isomorphic_of_vert_eq_unary {N1 N2 T1 T2} {n1 m1 n2 m2}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2) :
  Proper (scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (sized_isomorphic ==> sized_isomorphic) f ->
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic) f.
Proof.
  intros Hfeq Hfiso.
  intros cohg cohg' Heq%Hfiso.
  rewrite <- (norm_sized_verts_vert_eq cohg), <- (norm_sized_verts_vert_eq cohg').
  apply (subrel Heq).
Qed.

Lemma proper_struct_sized_isomorphic_of_vert_eq_binary {N1 N2 N3 T1 T2 T3} {n1 m1 n2 m2 n3 m3}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2 ->
    SizedCospanHyperGraph N3 T3 n3 m3) :
  Proper (scohg_vert_eq ==> scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (sized_isomorphic ==> sized_isomorphic ==> sized_isomorphic) f ->
  Proper (struct_sized_isomorphic ==> struct_sized_isomorphic ==> struct_sized_isomorphic) f.
Proof.
  intros Hfeq Hfiso.
  intros cohg1 cohg1' Heq1%Hfiso.
  intros cohg2 cohg2' Heq2%Heq1.
  rewrite <- (norm_sized_verts_vert_eq cohg1), <- (norm_sized_verts_vert_eq cohg2).
  rewrite Heq2.
  now rewrite 2 norm_sized_verts_vert_eq.
Qed.



Lemma proper_scohg_syntactic_eq_of_iso_vert_eq_unary {N1 N2} `{Equiv T1, Reflexive T1 equiv,
  Transitive T1 equiv, Equiv T2, Reflexive T2 equiv, Transitive T2 equiv} {n1 m1 n2 m2}
  (f : SizedCospanHyperGraph N1 T1 n1 m1 -> SizedCospanHyperGraph N2 T2 n2 m2) :
  Proper (scohg_vert_eq ==> scohg_vert_eq) f ->
  Proper (sized_isomorphic ==> sized_isomorphic) f ->
  Proper (scohg_eq ==> scohg_eq) f ->
  Proper (scohg_syntactic_eq ==> scohg_syntactic_eq) f.
Proof.
  intros Hfveq Hfiso Hfeq.
  pose proof (@Proper_equiv_proper).
  rewrite 2 scohg_syntactic_eq_alt.
  apply rtc_proper.
  apply rel_union_proper, _.
  now apply rel_union_proper.
Qed.

(*
Lemma proper_scohg_syntactic_eq_of_iso_vert_eq_binary `{Equiv T1, Reflexive T1 equiv,
  Transitive T1 equiv, Equiv T2, Reflexive T2 equiv, Transitive T2 equiv} {n1 m1 n2 m2}
  (f : SizedCospanHyperGraph N T1 n1 m1 -> SizedCospanHyperGraph N T2 n2 m2) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) f ->
  Proper (sized_isomorphic ==> sized_isomorphic) f ->
  Proper (scohg_eq ==> scohg_eq) f ->
  Proper (scohg_syntactic_eq ==> scohg_syntactic_eq) f. *)


(*
Lemma referenced_vertices_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  referenced_vertices (stack_sized_graphs cohg cohg') =
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

Lemma isolated_vertices_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  isolated_vertices (stack_sized_graphs cohg cohg') =
  set_map (bcons false) (isolated_vertices cohg) ∪
  set_map (bcons true) (isolated_vertices cohg').
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_stack_sized_graphs.
  cbn.
  rewrite 2 (set_map_difference_L _).
  generalize (hypervertices cohg) (hypervertices cohg')
    (referenced_vertices cohg) (referenced_vertices cohg').
  set_solver.
Qed.

Lemma referenced_vertices_swapped_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  referenced_vertices (swapped_stack_sized_graphs cohg cohg') =
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

Lemma isolated_vertices_swapped_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  isolated_vertices (swapped_stack_sized_graphs cohg cohg') =
  set_map (bcons false) (isolated_vertices cohg) ∪
  set_map (bcons true) (isolated_vertices cohg').
Proof.
  unfold isolated_vertices.
  rewrite referenced_vertices_swapped_stack_sized_graphs.
  cbn.
  rewrite 2 (set_map_difference_L _).
  generalize (hypervertices cohg) (hypervertices cohg')
    (referenced_vertices cohg) (referenced_vertices cohg').
  set_solver.
Qed.

Lemma norm_sized_verts_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  norm_sized_verts (stack_sized_graphs cohg cohg') =
  stack_sized_graphs (norm_sized_verts cohg) (norm_sized_verts cohg').
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  apply isolated_vertices_stack_sized_graphs.
Qed.


Add Parametric Morphism {T n m n' m'} : (@stack_sized_graphs T n m n' m') with signature
  cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq as stack_sized_graphs_vert_eq_mor.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  hnf.
  rewrite 2 norm_sized_verts_stack_sized_graphs.
  now f_equal.
Qed.


Lemma norm_sized_verts_swapped_stack_sized_graphs {T n m n' m'}
  (cohg : SizedCospanHyperGraph N T n m) (cohg' : SizedCospanHyperGraph N T n' m') :
  norm_sized_verts (swapped_stack_sized_graphs cohg cohg') =
  swapped_stack_sized_graphs (norm_sized_verts cohg) (norm_sized_verts cohg').
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  apply isolated_vertices_swapped_stack_sized_graphs.
Qed.


Add Parametric Morphism {T n m n' m'} : (@swapped_stack_sized_graphs T n m n' m') with signature
  cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq as swapped_stack_sized_graphs_vert_eq_mor.
Proof.
  intros cohg1 cohg1' Heq1 cohg2 cohg2' Heq2.
  hnf.
  rewrite 2 norm_sized_verts_swapped_stack_sized_graphs.
  now f_equal.
Qed. *)


Lemma relabel_sized_graph_scohg_vert_eq {N T n m} f `{Hf : !Inj eq eq f}
  (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ᵥ cohg' ->
  relabel_sized_graph f cohg ≡ᵥ relabel_sized_graph f cohg'.
Proof.
  intros Heq.
  split.
  - now apply relabel_graph_cohg_vert_eq, Heq.1.
  - cbn.
    intros fv.
    rewrite vertices_relabel_graph.
    intros (v & -> & Hv)%elem_of_map.
    rewrite 2 (lookup_kmap _).
    now apply Heq.2.
Qed.

Add Parametric Morphism {N T n m} f `{Hf : !Inj eq eq f} :
  (@relabel_sized_graph N T n m f) with signature
  scohg_vert_eq ==> scohg_vert_eq as relabel_sized_graph_vert_eq_mor.
Proof.
  intros cohg cohg'.
  now apply relabel_sized_graph_scohg_vert_eq.
Qed.

Lemma reindex_sized_graph_scohg_vert_eq {N T n m} f `{!Inj eq eq f}
  (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ᵥ cohg' ->
  reindex_sized_graph f cohg ≡ᵥ reindex_sized_graph f cohg'.
Proof.
  intros Heq.
  split; [now apply reindex_graph_cohg_vert_eq, Heq.1|].
  cbn.
  rewrite (vertices_reindex_graph _).
  apply Heq.2.
Qed.


Section Compose.

  Context {N T : Type}.

  Definition compose_sized_graphs_aux {n m o} (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) : SizedCospanHyperGraph N T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_sized_graph (subst_by_vec connected_substs)
      (mk_scohg (tgl.(inputs) ->
        hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set tgr.(inputs) ∖ (vertices_hg tgl ∪ vertices_hg tgr))
          <- tgr.(outputs)) (tgl.(sized_map) ∪ tgr.(sized_map))).

  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_sized_graphs {n m o} (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) : SizedCospanHyperGraph N T n o :=
    compose_sized_graphs_aux
      (reindex_sized_graph (bcons false) (relabel_sized_graph (bcons false) tgl))
      (reindex_sized_graph (bcons true) (relabel_sized_graph (bcons true) tgr)).


  (* Definition compose_sized_graphs_unsafe {n m o} (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) : SizedCospanHyperGraph N T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set (tgr.(inputs)) ∖ (vertices_hg tgl ∪ vertices_hg tgr)) <- tgr.(outputs).


  Definition compose_sized_graphs_unsafe' {n m o} (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) : SizedCospanHyperGraph N T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges))
      (list_to_set (tgr.(inputs)) ∖ (vertices_hg tgl ∪ vertices_hg tgr ∪ list_to_set (tgl.(inputs) ++ tgr.(outputs)))) <- tgr.(outputs). *)

(* Lemma isolated_vertices_alt_vertices {n m} (cohg : SizedCospanHyperGraph N T n m) :
  isolated_vertices cohg = sized_vertices cohg ∖ referenced_vertices cohg.
Proof.
  rewrite sized_vertices_decomp.
  rewrite difference_union_distr_l_L.
  rewrite difference_diag_L.
  unfold isolated_vertices.
  rewrite union_empty_r_L.
  now rewrite difference_twice_L.
Qed.

Lemma cohg_vert_eq_alt_vertices {n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ᵥ cohg' <->
  inputs cohg = inputs cohg' /\
  outputs cohg = outputs cohg' /\
  hyperedges cohg = hyperedges cohg' /\
  sized_vertices cohg = sized_vertices cohg'.
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
    rewrite 2 sized_vertices_decomp, Hisol.
    f_equal.
    unfold referenced_vertices.
    congruence.
  - rewrite 2 isolated_vertices_alt_vertices.
    intros ->.
    unfold referenced_vertices.
    congruence.
Qed.

Lemma compose_sized_graphs_unsafe'_correct {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  compose_sized_graphs_unsafe' tgl tgr ≡ᵥ compose_sized_graphs_unsafe tgl tgr.
Proof.
  apply cohg_vert_eq_alt_vertices.
  split_and!; [done..|].
  unfold sized_vertices.
  cbn.
  rewrite 2 vertices_hg_add_vertices.
  rewrite <- (difference_difference_l_L (list_to_set tgr.(inputs))).
  rewrite <- (union_assoc_L _), difference_union_L.
  apply union_assoc_L.
Qed. *)

Lemma compose_sized_graphs_to_compose_sized_graphs_aux {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  compose_sized_graphs tgl tgr = compose_sized_graphs_aux
    (reindex_sized_graph (bcons false) (relabel_sized_graph (bcons false) tgl))
    (reindex_sized_graph (bcons true) (relabel_sized_graph (bcons true) tgr)).
Proof.
  reflexivity.
Qed.

(* Lemma compose_sized_graphs_aux_to_compose_sized_graphs_unsafe {n m o} (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  tgl.(outputs) = tgr.(inputs) ->
  compose_sized_graphs_aux tgl tgr = compose_sized_graphs_unsafe tgl tgr.
Proof.
  intros.
  unfold compose_sized_graphs_aux.
  rewrite H.
  unfold relabel_sized_graph.
  rewrite Vector.map_ext with (g:=(λ x : _, x)) by apply subst_by_vec_id.
  rewrite Vector.map_id.
  simpl.
  rewrite Vector.map_ext with (g:=(λ x : _, x)) by apply subst_by_vec_id.
  rewrite Vector.map_id.
  simpl.
  rewrite relabel_hg_id' by apply subst_by_vec_id.
  reflexivity.
Qed. *)
(* 
Lemma inputs_add_top_loops {n m m'}
  (tg : SizedCospanHyperGraph N T (n + m) (n + m')) :
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
  (tg : SizedCospanHyperGraph N T (n + m) (n + m')) :
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
  (tg : SizedCospanHyperGraph N T (n + m) (n + m')) :
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
  (tg : SizedCospanHyperGraph N T (n + m) (n + m')) :
  add_top_loops tg =
  relabel_sized_graph (subst_by_vec (propogate_subst
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
  (tg : SizedCospanHyperGraph N T (S n) (S m)) :
  add_top_loop' tg ≡ᵥ add_top_loop tg.
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  unfold add_top_loop', add_top_loop.
  unfold isolated_vertices.
  rewrite 2 referenced_vertices_relabel_sized_graph.
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


Lemma isolated_vertices_add_top_loop {n m} (cohg : SizedCospanHyperGraph N T (S n) (S m)) :
  isolated_vertices (add_top_loop cohg) =
  isolated_vertices cohg ∪ ({[(vhd (inputs cohg))]} ∖ referenced_vertices (add_top_loop cohg)).
Proof.
  unfold isolated_vertices, add_top_loop.
  rewrite referenced_vertices_relabel_sized_graph.
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



Lemma norm_sized_verts_add_top_loop {n m} (cohg : SizedCospanHyperGraph N T (S n) (S m)) :
  norm_sized_verts (add_top_loop cohg) = norm_sized_verts (add_top_loop (norm_sized_verts cohg)).
Proof.
  apply cohg_ext'; [done..|].
  cbn.
  rewrite 2 isolated_vertices_add_top_loop.
  rewrite isolated_vertices_norm_sized_verts.
  done.
Qed.

Lemma norm_sized_verts_add_top_loops {n m o} (cohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  norm_sized_verts (add_top_loops cohg) = norm_sized_verts (add_top_loops (norm_sized_verts cohg)).
Proof.
  induction n; [cbn; now rewrite norm_sized_verts_idemp|].
  cbn.
  now rewrite IHn, norm_sized_verts_add_top_loop, <- IHn.
Qed.

#[export] Instance add_top_loop_proper {n m} :
  Proper (@cohg_vert_eq T (S n) (S m) ==> cohg_vert_eq) add_top_loop.
Proof.
  intros cohg cohg' Heq.
  hnf.
  rewrite norm_sized_verts_add_top_loop, Heq, <- norm_sized_verts_add_top_loop.
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
  rewrite norm_sized_verts_add_top_loops, Heq, <- norm_sized_verts_add_top_loops.
  done.
Qed.

Lemma add_top_loops'_correct {n m o}
  (tg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  add_top_loops' tg ≡ᵥ add_top_loops tg.
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  now rewrite add_top_loop'_correct.
Qed.


Lemma add_top_loops_alt_vert_eq {n m m'}
  (tg : SizedCospanHyperGraph N T (n + m) (n + m')) :
  add_top_loops tg ≡ᵥ
  relabel_sized_graph (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
    (vsplitr tg.(inputs) ->
      hg_add_vertices tg.(hedges)
      (list_to_set (vsplitl tg.(inputs)) ∖ vertices_hg tg)
      <- vsplitr tg.(outputs)).
Proof.
  rewrite add_top_loops_alt.
  apply relabel_sized_graph_cohg_vert_eq.
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



Lemma compose_sized_graphs_alt_aux_correct {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  hyperedges tgl ##ₘ hyperedges tgr ->
  add_top_loops (swapped_stack_sized_graphs_aux tgl tgr) ≡ᵥ
    compose_sized_graphs_aux tgl tgr.
Proof.
  intros Hdisj.
  rewrite add_top_loops_alt_vert_eq.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  unfold compose_sized_graphs_aux.
  rewrite vertices_hg_union by done.
  reflexivity.
Qed.

Lemma compose_sized_graphs_alt_correct {n m o}
  (tgl : SizedCospanHyperGraph N T n m) (tgr : SizedCospanHyperGraph N T m o) :
  add_top_loops (swapped_stack_sized_graphs tgl tgr) ≡ᵥ
    compose_sized_graphs tgl tgr.
Proof.
  rewrite compose_sized_graphs_to_compose_sized_graphs_aux.
  rewrite <- compose_sized_graphs_alt_aux_correct; [rewrite 2 reindex_relabel_sized_graph; done|].
  cbn.
  now apply (kmap_inj2_disjoint _).
Qed. *)

End Compose.