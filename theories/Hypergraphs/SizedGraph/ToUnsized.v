From TensorRocq Require Export SizedGraph.Definitions.
















































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


Definition venlarge_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) : CospanHyperGraph T _ _ :=
  vbind f cohg.(inputs) ->
    enlarge_hypergraph (λ p, vec_to_list (f p)) cohg
    <- vbind f cohg.(outputs).


Definition bind_sized_graph {N} {T n m} (scohg : SizedCospanHyperGraph (list N) T n m) :
  SizedCospanHyperGraph N T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : N), encode (k, i)) (scohg.(sized_map) !!! k))
    scohg)
    (venlarge_Pmap (λ k _, list_to_vec (default [] (scohg.(sized_map) !! k)))
      scohg.(sized_map)).


Definition map_list_sized_graph {N M} {T n m} (f : N -> list M)
  (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : M), encode (k, i)) ((f <$> scohg.(sized_map)) !!! k)) scohg)
    (venlarge_Pmap (λ k _, list_to_vec (default [] (f <$> scohg.(sized_map) !! k)))
      (scohg.(sized_map))).

Definition map_vec_sized_graph {N M} {T n m} {nf : N -> nat}
  (f : forall k, vec M (nf k)) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T _ _ :=
  mk_scohg (venlarge_graph
      (nf := λ p, default 0 (nf <$> (scohg.(sized_map) !! p)))
      (λ p, (fun_to_vec (λ i, encode (p, i:>nat)))) scohg)
    (list_enlarge_Pmap (λ k a, f a) scohg.(sized_map)).






(* Only valid if vertices scohg ⊆ dom scohg.(sized_map) *)
Definition unit_sized_graph_to_graph {T n m}
  (scohg : SizedCospanHyperGraph unit T n m) : CospanHyperGraph T n m := scohg.

Definition nat_sized_graph_to_unit_graph {T n m}
  (scohg : SizedCospanHyperGraph nat T n m) :
  SizedCospanHyperGraph unit T _ _ :=
  map_vec_sized_graph (nf := id)
    (fun k => fun_to_vec (λ _, ())) scohg.

(* Definition sized_graph_to_nat_sized_graph {N T n m} (f : N -> nat)
  (scohg : SizedCospanHyperGraph N T n m) : SizedCospanHyperGraph nat T _ _ :=
  map_
  {T n m} *)

Definition sized_graph_to_graph {N T n m} (f : N -> nat)
  (scohg : SizedCospanHyperGraph N T n m) : CospanHyperGraph T _ _ :=
  map_vec_sized_graph (nf := f)
    (fun k => fun_to_vec (λ _, ())) scohg.


(* Definition graph_to_bundled_graph {T n m} (cohg : CospanHyperGraph T n m) :
  {n & {m & CospanHyperGraph T n m}} :=
  existT n (existT m cohg). *)

(* Definition graph_to_untyped_graph {T n m} (cohg : CospanHyperGraph T n m) :
  HyperGraph T * list positive * list positive :=
  (hedges cohg, vec_to_list $ inputs cohg, vec_to_list $ outputs cohg). *)

(* Coercion graph_to_bundled_graph : CospanHyperGraph >-> sigT. *)











(* Definition sized_graph_to_bundled_sized_graph
  {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  {n & {m & SizedCospanHyperGraph N T n m}} :=
  existT n (existT m cohg).

(* Coercion sized_graph_to_bundled_sized_graph : SizedCospanHyperGraph >-> sigT. *)

Lemma bundled_sized_graph_eq_iff {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') :
  sized_graph_to_bundled_sized_graph cohg =ₛ
  sized_graph_to_bundled_sized_graph cohg' <-> exists Hn Hm, cohg = eq_rect_r (λ k, SizedCospanHyperGraph N T n k)
    (eq_rect_r (λ k, SizedCospanHyperGraph N T k m') cohg' Hn) Hm.
Proof.
  split.
  - intros Heq.
    unfold sized_graph_to_bundled_sized_graph in Heq.
    inversion_sigma Heq.
    subst n'.
    cbn in Heq2.
    inversion_sigma Heq2.
    subst m'.
    cbn in *.
    subst.
    exists eq_refl, eq_refl.
    done.
  - intros (<- & <- & ->).
    done.
Qed. *)


Lemma enlarge_hypergraph_relabel_hg {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  enlarge_hypergraph f (relabel_hg g hg) = enlarge_hypergraph (f ∘ g) hg.
Proof.
  apply hg_ext; cbn.
  - rewrite <- map_fmap_compose.
    apply map_fmap_ext.
    intros k [[t i] o] _.
    cbn.
    rewrite 2 list_fmap_bind.
    done.
  - set_solver.
Qed.

Lemma relabel_hg_enlarge_hypergraph {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  relabel_hg g (enlarge_hypergraph f hg) = enlarge_hypergraph (fmap g ∘ f) hg.
Proof.
  apply hg_ext; cbn.
  - rewrite <- map_fmap_compose.
    apply map_fmap_ext.
    intros k [[t i] o] _.
    cbn.
    rewrite 2 list_bind_fmap.
    done.
  - set_solver.
Qed.



Lemma enlarge_hypergraph_ext {T} f g (hg : HyperGraph T) :
  (forall i, f i = g i) ->
  enlarge_hypergraph f hg = enlarge_hypergraph g hg.
Proof.
  intros Hfg.
  apply hg_ext.
  - cbn.
    apply map_fmap_ext.
    intros _ tio _.
    f_equal; [f_equal|]; apply list_bind_ext, reflexivity; intros; apply Hfg.
  - cbn.
    set_unfold.
    setoid_rewrite Hfg.
    done.
Qed.

Lemma enlarge_hypergraph_id {T} (hg : HyperGraph T) :
  enlarge_hypergraph (λ k, [k]) hg = hg.
Proof.
  apply hg_ext.
  - cbn.
    etransitivity; [|apply map_fmap_id].
    apply map_fmap_ext.
    intros _ [[t i] o] _.
    cbn.
    now f_equal; [f_equal|]; rewrite list_bind_singleton_r, list_fmap_id.
  - cbn.
    set_solver.
Qed.






From TensorRocq Require Export sigT2_relation.


















Definition graph_to_pair_bundled {T n m}
  (scohg : CospanHyperGraph T n m) : {nm : nat * nat & CospanHyperGraph T nm.1 nm.2} :=
  existT (n, m) scohg.


Notation "g =ₛ g'" := (graph_to_pair_bundled g%cohg = graph_to_pair_bundled g'%cohg)
  (at level 70) : cohg_scope.

Notation "sg '[≡ₕ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_eq _ n m _)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ᵥ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_vert_eq _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ᵢ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @struct_isomorphic _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ₛ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_syntactic_eq _ _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Lemma mk_cohg_bundled_eq {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  inputs cohg =@{list _} inputs cohg' ->
  outputs cohg =@{list _} outputs cohg' ->
  hedges cohg = hedges cohg' ->
  cohg =ₛ cohg'.
Proof.
  intros Hins Houts Hhedges.
  apply vec_to_list_inj1 in Hins as Hn.
  apply vec_to_list_inj1 in Houts as Hm.
  subst.
  apply vec_to_list_inj2 in Hins.
  apply vec_to_list_inj2 in Houts.
  auto using cohg_ext with f_equal.
Qed.





Lemma bundled_cohg_eq_iff `{Equiv T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  scohg [≡ₕ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hedges scohg ≡ hedges scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    split_and!; apply Hequiv || f_equal; apply Hequiv.
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    split; [|done].
    now apply mk_cohg_eq.
Qed.

Lemma mk_bundled_cohg_eq `{Equiv T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hedges scohg ≡ hedges scohg' ->
  scohg [≡ₕ]ₛ scohg'.
Proof.
  intros; apply bundled_cohg_eq_iff; easy.
Qed.

Lemma bundled_cohg_vert_eq_iff {T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  scohg [≡ᵥ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    apply cohg_vert_eq_alt_vertices in Hequiv.
    split_and!; first [apply Hequiv|f_equal; apply Hequiv].
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    now apply cohg_vert_eq_alt_vertices.
Qed.

Lemma mk_bundled_cohg_vert_eq {T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hyperedges scohg = hyperedges scohg' ->
  vertices scohg = vertices scohg' ->
  scohg [≡ᵥ]ₛ scohg'.
Proof.
  intros; apply bundled_cohg_vert_eq_iff; easy.
Qed.


Lemma graph_to_pair_bundled_apply {T T'}
  (f : forall n m, CospanHyperGraph T n m -> CospanHyperGraph T' n m)
  {n m}
  (scohg : CospanHyperGraph T n m) :
  f n m scohg =ₛ
  (λ scohg', f _ _ (projT2 scohg'))
  (graph_to_pair_bundled scohg).
Proof.
  done.
Qed.






Lemma venlarge_graph_relabel_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  (cohg : CospanHyperGraph T n m) :
  venlarge_graph f (relabel_graph g cohg) =ₛ
  venlarge_graph (λ k, f (g k)) cohg.
Proof.
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite vec_to_list_map.
    now rewrite list_fmap_bind.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite vec_to_list_map.
    now rewrite list_fmap_bind.
  - cbn.
    apply enlarge_hypergraph_relabel_hg.
Qed.


Definition sized_graph_to_pair_bundled {N T n m}
  (scohg : SizedCospanHyperGraph N T n m) : {nm : nat * nat & SizedCospanHyperGraph N T nm.1 nm.2} :=
  existT (n, m) scohg.


Notation "g =ₛ g'" := (sized_graph_to_pair_bundled g = sized_graph_to_pair_bundled g')
  (at level 70) : scohg_scope.

Notation "sg '[≡ₕ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_eq _ _ n m _)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ᵥ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_vert_eq _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ᵢ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @struct_sized_isomorphic _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ₛ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_syntactic_eq _ _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Lemma bundled_sized_rel_alt {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m')
  (R : forall n m, relation (SizedCospanHyperGraph N T n m)) :
  sigT2_relation R (sized_graph_to_pair_bundled scohg)
    (sized_graph_to_pair_bundled scohg') <->
  exists Hn Hm, R n m scohg (mk_scohg (mk_cohg scohg'
    (Vector.cast scohg'.(inputs) Hn)
    (Vector.cast scohg'.(outputs) Hm)) (scohg'.(sized_map))).
Proof.
  split.
  - intros (Heq & Hcast)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    exists eq_refl, eq_refl.
    rewrite 2 cast_id.
    now destruct scohg' as [[]].
  - intros (-> & -> & HR).
    apply mk_sigT2_relation_alt.
    exists eq_refl, eq_refl.
    cbn.
    rewrite 2 cast_id in HR.
    now destruct scohg' as [[]].
Qed.

Lemma mk_scohg_bundled_eq {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') :
  vec_to_list (inputs cohg) = vec_to_list (inputs cohg') ->
  vec_to_list (outputs cohg) = vec_to_list (outputs cohg') ->
  hedges cohg = hedges cohg' ->
  sized_map cohg = sized_map cohg' ->
  cohg =ₛ cohg'.
Proof.
  intros Hi Ho Hh Hmap.
  apply vec_to_list_inj1 in Hi as Hn.
  subst n'.
  apply vec_to_list_inj1 in Ho as Hm.
  subst m'.
  f_equal.
  apply vec_to_list_inj2 in Hi, Ho.
  auto using scohg_ext, cohg_ext.
Qed.


Lemma bundled_scohg_eq_iff {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  scohg [≡ₕ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  sized_map scohg = sized_map scohg' /\
  hedges scohg ≡ hedges scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    split_and!; apply Hequiv || f_equal; apply Hequiv.
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    split; [|done].
    now apply mk_cohg_eq.
Qed.

Lemma mk_bundled_scohg_eq {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  sized_map scohg = sized_map scohg' ->
  hedges scohg ≡ hedges scohg' ->
  scohg [≡ₕ]ₛ scohg'.
Proof.
  intros; apply bundled_scohg_eq_iff; easy.
Qed.

Lemma scohg_vert_eq_iff {N} {T} {n m}
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' <->
  inputs scohg = inputs scohg' /\
  outputs scohg = outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg' /\
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg').
Proof.
  split.
  - intros Heq.
    pose proof Heq as Heq'.
    unfold scohg_vert_eq in Heq'.
    rewrite cohg_vert_eq_alt_vertices in Heq'.
    split_and!; [apply Heq'.1..|].
    rewrite <- Heq'.1.2.2.2.
    apply map_eq; intros k.
    rewrite 2 map_lookup_filter.
    cbn.
    case_guard; [|cbn; now rewrite 2 option_bind_None_r].
    cbn.
    now rewrite <- Heq'.2 by done.
  - intros (Hins & Houts & Hh & Hverts & Hm).
    split; [now apply cohg_vert_eq_alt_vertices|].
    intros v Hv.
    rewrite <- Hverts in Hm.
    apply (f_equal (.!!v)) in Hm.
    rewrite 2 map_lookup_filter in Hm.
    revert Hm.
    cbn.
    case_guard; [|done].
    cbn.
    destruct (_ !! _), (_ !! _); cbn; congruence.
Qed.

Lemma bundled_scohg_vert_eq_iff {N} {T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  scohg [≡ᵥ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg' /\
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg').
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    apply scohg_vert_eq_iff in Hequiv.
    split_and!; first [apply Hequiv|f_equal; apply Hequiv].
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    now apply scohg_vert_eq_iff.
Qed.

Lemma mk_bundled_scohg_vert_eq {N} {T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hyperedges scohg = hyperedges scohg' ->
  vertices scohg = vertices scohg' ->
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg') ->
  scohg [≡ᵥ]ₛ scohg'.
Proof.
  intros; apply bundled_scohg_vert_eq_iff; easy.
Qed.


Lemma map_vec_sized_graph_relabel_sized_graph {N M T n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (g : positive -> positive) `{Hg : !Inj eq eq g}
  (scohg : SizedCospanHyperGraph N T n m) :
  map_vec_sized_graph f (relabel_sized_graph g scohg) =ₛ
  relabel_sized_graph
    (encode_map (prod_map g (@id nat)))
    (map_vec_sized_graph f scohg).
Proof.
  apply mk_scohg_bundled_eq.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_map, vec_to_list_bind.
    rewrite list_bind_fmap, list_fmap_bind.
    apply list_bind_ext; [|done].
    intros k.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_map, vec_to_list_bind.
    rewrite list_bind_fmap, list_fmap_bind.
    apply list_bind_ext; [|done].
    intros k.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    rewrite enlarge_hypergraph_relabel_hg.
    rewrite relabel_hg_enlarge_hypergraph.
    apply enlarge_hypergraph_ext.
    intros i.
    cbn.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    unfold list_enlarge_Pmap.
    rewrite (map_kmap_bind _) by apply list_enlarge_Pmap_disjointness.
    rewrite (map_bind_kmap _ _) by apply list_enlarge_Pmap_disjointness.
    apply map_bind_ext.
    intros k a _.
    rewrite (kmap_list_to_map _).
    f_equal.
    rewrite fmap_imap.
    unfold compose.
    apply imap_ext.
    intros i x _.
    cbn.
    now rewrite encode_map_encode.
Qed.

Lemma enlarge_hypergraph_reindex_hg {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  enlarge_hypergraph f (reindex_hg g hg) = reindex_hg g (enlarge_hypergraph f hg).
Proof.
  apply hg_ext; cbn.
  - now rewrite kmap_fmap'.
  - done.
Qed.

Lemma map_vec_sized_graph_reindex_sized_graph {N M T n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (g : positive -> positive) `{Hg : !Inj eq eq g}
  (scohg : SizedCospanHyperGraph N T n m) :
  map_vec_sized_graph f (reindex_sized_graph g scohg) =ₛ
  reindex_sized_graph g
    (map_vec_sized_graph f scohg).
Proof.
  apply mk_scohg_bundled_eq; [done..| |done].
  cbn.
  apply enlarge_hypergraph_reindex_hg.
Qed.



#[export] Instance enlarge_hypergraph_proper `{Equiv T} f :
  Proper ((≡@{HyperGraph T}) ==> equiv) (enlarge_hypergraph f).
Proof.
  intros hg hg'.
  intros [He Hv].
  split.
  - cbn.
    apply map_fmap_proper, He.
    intros tio tio' Htio.
    split; [split|]; cbn; [|f_equal..]; apply Htio.
  - cbn.
    now f_equal.
Qed.

Lemma map_vec_sized_graph_scohg_eq {N M} `{Equiv T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₕ scohg' ->
  map_vec_sized_graph f scohg [≡ₕ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros Heq.
  apply mk_bundled_scohg_eq.
  - cbn.
    rewrite Heq.1.1, Heq.2.
    done.
  - cbn.
    rewrite Heq.1.2.1, Heq.2.
    done.
  - cbn.
    rewrite Heq.2.
    done.
  - cbn.
    rewrite Heq.2.
    apply enlarge_hypergraph_proper, Heq.1.2.2.
Qed.


Lemma vertices_hg_enlarge_hypergraph {T}
  (f : positive -> list positive) (hg : HyperGraph T) :
  vertices_hg (enlarge_hypergraph f hg) =
  set_bind (list_to_set ∘ f) (vertices_hg hg).
Proof.
  rewrite 2 vertices_hg_decomp.
  rewrite set_bind_union_L.
  f_equal.
  cbn.
  apply set_eq; intros p.
  set_unfold.
  split.
  - intros (ktio & Hp & Hktio).
    rewrite map_to_list_fmap in Hktio.
    apply elem_of_list_fmap in Hktio as ([k tio] & -> & Hktio).
    cbn in *.
    rewrite <- elem_of_app, <- bind_app in Hp.
    apply elem_of_list_bind in Hp as (x & Hp & Hx).
    set_solver.
  - intros (x & ([k tio] & Hx & Hktio) & Hp).
    rewrite <- elem_of_app in Hx.
    exists (k, (tio.1.1, (tio.1.2 ≫= f), (tio.2 ≫= f))).
    rewrite map_to_list_fmap.
    split; [set_solver + Hx Hp|].
    refine (elem_of_list_fmap_1 (prod_map id
    (λ tio, (tio.1.1, (tio.1.2 ≫= f), (tio.2 ≫= f)))) _ (k, ((tio.1.1, tio.1.2), tio.2)) _).
    now destruct tio as [ [] ].
Qed.


Lemma vertices_venlarge_graph {T n m nf}
  (f : forall p, vec positive (nf p)) (cohg : CospanHyperGraph T n m) :
  vertices (venlarge_graph f cohg) =
  set_bind (list_to_set ∘ f) (vertices cohg).
Proof.
  unfold vertices.
  cbn.
  rewrite set_bind_union_L.
  rewrite vertices_hg_enlarge_hypergraph.
  rewrite 2 vec_to_list_bind.
  f_equal.
  rewrite 2 list_to_set_app_L, set_bind_union_L; f_equal;
  set_solver +.
Qed.

Lemma map_vec_sized_graph_scohg_vert_eq {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' ->
  map_vec_sized_graph f scohg [≡ᵥ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros Heq'.
  pose proof Heq' as Heq%scohg_vert_eq_alt.
  assert (Hverts : vertices (map_vec_sized_graph f scohg) =
    vertices (map_vec_sized_graph f scohg')). 1:{
    cbn.
    rewrite 2 vertices_venlarge_graph.
    apply scohg_vert_eq_iff in Heq'.
    apply leibniz_equiv_iff, set_bind_ext, eq_reflexivity, Heq'.2.2.2.1.
    intros p Hp _.
    cbn.
    rewrite <- Heq.2.2.2.2 by now apply elem_of_union_l.
    done.
  }
  apply mk_bundled_scohg_vert_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite <- Heq.1.
    apply list_bind_ext_strong.
    intros k Hk.
    rewrite <- Heq.2.2.2.2 by set_solver +Hk.
    done.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite <- Heq.2.1.
    apply list_bind_ext_strong.
    intros k Hk.
    rewrite <- Heq.2.2.2.2 by set_solver +Hk.
    done.
  - cbn.
    rewrite Heq.2.2.1.
    apply map_fmap_ext.
    intros i tio Hi.
    f_equal; [f_equal|].
    + apply list_bind_ext_strong.
      intros v Hv.
      rewrite <- Heq.2.2.2.2 by now apply elem_of_union_r, elem_of_vertices; set_solver +Hv Hi.
      done.
    + apply list_bind_ext_strong.
      intros v Hv.
      rewrite <- Heq.2.2.2.2 by now apply elem_of_union_r, elem_of_vertices; set_solver +Hv Hi.
      done.
  - apply Hverts.
  - rewrite <- Hverts.
    apply map_filter_strong_ext.
    intros i s.
    cbn [fst].
    apply and_iff_from_l; [done|].
    intros Hi _.
    cbn.
    cbn in Hi.
    rewrite vertices_venlarge_graph in Hi.
    apply elem_of_set_bind in Hi as (p & Hp & Hi).
    cbn in Hi.
    rewrite (vec_to_list_fun_to_vec (λ i, encode (p, i))) in Hi.
    set_unfold in Hi.
    cbn in Hi.
    destruct Hi as (j & -> & Hj).
    rewrite 2 lookup_list_enlarge_Pmap_encode.
    rewrite <- Heq'.2 by done.
    done.
Qed.

Lemma sized_graph_to_pair_bundled_apply {N N' T T'}
  (f : forall n m, SizedCospanHyperGraph N T n m -> SizedCospanHyperGraph N' T' n m)
  {n m}
  (scohg : SizedCospanHyperGraph N T n m) :
  f n m scohg =ₛ
  (λ scohg', f _ _ (projT2 scohg'))
  (sized_graph_to_pair_bundled scohg).
Proof.
  done.
Qed.

Lemma map_vec_sized_graph_sized_isomorphic {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  sized_isomorphic scohg scohg' ->
  sigT2_relation (@sized_isomorphic _ _)
    (sized_graph_to_pair_bundled (map_vec_sized_graph f scohg))
    (sized_graph_to_pair_bundled (map_vec_sized_graph f scohg')).
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%sized_isomorphic_exists.
  rewrite (map_vec_sized_graph_relabel_sized_graph _ _).
  rewrite (sized_graph_to_pair_bundled_apply
    (fun _ _ => relabel_sized_graph _)).
  rewrite (map_vec_sized_graph_reindex_sized_graph _ _).
  cbn.
  constructor.
  constructor; apply _.
Qed.



Lemma map_vec_sized_graph_struct_sized_isomorphic {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵢ scohg' ->
  map_vec_sized_graph f scohg [≡ᵢ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  unfold struct_sized_isomorphic at 1.
  intros Heq%(map_vec_sized_graph_sized_isomorphic f).
  etransitivity; [|etransitivity; [apply (subrel Heq)|]].
  - refine (subrel (map_vec_sized_graph_scohg_vert_eq f _ _ _)).
    now rewrite norm_sized_verts_vert_eq.
  - refine (subrel (map_vec_sized_graph_scohg_vert_eq f _ _ _)).
    now rewrite norm_sized_verts_vert_eq.
Qed.



Lemma map_vec_sized_graph_scohg_syntactic_eq {N M}
  `{Equiv T, Equivalence T equiv} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₛ scohg' ->
  map_vec_sized_graph f scohg [≡ₛ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros (scohg'' & fv & fe & Hfv & Hfe & Heq & ->)%scohg_syntactic_eq_exists.
  rewrite <- (map_vec_sized_graph_sized_isomorphic f scohg'' _
    (sized_iso_relabel_reindex _ _ _)).
  rewrite <- (map_vec_sized_graph_scohg_vert_eq f _ scohg
    (norm_sized_verts_vert_eq _)).
  rewrite (map_vec_sized_graph_scohg_eq f _ _ Heq).
  rewrite map_vec_sized_graph_scohg_vert_eq by apply norm_sized_verts_vert_eq.
  done.
Qed.


#[export] Instance unit_sized_graph_to_graph_cohg_eq `{Equiv T} {n m} :
  Proper (scohg_eq ==> @cohg_eq T n m _) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  apply Heq.1.
Qed.

#[export] Instance unit_sized_graph_to_graph_cohg_vert_eq {T n m} :
  Proper (scohg_vert_eq ==> @cohg_vert_eq T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  apply Heq.1.
Qed.

#[export] Instance unit_sized_graph_to_graph_sized_isomorphic {T n m} :
  Proper (sized_isomorphic ==> @isomorphic T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  now constructor.
Qed.

#[export] Instance unit_sized_graph_to_graph_struct_sized_isomorphic {T n m} :
  Proper (struct_sized_isomorphic ==> @struct_isomorphic T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq%unit_sized_graph_to_graph_sized_isomorphic.
  apply Heq.
Qed.

#[export] Instance unit_sized_graph_to_graph_cohg_syntactic_eq `{Equiv T} {n m} :
  Proper (scohg_syntactic_eq ==> @cohg_syntactic_eq T _ n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  constructor; [done..|].
  unfold scohg_eq in *.
  destruct_and!.
  assumption.
Qed.


#[export] Instance sized_cospan_cohg_syntactic_eq {N} `{Equiv T} {n m} :
  Proper (scohg_syntactic_eq (N:=N) ==> @cohg_syntactic_eq T _ n m) sized_cospan.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  constructor; [done..|].
  unfold scohg_eq in *.
  destruct_and!.
  assumption.
Qed.


#[export] Instance sized_cospan_struct_isomorphic {N T} {n m} :
  Proper (struct_sized_isomorphic (N:=N) ==> @struct_isomorphic T n m) sized_cospan.
Proof.
  intros cohg cohg' (fv & fe & Hfv & Hfe & Heq)%sized_isomorphic_exists.
  apply (f_equal sized_cospan) in Heq.
  cbn in Heq.
  unfold struct_isomorphic.
  rewrite Heq.
  now constructor.
Qed.


Lemma sigT2_relation_f_equiv {A B} {P Q : A -> B -> Type}
  (R : forall a b, relation (P a b))
  (R' : forall a b, relation (Q a b)) (f : forall a b, P a b -> Q a b)
  `{Hf : forall a b, Proper (R a b ==> R' a b) (f a b)} :
  Proper (sigT2_relation R ==> sigT2_relation R') (λ x, existT (_, _) (f _ _ (projT2 x))).
Proof.
  intros x y Heq.
  induction Heq.
  cbn.
  constructor.
  now f_equiv.
Qed.
Lemma sigT2_relation_f_equiv_2 {A B} {P1 P2 P3 : A -> B -> Type}
  (R1 : forall a b, relation (P1 a b))
  (R2 : forall a b, relation (P2 a b))
  (R3 : forall a b, relation (P3 a b))
  {fa : A -> A -> A} {fb : B -> B -> B}
  (f : forall a b a' b', P1 a b -> P2 a' b' -> P3 (fa a a') (fb b b'))
  `{Hf : forall a b a' b', Proper (R1 a b ==> R2 a' b' ==> R3 _ _) (f a b a' b')} :
  Proper (sigT2_relation R1 ==> sigT2_relation R2
   ==> sigT2_relation R3) (λ x y, existT (_, _) (f _ _ _ _ (projT2 x) (projT2 y))).
Proof.
  intros x x' Heq y y' Heq'.
  induction Heq.
  induction Heq'.
  cbn.
  constructor.
  now f_equiv.
Qed.


Lemma sized_graph_to_graph_struct_sized_isomorphic
  {N T} {n m}
  (f : N -> nat) (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵢ scohg' ->
  (sized_graph_to_graph f scohg [≡ᵢ]ₛ sized_graph_to_graph f scohg')%cohg.
Proof.
  unfold sized_graph_to_graph.
  intros Heq%(map_vec_sized_graph_struct_sized_isomorphic (nf:=f) (λ k, fun_to_vec (λ _, ()))).
  refine (sigT2_relation_f_equiv _ _ (fun _ _ => sized_cospan)
    (Hf:=fun _ _ => sized_cospan_struct_isomorphic) _ _ Heq).
Qed.

Lemma sized_graph_to_graph_cohg_syntactic_eq {N} `{Equiv T, Equivalence T equiv} {n m}
  (f : N -> nat) (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₛ scohg' ->
  (sized_graph_to_graph f scohg [≡ₛ]ₛ sized_graph_to_graph f scohg')%cohg.
Proof.
  unfold sized_graph_to_graph.
  intros Heq%(map_vec_sized_graph_scohg_syntactic_eq (nf:=f) (λ k, fun_to_vec (λ _, ()))).
  refine (sigT2_relation_f_equiv _ _ (fun _ _ => sized_cospan)
    (Hf:=fun _ _ => sized_cospan_cohg_syntactic_eq) _ _ Heq).
Qed.



(* Notation "'cast_graph' Hn Hm cohg" :=
  (eq_rect _ (λ k, CospanHyperGraph _ k _)
    (eq_rect _ (CospanHyperGraph _ _) cohg%cohg _ Hm) _ Hn)
  (at level 10, Hn at level 9, Hm at level 9, cohg at level 9) : cohg_scope. *)


(* Notation "'cast_sized_graph' Hn Hm cohg" :=
  (eq_rect _ (λ k, SizedCospanHyperGraph _ _ k _)
    (eq_rect _ (SizedCospanHyperGraph _ _ _) cohg%scohg _ Hm) _ Hn)
  (at level 10, Hn at level 9, Hm at level 9, cohg at level 9) : scohg_scope. *)




Lemma subst_by_vec_ext_to_list {n m}
  (v : vec _ n) (w : vec _ m) :
  v =@{list _} w ->
  subst_by_vec v = subst_by_vec w.
Proof.
  intros Heq.
  apply vec_to_list_inj1 in Heq as Hnm.
  subst m.
  apply vec_to_list_inj2 in Heq.
  now subst.
Qed.

Lemma propogate_subst_ext_to_list {n m}
  (v : vec _ n) (w : vec _ m) :
  v =@{list _} w ->
  propogate_subst v =@{list _} propogate_subst w.
Proof.
  intros Heq.
  apply vec_to_list_inj1 in Heq as Hnm.
  subst m.
  apply vec_to_list_inj2 in Heq.
  now subst.
Qed.


(* Lemma vzip_vbind_cast_l {A B} {nf : A -> nat} (f : forall a, vec B (nf a))
  {n} (v w : vec A n) H K :
  nf <$> (v :> list A) = nf <$> (w :> list A) ->
  vzip (Vector.cast (vbind f v) H) (vbind f w) =
  K. *)


(*
Lemma venlarge_graph_compose_graphs_aux {T n m o} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o)
  (Hoi : nf <$> (outputs cohg :> list _) = nf <$> (inputs cohg' :> list _)) :
  (venlarge_graph f (compose_graphs_aux cohg cohg') =ₛ
  compose_graphs_aux (
    cast_graph eq_refl (sum_list_with_eq_of_fmap Hoi)
    (venlarge_graph f cohg)) (venlarge_graph f cohg'))%cohg.
Proof.
  unfold compose_graphs_aux.
  rewrite venlarge_graph_relabel_graph.
  apply mk_cohg_bundled_eq.
  - cbn -[eq_rect].
    rewrite vec_to_list_bind, vec_to_list_map.
    rewrite outputs_cast_graph, inputs_cast_graph.
    rewrite cast_id.
    cbn.
    symmetry.
    assert (f = (λ p, fun_to_vec (λ i, encode (p, fin_to_nat i)))) by admit.
    subst f.

    erewrite subst_by_vec_ext_to_list. 2:{
      apply propogate_subst_ext_to_list.
      rewrite vec_to_list_zip_with.
      rewrite vec_to_list_cast.
      rewrite 2 vec_to_list_bind.
      rewrite zip_with_bind. 2:{
        apply list_eq_Forall2 in Hoi.
        rewrite Forall2_fmap in Hoi.
        apply (Forall2_impl _ _ _ _ Hoi).
        now intros; rewrite 2 length_vec_to_list.
      }
      etransitivity. 1:{
        apply list_bind_ext_strong.
        intros ab Hab.
        apply elem_of_list_lookup in Hab as (i & Hi).
        rewrite (surjective_pairing ab) in Hi.
        apply lookup_zip_Some in Hi as [Hia Hib].
        apply (f_equal (.!! i)) in Hoi.
        rewrite 2 list_lookup_fmap, Hia, Hib in Hoi.
        cbn in Hoi.
        pose proof Hoi as [= Hnf].
        rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        rewrite zip_fmap_l, zip_fmap_r.
        cbn.
        rewrite <- Hnf.
        rewrite zip_with_diag.
        rewrite <- 2 list_fmap_compose.
        unfold compose; cbn.
        reflexivity.
      }
      etransitivity; [symmetry; apply vec_to_list_to_vec|].
      reflexivity.
    }
    rewrite vec_to_list_bind.
    rewrite list_bind_fmap.
    apply list_bind_ext, reflexivity.
    intros p.
    rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
    rewrite <- list_fmap_compose.
    unfold compose.
    rewrite
    rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
    subst f.
    cbn.
    rewrite <- list_fmap_compose.
    unfold compose.


Lemma venlarge_graph_compose_graphs_aux {T n m o} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o)
  (Hoi : nf <$> (outputs cohg :> list _) = nf <$> (inputs cohg' :> list _)) :
  (venlarge_graph f (compose_graphs_aux cohg cohg') =ₛ
  compose_graphs_aux (
    cast_graph eq_refl (sum_list_with_eq_of_fmap Hoi)
    (venlarge_graph f cohg)) (venlarge_graph f cohg'))%cohg.
Proof.
  unfold compose_graphs_aux.
  rewrite venlarge_graph_relabel_graph.
  apply mk_cohg_bundled_eq.
  - cbn -[eq_rect].
    rewrite vec_to_list_bind, vec_to_list_map.
    rewrite outputs_cast_graph, inputs_cast_graph.
    rewrite cast_id.
    cbn.
    symmetry.
    erewrite subst_by_vec_ext_to_list. 2:{
      apply propogate_subst_ext_to_list.
      rewrite vec_to_list_zip_with.
      rewrite vec_to_list_cast.
      rewrite 2 vec_to_list_bind.
      rewrite zip_with_bind. 2:{
        apply list_eq_Forall2 in Hoi.
        rewrite Forall2_fmap in Hoi.
        apply (Forall2_impl _ _ _ _ Hoi).
        now intros; rewrite 2 length_vec_to_list.
      }
      etransitivity; [symmetry; apply vec_to_list_to_vec|].
      reflexivity.
    }
    rewrite vec_to_list_bind.
    rewrite list_bind_fmap.
    apply list_bind_ext, reflexivity.
    intros p.
    assert (f = (λ p, fun_to_vec (λ i, encode (p, fin_to_nat i)))) by admit.
    subst f.
    cbn.
    rewrite (vec_to_list_fun_to_vec (λ i, encode (p, i))).
    rewrite <- list_fmap_compose.
    unfold compose. *)


(* FIXME: Move *)
From TensorRocq Require Import GraphRewriting.
Import list.

Lemma propogate_subst_vmaps_diag {A} (f g : A -> positive)
  `{Hf : !Inj eq eq f}
  (Hfg : (forall a b, f a <> g b) \/ (forall a, f a = g a)) {n} (v : vec A n) : NoDup v ->
  propogate_subst (vzip (vmap f v) (vmap g v)) =
  vzip (vmap f v) (vmap g v).
Proof.
  revert v.
  induction n; [now intros v; induction v using vec_0_inv|].
  intros v.
  induction v as [a v] using vec_S_inv.
  cbn.
  intros [Ha Hv]%NoDup_cons.
  f_equal.

  rewrite <- IHn at 2 by done.
  f_equal.
  apply vec_eq.
  intros i.
  rewrite vlookup_map, vlookup_zip_with, 2 vlookup_map.
  simpl.
  rewrite 2 fn_lookup_singleton_ne_strong; [done|..].
  - intros Hfga.
    destruct Hfg as [Hfg|]; [|naive_solver].
    apply Hfg.
  - intros _.
    apply not_inj.
    intros ->.
    apply Ha.
    apply elem_of_list_lookup.
    exists i.
    now rewrite lookup_vec_to_list_fin.
Qed.

Lemma fin_elements_eq_fun_to_vec n :
  fin_elements n = fun_to_vec id.
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  rewrite <- vec_to_list_map, vmap_fun_to_vec.
  done.
Qed.

Lemma vec_to_list_fun_to_vec_gen
  {A n} (f : fin n -> A) :
  vec_to_list (fun_to_vec f) = f <$> fin_elements _.
Proof.
  rewrite fin_elements_eq_fun_to_vec.
  rewrite <- vec_to_list_map, vmap_fun_to_vec.
  done.
Qed.


Lemma NoDup_fun_to_vec {A n} (f : fin n -> A) (Hf : Inj eq eq f) :
  NoDup (fun_to_vec f).
Proof.
  rewrite vec_to_list_fun_to_vec_gen.
  apply (NoDup_fmap _), fin_elements_NoDup.
Qed.

Lemma subst_by_vec_id' {n} (v : vec positive n) p :
  subst_by_vec (vzip v v) p = p.
Proof.
  induction v; [done|].
  cbn.
  now rewrite fn_lookup_singleton_id.
Qed.


Lemma subst_by_vec_vmaps_diag `{EqDecision A} (f g : A -> positive)
  {Hf : Inj eq eq f} (Hfg : (forall a b, f a <> g b) \/ (forall a, f a = g a))
   {n} (v : vec A n) : forall p,
  (subst_by_vec (vzip (vmap f v) (vmap g v)) (f p) =
  if decide (p ∈ vec_to_list v) then
    g p
  else f p) /\
  subst_by_vec (vzip (vmap f v) (vmap g v)) (g p) = g p.
Proof.
  induction n as [|n IHn]; [induction v using vec_0_inv; easy|].
  intros p.
  case_decide as Hp.
  2:{
    split.
    - apply subst_by_vec_notin.
      rewrite vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
      rewrite vec_to_list_map.
      apply not_elem_of_list_fmap.
      intros ? ?; apply not_inj.
      congruence.
    - destruct Hfg as [Hfg|Hfg].
      + apply subst_by_vec_notin.
        rewrite vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
        rewrite vec_to_list_map.
        apply not_elem_of_list_fmap.
        naive_solver.
      + rewrite (Vector.map_ext _ _ _ _ Hfg).
        apply subst_by_vec_id'.
  }
  induction v as [q v] using vec_S_inv.
  cbn.
  rewrite fn_lookup_singleton_case.
  rewrite (decide_ext _ _ _ _ (inj_iff f q p)).
  case_decide.
  - subst.
    split.
    + apply IHn.
    + rewrite fn_lookup_singleton_ne_strong; [apply IHn|].
      naive_solver.
  - rewrite (IHn _ _).1.
    cbn in Hp.
    rewrite elem_of_cons in Hp.
    rewrite decide_True by now destruct Hp; [congruence|].
    split; [done|].
    rewrite fn_lookup_singleton_ne_strong by naive_solver.
    apply IHn.
Qed.

Lemma subst_by_vec_propogate_subst_vmaps_diag `{EqDecision A} (f g : A -> positive)
  {Hf : Inj eq eq f} (Hfg : (forall a b, f a <> g b) \/ (forall a, f a = g a))
   {n} (v : vec A n) : NoDup v -> forall p,
  (subst_by_vec (propogate_subst (vzip (vmap f v) (vmap g v))) (f p) =
  if decide (p ∈ vec_to_list v) then
    g p
  else f p) /\
  subst_by_vec (propogate_subst (vzip (vmap f v) (vmap g v))) (g p) = g p.
Proof.
  intros Hv p.
  rewrite propogate_subst_vmaps_diag by done.
  now apply subst_by_vec_vmaps_diag.
Qed.

Lemma vertices_add_top_loop {T n m} (cohg : CospanHyperGraph T (S n) (S m)) :
  vertices (add_top_loop cohg) =
  set_map {[vhd cohg.(outputs) := vhd cohg.(inputs)]} (vertices cohg).
Proof.
  unfold add_top_loop.
  rewrite vertices_relabel_graph.
  apply leibniz_equiv_iff.
  apply set_subseteq_antisymm.
  - apply set_map_mono; [reflexivity|].
    destruct cohg as [hg ins outs].
    induction ins as [i ins] using vec_S_inv.
    induction outs as [o outs] using vec_S_inv.
    cbn.
    rewrite 2 vertices_vertices_hg_decomp.
    cbn -[union].
    rewrite vertices_hg_add_vertices.
    rewrite 2 list_to_set_app_L.
    set_solver +.
  - rewrite 2 vertices_vertices_hg_decomp.
    cbn.
    rewrite vertices_hg_add_vertices.
    rewrite 2 list_to_set_app_L.
    rewrite set_map_union.
    apply union_subseteq.
    split; [apply set_map_mono; set_solver +|].
    induction (inputs cohg) as [i ins] using vec_S_inv.
    induction (outputs cohg) as [o outs] using vec_S_inv.
    cbn -[union].
    rewrite 3 set_map_union.
    apply union_least; apply union_least;
      cycle 2; [|now apply set_map_mono; set_solver +..].
    rewrite set_map_singleton.
    rewrite fn_lookup_singleton.
    rewrite 2 set_map_union.
    rewrite set_map_singleton.
    rewrite fn_lookup_singleton_r.
    set_solver +.
Qed.


Lemma vertices_add_top_loops {T n m o} (cohg : CospanHyperGraph T (n + m) (n + o)) :
  vertices (add_top_loops cohg) =
  set_map (subst_by_vec (propogate_subst
    (vzip (vsplitl cohg.(outputs)) (vsplitl cohg.(inputs))))) (vertices cohg).
Proof.
  induction n.
  - cbn.
    now rewrite set_map_id_L.
  - cbn.
    rewrite IHn.
    rewrite vertices_add_top_loop.
    rewrite set_map_compose_L.
    rewrite vhd_vzip_with.
    apply set_map_ext_L.
    intros k _.
    cbn.
    rewrite vtl_vzip_with.
    rewrite <- vzip_map.
    rewrite 2 vhd_vsplitl.
    rewrite 2 vsplitl_map, 2 vtl_vsplitl.
    done.
Qed.

(* FIXME: Move *)
Lemma fn_lookup_singleton_irrel `{EqDecision A} {B} (f : A -> B)
  (a b c : A) :
  f a = f b ->
  f ({[a := b]} c) = f c.
Proof.
  rewrite fn_lookup_singleton_case.
  case_decide; congruence.
Qed.
Lemma fn_lookup_singleton_cancel `{EqDecision A} {B} (f : A -> B)
  (a b c : A) :
  f a = f b ->
  f ({[a := b]} ({[b := a]} c)) = f c.
Proof.
  intros Hab.
  now rewrite 2 (fn_lookup_singleton_irrel f).
Qed.

Lemma set_bind_map `{FinSet A SA, FinSet B SB, SemiSet C SC}
  (f : A -> SB) (g : B -> C) (X : SA) :
  set_map g (set_bind f X :> SB) ≡@{SC}
  set_bind (λ a, set_map g (f a)) X.
Proof.
  set_solver.
Qed.

Lemma set_bind_map_L `{FinSet A SA, FinSet B SB, SemiSet C SC,
  !LeibnizEquiv SC}
  (f : A -> SB) (g : B -> C) (X : SA) :
  set_map g (set_bind f X :> SB) =@{SC}
  set_bind (λ a, set_map g (f a)) X.
Proof.
  unfold_leibniz.
  apply set_bind_map.
Qed.

Lemma set_map_bind `{FinSet A SA, FinSet B SB, SemiSet C SC}
  (f : A -> B) (g : B -> SC) (X : SA) :
  set_bind g (set_map f X :> SB) ≡@{SC}
  set_bind (g ∘ f) X.
Proof.
  set_solver.
Qed.

Lemma set_map_bind_L `{FinSet A SA, FinSet B SB, SemiSet C SC,
  !LeibnizEquiv SC}
  (f : A -> B) (g : B -> SC) (X : SA) :
  set_bind g (set_map f X :> SB) =@{SC}
  set_bind (g ∘ f) X.
Proof.
  unfold_leibniz.
  apply set_map_bind.
Qed.

Lemma vertices_sized_graph_to_graph
  {N T n m} (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m) :
  vertices (sized_graph_to_graph f scohg) =
  set_bind (λ i, list_to_set
    ((encode ∘ (i,.)) <$> seq 0 (default 0 (f <$> scohg.(sized_map) !! i
      )))) (vertices scohg).
Proof.
  cbn.
  rewrite vertices_venlarge_graph.
  apply leibniz_equiv_iff, set_bind_ext, reflexivity.
  intros k _ _.
  cbn.
  rewrite (vec_to_list_fun_to_vec (λ i, encode (k,i))).
  done.
Qed.


Lemma sized_graph_to_graph_add_top_loop {N T n m}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  (scohg.(sized_map) !! (vhd scohg.(inputs))) =
  (scohg.(sized_map) !! (vhd scohg.(outputs))) ->
  exists (eql :
   _ = default 0 (f <$> scohg.(sized_map) !! (vhd scohg.(inputs)))
    + (sum_list_with (λ p, default 0 (f <$> sized_map scohg !! p)) (vtl scohg.(inputs))))
    (eqr :
   _ = default 0 (f <$> scohg.(sized_map) !! (vhd scohg.(inputs)))
    + (sum_list_with (λ p, default 0 (f <$> sized_map scohg !! p)) (vtl scohg.(outputs)))),
  (sized_graph_to_graph f (sized_add_top_loop scohg) [≡ᵥ]ₛ
  add_top_loops (n:=default 0 (f <$> scohg.(sized_map) !! (vhd scohg.(inputs))))
    (cast_sized_graph eql eqr (sized_graph_to_graph f scohg)))%cohg.
Proof.
  intros Heq.
  destruct scohg as [[hedges ins outs] smap].
  induction ins as [i ins] using vec_S_inv.
  induction outs as [o outs] using vec_S_inv.
  cbn [inputs outputs sized_map sized_cospan vhd vtl Vector.caseS] in *.
  exists eq_refl.
  cbn [vec_to_list sum_list_with].
  apply exists_by_forall; [now rewrite Heq|].
  intros eqr.
  unfold sized_add_top_loop.
  cbn [inputs outputs sized_map sized_cospan vhd vtl Vector.caseS] in *.

  assert (Haux1 : ∀ (q : positive) (k : nat), k < default 0 (f <$> smap !! q)
  -> encode (({[o := i]} :> positive -> positive) q, k) = subst_by_vec
      (propogate_subst (vzip_with pair (fun_to_vec (λ a : fin (default 0 (f <$> smap !! i)), encode (o, fin_to_nat a)))
            (fun_to_vec (λ i0 : fin (default 0 (f <$> smap !! i)), encode (i, fin_to_nat i0))))) (encode (q, k))).
  1:{
    intros q k Hk.

    symmetry.
    let lem := open_constr:(vmap_fun_to_vec fin_to_nat (encode ∘ (o,.))) in
    let T := type of lem in
    let T' := eval unfold compose in T in
    rewrite <- (lem : T').
    let lem := open_constr:(vmap_fun_to_vec fin_to_nat (encode ∘ (i,.))) in
    let T := type of lem in
    let T' := eval unfold compose in T in
    rewrite <- (lem : T').
    rewrite fn_lookup_singleton_case.
    case_decide.
    + subst q.
      etransitivity; [
      apply (subst_by_vec_propogate_subst_vmaps_diag
        (λ x, (encode (o, x))) _)|].
      * destruct_decide (decide (o = i)); [now subst; right|].
        left.
        intros ? ?; now apply not_inj; congruence.
      * apply NoDup_fun_to_vec, _.
      * apply decide_True.
        change (@fin_to_nat ?n) with (λ p, @fin_to_nat n (id p)).
        setoid_rewrite (vec_to_list_fun_to_vec (@id nat)).
        rewrite list_fmap_id.
        rewrite elem_of_seq.
        split; [lia|].
        now rewrite Heq.
    + rewrite (propogate_subst_vmaps_diag _ _).
      * rewrite subst_by_vec_notin; [done|].
        rewrite vec_to_list_zip_with, fst_zip by now rewrite 2 length_vec_to_list.
        rewrite vec_to_list_map.
        apply not_elem_of_list_fmap.
        intros ? ?; apply not_inj.
        congruence.
      * destruct_decide (decide (o = i)); [now subst; right|].
        left.
        intros ? ?; now apply not_inj; congruence.
      * apply NoDup_fun_to_vec, _.
  }

  assert (Haux : forall x : positive,
  (λ p0 : positive, fun_to_vec
    (λ i0 : fin (default 0 (f <$> map_relabel_one i o smap !! p0)),
      encode (p0, fin_to_nat i0)))
   ({[o := i]} x) =@{list _}
  subst_by_vec
    (propogate_subst
       (vzip_with pair
          (fun_to_vec (λ a : fin (default 0 (f <$> smap !! i)), encode (o, fin_to_nat a)))
          (fun_to_vec (λ i0 : fin (default 0 (f <$> smap !! i)), encode (i, fin_to_nat i0))))) <$>
  (vec_to_list (fun_to_vec (λ i0 : fin (default 0 (f <$> smap !! x)), encode (x, fin_to_nat i0))))).
  1:{
    intros q.
    cbn.
    rewrite <- vec_to_list_map.
    apply (list_eq_same_length _ _ _ eq_refl).
    1:{
      rewrite 2 length_vec_to_list.
      rewrite lookup_map_relabel_one.
      now rewrite (fn_lookup_singleton_cancel (smap !!.)).
    }
    rewrite length_vec_to_list.
    intros k a b Hk.
    rewrite <- (fin_to_nat_to_fin _ _ Hk).
    rewrite lookup_vec_to_list_fin.
    rewrite fin_to_nat_to_fin.
    rewrite lookup_vec_to_list.
    rewrite lookup_map_relabel_one.
    rewrite (fn_lookup_singleton_cancel (smap !!.)) by done.
    case_guard; [|easy].
    cbn.
    rewrite vlookup_map, 2 lookup_fun_to_vec.
    rewrite 2 fin_to_nat_to_fin.
    intros [= <-].
    intros [= <-].
    now rewrite Haux1.
  }

  apply mk_bundled_cohg_vert_eq.
  - rewrite inputs_add_top_loops.
    cbn.
    unshelve erewrite 2 cast_app; [congruence..|].
    rewrite 3 cast_id.
    rewrite 2 vsplitl_app, vsplitr_app.
    rewrite cast_fun_to_vec.
    erewrite fun_to_vec_ext_mor by
      now intros ?; rewrite fin_to_nat_cast.
    rewrite vbind_map, vmap_bind.
    rewrite vec_to_list_cast.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext, reflexivity.
    intros p.
    rewrite vmap_fun_to_vec.
    apply fun_to_vec_ext_to_list.
    apply exists_by_forall.
    1:{
      rewrite lookup_map_relabel_one.
      now rewrite (fn_lookup_singleton_cancel (smap !!.)).
    }
    intros Heq'.
    intros q.
    rewrite Haux1 by now apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt q));
      rewrite lookup_map_relabel_one, (fn_lookup_singleton_cancel (smap !!.)) by done.
    cbn.
    rewrite fin_to_nat_cast.
    done.
  - rewrite outputs_add_top_loops.
    cbn.
    unshelve erewrite 2 cast_app; [congruence..|].
    rewrite 3 cast_id.
    rewrite 2 vsplitl_app, vsplitr_app.
    rewrite cast_fun_to_vec.
    erewrite fun_to_vec_ext_mor by
      now intros ?; rewrite fin_to_nat_cast.
    rewrite vbind_map, vmap_bind.
    rewrite vec_to_list_cast.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext, reflexivity.
    intros p.
    rewrite vmap_fun_to_vec.
    apply fun_to_vec_ext_to_list.
    apply exists_by_forall.
    1:{
      rewrite lookup_map_relabel_one.
      rewrite 2 fn_lookup_singleton_case.
      do 2 case_decide; congruence.
    }
    intros Heq'.
    intros q.
    cbn.
    rewrite fin_to_nat_cast.
    apply Haux1.
    now apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt q));
      rewrite lookup_map_relabel_one, (fn_lookup_singleton_cancel (smap !!.)) by done.

  - rewrite hedges_add_top_loops.
    unfold relabel_hg, hg_add_vertices.
    cbn [hyperedges].
    cbn -[sized_graph_to_graph].
    unshelve erewrite 2 cast_app; [congruence..|].
    rewrite 3 cast_id.
    rewrite 2 vsplitl_app.
    rewrite cast_fun_to_vec.
    erewrite fun_to_vec_ext_mor by
      now intros ?; rewrite fin_to_nat_cast.

    cbn.
    rewrite <- 2 map_fmap_compose.
    apply map_fmap_ext.
    intros p [[t ti] to] _.
    cbn.

    rewrite 2 list_bind_fmap, 2 list_fmap_bind.
    eenough (Hen : _) by
    (f_equal; [f_equal|]; (apply list_bind_ext, reflexivity; apply Hen)).
    apply Haux.
  - etransitivity; [apply (vertices_sized_graph_to_graph f)|].
    cbn [sized_cospan sized_map].
    rewrite vertices_add_top_loop.
    cbn [inputs outputs vhd Vector.caseS].
    rewrite vertices_add_top_loops.
    unfold cast_sized_graph; cbn [sized_cospan].
    rewrite vertices_cast_graph.
    etransitivity; [|apply f_equal, symmetry,
      (vertices_sized_graph_to_graph f (mk_scohg
        (i ::: ins -> hedges <- o ::: outs) smap))].
    rewrite inputs_cast_graph, outputs_cast_graph.
    cbn.

    unshelve erewrite 2 cast_app; [congruence..|].
    rewrite 3 cast_id.
    rewrite 2 vsplitl_app.
    rewrite cast_fun_to_vec.
    erewrite fun_to_vec_ext_mor by
      now intros ?; rewrite fin_to_nat_cast.

    rewrite set_bind_map_L, set_map_bind_L.
    apply leibniz_equiv_iff, set_bind_ext, reflexivity.
    intros k _ _.
    cbn.
    rewrite set_map_list_to_set_L.
    apply eq_reflexivity, f_equal.
    rewrite <- list_fmap_compose.
    rewrite lookup_map_relabel_one, (fn_lookup_singleton_cancel (smap !!.)) by done.
    apply list_fmap_ext.
    intros _ q Hq%elem_of_list_lookup_2%elem_of_seq.
    cbn.
    now apply Haux1.
Qed.

(* FIXME: Move *)
Add Parametric Morphism {T n m n' m'} (Hn : n = n') (Hm : m = m') :
  (cast_graph (T:=T) Hn Hm) with signature cohg_vert_eq ==> cohg_vert_eq as
  cast_graph_cohg_vert_eq.
Proof.
  subst.
  intros; now rewrite 2 cast_graph_id.
Qed.


Lemma add_top_loops_assoc {T n m o p}
  (cohg : CospanHyperGraph T (n + (m + o)) (n + (m + p))) :
  (add_top_loops (add_top_loops cohg) =ₛ
  add_top_loops (cast_graph (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) cohg))%cohg.
Proof.
  induction n.
  - cbn.
    now rewrite cast_graph_id.
  - cbn.
    rewrite IHn.
    rewrite cast_graph_add_top_loop.
    do 4 f_equal; apply proof_irrel.
Qed.


Lemma bundled_cohg_vert_eq_iff_cast {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (cohg [≡ᵥ]ₛ cohg' <->
  exists Hn Hm, cast_graph Hn Hm cohg ≡ᵥ cohg')%cohg.
Proof.
  split.
  - intros (Heq & Heqv)%sigT2_relation_alt.
    exists (f_equal fst Heq), (f_equal snd Heq).
    cbn in Heq.
    assert (n = n') as <- by congruence.
    assert (m = m') as <- by congruence.
    cbn in *.
    rewrite cast_graph_id.
    rewrite Heqv, eq_rect_r_to_cast_graph, cast_graph_id.
    done.
  - intros (<- & <- & Heqv).
    constructor.
    now rewrite cast_graph_id in Heqv.
Qed.

(* FIXME: Move *)
Lemma vsplitr_vtl {A n m} (v : vec A ((S n) + m)) :
  vsplitr (vtl v) = vsplitr v.
Proof.
  induction v as [vl vr] using vec_add_inv.
  rewrite vsplitr_app.
  induction vl as [vh vl] using vec_S_inv.
  cbn.
  apply vsplitr_app.
Qed.

Lemma add_top_loops_proper_cast {T n n' m m'}
  (cohg : CospanHyperGraph T (n + m) (n + m'))
  (cohg' : CospanHyperGraph T (n' + m) (n' + m')) :
  ((exists Hn, cast_graph (f_equal (λ k, k + m) Hn) (f_equal (λ k, k + m') Hn) cohg
    ≡ᵥ cohg') ->
  add_top_loops cohg ≡ᵥ add_top_loops cohg')%cohg.
Proof.
  intros (<- & Heqv).
  rewrite cast_graph_id in Heqv.
  now f_equiv.
Qed.

Lemma vsplitl_cons {A n m} a (v : vec A (n + m)) :
  vsplitl (n:=S n) (a ::: v) = a ::: vsplitl v.
Proof.
  induction v using vec_add_inv.
  rewrite vsplitl_app.
  apply (vsplitl_app (a ::: _)).
Qed.

Lemma vsplitr_cons {A n m} a (v : vec A (n + m)) :
  vsplitr (n:=S n) (a ::: v) = vsplitr v.
Proof.
  induction v using vec_add_inv.
  rewrite vsplitr_app.
  apply (vsplitr_app (a ::: _)).
Qed.

Lemma sized_graph_to_graph_add_top_loops {N T n m m'}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T (n + m) (n + m')) :
  (scohg.(sized_map) !!.) <$> (vec_to_list (vsplitl scohg.(inputs))) =
  (scohg.(sized_map) !!.) <$> (vec_to_list (vsplitl scohg.(outputs))) ->
  exists (eql :
   _ = sum_list_with (λ p, default 0 (f <$> scohg.(sized_map) !! p)) (vsplitl scohg.(inputs))
    + (sum_list_with (λ p, default 0 (f <$> sized_map scohg !! p)) (vsplitr scohg.(inputs))))
    (eqr :
   _ = sum_list_with (λ p, default 0 (f <$> scohg.(sized_map) !! p)) (vsplitl scohg.(inputs))
    + (sum_list_with (λ p, default 0 (f <$> sized_map scohg !! p)) (vsplitr scohg.(outputs)))),
  (sized_graph_to_graph f (sized_add_top_loops scohg) [≡ᵥ]ₛ
  add_top_loops
    (cast_graph eql eqr (sized_graph_to_graph f scohg)))%cohg.
Proof.
  induction n.
  - intros _.
    exists eq_refl, eq_refl.
    rewrite cast_graph_id.
    done.
  - cbn [sized_add_top_loops].
    intros Heq.
    specialize (IHn (sized_add_top_loop scohg)).
    tspecialize IHn. 1:{
      cbn -[Nat.add].
      change (inputs scohg) with (inputs scohg). (* Fix dimensions *)
      change (outputs scohg) with (outputs scohg). (* Fix dimensions *)
      induction (inputs scohg) as [il ir] using vec_add_inv.
      induction (outputs scohg) as [ol or] using vec_add_inv.
      induction il as [i il] using vec_S_inv.
      induction ol as [o ol] using vec_S_inv.
      rewrite 2 vsplitl_app in Heq.
      cbn -[map_relabel_one].
      rewrite 2 vsplitl_map, 2 vsplitl_app.
      rewrite <- 2 vec_to_list_map, 2 Vector.map_map.
      f_equal.
      apply vec_eq.
      intros p.
      rewrite 2 vlookup_map.
      rewrite 2 lookup_map_relabel_one.
      cbn in Heq.
      injection Heq as Hio Heqs.
      rewrite 2 (fn_lookup_singleton_cancel (_ !!.)) by done.
      rewrite <- 2 vec_to_list_map in Heqs.
      apply vec_to_list_inj2 in Heqs.
      apply (f_equal (.!!!p)) in Heqs.
      now rewrite 2 vlookup_map in Heqs.
    }
    destruct IHn as (eql & eqr & Heqv).
    pose proof Heq as Heq'.
    rewrite <- 2 vec_to_list_map in Heq'.
    apply vec_to_list_inj2 in Heq'.
    apply (f_equal vhd) in Heq' as Hhd.
    rewrite 2 vhd_vmap, 2 vhd_vsplitl in Hhd.
    pose proof Hhd as Hhd'.
    apply (sized_graph_to_graph_add_top_loop f scohg) in Hhd as (eql' & eqr' & Heqv').
    apply exists_by_forall.
    1: {
      now rewrite <- sum_list_with_app, <- vec_to_list_app, app_vsplit.
    }
    intros EQL.
    apply exists_by_forall.
    1: {
      rewrite <- (app_vsplit scohg.(outputs)) at 1.
      rewrite vec_to_list_app, sum_list_with_app.
      f_equal.
      apply sum_list_with_eq_of_fmap.
      apply (f_equal (fmap (λ p, default 0 (f <$> p)))) in Heq.
      rewrite <- 2 list_fmap_compose in Heq.
      symmetry; apply Heq.
    }
    intros EQR.
    rewrite Heqv.
    apply sigT2_relation_alt in Heqv' as (Heqs & Heqv').
    etransitivity.
    1:{
      instantiate (1:=(graph_to_pair_bundled _)).
      constructor.
      apply add_top_loops_proper.
      apply cast_graph_cohg_vert_eq_Proper.
      apply Heqv'.
    }
    rewrite eq_rect_r_to_cast_graph.
    rewrite cast_graph_cast_graph.
    cbn [projT2 graph_to_pair_bundled].
    rewrite cast_graph_add_top_loops.
    rewrite add_top_loops_assoc.
    rewrite cast_graph_cast_graph.
    unfold cast_sized_graph.
    cbn [sized_cospan].
    rewrite cast_graph_cast_graph.
    apply bundled_cohg_vert_eq_iff_cast.
    apply exists_by_forall.
    1:{
      apply sum_list_with_eq_of_fmap.
      rewrite <- 2 vec_to_list_map.
      f_equal.
      apply vec_eq.
      intros i.
      rewrite 2 vlookup_map.
      cbn.
      rewrite vsplitr_map.
      rewrite vsplitr_vtl.
      rewrite vlookup_map.
      rewrite lookup_map_relabel_one.
      rewrite (fn_lookup_singleton_cancel (_ !!.)) by done.
      done.
    }
    intros EQL'.
    apply exists_by_forall.
    1:{
      apply sum_list_with_eq_of_fmap.
      rewrite <- 2 vec_to_list_map.
      f_equal.
      apply vec_eq.
      intros i.
      rewrite 2 vlookup_map.
      cbn.
      rewrite vsplitr_map.
      rewrite vsplitr_vtl.
      rewrite vlookup_map.
      rewrite lookup_map_relabel_one.
      rewrite (fn_lookup_singleton_cancel (_ !!.)) by done.
      done.
    }
    intros EQR'.
    rewrite cast_graph_add_top_loops, cast_graph_cast_graph.
    apply add_top_loops_proper_cast.
    apply exists_by_forall.
    1:{
      rewrite (Vector.eta (inputs scohg)).
      rewrite vsplitl_cons.
      cbn [vec_to_list sum_list_with].
      f_equal.
      apply sum_list_with_eq_of_fmap.
      rewrite <- 2 vec_to_list_map.
      f_equal.
      apply vec_eq.
      intros i.
      rewrite 2 vlookup_map.
      cbn.
      rewrite vsplitl_map.
      rewrite vlookup_map.
      rewrite lookup_map_relabel_one.
      rewrite (fn_lookup_singleton_cancel (_ !!.)) by done.
      done.
    }
    intros EQM.
    rewrite cast_graph_cast_graph.
    apply eq_reflexivity.
    f_equal; apply proof_irrel.
Qed.


Lemma enlarge_hypergraph_union {T} f (hg hg' : HyperGraph T) :
  enlarge_hypergraph f (hg ∪ hg') =
  enlarge_hypergraph f hg ∪ enlarge_hypergraph f hg'.
Proof.
  apply hg_ext.
  - apply map_fmap_union.
  - cbn.
    apply set_bind_union_L.
Qed.

Lemma graph_to_pair_bundled_apply2 {T T' T''}
  {fn : nat -> nat -> nat} {fm : nat -> nat -> nat}
  (f : forall n m n' m',
    CospanHyperGraph T n m -> CospanHyperGraph T' n' m' ->
    CospanHyperGraph T'' (fn n n') (fm m m'))
  {n m n' m'} (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T' n' m') :
  (f n m n' m' cohg cohg' =ₛ
  (λ x y, f _ _ _ _ (projT2 x) (projT2 y)) (graph_to_pair_bundled cohg)
    (graph_to_pair_bundled cohg'))%cohg.
Proof.
  done.
Qed.



Lemma venlarge_graph_reindex_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  (cohg : CospanHyperGraph T n m) :
  venlarge_graph f (reindex_graph g cohg) =
  reindex_graph g (venlarge_graph f cohg).
Proof.
  apply cohg_ext; [|done..].
  cbn.
  apply enlarge_hypergraph_reindex_hg.
Qed.


(* FIXME: Put this in GraphRewriting, overwriting existing lemma *)

Lemma reindex_is_isomorphic {T n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T n m) :
  isomorphic (reindex_graph f cohg) cohg.
Proof.
  symmetry.
  rewrite isomorphic_exists.
  exists id, f.
  rewrite relabel_graph_id.
  split; easy + apply _.
Qed.

Lemma relabel_is_isomorphic {T n m} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (cohg : CospanHyperGraph T n m) :
  isomorphic (relabel_graph f cohg) cohg.
Proof.
  symmetry.
  rewrite isomorphic_exists.
  exists f, id.
  rewrite reindex_graph_id.
  split; easy + apply _.
Qed.

Lemma relabel_graph_venlarge_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  (cohg : CospanHyperGraph T n m) :
  relabel_graph g (venlarge_graph f cohg) =
  venlarge_graph (λ p, vmap g (f p)) cohg.
Proof.
  apply cohg_ext.
  - cbn.
    rewrite relabel_hg_enlarge_hypergraph.
    apply enlarge_hypergraph_ext.
    intros i.
    now rewrite vec_to_list_map.
  - cbn.
    now rewrite vmap_bind.
  - cbn.
    now rewrite vmap_bind.
Qed.

Lemma venlarge_graph_isomorphic_of_map {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  `{Hg : !Inj eq eq g} (cohg : CospanHyperGraph T n m) :
  isomorphic (venlarge_graph (λ p, vmap g (f p)) cohg) (venlarge_graph f cohg).
Proof.
  rewrite <- relabel_graph_venlarge_graph.
  now apply relabel_is_isomorphic.
Qed.
(* FIXME: Move *)
Lemma enlarge_hypergraph_ext_strong {T} (f g : positive -> list positive)
  (hg : HyperGraph T) :
  (forall i, i ∈ vertices_hg hg -> f i = g i) ->
  enlarge_hypergraph f hg = enlarge_hypergraph g hg.
Proof.
  intros Hfg.
  apply hg_ext.
  - cbn.
    apply map_fmap_ext.
    intros i tio Htio.
    f_equal; [f_equal|]; apply list_bind_ext_strong; intros; apply Hfg;
    rewrite elem_of_vertices_hg; set_solver.
  - cbn.
    setoid_rewrite elem_of_vertices_hg in Hfg.
    set_unfold.
    firstorder first [rewrite Hfg in * by auto|rewrite <- Hfg in * by auto]; eauto.
Qed.

Lemma venlarge_graph_ext_strong {T n m} {nf : positive -> nat}
  (f g : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) :
  (forall i, i ∈ vertices cohg -> f i = g i) ->
  venlarge_graph f cohg = venlarge_graph g cohg.
Proof.
  intros Hfg.
  apply cohg_ext.
  - cbn.
    apply enlarge_hypergraph_ext_strong.
    rewrite vertices_vertices_hg_decomp in Hfg.
    intros; f_equal; apply Hfg.
    now apply elem_of_union_l.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong.
    intros i Hi; f_equal; apply Hfg;
    set_solver + Hi.
  - cbn.
    apply vec_to_list_inj2.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong.
    intros i Hi; f_equal; apply Hfg;
    set_solver + Hi.
Qed.


Lemma venlarge_graph_ext_strong' {T n m} {nf ng : positive -> nat}
  (f : forall p, vec positive (nf p))
  (g : forall p, vec positive (ng p))
  (cohg : CospanHyperGraph T n m) :
  (forall i, i ∈ vertices cohg -> f i =@{list _} g i) ->
  (venlarge_graph f cohg =ₛ venlarge_graph g cohg)%cohg.
Proof.
  intros Hfg.
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong.
    intros i Hi; apply Hfg;
    set_solver + Hi.
  - cbn.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong.
    intros i Hi; apply Hfg;
    set_solver + Hi.
  - apply enlarge_hypergraph_ext_strong.
    rewrite vertices_vertices_hg_decomp in Hfg.
    intros; f_equal; apply Hfg.
    now apply elem_of_union_l.
Qed.


Lemma venlarge_graph_stack_graphs_aux {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (* hyperedges cohg ##ₘ hyperedges cohg' -> *)
  (venlarge_graph f (stack_graphs_aux cohg cohg') =ₛ
  stack_graphs_aux (venlarge_graph f cohg) (venlarge_graph f cohg'))%cohg.
Proof.
  (* intros Hdisj. *)
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    apply enlarge_hypergraph_union.
Qed.

Lemma venlarge_graph_stack_graphs' {T n m n' m'} {nfl nfr : positive -> nat}
  (fl : forall p, vec positive (nfl p))
  (fr : forall p, vec positive (nfr p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (stack_graphs (venlarge_graph fl cohg) (venlarge_graph fr cohg') [≡ᵢ]ₛ
  venlarge_graph (@pos_case (λ p, vec positive (pos_case nfl nfr 0 p))
    (λ p, vmap (bcons false) (fl p))
    (λ p, vmap (bcons true) (fr p)) [#]) (stack_graphs cohg cohg'))%cohg.
Proof.
  unfold stack_graphs.
  rewrite venlarge_graph_stack_graphs_aux.
  symmetry.
  rewrite graph_to_pair_bundled_apply2.
  rewrite 2 venlarge_graph_relabel_graph, 2 venlarge_graph_reindex_graph.
  cbn.
  constructor.
  rewrite stack_graphs_aux_to_stack_graphs_disjoint.
  2:{
    cbn.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 (vertices_reindex_graph _).
    rewrite 2 vertices_venlarge_graph.
    unfold compose.
    set_unfold.
    setoid_rewrite vec_to_list_map.
    set_solver.
  }
  rewrite stack_graphs_aux_to_stack_graphs_disjoint.
  2:{
    cbn.
    apply map_disjoint_fmap.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 vertices_relabel_graph.
    set_solver.
  }
  apply stack_graphs_struct_isomorphic_Proper.
  - rewrite (reindex_is_isomorphic _).
    rewrite <- relabel_graph_venlarge_graph.
    rewrite (relabel_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
  - rewrite (reindex_is_isomorphic _).
    rewrite <- relabel_graph_venlarge_graph.
    rewrite (relabel_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
Qed.

Lemma venlarge_graph_stack_graphs'' {T n m n' m'} {nfl nfr : positive -> nat}
  (fl : forall p, vec positive (nfl p))
  (fr : forall p, vec positive (nfr p))
  (n0 : nat) (v0 : vec positive n0)
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m')
  (Hflr : forall p q, vec_to_list (fl p) ## vec_to_list (fr q)) :
  (stack_graphs (venlarge_graph fl cohg) (venlarge_graph fr cohg') [≡ᵢ]ₛ
  venlarge_graph (@pos_case (λ p, vec positive (pos_case nfl nfr n0 p))
    (λ p, (fl p))
    (λ p, (fr p)) v0) (stack_graphs cohg cohg'))%cohg.
Proof.
  unfold stack_graphs.
  rewrite venlarge_graph_stack_graphs_aux.
  symmetry.
  rewrite graph_to_pair_bundled_apply2.
  rewrite 2 venlarge_graph_relabel_graph, 2 venlarge_graph_reindex_graph.
  cbn.
  constructor.
  rewrite stack_graphs_aux_to_stack_graphs_disjoint.
  2:{
    cbn.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 (vertices_reindex_graph _).
    rewrite 2 vertices_venlarge_graph.
    set_solver.
  }
  rewrite stack_graphs_aux_to_stack_graphs_disjoint.
  2:{
    cbn.
    apply map_disjoint_fmap.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 vertices_relabel_graph.
    set_solver +.
  }
  apply stack_graphs_struct_isomorphic_Proper.
  - rewrite (reindex_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
  - rewrite (reindex_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
Qed.



Lemma venlarge_graph_stack_graphs {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m')
  (Hf : forall p q, vec_to_list (f p~0) ## vec_to_list (f q~1)) :
  (venlarge_graph f (stack_graphs cohg cohg') [≡ᵢ]ₛ
  stack_graphs (venlarge_graph (λ p, f (p~0)) cohg)
    (venlarge_graph (λ p, f (p~1)) cohg'))%cohg.
Proof.
  rewrite (venlarge_graph_stack_graphs'' _ _
    _ (f xH)) by auto.
  pose proof @eq_subrelation.
  apply (subrel' (sigT2_relation (λ _ _, eq))).
  erewrite venlarge_graph_ext_strong'; [reflexivity|].
  intros i.
  destruct i; done.
Qed.


Lemma sized_graph_to_graph_stack_graphs {N T n m n' m'}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  (sized_graph_to_graph f (stack_sized_graphs scohg scohg') [≡ᵢ]ₛ
  stack_graphs (sized_graph_to_graph f scohg)
    (sized_graph_to_graph f scohg'))%cohg.
Proof.
  cbn.
  fold (stack_graphs scohg scohg').
  etransitivity; [apply venlarge_graph_stack_graphs|].
  1: {
    intros p q.
    rewrite 2 vec_to_list_fun_to_vec_gen.
    set_solver.
  }
  rewrite graph_to_pair_bundled_apply2.
  symmetry.
  rewrite graph_to_pair_bundled_apply2.

  refine (sigT2_relation_f_equiv_2 _ _ _
    (fun _ _ _ _ => stack_graphs) _ _ _ _ _ _).
  - etransitivity. 1:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply (subrel' isomorphic).
      refine (relabel_is_isomorphic
      (encode_map (prod_map (bcons false) (@id nat))) _).
    }
    rewrite relabel_graph_venlarge_graph.
    erewrite venlarge_graph_ext_strong'; [reflexivity|].
    intros i Hi.
    cbn.
    rewrite lookup_union, (lookup_kmap (bcons false) _ i).
    rewrite (lookup_kmap_None _ _ _).2 by lia.
    rewrite (right_id_L None _).
    rewrite vmap_fun_to_vec.
    apply f_equal, vec_eq.
    intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    rewrite encode_map_encode.
    done.
  - etransitivity. 1:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply (subrel' isomorphic).
      refine (relabel_is_isomorphic
      (encode_map (prod_map (bcons true) (@id nat))) _).
    }
    rewrite relabel_graph_venlarge_graph.
    erewrite venlarge_graph_ext_strong'; [reflexivity|].
    intros i Hi.
    cbn.
    rewrite lookup_union, (lookup_kmap (bcons true) _ i).
    rewrite (lookup_kmap_None _ _ _).2 by lia.
    rewrite (left_id_L None _).
    rewrite vmap_fun_to_vec.
    apply f_equal, vec_eq.
    intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    rewrite encode_map_encode.
    done.
Qed.




Lemma venlarge_graph_swapped_stack_graphs_aux {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (* hyperedges cohg ##ₘ hyperedges cohg' -> *)
  (venlarge_graph f (swapped_stack_graphs_aux cohg cohg') =ₛ
  swapped_stack_graphs_aux (venlarge_graph f cohg) (venlarge_graph f cohg'))%cohg.
Proof.
  (* intros Hdisj. *)
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    apply enlarge_hypergraph_union.
Qed.

Lemma venlarge_graph_swapped_stack_graphs' {T n m n' m'} {nfl nfr : positive -> nat}
  (fl : forall p, vec positive (nfl p))
  (fr : forall p, vec positive (nfr p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (swapped_stack_graphs (venlarge_graph fl cohg) (venlarge_graph fr cohg') [≡ᵢ]ₛ
  venlarge_graph (@pos_case (λ p, vec positive (pos_case nfl nfr 0 p))
    (λ p, vmap (bcons false) (fl p))
    (λ p, vmap (bcons true) (fr p)) [#]) (swapped_stack_graphs cohg cohg'))%cohg.
Proof.
  unfold swapped_stack_graphs.
  rewrite venlarge_graph_swapped_stack_graphs_aux.
  symmetry.
  rewrite (graph_to_pair_bundled_apply2 (fun _ _ _ _ => swapped_stack_graphs_aux)).
  rewrite 2 venlarge_graph_relabel_graph, 2 venlarge_graph_reindex_graph.
  cbn.
  constructor.
  rewrite swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint.
  2:{
    cbn.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 (vertices_reindex_graph _).
    rewrite 2 vertices_venlarge_graph.
    unfold compose.
    set_unfold.
    setoid_rewrite vec_to_list_map.
    set_solver.
  }
  rewrite swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint.
  2:{
    cbn.
    apply map_disjoint_fmap.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 vertices_relabel_graph.
    set_solver.
  }
  apply swapped_stack_graphs_struct_isomorphic_Proper.
  - rewrite (reindex_is_isomorphic _).
    rewrite <- relabel_graph_venlarge_graph.
    rewrite (relabel_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
  - rewrite (reindex_is_isomorphic _).
    rewrite <- relabel_graph_venlarge_graph.
    rewrite (relabel_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
Qed.

Lemma venlarge_graph_swapped_stack_graphs'' {T n m n' m'} {nfl nfr : positive -> nat}
  (fl : forall p, vec positive (nfl p))
  (fr : forall p, vec positive (nfr p))
  (n0 : nat) (v0 : vec positive n0)
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m')
  (Hflr : forall p q, vec_to_list (fl p) ## vec_to_list (fr q)) :
  (swapped_stack_graphs (venlarge_graph fl cohg) (venlarge_graph fr cohg') [≡ᵢ]ₛ
  venlarge_graph (@pos_case (λ p, vec positive (pos_case nfl nfr n0 p))
    (λ p, (fl p))
    (λ p, (fr p)) v0) (swapped_stack_graphs cohg cohg'))%cohg.
Proof.
  unfold swapped_stack_graphs.
  rewrite venlarge_graph_swapped_stack_graphs_aux.
  symmetry.
  rewrite (graph_to_pair_bundled_apply2 (fun _ _ _ _ => swapped_stack_graphs_aux)).
  rewrite 2 venlarge_graph_relabel_graph, 2 venlarge_graph_reindex_graph.
  cbn.
  constructor.
  rewrite swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint.
  2:{
    cbn.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 (vertices_reindex_graph _).
    rewrite 2 vertices_venlarge_graph.
    set_solver.
  }
  rewrite swapped_stack_graphs_aux_to_swapped_stack_graphs_disjoint.
  2:{
    cbn.
    apply map_disjoint_fmap.
    apply (kmap_inj2_disjoint _).
    easy.
  }
  2:{
    rewrite 2 vertices_relabel_graph.
    set_solver +.
  }
  apply swapped_stack_graphs_struct_isomorphic_Proper.
  - rewrite (reindex_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
  - rewrite (reindex_is_isomorphic _).
    now rewrite <- iso_relabel_reindex by apply _.
Qed.



Lemma venlarge_graph_swapped_stack_graphs {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m')
  (Hf : forall p q, vec_to_list (f p~0) ## vec_to_list (f q~1)) :
  (venlarge_graph f (swapped_stack_graphs cohg cohg') [≡ᵢ]ₛ
  swapped_stack_graphs (venlarge_graph (λ p, f (p~0)) cohg)
    (venlarge_graph (λ p, f (p~1)) cohg'))%cohg.
Proof.
  rewrite (venlarge_graph_swapped_stack_graphs'' _ _
    _ (f xH)) by auto.
  pose proof @eq_subrelation.
  apply (subrel' (sigT2_relation (λ _ _, eq))).
  erewrite venlarge_graph_ext_strong'; [reflexivity|].
  intros i.
  destruct i; done.
Qed.


Lemma sized_graph_to_graph_swapped_stack_graphs {N T n m n' m'}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  (sized_graph_to_graph f (swapped_stack_sized_graphs scohg scohg') [≡ᵢ]ₛ
  swapped_stack_graphs (sized_graph_to_graph f scohg)
    (sized_graph_to_graph f scohg'))%cohg.
Proof.
  cbn.
  fold (stack_graphs scohg scohg').
  etransitivity; [apply venlarge_graph_swapped_stack_graphs|].
  1: {
    intros p q.
    rewrite 2 vec_to_list_fun_to_vec_gen.
    set_solver.
  }
  rewrite (graph_to_pair_bundled_apply2 (fun _ _ _ _ => swapped_stack_graphs)).
  symmetry.
  rewrite (graph_to_pair_bundled_apply2 (fun _ _ _ _ => swapped_stack_graphs)).
  pose proof @swapped_stack_graphs_struct_isomorphic_Proper.
  refine (sigT2_relation_f_equiv_2 (λ _ _, struct_isomorphic)
    (λ _ _, struct_isomorphic) (λ _ _, struct_isomorphic)
    (fa:=fun a b => b + a)
    (fb:=Nat.add)
    (@swapped_stack_graphs T) _ _ _ _ _ _).

  - etransitivity. 1:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply (subrel' isomorphic).
      refine (relabel_is_isomorphic
      (encode_map (prod_map (bcons false) (@id nat))) _).
    }
    rewrite relabel_graph_venlarge_graph.
    erewrite venlarge_graph_ext_strong'; [reflexivity|].
    intros i Hi.
    cbn.
    rewrite lookup_union, (lookup_kmap (bcons false) _ i).
    rewrite (lookup_kmap_None _ _ _).2 by lia.
    rewrite (right_id_L None _).
    rewrite vmap_fun_to_vec.
    apply f_equal, vec_eq.
    intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    rewrite encode_map_encode.
    done.
  - etransitivity. 1:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply (subrel' isomorphic).
      refine (relabel_is_isomorphic
      (encode_map (prod_map (bcons true) (@id nat))) _).
    }
    rewrite relabel_graph_venlarge_graph.
    erewrite venlarge_graph_ext_strong'; [reflexivity|].
    intros i Hi.
    cbn.
    rewrite lookup_union, (lookup_kmap (bcons true) _ i).
    rewrite (lookup_kmap_None _ _ _).2 by lia.
    rewrite (left_id_L None _).
    rewrite vmap_fun_to_vec.
    apply f_equal, vec_eq.
    intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    rewrite encode_map_encode.
    done.
Qed.

Lemma venlarge_graph_cohg_vert_eq' {T n m}
  {nf nf' : positive -> nat}
  (f : forall p, vec positive (nf p))
  (f' : forall p, vec positive (nf' p))
  (cohg cohg' : CospanHyperGraph T n m) :
  (cohg ≡ᵥ cohg')%cohg ->
  (forall p, p ∈ vertices cohg -> f p =@{list _} f' p) ->
  (venlarge_graph f cohg [≡ᵥ]ₛ venlarge_graph f' cohg')%cohg.
Proof.
  intros (Hins & Houts & Hhg & Hverts)%cohg_vert_eq_alt_vertices Hf.
  destruct cohg as [hg ins outs], cohg' as [hg' ins' outs'].
  cbn in *.
  subst ins' outs'.
  apply mk_bundled_cohg_vert_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong;
    intros a Ha; apply Hf;
    set_solver +Ha.
  - cbn.
    rewrite 2 vec_to_list_bind.
    apply list_bind_ext_strong;
    intros a Ha; apply Hf;
    set_solver +Ha.
  - cbn.
    rewrite <- Hhg.
    apply map_fmap_ext.
    intros i [[t is] os] Htio.
    cbn.
    f_equal; [f_equal|];
    apply list_bind_ext_strong;
    intros a Ha; f_equal; apply Hf, elem_of_vertices; left;
    set_solver.
  - etransitivity; [apply vertices_venlarge_graph|].
    etransitivity; [|symmetry; apply vertices_venlarge_graph].
    rewrite <- Hverts.
    apply leibniz_equiv_iff, set_bind_ext, reflexivity.
    intros x Hx _.
    cbn.
    now rewrite <- Hf by done.
Qed.

Lemma sized_graph_to_graph_scohg_vert_eq {N T n m} f
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' ->
  (sized_graph_to_graph f scohg [≡ᵥ]ₛ sized_graph_to_graph f scohg')%cohg.
Proof.
  intros Heq.
  pose proof Heq as (Hins & Houts & Hhedges & Hverts & Hmap)%scohg_vert_eq_iff.
  destruct scohg as [[hg ins outs] smap].
  destruct scohg' as [[hg' ins' outs'] smap'].
  cbn in *.
  subst ins' outs'.
  pose proof Heq.1 as Hveq.
  cbn in Hveq.
  refine (venlarge_graph_cohg_vert_eq' _ _
  (ins -> hg <- outs) (ins -> hg' <- outs) _ _).
  - apply Hveq.
  - intros p Hp.
    rewrite <- Hverts in Hmap.
    apply (f_equal (.!! p)) in Hmap.
    rewrite 2 map_lookup_filter in Hmap.
    cbn in Hmap.
    case_guard; [|easy].
    cbn in Hmap.
    rewrite 2 bind_with_Some in Hmap.
    rewrite <- Hmap.
    done.
Qed.

Lemma add_top_loops_bundled_struct_isomorphic
  {T n m o n' m' o'}
  (cohg : CospanHyperGraph T (n + m) (n + o))
  (cohg' : CospanHyperGraph T (n' + m') (n' + o')) :
  n = n' ->
  (cohg [≡ᵢ]ₛ cohg' ->
  add_top_loops cohg [≡ᵢ]ₛ add_top_loops cohg')%cohg.
Proof.
  intros <-.
  intros (Hnm & Heq)%sigT2_relation_alt.
  cbn in Heq, Hnm.
  apply pair_eq in Hnm as Hnm'.
  assert (m = m') as <- by lia.
  assert (o = o') as <- by lia.
  constructor.
  apply add_top_loops_struct_isomorphic.
  rewrite Heq.
  rewrite (proof_irrel Hnm eq_refl).
  done.
Qed.

Lemma cast_graph_bundled_eq {T n m n' m'}
  (Hn : n = n') (Hm : m = m') (cohg : CospanHyperGraph T n m) :
  (cast_graph Hn Hm cohg =ₛ cohg)%cohg.
Proof.
  subst.
  rewrite cast_graph_id.
  done.
Qed.

Lemma cast_sized_graph_bundled_eq {N T n m n' m'}
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  (cast_sized_graph Hn Hm scohg =ₛ scohg)%scohg.
Proof.
  subst.
  rewrite cast_sized_graph_id.
  done.
Qed.



Lemma sized_graph_to_graph_cast {N T n m n' m'} (f : N -> nat)
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  sized_graph_to_graph f (cast_sized_graph Hn Hm scohg) =
  cast_graph (f_equal (sum_list_with _) (eq_sym (vec_to_list_cast _ _)))
    (f_equal (sum_list_with _) (eq_sym (vec_to_list_cast _ _))) (sized_graph_to_graph f scohg).
Proof.
  apply cohg_ext.
  - done.
  - simpl.
    apply vec_to_list_inj2.
    rewrite vec_to_list_cast, 2 vec_to_list_bind, vec_to_list_cast.
    done.
  - simpl.
    apply vec_to_list_inj2.
    rewrite vec_to_list_cast, 2 vec_to_list_bind, vec_to_list_cast.
    done.
Qed.

Lemma sized_graph_to_pair_bundled_cast {N T n m n' m'}
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  sized_graph_to_pair_bundled (cast_sized_graph Hn Hm scohg) =
  sized_graph_to_pair_bundled scohg.
Proof.
  now subst; rewrite cast_sized_graph_id.
Qed.

Lemma graph_to_pair_bundled_cast {T n m n' m'}
  (Hn : n = n') (Hm : m = m') (scohg : CospanHyperGraph T n m) :
  graph_to_pair_bundled (cast_graph Hn Hm scohg) =
  graph_to_pair_bundled scohg.
Proof.
  now subst; rewrite cast_graph_id.
Qed.

(* FIXME: Move (to before the statement of compose correctness) *)
Definition sized_inputs {N T n m} (scohg : SizedCospanHyperGraph N T n m) :
  list (option N) :=
  (scohg.(sized_map) !!.) <$> (scohg.(inputs) :> list _).
Definition sized_outputs {N T n m} (scohg : SizedCospanHyperGraph N T n m) :
  list (option N) :=
  (scohg.(sized_map) !!.) <$> (scohg.(outputs) :> list _).

Lemma lookup_kmap_alt `{FinMap K1 M1, FinMap K2 M2}
  {A} (f : K1 -> K2) (m : M1 A) :
  (forall i j a b, f i = f j -> m !! i = Some a -> m !! j = Some b -> a = b) ->
  forall i a,
  m !! i = Some a -> (kmap f m :> M2 A) !! f i = Some a.
Proof.
  intros Hf.
  unfold kmap.
  intros i a.
  intros Hmi.
  apply elem_of_map_to_list in Hmi.
  setoid_rewrite <- elem_of_map_to_list in Hf.
  induction (map_to_list m) as [|(j, b) l IHl]; [easy|].
  apply elem_of_cons in Hmi as [ [= <- <-] | Hmi];
    [apply lookup_insert|].
  cbn.
  rewrite lookup_insert_case.
  case_decide as Hfij.
  - f_equal; eapply Hf; eauto using elem_of_list.
  - apply IHl, Hmi.
    eauto using elem_of_list_further.
Qed.


Definition well_sized {N T n m} (scohg : SizedCospanHyperGraph N T n m) :=
  vertices scohg ⊆ dom (sized_map scohg).

Lemma sized_inputs_relabel_sized_graph {N T n m}
  (f : positive -> positive) (scohg : SizedCospanHyperGraph N T n m) :
  well_sized scohg ->
  (forall i j n m, f i = f j -> scohg.(sized_map) !! i = Some n ->
    scohg.(sized_map) !! j = Some m -> n = m) ->
  sized_inputs (relabel_sized_graph f scohg) = sized_inputs scohg.
Proof.
  intros Hsized Hf.
  unfold sized_inputs; cbn.
  rewrite vec_to_list_map, <- list_fmap_compose.
  unfold compose.
  apply list_fmap_ext.
  intros _ i Hi%elem_of_list_lookup_2.
  assert (Hsi : is_Some (sized_map scohg !! i)). 1:{
    apply elem_of_dom.
    apply Hsized.
    set_solver +Hi.
  }
  destruct Hsi as [si Hsi].
  rewrite Hsi.
  now apply lookup_kmap_alt.
Qed.

Lemma sized_outputs_relabel_sized_graph {N T n m}
  (f : positive -> positive) (scohg : SizedCospanHyperGraph N T n m) :
  well_sized scohg ->
  (forall i j n m, f i = f j -> scohg.(sized_map) !! i = Some n ->
    scohg.(sized_map) !! j = Some m -> n = m) ->
  sized_outputs (relabel_sized_graph f scohg) = sized_outputs scohg.
Proof.
  intros Hsized Hf.
  unfold sized_outputs; cbn.
  rewrite vec_to_list_map, <- list_fmap_compose.
  unfold compose.
  apply list_fmap_ext.
  intros _ i Hi%elem_of_list_lookup_2.
  assert (Hsi : is_Some (sized_map scohg !! i)). 1:{
    apply elem_of_dom.
    apply Hsized.
    set_solver +Hi.
  }
  destruct Hsi as [si Hsi].
  rewrite Hsi.
  now apply lookup_kmap_alt.
Qed.
(*
Lemma lookup_sized_inputs {N T n m} (scohg : SizedCospanHyperGraph N T n m) i :
  sized_inputs  *)

Lemma sized_inputs_add_top_loop {N T n m}
  (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  sized_inputs scohg !! 0 = sized_outputs scohg !! 0 ->
  sized_inputs (sized_add_top_loop scohg) = tl (sized_inputs scohg).
Proof.
  intros Heq.
  cbn.
  destruct scohg as [ [hg ins outs] smap].
  induction ins as [ih ins] using vec_S_inv.
  induction outs as [oh outs] using vec_S_inv.
  cbn -[map_relabel_one] in *.
  injection Heq as Heq.
  rewrite <- 2 vec_to_list_map.
  f_equal.
  apply vec_eq.
  intros p.
  rewrite 3 vlookup_map.
  rewrite lookup_map_relabel_one.
  now rewrite (fn_lookup_singleton_cancel (smap !!.)) by done.
Qed.

Lemma sized_outputs_add_top_loop {N T n m}
  (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  sized_inputs scohg !! 0 = sized_outputs scohg !! 0 ->
  sized_outputs (sized_add_top_loop scohg) = tl (sized_outputs scohg).
Proof.
  intros Heq.
  cbn.
  destruct scohg as [ [hg ins outs] smap].
  induction ins as [ih ins] using vec_S_inv.
  induction outs as [oh outs] using vec_S_inv.
  cbn -[map_relabel_one] in *.
  injection Heq as Heq.
  rewrite <- 2 vec_to_list_map.
  f_equal.
  apply vec_eq.
  intros p.
  rewrite 3 vlookup_map.
  rewrite lookup_map_relabel_one.
  now rewrite (fn_lookup_singleton_cancel (smap !!.)) by done.
Qed.

(* FIXME: MOve *)
Lemma tail_is_drop {A} (l : list A) :
  tail l = drop 1 l.
Proof.
  done.
Qed.

Lemma sized_inputs_add_top_loops {N T n m o}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  take n $ sized_inputs scohg = take n $ sized_outputs scohg ->
  sized_inputs (sized_add_top_loops scohg) = drop n (sized_inputs scohg).
Proof.
  induction n; [done|].
  intros Heq.
  cbn.
  assert (Hhd : sized_inputs scohg !! 0 = sized_outputs scohg !! 0). 1:{
    now rewrite <- (lookup_take _ (S n) 0), Heq, (lookup_take _ (S n) 0) by lia.
  }
  rewrite IHn. 2:{
    rewrite sized_inputs_add_top_loop, sized_outputs_add_top_loop by done.
    rewrite 2 tail_is_drop.
    rewrite 2 firstn_skipn_comm.
    cbn.
    f_equal.
    apply Heq.
  }
  rewrite sized_inputs_add_top_loop by done.
  rewrite tail_is_drop.
  rewrite skipn_skipn.
  f_equal; lia.
Qed.

Lemma sized_outputs_add_top_loops {N T n m o}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  take n $ sized_inputs scohg = take n $ sized_outputs scohg ->
  sized_outputs (sized_add_top_loops scohg) = drop n (sized_outputs scohg).
Proof.
  induction n; [done|].
  intros Heq.
  cbn.
  assert (Hhd : sized_inputs scohg !! 0 = sized_outputs scohg !! 0). 1:{
    now rewrite <- (lookup_take _ (S n) 0), Heq, (lookup_take _ (S n) 0) by lia.
  }
  rewrite IHn. 2:{
    rewrite sized_inputs_add_top_loop, sized_outputs_add_top_loop by done.
    rewrite 2 tail_is_drop.
    rewrite 2 firstn_skipn_comm.
    cbn.
    f_equal.
    apply Heq.
  }
  rewrite sized_outputs_add_top_loop by done.
  rewrite tail_is_drop.
  rewrite skipn_skipn.
  f_equal; lia.
Qed.

Lemma sized_inputs_swapped_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_inputs (swapped_stack_sized_graphs scohg scohg') =
  sized_inputs scohg' ++ sized_inputs scohg.
Proof.
  cbn.
  rewrite vec_to_list_app, fmap_app.
  rewrite 2 vec_to_list_map, <- 2 list_fmap_compose.
  f_equal; apply list_fmap_ext; intros; cbn -[bcons];
  rewrite lookup_union, (lookup_kmap _),
    (lookup_kmap_None _ _ _).2 by lia;
  [apply left_id_L, _|apply right_id_L, _].
Qed.

Lemma sized_outputs_swapped_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_outputs (swapped_stack_sized_graphs scohg scohg') =
  sized_outputs scohg ++ sized_outputs scohg'.
Proof.
  cbn.
  rewrite vec_to_list_app, fmap_app.
  rewrite 2 vec_to_list_map, <- 2 list_fmap_compose.
  f_equal; apply list_fmap_ext; intros; cbn -[bcons];
  rewrite lookup_union, (lookup_kmap _),
    (lookup_kmap_None _ _ _).2 by lia;
  [apply right_id_L, _|apply left_id_L, _].
Qed.

Lemma dom_partial_alter `{FinMapDom K M SK} {A} (k : K)
  (f : option A -> option A) (m : M A) :
  dom (partial_alter f k m) ≡ dom m ∖ {[k]} ∪
     if decide (is_Some (f (m !! k))) then {[k]} else ∅.
Proof.
  set_unfold.
  intros x.
  rewrite 2 elem_of_dom.
  destruct_decide (decide (x = k)).
  - subst.
    rewrite lookup_partial_alter.
    case_decide; set_solver.
  - rewrite lookup_partial_alter_ne by done.
    case_decide; set_solver.
Qed.


Lemma dom_partial_alter_L `{FinMapDom K M SK,
  !LeibnizEquiv SK} {A} (k : K)
  (f : option A -> option A) (m : M A) :
  dom (partial_alter f k m) = dom m ∖ {[k]} ∪
    if decide (is_Some (f (m !! k))) then {[k]} else ∅.
Proof.
  unfold_leibniz.
  apply dom_partial_alter.
Qed.


Lemma dom_map_relabel_one `{FinMapDom K M SK} {A} (a b : K) (m : M A) :
  dom (map_relabel_one a b m) ≡@{SK}
  dom m ∖ {[a]} ∪ if decide (is_Some (m !! b)) then {[a]} else ∅.
Proof.
  unfold map_relabel_one.
  now rewrite dom_partial_alter.
Qed.

Lemma dom_map_relabel_one_L `{FinMapDom K M SK, !LeibnizEquiv SK} {A} (a b : K) (m : M A) :
  dom (map_relabel_one a b m) =@{SK}
  dom m ∖ {[a]} ∪ if decide (is_Some (m !! b)) then {[a]} else ∅.
Proof.
  unfold map_relabel_one.
  now rewrite dom_partial_alter_L.
Qed.


Lemma well_sized_add_top_loop {N T n m}
  (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  well_sized scohg -> well_sized (sized_add_top_loop scohg).
Proof.
  intros HWF.
  unfold well_sized.
  cbn.
  rewrite vertices_add_top_loop.
  etransitivity; [|apply eq_reflexivity, symmetry;
  refine (dom_map_relabel_one_L (M:=Pmap) _ _ _)].
  rewrite set_map_fn_singleton_L.
  rewrite decide_True.
  2:{
    rewrite vertices_vertices_hg_decomp, (Vector.eta scohg.(outputs)).
    set_solver +.
  }
  rewrite decide_True.
  2:{
    apply elem_of_dom.
    apply HWF.
    rewrite vertices_vertices_hg_decomp, (Vector.eta scohg.(outputs)).
    set_solver +.
  }
  rewrite difference_union_L.
  apply union_least, union_subseteq_r.
  apply subseteq_difference_l.
  apply union_subseteq_l', HWF.
Qed.

Lemma well_sized_add_top_loops {N T n m o}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  well_sized scohg -> well_sized (sized_add_top_loops scohg).
Proof.
  intros HWF.
  induction n; [done|].
  cbn.
  now apply IHn, well_sized_add_top_loop.
Qed.


Lemma well_sized_swapped_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  well_sized scohg -> well_sized scohg' ->
  well_sized (swapped_stack_sized_graphs scohg scohg').
Proof.
  intros HWF HWF'.
  unfold well_sized.
  unfold swapped_stack_sized_graphs at 1.
  cbn.
  rewrite vertices_swapped_stack_graphs_aux by
    now apply map_disjoint_fmap, (kmap_inj2_disjoint _).
  rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _).
  rewrite dom_union, 2 dom_kmap_L'.
  apply union_mono; now apply set_map_mono.
Qed.



Add Parametric Morphism {N T n m} : (@sized_inputs N T n m)
  with signature scohg_vert_eq ==> eq as sized_inputs_scohg_vert_eq.
Proof.
  intros scohg scohg' Heq%scohg_vert_eq_alt.
  unfold sized_inputs.
  rewrite <- Heq.1.
  apply list_fmap_ext.
  intros _ x Hx%elem_of_list_lookup_2.
  apply Heq.2.2.2.
  set_solver + Hx.
Qed.

Add Parametric Morphism {N T n m} : (@sized_outputs N T n m)
  with signature scohg_vert_eq ==> eq as sized_outputs_scohg_vert_eq.
Proof.
  intros scohg scohg' Heq%scohg_vert_eq_alt.
  unfold sized_outputs.
  rewrite <- Heq.2.1.
  apply list_fmap_ext.
  intros _ x Hx%elem_of_list_lookup_2.
  apply Heq.2.2.2.
  set_solver + Hx.
Qed.

(* Local Add Parametric Morphism {N T n m} : (@well_sized N T n m)
  with signature scohg_vert_eq ==> impl as well_sized_scohg_vert_eq_impl.
Proof.
  intros scohg scohg' Heq.
  pose proof Heq as Heq'%scohg_vert_eq_alt.
  Search subseteq intersection.
  unfold well_sized.
  rewrite <- vertices_norm_verts.
  rewrite Heq.1.
  f_equiv.
  - now rewrite vertices_norm_verts.
  -
  rewrite <- Heq at 1. *)

Add Parametric Morphism {N T n m} : (@well_sized N T n m)
  with signature scohg_vert_eq ==> iff as well_sized_scohg_vert_eq.
Proof.
  intros scohg scohg' Heq.
  pose proof Heq as Heq'%scohg_vert_eq_alt.
  unfold well_sized.
  rewrite <- (vertices_norm_verts scohg').
  rewrite <- Heq.1.
  rewrite vertices_norm_verts.
  rewrite 2 subseteq_intersection.
  f_equiv.
  intros x.
  rewrite 2 elem_of_intersection.
  apply and_iff_from_l; [done|].
  intros Hx _.
  rewrite 2 elem_of_dom.
  rewrite Heq'.2.2.2.2 by now apply elem_of_union_l.
  done.
Qed.

Lemma length_sized_inputs {N T n m} (scohg : SizedCospanHyperGraph N T n m) :
  length (sized_inputs scohg) = n.
Proof.
  unfold sized_inputs.
  now rewrite length_fmap, length_vec_to_list.
Qed.

Lemma length_sized_outputs {N T n m} (scohg : SizedCospanHyperGraph N T n m) :
  length (sized_outputs scohg) = m.
Proof.
  unfold sized_outputs.
  now rewrite length_fmap, length_vec_to_list.
Qed.


Lemma sized_inputs_compose_sized_graphs {N T n m o}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T m o) :
  sized_outputs scohg = sized_inputs scohg' ->
  sized_inputs (compose_sized_graphs scohg scohg') =
  sized_inputs scohg.
Proof.
  rewrite <- compose_sized_graphs_alt_correct.
  intros Heq.
  rewrite sized_inputs_add_top_loops. 2:{
    rewrite sized_inputs_swapped_stack_sized_graphs,
      sized_outputs_swapped_stack_sized_graphs.
    rewrite <- (length_sized_inputs scohg') at 1.
    rewrite <- (length_sized_outputs scohg) at 4.
    rewrite 2 take_app_length.
    done.
  }
  rewrite sized_inputs_swapped_stack_sized_graphs.
  rewrite <- (length_sized_inputs scohg') at 1.
  now rewrite drop_app_length.
Qed.

Lemma sized_outputs_compose_sized_graphs {N T n m o}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T m o) :
  sized_outputs scohg = sized_inputs scohg' ->
  sized_outputs (compose_sized_graphs scohg scohg') =
  sized_outputs scohg'.
Proof.
  rewrite <- compose_sized_graphs_alt_correct.
  intros Heq.
  rewrite sized_outputs_add_top_loops. 2:{
    rewrite sized_inputs_swapped_stack_sized_graphs,
      sized_outputs_swapped_stack_sized_graphs.
    rewrite <- (length_sized_inputs scohg') at 1.
    rewrite <- (length_sized_outputs scohg) at 4.
    rewrite 2 take_app_length.
    done.
  }
  rewrite sized_outputs_swapped_stack_sized_graphs.
  rewrite <- (length_sized_outputs scohg) at 1.
  now rewrite drop_app_length.
Qed.



Lemma sized_inputs_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_inputs (stack_sized_graphs scohg scohg') =
  sized_inputs scohg ++ sized_inputs scohg'.
Proof.
  cbn.
  rewrite vec_to_list_app, fmap_app.
  rewrite 2 vec_to_list_map, <- 2 list_fmap_compose.
  f_equal; apply list_fmap_ext; intros; cbn -[bcons];
  rewrite lookup_union, (lookup_kmap _),
    (lookup_kmap_None _ _ _).2 by lia;
  [apply right_id_L, _|apply left_id_L, _].
Qed.

Lemma sized_outputs_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_outputs (stack_sized_graphs scohg scohg') =
  sized_outputs scohg ++ sized_outputs scohg'.
Proof.
  cbn.
  rewrite vec_to_list_app, fmap_app.
  rewrite 2 vec_to_list_map, <- 2 list_fmap_compose.
  f_equal; apply list_fmap_ext; intros; cbn -[bcons];
  rewrite lookup_union, (lookup_kmap _),
    (lookup_kmap_None _ _ _).2 by lia;
  [apply right_id_L, _|apply left_id_L, _].
Qed.

Lemma well_sized_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  well_sized scohg -> well_sized scohg' ->
  well_sized (stack_sized_graphs scohg scohg').
Proof.
  unfold well_sized.
  intros Hsized Hsized'.
  cbn.
  setoid_rewrite vertices_stack_graphs.
  rewrite dom_union.
  rewrite 2 dom_kmap'.
  apply union_mono; now f_equiv.
Qed.

Lemma well_sized_compose_sized_graphs {N T n m o}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T m o) :
  well_sized scohg -> well_sized scohg' ->
  (* sized_outputs scohg = sized_inputs scohg' -> *)
  well_sized (compose_sized_graphs scohg scohg').
Proof.
  intros Hscohg Hscohg'.
  rewrite <- compose_sized_graphs_alt_correct.
  now apply well_sized_add_top_loops, well_sized_swapped_stack_sized_graphs.
Qed.

Lemma well_sized_id_sized_graph {N T n} (v : vec N n) :
  well_sized (@id_sized_graph N T n v).
Proof.
  unfold well_sized.
  cbn.
  rewrite dom_list_to_map.
  rewrite fmap_imap; unfold compose; cbn.
  rewrite imap_seq_0.
  cbn.
  rewrite vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_empty, union_empty_l_L.
  rewrite vec_to_list_map, vec_to_list_seq.
  rewrite list_to_set_app_L, union_idemp_L.
  now rewrite length_vec_to_list.
Qed.

Lemma well_sized_cap_sized_graph {N T n} (v : vec N n) :
  well_sized (@cap_sized_graph N T n v).
Proof.
  unfold well_sized.
  cbn.
  rewrite dom_list_to_map.
  rewrite fmap_imap; unfold compose; cbn.
  rewrite imap_seq_0.
  cbn.
  rewrite vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_empty, union_empty_l_L.
  rewrite vec_to_list_map, vec_to_list_app, vec_to_list_seq.
  rewrite app_nil_r.
  rewrite length_vec_to_list.
  set_solver +.
Qed.

Lemma well_sized_cup_sized_graph {N T n} (v : vec N n) :
  well_sized (@cup_sized_graph N T n v).
Proof.
  unfold well_sized.
  cbn.
  rewrite dom_list_to_map.
  rewrite fmap_imap; unfold compose; cbn.
  rewrite imap_seq_0.
  cbn.
  rewrite vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_empty, union_empty_l_L.
  rewrite vec_to_list_map, vec_to_list_app, vec_to_list_seq.
  rewrite length_vec_to_list.
  set_solver +.
Qed.

Lemma well_sized_swap_sized_graph {N T n m} (v : vec N n) (w : vec N m) :
  well_sized (@swap_sized_graph N T n m v w).
Proof.
  unfold well_sized.
  cbn.
  rewrite dom_list_to_map.
  rewrite fmap_imap; unfold compose; cbn.
  rewrite imap_seq_0.
  cbn.
  rewrite vertices_vertices_hg_decomp.
  cbn.
  rewrite vertices_hg_empty, union_empty_l_L.
  rewrite <- vseq_app.
  rewrite 2 vec_to_list_map, vec_to_list_app, 3 vec_to_list_seq.
  rewrite list_to_set_app_L.
  rewrite Permutation_app_comm, <- seq_app.
  rewrite union_idemp_L.
  rewrite length_app, 2 length_vec_to_list.
  done.
Qed.

Lemma well_sized_sized_graph_of_tensor {N T n m} t (v : vec N n) (w : vec N m) :
  well_sized (@sized_graph_of_tensor N T t n m v w).
Proof.
  unfold well_sized.
  cbn.
  rewrite dom_union.
  rewrite 2 dom_list_to_map.
  rewrite 2 fmap_imap; unfold compose; cbn.
  rewrite 2 imap_seq_0.
  cbn.
  rewrite vertices_vertices_hg_decomp.
  cbn.
  rewrite union_comm_L, set_union_eq_l. 2:{
    rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
    rewrite vertices_hg_decomp.
    cbn.
    rewrite union_empty_r_L.
    unfold referenced_vertices_hg.
    rewrite hyperedges_singleton.
    rewrite map_to_list_singleton.
    cbn.
    now rewrite app_nil_r.
  }
  rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
  rewrite 2 length_vec_to_list.
  set_solver.
Qed.

Lemma sized_inputs_id_sized_graph {N T n} (v : vec N n) :
  sized_inputs (@id_sized_graph N T n v) = Some <$> vec_to_list v.
Proof.
  unfold sized_inputs.
  cbn.
  apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, 2 length_vec_to_list|].
  intros i ma mb Hi.
  rewrite length_fmap, length_vec_to_list in Hi.
  replace i with (nat_to_fin Hi :> nat) by apply fin_to_nat_to_fin.
  rewrite 2 list_lookup_fmap, 2 lookup_vec_to_list_fin.
  rewrite vlookup_map, vlookup_seq.
  cbn.
  rewrite lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat.
  rewrite option_fmap_id.
  rewrite lookup_vec_to_list_fin.
  congruence.
Qed.

Lemma sized_outputs_id_sized_graph {N T n} (v : vec N n) :
  sized_outputs (@id_sized_graph N T n v) = Some <$> vec_to_list v.
Proof.
  apply sized_inputs_id_sized_graph.
Qed.

Lemma sized_inputs_cap_sized_graph {N T n} (v : vec N n) :
  sized_inputs (@cap_sized_graph N T n v) = Some <$> (v ++ v).
Proof.
  unfold sized_inputs.
  cbn.
  rewrite Vector.map_append, vec_to_list_app, 2 fmap_app.
  refine ((fun H => f_equal2 app H H) _).
  apply (@sized_inputs_id_sized_graph N T).
Qed.

Lemma sized_outputs_cap_sized_graph {N T n} (v : vec N n) :
  sized_outputs (@cap_sized_graph N T n v) = [].
Proof.
  done.
Qed.

Lemma sized_inputs_cup_sized_graph {N T n} (v : vec N n) :
  sized_inputs (@cup_sized_graph N T n v) = [].
Proof.
  done.
Qed.

Lemma sized_outputs_cup_sized_graph {N T n} (v : vec N n) :
  sized_outputs (@cup_sized_graph N T n v) = Some <$> (v ++ v).
Proof.
  unfold sized_inputs.
  cbn.
  rewrite Vector.map_append, vec_to_list_app, 2 fmap_app.
  refine ((fun H => f_equal2 app H H) _).
  apply (@sized_inputs_id_sized_graph N T).
Qed.


Lemma sized_inputs_swap_sized_graph {N T n m} (v : vec N n) (w : vec N m) :
  sized_inputs (@swap_sized_graph N T n m v w) = Some <$> (v ++ w).
Proof.
  unfold sized_inputs.
  cbn.
  rewrite <- vseq_app, <- vec_to_list_app.
  apply (@sized_inputs_id_sized_graph N T).
Qed.

Lemma sized_outputs_swap_sized_graph {N T n m} (v : vec N n) (w : vec N m) :
  sized_outputs (@swap_sized_graph N T n m v w) = Some <$> (w ++ v).
Proof.
  unfold sized_outputs.
  cbn.
  pose proof (sized_inputs_swap_sized_graph (T:=T) v w) as Heq.
  unfold sized_inputs in Heq.
  cbn in Heq.
  rewrite Vector.map_append, vec_to_list_app, 2 fmap_app in Heq.
  rewrite Vector.map_append, vec_to_list_app, 2 fmap_app.
  apply app_inj_len_l in Heq; [|now rewrite 2 length_fmap, 2 length_vec_to_list].
  now f_equal.
Qed.

Lemma sized_inputs_sized_graph_of_tensor {N T n m} t (v : vec N n) (w : vec N m) :
  sized_inputs (@sized_graph_of_tensor N T t n m v w) = Some <$> (vec_to_list v).
Proof.
  unfold sized_inputs.
  cbn -[bcons].
  apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, 2 length_vec_to_list|].
  intros i ma mb Hi.
  rewrite length_fmap, length_vec_to_list in Hi.
  replace i with (nat_to_fin Hi :> nat) by apply fin_to_nat_to_fin.
  rewrite 2 list_lookup_fmap, 2 lookup_vec_to_list_fin.
  rewrite vlookup_map, vlookup_seq.
  cbn -[bcons].
  rewrite lookup_union.
  rewrite (lookup_list_to_map_imap (λ i, bcons false (Pos.of_succ_nat i))), option_fmap_id.
  rewrite lookup_vec_to_list_fin.
  rewrite union_Some_l.
  congruence.
Qed.

Lemma sized_outputs_sized_graph_of_tensor {N T n m} t (v : vec N n) (w : vec N m) :
  sized_outputs (@sized_graph_of_tensor N T t n m v w) = Some <$> (vec_to_list w).
Proof.
  unfold sized_outputs.
  cbn -[bcons].
  apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite 2 length_fmap, 2 length_vec_to_list|].
  intros i ma mb Hi.
  rewrite length_fmap, length_vec_to_list in Hi.
  replace i with (nat_to_fin Hi :> nat) by apply fin_to_nat_to_fin.
  rewrite 2 list_lookup_fmap, 2 lookup_vec_to_list_fin.
  rewrite vlookup_map, vlookup_seq.
  cbn -[bcons].
  rewrite lookup_union.
  rewrite (lookup_list_to_map_imap (λ i, bcons true (Pos.of_succ_nat i))), option_fmap_id.
  rewrite not_elem_of_dom_1, lookup_vec_to_list_fin, (left_id_L None _); [congruence|].
  rewrite dom_list_to_map_L.
  rewrite fmap_imap; unfold compose; simpl.
  rewrite imap_seq_0.
  set_solver.
Qed.

Lemma sized_inputs_cast {N T n m n' m'} (Hn : n = n') (Hm : m = m')
  (scohg : SizedCospanHyperGraph N T n m) :
  sized_inputs (cast_sized_graph Hn Hm scohg) = sized_inputs scohg.
Proof.
  subst; now rewrite cast_sized_graph_id.
Qed.

Lemma sized_outputs_cast {N T n m n' m'} (Hn : n = n') (Hm : m = m')
  (scohg : SizedCospanHyperGraph N T n m) :
  sized_outputs (cast_sized_graph Hn Hm scohg) = sized_outputs scohg.
Proof.
  subst; now rewrite cast_sized_graph_id.
Qed.

Lemma well_sized_cast {N T n m n' m'} (Hn : n = n') (Hm : m = m')
  (scohg : SizedCospanHyperGraph N T n m) :
  well_sized (cast_sized_graph Hn Hm scohg) <-> well_sized scohg.
Proof.
  subst; now rewrite cast_sized_graph_id.
Qed.

Lemma graph_to_pair_bundled_inj2 {T n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  graph_to_pair_bundled cohg = graph_to_pair_bundled cohg' ->
  cohg = cohg'.
Proof.
  unfold graph_to_pair_bundled.
  intros Heq.
  inversion_sigma Heq.
  rewrite (proof_irrel _ eq_refl) in *.
  done.
Qed.

Lemma compose_graphs_bundled_eq {T n m o n' m' o'}
  (cohg1 : CospanHyperGraph T n m) (cohg2 : CospanHyperGraph T m o)
  (cohg1' : CospanHyperGraph T n' m') (cohg2' : CospanHyperGraph T m' o') :
  (cohg1 =ₛ cohg1' ->
  cohg2 =ₛ cohg2' ->
  compose_graphs cohg1 cohg2 =ₛ compose_graphs cohg1' cohg2')%cohg.
Proof.
  intros Heq1 Heq2.
  inversion Heq1.
  subst.
  apply graph_to_pair_bundled_inj2 in Heq1 as <-.
  inversion Heq2.
  subst.
  apply graph_to_pair_bundled_inj2 in Heq2 as <-.
  done.
Qed.



Lemma sized_graph_to_graph_compose_graphs {N T n m o}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T m o) :
  (scohg.(sized_map) !!.) <$> (outputs scohg :> list _) =
  (scohg'.(sized_map) !!.) <$> (inputs scohg' :> list _) ->
  exists H,
  (sized_graph_to_graph f (compose_sized_graphs scohg scohg') [≡ᵢ]ₛ
  compose_graphs (cast_graph eq_refl H (sized_graph_to_graph f scohg))
    (sized_graph_to_graph f scohg'))%cohg.
Proof.
  intros Heq.
  apply exists_by_forall.
  1:{
    apply sum_list_with_eq_of_fmap.
    apply (f_equal (fmap (fmap f))) in Heq.
    apply (f_equal (fmap (default 0))) in Heq.
    rewrite <- 4 list_fmap_compose in Heq.
    apply Heq.
  }
  intros H.
  rewrite <- (sized_graph_to_graph_scohg_vert_eq f
    _ _ (compose_sized_graphs_alt_correct _ _)).
  etransitivity. 2:{
    instantiate (1:=graph_to_pair_bundled _).
    constructor.
    apply (subrel' cohg_vert_eq).
    apply compose_graphs_alt_correct.
  }
  specialize (sized_graph_to_graph_add_top_loops f
    (swapped_stack_sized_graphs scohg scohg')) as Hrw.
  tspecialize Hrw. 1:{
    cbn.
    rewrite 2 vsplitl_app.
    rewrite 2 vec_to_list_map.
    rewrite <- 2 list_fmap_compose.
    rewrite list_eq_Forall2 in Heq |- *.
    rewrite Forall2_fmap in Heq |- *.
    apply Forall2_flip.
    apply (Forall2_impl _ _ _ _ Heq).
    intros p q.
    cbn -[bcons].
    rewrite 2 lookup_union.
    rewrite 2 (lookup_kmap _).
    rewrite 2 (lookup_kmap_None _ _ _).2 by lia.
    rewrite (left_id_L None _), (right_id_L None _).
    now intros ->.
  }
  destruct Hrw as (eql & eqr & Hrw).
  rewrite Hrw.

  apply add_top_loops_bundled_struct_isomorphic.
  - cbn.
    rewrite vsplitl_app.
    apply sum_list_with_eq_of_fmap.
    rewrite vec_to_list_map, <- list_fmap_compose.
    apply list_eq_Forall2.
    apply Forall2_fmap.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros i _.
    cbn -[bcons].
    rewrite lookup_union.
    rewrite (lookup_kmap _), (lookup_kmap_None _ _ _).2 by lia.
    rewrite (left_id_L None _).
    done.
  - rewrite cast_graph_bundled_eq.
    rewrite (sized_graph_to_graph_swapped_stack_graphs f scohg scohg').
    symmetry.
    rewrite (graph_to_pair_bundled_apply2 (fun _ _ _ _ => swapped_stack_graphs)).
    rewrite cast_graph_bundled_eq.
    done.
Qed.


From TensorRocq Require Import Isomorphism.IsoAux.

Lemma isomorphic_id_graph_of_empty_NoDup {T n}
  (cohg : CospanHyperGraph T n n) :
  hedges cohg = ∅ ->
  inputs cohg = outputs cohg ->
  NoDup (inputs cohg) ->
  isomorphic cohg (id_graph _).
Proof.
  intros Hhedges Hio Hdup.
  symmetry.
  apply (isomorphic_of_partial_inj' _ _
    (Pmap_injmap (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p)) (inputs cohg)))) id).
  - intros ? ? _ _.
    apply Pmap_injmap_inj.
    apply map_inj_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_seq_0.
      apply (NoDup_fmap _), NoDup_seq.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_to_fmap.
      now rewrite list_fmap_id.
  - easy.
  - enough (Hen : _) by
    (apply cohg_ext; [apply Hhedges| |rewrite <- Hio];
    exact Hen).
    cbn.
    apply vec_eq.
    intros i.
    rewrite 2 vlookup_map, vlookup_seq.
    cbn.
    symmetry.
    apply Pmap_injmap_correct.
    rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
    rewrite pos_to_nat_pred_of_nat.
    rewrite lookup_vec_to_list_fin.
    done.
Qed.


Lemma isomorphic_cap_graph_of_empty_NoDup {T n}
  (cohg : CospanHyperGraph T (n + n) 0) :
  hedges cohg = ∅ ->
  vsplitl (inputs cohg) = vsplitr (inputs cohg) ->
  NoDup (vsplitl (inputs cohg)) ->
  isomorphic cohg (cap_graph _).
Proof.
  intros Hhedges Hio Hdup.
  symmetry.
  apply (isomorphic_of_partial_inj' _ _
    (Pmap_injmap (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p)) (vsplitl (inputs cohg))))) id).
  - intros ? ? _ _.
    apply Pmap_injmap_inj.
    apply map_inj_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_seq_0.
      apply (NoDup_fmap _), NoDup_seq.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_to_fmap.
      now rewrite list_fmap_id.
  - easy.
  - apply cohg_ext; [apply Hhedges| |apply vec_eq, fin_0_inv].
    cbn.
    rewrite 2 Vector.map_append.
    rewrite <- (app_vsplit (inputs cohg)), <- Hio.
    refine ((fun H => f_equal2 vapp H H) _).

    apply vec_eq.
    intros i.
    rewrite 2 vlookup_map, vlookup_seq.
    cbn.
    symmetry.
    apply Pmap_injmap_correct.
    rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
    rewrite pos_to_nat_pred_of_nat.
    rewrite lookup_vec_to_list_fin.
    rewrite vsplitl_app.
    done.
Qed.

Lemma isomorphic_cup_graph_of_empty_NoDup {T n}
  (cohg : CospanHyperGraph T 0 (n + n)) :
  hedges cohg = ∅ ->
  vsplitl (outputs cohg) = vsplitr (outputs cohg) ->
  NoDup (vsplitl (outputs cohg)) ->
  isomorphic cohg (cup_graph _).
Proof.
  intros Hhedges Hio Hdup.
  symmetry.
  apply (isomorphic_of_partial_inj' _ _
    (Pmap_injmap (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p)) (vsplitl (outputs cohg))))) id).
  - intros ? ? _ _.
    apply Pmap_injmap_inj.
    apply map_inj_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_seq_0.
      apply (NoDup_fmap _), NoDup_seq.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_to_fmap.
      now rewrite list_fmap_id.
  - easy.
  - apply cohg_ext; [apply Hhedges| apply vec_eq, fin_0_inv|].
    cbn.
    rewrite 2 Vector.map_append.
    rewrite <- (app_vsplit (outputs cohg)), <- Hio.
    refine ((fun H => f_equal2 vapp H H) _).

    apply vec_eq.
    intros i.
    rewrite 2 vlookup_map, vlookup_seq.
    cbn.
    symmetry.
    apply Pmap_injmap_correct.
    rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
    rewrite pos_to_nat_pred_of_nat.
    rewrite lookup_vec_to_list_fin.
    rewrite vsplitl_app.
    done.
Qed.

Lemma isomorphic_swap_graph_of_empty_NoDup {T n m}
  (cohg : CospanHyperGraph T (n + m) (m + n)) :
  hedges cohg = ∅ ->
  inputs cohg = vsplitr (outputs cohg) +++ vsplitl (outputs cohg) ->
  NoDup (inputs cohg) ->
  isomorphic cohg (swap_graph _ _).
Proof.
  intros Hhedges Hio Hdup.
  symmetry.
  apply (isomorphic_of_partial_inj' _ _
    (Pmap_injmap (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p)) (inputs cohg)))) id).
  - intros ? ? _ _.
    apply Pmap_injmap_inj.
    apply map_inj_list_to_map.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_seq_0.
      apply (NoDup_fmap _), NoDup_seq.
    + rewrite fmap_imap; unfold compose; cbn.
      rewrite imap_to_fmap.
      now rewrite list_fmap_id.
  - easy.
  - eenough (Hen : _); [
    apply cohg_ext; [apply Hhedges|exact Hen|refine (_ Hen)]|].
    + cbn.
      rewrite Hio at 1.
      rewrite 4 Vector.map_append.
      intros Heq.
      rewrite <- (app_vsplit (outputs cohg)).
      f_equal.
      * apply (f_equal vsplitr) in Heq.
        now rewrite 2 vsplitr_app in Heq.
      * apply (f_equal vsplitl) in Heq.
        now rewrite 2 vsplitl_app in Heq.
    + cbn.
      apply vec_eq.
      intros i.
      rewrite <- vseq_app, 2 vlookup_map, vlookup_seq.
      cbn.
      symmetry.
      apply Pmap_injmap_correct.
      rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
      rewrite pos_to_nat_pred_of_nat.
      rewrite lookup_vec_to_list_fin.
      done.
Qed.

(* Require Import GraphRewriting stdpp.list. *)

(* TODO: *)

Lemma map_inj_iff_NoDup_snd_map_to_list `{FinMap K M} {A}
  (m : M A) : map_inj m <-> NoDup (map_to_list m).*2.
Proof.
  split.
  - intros Hinj.
    apply NoDup_fmap_2_strong, NoDup_map_to_list.
    intros [k a] [k' a'].
    cbn.
    rewrite 2 elem_of_map_to_list.
    intros ? ? <-.
    f_equal.
    now apply (Hinj _ _ a).
  - intros Hdup.
    intros j k a Hj Hk.
    specialize (NoDup_fmap_1_strong _ _ Hdup) as Hinj.
    specialize (Hinj (j, a) (k, a)).
    rewrite 2 elem_of_map_to_list in Hinj.
    enough ((j, a) = (k, a)) by congruence.
    now apply Hinj.
Qed.

(* Lemma map_inj_kmap_1 `{FinMap K1 M1, FinMap K2 M2} {A}
  (f : K1 -> K2) (m : M1 A) :
  map_inj (kmap f m :> M2 A) -> map_inj m.
Proof.
  rewrite 2 map_inj_iff_NoDup_snd_map_to_list.

  map_to_list_kmap.

  intros Hinj k k' a.
  split.
  -  *)

Lemma map_inj_kmap `{FinMap K1 M1, FinMap K2 M2} {A}
  (f : K1 -> K2) `{Hf : !Inj eq eq f} (m : M1 A) :
  map_inj (kmap f m :> M2 A) <-> map_inj m.
Proof.
  rewrite map_inj_iff_NoDup_snd_map_to_list.
  rewrite (map_to_list_kmap _).
  rewrite snds_prod_map, list_fmap_id.
  now rewrite map_inj_iff_NoDup_snd_map_to_list.
Qed.

Lemma isomorphic_graph_of_tensor_of_singleton_NoDup {T n m}
  (cohg : CospanHyperGraph T n m) k tio :
  hedges cohg = mk_hg {[k := tio]} ∅ ->
  vec_to_list (inputs cohg) = tio.1.2 ->
  vec_to_list (outputs cohg) = tio.2 ->
  NoDup (inputs cohg ++ outputs cohg) ->
  isomorphic cohg (graph_of_tensor tio.1.1 n m).
Proof.
  intros Hhedges Hi Ho Hdup.
  symmetry.
  apply (isomorphic_of_partial_inj' _ _
    (Pmap_injmap
      ((kmap (bcons false) (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p))
        (inputs cohg)))) ∪ (kmap (bcons true)
        (list_to_map (imap (λ i p, (Pos.of_succ_nat i, p)) (outputs cohg))))))
    (λ _, k)).
  - refine (fun _ _ _ _ => Pmap_injmap_inj _ _ _ _).
    apply NoDup_app in Hdup.
    apply map_inj_disj_union; [now apply (kmap_inj2_disjoint bcons)|..].
    + apply (map_inj_kmap _).
      apply map_inj_list_to_map.
      * rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_seq_0.
        apply (NoDup_fmap _), NoDup_seq.
      * rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_to_fmap.
        now rewrite list_fmap_id.
    + apply (map_inj_kmap _).
      apply map_inj_list_to_map.
      * rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_seq_0.
        apply (NoDup_fmap _), NoDup_seq.
      * rewrite fmap_imap; unfold compose; cbn.
        rewrite imap_to_fmap.
        now rewrite list_fmap_id.
    + clear -Hdup.
      intros i j a b.
      intros Ha%(elem_of_map_img_2 (SA:=Pset)).
      intros Hb%(elem_of_map_img_2 (SA:=Pset)).
      rewrite (map_img_kmap _) in Ha.
      rewrite (map_img_kmap _) in Hb.
      rewrite map_img_list_to_map in Ha, Hb by
        now rewrite fmap_imap; unfold compose; cbn;
        rewrite imap_seq_0; apply (NoDup_fmap _), NoDup_seq.
      rewrite fmap_imap in Ha, Hb.
      unfold compose in Ha, Hb.
      cbn in Ha, Hb.
      rewrite imap_to_fmap, list_fmap_id, elem_of_list_to_set in Ha, Hb.
      intros ->; eapply Hdup.2.1; eauto.
  - intros i j tabs tabs'.
    cbn -[singletonM].
    rewrite hyperedges_singleton.
    rewrite 2 lookup_singleton_Some.
    now intros [<- _] [<- _].
  - refine ((fun Hig Hog =>
    cohg_ext _ _ (_ Hig Hog) Hig Hog) _ _).
    + intros His Hos.
      rewrite Hhedges.
      apply hg_ext; [|done].
      cbn -[singletonM].
      rewrite hyperedges_singleton.
      rewrite kmap_singleton, map_fmap_singleton.
      f_equal.
      rewrite (surjective_pairing tio),
        (surjective_pairing tio.1) at 1.
      cbn.
      f_equal; [f_equal|].
      cbn in His, Hos.
      * rewrite <- Hi.
        rewrite Hig at 1.
        cbn.
        rewrite 2 vec_to_list_map, vec_to_list_seq.
        done.
      * rewrite <- Ho.
        rewrite Hog at 1.
        cbn.
        rewrite 2 vec_to_list_map, vec_to_list_seq.
        done.
    + cbn.
      apply vec_eq.
      intros i.
      rewrite 2 vlookup_map, vlookup_seq.
      cbn -[bcons].
      symmetry.
      apply Pmap_injmap_correct.
      rewrite lookup_union, (lookup_kmap _), (lookup_kmap_None _ _ _).2 by lia.
      rewrite (right_id_L None _).
      rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
      rewrite pos_to_nat_pred_of_nat.
      rewrite lookup_vec_to_list_fin.
      done.
    + cbn.
      apply vec_eq.
      intros i.
      rewrite 2 vlookup_map, vlookup_seq.
      cbn -[bcons].
      symmetry.
      apply Pmap_injmap_correct.
      rewrite lookup_union, (lookup_kmap _), (lookup_kmap_None _ _ _).2 by lia.
      rewrite (left_id_L None _).
      rewrite lookup_list_to_map_imap_to_pos, option_fmap_id.
      rewrite pos_to_nat_pred_of_nat.
      rewrite lookup_vec_to_list_fin.
      done.
Qed.

Lemma isomorphic_graph_of_tensor_of_singleton_NoDup' {T n m}
  (cohg : CospanHyperGraph T n m) k t :
  hedges cohg = mk_hg {[k := (t, vec_to_list (inputs cohg), vec_to_list (outputs cohg))]} ∅ ->
  NoDup (inputs cohg ++ outputs cohg) ->
  isomorphic cohg (graph_of_tensor t n m).
Proof.
  intros Hcohg Hdup.
  eapply (isomorphic_graph_of_tensor_of_singleton_NoDup cohg k (t, _, _)); cbn; eauto.
Qed.





Lemma sized_graph_to_graph_id_sized_graph {N T} (f : N -> nat)
  {n} (v : vec N n) :
  isomorphic (sized_graph_to_graph f (@id_sized_graph N T n v))
  (id_graph _)%cohg.
Proof.
  apply isomorphic_id_graph_of_empty_NoDup.
  - done.
  - done.
  - cbn.
    rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
    apply NoDup_bind, (NoDup_fmap _), NoDup_seq.
    + intros x0 x1 y.
      intros (p & -> & Hp)%elem_of_list_fmap
        (q & -> & Hq)%elem_of_list_fmap.
      rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
      set_solver +.
    + intros p Hp.
      rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
      apply (NoDup_fmap _), NoDup_seq.
Qed.

Lemma helper_sized_graph_sum_eq {N} (f : N -> nat) :
  forall n (v : vec N n), sum_list_with f v = sum_list_with ((λ p,
      default 0 (f <$> list_to_map (M:=Pmap _) (imap (λ i k, (Pos.of_succ_nat i, k)) v)
         !! p))) (vmap Pos.of_succ_nat (vseq 0 n)).
Proof.
  intros n' v'.
  rewrite vec_to_list_map, sum_list_with_fmap.
  apply sum_list_with_eq_of_fmap.
  rewrite <- 2 vec_to_list_map.
  f_equal.
  apply vec_eq.
  intros i.
  rewrite 2 vlookup_map, vlookup_seq.
  cbn.
  rewrite lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat.
  rewrite lookup_vec_to_list_fin.
  done.
Qed.


Lemma sized_graph_to_graph_id_sized_graph' {N T} (f : N -> nat)
  {n} (v : vec N n) :
  ((sized_graph_to_graph f (@id_sized_graph N T n v)) [≡ᵢ]ₛ
  (id_graph (sum_list_with f v)))%cohg.
Proof.
  etransitivity; [instantiate (1:=graph_to_pair_bundled _);
    constructor; apply (subrel (sized_graph_to_graph_id_sized_graph _ _))|].
  apply sigT2_relation_alt.
  apply exists_by_forall.
  - cbn.
    now rewrite <- (helper_sized_graph_sum_eq f).
  - cbn.
    rewrite <- (helper_sized_graph_sum_eq f).
    intros H.
    rewrite (proof_irrel H eq_refl).
    done.
Qed.



Lemma sized_graph_to_graph_cup_sized_graph {N T} (f : N -> nat)
  {n} (v : vec N n) :
  sigT2_relation (@isomorphic T)
    (graph_to_pair_bundled (sized_graph_to_graph f (@cup_sized_graph N T n v)))
    (graph_to_pair_bundled (cup_graph (sum_list_with f v))).
Proof.
  symmetry.
  apply sigT2_relation_alt.
  cbn.
  assert (Hsizeeq : sum_list_with f v = sum_list_with ((λ p,
      default 0 (f <$> list_to_map (M:=Pmap _) (imap (λ i k, (Pos.of_succ_nat i, k)) v)
         !! p))) (vmap Pos.of_succ_nat (vseq 0 n))). 1:{
    rewrite vec_to_list_map, sum_list_with_fmap.
    apply sum_list_with_eq_of_fmap.
    rewrite <- 2 vec_to_list_map.
    f_equal.
    apply vec_eq.
    intros i.
    rewrite 2 vlookup_map, vlookup_seq.
    cbn.
    rewrite lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat.
    rewrite lookup_vec_to_list_fin.
    done.
  }
  apply exists_by_forall.
  - f_equal.
    rewrite Vector.map_append.
    rewrite vec_to_list_app, vec_to_list_map.
    rewrite <- fmap_app.
    rewrite sum_list_with_fmap.
    rewrite sum_list_with_app.
    refine ((fun H => f_equal2 Nat.add H H) _).
    rewrite Hsizeeq.
    now rewrite vec_to_list_map, sum_list_with_fmap.
  - intros H.
    symmetry.
    apply isomorphic_cup_graph_of_empty_NoDup.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite hedges_cast_graph.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite outputs_cast_graph.
      cbn.
      revert H.
      rewrite (Vector.map_append), vbind_app; intros H.
      rewrite cast_cast.
      rewrite (cast_app (eq_sym Hsizeeq) (eq_sym Hsizeeq)).
      rewrite vsplitl_app, vsplitr_app.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite outputs_cast_graph.
      cbn.
      revert H.
      rewrite (Vector.map_append), vbind_app; intros H.
      rewrite cast_cast.
      rewrite (cast_app (eq_sym Hsizeeq) (eq_sym Hsizeeq)).
      rewrite vsplitl_app.
      rewrite vec_to_list_cast.
      rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
      apply NoDup_bind, (NoDup_fmap _), NoDup_seq.
      * intros x0 x1 y.
        intros (p & -> & Hp)%elem_of_list_fmap
          (q & -> & Hq)%elem_of_list_fmap.
        rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        set_solver +.
      * intros p Hp.
        rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        apply (NoDup_fmap _), NoDup_seq.
Qed.

Lemma sized_graph_to_graph_cap_sized_graph {N T} (f : N -> nat)
  {n} (v : vec N n) :
  sigT2_relation (@isomorphic T)
    (graph_to_pair_bundled (sized_graph_to_graph f (@cap_sized_graph N T n v)))
    (graph_to_pair_bundled (cap_graph (sum_list_with f v))).
Proof.
  symmetry.
  apply sigT2_relation_alt.
  cbn.
  assert (Hsizeeq : sum_list_with f v = sum_list_with ((λ p,
      default 0 (f <$> list_to_map (M:=Pmap _) (imap (λ i k, (Pos.of_succ_nat i, k)) v)
         !! p))) (vmap Pos.of_succ_nat (vseq 0 n))). 1:{
    rewrite vec_to_list_map, sum_list_with_fmap.
    apply sum_list_with_eq_of_fmap.
    rewrite <- 2 vec_to_list_map.
    f_equal.
    apply vec_eq.
    intros i.
    rewrite 2 vlookup_map, vlookup_seq.
    cbn.
    rewrite lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat.
    rewrite lookup_vec_to_list_fin.
    done.
  }
  apply exists_by_forall.
  - f_equal.
    rewrite Vector.map_append.
    rewrite vec_to_list_app, vec_to_list_map.
    rewrite <- fmap_app.
    rewrite sum_list_with_fmap.
    rewrite sum_list_with_app.
    refine ((fun H => f_equal2 Nat.add H H) _).
    rewrite Hsizeeq.
    now rewrite vec_to_list_map, sum_list_with_fmap.
  - intros H.
    symmetry.
    apply isomorphic_cap_graph_of_empty_NoDup.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite hedges_cast_graph.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite inputs_cast_graph.
      cbn.
      revert H.
      rewrite (Vector.map_append), vbind_app; intros H.
      rewrite cast_cast.
      rewrite (cast_app (eq_sym Hsizeeq) (eq_sym Hsizeeq)).
      rewrite vsplitl_app, vsplitr_app.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite inputs_cast_graph.
      cbn.
      revert H.
      rewrite (Vector.map_append), vbind_app; intros H.
      rewrite cast_cast.
      rewrite (cast_app (eq_sym Hsizeeq) (eq_sym Hsizeeq)).
      rewrite vsplitl_app.
      rewrite vec_to_list_cast.
      rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
      apply NoDup_bind, (NoDup_fmap _), NoDup_seq.
      * intros x0 x1 y.
        intros (p & -> & Hp)%elem_of_list_fmap
          (q & -> & Hq)%elem_of_list_fmap.
        rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        set_solver +.
      * intros p Hp.
        rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        apply (NoDup_fmap _), NoDup_seq.
Qed.


Lemma sized_graph_to_graph_swap_sized_graph {N T} (f : N -> nat)
  {n m} (v : vec N n) (w : vec N m) :
  sigT2_relation (@isomorphic T)
    (graph_to_pair_bundled (sized_graph_to_graph f (@swap_sized_graph N T n m v w)))
    (graph_to_pair_bundled (swap_graph (sum_list_with f v) (sum_list_with f w))).
Proof.
  symmetry.
  apply sigT2_relation_alt.
  cbn.
  pose proof (helper_sized_graph_sum_eq f) as Hvw.
  assert (Hv : sum_list_with (λ p, default 0 (f <$>
    list_to_map (M:=Pmap _) (imap (λ i k, (Pos.of_succ_nat i, k)) (v ++ w)) !! p))
      (vmap Pos.of_succ_nat (vseq 0 n)) = sum_list_with f v). 1:{
    rewrite Hvw.
    apply sum_list_with_ext.
    intros a.
    rewrite vec_to_list_map, vec_to_list_seq.
    intros (i & -> & Hi%elem_of_seq)%elem_of_list_fmap.
    rewrite 2 lookup_list_to_map_imap_to_pos, pos_to_nat_pred_of_nat, 2 option_fmap_id.
    rewrite lookup_app_l by now rewrite length_vec_to_list.
    done.
  }
  assert (Hw : sum_list_with (λ p, default 0 (f <$>
    list_to_map (M:=Pmap _) (imap (λ i k, (Pos.of_succ_nat i, k)) (v ++ w)) !! p))
      (vmap Pos.of_succ_nat (vseq n m)) = sum_list_with f w). 1:{
    specialize (Hvw _ (v +++ w)).
    revert Hvw.
    rewrite vseq_app, Vector.map_append, 2 vec_to_list_app, 2 sum_list_with_app.
    cbn.
    lia.
  }
  apply exists_by_forall.
  - rewrite Nat.add_comm.
    symmetry.
    rewrite 2 Vector.map_append, 2 vec_to_list_app, 2 sum_list_with_app.
    rewrite Nat.add_comm.
    apply (f_equal (λ a, (a, a))).
    rewrite Nat.add_comm.
    rewrite <- sum_list_with_app, <- 2 vec_to_list_app, <- Vector.map_append.
    rewrite <- vseq_app.
    rewrite <- Hvw.
    rewrite vec_to_list_app, sum_list_with_app.
    apply Nat.add_comm.
  - intros H.
    symmetry.
    apply isomorphic_swap_graph_of_empty_NoDup.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite hedges_cast_graph.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite inputs_cast_graph, outputs_cast_graph.
      cbn.
      revert H.
      rewrite 2 (Vector.map_append), 2 vbind_app; intros H.
      rewrite 2 cast_cast.
      rewrite (cast_app Hv Hw).
      rewrite (cast_app Hw Hv).
      clear.
      rewrite vsplitl_app, vsplitr_app.
      done.
    + unfold eq_rect_r.
      rewrite cast_pair_to_cast_graph.
      rewrite inputs_cast_graph.
      rewrite vec_to_list_cast.
      cbn.
      rewrite <- vseq_app.
      rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
      apply NoDup_bind, (NoDup_fmap _), NoDup_seq.
      * intros x0 x1 y.
        intros (p & -> & Hp)%elem_of_list_fmap
          (q & -> & Hq)%elem_of_list_fmap.
        rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        set_solver +.
      * intros p Hp.
        rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        apply (NoDup_fmap _), NoDup_seq.
Qed.


Lemma sized_graph_to_graph_sized_graph_of_tensor {N T} (f : N -> nat)
  {n m} (v : vec N n) (w : vec N m) t :
  isomorphic
    (sized_graph_to_graph f (@sized_graph_of_tensor N T t n m v w))
    (graph_of_tensor t _ _).
Proof.
  eapply (isomorphic_graph_of_tensor_of_singleton_NoDup' _ 1 t).
  - apply hg_ext; [|done].
    cbn -[singletonM].
    rewrite hyperedges_singleton.
    rewrite map_fmap_singleton.
    cbn.
    f_equal.
    f_equal; [f_equal|].
    + rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
      done.
    + rewrite vec_to_list_bind, vec_to_list_map, vec_to_list_seq.
      done.
  - cbn.
    rewrite 2 vec_to_list_bind, <- bind_app.
    rewrite 2 vec_to_list_map, 2 vec_to_list_seq.
    apply NoDup_bind.
    + intros x0 x1 y.
      rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
      intros _ _.
      (* intros [Hx0|Hx0]%elem_of_app
      [Hx1|Hx1]%elem_of_app;
      apply elem_of_list_fmap in Hx0 as (p & -> & Hp);
      apply elem_of_list_fmap in Hx1 as (q & -> & Hq). *)
      (* rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))). *)
      set_solver +.
    + intros p Hp.
      rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
      apply (NoDup_fmap _), NoDup_seq.
    + apply NoDup_app.
      split_and!; cycle 1; [|apply (NoDup_fmap _), NoDup_seq..].
      set_solver.
Qed.


Lemma sized_graph_to_graph_sized_graph_of_tensor' {N T} (f : N -> nat)
  {n m} (v : vec N n) (w : vec N m) t :
  sigT2_relation (@isomorphic T)
    (graph_to_pair_bundled
      (sized_graph_to_graph f (@sized_graph_of_tensor N T t n m v w)))
    (graph_to_pair_bundled
      (graph_of_tensor t (sum_list_with f v) (sum_list_with f w))).
Proof.
  etransitivity; [instantiate (1:=graph_to_pair_bundled _);
    constructor; apply (subrel (sized_graph_to_graph_sized_graph_of_tensor _ _ _ _))|].
  replace (sum_list_with _ _) with (sum_list_with f v);
  [replace (sum_list_with _ (outputs _)) with (sum_list_with f w); [done|]|].
  - cbn.
    rewrite (helper_sized_graph_sum_eq f _ w).
    rewrite 2 vec_to_list_map, 2 sum_list_with_fmap.
    apply sum_list_with_ext.
    intros i _.
    cbn.
    rewrite lookup_union, lookup_list_to_map_imap_to_pos.
    rewrite (lookup_list_to_map_imap (λ i, (Pos.of_succ_nat i)~1)).
    rewrite (not_elem_of_dom_1 (list_to_map _)) by now rewrite dom_list_to_map,
      fmap_imap; unfold compose; cbn; rewrite imap_seq_0; set_solver.
    rewrite (left_id_L None _).
    now rewrite pos_to_nat_pred_of_nat.
  - cbn.
    rewrite (helper_sized_graph_sum_eq f _ v).
    rewrite 2 vec_to_list_map, 2 sum_list_with_fmap.
    apply sum_list_with_ext.
    intros i _.
    cbn.
    rewrite lookup_union, lookup_list_to_map_imap_to_pos.
    rewrite (lookup_list_to_map_imap (λ i, (Pos.of_succ_nat i)~0)).
    rewrite (not_elem_of_dom_1 (list_to_map _)) by now rewrite dom_list_to_map,
      fmap_imap; unfold compose; cbn; rewrite imap_seq_0; set_solver.
    rewrite (right_id_L None _).
    now rewrite pos_to_nat_pred_of_nat.
Qed.