Require Export CospanHyperGraph.Definitions Isomorphism.Testing Aux_pos.

Require Export Syntax.Definitions Syntax.Cospans.

(* FIXME: Move: *)
Require Combinators.



(* FIXME: Move: *)


#[export] Instance ntl_eq_of_ntl_aeq tl : subrelation ntl_aeq (ntl_eq tl).
Proof.
  intros ntl ntl' Hntl.
  hnf.
  apply rtc_once.
  now left.
Qed.

#[export] Instance ntl_eq_of_ntl_delta_eq tl :
  subrelation (ntl_delta_eq tl) (ntl_eq tl).
Proof.
  intros ntl ntl' Hntl.
  hnf.
  apply rtc_once.
  now right.
Qed.

Add Parametric Morphism : mk_ntl with signature
  Permutation ==> Permutation ==> Permutation ==> ntl_aeq as mk_ntl_perm_eq.
Proof.
  intros; now apply ntl_aeq_of_perm.
Qed.


#[local] Coercion pos_to_nat_pred : positive >-> nat.

(* Semantics of TensorGraphs into tensor expressions *)


Section TensorGraphExpr.

Context {T : Type}.
(* Context {n m : nat}. *)

Let TensorGraph := (CospanHyperGraph T).

(* Implicit Types tg : CospanHyperGraph. *)


Definition tg_abstracts (tm : Pmap (T * list positive * list positive)) :
  list (Idx * list var * list var) :=
  (λ k_flu : _*(_*list _*list _),
    (k_flu.1, bound <$> k_flu.2.1.2, bound <$> k_flu.2.2)) <$>
    (map_to_list tm :> list (positive * (T * list positive * list positive))).

Definition tg_list_to_deltas (is_output : bool)
  (idxs : list positive) : list (var * var) :=
  imap (λ idx input, (free $ bcons is_output (Pos.of_succ_nat idx), bound input))
    idxs.

(* The interpretation of a cospan of a hypergraph as a syntactic 
  [namedtensorlist]. *)
Definition graph_namedtensorlist_semantics {n m} (tg : TensorGraph n m) : namedtensorlist := {|
  ntl_sums := elements (vertices tg);
  ntl_abstracts := tg_abstracts tg.(hedges);
  ntl_deltas := tg_list_to_deltas false tg.(inputs)
    ++ tg_list_to_deltas true tg.(outputs);
|}.


(* The interpretation of a cospan of a hypergraph as a syntactic cospan of
  [namedtensorlist], representing a tensor. *)
Definition graph_contl_semantics {n m} (tg : TensorGraph n m) :
  CospanNamedTensorList n m :=
  mk_contl (graph_namedtensorlist_semantics tg)
    (vmap (bcons false ∘ Pos.of_succ_nat) $ vseq 0 n)
    (vmap (bcons true ∘ Pos.of_succ_nat) $ vseq 0 m).

Definition tg_list_to_deltas_offset (offset : nat) (is_output : bool)
  idxs : list (var * var) :=
  imap (λ idx input, (free $ bcons is_output
    (Pos.of_succ_nat (offset + idx)), bound input))
    idxs.


Definition graph_namedtensorlist_semantics_offset (noff moff : nat) {n m}
  (tg : TensorGraph n m) : namedtensorlist := {|
    ntl_sums := elements (vertices tg);
    ntl_abstracts := tg_abstracts tg.(hedges);
    ntl_deltas := tg_list_to_deltas_offset noff false tg.(inputs)
      ++ tg_list_to_deltas_offset moff true tg.(outputs);
  |}.

Definition graph_contl_semantics_offset (noff moff : nat) {n m} (tg : TensorGraph n m) :
  CospanNamedTensorList n m :=
  mk_contl (graph_namedtensorlist_semantics_offset noff moff tg)
    (vmap (bcons false ∘ Pos.of_succ_nat) $ vseq noff n)
    (vmap (bcons true ∘ Pos.of_succ_nat) $ vseq moff m).

Lemma tg_list_to_deltas_to_offset out idxs :
  tg_list_to_deltas out idxs = tg_list_to_deltas_offset 0 out idxs.
Proof.
  done.
Qed.

Lemma graph_namedtensorlist_semantics_to_offset `(tg : TensorGraph n m) :
  graph_namedtensorlist_semantics tg =
  graph_namedtensorlist_semantics_offset 0 0 tg.
Proof.
  done.
Qed.


Lemma abstracts_bound_vars_graph {o p} (tg : TensorGraph o p) :
  abstracts_bound_vars (graph_namedtensorlist_semantics tg).(ntl_abstracts) =
  list_to_set ('(_, low, up) ← (map_to_list tg.(hedges).(hyperedges)).*2; low ++ up).
Proof.
  unfold abstracts_bound_vars.
  cbn.
  f_equiv.
  unfold tg_abstracts.
  rewrite 2 list_fmap_bind.
  apply list_bind_ext; [|done].
  intros [k [[idx low] up]].
  cbn.
  rewrite <- fmap_app, list_omap_fmap.
  unfold compose; cbn.
  rewrite <- list_fmap_alt.
  apply list_fmap_id.
Qed.


Lemma deltas_bound_vars_graph {n m} (tg : TensorGraph n m) :
  deltas_bound_vars (graph_namedtensorlist_semantics tg).(ntl_deltas) =
  list_to_set ((vec_to_list tg.(inputs)) ++ (vec_to_list tg.(outputs))).
Proof.
  unfold deltas_bound_vars.
  cbn.
  rewrite bind_app.
  unfold tg_list_to_deltas.
  rewrite 2 imap_to_zip_with_seq.
  rewrite <- (fmap_zip_with pair
    (prod_map (free ∘ bcons false ∘ Pos.of_succ_nat) bound)),
    <- (fmap_zip_with pair
    (prod_map (free ∘ bcons true ∘ Pos.of_succ_nat) bound)).
  rewrite 2 list_fmap_bind.
  unfold compose, prod_map; cbn.
  now rewrite <- 2 list_fmap_to_bind, 2 snd_zip by now rewrite length_seq.
Qed.

Lemma abstracts_free_vars_graph {n m} (tg : TensorGraph n m) :
  abstracts_free_vars (graph_namedtensorlist_semantics tg).(ntl_abstracts) =
  ∅.
Proof.
  cbn.
  unfold tg_abstracts, abstracts_free_vars.
  rewrite list_fmap_bind.
  erewrite (list_bind_ext _ (λ _, nil)); [..|reflexivity]. 2:{
    intros [k [[f low] up]].
    cbn.
    rewrite <- fmap_app, list_omap_fmap.
    unfold compose; cbn.
    apply elem_of_nil_inv.
    now intros ? (?&?&?)%elem_of_list_omap.
  }
  now rewrite list_bind_nil_r.
Qed.

Lemma deltas_free_vars_graph {n m} (tg : TensorGraph n m) :
  deltas_free_vars (graph_namedtensorlist_semantics tg).(ntl_deltas) =
  list_to_set ((bcons false <$> pseq 1 (N.of_nat n)) ++
    (bcons true <$> pseq 1 (N.of_nat m))).
Proof.
  unfold deltas_free_vars.
  cbn.
  rewrite bind_app.
  unfold tg_list_to_deltas.
  rewrite 2 imap_to_zip_with_seq.
  rewrite <- (fmap_zip_with pair
    (prod_map (free ∘ bcons false ∘ Pos.of_succ_nat) bound)),
    <- (fmap_zip_with pair
    (prod_map (free ∘ bcons true ∘ Pos.of_succ_nat) bound)).
  rewrite 2 list_fmap_bind.
  unfold compose, prod_map; cbn -[bcons].
  rewrite <- (list_fmap_to_bind (bcons false ∘ Pos.of_succ_nat ∘ @fst _ Idx)).
  rewrite <- (list_fmap_to_bind (bcons true ∘ Pos.of_succ_nat ∘ @fst _ Idx)).
  rewrite 2 (list_fmap_compose fst), 2 fst_zip by now rewrite length_seq.
  rewrite 2 list_fmap_compose, 2 pseq_to_seq_inv.
  rewrite 2 length_vec_to_list.
  reflexivity.
Qed.


Lemma graph_namedtensorlist_semantics_WF {n m} (tg : TensorGraph n m) :
  WF_ntl (graph_namedtensorlist_semantics tg).
Proof.
  split; [|split].
  - cbn.
    apply NoDup_elements.
  - rewrite abstracts_bound_vars_graph.
    cbn.
    unfold vertices.
    rewrite list_to_set_elements.
    rewrite list_fmap_bind.
    etransitivity; [|apply union_subseteq_l].
    etransitivity; [|unfold vertices_hg; apply union_subseteq_l].
    apply list_to_set_subseteq.
    apply eq_reflexivity, list_bind_ext; [|done].
    now intros [? [[]]].
  - rewrite deltas_bound_vars_graph.
    cbn.
    unfold vertices.
    rewrite list_to_set_elements.
    apply union_subseteq_r.
Qed.





Lemma graph_namedtensorlist_semantics_relabel_graph
  (f : Idx -> Idx) `{Hfint : !Inj eq eq f} {n m} (tg : TensorGraph n m) :
  graph_namedtensorlist_semantics (relabel_graph f tg) =ntl=
  graph_namedtensorlist_semantics tg.
Proof.
  symmetry.
  exists f.
  split; [intros ? ? ? ?; apply Hfint|].
  split; [|split].
  - cbn.
    rewrite vertices_relabel_graph.
    now rewrite <- (fmap_elements _).
  - cbn.
    unfold tg_abstracts.
    rewrite map_to_list_fmap, <- 2 list_fmap_compose.
    apply eq_reflexivity, list_fmap_ext; intros _ [k [[idx low] up]] _.
    cbn.
    rewrite <- 4 list_fmap_compose.
    reflexivity.
  - cbn.
    unfold tg_list_to_deltas.
    rewrite fmap_app, 2 fmap_imap.
    rewrite 2 vec_to_list_map, 2 imap_fmap.
    reflexivity.
Qed.


Lemma graph_namedtensorlist_semantics_reindex_graph
  (f : Idx -> Idx) `{Hfint : !Inj eq eq f} {n m} (tg : TensorGraph n m) :
  graph_namedtensorlist_semantics (reindex_graph f tg) =ntl=
  ntl_relabel_absidx f (graph_namedtensorlist_semantics tg).
Proof.
  unfold graph_namedtensorlist_semantics, ntl_relabel_absidx; cbn.
  rewrite (vertices_reindex_graph _).
  apply ntl_aeq_of_perm; [done| |done].
  cbn.
  unfold tg_abstracts.
  unfold kmap.
  rewrite map_to_list_to_map by now
    rewrite fsts_prod_map, (NoDup_fmap _); apply NoDup_fst_map_to_list.
  rewrite <- 2 list_fmap_compose.
  reflexivity.
Qed.

Lemma abstracts_bound_vars_ntl_relabel_absidx f ntl :
  abstracts_bound_vars (ntl_relabel_absidx f ntl).(ntl_abstracts) =
  abstracts_bound_vars ntl.(ntl_abstracts).
Proof.
  apply set_eq.
  intros r.
  rewrite 2 elem_of_abstracts_bound_vars.
  cbn.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite exists_pair.
  setoid_rewrite exists_pair.
  cbn.
  setoid_rewrite pair_eq.
  setoid_rewrite pair_eq.
  naive_solver.
Qed.

Lemma deltas_bound_vars_ntl_relabel_absidx f ntl :
  deltas_bound_vars (ntl_relabel_absidx f ntl).(ntl_deltas) =
  deltas_bound_vars ntl.(ntl_deltas).
Proof.
  reflexivity.
Qed.



Lemma ntl_relabel_absidx_aeq f `{Hf : !Inj eq eq f} ntl ntl' :
  ntl =ntl= ntl' ->
  ntl_relabel_absidx f ntl =ntl=
  ntl_relabel_absidx f ntl'.
Proof.
  intros (fr & Hfrinj & Hsums & Habs & Hdelt).
  exists fr.
  rewrite abstracts_bound_vars_ntl_relabel_absidx,
    deltas_bound_vars_ntl_relabel_absidx.
  split; [apply Hfrinj|].
  split; [apply Hsums|].
  split; [|apply Hdelt].
  cbn.
  rewrite <- Habs.
  rewrite <- 2 list_fmap_compose.
  apply eq_reflexivity, list_fmap_ext; now intros _ [[]] _.
Qed.


Lemma graph_namedtensorlist_semantics_isomorphic {n m} (tg tg' : TensorGraph n m) :
  isomorphic tg tg' ->
  exists fv, Inj eq eq fv /\
  ntl_relabel_absidx fv (graph_namedtensorlist_semantics tg) =ntl=
  graph_namedtensorlist_semantics tg'.
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%isomorphic_exists.
  exists fv.
  split; [easy|].
  rewrite (graph_namedtensorlist_semantics_relabel_graph _),
    (graph_namedtensorlist_semantics_reindex_graph _).
  reflexivity.
Qed.

(* FIXME: Move *)
(* Lemma ntl_aeq_of_WF ntl ntl' : WF_ntl ntl ->
  (exists fr,
    set_Forall2 (λ i j, fr i = fr j -> i = j) (list_to_set ntl.(ntl_sums).*1:>Pset ) /\
    prod_map fr id <$> ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\
    relabel_abs (relabel_bounds fr) <$> ntl.(ntl_abstracts) ≡ₚ ntl'.(ntl_abstracts)
    ) ->
  ntl =ntl= ntl'.
Proof.
  intros HWF (fr & Hfr & Hsums & Habs).
  exists fr.
  split; [|easy].
  intros x y Hx Hy.
  apply Hfr; specialize (HWF.2); [set_solver +Hx|set_solver +Hy].
Qed. *)

Lemma relabel_frees_tg_abstracts f (hg : Pmap (T * _ * _)) :
  relabel_abs (relabel_frees f) <$> tg_abstracts hg = tg_abstracts hg.
Proof.
  apply list_fmap_id'.
  intros _ ((k & [[idx low] up]) & -> & _)%elem_of_list_fmap.
  cbn.
  now rewrite <- 2 list_fmap_compose.
Qed.

(* Lemma tg_list_to_deltas_offset_correct off out idxs :
  tg_list_to_deltas off out idxs =
   *)

Lemma graph_namedtensorlist_semantics_offset_correct noff moff `(tg : TensorGraph n m) :
  graph_namedtensorlist_semantics_offset noff moff tg =
  ntl_relabel_free (pos_map (pos_nat_add noff) (pos_nat_add moff))
  (graph_namedtensorlist_semantics tg).
Proof.
  apply ntl_ext; cbn.
  - done.
  - rewrite relabel_frees_tg_abstracts.
    done.
  - symmetry; rewrite fmap_app.
    unfold tg_list_to_deltas, tg_list_to_deltas_offset.
    rewrite 2 fmap_imap.
    f_equal; apply imap_ext; intros ? ? _; f_equal/=; f_equal; lia.
Qed.

Lemma graph_contl_semantics_offset_correct' noff moff `(tg : TensorGraph n m) :
  contl_interface_eq (graph_contl_semantics_offset noff moff tg)
    (graph_contl_semantics tg).
Proof.
  symmetry.
  apply contl_interface_eq_iff_exists.
  exists (pos_map (pos_nat_add noff) (pos_nat_add moff)).
  split; [apply _|].
  apply contl_ext; cbn.
  - now rewrite graph_namedtensorlist_semantics_offset_correct.
  - apply vec_eq.
    intros i.
    rewrite 3 vlookup_map, 2 vlookup_seq.
    cbn.
    lia.
  - apply vec_eq.
    intros i.
    rewrite 3 vlookup_map, 2 vlookup_seq.
    cbn.
    lia.
Qed.

Lemma graph_contl_semantics_offset_correct noff moff `(tg : TensorGraph n m) :
  contl_eq (graph_contl_semantics_offset noff moff tg)
    (graph_contl_semantics tg).
Proof.
  apply rtc_once; constructor.
  apply graph_contl_semantics_offset_correct'.
Qed.



Lemma tg_abstracts_relabel_abs (f : positive -> positive)
  (hg : Pmap (T * _ * _)) :
  tg_abstracts (relabel_abs f <$> hg) =
  relabel_abs (relabel_bounds f) <$> tg_abstracts hg.
Proof.
  unfold tg_abstracts.
  rewrite map_to_list_fmap.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; intros _ [k [[? l] u]] _.
  cbn.
  f_equal; [f_equal|];
  rewrite <- 2 list_fmap_compose; done.
Qed.

Lemma tg_abstracts_union (hg hg' : Pmap (T * _ * _)) :
  (hg :> Pmap _) ##ₘ (hg' :> Pmap _) ->
  tg_abstracts (hg ∪ hg') ≡ₚ
  tg_abstracts hg ++ tg_abstracts hg'.
Proof.
  intros Hdisj.
  unfold tg_abstracts.
  cbn.
  rewrite map_to_list_disj_union by done.
  now rewrite fmap_app.
Qed.

Lemma tg_abstracts_kmap f `{Hf : !Inj eq eq f} (hg : Pmap (T * _ * _)) :
  tg_abstracts (kmap f hg) ≡ₚ
  prod_map (prod_map f id) id <$> tg_abstracts hg.
Proof.
  unfold tg_abstracts.
  rewrite (map_to_list_kmap _).
  rewrite <- 2 list_fmap_compose.
  done.
Qed.

Lemma vertices_swapped_stack_graphs_aux {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  tg.(hedges).(hyperedges) ##ₘ tg'.(hedges).(hyperedges) ->
  vertices (swapped_stack_graphs_aux tg tg') =
  vertices tg ∪ vertices tg'.
Proof.
  intros Hdisj.
  unfold vertices; cbn.
  rewrite vertices_hg_union by done.
  rewrite 2 vec_to_list_app, 5 list_to_set_app_L.
  apply set_eq; intros x.
  rewrite 10 elem_of_union. tauto.
Qed.

Lemma vertices_swapped_stack_graphs {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  vertices (swapped_stack_graphs tg tg') =
  set_map (bcons false) (vertices tg) ∪
  set_map (bcons true) (vertices tg').
Proof.
  unfold swapped_stack_graphs.
  rewrite vertices_swapped_stack_graphs_aux.
  - now rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _).
  - cbn.
    rewrite map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
Qed.

Lemma vertices_stack_graphs_aux {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  tg.(hedges).(hyperedges) ##ₘ tg'.(hedges).(hyperedges) ->
  vertices (stack_graphs_aux tg tg') =
  vertices tg ∪ vertices tg'.
Proof.
  intros Hdisj.
  unfold vertices; cbn.
  rewrite vertices_hg_union by done.
  rewrite 2 vec_to_list_app, 5 list_to_set_app_L.
  apply set_eq; intros x.
  rewrite 10 elem_of_union. tauto.
Qed.

Lemma vertices_stack_graphs {n m n' m'}
  (tg : TensorGraph n m) (tg' : TensorGraph n' m') :
  vertices (stack_graphs tg tg') =
  set_map (bcons false) (vertices tg) ∪
  set_map (bcons true) (vertices tg').
Proof.
  unfold stack_graphs.
  rewrite vertices_stack_graphs_aux.
  - now rewrite 2 vertices_relabel_graph, 2 (vertices_reindex_graph _).
  - cbn.
    rewrite map_disjoint_fmap.
    now apply (kmap_inj2_disjoint _).
Qed.


Lemma ntl_relabel_absidx_relabel_free f g ntl :
  ntl_relabel_absidx f (ntl_relabel_free g ntl) =
  ntl_relabel_free g (ntl_relabel_absidx f ntl).
Proof.
  unfold ntl_relabel_absidx, ntl_relabel_free.
  cbn.
  f_equal.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; now intros _ [[]] _.
Qed.

Lemma ntl_relabel_absidx_relabel_bound f g ntl :
  ntl_relabel_absidx f (ntl_relabel_bound g ntl) =
  ntl_relabel_bound g (ntl_relabel_absidx f ntl).
Proof.
  unfold ntl_relabel_absidx, ntl_relabel_bound.
  cbn.
  f_equal.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; now intros _ [[]] _.
Qed.

Lemma ntl_relabel_absidx_relabel f g ntl :
  ntl_relabel_absidx f (relabel_ntl g ntl) =
  relabel_ntl g (ntl_relabel_absidx f ntl).
Proof.
  unfold ntl_relabel_absidx, relabel_ntl.
  cbn.
  f_equal.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; now intros _ [[]] _.
Qed.

Lemma tg_list_to_deltas_fmap b f ioputs :
  tg_list_to_deltas b (f <$> ioputs) =
  relabel_delt (relabel_bounds f) <$> tg_list_to_deltas b ioputs.
Proof.
  unfold tg_list_to_deltas.
  rewrite fmap_imap, imap_fmap.
  reflexivity.
Qed.

Lemma tg_list_to_deltas_offset_fmap off b f ioputs :
  tg_list_to_deltas_offset off b (f <$> ioputs) =
  relabel_delt (relabel_bounds f) <$> tg_list_to_deltas_offset off b ioputs.
Proof.
  unfold tg_list_to_deltas_offset.
  rewrite fmap_imap, imap_fmap.
  reflexivity.
Qed.

Lemma tg_list_to_deltas_app out idxs idxs' :
  tg_list_to_deltas out (idxs ++ idxs') =
  tg_list_to_deltas out idxs ++
  tg_list_to_deltas_offset (length idxs) out idxs'.
Proof.
  refine (imap_app _ _ _).
Qed.

Lemma graph_namedtensorlist_semantics_stack {n m n' m'} (tg : TensorGraph n m)
  (tg' : TensorGraph n' m') :
  graph_namedtensorlist_semantics (stack_graphs tg tg') =ntl=
  ntl_times
    (ntl_relabel_absidx (bcons false)
      (graph_namedtensorlist_semantics tg))
    (ntl_relabel_absidx (bcons true)
      (graph_namedtensorlist_semantics_offset n m tg')).
Proof.
  apply ntl_aeq_of_perm.
  - cbn.
    rewrite vertices_stack_graphs.
    rewrite elements_disj_union by now apply (set_map_inj2_disjoint _).
    rewrite <- 2 (fmap_elements _).
    done.
  - cbn.
    rewrite tg_abstracts_union by now rewrite map_disjoint_fmap; apply (kmap_inj2_disjoint _).
    rewrite 2 tg_abstracts_relabel_abs, 2 (tg_abstracts_kmap _).
    (* rewrite 2 relabel_frees_tg_abstracts. *)
    done.
  - cbn -[tg_list_to_deltas].
    rewrite 2 vec_to_list_app, 4 vec_to_list_map.
    rewrite 2 tg_list_to_deltas_app.
    rewrite 2 tg_list_to_deltas_fmap, 2 tg_list_to_deltas_offset_fmap.
    rewrite 2 length_fmap, 2 length_vec_to_list.
    rewrite 2 fmap_app.
    solve_Permutation.
Qed.

Lemma contl_eq_of_ntl_eq' {n m}
  (contl : CospanNamedTensorList n m) (contl' : CospanNamedTensorList n m) :
  contl.(contl_inputs) = contl'.(contl_inputs) ->
  contl.(contl_outputs) = contl'.(contl_outputs) ->
  ntl_eq (contl_boundary contl) contl contl' ->
  contl_eq contl contl'.
Proof.
  destruct contl as [ntl ins outs], contl' as [ntl' ins' outs'].
  cbn.
  intros <- <-.
  apply contl_eq_of_ntl_eq.
Qed.


Lemma graph_contl_semantics_stack {n m n' m'} (tg : TensorGraph n m)
  (tg' : TensorGraph n' m') :
  contl_eq (graph_contl_semantics (stack_graphs tg tg'))
  (stack_contl_aux (reindex_contl (bcons false) $ graph_contl_semantics tg)
    (reindex_contl (bcons true) $ graph_contl_semantics_offset n m tg')).
Proof.
  apply contl_eq_of_ntl_eq'.
  - cbn.
    now rewrite vseq_app, Vector.map_append.
  - cbn.
    now rewrite vseq_app, Vector.map_append.
  - apply ntl_eq_of_ntl_aeq.
    apply graph_namedtensorlist_semantics_stack.
Qed.



Lemma graph_namedtensorlist_semantics_norm_verts {n m} (cohg : TensorGraph n m) : 
  graph_namedtensorlist_semantics (norm_verts cohg) = 
  graph_namedtensorlist_semantics cohg.
Proof.
  unfold graph_namedtensorlist_semantics.
  rewrite vertices_norm_verts.
  done.
Qed.

Lemma graph_contl_semantics_norm_verts {n m} (cohg : TensorGraph n m) : 
  graph_contl_semantics (norm_verts cohg) = 
  graph_contl_semantics cohg.
Proof.
  unfold graph_contl_semantics.
  now rewrite graph_namedtensorlist_semantics_norm_verts.
Qed.


Lemma graph_namedtensorlist_semantics_struct_isomorphic {n m} (tg tg' : TensorGraph n m) :
  tg ≡ᵢ tg' ->
  exists fv, Inj eq eq fv /\
  ntl_relabel_absidx fv (graph_namedtensorlist_semantics tg) =ntl=
  graph_namedtensorlist_semantics tg'.
Proof.
  intros (fv & Hfv & Heq)%graph_namedtensorlist_semantics_isomorphic.
  exists fv.
  now rewrite 2 graph_namedtensorlist_semantics_norm_verts in Heq.
Qed.

Lemma graph_namedtensorlist_semantics_vert_eq {n m} (tg tg' : TensorGraph n m) :
  tg ≡ᵥ tg' -> graph_namedtensorlist_semantics tg = graph_namedtensorlist_semantics tg'.
Proof.
  intros Heq.
  now rewrite <- graph_namedtensorlist_semantics_norm_verts, Heq, 
    graph_namedtensorlist_semantics_norm_verts.
Qed.

End TensorGraphExpr.

