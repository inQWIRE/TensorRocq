Require Export TensorGraph Aux_pos.

Require Export TESyntax.

(* FIXME: Move: *)
Require Combinators.

(* FIXME: Move: *)
Lemma pseq_to_seq_inv (start len : nat) :
  Pos.of_succ_nat <$> seq start len =
  pseq (Pos.of_succ_nat start) (N.of_nat len).
Proof.
  rewrite pseq_to_seq.
  do 2 f_equal; lia.
Qed.

#[local] Coercion pos_to_nat_pred : positive >-> nat.

(* Semantics of TensorGraphs into tensor expressions *)


Section TensorGraphExpr.

Context {T : Type}.

Let TensorGraph := (CospanHyperGraph T).

(* Implicit Types tg : TensorGraph. *)


Definition tg_abstracts (tm : Pmap (T * list positive * list positive)) :
  list (Idx * list var * list var) :=
  (λ k_flu : _*(_*list _*list _),
    (k_flu.1, bound <$> k_flu.2.1.2, bound <$> k_flu.2.2)) <$>
    (map_to_list tm :> list (positive * (T * list positive * list positive))).

Definition tg_list_to_deltas (is_output : bool)
  (idxs : list positive) : list (var * var) :=
  imap (λ idx input, (free $ bcons is_output (Pos.of_succ_nat idx), bound input))
    idxs.


Definition graph_namedtensorlist_semantics {n m} (tg : TensorGraph n m) : namedtensorlist := {|
  ntl_sums := elements (vertices tg);
  ntl_abstracts := tg_abstracts tg.(hedges);
  ntl_deltas := tg_list_to_deltas false tg.(inputs)
    ++ tg_list_to_deltas true tg.(outputs);
|}.


(*
Definition graph_tensorlist_semantics (tg : TensorGraph) : tensorlist :=
  mk_tl (const 0%nat <$> internal_edges tg)
    (mk_node (i_internal_edges tg) (i_external_edges tg) <$>
      (map_to_list (fst tg)).*1).

Definition num_internals (tg : TensorGraph) : nat :=
  length (internal_edges tg).

Definition num_externals (tg : TensorGraph) : nat :=
  length (external_edges tg).

#[global] Arguments num_internals !_ /.
#[global] Arguments num_externals !_ /.

Definition graph_namedtensorlist_semantics_aux
  (lint lext : list labedge) (ks : list nat) :=
  mk_ntl ((., O) ∘ Pos.of_succ_nat ∘ fst <$>
    lint)
    (mk_node lint
      lext <$>
      ks).

Definition graph_namedtensorlist_semantics (tg : TensorGraph)
  (int_labs ext_labs : list nat) : namedtensorlist :=
  mk_ntl (zip_with (λ i _, (Pos.of_succ_nat i, O)) int_labs $ internal_edges tg)
    (mk_node (zip int_labs (internal_edges tg))
      (zip ext_labs (external_edges tg)) <$>
      (map_to_list (hedges tg)).*1).

Lemma graph_namedtensorlist_semantics_to_aux tg int_labs ext_labs :
  graph_namedtensorlist_semantics tg int_labs ext_labs =
  graph_namedtensorlist_semantics_aux
    (zip int_labs (internal_edges tg)) (zip ext_labs (external_edges tg))
    (map_to_list (hedges tg)).*1.
Proof.
  unfold graph_namedtensorlist_semantics, graph_namedtensorlist_semantics_aux.
  rewrite fmap_zip_with.
  reflexivity.
Qed.


Definition graph_tabst (tg : TensorGraph) : Pmap (nat * nat) :=
  kmap Pos.of_succ_nat $
  map_imap (λ (k : nat) (_ : T), Some (length (filter (is_node_input k) (edges tg)),
    length (filter (is_node_output k) (edges tg)))) (hedges tg).


Lemma fold_internal_edges tg :
  filter (is_internal (hedges tg)) (edges tg) = internal_edges tg.
Proof. reflexivity. Qed.

Lemma fold_external_edges tg :
  filter (not_internal (hedges tg)) (edges tg) = external_edges tg.
Proof. reflexivity. Qed.

Lemma fold_num_internals tg :
  length (internal_edges tg) = num_internals tg.
Proof. reflexivity. Qed.

Lemma fold_num_externals tg :
  length (external_edges tg) = num_externals tg.
Proof. reflexivity. Qed.

Lemma graph_namedtensorlist_semantics_seq_correct tg :
  graph_namedtensorlist_semantics tg (seq 0 (num_internals tg))
    (seq 0 (num_externals tg)) = tl2ntl (graph_tensorlist_semantics tg).
Proof.
  cbn -[reverse].
  rewrite fmap_const, reverse_replicate.
  rewrite fold_internal_edges; fold (num_internals tg) (num_externals tg).
  rewrite fold_external_edges.
  unfold graph_namedtensorlist_semantics.
  f_equal.
  - rewrite imap_to_zip_with_seq, length_replicate.
    unfold num_internals.
    rewrite <- fmap_const, zip_with_fmap_r.
    reflexivity.
  - now rewrite 2 imap_to_zip_with_seq.
Qed.

Lemma list_fmap_subseteq {A B} (f : A -> B) (l1 l2 : list A) :
  l1 ⊆ l2 -> f <$> l1 ⊆ f <$> l2.
Proof.
  intros Hl b (a & -> & ?%Hl)%elem_of_list_fmap.
  now apply elem_of_list_fmap_1.
Qed.

Lemma list_subseteq_app {A} {l1 l1' l2 l2' : list A} :
  l1 ⊆ l1' -> l2 ⊆ l2' -> l1 ++ l2 ⊆ l1' ++ l2'.
Proof.
  intros;
  apply list_subseteq_app_iff_l, conj;
    [apply list_subseteq_app_l|apply list_subseteq_app_r];
  done.
Qed.

Lemma input_edges_subseteq_labels lint lext k :
  input_edges lint lext k ⊆
    (rel ∘ Pos.of_succ_nat ∘ fst <$> lint) ++
    (loc ∘ bcons false ∘ Pos.of_succ_nat ∘ fst ∘ snd <$> lext).
Proof.
  unfold input_edges.
  apply list_subseteq_app;
  apply list_fmap_subseteq, list_filter_subseteq.
Qed.

Lemma output_edges_subseteq_labels lint lext k :
  output_edges lint lext k ⊆
    (rel ∘ Pos.of_succ_nat ∘ fst <$> lint) ++
    (loc ∘ bcons true ∘ Pos.of_succ_nat ∘ snd ∘ snd <$> lext).
Proof.
  unfold output_edges.
  apply list_subseteq_app;
  apply list_fmap_subseteq, list_filter_subseteq.
Qed.


Lemma graph_tensorlist_semantics_WF tg :
  WF_tl (graph_tensorlist_semantics tg).
Proof.
  intros i.
  rewrite elem_of_abstracts_rel_vars.
  cbn -[internal_edges external_edges].
  rewrite length_fmap, fold_num_internals.
  intros (f & low & up & (k & [= -> -> ->] & Hk)%elem_of_list_fmap & Hi).
  apply (elem_of_list_to_set (C:=gset nat)) in Hk.
  rewrite <- dom_alt in Hk.
  apply (list_subseteq_app (input_edges_subseteq_labels _ _ _)
    (output_edges_subseteq_labels _ _ _)) in Hi.
  rewrite Permutation_swap_app_app, elem_of_app in Hi.
  destruct Hi as [Hi|HF]. 2:{
    rewrite !Combinators.compose_assoc in HF.
    rewrite 2 (list_fmap_compose _ loc), <- fmap_app in HF.
    apply elem_of_list_fmap in HF as (? & [=] & _).
  }
  revert Hi.
  rewrite elem_of_app, (or_idemp _).
  rewrite Combinators.compose_assoc, list_fmap_compose.
  rewrite elem_of_list_fmap_inj by apply _.
  unfold i_internal_edges, enumerate.
  rewrite fmap_imap.
  unfold compose; cbn -[internal_edges].
  rewrite imap_seq_0, pseq_to_seq_inv.
  intros ?%elem_of_pseq_1.
  rewrite fold_num_internals in Hi.
  lia.
Qed.

Lemma uncurry_alt {A B C} (f : A -> B -> C) p :
  uncurry f p = f p.1 p.2.
Proof.
  now destruct p.
Qed.*)

Lemma list_omap_fmap {A B C} (f : A -> B) (g : B -> option C) (l : list A) :
  omap g (f <$> l) = omap (g ∘ f) l.
Proof.
  induction l; [done|cbn]; case_match; f_equal; easy.
Qed.

Lemma abstracts_bound_vars_graph {n m} (tg : TensorGraph n m) :
  abstracts_bound_vars (graph_namedtensorlist_semantics tg).(ntl_abstracts) =
  list_to_set ('(_, low, up) ← (map_to_list tg.(hedges)).*2; low ++ up).
Proof.
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
  unfold tg_abstracts.
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
    apply list_to_set_subseteq.
    apply eq_reflexivity, list_bind_ext; [|done].
    now intros [? [[]]].
  - rewrite deltas_bound_vars_graph.
    cbn.
    unfold vertices.
    rewrite list_to_set_elements.
    apply union_subseteq_r.
Qed.

Lemma relabel_bounds_node_input_edges lint k fint :
  prod_map fint id <$>
    (node_input_edges k lint) =
  node_input_edges k (prod_map fint id <$> lint).
Proof.
  unfold node_input_edges.
  rewrite list_filter_fmap.
  reflexivity.
Qed.

Lemma relabel_bounds_node_output_edges lext k fint :
  prod_map fint id <$>
    (node_output_edges k lext) =
  node_output_edges k (prod_map fint id <$> lext).
Proof.
  unfold node_output_edges.
  rewrite list_filter_fmap.
  reflexivity.
Qed.
(*
Lemma relabel_bounds_input_edges lint lext k fint :
  relabel_bounds (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred) <$>
    (input_edges lint lext k) =
  input_edges (prod_map fint id <$> lint) lext k.
Proof.
  unfold input_edges.
  rewrite <- relabel_bounds_node_input_edges.
  rewrite <- list_fmap_compose, fmap_app, <- !list_fmap_compose.
  f_equal.
  now apply list_fmap_ext; intros _ ? _; cbn; rewrite pos_to_nat_pred_of_nat.
Qed.

Lemma relabel_bounds_output_edges lint lext k fint :
  relabel_bounds (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred) <$>
    (output_edges lint lext k) =
  output_edges (prod_map fint id <$> lint) lext k.
Proof.
  unfold output_edges.
  rewrite <- relabel_bounds_node_output_edges.
  rewrite <- list_fmap_compose, fmap_app, <- !list_fmap_compose.
  f_equal.
  now apply list_fmap_ext; intros _ ? _; cbn; rewrite pos_to_nat_pred_of_nat.
Qed. *)

(*
Lemma relabel_bounds_mk_node lint lext k fint :
  relabel_abs (relabel_bounds (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred))
    (mk_node lint lext k) =
  mk_node (prod_map fint id <$> lint) lext k.
Proof.
  unfold mk_node; cbn.
  now rewrite relabel_bounds_input_edges, relabel_bounds_output_edges.
Qed. *)


(* Lemma relabel_bounds_input_edges' lint lext k fr :
  relabel_bounds fr <$>
    (input_edges lint lext k) =
  input_edges (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  rewrite <- relabel_bounds_input_edges.
  apply list_fmap_ext; intros _ ? _; apply relabel_bounds_ext; intros ?;
  unfold compose; cbn; now rewrite !pos_to_nat_pred_to_pos.
Qed.

Lemma relabel_bounds_output_edges' lint lext k fr :
  relabel_bounds fr <$>
    (output_edges lint lext k) =
  output_edges (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  rewrite <- relabel_bounds_output_edges.
  apply list_fmap_ext; intros _ ? _; apply relabel_bounds_ext; intros ?;
  unfold compose; cbn; now rewrite !pos_to_nat_pred_to_pos.
Qed.

Lemma relabel_bounds_mk_node' lint lext k fr :
  relabel_abs (relabel_bounds fr)
    (mk_node lint lext k) =
  mk_node (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  unfold mk_node; cbn.
  now rewrite relabel_bounds_input_edges', relabel_bounds_output_edges'.
Qed. *)


Lemma fmap_elements `{FinSet A SA, FinSet B SB} (f : A -> B) `{!Inj eq eq f} (X : SA) :
  f <$> elements X ≡ₚ
  elements (set_map f X :> SB).
Proof.
  apply NoDup_Permutation;
  [apply (NoDup_fmap_2 _ _), NoDup_elements|apply NoDup_elements|].
  set_solver.
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

(* FIXME: Move *)

Lemma NoDup_fmap_ind `(f : A -> B) (P : list A -> Prop)
  (Pnil : P []) (Pcons : forall a l, f a ∉ f <$> l -> NoDup (f <$> l) ->
    P l -> P (a :: l)) : forall l, NoDup (f <$> l) -> P l.
Proof.
  intros l.
  induction l; [easy|].
  cbn; rewrite NoDup_cons.
  intros []; eauto.
Qed.




End TensorGraphExpr.