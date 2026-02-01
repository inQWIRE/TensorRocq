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

Let TensorGraph := (TensorHyperGraph T).

Implicit Types tg : TensorGraph.


Definition tg_abstracts (tm : Pmap (T * list positive * list positive)) :
  list (Idx * list var * list var) :=
  (λ k_flu : _*(_*list _*list _), 
    (k_flu.1, bound <$> k_flu.2.1.2, bound <$> k_flu.2.2)) <$> 
    (map_to_list tm :> list (positive * (T * list positive * list positive))).

Definition tg_list_to_deltas (is_output : bool) 
  (idxs : list positive) : list (var * var) :=
  imap (λ idx input, (free $ bcons is_output (Pos.of_succ_nat idx), bound input))
    idxs.


Definition graph_namedtensorlist_semantics (tg : TensorGraph) : namedtensorlist := {|
  ntl_sums := elements (vertices tg);
  ntl_abstracts := tg_abstracts tg.(nodes);
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
      (map_to_list (nodes tg)).*1).

Lemma graph_namedtensorlist_semantics_to_aux tg int_labs ext_labs :
  graph_namedtensorlist_semantics tg int_labs ext_labs =
  graph_namedtensorlist_semantics_aux
    (zip int_labs (internal_edges tg)) (zip ext_labs (external_edges tg))
    (map_to_list (nodes tg)).*1.
Proof.
  unfold graph_namedtensorlist_semantics, graph_namedtensorlist_semantics_aux.
  rewrite fmap_zip_with.
  reflexivity.
Qed.


Definition graph_tabst (tg : TensorGraph) : Pmap (nat * nat) :=
  kmap Pos.of_succ_nat $
  map_imap (λ (k : nat) (_ : T), Some (length (filter (is_node_input k) (edges tg)),
    length (filter (is_node_output k) (edges tg)))) (nodes tg).


Lemma fold_internal_edges tg :
  filter (is_internal (nodes tg)) (edges tg) = internal_edges tg.
Proof. reflexivity. Qed.

Lemma fold_external_edges tg :
  filter (not_internal (nodes tg)) (edges tg) = external_edges tg.
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
Qed.

Lemma graph_namedtensorlist_semantics_WF tg int_lab ext_lab :
  NoDup int_lab -> length int_lab = num_internals tg ->
  WF_ntl (graph_namedtensorlist_semantics tg int_lab ext_lab).
Proof.
  intros Hdupi Hleni.
  split.
  - cbn.
    rewrite zip_with_zip.
    erewrite (list_fmap_ext (uncurry _ )) by now intros; rewrite uncurry_alt.
    rewrite <- list_fmap_compose.
    unfold compose; cbn.
    setoid_rewrite (list_fmap_compose fst Pos.of_succ_nat).
    rewrite fst_zip by now apply eq_reflexivity.
    apply NoDup_fmap_2; [apply _|done].
  - intros r.
    rewrite elem_of_abstracts_rel_vars, elem_of_list_to_set.
    cbn -[internal_edges external_edges].
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
    rewrite 2 fmap_zip_with.
    easy.
Qed.

Lemma relabel_rels_node_input_edges lint k fint :
  prod_map fint id <$>
    (node_input_edges k lint) =
  node_input_edges k (prod_map fint id <$> lint).
Proof.
  unfold node_input_edges.
  rewrite list_filter_fmap.
  reflexivity.
Qed.

Lemma relabel_rels_node_output_edges lext k fint :
  prod_map fint id <$>
    (node_output_edges k lext) =
  node_output_edges k (prod_map fint id <$> lext).
Proof.
  unfold node_output_edges.
  rewrite list_filter_fmap.
  reflexivity.
Qed.

Lemma relabel_rels_input_edges lint lext k fint :
  relabel_rels (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred) <$>
    (input_edges lint lext k) =
  input_edges (prod_map fint id <$> lint) lext k.
Proof.
  unfold input_edges.
  rewrite <- relabel_rels_node_input_edges.
  rewrite <- list_fmap_compose, fmap_app, <- !list_fmap_compose.
  f_equal.
  now apply list_fmap_ext; intros _ ? _; cbn; rewrite pos_to_nat_pred_of_nat.
Qed.

Lemma relabel_rels_output_edges lint lext k fint :
  relabel_rels (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred) <$>
    (output_edges lint lext k) =
  output_edges (prod_map fint id <$> lint) lext k.
Proof.
  unfold output_edges.
  rewrite <- relabel_rels_node_output_edges.
  rewrite <- list_fmap_compose, fmap_app, <- !list_fmap_compose.
  f_equal.
  now apply list_fmap_ext; intros _ ? _; cbn; rewrite pos_to_nat_pred_of_nat.
Qed.


Lemma relabel_rels_mk_node lint lext k fint :
  relabel_abs (relabel_rels (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred))
    (mk_node lint lext k) =
  mk_node (prod_map fint id <$> lint) lext k.
Proof.
  unfold mk_node; cbn.
  now rewrite relabel_rels_input_edges, relabel_rels_output_edges.
Qed.


Lemma relabel_rels_input_edges' lint lext k fr :
  relabel_rels fr <$>
    (input_edges lint lext k) =
  input_edges (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  rewrite <- relabel_rels_input_edges.
  apply list_fmap_ext; intros _ ? _; apply relabel_rels_ext; intros ?;
  unfold compose; cbn; now rewrite !pos_to_nat_pred_to_pos.
Qed.

Lemma relabel_rels_output_edges' lint lext k fr :
  relabel_rels fr <$>
    (output_edges lint lext k) =
  output_edges (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  rewrite <- relabel_rels_output_edges.
  apply list_fmap_ext; intros _ ? _; apply relabel_rels_ext; intros ?;
  unfold compose; cbn; now rewrite !pos_to_nat_pred_to_pos.
Qed.

Lemma relabel_rels_mk_node' lint lext k fr :
  relabel_abs (relabel_rels fr)
    (mk_node lint lext k) =
  mk_node (prod_map (pos_to_nat_pred ∘ fr ∘ Pos.of_succ_nat) id <$> lint) lext k.
Proof.
  unfold mk_node; cbn.
  now rewrite relabel_rels_input_edges', relabel_rels_output_edges'.
Qed.



Lemma graph_namedtensorlist_semantics_reindex_int
  (fint : nat -> nat) `{Hfint : !Inj eq eq fint} tg int_lab ext_lab :
  graph_namedtensorlist_semantics tg (fint <$> int_lab) ext_lab =ntl=
  graph_namedtensorlist_semantics tg int_lab ext_lab.
Proof.
  (* intros Hdupi Hleni. *)
  symmetry.
  hnf.
  exists (Pos.of_succ_nat ∘ fint ∘ pos_to_nat_pred).
  split; [intros ????; apply (inj _)|].
  split.
  - cbn -[internal_edges].
    rewrite fmap_zip_with, zip_with_fmap_l.
    cbn.
    apply eq_reflexivity, zip_with_ext; now intros;
    rewrite ?pos_to_nat_pred_of_nat.
  - cbn -[internal_edges external_edges].
    apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_ext; intros _ k _.
    unfold compose at 1.
    rewrite relabel_rels_mk_node.
    now rewrite fmap_zip_with, zip_with_fmap_l.
Qed.

Arguments internal_edges !_ /.
Arguments external_edges !_ /.

Lemma internal_external_decomp tg :
  edges tg ≡ₚ internal_edges tg ++ external_edges tg.
Proof.
  unfold internal_edges, external_edges.
  symmetry.
  apply filter_with_neg_Permutation.
Qed.

Lemma mk_node_abst_WT'_aux tg int_lab ext_lab k :
  (num_internals tg <= length int_lab)%nat ->
  (num_externals tg <= length ext_lab)%nat ->
  k ∈ dom (nodes tg) ->
  abst_WT' (graph_tabst tg)
    (mk_node (zip int_lab (internal_edges tg)) (zip ext_lab (external_edges tg))
      k).
Proof.
  intros Hilab Helab Hk.
  unfold abst_WT';
  cbn.
  unfold graph_tabst.
  rewrite lookup_kmap by apply _.
  rewrite map_lookup_imap.
  apply elem_of_dom in Hk as [t Ht].
  rewrite Ht.
  cbn.
  f_equal.
  rewrite internal_external_decomp, 2 filter_app.
  unfold input_edges, output_edges.
  rewrite !length_app, ! length_fmap.
  rewrite <- ! length_app.
  unfold node_input_edges, node_output_edges.
  rewrite <- 4 filter_app.
  f_equal; symmetry;
  rewrite <- (length_fmap snd), <- list_filter_fmap, fmap_app, 2 snd_zip by easy;
  reflexivity.
Qed.


Lemma mk_node_abst_WT'_imap_pair tg k :
  k ∈ dom (nodes tg) ->
  abst_WT' (graph_tabst tg)
    (mk_node (imap pair (internal_edges tg)) 
      (imap pair (external_edges tg))
      k).
Proof.
  intros Hk.
  rewrite 2 imap_to_zip_with_seq.
  apply mk_node_abst_WT'_aux; now try rewrite length_seq.
Qed.

Import SetoidList SetoidPermutation list.


Lemma input_edges_perm_eq lint lint' lext lext' k :
  lint ≡ₚ lint' -> lext ≡ₚ lext' ->
  input_edges lint lext k ≡ₚ input_edges lint' lext' k.
Proof.
  intros Hlint Hlext.
  unfold input_edges.
  do 2 f_equiv;
  unfold node_input_edges;
  now f_equiv.
Qed.

Lemma output_edges_perm_eq lint lint' lext lext' k :
  lint ≡ₚ lint' -> lext ≡ₚ lext' ->
  output_edges lint lext k ≡ₚ output_edges lint' lext' k.
Proof.
  intros Hlint Hlext.
  unfold output_edges.
  do 2 f_equiv;
  unfold node_output_edges;
  now f_equiv.
Qed.

Lemma mk_node_perm_eq lint lint' lext lext' k :
  lint ≡ₚ lint' -> lext ≡ₚ lext' ->
  mk_node lint lext k ≡abs≡ₚ mk_node lint' lext' k.
Proof.
  intros Hlint Hext.
  unfold mk_node; cbn.
  split_and!; cbn;
  [done|now apply input_edges_perm_eq|now apply output_edges_perm_eq].
Qed.

(* FIXME: Move *)
Lemma zip_Permutation_l_exists_r {A B} (l l' : list A) (k : list B) :
  l ≡ₚ l' ->
  length l = length k ->
  exists k', k ≡ₚ k' /\
  zip l k ≡ₚ zip l' k'.
Proof.
  intros Hl.
  revert k;
  induction Hl; intros k.
  - destruct k; [|done].
    now exists [].
  - destruct k as [|y k]; [done|].
    intros [= (k' & Hk & Hzip)%IHHl].
    exists (y :: k').
    split; now cbn; f_equiv.
  - destruct k as [|y' [|x' k]]; [done..|].
    intros _.
    exists (x' :: y' :: k).
    split; cbn; solve_Permutation.
  - intros Hlen.
    apply IHHl1 in Hlen as Hk'.
    destruct Hk' as (k' & Hkk' & Hzip).
    pose proof Hlen as Hlen'.
    rewrite Hl1, Hkk' in Hlen'.
    apply IHHl2 in Hlen' as (k'' & Hk'k'' & Hzip').
    exists k''.
    split; solve [eauto using Permutation_trans].
Qed.
Lemma zip_Permutation_r_exists_l {A B} (l : list A) (k k' : list B) :
  k ≡ₚ k' ->
  length l = length k ->
  exists l', l ≡ₚ l' /\
  zip l k ≡ₚ zip l' k'.
Proof.
  intros Hk Hlen%eq_sym.
  destruct (zip_Permutation_l_exists_r k k' l Hk Hlen) as (l' & Hl' & Hzip).
  exists l'.
  split; [easy|].
  rewrite <- 2 (@zip_with_flip A B).
  apply (fmap_Permutation prod_swap) in Hzip.
  rewrite 2 fmap_zip_with in Hzip.
  apply Hzip.
Qed.




(*
Lemma input_edges_edges_perm_eq int_lab ints ints'
  ext_lab exts exts' k :
  ints ≡ₚ ints' -> exts ≡ₚ exts' ->
  length int_lab = length ints ->
  length ext_lab = length exts ->
  input_edges (zip int_lab ints) (zip ext_lab exts) k ≡ₚ
  input_edges (zip int_lab ints') (zip ext_lab exts') k.
Proof.
  intros Hints Hexts Hleni Hlene.
  unfold input_edges.
  f_equiv.
  - rewrite 2 (list_fmap_compose fst).
    unfold node_input_edges.
    rewrite list_filter_fmap.
    rewrite <- Combinators.compose_assoc.
  intros Hlint Hlext Hleni Hlene.
  specialize
  unfold input_edges.
  do 2 f_equiv;
  unfold node_input_edges;
  now f_equiv.
Qed. *)

(* Lemma input_edges_lab_perm_eq int_lab int_lab' ints
  ext_lab ext_lab' exts k :
  int_lab ≡ₚ int_lab' -> ext_lab ≡ₚ ext_lab' ->
  length int_lab = length ints ->
  length ext_lab = length exts ->
  input_edges (zip int_lab ints) (zip ext_lab exts) k ≡ₚ
  input_edges (zip int_lab' ints) (zip ext_lab' exts) k.
Proof.
  intros Hlint Hlext Hleni Hlene.
  specialize
  unfold input_edges.
  do 2 f_equiv;
  unfold node_input_edges;
  now f_equiv.
Qed. *)


Lemma graph_namedtensorlist_semantics_aux_perm_eq' lint lint' lext lext' ks ks' :
  NoDup lint.*1 -> lint ≡ₚ lint' ->
  lext ≡ₚ lext' -> ks ≡ₚ ks' ->
  graph_namedtensorlist_semantics_aux lint lext ks ≡ntl'≡ₚ
  graph_namedtensorlist_semantics_aux lint' lext' ks'.
Proof.
  intros Hdup Hlint Hlext Hks.
  split; cbn.
  - apply list_to_map_proper; [|now f_equiv].
    rewrite <- list_fmap_compose.
    unfold compose; cbn.
    change (_ <$> _) with (Pos.of_succ_nat ∘ fst <$> lint).
    rewrite list_fmap_compose.
    now apply (NoDup_fmap_2 _ _).
  - etransitivity; [|apply (Permutation_PermutationA _); now rewrite <- Hks].
    apply eqlistA_PermutationA.
    apply eqlistA_altdef.
    rewrite Forall2_fmap.
    apply Forall_Forall2_diag, (set_Forall_list_to_set (C:=gset nat)).
    intros k _.
    now apply mk_node_perm_eq.
Qed.

(* FIXME: Move *)
Lemma ntl_aeq_WF ntl ntl' :
  ntl =ntl= ntl' -> WF_ntl ntl -> WF_ntl ntl'.
Proof.
  intros (fr & Hfr & Hfsums & Hfabs).
  cbn.
  intros [Hdup Habs].
  split.
  - rewrite <- Hfsums.
    rewrite fsts_prod_map.
    apply NoDup_fmap_2_strong, Hdup.
    intros ? ? Hx Hy; apply Hfr; set_solver + Hx Hy.
  - rewrite <- Hfsums, <- Hfabs.
    rewrite abstracts_rel_vars_relabel_rels, fsts_prod_map,
      <- (set_map_list_to_set_L (SA:=Pset)).
    f_equiv; apply Habs.
Qed.
Lemma ntl_aeq_of_WF ntl ntl' : WF_ntl ntl ->
  (exists fr,
    set_Forall2 (λ i j, fr i = fr j -> i = j) (list_to_set ntl.(ntl_sums).*1:>Pset ) /\
    prod_map fr id <$> ntl.(ntl_sums) ≡ₚ ntl'.(ntl_sums) /\
    relabel_abs (relabel_rels fr) <$> ntl.(ntl_abstracts) ≡ₚ ntl'.(ntl_abstracts)
    ) ->
  ntl =ntl= ntl'.
Proof.
  intros HWF (fr & Hfr & Hsums & Habs).
  exists fr.
  split; [|easy].
  intros x y Hx Hy.
  apply Hfr; specialize (HWF.2); [set_solver +Hx|set_solver +Hy].
Qed.

(* FIXME: Move *)
Section list_index.
Context `{EqDecision A}.
Implicit Type l : list A.

Definition list_index (x : A) l :=
  fst <$> list_find (eq x) l.

Lemma list_index_is_Some x l :
  is_Some (list_index x l) <-> x ∈ l.
Proof.
  unfold list_index.
  rewrite fmap_is_Some.
  split; [|intros Hx; apply (list_find_elem_of _ _ x Hx eq_refl)].
  now intros [[] (?%elem_of_list_lookup_2 & <- & _)%list_find_Some].
Qed.

Lemma list_index_Some x l i :
  list_index x l = Some i <->
  l !! i = Some x /\ forall j y, l !! j = Some y -> j < i -> x <> y.
Proof.
  unfold list_index.
  rewrite fmap_Some, exists_pair.
  setoid_rewrite list_find_Some.
  naive_solver.
Qed.

Lemma list_index_Some_NoDup x l i :
  NoDup l ->
  list_index x l = Some i <-> l !! i = Some x.
Proof.
  intros Hdup.
  rewrite list_index_Some.
  rewrite <- (and_True (l !! i = Some x)) at 2.
  apply and_iff_from_l; [reflexivity|intros Hli _].
  apply iff_True_1.
  intros j y Hlj Hji ->.
  enough (i = j) by lia.
  revert Hli Hlj.
  now apply NoDup_lookup.
Qed.

Lemma list_index_inj x y l i :
  list_index x l = Some i -> list_index y l = Some i -> x = y.
Proof.
  rewrite 2 list_index_Some.
  intros [] [].
  congruence.
Qed.

Lemma list_index_lt x l i :
  list_index x l = Some i -> i < length l.
Proof.
  now intros [?%lookup_lt_Some _]%list_index_Some.
Qed.

Lemma list_index_ppermute_NoDup x l f : posperm (lengthP l) f ->
  NoDup l ->
  list_index x (ppermute f l) =
  (pos_to_nat_pred ∘ posperm_inv (lengthP l) f ∘ Pos.of_succ_nat) <$> list_index x l.
Proof.
  intros Hf Hl.
  apply option_eq; intros i.
  rewrite list_index_Some_NoDup by now rewrite ppermute_permutation.
  pose proof (lengthN_correct l).
  split.
  - intros Hlook.
    apply lookup_lt_Some in Hlook as Hi.
    rewrite length_ppermute in Hi.
    rewrite lookup_ppermute_alt_bdd in Hlook by now easy + apply posperm_bounded.
    replace (list_index x l) with (Some (f (Pos.of_succ_nat i) :> nat)) by
      now symmetry; apply list_index_Some_NoDup.
    cbn.
    rewrite pos_to_nat_pred_to_pos.
    rewrite posperm_inv_linv by now easy + lia.
    f_equal; lia.
  - destruct (list_index x l) as [fi|] eqn:Hfi; [|easy].
    apply list_index_Some in Hfi as [Hfi _].
    apply lookup_lt_Some in Hfi as Hfilt.
    cbn.
    intros [= <-].
    rewrite lookup_ppermute_alt_bdd by first [
      now apply posperm_bounded|
      specialize (posperm_inv_bounded (lengthP l) f (Pos.of_succ_nat fi));
      lia
    ].
    rewrite pos_to_nat_pred_to_pos.
    rewrite posperm_inv_rinv by now easy || lia.
    now rewrite pos_to_nat_pred_of_nat.
Qed.

Lemma list_lookup_omap_all_is_Some `(f : A -> option B) (l : list A) (i : nat)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l !! i = l !! i ≫= f.
Proof.
  rewrite <- Forall_forall in Hf.
  revert i;
  induction Hf; [now intros []|intros i].
  cbn.
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  destruct i; [cbn; now rewrite Hfx|].
  cbn.
  apply IHHf.
Qed.

Lemma length_omap_all_is_Some `(f : A -> option B) (l : list A)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  length (omap f l) = length l.
Proof.
  rewrite <- Forall_forall in Hf.
  induction Hf; [done|cbn].
  destruct (f x) as [fx|] eqn:Hfx; [|now rewrite is_Some_alt in *].
  cbn.
  f_equal; apply IHHf.
Qed.

Lemma omap_all_is_Some_default `(f : A -> option B) (l : list A) (g : A -> B)
  (Hf : forall a, a ∈ l -> is_Some (f a)) :
  omap f l = (λ i, default (g i) (f i)) <$> l.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl).
  - now rewrite length_fmap; apply length_omap_all_is_Some.
  - intros i x y.
    rewrite length_fmap.
    intros Hi.
    rewrite list_lookup_omap_all_is_Some by easy.
    rewrite list_lookup_fmap.
    destruct (l !! i) as [li|]; [|easy].
    cbn.
    destruct (f li); [|easy].
    cbn; congruence.
Qed.

Lemma ppermute_alt_list_index_aux_Some f l : posbdd (lengthP l) f -> NoDup l ->
  forall x, x ∈ l ->
    is_Some (i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat)).
Proof.
  intros Hf Hl x Hx.
  pose proof (lengthN_correct l).
  apply elem_of_list_lookup in Hx as Hi.
  destruct Hi as [i Hi].
  apply list_index_Some_NoDup in Hi as Hi'; [|easy].
  rewrite Hi'.
  cbn.
  apply lookup_lt_Some in Hi as Hilt.
  apply lookup_lt_is_Some.
  specialize (Hf (Pos.of_succ_nat i)).
  lia.
Qed.

Lemma ppermute_alt_list_index f l : posbdd (lengthP l) f -> NoDup l ->
  ppermute f l = omap (λ x, i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat)) l.
Proof.
  intros Hf Hl.
  pose proof (lengthN_correct l).
  specialize (ppermute_alt_list_index_aux_Some f l Hf Hl) as Hsome.
  apply length_omap_all_is_Some in Hsome as Hlen.
  apply (λ H, list_eq_same_length _ _ _ H eq_refl);
  [now rewrite length_ppermute, Hlen|].
  intros i x y.
  rewrite length_ppermute.
  intros Hi.
  rewrite lookup_ppermute_alt_bdd by easy.
  rewrite list_lookup_omap_all_is_Some by easy.
  apply lookup_lt_is_Some in Hi as Hli.
  destruct Hli as [li Hli].
  rewrite Hli.
  cbn.
  apply list_index_Some_NoDup in Hli as Hli'; [|easy].
  rewrite Hli'.
  cbn.
  congruence.
Qed.

Lemma ppermute_alt_list_index_total
  f l : posbdd (lengthP l) f -> NoDup l ->
  ppermute f l = (λ x, default x
    (i ← list_index x l; l !! (f (Pos.of_succ_nat i):>nat))) <$> l.
Proof.
  intros Hf Hl.
  rewrite ppermute_alt_list_index by easy.
  now apply omap_all_is_Some_default, ppermute_alt_list_index_aux_Some.
Qed.

End list_index.

Lemma graph_namedtensorlist_semantics_ppermute tg int_lab fi ext_lab :
  NoDup int_lab -> length int_lab = num_internals tg ->
  posperm (lengthP int_lab) fi ->
  graph_namedtensorlist_semantics tg int_lab ext_lab =ntl=
  graph_namedtensorlist_semantics tg (ppermute fi int_lab) ext_lab.
Proof.
  intros Hdup Hlen Hfi.
  pose proof (lengthN_correct int_lab).
  rewrite 2 graph_namedtensorlist_semantics_to_aux.
  apply ntl_aeq_of_WF; [now rewrite <- graph_namedtensorlist_semantics_to_aux;
    apply graph_namedtensorlist_semantics_WF|].


  cbn.
  rewrite (list_fmap_compose fst), fst_zip by now apply eq_reflexivity.
  rewrite <- list_fmap_compose.
  change (fst ∘ _) with (Pos.of_succ_nat).
  rewrite (list_fmap_compose fst), fst_zip by
    now rewrite length_ppermute; apply eq_reflexivity.
  (* rewrite <- list_fmap_compose. *)
  change (fst ∘ _) with (Pos.of_succ_nat).
  pose proof (lengthN_correct int_lab).
  exists (Pos.of_succ_nat
      ∘ (λ x : Ty,
           default x
             (list_index x int_lab
              ≫= λ i : Ty, int_lab !! (fi (Pos.of_succ_nat i):>nat)))
      ∘ pos_to_nat_pred).
  split_and!.
  - intros _ _ (x & -> & Hx)%elem_of_list_to_set%elem_of_list_fmap
      (y & -> & Hy)%elem_of_list_to_set%elem_of_list_fmap.
    cbn.
    rewrite 2 pos_to_nat_pred_of_nat.
    apply elem_of_list_lookup in Hx as Hi.
    apply elem_of_list_lookup in Hy as Hj.
    destruct Hi as [i Hi], Hj as [j Hj].
    apply list_index_Some_NoDup in Hi as Hi'; [|easy].
    apply list_index_Some_NoDup in Hj as Hj'; [|easy].
    rewrite Hi', Hj'.
    cbn.
    intros Heq%(inj Pos.of_succ_nat).
    pose proof (posperm_bounded _ _ Hfi) as Hfibdd.
    apply lookup_lt_Some in Hi as Hilt.
    apply lookup_lt_Some in Hj as Hjlt.

    assert (is_Some (int_lab !! (fi (Pos.of_succ_nat i) :> nat))) as Hfi_i. 1:{
      apply lookup_lt_is_Some.
      specialize (Hfibdd (Pos.of_succ_nat i)).
      lia.
    }
    assert (is_Some (int_lab !! (fi (Pos.of_succ_nat j) :> nat))) as Hfi_j. 1:{
      apply lookup_lt_is_Some.
      specialize (Hfibdd (Pos.of_succ_nat j)).
      lia.
    }
    destruct Hfi_i as [fii Hfii], Hfi_j as [fij Hfij].
    rewrite Hfii, Hfij in Heq.
    cbn in Heq.
    subst fij.
    specialize (NoDup_lookup _ _ _ _ Hdup Hfii Hfij)
      as Heq%(inj pos_to_nat_pred).
    apply (posperm_inj _ _ Hfi) in Heq as Heq%(inj _); [|lia..].
    subst j.
    congruence.
  - rewrite ppermute_alt_list_index_total by now easy + apply posperm_bounded.
    apply eq_reflexivity.
    rewrite <- 2 list_fmap_compose.
    apply list_fmap_ext; intros _ x Hx%elem_of_list_lookup_2.
    cbn.
    now rewrite pos_to_nat_pred_of_nat.
  -
    apply eq_reflexivity.
    rewrite <- list_fmap_compose.
    apply list_fmap_ext; intros _ k Hk%elem_of_list_lookup_2.
    rewrite <- (elem_of_list_to_set (C:=gset nat)), <- dom_alt in Hk.
    cbn [compose].
    rewrite ppermute_alt_list_index_total by now easy + apply posperm_bounded.
    rewrite zip_fmap_l, <- relabel_rels_mk_node.
    reflexivity.
Qed.

Lemma NoDup_fmap_ind `(f : A -> B) (P : list A -> Prop)
  (Pnil : P []) (Pcons : forall a l, f a ∉ f <$> l -> NoDup (f <$> l) ->
    P l -> P (a :: l)) : forall l, NoDup (f <$> l) -> P l.
Proof.
  intros l.
  induction l; [easy|].
  cbn; rewrite NoDup_cons.
  intros []; eauto.
Qed.

Lemma input_edges_ext_label_irrel lint lext lext' k :
  lext.*2 = lext'.*2 ->
  input_edges lint lext k = input_edges lint lext' k.
Proof.
  intros Hlext.
  unfold input_edges; f_equal.
  unfold node_input_edges.
  rewrite 2 (list_fmap_compose snd), <- 2 list_filter_fmap.
  now rewrite Hlext.
Qed.

Lemma output_edges_ext_label_irrel lint lext lext' k :
  lext.*2 = lext'.*2 ->
  output_edges lint lext k = output_edges lint lext' k.
Proof.
  intros Hlext.
  unfold output_edges; f_equal.
  unfold node_output_edges.
  rewrite 2 (list_fmap_compose snd (_ ∘ snd)), <- 2 list_filter_fmap.
  now rewrite Hlext.
Qed.

Lemma mk_node_ext_label_irrel lint lext lext' k :
  lext.*2 = lext'.*2 ->
  mk_node lint lext k = mk_node lint lext' k.
Proof.
  intros Hext.
  unfold mk_node.
  f_equal; [f_equal|];
  [now apply input_edges_ext_label_irrel|
   now apply output_edges_ext_label_irrel].
Qed.

Lemma zip_with_irrel_l {A B C} (f : B -> C) (l l' : list A) (k : list B) :
  length l = length l' ->
  zip_with (λ _ b, f b) l k = zip_with (λ _ b, f b) l' k.
Proof.
  intros Hall%Forall2_same_length.
  revert k;
  induction Hall; intros []; cbn; congruence.
Qed.

Lemma zip_with_irrel_r {A B C} (f : A -> C) (l : list A) (k k' : list B) :
  length k = length k' ->
  zip_with (λ a _, f a) l k = zip_with (λ a _, f a) l k'.
Proof.
  intros Hall%Forall2_same_length.
  revert l;
  induction Hall; intros []; cbn; congruence.
Qed.

Lemma graph_namedtensorlist_semantics_ext_lab_irrel tg int_lab ext_lab ext_lab' :
  length ext_lab = length ext_lab' ->
  graph_namedtensorlist_semantics tg int_lab ext_lab =
  graph_namedtensorlist_semantics tg int_lab ext_lab'.
Proof.
  intros Hlen.
  unfold graph_namedtensorlist_semantics.
  f_equal.
  apply list_fmap_ext; intros _ x _.
  apply mk_node_ext_label_irrel.
  rewrite 2 fmap_zip_with; cbn.
  now apply zip_with_irrel_l.
Qed.



Lemma graph_namedtensorlist_semantics_perm_eq tg int_lab int_lab'
  ext_lab ext_lab' :
  NoDup int_lab -> length int_lab = num_internals tg ->
  int_lab ≡ₚ int_lab' ->
  length ext_lab = length ext_lab' ->
  graph_namedtensorlist_semantics tg int_lab ext_lab =ntl=
  graph_namedtensorlist_semantics tg int_lab' ext_lab'.
Proof.
  intros Hdup Hlen (f & Hf & <- & Hlook)%perm_exists_posperm Hext.
  etransitivity; [apply graph_namedtensorlist_semantics_ppermute; eauto|].
  apply eq_reflexivity.
  now apply graph_namedtensorlist_semantics_ext_lab_irrel.
Qed.


Lemma graph_namedtensorlist_semantics_seq_correct' tg :
  graph_tensorlist_semantics tg =
  ntl2tl (graph_namedtensorlist_semantics tg (seq 0 (num_internals tg))
	  (seq 0 (num_externals tg))).
Proof.
  rewrite graph_namedtensorlist_semantics_seq_correct.
  now rewrite tl2ntl2tl.
Qed.

Lemma internal_edges_perm ns es es' :
  es ≡ₚ es' ->
  @internal_edges T (mk_tg ns es) ≡ₚ internal_edges (mk_tg ns es').
Proof.
  intros Hes.
  unfold internal_edges; cbn.
  now f_equiv.
Qed.

Lemma external_edges_perm ns es es' :
  es ≡ₚ es' ->
  @external_edges T (mk_tg ns es) ≡ₚ external_edges (mk_tg ns es').
Proof.
  intros Hes.
  unfold external_edges; cbn.
  now f_equiv.
Qed.


Lemma graph_tensorlist_semantics_perm_eq_pairs_elab ns es es' :
  es ≡ₚ es' ->
  exists idxs idxs',
  idxs ≡ₚ seq 0 (num_internals (mk_tg ns es)) /\
  idxs' ≡ₚ seq 0 (num_externals (mk_tg ns es)) /\
  tl2ntl (graph_tensorlist_semantics (mk_tg ns es)) ≡ntl'≡ₚ
  graph_namedtensorlist_semantics_aux
    (zip idxs (internal_edges (mk_tg ns es')))
    (zip idxs' (external_edges (mk_tg ns es')))
    (map_to_list ns).*1 /\
  graph_namedtensorlist_semantics_aux
    (zip idxs (internal_edges (mk_tg ns es')))
    (zip idxs' (external_edges (mk_tg ns es')))
    (map_to_list ns).*1
    =ntl= tl2ntl (graph_tensorlist_semantics (mk_tg ns es')).
Proof.
  intros Hes.
  apply (internal_edges_perm ns) in Hes as Hies.
  apply (external_edges_perm ns) in Hes as Hees.

  apply perm_exists_perm_seq in Hies as Hidxs.
  apply perm_exists_perm_seq in Hees as Hidxs'.

  destruct Hidxs as (idxs & Hidxs & Himap).
  destruct Hidxs' as (idxs' & Hidxs' & Himap').
  exists idxs, idxs'.
  split; [easy|].
  split; [easy|].
  split.
  - rewrite <- graph_namedtensorlist_semantics_seq_correct.
    rewrite graph_namedtensorlist_semantics_to_aux.
    cbn [nodes].
    eapply graph_namedtensorlist_semantics_aux_perm_eq';
    [rewrite fst_zip by (now rewrite length_seq);
     apply NoDup_seq|..|reflexivity].
    + etransitivity; [|apply Himap].
      now rewrite imap_to_zip_with_seq.
    + etransitivity; [|apply Himap'].
      now rewrite imap_to_zip_with_seq.
  - rewrite <- graph_namedtensorlist_semantics_to_aux.
    rewrite <- graph_namedtensorlist_semantics_seq_correct.
    apply graph_namedtensorlist_semantics_perm_eq.
    + rewrite Hidxs; apply NoDup_seq.
    + rewrite Hidxs.
      now rewrite length_seq, Hies.
    + rewrite Hidxs.
      f_equiv.
      now rewrite Hies.
    + rewrite Hidxs'.
      now rewrite 2 length_seq, Hees.
Qed.


Lemma graph_tensorlist_semantics_perm_eq_pairs ns es es' :
  es ≡ₚ es' ->
  exists mid,
  tl2ntl (graph_tensorlist_semantics (mk_tg ns es)) ≡ntl'≡ₚ mid /\
  mid =ntl= tl2ntl (graph_tensorlist_semantics (mk_tg ns es')).
Proof.
  intros Hes.
  apply (graph_tensorlist_semantics_perm_eq_pairs_elab ns) in Hes.
  naive_solver.
Qed.

 *)



End TensorGraphExpr.