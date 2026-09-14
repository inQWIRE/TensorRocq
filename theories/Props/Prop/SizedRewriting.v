(* A file containing rewriting theory, especially for rewriting in
  autonomous and frobenius categories *)

From TensorRocq Require Import tc BW.

From TensorRocq Require Import
  Isomorphism.IsoAux SizedGraph.Matching SizedGraph.Testing
  SizedGraph.BWSized SizedGraph.Hom
  ProLike Props PropsGraphs ProQuote Rewriting
  SizedProps
  SizedProLike
  SizedPropsGraphs.
(*
From TensorRocq Require Import Isomorphism.IsoAux SizedGraph.Testing
  (* CospanHyperGraph.Definitions *)
  CospanHyperGraph.Ops SizedGraph.Definitions
  SizedGraph.Testing SizedGraph.ToUnsized SizedPropsGraphs SizedProps. *)
Require Ltac2.Ltac2.

Import SizedGraph.Definitions. (* FIXME: Remove. Contains definition N := I : True,
  preventing forgotten arguments from implicitly restricting a type N to mean
  only binary naturals. *)

From TensorRocq Require SizedPropGraphTerm.

Local Existing Instance Countable_Equiv.

Local Open Scope positive_scope.


(* FIXME: Move *)
Lemma InA_alt {A} (eqA : A -> A -> Prop) (x : A) l :
  InA eqA x l <-> exists y, eqA x y /\ y ∈ l.
Proof.
  rewrite InA_alt.
  setoid_rewrite elem_of_list_In.
  done.
Qed.

Local Existing Instance Countable_Equiv.


(* FIXME: Move *)
Fixpoint MPRO_tensors {N Struct T} {n m}
  (mp : @MPRO N Struct T n m) : list (btree N * btree N * T) :=
  match mp with
  | Mid _ | Mstruct _ _ _ => []
  | Mcompose ml mr | Mstack ml mr => MPRO_tensors ml ++ MPRO_tensors mr
  | Mgen n m t => [(n, m, t)]
  end.

Definition MPRO_tensors_lists {N Struct T} {n m}
  (mp : @MPRO N Struct T n m) : list (list N * list N * T) :=
  prod_map (prod_map btree_elems btree_elems) id <$> MPRO_tensors mp.

Definition MPRO_tensors_encoded {N Struct T} `{Countable N, Countable T}
  {n m} (mp : @MPRO N Struct T n m) : list positive :=
  encode ∘ prod_map (prod_map btree_elems btree_elems) id <$> MPRO_tensors mp.

Fixpoint MPRO_tensors_set {N Struct T} `{Countable N, Countable T}
  {n m} (mp : @MPRO N Struct T n m) : Pset :=
  match mp with
  | Mid _ | Mstruct _ _ _ => ∅
  | Mcompose ml mr | Mstack ml mr => MPRO_tensors_set ml ∪ MPRO_tensors_set mr
  | Mgen n m t => {[encode (btree_elems n, btree_elems m, t)]}
  end.

Lemma list_to_set_MPRO_tensors_encoded {N Struct T} `{Countable N, Countable T}
  {n m} (mp : @MPRO N Struct T n m) :
  list_to_set (MPRO_tensors_encoded mp) = MPRO_tensors_set mp.
Proof.
  induction mp; [done
    | cbn; rewrite fmap_app, list_to_set_app_L; f_equal; auto..
    | done
    | apply leibniz_equiv_iff, list_to_set_singleton].
Qed.

Lemma PRO_tensors_MPRO_to_PRO {N MStruct Struct T}
  `{InterpStruct N MStruct Struct}
  (fN : N -> nat) {n m}
  (mp : @MPRO N MStruct T n m) : PRO_tensors (MPRO_to_PRO fN mp) =
  prod_map (prod_map (btree_size fN) (btree_size fN)) id <$>
  MPRO_tensors mp.
Proof.
  induction mp; [done| | |done..];
  cbn; rewrite fmap_app; now f_equal.
Qed.

Lemma PRO_tensors_MPRO_to_PRO_lists {N MStruct Struct T}
  `{InterpStruct N MStruct Struct}
  (fN : N -> nat) {n m}
  (mp : @MPRO N MStruct T n m) : PRO_tensors (MPRO_to_PRO fN mp) =
  prod_map (prod_map (sum_list_with fN) (sum_list_with fN)) id <$>
  MPRO_tensors_lists mp.
Proof.
  rewrite PRO_tensors_MPRO_to_PRO.
  unfold MPRO_tensors_lists.
  rewrite <- list_fmap_compose.
  apply list_fmap_ext.
  intros _ [[i o] t] _.
  cbn.
  now rewrite 2 sum_list_with_btree_elems.
Qed.

(* FIXME: Move *)
Lemma list_fmap_subseteq_inv {A B} (f : A -> B) {Hf : Inj eq eq f}
  (l l' : list A) :
  f <$> l ⊆ f <$> l' -> l ⊆ l'.
Proof.
  set_solver.
Qed.
#[export] Instance Forall_subseteq_proper {A} :
  Proper (pointwise_relation A iff ==> subseteq --> impl) (@Forall A).
Proof.
  intros P P' HP l l' Hl.
  rewrite 2 Forall_forall.
  hnf in *.
  naive_solver.
Qed.
Lemma Forall_subseteq_proper_inv {A} (l l' : list A)
  (Hl : forall P, Forall P l -> Forall P l') : l' ⊆ l.
Proof.
  specialize (Hl (.∈ l)).
  rewrite 2 Forall_forall in Hl.
  hnf.
  naive_solver.
Qed.

(* FIXME: Move *)
Lemma PRO_tensors_PRO_denote {Struct T T'} (f : T -> T')
  {n m} (p : PRO Struct T n m) :
  PRO_tensors (PRO_denote f p) = prod_map id f <$> PRO_tensors p.
Proof.
  induction p; cbn; rewrite ? fmap_app; f_equal; auto.
Qed.
Definition denote_MPRO {N} {MStruct} {T T'}
  (f : T -> T') {n m : btree N} (mp : MPRO MStruct T n m) : MPRO MStruct T' n m :=
  map_MPRO (λ _ _ s, s) f mp.
Lemma MPRO_to_PRO_denote_MPRO {N} {MStruct} {Struct}
  `{InterpM : InterpStruct N MStruct Struct} {T T'}
  (f : T -> T') fN {n m : btree N} (mp : MPRO MStruct T n m) :
  MPRO_to_PRO fN (denote_MPRO f mp) = PRO_denote f (MPRO_to_PRO fN mp).
Proof.
  induction mp; cbn; f_equal; done.
Qed.
Lemma MPRO_tensors_denote_MPRO {A MStruct T T'} (f : T -> T')
  {n m : btree A} (mp : MPRO MStruct T n m) :
  MPRO_tensors (denote_MPRO f mp) = prod_map id f <$> MPRO_tensors mp.
Proof.
  induction mp; cbn; rewrite ? fmap_app; f_equal; auto.
Qed.
Lemma MPRO_tensors_lists_denote_MPRO {A MStruct T T'} (f : T -> T')
  {n m : btree A} (mp : MPRO MStruct T n m) :
  MPRO_tensors_lists (denote_MPRO f mp) = prod_map id f <$> MPRO_tensors_lists mp.
Proof.
  induction mp; cbn; rewrite ? fmap_app; f_equal; auto.
Qed.

(* FIXME: Move to SizedPropGraphs or something *)
Class FreeSizedStructGraphable {N} (MStruct : Mor (btree N))
  {MStructG : forall T, SizedStructGraphable MStruct T} :=
  sized_graph_of_struct_free T {n m} (s : MStruct n m) :
    (sized_graph_of_struct (T:=T) s).(bw_scohg) =
    (bw_sized_graph_apply_hom (Empty_set_rect _) (sized_graph_of_struct s)).(bw_scohg).


#[export] Instance morunion_free_sized_graphable {N}
  `{FreeGraphS : FreeSizedStructGraphable N Struct,
    FreeGraphS' : FreeSizedStructGraphable N Struct'} :
      FreeSizedStructGraphable (MorUnion Struct Struct').
Proof.
  intros T n m [s|s]; cbn; apply sized_graph_of_struct_free.
Qed.

#[export] Instance mmonoidal_free_sized_graphable {A} :
  FreeSizedStructGraphable (@MMonoidal A).
Proof.
  intros T n m []; done.
Qed.

#[export] Instance msymmetry_free_sized_graphable {A} :
  FreeSizedStructGraphable (@MSymmetry A).
Proof.
  intros T n m []; done.
Qed.

#[export] Instance mautonomy_free_sized_graphable {A} :
  FreeSizedStructGraphable (@MAutonomy A).
Proof.
  intros T n m []; done.
Qed.

#[export] Instance mfrobenial_free_sized_graphable {A} :
  FreeSizedStructGraphable (@MFrobenial A).
Proof.
  intros T n m []; done.
Qed.



(* FIXME: Move *)
Delimit Scope lazy_bool_scope with lazy.




(* FIXME: Move *)
Lemma Forall2_of_impl {A B} (P Q : A -> B -> Prop) l l' :
  Forall2 (λ a b, P a b -> Q a b) l l' ->
  Forall2 P l l' -> Forall2 Q l l'.
Proof.
  intros Hll'.
  induction Hll'; [easy|].
  rewrite 2 Forall2_cons.
  tauto.
Qed.

Lemma Forall_of_impl {A} (P Q : A -> Prop) l :
  Forall (λ a, P a -> Q a) l ->
  Forall P l -> Forall Q l.
Proof.
  intros Hll'.
  induction Hll'; [easy|].
  rewrite 2 Forall_cons.
  tauto.
Qed.
(* FIXME: Move *)
Lemma Forall_zip_with_Forall2 {A B C} (P : C -> Prop)
  (f : A -> B -> C) l l' :
  length l = length l' ->
  Forall P (zip_with f l l') <-> Forall2 (λ a b, P (f a b)) l l'.
Proof.
  intros Hll'%Forall2_same_length.
  induction Hll'; [easy|].
  cbn.
  rewrite Forall_cons, Forall2_cons.
  f_equiv.
  done.
Qed.

Lemma Forall2_Forall_zip {A B} (P : A -> B -> Prop) l l' :
  length l = length l' ->
  Forall2 (λ a b, P a b) l l' <-> Forall (λ ab, P ab.1 ab.2) (zip l l').
Proof.
  intros Hlen.
  rewrite Forall_zip_with_Forall2 by done.
  done.
Qed.

Lemma elem_of_zip_lr {A B} (a : A) (b : B) l l' :
  (a, b) ∈ zip l l' -> a ∈ l /\ b ∈ l'.
Proof.
  intros Hab.
  apply elem_of_zip_l in Hab as Ha.
  apply elem_of_zip_r in Hab as Hb.
  done.
Qed.

(* FIXME: Move *)
Lemma simpl {P Q : Prop} {HPQ : TCSimpl P Q} :
  P -> Q.
Proof.
  hnf in HPQ.
  induction HPQ.
  done.
Qed.

(* FIXME: Move *)
Definition sized_graph_tensors {N T} {n m}
  (scohg : SizedCospanHyperGraph N T n m) : list (list N * list N * T) :=
  let smap : list positive -> list N := omap (scohg.(sized_map)!!.) in
  (λ '(_, (t, i, o)), (smap i, smap o, t)) <$>
  map_to_list scohg.(hyperedges).



Lemma sized_graph_tensors_scohg_syntactic_eq {N T}
  `{Equiv T, Equivalence T equiv} {n m}
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₛ scohg' ->
  PermutationA (prod_relation eq equiv)
    (sized_graph_tensors scohg)
    (sized_graph_tensors scohg').
Proof.
  intros Hscohg.
  induction Hscohg as [scohg scohg' fv fe Hfv Hfe Heq].
  unfold sized_graph_tensors.
  cbn.
  etransitivity. 2:{
    apply (Permutation_PermutationA _).
    rewrite map_to_list_fmap, (map_to_list_kmap fe).
    rewrite <- 2 list_fmap_compose.
    rewrite (list_fmap_ext _ (let smap : list positive -> list N :=
      omap (scohg'.(sized_map)!!.) in
      (λ '(_, (t, i, o)), (smap i, smap o, t)))). 2:{
      intros _ [k [ [t i] o]] _.
      simpl.
      rewrite 2 list_omap_fmap.
      f_equal.
      f_equal; apply list_omap_ext, Forall_Forall2_diag;
      rewrite Forall_forall;
      intros p _;
      cbn;
      rewrite (lookup_kmap _); done.
    }
    done.
  }
  apply eqlistA_PermutationA.
  specialize Heq.1.2.2.1 as Heq'.
  cbn in Heq'.
  apply (f_equiv map_to_list) in Heq'.
  rewrite eqlistA_altdef in Heq' |- *.
  rewrite Forall2_fmap.
  eapply Forall2_of_impl, Heq'.
  apply Forall2_length in Heq' as Hlen.
  rewrite Forall2_Forall_zip in Heq' |- * by done.
  rewrite Forall_forall.
  intros [[k [[t i] o]] [k' [[t' i'] o']]] [Hktio Hktio']%elem_of_zip_lr.
  cbn.
  intros [[= <-] [[Hts%simpl [= <-]] [= <-]]].
  split; [|done].
  cbn.
  specialize Heq.2 as Hmap.
  eenough (Forall _ (i ++ o)) as Hen.
  1:{
    apply Forall_app in Hen as [Hi Ho].
    f_equal; apply list_omap_ext, Forall_Forall2_diag; done.
  }
  rewrite Forall_forall.
  intros v Hvio.
  assert (Hv : v ∈ vertices scohg). 1:{
    apply elem_of_vertices.
    left.
    apply elem_of_app in Hvio.
    exists k, (t, i, o).
    split; [now apply elem_of_map_to_list|].
    done.
  }
  assert (Hv' : v ∈ vertices scohg'). 1:{
    apply elem_of_vertices.
    left.
    apply elem_of_app in Hvio.
    exists k, (t', i, o).
    split; [now apply elem_of_map_to_list|].
    done.
  }
  apply (f_equal (.!! v)) in Hmap.
  cbn in Hmap.
  rewrite 2 map_lookup_filter in Hmap.
  cbn in Hmap.
  do 2 (case_guard; [|contradiction]).
  cbn in Hmap.
  rewrite 2 bind_with_Some in Hmap.
  done.
Qed.

#[export] Instance sized_graph_tensors_scohg_vert_eq {N T n m} :
  Proper (scohg_vert_eq ==> eq) (@sized_graph_tensors N T n m).
Proof.
  intros scohg scohg' Hscohg%scohg_vert_eq_alt.
  unfold sized_graph_tensors.
  rewrite <- Hscohg.2.2.1.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] Hktio%elem_of_list_lookup_2%elem_of_map_to_list.
  f_equal.

  eenough (Forall _ (i ++ o)) as Hen.
  1:{
    apply Forall_app in Hen as [Hi Ho].
    f_equal; apply list_omap_ext, Forall_Forall2_diag; done.
  }
  rewrite Forall_forall.
  intros v Hvio.
  assert (Hv : v ∈ vertices scohg). 1:{
    apply elem_of_vertices.
    left.
    apply elem_of_app in Hvio.
    exists k, (t, i, o).
    done.
  }
  apply Hscohg.2.2.2.2.
  now apply elem_of_union_l.
Qed.

Import ToUnsized.


Lemma sized_graph_tensors_sized_add_top_loop {N T n m}
  (scohg : SizedCospanHyperGraph N T (S n) (S m)) :
  head (sized_inputs scohg) = head (sized_outputs scohg) ->
  sized_graph_tensors (sized_add_top_loop scohg) = sized_graph_tensors scohg.
Proof.
  intros Hio.
  unfold sized_graph_tensors.
  cbn.
  rewrite map_to_list_fmap, <- list_fmap_compose.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] Hktio%elem_of_list_lookup_2%elem_of_map_to_list.
  cbn.
  f_equal.
  rewrite 2 list_omap_fmap.

  eenough (Forall _ (i ++ o)) as Hen.
  1:{
    apply Forall_app in Hen as [Hi Ho].
    f_equal; apply list_omap_ext, Forall_Forall2_diag; done.
  }
  rewrite Forall_forall.
  intros v Hvio.
  unfold sized_inputs in Hio.
  unfold sized_outputs in Hio.
  destruct scohg as [[hg ins outs] smap].
  cbn in *.
  revert Hio.
  inv_vec ins; intros hi ins.
  inv_vec outs; intros ho outs.
  intros [= Hio].
  cbn -[map_relabel_one].
  rewrite lookup_map_relabel_one.
  rewrite (fn_lookup_singleton_case _ _ v).
  case_decide; [subst v; now rewrite fn_lookup_singleton|].
  rewrite (fn_lookup_singleton_case _ _ v).
  case_decide; [subst v|]; done.
Qed.

Lemma sized_graph_tensors_sized_add_top_loops {N T n m o}
  (scohg : SizedCospanHyperGraph N T (n + m) (n + o)) :
  take n $ sized_inputs scohg = take n $ sized_outputs scohg ->
  sized_graph_tensors (sized_add_top_loops scohg) = sized_graph_tensors scohg.
Proof.
  intros Hio.
  induction n; [done|].
    cbn in Hio.
  cbn.
  fold Nat.add.
  rewrite IHn.
  2:{
    rewrite sized_inputs_add_top_loop, sized_outputs_add_top_loop by
      (rewrite <- (lookup_take _ (S n)), Hio, lookup_take by lia; done).
    rewrite 2 tail_is_drop, 2 firstn_skipn_comm.
    cbn.
    rewrite Hio.
    done.
  }
  rewrite sized_graph_tensors_sized_add_top_loop; [done|].
  rewrite 2 head_lookup.
  rewrite <- (lookup_take _ (S n)), Hio, lookup_take by lia; done.
Qed.

Lemma sized_graph_tensors_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m) (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_graph_tensors (stack_sized_graphs scohg scohg') ≡ₚ
  sized_graph_tensors scohg ++ sized_graph_tensors scohg'.
Proof.
  unfold sized_graph_tensors.
  cbn.
  rewrite map_to_list_disj_union by
    now apply map_disjoint_fmap, (kmap_inj2_disjoint _).
  rewrite fmap_app.
  rewrite 2 map_to_list_fmap, 2 (map_to_list_kmap _).
  rewrite <- 4 list_fmap_compose.
  f_equiv; apply eq_reflexivity, list_fmap_ext;
  intros _ [k [[t i] o]] _; cbn; f_equal;

  rewrite 2 list_omap_fmap;
  (
  eenough (Forall _ (i ++ o)) as Hen;
  [
    apply Forall_app in Hen as [Hi Ho];
    f_equal; apply list_omap_ext, Forall_Forall2_diag; done|];
  rewrite Forall_forall;
  intros v _;
  cbn -[bcons]).
  - rewrite lookup_union, (lookup_kmap _), (lookup_kmap_None_1 _) by lia.
    apply (right_id_L _ _).
  - rewrite lookup_union, (lookup_kmap _), (lookup_kmap_None_1 _) by lia.
    apply (left_id_L _ _).
Qed.

Lemma sized_graph_tensors_swapped_stack_sized_graphs {N T n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m) (scohg' : SizedCospanHyperGraph N T n' m') :
  sized_graph_tensors (swapped_stack_sized_graphs scohg scohg') ≡ₚ
  sized_graph_tensors scohg ++ sized_graph_tensors scohg'.
Proof.
  unfold sized_graph_tensors.
  cbn.
  rewrite map_to_list_disj_union by
    now apply map_disjoint_fmap, (kmap_inj2_disjoint _).
  rewrite fmap_app.
  rewrite 2 map_to_list_fmap, 2 (map_to_list_kmap _).
  rewrite <- 4 list_fmap_compose.
  f_equiv; apply eq_reflexivity, list_fmap_ext;
  intros _ [k [[t i] o]] _; cbn; f_equal;

  rewrite 2 list_omap_fmap;
  (
  eenough (Forall _ (i ++ o)) as Hen;
  [
    apply Forall_app in Hen as [Hi Ho];
    f_equal; apply list_omap_ext, Forall_Forall2_diag; done|];
  rewrite Forall_forall;
  intros v _;
  cbn -[bcons]).
  - rewrite lookup_union,
   (lookup_kmap _), (lookup_kmap_None_1 _) by lia.
    apply (right_id_L _ _).
  - rewrite lookup_union, (lookup_kmap _), (lookup_kmap_None_1 _) by lia.
    apply (left_id_L _ _).
Qed.

Lemma sized_graph_tensors_compose_sized_graphs {N T n m o}
  (scohg : SizedCospanHyperGraph N T n m) (scohg' : SizedCospanHyperGraph N T m o) :
  sized_outputs scohg = sized_inputs scohg' ->
  sized_graph_tensors (compose_sized_graphs scohg scohg') ≡ₚ
  sized_graph_tensors scohg ++ sized_graph_tensors scohg'.
Proof.
  intros Hoi.
  rewrite <- compose_sized_graphs_alt_correct.
  rewrite sized_graph_tensors_sized_add_top_loops, sized_graph_tensors_swapped_stack_sized_graphs;
  [done|].
  rewrite sized_inputs_swapped_stack_sized_graphs, sized_outputs_swapped_stack_sized_graphs.
  rewrite <- (length_sized_inputs scohg') at 1.
  rewrite take_app_length.
  rewrite <- (length_sized_outputs scohg) at 2.
  rewrite take_app_length.
  done.
Qed.

Lemma sized_graph_tensors_sized_graph_apply_hom {N T T' n m}
  (f : T -> T') (scohg : SizedCospanHyperGraph N T n m) :
  sized_graph_tensors (sized_graph_apply_hom f scohg) =
  prod_map id f <$> (sized_graph_tensors scohg).
Proof.
  unfold sized_graph_tensors.
  cbn.
  rewrite map_to_list_fmap, <- 2 list_fmap_compose.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] _; done.
Qed.

Lemma sized_graph_tensors_empty {N n m}
  (scohg : SizedCospanHyperGraph N Empty_set n m) :
  sized_graph_tensors scohg = [].
Proof.
  destruct (sized_graph_tensors _) as [|[? []]]; done.
Qed.

Lemma sized_graph_tensors_sized_graph_of_tensor {N T}
  (t : T) {n m} (v : vec N n) (w : vec N m) :
  sized_graph_tensors (sized_graph_of_tensor t v w) =
  [(vec_to_list v, vec_to_list w, t)].
Proof.
  unfold sized_graph_tensors.
  cbn -[union singletonM insert].
  setoid_rewrite map_to_list_singleton.
  cbn.
  do 2 f_equal.
  f_equal.
  - rewrite list_omap_fmap.
    eenough (Hall : _).
    apply (list_eq_same_length _ _ _ eq_refl).
    1:{
      rewrite length_omap_all_is_Some, length_vec_to_list, length_seq; [reflexivity|].
      apply Hall.
    }
    2:{
      intros a [_ Ha]%elem_of_seq.
      cbn [compose].
      rewrite lookup_union.
      rewrite (lookup_list_to_map_imap (bcons false ∘ Pos.of_succ_nat) _ _ a).
      rewrite option_fmap_id.
      rewrite union_is_Some.
      rewrite lookup_lt_is_Some.
      rewrite length_vec_to_list.
      now left.
    }
    intros i x y Hi.
    rewrite length_vec_to_list in Hi.
    rewrite list_lookup_omap_all_is_Some by done.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite lookup_union.
    setoid_rewrite (lookup_list_to_map_imap (xO ∘ Pos.of_succ_nat)).
    rewrite option_fmap_id.
    rewrite lookup_vec_to_list.
    case_guard; [|done].
    cbn.
    rewrite union_Some_l.
    congruence.
  - rewrite list_omap_fmap.
    eenough (Hall : _).
    apply (list_eq_same_length _ _ _ eq_refl).
    1:{
      rewrite length_omap_all_is_Some, length_vec_to_list, length_seq; [reflexivity|].
      apply Hall.
    }
    2:{
      intros a [_ Ha]%elem_of_seq.
      cbn [compose].
      rewrite lookup_union.
      rewrite union_is_Some.
      right.
      rewrite (lookup_list_to_map_imap (bcons true ∘ Pos.of_succ_nat) _ _ a).
      rewrite option_fmap_id.
      rewrite lookup_lt_is_Some.
      rewrite length_vec_to_list.
      done.
    }
    intros i x y Hi.
    rewrite length_vec_to_list in Hi.
    rewrite list_lookup_omap_all_is_Some by done.
    rewrite lookup_seq_lt by done.
    cbn.
    rewrite lookup_union.
    setoid_rewrite (lookup_list_to_map_imap (xI ∘ Pos.of_succ_nat)).
    rewrite option_fmap_id.
    rewrite lookup_vec_to_list.
    case_guard; [|done].
    cbn.
    rewrite (not_elem_of_list_to_map _ _).1. 2:{
      rewrite fmap_imap.
      rewrite elem_of_lookup_imap.
      cbn.
      naive_solver.
    }
    rewrite (left_id_L None _).
    congruence.
Qed.

Lemma sized_graph_tensors_MPRO_graph_semantics
  {A} {MStruct : Mor (btree A)}
  {MStructG : forall T, @SizedStructGraphable A MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {T}
  {n m} (mp : MPRO MStruct T n m) :
  sized_graph_tensors (MPRO_graph_semantics mp) ≡ₚ
  MPRO_tensors_lists mp.
Proof.
  induction mp.
  - done.
  - cbn.
    rewrite sized_graph_tensors_compose_sized_graphs, fmap_app; [now f_equiv|].
    rewrite bw_outputs, bw_inputs.
    done.
  - cbn.
    rewrite sized_graph_tensors_stack_sized_graphs, fmap_app; now f_equiv.
  - cbn.
    rewrite sized_graph_of_struct_free.
    cbn.
    rewrite sized_graph_tensors_sized_graph_apply_hom.
    rewrite sized_graph_tensors_empty.
    done.
  - cbn.
    rewrite sized_graph_tensors_sized_graph_of_tensor.
    now rewrite 2 btree_to_vec_to_list.
Qed.


(* FIXME: Move *)
Definition graph_tensors {T} {n m}
  (scohg : CospanHyperGraph T n m) : list (nat * nat * T) :=
  (λ '(_, (t, i, o)), (length i, length o, t)) <$>
  map_to_list scohg.(hyperedges).



Lemma graph_tensors_cohg_syntactic_eq {T}
  `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  (cohg ≡ₛ cohg')%cohg ->
  PermutationA (prod_relation eq equiv)
    (graph_tensors cohg)
    (graph_tensors cohg').
Proof.
  intros Hcohg.
  induction Hcohg as [cohg cohg' fv fe Hfv Hfe Heq].
  unfold graph_tensors.
  cbn.
  etransitivity. 2:{
    apply (Permutation_PermutationA _).
    rewrite map_to_list_fmap, (map_to_list_kmap fe).
    rewrite <- 2 list_fmap_compose.
    rewrite (list_fmap_ext _
      (λ '(_, (t, i, o)), (length i, length o, t))). 2:{
      intros _ [k [ [t i] o]] _.
      simpl.
      rewrite 2 length_fmap; done.
    }
    done.
  }
  apply eqlistA_PermutationA.
  specialize Heq.2.2.1 as Heq'.
  cbn in Heq'.
  apply (f_equiv map_to_list) in Heq'.
  rewrite eqlistA_altdef in Heq' |- *.
  rewrite Forall2_fmap.
  eapply Forall2_of_impl, Heq'.
  apply Forall2_length in Heq' as Hlen.
  rewrite Forall2_Forall_zip in Heq' |- * by done.
  rewrite Forall_forall.
  intros [[k [[t i] o]] [k' [[t' i'] o']]] [Hktio Hktio']%elem_of_zip_lr.
  cbn.
  intros [[= <-] [[Hts%simpl [= <-]] [= <-]]].
  done.
Qed.

#[export] Instance graph_tensors_cohg_vert_eq {T n m} :
  Proper (cohg_vert_eq ==> eq) (@graph_tensors T n m).
Proof.
  intros cohg cohg' Hcohg%cohg_vert_eq_alt.
  unfold graph_tensors.
  rewrite <- Hcohg.2.2.1.
  done.
Qed.

Lemma graph_tensors_relabel_graph {T n m} f
  (cohg : CospanHyperGraph T n m) :
  graph_tensors (relabel_graph f cohg) = graph_tensors cohg.
Proof.
  unfold graph_tensors.
  cbn.
  rewrite map_to_list_fmap.
  rewrite <- list_fmap_compose.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] _.
  cbn.
  now rewrite 2 length_fmap.
Qed.

Lemma graph_tensors_add_top_loop {T n m}
  (cohg : CospanHyperGraph T (S n) (S m)) :
  graph_tensors (add_top_loop cohg) = graph_tensors cohg.
Proof.
  unfold add_top_loop.
  rewrite graph_tensors_relabel_graph.
  done.
Qed.

Lemma graph_tensors_add_top_loops {T n m o}
  (cohg : CospanHyperGraph T (n + m) (n + o)) :
  graph_tensors (add_top_loops cohg) = graph_tensors cohg.
Proof.
  induction n; [done|].
  cbn.
  fold Nat.add.
  rewrite IHn.
  rewrite graph_tensors_add_top_loop; done.
Qed.

Lemma graph_tensors_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  graph_tensors (stack_graphs cohg cohg') ≡ₚ
  graph_tensors cohg ++ graph_tensors cohg'.
Proof.
  unfold graph_tensors.
  cbn.
  rewrite map_to_list_disj_union by
    now apply map_disjoint_fmap, (kmap_inj2_disjoint _).
  rewrite fmap_app.
  rewrite 2 map_to_list_fmap, 2 (map_to_list_kmap _).
  rewrite <- 4 list_fmap_compose.
  f_equiv; apply eq_reflexivity, list_fmap_ext;
  intros _ [k [[t i] o]] _; cbn; now rewrite 2 length_fmap.
Qed.

Lemma graph_tensors_swapped_stack_graphs {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  graph_tensors (swapped_stack_graphs cohg cohg') ≡ₚ
  graph_tensors cohg ++ graph_tensors cohg'.
Proof.
  unfold graph_tensors.
  cbn.
  rewrite map_to_list_disj_union by
    now apply map_disjoint_fmap, (kmap_inj2_disjoint _).
  rewrite fmap_app.
  rewrite 2 map_to_list_fmap, 2 (map_to_list_kmap _).
  rewrite <- 4 list_fmap_compose.
  f_equiv; apply eq_reflexivity, list_fmap_ext;
  intros _ [k [[t i] o]] _; cbn; now rewrite 2 length_fmap.
Qed.

Lemma graph_tensors_compose_graphs {T n m o}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o) :
  graph_tensors (compose_graphs cohg cohg') ≡ₚ
  graph_tensors cohg ++ graph_tensors cohg'.
Proof.
  rewrite <- compose_graphs_alt_correct.
  rewrite graph_tensors_add_top_loops, graph_tensors_swapped_stack_graphs;
  done.
Qed.

Lemma graph_tensors_graph_apply_hom {T T' n m}
  (f : T -> T') (cohg : CospanHyperGraph T n m) :
  graph_tensors (graph_apply_hom f cohg) =
  prod_map id f <$> (graph_tensors cohg).
Proof.
  unfold graph_tensors.
  cbn.
  rewrite map_to_list_fmap, <- 2 list_fmap_compose.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] _; done.
Qed.

Lemma graph_tensors_empty {n m}
  (cohg : CospanHyperGraph Empty_set n m) :
  graph_tensors cohg = [].
Proof.
  destruct (graph_tensors _) as [|[? []]]; done.
Qed.

Lemma graph_tensors_graph_of_tensor {T}
  (t : T) n m :
  graph_tensors (graph_of_tensor t n m) =
  [(n, m, t)].
Proof.
  unfold graph_tensors.
  cbn -[union singletonM insert].
  setoid_rewrite map_to_list_singleton.
  cbn.
  rewrite 2 length_fmap, 2 length_seq.
  done.
Qed.

Lemma graph_tensors_PRO_graph_semantics
  {Struct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeMStructG : FreeStructGraphable Struct}
  {T}
  {n m} (mp : PRO Struct T n m) :
  graph_tensors (PRO_graph_semantics mp) ≡ₚ
  PRO_tensors mp.
Proof.
  induction mp.
  - done.
  - cbn.
    rewrite graph_tensors_compose_graphs.
    now f_equiv.
  - cbn.
    rewrite graph_tensors_stack_graphs.
    now f_equiv.
  - cbn.
    rewrite graph_of_struct_free.
    cbn.
    rewrite graph_tensors_graph_apply_hom.
    rewrite graph_tensors_empty.
    done.
  - cbn.
    rewrite graph_tensors_graph_of_tensor.
    done.
Qed.

(* FIXME: Move *)
Lemma length_list_bind {A B} (f : A -> list B) l :
  length (l ≫= f) = sum_list_with (length ∘ f) l.
Proof.
  induction l; cbn; [done|].
  now rewrite length_app; f_equal.
Qed.

Lemma graph_tensors_sized_graph_to_graph {N T n m}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m) :
  graph_tensors (sized_graph_to_graph f scohg) =
  prod_map (prod_map (sum_list_with f) (sum_list_with f)) id <$>
  sized_graph_tensors scohg.
Proof.
  unfold graph_tensors.
  cbn.
  rewrite map_to_list_fmap.
  unfold sized_graph_tensors.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext.
  intros _ [k [[t i] o]] _.
  cbn.
  f_equal.
  rewrite 2 length_list_bind.
  eenough (forall l, _ l =@{nat} sum_list_with f (_ l)) as Hen.
  1:{
    f_equal.
    - exact (Hen i).
    - exact (Hen o).
  }
  clear i o.
  intros l.
  induction l; [done|].
  cbn.
  case_match eqn:Heq.
  - cbn.
    rewrite length_vec_to_list.
    f_equal.
    done.
  - done.
Qed.

(* FIXME: Move *)
#[export] Instance Permutation_PermutationA_subrelation {A} (R : relation A) {HR : Equivalence R} :
  subrelation Permutation (PermutationA R).
Proof.
  intros ? ?.
  now apply Permutation_PermutationA.
Qed.

Lemma graph_tensors_cast_graph {T n m n' m'}
  (Hn : n = n') (Hm : m = m') (cohg : CospanHyperGraph T n m) :
  graph_tensors (cast_graph Hn Hm cohg) = graph_tensors cohg.
Proof.
  subst.
  rewrite cast_graph_id.
  done.
Qed.


Lemma MPRO_PRO_quote_correct_tensors_lists {N}
  {MStruct : Mor (btree N)} {Struct : Mor nat} {T}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {InterpS : InterpStruct MStruct Struct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {MStructG : forall T, SizedStructGraphable MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {LawStruct : LawfulSizedStructGraphable MStruct Struct T}
  (fN : N -> nat)

  {a b : btree N} (mp : MPRO MStruct T a b) {n m} (p : PRO Struct T n m) :
  MPRO_PRO_quote fN mp p ->
  PermutationA (prod_relation eq equiv)
    (prod_map (prod_map (sum_list_with fN) (sum_list_with fN)) id <$> MPRO_tensors_lists mp)
    (PRO_tensors p).
Proof.
  intros Hmp.
  apply MPRO_PRO_quote_size in Hmp as Hnm.
  destruct Hnm as [-> ->].
  apply MPRO_PRO_quote_correct_graph_semantics' in Hmp.
  apply graph_tensors_cohg_syntactic_eq in Hmp.
  rewrite (graph_tensors_PRO_graph_semantics p) in Hmp.
  rewrite Hmp.
  unfold bw_sized_graph_to_graph.
  rewrite graph_tensors_cast_graph.
  rewrite graph_tensors_sized_graph_to_graph.
  rewrite sized_graph_tensors_MPRO_graph_semantics.
  done.
Qed.

Lemma PRO_quote_correct_tensors {Struct} `{forall n m, Equiv (Struct n m)} {T T'} `{Equiv T', Equivalence T' equiv}
  (f : T -> T') {n m} (qp : PRO Struct T n m) p :
  PRO_quote f qp p ->
  eqlistA (prod_relation eq equiv) (prod_map id f <$> PRO_tensors qp) (PRO_tensors p).
Proof.
  intros Hqp.
  hnf in Hqp.
  unfold PRO_denote in Hqp.
  apply PRO_equiv_fun_correct' in Hqp.
  induction qp.
  - destruct p; destruct Hqp as [].
    done.
  - destruct p as [|n m' o p1 p2| | |]; first [destruct Hqp as [ Hp1 Hp2]|destruct Hqp as []].
    apply PRO_equiv_fun_correct_dim in Hp1 as Hdims.
    destruct Hdims as [_ <-].
    cbn.
    rewrite fmap_app.
    f_equiv; eauto.
  - destruct p; destruct Hqp as [].
    cbn.
    select (PRO_equiv_fun _ p1) (fun H => apply PRO_equiv_fun_correct_dim in H as Hdims; destruct Hdims as [<- <-]).
    select (PRO_equiv_fun _ p2) (fun H => apply PRO_equiv_fun_correct_dim in H as Hdims; destruct Hdims as [<- <-]).
    rewrite fmap_app.
    f_equiv; eauto.
  - destruct p; destruct Hqp as [].
    done.
  - destruct p; destruct Hqp as [].
    destruct_and!.
    cbn.
    constructor; done.
Qed.

(* FIXME: Move *)
Lemma InA_eqA {A} {R : relation A} {HRS : Symmetric R}
  {HRT : Transitive R} (x y : A) l :
  R x y -> InA R x l <-> InA R y l.
Proof.
  intros Hxy.
  induction l; [easy|].
  rewrite 2 InA_cons.
  f_equiv; [|done].
  naive_solver.
Qed.

#[export] Instance InA_eqlistA {A} {R : relation A} {HRS : Symmetric R}
  {HRT : Transitive R} :
  Proper (R ==> eqlistA R ==> iff) (InA R).
Proof.
  intros x y Hxy l l' Hl.
  rewrite <- (InA_eqA _ _ _ Hxy).
  clear y Hxy.
  induction Hl; [done|].
  rewrite 2 InA_cons.
  f_equiv; [|done].
  naive_solver.
Qed.


#[export] Instance inclA_eqlistA {A} {R : relation A} {HR : Equivalence R} :
  Proper (eqlistA R ==> eqlistA R ==> iff) (inclA R).
Proof.
  intros l0 l0' Hl0 l1 l1' Hl1.
  unfold inclA.
  apply forall_iff; intros a.
  rewrite Hl0, Hl1.
  done.
Qed.

Lemma InA_fmap {A B} {RA : relation A} {RB : relation B} {HRA : Reflexive RA}
  {HRB : Transitive RB}
  (f : A -> B) {Hf : Proper (RA ==> RB) f} x l :
  InA RB x (f <$> l) <-> exists y, RB x (f y) /\ InA RA y l.
Proof.
  induction l.
  - cbn.
    split; [easy|].
    intros []; easy.
  - cbn.
    setoid_rewrite InA_cons.
    rewrite IHl.
    naive_solver.
Qed.


#[export] Instance list_fmap_inclA {A B} {RA : relation A} {RB : relation B}
  {HRA : Equivalence RA} {HRB : Equivalence RB}
  f {Hf : Proper (RA ==> RB) f} : Proper (inclA RA ==> inclA RB) (fmap f).
Proof.
  intros l l' Hl x.
  assert (HRA' : Reflexive RA) by apply _.
  rewrite 2 (InA_fmap f).
  intros (y & Hxy & Hyl).
  apply Hl in Hyl.
  eauto.
Qed.

#[export] Instance inclA_cons {A} {R : relation A} {HR : Transitive R} :
  Proper (R ==> inclA R ==> inclA R) cons.
Proof.
  intros x y Hxy l l' Hl.
  intros z.
  rewrite 2 InA_cons.
  rewrite Hxy.
  naive_solver.
Qed.

#[export] Instance inclA_trans {A} {R : relation A} {HR : Transitive R} :
  Transitive (inclA R).
Proof.
  intros l l' l''.
  unfold inclA.
  naive_solver.
Qed.

#[export] Instance inclA_refl {A} {R : relation A} :
  Reflexive (inclA R).
Proof.
  easy.
Qed.

#[export] Instance PermutationA_inclA {A} {R : relation A} {HR : Transitive R} :
  subrelation (PermutationA R) (inclA R).
Proof.
  intros l l' Hl.
  induction Hl.
  - easy.
  - f_equiv; done.
  - intros z.
    rewrite 4 InA_cons.
    tauto.
  - etransitivity; eauto.
Qed.





Record LawfulMPRORewritingRelation {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
   := mk_LawfulMPRORewritingRelation {
  LPRR :>
    LawfulPRORewritingRelation Struct T;
  pro_rewriting_domain_mono_strong {n m} (p : PRO Struct T n m)
    {n' m'} (p' : PRO Struct T n' m') :
    (forall nmt, nmt ∈ PRO_tensors p -> InA (prod_relation eq equiv) nmt (PRO_tensors p')) ->
    LPRR.(pro_rewriting_domain) p' -> LPRR.(pro_rewriting_domain) p;
  mpro_rewriting_relation_graph_syntax_l {n m} (mp mp' mq : MPRO MStruct T n m)  :
    MPRO_graph_semantics mp ≡ₛ MPRO_graph_semantics mp' ->
    forall fN,
    LPRR.(pro_rewriting_domain) (MPRO_to_PRO fN mp') ->
    LPRR _ _ (MPRO_to_PRO fN mp) (MPRO_to_PRO fN mq) ->
    LPRR _ _ (MPRO_to_PRO fN mp') (MPRO_to_PRO fN mq);
  }.

Global Arguments LawfulMPRORewritingRelation (_ _ _) {_ _ _ _ _ _ _} : assert.


Lemma pro_rewriting_domain_mono {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (p : PRO Struct T n m)
    {n' m'} (p' : PRO Struct T n' m') :
    PRO_tensors p ⊆ PRO_tensors p' ->
    RW.(pro_rewriting_domain) p' -> RW.(pro_rewriting_domain) p.
Proof.
  intros Htens.
  apply pro_rewriting_domain_mono_strong.
  intros nmt Hnmt%Htens%elem_of_list_In.
  apply (In_InA _).
  done.
Qed.

Lemma pro_rewriting_domain_mono_inclA {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (p : PRO Struct T n m)
    {n' m'} (p' : PRO Struct T n' m') :
    inclA (prod_relation eq equiv) (PRO_tensors p) (PRO_tensors p') ->
    RW.(pro_rewriting_domain) p' -> RW.(pro_rewriting_domain) p.
Proof.
  intros Hpp'.
  apply pro_rewriting_domain_mono_strong.
  intros nmt Hnmt.
  apply Hpp'.
  apply (In_InA _), elem_of_list_In.
  done.
Qed.




Lemma mpro_rewriting_domain_mono {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp : MPRO MStruct T n m)
    {n' m'} (mp' : MPRO MStruct T n' m') :
    MPRO_tensors mp ⊆ MPRO_tensors mp' ->
  forall fN,
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp') ->
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp).
Proof.
  intros Hmp fN.
  apply pro_rewriting_domain_mono.
  rewrite 2 PRO_tensors_MPRO_to_PRO.
  now apply list_fmap_subseteq.
Qed.

Lemma mpro_rewriting_domain_mono_lists {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp : MPRO MStruct T n m)
    {n' m'} (mp' : MPRO MStruct T n' m') :
    MPRO_tensors_lists mp ⊆ MPRO_tensors_lists mp' ->
  forall fN,
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp') ->
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp).
Proof.
  intros Hmp fN.
  apply pro_rewriting_domain_mono.
  rewrite 2 PRO_tensors_MPRO_to_PRO_lists.
  now apply list_fmap_subseteq.
Qed.



Lemma mpro_rewriting_domain_mono_encoded {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{Countable T}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp : MPRO MStruct T n m)
    {n' m'} (mp' : MPRO MStruct T n' m') :
    MPRO_tensors_encoded mp ⊆ MPRO_tensors_encoded mp' ->
  forall fN,
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp') ->
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp).
Proof.
  intros Hmp.
  apply mpro_rewriting_domain_mono_lists.
  apply (list_fmap_subseteq_inv encode).
  unfold MPRO_tensors_lists.
  rewrite <- 2 list_fmap_compose.
  exact Hmp.
Qed.

Lemma mpro_rewriting_domain_mono_set {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{Countable T}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp : MPRO MStruct T n m)
    {n' m'} (mp' : MPRO MStruct T n' m') :
    MPRO_tensors_set mp ⊆ MPRO_tensors_set mp' ->
  forall fN,
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp') ->
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mp).
Proof.
  intros Hmp.
  apply mpro_rewriting_domain_mono_encoded.
  rewrite <- 2 list_to_set_MPRO_tensors_encoded in Hmp.
  now apply list_to_set_subseteq in Hmp.
Qed.

Lemma mpro_rewriting_domain_mono_set_quoted {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{Equiv T, Equivalence T equiv}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  `{Countable T'} (f : T' -> T)
  {n m} (mp : MPRO MStruct T' n m)
    {n' m'} (mp' : MPRO MStruct T' n' m') :
    MPRO_tensors_set mp ⊆ MPRO_tensors_set mp' ->
  forall fN,
    RR.(pro_rewriting_domain) (PRO_denote f (MPRO_to_PRO fN mp')) ->
    RR.(pro_rewriting_domain) (PRO_denote f (MPRO_to_PRO fN mp)).
Proof.
  intros Hmp fN.
  rewrite <- 2 MPRO_to_PRO_denote_MPRO.
  apply mpro_rewriting_domain_mono_lists.
  rewrite 2 MPRO_tensors_lists_denote_MPRO.
  apply list_fmap_subseteq.
  apply (list_fmap_subseteq_inv encode).
  rewrite <- 2 list_to_set_MPRO_tensors_encoded in Hmp.
  unfold MPRO_tensors_lists.
  rewrite <- 2 list_fmap_compose.
  now apply list_to_set_subseteq in Hmp.
Qed.

Lemma mpro_rewriting_relation_graph_syntax_r {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp mq mq' : MPRO MStruct T n m)  :
    MPRO_graph_semantics mq ≡ₛ MPRO_graph_semantics mq' ->
    forall fN,
    RR.(pro_rewriting_domain) (MPRO_to_PRO fN mq') ->
    RR _ _ (MPRO_to_PRO fN mp) (MPRO_to_PRO fN mq) ->
    RR _ _ (MPRO_to_PRO fN mp) (MPRO_to_PRO fN mq').
Proof.
  intros Hqq' fN Hq' Hqp%symmetry.
  apply (mpro_rewriting_relation_graph_syntax_l RR mq mq' mp Hqq') in Hqp; [|by auto..].
  now symmetry.
Qed.

Lemma mpro_rewriting_relation_graph_syntax  {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (RR : LawfulMPRORewritingRelation MStruct Struct T)
  {n m} (mp mq : MPRO MStruct T n m)  :
    MPRO_graph_semantics mp ≡ₛ MPRO_graph_semantics mq ->
    forall fN,
    pro_rewriting_domain RR (MPRO_to_PRO fN mp) ->
    pro_rewriting_domain RR (MPRO_to_PRO fN mq) ->
    RR _ _ (MPRO_to_PRO fN mp) (MPRO_to_PRO fN mq).
Proof.
  intros Hpq fN Hp Hq.
  apply (mpro_rewriting_relation_graph_syntax_l RR mq mp mq); [done..|].
  now apply pro_rewriting_relation_refl.
Qed.

(* Definition LMPRR_rel {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  {concrete_assignments : Pmap nat}
  (RR : LawfulMPRORewritingRelation MStruct Struct T concrete_assignments) *)



Program Definition LawfulProLike_LawfulMPRORewritingRelation
  (MStruct : Mor (btree positive))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct n m) equiv}
  {SizedProD : SizedProLike MStruct Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct MStruct Struct := SizedProD.(SPL_interp))
  (* (SomeTTest : SizedOfTensorSomeTestable T D := SizedProD.(SPL_test)) *)
  {MStructG : @SizedStructGraphable positive MStruct T}
  {StructG : StructGraphable Struct T}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable MStruct Struct T}
  {LawTensD : LawfulTensorableDiagram R A T D }
  (* {LawSomeTTest : LawfulSizedOfTensorSomeTestable T D} *)
  : LawfulMPRORewritingRelation MStruct Struct T := {|
  LPRR := LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro;
  (* pro_rewriting_relation n m :=
    λ p q, exists d1 d2, DiagramDenote d1 p /\ DiagramDenote d2 q /\ d1 ≡ d2;
  pro_rewriting_domain n m p := is_Some (PRO_to_diagram p); *)
|}.
Next Obligation.
  intros until p'.
  intros Hp.
  cbn.
  rewrite 2 PRO_to_diagram_is_Some.
  rewrite 2 Forall_forall.
  intros Hp'.
  intros ((i, o), t) Htio%Hp%InA_alt.
  destruct Htio as ([[i' o'] t'] & [[= <- <-] Hts] & Ht').
  simpl in Hts.
  erewrite (f_equiv is_Some).
  2:{
    apply (LawTensD.(ofTensor_proper R A)), Hts.
  }
  now apply (Hp' (i, o, t')).
Qed.
Next Obligation.
  intros until mp.
  intros mp' mq Hpp' fN Hmp' Hpq.
  eapply pro_rewriting_relation_graph_syntax_l, Hpq; [done|].
  rewrite <- 2 (MPRO_graph_semantics_correct).
  now apply bw_sized_graph_to_graph_scohg_syntactic_eq.
Qed.






Import SizedPropGraphTerm.





















(* FIXME: Move *)



Lemma LawfulMProLike_MPRO_quote_test_correct `{Countable T'}
  (MStruct : Mor (btree positive))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct n m) equiv}
  {SizedProD : SizedProLike MStruct Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct MStruct Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable MStruct Struct T}
  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation MStruct LawPro)
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}


  (f : T' -> T)
  {n m} (dlhs drhs : D n m) :
  forall lhs rhs,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  forall (fN : positive -> nat) a b (Mlhs Mrhs : MPRO MStruct T' a b),
  MPRO_PRO_quote (MStruct:=MStruct) fN Mlhs Qlhs ->
  MPRO_PRO_quote (MStruct:=MStruct) fN Mrhs Qrhs ->
  default_countable_sized_graph_iso_test (MPRO_graph_semantics Mlhs)
    (MPRO_graph_semantics Mrhs) = true ->
  dlhs ≡ drhs.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros lhs rhs Hlhs Hrhs Qlhs Qrhs HQlhs HQrhs fN a b Mlhs Mrhs HMlhs HMrhs.
  intros HMlr%default_countable_sized_graph_iso_test_correct.


  apply (PRO_quote_correct_graph_semantics _) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics _) in HQrhs as HQrhs'.
  assert (Hlr : (PRO_graph_semantics Qlhs ≡ₛ PRO_graph_semantics Qrhs)%cohg). 1:{
    eapply MPRO_PRO_quote_correct_graph_semantics_mor, HMlr; eauto.
  }
  eapply (DiagramQuote_correct R A); [eauto..|].
  rewrite <- 2 PRO_graph_semantics_correct.
  apply graph_semantics_syntactic_eq.
  rewrite HQlhs', HQrhs'.
  f_equiv.
  apply Hlr.
Qed.


Lemma LawfulMProLike_MPRO_quote_test_correct_casted `{Countable T'}
  (MStruct : Mor (btree positive))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct n m) equiv}
  {SizedProD : SizedProLike MStruct Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct MStruct Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable MStruct Struct T}
  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation MStruct LawPro)
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}


  (f : T' -> T)
  {n m} (dlhs drhs : D n m) :
  forall lhs rhs,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  forall (fN : positive -> nat) 
    a b a' b' (Mlhs : MPRO MStruct T' a b) (Mrhs : MPRO MStruct T' a' b'),
  MPRO_PRO_quote (MStruct:=MStruct) fN Mlhs Qlhs ->
  MPRO_PRO_quote (MStruct:=MStruct) fN Mrhs Qrhs ->
  forall (Ha : a' =@{list _} a) (Hb : b' =@{list _} b),
  default_countable_sized_graph_iso_test (MPRO_graph_semantics Mlhs)
    (cast_sized_graph (bsize_eq_elems Ha) (bsize_eq_elems Hb) 
      (MPRO_graph_semantics Mrhs)) = true ->
  dlhs ≡ drhs.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros lhs rhs Hlhs Hrhs Qlhs Qrhs HQlhs HQrhs fN a b a' b' Mlhs Mrhs HMlhs HMrhs Ha Hb.
  intros HMlr%default_countable_sized_graph_iso_test_correct.


  apply (PRO_quote_correct_graph_semantics _) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics _) in HQrhs as HQrhs'.
  assert (Hlr : (PRO_graph_semantics Qlhs ≡ₛ PRO_graph_semantics Qrhs)%cohg). 1:{
    eapply MPRO_PRO_quote_correct_graph_semantics_mor_casted, HMlr; eauto.
  }
  eapply (DiagramQuote_correct R A); [eauto..|].
  rewrite <- 2 PRO_graph_semantics_correct.
  apply graph_semantics_syntactic_eq.
  rewrite HQlhs', HQrhs'.
  f_equiv.
  apply Hlr.
Qed.

(*

Lemma LawfulProLike_RW_dom_of_Quote
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeSizedStructGraphable Struct,
    LawGraphS : !LawfulSizedStructGraphable Struct T}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d : D n m) p :
  DiagramQuote d p ->
  RW.(pro_rewriting_domain) p.
Proof.
  intros [Hdp%(f_equiv is_Some)].
  now apply Hdp.
Qed.

Lemma LawfulProLike_RW_dom_of_Denote
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeSizedStructGraphable Struct,
    LawGraphS : !LawfulSizedStructGraphable Struct T}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d : D n m) p :
  DiagramDenote d p ->
  RW.(pro_rewriting_domain) p.
Proof.
  intros [Hdp%(f_equiv is_Some)].
  now apply Hdp.
Qed.



Lemma LawfulProLike_equiv_of_RW_Quote
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeSizedStructGraphable Struct,
    LawGraphS : !LawfulSizedStructGraphable Struct T}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d d' : D n m) p p' :
  DiagramQuote d p ->
  DiagramQuote d' p' ->
  RW n m p p' -> d ≡ d'.
Proof.
  intros [Hdp] [Hdp'] (d1 & d1' & [Hd1] & [Hd1'] & Heq).
  rewrite Hd1 in Hdp.
  rewrite Hd1' in Hdp'.
  apply (inj Some) in Hdp, Hdp'.
  rewrite <- Hdp, <- Hdp'; done.
Qed. *)




















Definition MPRO_monog_quote_context_domainb
  {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (valid_tensors : Pset)
  {i j n m}
  (ctx : {k & BWSizedCospanHyperGraph positive T' n (k + i) *
    BWSizedCospanHyperGraph positive T' (k + j) m}%type) :
  bool :=
  default false (
    let '(existT k (GC1, GC2)) := ctx in
    C1 ←@{option} sized_graph_to_term _ _ GC1;
    C2 ← sized_graph_to_term _ _ GC2;
    Some (Pset_subseteqb (MPRO_tensors_set C1 ∪ MPRO_tensors_set C2) valid_tensors)).

Lemma MPRO_monog_quote_context_domainb_correct
  {MStruct Struct T}
  `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)

  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}

  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (Hsized_graph_to_term : forall n m bscohg p, sized_graph_to_term n m bscohg = Some p ->
    MPRO_graph_semantics p ≡ₛ bscohg)
  (valid_tensors : Pset)
  (fN : positive -> nat)
  (f : T' -> T)
  (HfN : forall (i o : btree positive) (mp : MPRO MStruct T' i o),
    MPRO_tensors_set mp ⊆ valid_tensors ->
    RW.(pro_rewriting_domain) (PRO_denote f $ MPRO_to_PRO fN mp))
  {i j n m}
  (ctx : {k & BWSizedCospanHyperGraph positive T' n (k + i) *
    BWSizedCospanHyperGraph positive T' (k + j) m}%type) :
  MPRO_monog_quote_context_domainb RW sized_graph_to_term valid_tensors ctx ->
  forall i' j' lhs rhs, RW i' j' lhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs -> PRO_quote f Qrhs rhs ->
  forall (* bi bj  *)(Mlhs Mrhs : MPRO MStruct T' i j),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->

  forall n' m' (tl tr : PRO Struct T n' m'),
    RW.(pro_rewriting_domain) tl ->
    RW.(pro_rewriting_domain) tr ->
    forall Qtl Qtr,
    PRO_quote f Qtl tl -> PRO_quote f Qtr tr ->
    forall (* bn bm  *)(Mtl Mtr : MPRO MStruct T' n m),
    MPRO_PRO_quote fN Mtl Qtl -> MPRO_PRO_quote fN Mtr Qtr ->
    MPRO_graph_semantics Mtl ≡ₛ make_bw_sized_monog_pushout (MPRO_graph_semantics Mlhs) ctx ->
    MPRO_graph_semantics Mtr ≡ₛ make_bw_sized_monog_pushout (MPRO_graph_semantics Mrhs) ctx ->
    RW n' m' tl tr.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  unfold MPRO_monog_quote_context_domainb.
  destruct ctx as [k [GC1 GC2]].
  destruct (sized_graph_to_term _ _ GC1) as [MC1|] eqn:HMC1; [|done].
  destruct (sized_graph_to_term _ _ GC2) as [MC2|] eqn:HMC2; [|done].
  set (C1 := MPRO_to_PRO fN MC1).
  set (C2 := MPRO_to_PRO fN MC2).

  cbn -[bw_scohg make_bw_sized_monog_pushout].
  rewrite Pset_subseteqb_correct.
  rewrite union_subseteq.
  intros (HdenC1'%HfN & HdenC2'%HfN).


  intros i' j' lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs Mlhs Mrhs HMlhs HMrhs.
  intros n' m' tl tr HRtl HRtr Qtl Qtr HQtl HQtr Mtl Mtr HMtl HMtr Htl Htr.
  apply (PRO_quote_correct_graph_semantics f) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQtl as HQtl'.
  apply (PRO_quote_correct_graph_semantics f) in HQtr as HQtr'.
  apply MPRO_PRO_quote_size in HMtl as Hnm'.
  destruct Hnm' as (-> & ->).
  apply MPRO_PRO_quote_correct_graph_semantics' in HMtl, HMtr.
  (* rewrite MPRO_PRO_quote_refl in HMtl, HMtr.
  subst Qtl Qtr. *)

  apply MPRO_PRO_quote_size in HMlhs as Hij'.
  destruct Hij' as (-> & ->).
  apply MPRO_PRO_quote_correct_graph_semantics' in HMlhs, HMrhs.
  (* rewrite MPRO_PRO_quote_refl in HMlhs, HMrhs.
  subst Qlhs Qrhs. *)

  assert (HC1 : (PRO_graph_semantics C1 ≡ₛ bw_sized_graph_to_graph fN GC1)%cohg). 1:{
    subst C1.
    rewrite <- MPRO_graph_semantics_correct.
    apply bw_sized_graph_to_graph_scohg_syntactic_eq.
    apply Hsized_graph_to_term in HMC1.
    done.
  }

  assert (HC2 : (PRO_graph_semantics C2 ≡ₛ bw_sized_graph_to_graph fN GC2)%cohg). 1:{
    subst C2.
    rewrite <- MPRO_graph_semantics_correct.
    apply bw_sized_graph_to_graph_scohg_syntactic_eq.
    apply Hsized_graph_to_term in HMC2.
    done.
  }

  eapply pro_rewriting_relation_graph_syntax_l with
    ((PRO_denote f C1 ;; Pid (btree_size _ _) * lhs) ;; PRO_denote f C2)%pro; [done|..].
  1: {
    cbn.
    rewrite 2 PRO_graph_semantics_denote.
    rewrite HQlhs'.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- 2 graph_apply_hom_compose_graphs.
    rewrite HQtl'.
    f_equiv.
    apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in Htl.
    rewrite MPRO_graph_semantics_correct in Htl.
    rewrite MPRO_graph_semantics_correct in HMtl.
    rewrite <- HMtl in Htl.
    rewrite Htl.
    cbn [make_bw_sized_monog_pushout].
    rewrite 2 bw_sized_graph_to_graph_compose by apply equiv.

    f_equiv; [f_equiv; [done|]|done].
    rewrite bw_sized_graph_to_graph_stack by apply equiv.
    rewrite bw_sized_graph_to_graph_id by apply equiv.
    f_equiv.
    rewrite MPRO_graph_semantics_correct.
    rewrite MPRO_graph_semantics_correct in HMlhs.
    done.
  }
  eapply pro_rewriting_relation_graph_syntax_r with
    ((PRO_denote f C1 ;; Pid (btree_size _ _) * rhs) ;; PRO_denote f C2)%pro; [done|..].
  2: {
    cbn.
    rewrite 2 PRO_graph_semantics_denote.
    rewrite HQrhs'.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- 2 graph_apply_hom_compose_graphs.
    rewrite HQtr'.
    f_equiv.
    apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in Htr.
    rewrite MPRO_graph_semantics_correct in Htr.
    rewrite MPRO_graph_semantics_correct in HMtr.
    rewrite <- HMtr in Htr.
    rewrite Htr.
    cbn [make_bw_sized_monog_pushout].
    rewrite 2 bw_sized_graph_to_graph_compose by apply equiv.
    f_equiv; [f_equiv; [done|]|done].
    rewrite bw_sized_graph_to_graph_stack.
    rewrite bw_sized_graph_to_graph_id.
    f_equiv.
    rewrite MPRO_graph_semantics_correct.
    rewrite MPRO_graph_semantics_correct in HMrhs.
    done.
  }
  apply pro_rewriting_relation_compose; [|now apply pro_rewriting_relation_refl].
  apply pro_rewriting_relation_compose; [now apply pro_rewriting_relation_refl|].
  apply pro_rewriting_relation_stack; [now apply RW.(LPRR), RW.(LPRR)|].
  done.
Qed.

Definition MPRO_monog_quote_rewrite {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  {MStructG' : @SizedStructGraphable positive MStruct T'}
  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (f : T' -> T)
  {i j} (Mlhs Mrhs : MPRO MStruct T' i j) {n m} (Mtgt : MPRO MStruct T' n m)
  (match_number : nat) : option (MPRO MStruct T' n m) :=
  let valid_tensors := MPRO_tensors_set Mlhs ∪ MPRO_tensors_set Mrhs ∪ MPRO_tensors_set Mtgt in
  let Glhs := MPRO_graph_semantics Mlhs in let Gtgt := MPRO_graph_semantics Mtgt in
  ctx ← select_bw_sized_monog_context Glhs Gtgt match_number;
  if negb (default_countable_sized_graph_iso_test
    Gtgt (make_bw_sized_monog_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (MPRO_monog_quote_context_domainb RW sized_graph_to_term valid_tensors ctx) then None else
  let Grhs := MPRO_graph_semantics Mrhs in
  sized_graph_to_term n m (make_bw_sized_monog_pushout Grhs ctx).



Lemma MPRO_monog_quote_rewrite_correct
  {MStruct Struct T}
  `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)

  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}

  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (Hsized_graph_to_term : forall n m bscohg p, sized_graph_to_term n m bscohg = Some p ->
    MPRO_graph_semantics p ≡ₛ bscohg)

  (f : T' -> T)
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number : nat) :
  pro_rewriting_domain RW tgt ->
  RW i j lhs rhs ->
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall (fN : positive -> nat) bi bj bn bm
    (Mlhs Mrhs : MPRO MStruct T' bi bj) (Mtgt : MPRO MStruct T' bn bm),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->
    MPRO_PRO_quote fN Mtgt Qtgt ->

  forall Mres,
    MPRO_monog_quote_rewrite RW sized_graph_to_term f
      Mlhs Mrhs Mtgt match_number = Some Mres ->

  forall Qres,
  MPRO_PRO_denote fN Mres Qres ->


  forall res, PRO_unquote f Qres res ->
  bool_decide (RW.(pro_rewriting_domain) res) ->
  RW n m tgt res.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Htgt Hlrhs Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt.
  intros fN bi bj bn bm Mlhs Mrhs Mtgt HMlhs HMrhs HMtgt.
  (* intros concr_asgn HfN. *)
  unfold MPRO_monog_quote_rewrite.
  set (Glhs := MPRO_graph_semantics Mlhs).
  set (Grhs := MPRO_graph_semantics Mrhs).
  set (Gtgt := MPRO_graph_semantics Mtgt).
  destruct (select_bw_sized_monog_context _ _ _) as [ctx|]; [|done].
  cbn.
  destruct (default_countable_sized_graph_iso_test_correct' Gtgt
    (make_bw_sized_monog_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (MPRO_monog_quote_context_domainb _ _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (fun HfN => MPRO_monog_quote_context_domainb_correct RW sized_graph_to_term Hsized_graph_to_term
    _ fN f HfN
    ctx (Is_true_true_2 _ Hdom)) as Hpush.
  apply pro_rewriting_relation_to_domain in Hlrhs as Hlrdom.
  destruct Hlrdom as [Hldom Hrdom].
  tspecialize Hpush. 1:{
    intros ins outs mp.
    change (_ ∪ _ ∪ _) with (MPRO_tensors_set (Mlhs * Mrhs * Mtgt)%mpro).
    intros Hmp.
    apply (mpro_rewriting_domain_mono_set_quoted RW f _ _ Hmp fN).
    cbn [MPRO_to_PRO].
    do 2 change (PRO_denote f (?l * ?r)) with (PRO_denote f l * PRO_denote f r)%pro.

    apply pro_rewriting_domain_stack; [apply pro_rewriting_domain_stack|].
    - apply MPRO_PRO_quote_correct_tensors_lists in HMlhs.
      apply PRO_quote_correct_tensors in HQlhs.
      eapply pro_rewriting_domain_mono_inclA, Hldom.
      rewrite <- HQlhs.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
    - apply MPRO_PRO_quote_correct_tensors_lists in HMrhs.
      apply PRO_quote_correct_tensors in HQrhs.
      eapply pro_rewriting_domain_mono_inclA, Hrdom.
      rewrite <- HQrhs.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
    - apply MPRO_PRO_quote_correct_tensors_lists in HMtgt.
      apply PRO_quote_correct_tensors in HQtgt.
      eapply pro_rewriting_domain_mono_inclA, Htgt.
      rewrite <- HQtgt.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
  }
  destruct (sized_graph_to_term _ _ _) as [Mres|] eqn:HMres_eq; [|done].
  intros _ [= <-].
  intros Qres HMres res HQres Hres%bool_decide_spec.
  apply MPRO_PRO_denote_iff_quote in HMres.
  apply (Hpush _ _ lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs Mlhs Mrhs HMlhs HMrhs
    _ _ _ _ Htgt Hres Qtgt Qres HQtgt HQres _ _ _ _).
  - done.
  - apply Hsized_graph_to_term in HMres_eq.
    rewrite HMres_eq.
    done.
Qed.

Lemma LawfulProLike_MPRO_monog_quote_rewrite_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructSymm : forall A, SubStruct MSymmetric (MStruct A)}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MPROP')
  (f : T' -> T)
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m) (match_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->

  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall (fN : positive -> nat) bi bj bn bm
    (Mlhs Mrhs : MPRO (MStruct positive) T' bi bj) (Mtgt : MPRO (MStruct positive) T' bn bm),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->
    MPRO_PRO_quote fN Mtgt Qtgt ->

  forall Mres,
    MPRO_monog_quote_rewrite RW sized_graph_to_term f
      Mlhs Mrhs Mtgt match_number = Some Mres ->

  forall Qres, MPRO_PRO_denote fN Mres Qres ->

  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (MPRO_monog_quote_rewrite_correct
    RW sized_graph_to_term (fun n m => bw_sized_graph_to_MPROP'_correct) f lhs rhs tgt match_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN bi bj bn bm Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt (* concr_asgn HfN *) Mres HMres_eq Qres HMres res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN _ _ _ _ Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt Mres HMres_eq Qres HMres res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.



Lemma LawfulProLike_MPRO_monog_quote_clean_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructSymm : forall A, SubStruct MSymmetric (MStruct A)}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MPROP')
  (f : T' -> T)
  {n m} (dtgt : D n m):
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall fN bn bm Mtgt,
    MPRO_PRO_quote fN Mtgt Qtgt ->
    forall Mres,

    sized_graph_to_term bn bm (MPRO_graph_semantics Mtgt) = Some Mres ->

  forall Qres,
    MPRO_PRO_denote fN Mres Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros tgt Htgt Qtgt HQtgt fN bn bm Mtgt HMtgt Mres HMres_eq Qres HQres res Hres dres Hdres.
  apply bw_sized_graph_to_MPROP'_correct in HMres_eq.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.

  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - eapply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + rewrite HQtgt', HQres'.
      f_equiv.
      apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in HMres_eq.
      apply MPRO_PRO_denote_iff_quote in HQres.
      apply MPRO_PRO_quote_size in HQres as Hnm.
      destruct Hnm as [-> ->].
      apply MPRO_PRO_quote_correct_graph_semantics' in HQres, HMtgt.
      rewrite HMtgt, HQres.
      done.
Qed.









Definition MPRO_quote_context_domainb
  {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (valid_tensors : Pset)
  (f : T' -> T)
  {i j n m}
  (ctx : BWSizedCospanHyperGraph positive T' n ((i + j) + m)) : bool :=
  default false (
    Mctx ←@{option} sized_graph_to_term _ _ ctx;
    Some (Pset_subseteqb (MPRO_tensors_set Mctx) valid_tensors)).

Lemma MPRO_quote_context_domainb_correct
  {MStruct Struct T}
  `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)

  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}
  {StructA : SubStruct Autonomy Struct}
  {StructAG : SubStructGraphable Autonomy Struct T}

  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m -> option (MPRO MStruct T' n m))
  (Hsized_graph_to_term : forall n m bscohg p, sized_graph_to_term n m bscohg = Some p ->
    MPRO_graph_semantics p ≡ₛ bscohg)
  (fN : positive -> nat)
  (f : T' -> T)
  valid_tensors
  (HfN : forall (i o : btree positive) (mp : MPRO MStruct T' i o),
    MPRO_tensors_set mp ⊆ valid_tensors ->
    RW.(pro_rewriting_domain) (PRO_denote f $ MPRO_to_PRO fN mp))
  {i j n m}
  (ctx : BWSizedCospanHyperGraph positive T' n ((i + j) + m)) :
  MPRO_quote_context_domainb RW sized_graph_to_term valid_tensors f ctx ->
  forall i' j' lhs rhs, RW i' j' lhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs -> PRO_quote f Qrhs rhs ->
  forall (* bi bj  *)(Mlhs Mrhs : MPRO MStruct T' i j),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->

  forall n' m' (tl tr : PRO Struct T n' m'),
    RW.(pro_rewriting_domain) tl ->
    RW.(pro_rewriting_domain) tr ->
    forall Qtl Qtr,
    PRO_quote f Qtl tl -> PRO_quote f Qtr tr ->
    forall (* bn bm  *)(Mtl Mtr : MPRO MStruct T' n m),
    MPRO_PRO_quote fN Mtl Qtl -> MPRO_PRO_quote fN Mtr Qtr ->
    MPRO_graph_semantics Mtl ≡ₛ make_bw_sized_pushout (MPRO_graph_semantics Mlhs) ctx ->
    MPRO_graph_semantics Mtr ≡ₛ make_bw_sized_pushout (MPRO_graph_semantics Mrhs) ctx ->
    RW n' m' tl tr.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  unfold MPRO_quote_context_domainb.
  destruct (sized_graph_to_term _ _ ctx) as [Mctx|] eqn:HMctx_eq; [|done].
  set (Pctx := MPRO_to_PRO fN Mctx).

  cbn -[bw_scohg make_bw_sized_pushout].
  rewrite Pset_subseteqb_correct.
  intros Hdenctx%HfN.


  intros i' j' lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs Mlhs Mrhs HMlhs HMrhs.
  intros n' m' tl tr HRtl HRtr Qtl Qtr HQtl HQtr Mtl Mtr HMtl HMtr Htl Htr.
  apply (PRO_quote_correct_graph_semantics f) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQtl as HQtl'.
  apply (PRO_quote_correct_graph_semantics f) in HQtr as HQtr'.
  apply MPRO_PRO_quote_size in HMtl as Hnm'.
  destruct Hnm' as (-> & ->).
  apply MPRO_PRO_quote_correct_graph_semantics' in HMtl, HMtr.
  (* rewrite MPRO_PRO_quote_refl in HMtl, HMtr.
  subst Qtl Qtr. *)

  apply MPRO_PRO_quote_size in HMlhs as Hij'.
  destruct Hij' as (-> & ->).
  apply MPRO_PRO_quote_correct_graph_semantics' in HMlhs, HMrhs.
  (* rewrite MPRO_PRO_quote_refl in HMlhs, HMrhs.
  subst Qlhs Qrhs. *)

  assert (Hctx : (PRO_graph_semantics Pctx ≡ₛ bw_sized_graph_to_graph fN ctx)%cohg). 1:{
    subst Pctx.
    rewrite <- MPRO_graph_semantics_correct.
    apply bw_sized_graph_to_graph_scohg_syntactic_eq.
    apply Hsized_graph_to_term in HMctx_eq.
    done.
  }

  eapply pro_rewriting_relation_graph_syntax_l with
  (PRO_denote f Pctx ;; ((((lhs * Pid (btree_size fN j) ;; Pcap (btree_size fN j))))
      * Pid (btree_size fN m)))%pro; [done|..].
  1:{
    cbn.
    rewrite PRO_graph_semantics_denote.
    rewrite HQlhs'.
    rewrite graph_of_struct_includeStruct.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- (graph_apply_hom_id_graph f (n:=btree_size fN m)).
    cbn.
    rewrite <- (graph_apply_hom_cap_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite HQtl'.
    f_equiv.

    apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in Htl.
    rewrite MPRO_graph_semantics_correct in Htl.
    rewrite MPRO_graph_semantics_correct in HMtl.
    rewrite <- HMtl in Htl.
    rewrite Htl.

    unfold make_bw_sized_pushout.
    rewrite bw_sized_graph_to_graph_lunit_r.
    rewrite bw_sized_graph_to_graph_compose.
    f_equiv; [done|].
    rewrite bw_sized_graph_to_graph_stack, bw_sized_graph_to_graph_compose.
    f_equiv; [|now rewrite bw_sized_graph_to_graph_id].
    f_equiv; [|now rewrite bw_sized_graph_to_graph_cap].
    rewrite bw_sized_graph_to_graph_stack, bw_sized_graph_to_graph_id.
    f_equiv; done.
  }

  eapply pro_rewriting_relation_graph_syntax_r with
    (PRO_denote f Pctx ;; ((((rhs * Pid (btree_size fN j) ;; Pcap (btree_size fN j))))
      * Pid (btree_size fN m)))%pro; [done|..].
  2:{
    cbn.
    rewrite PRO_graph_semantics_denote.
    rewrite HQrhs'.
    rewrite graph_of_struct_includeStruct.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- (graph_apply_hom_id_graph f (n:=btree_size fN m)).
    cbn.
    rewrite <- (graph_apply_hom_cap_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite HQtr'.
    f_equiv.

    apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in Htr.
    rewrite MPRO_graph_semantics_correct in Htr.
    rewrite MPRO_graph_semantics_correct in HMtr.
    rewrite <- HMtr in Htr.
    rewrite Htr.

    unfold make_bw_sized_pushout.
    rewrite bw_sized_graph_to_graph_lunit_r.
    rewrite bw_sized_graph_to_graph_compose.
    f_equiv; [done|].
    rewrite bw_sized_graph_to_graph_stack, bw_sized_graph_to_graph_compose.
    f_equiv; [|now rewrite bw_sized_graph_to_graph_id].
    f_equiv; [|now rewrite bw_sized_graph_to_graph_cap].
    rewrite bw_sized_graph_to_graph_stack, bw_sized_graph_to_graph_id.
    f_equiv; done.
  }
  apply pro_rewriting_relation_compose; [now apply pro_rewriting_relation_refl|].
  apply pro_rewriting_relation_stack; [|now apply RW.(LPRR), RW.(LPRR)].
  apply pro_rewriting_relation_compose; [|now apply RW.(LPRR), RW.(LPRR)].
  apply pro_rewriting_relation_stack; [|now apply RW.(LPRR), RW.(LPRR)].
  done.
Qed.


Definition MPRO_gen_quote_rewrite {MStruct Struct T}
  {MStructG : @SizedStructGraphable positive MStruct T}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}
  {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)
  {MStructG' : @SizedStructGraphable positive MStruct T'}
  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m ->
    option (MPRO MStruct T' n m))
  (select_context : forall i j (lhs : BWSizedCospanHyperGraph positive T' i j)
    n m (tgt : BWSizedCospanHyperGraph positive T' n m), nat -> nat ->
    option (BWSizedCospanHyperGraph positive T' n ((i + j) + m)))
  (f : T' -> T)
  {i j} (Mlhs Mrhs : MPRO MStruct T' i j) {n m} (Mtgt : MPRO MStruct T' n m)
  (match_number quotient_number : nat) : option (MPRO MStruct T' n m) :=
  let valid_tensors := MPRO_tensors_set Mlhs ∪ MPRO_tensors_set Mrhs ∪ MPRO_tensors_set Mtgt in
  let Glhs := MPRO_graph_semantics Mlhs in let Gtgt := MPRO_graph_semantics Mtgt in
  ctx ← select_context _ _ Glhs _ _ Gtgt match_number quotient_number;
  if negb (default_countable_sized_graph_iso_test
    Gtgt (make_bw_sized_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (MPRO_quote_context_domainb RW sized_graph_to_term valid_tensors f ctx) then None else
  let Grhs := MPRO_graph_semantics Mrhs in
  sized_graph_to_term n m (make_bw_sized_pushout Grhs ctx).


Lemma MPRO_gen_quote_rewrite_correct
  {MStruct Struct T}
  `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  {MStructG : forall T, @SizedStructGraphable positive MStruct T}
  {FreeMStructG : FreeSizedStructGraphable MStruct}
  {EqMStruct : forall n m, Equiv (MStruct n m)}
  {MStructI : InterpStruct MStruct Struct}

  `{Countable T'}
  (RW : LawfulMPRORewritingRelation MStruct Struct T)

  {LawGraphM' : LawfulSizedStructGraphable MStruct Struct T'}
  {StructA : SubStruct Autonomy Struct}
  {StructAG : SubStructGraphable Autonomy Struct T}


  (sized_graph_to_term : forall n m, BWSizedCospanHyperGraph positive T' n m ->
    option (MPRO MStruct T' n m))
  (Hsized_graph_to_term : forall n m bscohg p, sized_graph_to_term n m bscohg = Some p ->
    MPRO_graph_semantics p ≡ₛ bscohg)
  (select_context : forall i j (lhs : BWSizedCospanHyperGraph positive T' i j)
    n m (tgt : BWSizedCospanHyperGraph positive T' n m), nat -> nat ->
    option (BWSizedCospanHyperGraph positive T' n ((i + j) + m)))

  (f : T' -> T)
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number quotient_number : nat) :
  pro_rewriting_domain RW tgt ->
  RW i j lhs rhs ->
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall (fN : positive -> nat) bi bj bn bm
    (Mlhs Mrhs : MPRO MStruct T' bi bj) (Mtgt : MPRO MStruct T' bn bm),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->
    MPRO_PRO_quote fN Mtgt Qtgt ->

  forall Mres,
    MPRO_gen_quote_rewrite RW sized_graph_to_term select_context f
      Mlhs Mrhs Mtgt match_number quotient_number = Some Mres ->

  forall Qres,
  MPRO_PRO_denote fN Mres Qres ->


  forall res, PRO_unquote f Qres res ->
  bool_decide (RW.(pro_rewriting_domain) res) ->
  RW n m tgt res.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Htgt Hlrhs Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt.
  intros fN bi bj bn bm Mlhs Mrhs Mtgt HMlhs HMrhs HMtgt.
  (* intros concr_asgn HfN. *)
  unfold MPRO_gen_quote_rewrite.
  set (Glhs := MPRO_graph_semantics Mlhs).
  set (Grhs := MPRO_graph_semantics Mrhs).
  set (Gtgt := MPRO_graph_semantics Mtgt).
  destruct (select_context _ _ _ _ _ _  _ _) as [ctx|]; [|done].
  cbn -[bw_scohg make_bw_sized_pushout].
  destruct (default_countable_sized_graph_iso_test_correct' Gtgt
    (make_bw_sized_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (MPRO_quote_context_domainb _ _ _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (fun HfN => MPRO_quote_context_domainb_correct RW sized_graph_to_term Hsized_graph_to_term
    (* concr_asgn *) fN f _ HfN
    ctx (Is_true_true_2 _ Hdom)) as Hpush.
  
  apply pro_rewriting_relation_to_domain in Hlrhs as Hlrdom.
  destruct Hlrdom as [Hldom Hrdom].
  tspecialize Hpush. 1:{
    intros ins outs mp.
    change (_ ∪ _ ∪ _) with (MPRO_tensors_set (Mlhs * Mrhs * Mtgt)%mpro).
    intros Hmp.
    apply (mpro_rewriting_domain_mono_set_quoted RW f _ _ Hmp fN).
    cbn [MPRO_to_PRO].
    do 2 change (PRO_denote f (?l * ?r)) with (PRO_denote f l * PRO_denote f r)%pro.

    apply pro_rewriting_domain_stack; [apply pro_rewriting_domain_stack|].
    - apply MPRO_PRO_quote_correct_tensors_lists in HMlhs.
      apply PRO_quote_correct_tensors in HQlhs.
      eapply pro_rewriting_domain_mono_inclA, Hldom.
      rewrite <- HQlhs.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
    - apply MPRO_PRO_quote_correct_tensors_lists in HMrhs.
      apply PRO_quote_correct_tensors in HQrhs.
      eapply pro_rewriting_domain_mono_inclA, Hrdom.
      rewrite <- HQrhs.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
    - apply MPRO_PRO_quote_correct_tensors_lists in HMtgt.
      apply PRO_quote_correct_tensors in HQtgt.
      eapply pro_rewriting_domain_mono_inclA, Htgt.
      rewrite <- HQtgt.
      rewrite PRO_tensors_PRO_denote.
      apply (list_fmap_inclA (RA:=prod_relation eq equiv) _).
      rewrite PRO_tensors_MPRO_to_PRO_lists.
      apply PermutationA_inclA.
      done.
  }
  destruct (sized_graph_to_term _ _ _) as [Mres|] eqn:HMres_eq; [|done].
  intros _ [= <-].
  intros Qres HMres res HQres Hres%bool_decide_spec.
  apply MPRO_PRO_denote_iff_quote in HMres.
  apply (Hpush _ _ lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs Mlhs Mrhs HMlhs HMrhs
    _ _ _ _ Htgt Hres Qtgt Qres HQtgt HQres _ _ _ _).
  - done.
  - apply Hsized_graph_to_term in HMres_eq.
    rewrite HMres_eq.
    done.
Qed.

(* FIXME: Move *)
#[export] Instance substruct_msymmetric_of_mmonoidal_msymmetry {A}
  `{!SubStruct (@MMonoidal A) Struct, !SubStruct MSymmetry Struct} :
  SubStruct MSymmetric Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.

#[export] Instance substruct_mautonomous_of_msymmetric_mautonomy {A}
  `{!SubStruct (@MSymmetric A) Struct, !SubStruct MAutonomy Struct} :
  SubStruct MAutonomous Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.

#[export] Instance substruct_mfrobenius_of_mautonomous_mfrobenial {A}
  `{!SubStruct (@MAutonomous A) Struct, !SubStruct MFrobenial Struct} :
  SubStruct MFrobenius Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.



Lemma LawfulProLike_MPRO_bimonog_quote_rewrite_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructAuto : forall A, SubStruct MAutonomous (MStruct A)}
  {StructA : SubStruct Autonomy Struct}
  {StructAG : SubStructGraphable Autonomy Struct T}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MAPROP')
  (select_context : forall i j (lhs : BWSizedCospanHyperGraph positive T' i j)
    n m (tgt : BWSizedCospanHyperGraph positive T' n m), nat -> nat ->
    option (BWSizedCospanHyperGraph positive T' n ((i + j) + m)) :=
    fun _ _ lhs _ _ tgt => select_sized_bimonog_context lhs tgt)

  (f : T' -> T)
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m) (match_number quotient_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->

  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall (fN : positive -> nat) bi bj bn bm
    (Mlhs Mrhs : MPRO (MStruct positive) T' bi bj) (Mtgt : MPRO (MStruct positive) T' bn bm),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->
    MPRO_PRO_quote fN Mtgt Qtgt ->

  forall Mres,
    MPRO_gen_quote_rewrite RW sized_graph_to_term select_context f
      Mlhs Mrhs Mtgt match_number quotient_number = Some Mres ->

  forall Qres, MPRO_PRO_denote fN Mres Qres ->

  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (MPRO_gen_quote_rewrite_correct
    RW sized_graph_to_term (fun n m => bw_sized_graph_to_MAPROP'_correct)
      select_context f lhs rhs tgt match_number quotient_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN bi bj bn bm Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt (* concr_asgn HfN *) Mres HMres_eq Qres HMres res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN _ _ _ _ Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt (* _ HfN *) Mres HMres_eq Qres HMres res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.


Lemma LawfulProLike_MPRO_bimonog_quote_clean_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructAuto : forall A, SubStruct MAutonomous (MStruct A)}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MAPROP')
  (f : T' -> T)
  {n m} (dtgt : D n m):
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall fN bn bm Mtgt,
    MPRO_PRO_quote fN Mtgt Qtgt ->
    forall Mres,

    sized_graph_to_term bn bm (MPRO_graph_semantics Mtgt) = Some Mres ->

  forall Qres,
    MPRO_PRO_denote fN Mres Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros tgt Htgt Qtgt HQtgt fN bn bm Mtgt HMtgt Mres HMres_eq Qres HQres res Hres dres Hdres.
  apply bw_sized_graph_to_MAPROP'_correct in HMres_eq.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.

  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - eapply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + rewrite HQtgt', HQres'.
      f_equiv.
      apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in HMres_eq.
      apply MPRO_PRO_denote_iff_quote in HQres.
      apply MPRO_PRO_quote_size in HQres as Hnm.
      destruct Hnm as [-> ->].
      apply MPRO_PRO_quote_correct_graph_semantics' in HQres, HMtgt.
      rewrite HMtgt, HQres.
      done.
Qed.




Lemma LawfulProLike_MPRO_frobenius_quote_rewrite_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructFrob : forall A, SubStruct MFrobenius (MStruct A)}
  {StructA : SubStruct Autonomy Struct}
  {StructAG : SubStructGraphable Autonomy Struct T}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MFPROP')
  (select_context : forall i j (lhs : BWSizedCospanHyperGraph positive T' i j)
    n m (tgt : BWSizedCospanHyperGraph positive T' n m), nat -> nat ->
    option (BWSizedCospanHyperGraph positive T' n ((i + j) + m)) :=
    fun _ _ lhs _ _ tgt => select_sized_bimonog_context lhs tgt)

  (f : T' -> T)
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m) (match_number quotient_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->

  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall (fN : positive -> nat) bi bj bn bm
    (Mlhs Mrhs : MPRO (MStruct positive) T' bi bj) (Mtgt : MPRO (MStruct positive) T' bn bm),
    MPRO_PRO_quote fN Mlhs Qlhs ->
    MPRO_PRO_quote fN Mrhs Qrhs ->
    MPRO_PRO_quote fN Mtgt Qtgt ->

  forall Mres,
    MPRO_gen_quote_rewrite RW sized_graph_to_term select_context f
      Mlhs Mrhs Mtgt match_number quotient_number = Some Mres ->

  forall Qres, MPRO_PRO_denote fN Mres Qres ->

  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (MPRO_gen_quote_rewrite_correct
    RW sized_graph_to_term (fun n m => bw_sized_graph_to_MFPROP'_correct)
      select_context f lhs rhs tgt match_number quotient_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN bi bj bn bm Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt (* concr_asgn HfN *) Mres HMres_eq Qres HMres res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt fN _ _ _ _ Mlhs Mrhs Mtgt
    HMlhs HMrhs HMtgt (* _ HfN *) Mres HMres_eq Qres HMres res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.


Lemma LawfulProLike_MPRO_frobenius_quote_clean_correct `{Countable T'}
  (MStruct : forall A, Mor (btree A))
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : SummableOver R A, EQA : EqDecision A, 
    LSA : !LawfulSummableOver R A, WFA : !WFSummableOver R A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {EqT : Equiv T} {EquivT : @Equivalence T equiv}
  {EqMStruct : forall n m, Equiv (MStruct positive n m)}
  {EqStruct : forall n m, Equiv (Struct n m)}
  {EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {EquivMStruct : forall n m, @Equivalence (MStruct positive n m) equiv}
  {SizedProD : SizedProLike (MStruct positive) Struct T D}
  (ProD : ProLike Struct T D := SizedProD.(SPL_PL))
  (MStructI : InterpStruct (MStruct positive) Struct := SizedProD.(SPL_interp))
  {MStructG : forall T, @SizedStructGraphable positive (MStruct positive) T}
  {FreeMStructG : FreeSizedStructGraphable (MStruct positive)}
  {MStructRes : ResizableStruct MStruct}
  {StructG : forall T, StructGraphable Struct T}
  {FreeStructG : FreeStructGraphable Struct}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
    {LawGraphS : LawfulStructGraphable Struct T}
  {LawGraphM : LawfulSizedStructGraphable (MStruct positive) Struct T}
  {LawGraphM' : LawfulSizedStructGraphable (MStruct positive) Struct T'}
  (RW : LawfulMPRORewritingRelation (MStruct positive) Struct T :=
    LawfulProLike_LawfulMPRORewritingRelation (MStruct positive) LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{MStructFrob : forall A, SubStruct MFrobenius (MStruct A)}
  (* `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct} *)
  (sized_graph_to_term : forall n m,
    BWSizedCospanHyperGraph positive T' n m -> option (MPRO (MStruct positive) T' n m)
    := fun n m => bw_sized_graph_to_MFPROP')
  (f : T' -> T)
  {n m} (dtgt : D n m):
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall fN bn bm Mtgt,
    MPRO_PRO_quote fN Mtgt Qtgt ->
    forall Mres,

    sized_graph_to_term bn bm (MPRO_graph_semantics Mtgt) = Some Mres ->

  forall Qres,
    MPRO_PRO_denote fN Mres Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros tgt Htgt Qtgt HQtgt fN bn bm Mtgt HMtgt Mres HMres_eq Qres HQres res Hres dres Hdres.
  apply bw_sized_graph_to_MFPROP'_correct in HMres_eq.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.

  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - eapply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + rewrite HQtgt', HQres'.
      f_equiv.
      apply (bw_sized_graph_to_graph_scohg_syntactic_eq fN) in HMres_eq.
      apply MPRO_PRO_denote_iff_quote in HQres.
      apply MPRO_PRO_quote_size in HQres as Hnm.
      destruct Hnm as [-> ->].
      apply MPRO_PRO_quote_correct_graph_semantics' in HQres, HMtgt.
      rewrite HMtgt, HQres.
      done.
Qed.



