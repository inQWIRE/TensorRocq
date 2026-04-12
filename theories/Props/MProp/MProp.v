From TensorRocq Require Export Monoid.
From TensorRocq Require Import AProp.
From TensorRocq Require Import SizedGraph.ToUnsized.

(* FIXME: Move *)
#[export] Instance sum_decomp_MonoidSize `{MD : Monoid M mO madd meq,
  FMD : !FreeMonoid M X} (f : X -> nat) :
  MonoidSize (λ m : M, sum_list_with f (mdecomp m)).
Proof.
  split.
  - change (Proper ?R _) with (Proper R (sum_list_with f ∘ mdecomp)).
    apply _.
  - now rewrite mdecomp_mO.
  - intros n m.
    now rewrite mdecomp_madd, sum_list_with_app.
Qed.


Inductive MProp `{MD : Monoid M mO madd meq}
  {T : Type} : M -> M -> Type :=
  | Mid n : MProp n n
  | Mswap n m : MProp (madd n m) (madd m n)
  | Mcup n : MProp mO (madd n n)
  | Mcap n : MProp (madd n n) mO
  | Mcompose {n m o} (mp1 : MProp n m) (mp2 : MProp m o) : MProp n o
  | Mstack {n1 m1 n2 m2}
    (mp1 : MProp n1 m1) (mp2 : MProp n2 m2) : MProp (madd n1 n2) (madd m1 m2)
  | Massoc n m : meq n m -> MProp n m
  | Mgen (t : T) n m : MProp n m.

#[global] Arguments MProp _ {_ _ _ _} _ _ _ : assert.

Fixpoint MProp_to_AProp `{MD : Monoid M mO madd meq, f : M -> nat,
  MS : !MonoidSize f} {T} {n m : M}
  (mp : MProp M T n m) : AProp T (f n) (f m) :=
  match mp with
  | Mid n => Aid _
  | Mswap n m => cast_aprop' (msize_add n m) (msize_add m n) (Aswap (f n) (f m))
  | Mcup n => cast_aprop' msize_mO (msize_add n n) (Acup (f n))
  | Mcap n => cast_aprop' (msize_add n n) msize_mO (Acap (f n))
  | Mcompose mp1 mp2 =>
      Acompose (MProp_to_AProp mp1) (MProp_to_AProp mp2)
  | Mstack mp1 mp2 =>
      cast_aprop' (msize_add (_ :> M) _) (msize_add (_ :> M) _) (Astack
        (MProp_to_AProp mp1) (MProp_to_AProp mp2))
  | Massoc n m Hnm => cast_aprop eq_refl (msize_proper n m Hnm) (Aid _)
  | Mgen t n m => Agen t _ _
  end.




Fixpoint MProp_sized_graph_semantics `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} {a b : M} (mp : MProp M T a b) : SizedCospanHyperGraph X T (length (mdecomp a)) (length (mdecomp b)) :=
  match mp with
  | Mid n => id_sized_graph (list_to_vec (mdecomp n))
  | Mswap n m =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n m)) (length_app _ _)))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd m n)) (length_app _ _)))
      (swap_sized_graph (list_to_vec (mdecomp n)) (list_to_vec (mdecomp m)))
    (* cast_aprop' (msize_add n m) (msize_add m n) (Aswap (f n) (f m)) *)
  | Mcup n =>
    cast_sized_graph
      (eq_sym (f_equal length mdecomp_mO))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n n)) (length_app _ _)))
      (cup_sized_graph (list_to_vec (mdecomp n)))
  | Mcap n =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n n)) (length_app _ _)))
      (eq_sym (f_equal length mdecomp_mO))
      (cap_sized_graph (list_to_vec (mdecomp n)))

  | Mcompose mp1 mp2 =>
    compose_sized_graphs (MProp_sized_graph_semantics mp1)
      (MProp_sized_graph_semantics mp2)
  | Mstack mp1 mp2 =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd _ _)) (length_app _ _)))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd _ _)) (length_app _ _)))

      (stack_sized_graphs (MProp_sized_graph_semantics mp1)
        (MProp_sized_graph_semantics mp2))
  | Massoc n m Hnm => cast_sized_graph eq_refl
    (f_equal length (mdecomp_proper n m Hnm)) (id_sized_graph (list_to_vec (mdecomp n)))
  | Mgen t n m =>
    sized_graph_of_tensor t (list_to_vec (mdecomp n)) (list_to_vec (mdecomp m))
  end.


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



Lemma MProp_sized_graph_semantics_correct_aux `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} (f : X -> nat) {a b : M} (mp : MProp M T a b) :
  well_sized (MProp_sized_graph_semantics mp) /\
  sized_inputs (MProp_sized_graph_semantics mp) = Some <$> mdecomp a /\
  sized_outputs (MProp_sized_graph_semantics mp) = Some <$> mdecomp b /\
  (sized_graph_to_graph f (MProp_sized_graph_semantics mp) [≡ᵢ]ₛ
  AProp_graph_semantics (MProp_to_AProp (MS:=sum_decomp_MonoidSize f) mp))%cohg.
Proof.
  induction mp;
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
  - rewrite sized_graph_to_graph_id_sized_graph'.
    rewrite sized_inputs_id_sized_graph, sized_outputs_id_sized_graph.
    split; [apply well_sized_id_sized_graph|now rewrite vec_to_list_to_vec].
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_swap_sized_graph, sized_outputs_swap_sized_graph.
    split; [apply well_sized_swap_sized_graph|].
    rewrite 2 vec_to_list_to_vec, 2 mdecomp_madd.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_swap_sized_graph).
    now rewrite 2 vec_to_list_to_vec.
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_cup_sized_graph, sized_outputs_cup_sized_graph.
    split; [apply well_sized_cup_sized_graph|].
    rewrite vec_to_list_to_vec, mdecomp_madd, mdecomp_mO.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_cup_sized_graph).
    now rewrite vec_to_list_to_vec.
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_cap_sized_graph, sized_outputs_cap_sized_graph.
    split; [apply well_sized_cap_sized_graph|].
    rewrite vec_to_list_to_vec, mdecomp_madd, mdecomp_mO.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_cap_sized_graph).
    now rewrite vec_to_list_to_vec.
  - destruct IHmp1 as (Hws1 & Hins1 & Houts1 & Hiso1).
    destruct IHmp2 as (Hws2 & Hins2 & Houts2 & Hiso2).
    rewrite sized_inputs_compose_sized_graphs,
      sized_outputs_compose_sized_graphs by assumption + congruence.
    split; [apply well_sized_compose_sized_graphs; assumption + congruence|].
    split_and!; [assumption..|].
    destruct (sized_graph_to_graph_compose_graphs f
    (MProp_sized_graph_semantics mp1) (MProp_sized_graph_semantics mp2)) as (? & Heq).
    1:{
      unfold sized_inputs, sized_outputs in *.
      congruence.
    }
    rewrite Heq.
    symmetry in Hiso1, Hiso2.
    apply sigT2_relation_alt in Hiso1, Hiso2.
    destruct Hiso1 as (Hisoeq1 & Hiso1).
    destruct Hiso2 as (Hisoeq2 & Hiso2).
    etransitivity. 2:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply compose_graphs_struct_isomorphic;
      eassumption.
    }
    cbn [projT2 graph_to_pair_bundled].
    unfold eq_rect_r.
    rewrite 2 cast_pair_to_cast_graph.
    apply eq_reflexivity.
    apply compose_graphs_bundled_eq; now rewrite ?graph_to_pair_bundled_cast.
  - destruct IHmp1 as (Hws1 & Hins1 & Houts1 & Hiso1).
    destruct IHmp2 as (Hws2 & Hins2 & Houts2 & Hiso2).
    rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_stack_sized_graphs, sized_outputs_stack_sized_graphs.
    split; [apply well_sized_stack_sized_graphs; assumption|].
    split_and!; [rewrite mdecomp_madd, fmap_app; f_equal; done..|].
    rewrite sized_graph_to_graph_stack_graphs.
    refine (sigT2_relation_f_equiv_2 _ _ _
      (@stack_graphs T) _ _ Hiso1 _ _ Hiso2).
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_id_sized_graph, sized_outputs_id_sized_graph.
    split_and!; [apply well_sized_id_sized_graph|try now rewrite vec_to_list_to_vec|
      rewrite vec_to_list_to_vec; f_equal; now apply mdecomp_proper|].
    rewrite sized_graph_to_graph_id_sized_graph'.
    now rewrite vec_to_list_to_vec.
  - split; [apply well_sized_sized_graph_of_tensor|].
    rewrite sized_inputs_sized_graph_of_tensor,
      sized_outputs_sized_graph_of_tensor.
    split_and!; [now rewrite vec_to_list_to_vec..|].
    rewrite sized_graph_to_graph_sized_graph_of_tensor'.
    now rewrite 2 vec_to_list_to_vec.
Qed.




Lemma MProp_sized_graph_semantics_correct `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} (f : X -> nat) {a b : M} (mp : MProp M T a b) :
  (sized_graph_to_graph f (MProp_sized_graph_semantics mp) [≡ᵢ]ₛ
  AProp_graph_semantics (MProp_to_AProp (MS:=sum_decomp_MonoidSize f) mp))%cohg.
Proof.
  apply MProp_sized_graph_semantics_correct_aux.
Qed.

Lemma by_sigT2_relation {A B} `{forall ab : A * B, ProofIrrel (ab = ab)}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b))
  {a b} (x y : P a b) :
  sigT2_relation R (existT (a, b) x) (existT (a, b) y) ->
  R a b x y.
Proof.
  rewrite sigT2_relation_alt.
  cbn.
  intros (Hab & HR).
  now rewrite (proof_irrel Hab eq_refl) in HR.
Qed.


Declare Scope mprop_scope.
Bind Scope mprop_scope with MProp.
Delimit Scope mprop_scope with mprop.


Notation "x * y" := (Mstack x%mprop y%mprop)
  (at level 40, left associativity) : mprop_scope.

Notation "x ;' y" := (Mcompose x%mprop y%mprop)
  (at level 50, left associativity) : mprop_scope.

Notation Massoc' H := (Massoc _ _ H) (only parsing).

Close Scope aprop_scope.
Open Scope mprop_scope.



Section perms.

Context `{MD : Monoid M mO madd meq}.

Notation "0" := mO.
Notation "x '==' y" := (meq x y) (at level 70).
Infix "+" := madd.

(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Meq_equivalence : Equivalence meq := meq_equivalence.
Local Existing Instance Meq_equivalence.

Let Madd_proper : Proper (meq ==> meq ==> meq) madd := madd_proper.
Local Existing Instance Madd_proper.

Open Scope mprop_scope.

Definition cast_mprop {T} {n m n' m' : M}
  (Hn : n == n') (Hm : m == m') (mp : MProp M T n m) : MProp M T n' m' :=
  Mcompose (Massoc' (symmetry Hn)) $ Mcompose mp $ Massoc' Hm.

Notation cast_mprop' Hn Hm mp :=
  (cast_mprop (meq_equivalence.(Equivalence_Symmetric) _ _ Hn)
    (meq_equivalence.(Equivalence_Symmetric) _ _ Hm) mp) (only parsing).


Definition mtop_to_bottom {T} (ls : list M) :
  MProp M T (Mlist_sum ls) (Mlist_sum (tail ls) + Mlist_sum (option_list (head ls))) :=
  match ls with
  | [] => Massoc' (symmetry (madd_0_l 0))
  | a :: ls =>
    Mcompose (Mswap a (Mlist_sum ls))
      (Massoc (Mlist_sum ls + a) (Mlist_sum ls + (a + 0))
      (madd_proper (Mlist_sum ls) (Mlist_sum ls) (reflexivity (Mlist_sum ls))
      a (a + 0) (symmetry (MD.(madd_0_r) a))))
  end.

(*
Definition abottom_to_top {T} (n : nat) : MProp M T n n :=
  match n with
  | 0 => Aid 0
  | S n =>
    cast_aprop (Nat.add_comm n 1) eq_refl (Aswap n 1)
  end.

Definition aprop_aswap {T} (n : nat) : MProp M T n n :=
  match n with
  | 0 => Aid 0
  | 1 => Aid _
  | 2 => Aswap 1 1
  | S n =>
    cast_aprop (Nat.add_comm n 1) eq_refl
      (Acompose (Aswap n 1) (Astack (Aid 1) (atop_to_bottom n)))
  end.





Lemma Apad_prf {a n} (H : a < n) : a + (n - a) = n.
Proof. lia. Qed.

Definition Apad {T a} (ap : MProp M T a a) n : MProp M T n n :=
  match decide (a = n) with
  | left Han => cast_aprop Han Han ap
  | right _ =>
    match Nat.lt_dec a n with
    | left Han => cast_aprop (Apad_prf Han) (Apad_prf Han) (Astack ap (Aid (n - a)))
    | right _ => Aid _
    end
  end.


Definition ocast_aprop {T n m n' m'} (ap : MProp M T n m) : option (MProp M T n' m') :=
  match decide (n = n' /\ m = m') with
  | left Hnm => Some (cast_aprop Hnm.1 Hnm.2 ap)
  | right _ => None
  end.

Definition Apad_nonsquare {T a b} (ap : MProp M T a b) n m :
  option (MProp M T n m) :=
  match decide (a = n /\ b = m) with
  | left Heq => Some (cast_aprop Heq.1 Heq.2 ap)
  | right _ =>
    ocast_aprop (Astack ap (Aid (n - a)))
  end.

Lemma Apad_nonsquare_l_prf1 {a b n} (Han : a = n) : b = n + b - a.
Proof.
  lia.
Qed.

Lemma Apad_nonsquare_l_prf2 {a b n} (Han : a < n) : b + (n - a) = n + b - a.
Proof.
  lia.
Qed.

Definition Apad_nonsquare_l {T a b} (ap : MProp M T a b) n :
  option (MProp M T n (n + b - a)) :=
  match decide (a = n) with
  | left Han => Some $ cast_aprop Han (Apad_nonsquare_l_prf1 Han) ap
  | right _ =>
    match decide (a < n) with
    | left Han => Some $ cast_aprop (Apad_prf Han)
      (Apad_nonsquare_l_prf2 Han) (Astack ap (Aid (n - a)))
    | right _ => None
    end
  end.

Definition aprop_to_top {T} (a n : nat) : MProp M T n n :=
  Apad (abottom_to_top (S a `min` n)) n. *)


(* FIXME: Move *)
Lemma lookup_list_decomps_aux {A} (pre l : list A) k :
  list_decomps_aux pre l !! k =
  (λ a, (pre ++ take k l, a, drop (S k) l)) <$> l !! k.
Proof.
  revert k pre; induction l; intros k pre; [now destruct k|].
  cbn.
  destruct k as [|k]; [cbn; now rewrite app_nil_r, drop_0|].
  cbn.
  rewrite IHl.
  destruct (l !! k); [|done].
  cbn.
  now rewrite <- app_assoc.
Qed.
Lemma lookup_list_decomps {A} (l : list A) k :
  list_decomps l !! k =
  (λ a, (take k l, a, drop (S k) l)) <$> l !! k.
Proof.
  unfold list_decomps.
  rewrite lookup_list_decomps_aux.
  done.
Qed.
Lemma lookup_list_removals {A} (l : list A) k :
  list_removals l !! k =
  (., take k l ++ drop (S k) l) <$> l !! k.
Proof.
  unfold list_removals.
  rewrite list_lookup_fmap, lookup_list_decomps.
  rewrite <- option_fmap_compose.
  done.
Qed.



(* Definition list_to_front {A} (ns : list A) (a : nat) : list ns :=
  match list_removals ns !! a with
  | None => ns
  | Some  *)

(* Lemma false : False.
Proof. admit. Admitted. *)

Definition Mswapa {T} (a b c : M) : MProp M T (a + (b + c)) (b + (a + c)) :=
  (cast_mprop' ((MD.(madd_assoc) a b c))
    ((MD.(madd_assoc) b a c)) (Mstack (Mswap a b) (Mid c))).

Definition mprop_to_top {T n} (i : fin n) : forall (v : vec M n), MProp M T (Mlist_sum v)
  (Mlist_sum (v !!! i ::: vremove i v)) :=
  Fin.t_rect (fun n i => forall v : vec M n,
  MProp M T (Mlist_sum v) (Mlist_sum (v !!! i ::: vremove i v)))
  (λ n, vec_S_inv (λ v, MProp M T (Mlist_sum v)
    (Mlist_sum (v !!! (0%fin :> fin (S n)) ::: vremove 0%fin v)))
     (λ x v, (Mid (x + Mlist_sum v) :>
     MProp M T (Mlist_sum (x ::: v))
    (Mlist_sum ((x ::: v) !!! 0%fin ::: vremove 0 (x ::: v))))))
  (fun n i => match i with
    | 0%fin => fun _ => vec_S_inv _ (λ a : M, vec_S_inv _ (λ b v,
      Mswapa a b (Mlist_sum v)))
    | FS i' => fun IH =>
      vec_S_inv _ (λ a v,
      Mcompose (Mstack (Mid a) (IH v))
        (Mswapa _ _ _))
    end) n i.


Definition mprop_to_top' {T n} (i : fin n) (v : vec M n) : MProp M T (Mlist_sum' v)
  (Mlist_sum' (v !!! i ::: vremove i v)) :=
  cast_mprop' (Mlist_sum'_correct _) (Mlist_sum'_correct _)
  (mprop_to_top i v).



Fixpoint apply_sw {A n} (ns : vec A n) (l : list nat) {struct n} : vec A n :=
  match n with
  | 0 => fun ns => ns
  | S n => fun ns =>
    if decide (n <= 1) then
      match n as n return vec A (S n) -> vec A (S n) with
      | 1 => fun ns => if decide (head l = Some 1) then [# vhd (vtl ns) ; vhd ns] else ns
      | _ => fun ns => ns
      end ns
    else
      match l with
      | [] => ns
      | a :: l =>
        match decide (a < S n) with
        | right _ => ns
        | left Ha => ns !!! (nat_to_fin Ha) :::
          apply_sw (vremove (nat_to_fin Ha) ns)
          ((λ k, if decide (a < k) then Nat.pred k else k) <$> l)
        end
      end
  end ns.


Fixpoint mprop_of_sw {T n} (ns : vec M n) (l : list nat) :
  MProp M T (Mlist_sum ns) (Mlist_sum (apply_sw ns l)).
  refine (
    match n as n return forall ns : vec M n, MProp M T (Mlist_sum ns) (Mlist_sum (apply_sw ns l)) with
    | 0 => fun ns => Mid (Mlist_sum ns)
    | S n => fun ns => _
    end ns).
  cbn.
  case_decide as Hn.
  - refine (match n with
    | 1 => _
    | _ => _
    end ns).
    + intros; apply Mid.
    + case_decide; [|intros; apply Mid].
      refine (vec_S_inv _ _).
      intros a.
      refine (vec_S_inv _ _).
      intros b.
      refine (vec_0_inv _ _).
      cbn.
      apply Mswapa.
    + intros; apply Mid.
  - destruct l as [|a l]; [apply Mid|].
    case_decide as Ha; [|apply Mid].
    refine (Mcompose (mprop_to_top (nat_to_fin Ha) ns) _).
    cbn [vec_to_list Mlist_sum].
    refine (Mstack (Mid _) _).
    apply mprop_of_sw.
Defined.


Definition Mocompose `{!RelDecision meq} {T n m m' o} 
  (mp1 : MProp M T n m) (mp2 : MProp M T m' o) : 
  option (MProp M T n o) :=
  match decide (m == m') with 
  | right _ => None
  | left Heq => Some (Mcompose mp1 (Mcompose (Massoc' Heq) mp2))
  end.

Definition ocast_mprop_r `{!RelDecision meq} {T n m} m' 
  (mp : MProp M T n m) : option (MProp M T n m') :=
  match decide (m == m') with 
  | right _ => None
  | left Heq => Some (Mcompose mp (Massoc' Heq))
  end.

Definition ocast_mprop_l `{!RelDecision meq} {T n m} n' 
  (mp : MProp M T n m) : option (MProp M T n' m) :=
  match decide (n' == n) with 
  | right _ => None
  | left Heq => Some (Mcompose (Massoc' Heq) mp)
  end.

Definition ocast_mprop `{!RelDecision meq} {T n m} n' m'
  (mp : MProp M T n m) : option (MProp M T n' m') :=
  ocast_mprop_r m' mp ≫= ocast_mprop_l n'.

End perms.