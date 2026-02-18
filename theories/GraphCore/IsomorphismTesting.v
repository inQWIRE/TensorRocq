Require Export TensorGraph IsomorphismTestingAux.

Definition hyperedge_map_eq_reqs {T} (hg hg' : Pmap (HyperEdge T)) :
  option (list (T * T)) :=
  (* if decide (map_relation (λ _ tio tio' =>
    (tio.1.2 = tio'.1.2 /\ tio.2 = tio'.2)) (λ _, False) (λ _, False) hg hg')
    then
    map_to_list (merge (fun mt mt' =>
      )) *)
  join_list (map_to_list (merge (fun mt mt' =>
    Some ('(t, ins, outs) ← mt;
      '(t', ins', outs') ← mt';
      if decide (ins = ins' /\ outs = outs') then
        Some (t, t')
      else
        None
    )) hg hg')).*2.

Lemma hyperedge_map_eq_reqs_correct_1 {T} (hg hg' : Pmap (HyperEdge T)) ts :
  hyperedge_map_eq_reqs hg hg' = Some ts ->
  Forall (uncurry eq) ts ->
  hg = hg'.
Proof.
  intros Heq Hts.
  apply map_eq.
  intros i.
  apply option_eq.
  unfold hyperedge_map_eq_reqs in Heq.
  rewrite join_list_Some in Heq.
  set (m := merge _ _ _) in Heq.
  intros tio.
  destruct (m !! i) as [mi|] eqn:Hmi.
  + assert (Hmi_in : mi ∈ (map_to_list m).*2). 1:{
      rewrite elem_of_list_fmap.
      exists (i, mi).
      split; [done|].
      now rewrite elem_of_map_to_list.
    }
    pose proof Hmi_in as Hmi_ts.
    rewrite Heq in Hmi_ts.
    apply elem_of_list_fmap in Hmi_ts as Hmits.
    destruct Hmits as ((tl, tr) & -> & Htlr).
    unfold m in Hmi.
    rewrite lookup_merge in Hmi.
    destruct (hg !! i) as [[[t ins] outs]|] eqn:Hgi,
      (hg' !! i) as [[[t' ins'] outs']|] eqn:Hg'i; cbn in Hmi;
    [|exfalso; done..].
    revert Hmi.
    intros [= Hmi].
    case_decide as Hparts; [|done].
    f_equiv.
    f_equal.
    f_equal; [|easy].
    f_equal; [|easy].
    revert Hmi.
    intros [= <- <-].
    rewrite Forall_forall in Hts.
    apply Hts in Htlr.
    apply Htlr.
  + unfold m in Hmi.
    rewrite lookup_merge in Hmi.
    destruct (hg !! i), (hg' !! i); [done..|].
    easy.
Qed.

Lemma hyperedge_map_eq_reqs_correct {T} (hg hg' : Pmap (HyperEdge T)) :
  (exists ts, hyperedge_map_eq_reqs hg hg' = Some ts /\
  Forall (uncurry eq) ts) <->
  hg = hg'.
Proof.
  split; [intros (?&?&?); eauto using hyperedge_map_eq_reqs_correct_1|].
  intros <-.
  unfold hyperedge_map_eq_reqs.
  rewrite merge_diag.
  exists ((λ a, (a.2.1.1, a.2.1.1)) <$> map_to_list hg).
  split; [|rewrite Forall_fmap, Forall_forall; done].
  apply join_list_Some.
  rewrite (omap_ext _ (λ a, Some (Some (a.1.1, a.1.1)))). 2: {
    intros _ [[t ins] outs] _.
    cbn.
    now rewrite decide_True.
  }
  rewrite <- map_fmap_alt.
  rewrite map_to_list_fmap.
  rewrite snds_prod_map, <- 2 list_fmap_compose.
  done.
Qed.




Definition graph_eq_reqs {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  option (list (T * T)) :=
  if decide (cohg.(inputs) = cohg'.(inputs) /\ cohg.(outputs) = cohg'.(outputs)
    /\ cohg.(hedges).(hypervertices) = cohg'.(hedges).(hypervertices)) then
    hyperedge_map_eq_reqs cohg.(hedges).(hyperedges) cohg'.(hedges).(hyperedges)
  else
    None.

Lemma graph_eq_reqs_correct {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  (exists ts, graph_eq_reqs cohg cohg' = Some ts /\
    Forall (uncurry eq) ts) <->
  cohg = cohg'.
Proof.
  destruct cohg as [[hg hv] ins outs], cohg' as [[hg' hv'] ins' outs'].
  unfold graph_eq_reqs.
  cbn.
  case_decide as Haux.
  - rewrite hyperedge_map_eq_reqs_correct.
    split; [intros ->; now repeat f_equal|].
    congruence.
  - naive_solver.
Qed.



Fixpoint hyperedge_map_pre_isos_extending_aux {T}
  (hg hg' : list (positive * (HyperEdge T)))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T * T) * Pmap positive * Pmap positive) :=
  match hg with
  | [] => match hg' with | [] => [ts_mhe_mv] | _::_ => [] end
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, length (k_tio.2.1.2) = length ins /\
      length (k_tio.2.2) = length outs) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← extend_posmap_one k k_tio.1 ts_mhe_mv.1.2;
        mv' ← extend_posmap (zip (ins ++ outs) (k_tio.2.1.2 ++ k_tio.2.2))
          ts_mhe_mv.2;
        Some (hyperedge_map_pre_isos_extending_aux hg hg'rest
         ((t, k_tio.2.1.1) :: ts_mhe_mv.1.1, mhe', mv')))
  end.

Definition hyperedge_map_pre_isos_extending {T} (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T*T) * Pmap positive * Pmap positive) :=
  hyperedge_map_pre_isos_extending_aux (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.

Definition graph_pre_isos {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  list (list (T * T) * Pmap positive * Pmap positive) :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    default []
      (mv ← extend_posmap (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
      Some
      (hyperedge_map_pre_isos_extending cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) ([], ∅, mv)))
  else
    [].

Definition graph_iso_conditions {T n m}
  (cohg cohg' : CospanHyperGraph T n m) : list (list (T * T)) :=
  omap (λ '(ts, _, mv),
    if decide (size mv = size (map_img mv :> Pset)) then
      Some ts
    else None) (graph_pre_isos cohg cohg').

Lemma hyperedge_map_pre_isos_extending_aux_correct {T} hg hg' ts_mhe_mv :
  Forall (λ '(ts, mhe, mv),
    ts_mhe_mv.1.1 `suffix_of` ts /\
    ts_mhe_mv.1.2 ⊆ mhe /\
    ts_mhe_mv.2 ⊆ mv /\
    dom mhe = dom ts_mhe_mv.1.2 ∪ list_to_set hg.*1 /\
    dom mv = dom ts_mhe_mv.2 ∪ ⋃ (abs_vertices <$> hg.*2) /\
    map_img mv = map_img ts_mhe_mv.2 ∪ ⋃ (abs_vertices <$> hg'.*2) /\
    exists hg'', hg' ≡ₚ hg'' /\
    Forall2 (λ '(k, (t, ins, outs)) '(k', (t', ins', outs')),
      (t, t') ∈ ts /\
      mhe !! k = Some k' /\
      (mv !!.) <$> ins = Some <$> ins' /\
      (mv !!.) <$> outs = Some <$> outs') hg hg''
    ) (@hyperedge_map_pre_isos_extending_aux T hg hg' ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv;
  induction hg as [|[k [[t ins] outs]] hg IHhg]; intros hg' tg_mhe_mv.
  1:{
    cbn.
    destruct hg'; [|constructor].
    apply Forall_singleton.
    destruct tg_mhe_mv as [[tg mhe] mv].
    cbn.
    do 3 (split; [done|]).
    do 3 (split; [now rewrite union_empty_r_L|]).
    exists [].
    split; [done|].
    constructor.
  }
  cbn -[union].
  rewrite Forall_bind.
  rewrite Forall_forall.
  intros ((k' & [[t' ins'] outs']) & hg'rest)
    [[Hlenin Hlenout] Hperm]%elem_of_list_select_perm_Prop.
  cbn -[union] in *.
  destruct (extend_posmap_one _ _ _) as [mhe'|] eqn:Hmhe'; [cbn -[union]|done].
  destruct (extend_posmap _ _) as [mv'|] eqn:Hmv'; [cbn -[union]|done].
  eapply Forall_impl; [apply IHhg|].
  intros [[ts mhe] mv].
  cbn -[union].
  intros (Hts & Hmhe & Hmv & Hdom_mhe & Hdom_mv & Himg_mv & Hex).
  apply extend_posmap_one_Some in Hmhe'.
  apply extend_posmap_Some in Hmv'.
  split_and!.
  - rewrite <- Hts.
    now apply suffix_cons_r.
  - now rewrite Hmhe'.1.
  - now rewrite Hmv'.1.
  - rewrite Hdom_mhe, Hmhe'.2.2.
    symmetry; apply union_assoc_L.
  - rewrite Hdom_mv, Hmv'.2.2.1.
    rewrite fst_zip by now rewrite ?length_app; lia.
    symmetry; apply union_assoc_L.
  - rewrite Himg_mv, Hmv'.2.2.2.
    rewrite snd_zip by now rewrite ?length_app; lia.
    rewrite Hperm.
    cbn -[union].
    symmetry; apply union_assoc_L.
  - destruct Hex as (hg'' & Hhg''perm & Halls).
    exists ((k', (t', ins', outs')) :: hg'').
    split; [now rewrite Hperm, Hhg''perm|].
    constructor; [|done].
    split; [revert Hts; apply elem_of_suffix; left|].
    split; [revert Hmhe; apply lookup_weaken, Hmhe'.2.1|].
    pose proof Hmv'.2.1 as Hall2.
    rewrite zip_with_app in Hall2 by now rewrite ?length_app; lia.
    apply Forall_app in Hall2 as [Hins Houts].
    rewrite Forall_zip_with in Hins, Houts by easy.
    cbn in Hins, Houts.
    split; apply list_eq_Forall2, Forall2_fmap;
    [eapply Forall2_impl; [apply Hins|]|
      eapply Forall2_impl; [apply Houts|]];
    intros; revert Hmv;
    now apply lookup_weaken.
Qed.


(* Lemma hyperedge_map_pre_isos_extending_aux_correct' {T} hg hg' ts_mhe_mv :
  Forall (λ '(ts, mhe, mv),
    ts_mhe_mv.1.1 `suffix_of` ts /\
    ts_mhe_mv.1.2 ⊆ mhe /\
    ts_mhe_mv.2 ⊆ mv /\
    exists hg'', hg' ≡ₚ hg'' /\
    Forall2 (λ '(k, (t, ins, outs)) '(k', (t', ins', outs')),
      (t, t') ∈ ts /\
      mhe !! k = Some k' /\
      (mv !!.) <$> ins = Some <$> ins' /\
      (mv !!.) <$> outs = Some <$> outs') hg hg''
    ) (@hyperedge_map_pre_isos_extending_aux T hg hg' ts_mhe_mv). *)



Lemma hyperedge_map_pre_isos_extending_correct {T} (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  Forall (λ '(ts, mhe, mv),
    ts_mhe_mv.1.1 `suffix_of` ts /\
    ts_mhe_mv.1.2 ⊆ mhe /\
    ts_mhe_mv.2 ⊆ mv /\
    dom mhe = dom ts_mhe_mv.1.2 ∪ dom hg /\
    ((forall i j a, ts_mhe_mv.1.2 !! i = Some a ->
      ts_mhe_mv.1.2 !! j = Some a -> i = j) ->
     (forall i j a, ts_mhe_mv.1.2 !! i = Some a ->
      mhe !! j = Some a -> False) ->
      (forall i j a, mhe !! i = Some a -> mhe !! j = Some a -> i = j)) /\
    dom mv =
      dom ts_mhe_mv.2 ∪ ⋃ (abs_vertices <$> (map_to_list hg).*2) /\
    map_img mv =
      map_img ts_mhe_mv.2 ∪ ⋃ (abs_vertices <$> (map_to_list hg').*2) /\
    map_relation (λ _ '(t', ins', outs') '(t, ins, outs),
      (t, t') ∈ ts /\
      ins = ins' /\ outs = outs') (λ _ _, False) (λ _ _, False)
        (relabel_abs Some <$> hg')
        (relabel_abs (mv !!.) <$> kmap (Pmap_map mhe) hg))
  (hyperedge_map_pre_isos_extending hg hg' ts_mhe_mv).
Proof.
  eapply Forall_impl; [apply hyperedge_map_pre_isos_extending_aux_correct|].
  intros [[ts mhe] mv].
  cbn.
  intros (Hts & Hmhe & Hmv & Hdom_mhe & Hdom_mv & Himg_mv & Hex).
  do 3 (split; [done|]).
  split_and!.
  - rewrite Hdom_mhe.
    f_equal.
    symmetry.
    unfold_leibniz.
    apply dom_alt.
  - assert (Hmhe_ks : (mhe !!.) <$> (map_to_list hg).*1 ≡ₚ
      Some <$> (map_to_list hg').*1). 1:{
      destruct Hex as (hg'' & -> & Halls).
      apply eq_reflexivity.
      apply list_eq_Forall2, Forall2_fmap, Forall2_fmap.
      eapply Forall2_impl; [apply Halls|].
      intros (k, [[t ins] outs]) (k', [[t' ins'] outs']).
      cbn.
      easy.
    }
    assert (Hdup : NoDup ((mhe !!.) <$> (map_to_list hg).*1)). 1:{
      rewrite Hmhe_ks, (NoDup_fmap _).
      apply NoDup_fst_map_to_list.
    }
    specialize (NoDup_fmap_1_strong _ _ Hdup) as Hdup'.
    intros Hinj Hdisj i j a Hi Hj.
    specialize (Hinj i j a).
    specialize (Hdisj i j a) as Hij.
    specialize (Hdisj j i a) as Hji.
    apply elem_of_dom_2 in Hi as Hidom.
    apply elem_of_dom_2 in Hj as Hjdom.
    rewrite Hdom_mhe, elem_of_union, <- dom_alt, 2 elem_of_dom in Hidom, Hjdom.
    pose proof (fun i a H => lookup_weaken _ _ i a H Hmhe) as Hlook.
    specialize (Hlook i) as Hli.
    specialize (Hlook j) as Hlj.
    destruct Hidom as [[? Hi']|[]]; [apply Hlook in Hi' as Hi''|];
    (destruct Hjdom as [[? Hj']|[]]; [apply Hlook in Hj' as Hj''|]);
     [naive_solver|exfalso;
      eapply Hdisj; eauto..|].
    apply Hdup'; [..|congruence];
    rewrite <- (elem_of_list_to_set (C:=Pset)), <- dom_alt, elem_of_dom;
    unfold is_Some; eauto.
  - done.
  - done.
  - destruct Hex as (hg'' & Hhg''perm & Halls).
    rewrite <- (list_to_map_to_list hg').
    erewrite list_to_map_proper by
      first [eassumption|apply NoDup_fst_map_to_list].
    rewrite <- list_to_map_fmap.
    rewrite <- kmap_fmap'.
    unfold kmap.
    apply map_relation_list_to_map.
    rewrite Forall2_fmap.
    rewrite map_to_list_fmap.
    rewrite Forall2_fmap_r.
    unfold compose, prod_map; cbn.
    apply Forall2_flip.
    apply (Forall2_impl _ _ _ _ Halls).
    intros [k [[t ins] outs]] [k' [[t' ins'] outs']].
    cbn.
    intros (Htt' & Hkk' & Hins & Houts).
    split_and!; try done.
    symmetry.
    unfold Pmap_map.
    now rewrite Hkk'.
Qed.


Lemma graph_pre_isos_correct_aux {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    size (isolated_vertices cohg) = size (isolated_vertices cohg') /\
    dom mhe = dom cohg.(hedges).(hyperedges) /\
    (forall i j a, mhe !! i = Some a -> mhe !! j = Some a -> i = j) /\
    dom mv = referrenced_vertices cohg /\
    map_img mv = referrenced_vertices cohg' /\
    map_relation (λ _ '(t', ins', outs') '(t, ins, outs),
      (t, t') ∈ ts /\
      ins = ins' /\ outs = outs') (λ _ _, False) (λ _ _, False)
        (relabel_abs Some <$> cohg'.(hedges).(hyperedges))
        (relabel_abs (mv !!.) <$> kmap (Pmap_map mhe)
          cohg.(hedges).(hyperedges)) /\
    (mv !!.) <$> vec_to_list cohg.(inputs) = Some <$> vec_to_list cohg'.(inputs) /\
    (mv !!.) <$> vec_to_list cohg.(outputs) = Some <$> vec_to_list cohg'.(outputs)
    )
    (graph_pre_isos cohg cohg').
Proof.
  unfold graph_pre_isos.
  case_decide as Hsize; [|easy].
  destruct (extend_posmap _ _) as [mvi|] eqn:Hmvi; [|easy].
  cbn.
  eapply Forall_impl; [apply hyperedge_map_pre_isos_extending_correct|].
  intros [[ts mhe] mv].
  cbn.
  intros (_ & _ & Hmvi_mv & Hdom_mhe & Hinj & Hdom_mv & Himg_mv & Hrel).
  apply extend_posmap_Some in Hmvi as (_ & Hallio & Hdom_mvi & Himg_mvi).
  rewrite dom_empty_L, union_empty_l_L in Hdom_mhe, Hdom_mvi.
  rewrite map_img_empty_L, union_empty_l_L in Himg_mvi.
  rewrite fst_zip in Hdom_mvi by now rewrite 2 length_app, 4 length_vec_to_list.
  rewrite snd_zip in Himg_mvi by now rewrite 2 length_app, 4 length_vec_to_list.
  split; [done|].
  split; [done|].
  split; [apply Hinj; intros ???; now rewrite lookup_empty|].
  split; [rewrite Hdom_mv, Hdom_mvi;
    unfold referrenced_vertices; f_equal;
    rewrite list_to_set_bind_L, <- list_fmap_compose; done|].
  split; [rewrite Himg_mv, Himg_mvi;
    unfold referrenced_vertices; f_equal;
    rewrite list_to_set_bind_L, <- list_fmap_compose; done|].
  split; [done|].
  pose proof Hallio as Hall2.
  rewrite zip_with_app in Hall2 by now rewrite ?length_app, ?length_vec_to_list.
  apply Forall_app in Hall2 as [Hins Houts].
  rewrite Forall_zip_with in Hins, Houts by now rewrite ?length_vec_to_list.
  cbn in Hins, Houts.
  split; apply list_eq_Forall2, Forall2_fmap;
  [eapply Forall2_impl; [apply Hins|]|
    eapply Forall2_impl; [apply Houts|]];
  intros; revert Hmvi_mv;
  now apply lookup_weaken.
Qed.



Lemma graph_pre_isos_correct {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    Forall (uncurry eq) ts ->
    size (dom mv :> Pset) = size (map_img mv :> Pset) ->
    isomorphic (norm_verts cohg) (norm_verts cohg'))
    (graph_pre_isos cohg cohg').
Proof.
  eapply Forall_impl; [apply graph_pre_isos_correct_aux|].
  intros [[ts mhe] mv].
  intros (Hisol & Hdom_mhe & Hmhe_inj & Hdom_mv & Himg_mv & Heq & Hins & Houts)
    Hts Hsize.

  pose proof Hsize as Hinj.
  rewrite map_dom_img_eq_card_iff_inj in Hinj.
  apply size_set_eq_exists_map in Hisol as
    (misol & Hdom_misol%leibniz_equiv_iff &
      Himg_misol%leibniz_equiv_iff & Hmisol_inj).
  assert (Hdisj : misol ##ₘ mv). 1:{
    apply map_disjoint_dom.
    rewrite Hdom_misol, Hdom_mv.
    apply isolated_referrenced_disjoint.
  }
  eapply (isomorphic_of_partial_inj_dom' _ _
    (Pmap_map (misol ∪ mv)) (Pmap_map mhe)).
  - apply Pmap_map_inj_on.
    1:{
      rewrite dom_union.
      rewrite Hdom_misol, Hdom_mv.
      now rewrite vertices_norm_verts, vertices_decomp.
    }
    apply map_disjoint_union_inj.
    * done.
    * apply Hmisol_inj.
    * apply Hinj.
    * intros i j a Hi Hj.
      apply (elem_of_map_img_2 (SA:=Pset)) in Hi.
      rewrite Himg_misol in Hi.
      apply (elem_of_map_img_2 (SA:=Pset)) in Hj.
      rewrite Himg_mv in Hj.
      revert Hi Hj.
      apply isolated_referrenced_disjoint.
  - apply Pmap_map_inj_on; [now rewrite Hdom_mhe|].
    apply Hmhe_inj.
  - symmetry.
    apply cohg_ext; cbn; cycle 1.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Hins.
      rewrite 2 list_lookup_fmap in Hins.
      destruct ((vec_to_list (inputs cohg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (inputs cohg')) !! i) as [ii'|] eqn:Hii'; [|done].
      intros [= <-] [= <-].
      cbn in Hins |- *.
      revert Hins.
      intros [= Hmv_ii].
      unfold Pmap_map.
      eapply lookup_union_Some_r in Hmv_ii as Hun_ii; [|eauto].
      now rewrite Hun_ii.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Houts.
      rewrite 2 list_lookup_fmap in Houts.
      destruct ((vec_to_list (outputs cohg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (outputs cohg')) !! i) as [ii'|] eqn:Hii'; [|done].
      intros [= <-] [= <-].
      cbn in Houts |- *.
      revert Houts.
      intros [= Hmv_ii].
      unfold Pmap_map.
      eapply lookup_union_Some_r in Hmv_ii as Hun_ii; [|eauto].
      now rewrite Hun_ii.
    + apply hg_ext. 2:{
        cbn.
        rewrite <- Himg_misol.
        apply set_eq.
        intros k.
        rewrite elem_of_map, elem_of_map_img.
        unfold Pmap_map.
        split.
        - intros (i & -> & Hi).
          exists i.
          rewrite <- Hdom_misol, elem_of_dom in Hi.
          destruct Hi as [mi_i Hmi_i].
          rewrite lookup_union, Hmi_i.
          now rewrite union_Some_l.
        - intros (i & Hi).
          exists i.
          rewrite lookup_union, Hi.
          rewrite union_Some_l.
          rewrite <- Hdom_misol.
          now apply elem_of_dom_2 in Hi.
      }
      cbn.
      transitivity ((relabel_abs (Pmap_map mv) <$>
          kmap (Pmap_map mhe) (hedges cohg).(hyperedges)) :> Pmap _).
      1: {
        apply map_fmap_ext; intros fi tio (i & Hi & <-)%lookup_kmap_Some_2.
        apply relabel_abs_ext_strong.
        intros k Hk.
        unfold Pmap_map.
        rewrite lookup_union.
        enough (misol !! k = None) as -> by now rewrite (left_id_L None _).
        apply not_elem_of_dom.
        rewrite Hdom_misol.
        intros Href%isolated_referrenced_disjoint; apply Href.
        unfold referrenced_vertices.
        apply elem_of_union; right.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        exists (i, tio).
        split; [apply Hk|].
        now apply elem_of_map_to_list.
      }
      apply map_eq; intros i.
      specialize (Heq i).
      cbn in Heq.
      rewrite 2 lookup_fmap in Heq.
      rewrite lookup_fmap.
      destruct (_ !! _) as [tio'|], (_ !! _) as [tio|];
        cbn in Heq; [|easy..].
      destruct tio' as [[t' ins'] outs'],
        tio as [[t ins] outs].
      cbn.
      f_equal.
      cbn in Heq.
      destruct Heq as (Htt' & Hins' & Houts').
      f_equal; [f_equal|].
      * rewrite Forall_forall in Hts.
        apply (Hts _ Htt').
      * apply (list_eq_same_length _ _ _ eq_refl);
        [rewrite length_fmap; now apply (f_equal length) in Hins';
        rewrite 2 length_fmap in Hins'|].
        intros k a b Hk.
        rewrite list_lookup_fmap.
        apply (f_equal (.!! k)) in Hins'.
        rewrite 2 list_lookup_fmap in Hins'.
        destruct (ins !! k) as [ik|] eqn:Hik; [|done].
        destruct (ins' !! k) as [i'k|] eqn:Hi'k; [|done].
        cbn.
        intros [= <-] [= <-].
        cbn in Hins'.
        revert Hins'.
        unfold Pmap_map.
        now intros [= ->].
      * apply (list_eq_same_length _ _ _ eq_refl);
        [rewrite length_fmap; now apply (f_equal length) in Houts';
        rewrite 2 length_fmap in Houts'|].
        intros k a b Hk.
        rewrite list_lookup_fmap.
        apply (f_equal (.!! k)) in Houts'.
        rewrite 2 list_lookup_fmap in Houts'.
        destruct (outs !! k) as [ik|] eqn:Hik; [|done].
        destruct (outs' !! k) as [i'k|] eqn:Hi'k; [|done].
        cbn.
        intros [= <-] [= <-].
        cbn in Houts'.
        revert Houts'.
        unfold Pmap_map.
        now intros [= ->].
Qed.


Lemma graph_pre_isos_correct' `{Equiv T} {n m} (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    Forall (uncurry equiv) ts ->
    size (dom mv :> Pset) = size (map_img mv :> Pset) ->
    norm_verts cohg ≡ norm_verts cohg')
    (graph_pre_isos cohg cohg').
Proof.
  eapply Forall_impl; [apply graph_pre_isos_correct_aux|].
  intros [[ts mhe] mv].
  intros (Hisol & Hdom_mhe & Hmhe_inj & Hdom_mv & Himg_mv & Heq & Hins & Houts)
    Hts Hsize.

  pose proof Hsize as Hinj.
  rewrite map_dom_img_eq_card_iff_inj in Hinj.
  apply size_set_eq_exists_map in Hisol as
    (misol & Hdom_misol%leibniz_equiv_iff &
      Himg_misol%leibniz_equiv_iff & Hmisol_inj).
  assert (Hdisj : misol ##ₘ mv). 1:{
    apply map_disjoint_dom.
    rewrite Hdom_misol, Hdom_mv.
    apply isolated_referrenced_disjoint.
  }
  etransitivity; [
  eapply rtc_once, or_introl, (isomorphic_of_partial_inj_dom' _ _
    (Pmap_map (misol ∪ mv)) (Pmap_map mhe)), eq_refl|].
  - apply Pmap_map_inj_on.
    1:{
      rewrite dom_union.
      rewrite Hdom_misol, Hdom_mv.
      now rewrite vertices_norm_verts, vertices_decomp.
    }
    apply map_disjoint_union_inj.
    * done.
    * apply Hmisol_inj.
    * apply Hinj.
    * intros i j a Hi Hj.
      apply (elem_of_map_img_2 (SA:=Pset)) in Hi.
      rewrite Himg_misol in Hi.
      apply (elem_of_map_img_2 (SA:=Pset)) in Hj.
      rewrite Himg_mv in Hj.
      revert Hi Hj.
      apply isolated_referrenced_disjoint.
  - apply Pmap_map_inj_on; [now rewrite Hdom_mhe|].
    apply Hmhe_inj.
  - apply rtc_once, or_intror.
    apply mk_cohg_eq; cbn.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Hins.
      rewrite 2 list_lookup_fmap in Hins.
      destruct ((vec_to_list (inputs cohg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (inputs cohg')) !! i) as [ii'|] eqn:Hii'; [|done].
      intros [= <-] [= <-].
      cbn in Hins |- *.
      revert Hins.
      intros [= Hmv_ii].
      unfold Pmap_map.
      eapply lookup_union_Some_r in Hmv_ii as Hun_ii; [|eauto].
      now rewrite Hun_ii.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Houts.
      rewrite 2 list_lookup_fmap in Houts.
      destruct ((vec_to_list (outputs cohg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (outputs cohg')) !! i) as [ii'|] eqn:Hii'; [|done].
      intros [= <-] [= <-].
      cbn in Houts |- *.
      revert Houts.
      intros [= Hmv_ii].
      unfold Pmap_map.
      eapply lookup_union_Some_r in Hmv_ii as Hun_ii; [|eauto].
      now rewrite Hun_ii.
    + split. 2:{
        cbn.
        rewrite <- Himg_misol.
        apply set_eq.
        intros k.
        rewrite elem_of_map, elem_of_map_img.
        unfold Pmap_map.
        split.
        - intros (i & -> & Hi).
          exists i.
          rewrite <- Hdom_misol, elem_of_dom in Hi.
          destruct Hi as [mi_i Hmi_i].
          rewrite lookup_union, Hmi_i.
          now rewrite union_Some_l.
        - intros (i & Hi).
          exists i.
          rewrite lookup_union, Hi.
          rewrite union_Some_l.
          rewrite <- Hdom_misol.
          now apply elem_of_dom_2 in Hi.
      }
      cbn.
      replace (_ <$> _) with ((relabel_abs (Pmap_map mv) <$>
          kmap (Pmap_map mhe) (hedges cohg).(hyperedges)) :> Pmap _).
      2: {
        symmetry.
        apply map_fmap_ext; intros fi tio (i & Hi & <-)%lookup_kmap_Some_2.
        apply relabel_abs_ext_strong.
        intros k Hk.
        unfold Pmap_map.
        rewrite lookup_union.
        enough (misol !! k = None) as -> by now rewrite (left_id_L None _).
        apply not_elem_of_dom.
        rewrite Hdom_misol.
        intros Href%isolated_referrenced_disjoint; apply Href.
        unfold referrenced_vertices.
        apply elem_of_union; right.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        exists (i, tio).
        split; [apply Hk|].
        now apply elem_of_map_to_list.
      }
      intros i.
      specialize (Heq i).
      cbn in Heq.
      rewrite 2 lookup_fmap in Heq.
      rewrite lookup_fmap.
      apply option_relation_Forall2.
      destruct (_ !! _) as [tio'|], (_ !! _) as [tio|];
        cbn in Heq; [|easy..].
      destruct tio' as [[t' ins'] outs'],
        tio as [[t ins] outs].
      cbn.
      cbn in Heq.
      destruct Heq as (Htt' & Hins' & Houts').
      split; [split|]; cbn.
      * rewrite Forall_forall in Hts.
        apply (Hts _ Htt').
      * apply (list_eq_same_length _ _ _ eq_refl);
        [rewrite length_fmap; now apply (f_equal length) in Hins';
        rewrite 2 length_fmap in Hins'|].
        intros k a b Hk.
        rewrite list_lookup_fmap.
        apply (f_equal (.!! k)) in Hins'.
        rewrite 2 list_lookup_fmap in Hins'.
        destruct (ins !! k) as [ik|] eqn:Hik; [|done].
        destruct (ins' !! k) as [i'k|] eqn:Hi'k; [|done].
        cbn.
        intros [= <-] [= <-].
        cbn in Hins'.
        revert Hins'.
        unfold Pmap_map.
        now intros [= ->].
      * apply (list_eq_same_length _ _ _ eq_refl);
        [rewrite length_fmap; now apply (f_equal length) in Houts';
        rewrite 2 length_fmap in Houts'|].
        intros k a b Hk.
        rewrite list_lookup_fmap.
        apply (f_equal (.!! k)) in Houts'.
        rewrite 2 list_lookup_fmap in Houts'.
        destruct (outs !! k) as [ik|] eqn:Hik; [|done].
        destruct (outs' !! k) as [i'k|] eqn:Hi'k; [|done].
        cbn.
        intros [= <-] [= <-].
        cbn in Houts'.
        revert Houts'.
        unfold Pmap_map.
        now intros [= ->].
Qed.

Lemma graph_iso_conditions_correct_aux {T n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ ts, ts.*1 = ts.*2 ->
    isomorphic (norm_verts cohg) (norm_verts cohg'))
    (graph_iso_conditions cohg cohg').
Proof.
  rewrite Forall_forall.
  intros ts ([[ts' mhe'] mv'] & Htms & Hts)%elem_of_list_omap.
  case_decide as Hsize; [|done].
  revert Hts.
  intros [= ->].
  pose proof (graph_pre_isos_correct cohg cohg') as Hall.
  rewrite Forall_forall in Hall.
  specialize (Hall _ Htms).
  cbn in Hall.
  intros Heq.
  apply Hall.
  - rewrite <- zip_fst_snd.
    rewrite Forall_zip_with by now rewrite 2 length_fmap.
    cbn.
    now apply list_eq_Forall2 in Heq.
  - now rewrite size_dom.
Qed.


Lemma graph_iso_conditions_correct {T n m}
  (cohg cohg' : CospanHyperGraph T n m) i :
  match (graph_iso_conditions cohg cohg' !! i) with
  | None => False
  | Some ts => ts.*1 = ts.*2
  end ->
  isomorphic (norm_verts cohg) (norm_verts cohg').
Proof.
  case_match eqn:Hmi; [|done].
  apply elem_of_list_lookup_2 in Hmi.
  revert Hmi.
  refine ((Forall_forall (λ ts, ts.*1 = ts.*2 -> _) _).1 _ _).
  apply graph_iso_conditions_correct_aux.
Qed.



Fixpoint hyperedge_map_pre_isos_extending_aux_alt {T}
  (hg hg' : list (positive * (HyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  list (list (T * T) * Piso * Piso) :=
  match hg with
  | [] => match hg' with | [] => [ts_mhe_mv] | _::_ => [] end
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, length (k_tio.2.1.2) = length ins /\
      length (k_tio.2.2) = length outs) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← pupdate k k_tio.1 ts_mhe_mv.1.2;
        mv' ← pupdates (zip (ins ++ outs) (k_tio.2.1.2 ++ k_tio.2.2))
          ts_mhe_mv.2;
        Some (hyperedge_map_pre_isos_extending_aux_alt hg hg'rest
         ((t, k_tio.2.1.1) :: ts_mhe_mv.1.1, mhe', mv')))
  end.

Definition hyperedge_map_pre_isos_extending_alt {T} (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  list (list (T*T) * Piso * Piso) :=
  hyperedge_map_pre_isos_extending_aux_alt (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.

Definition graph_pre_isos_alt {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  list (list (T * T) * Piso * Piso) :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    default []
      (mv ← pupdates (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
      Some
      (hyperedge_map_pre_isos_extending_alt cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) ([], ∅, mv)))
  else
    [].




Lemma hyperedge_map_pre_isos_extending_aux_alt_correct {T}
  (hg hg' : list (positive * (HyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
    hyperedge_map_pre_isos_extending_aux_alt hg hg' ts_mhe_mv
    ⊆ hyperedge_map_pre_isos_extending_aux hg hg'
    ((prod_map (prod_map id Piso_map) Piso_map) ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv; induction hg as [|[k [[t i] o]] hg IHhg];
    intros hg' ts_mhe_mv; [destruct hg'; done|].
  cbn.
  rewrite list_bind_fmap.
  apply list_bind_mono_r.
  intros [k' tio'] ([Hi Ho] & Hhg')%elem_of_list_select_perm_Prop.
  unfold prod_map at 7 8.
  cbn.
  destruct (pupdate k k'.1 ts_mhe_mv.1.2) as [mhe'|] eqn:Hmhe';
    [|now apply list_subseteq_nil].
  apply extend_posmap_one_Piso_map' in Hmhe' as Hmhe''.
  rewrite Hmhe''.
  cbn.
  destruct (pupdates (zip (i ++ o) (k'.2.1.2 ++ k'.2.2)) ts_mhe_mv.2)
    as [mv'|] eqn:Hmv'; [|now apply list_subseteq_nil].
  apply extend_posmap_Piso_map in Hmv' as Hmv''.
  unfold prod_map at 5 6.
  cbn.
  rewrite Hmv''.
  apply IHhg.
Qed.

Lemma hyperedge_map_pre_isos_extending_alt_correct {T}
  (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
    hyperedge_map_pre_isos_extending_alt hg hg' ts_mhe_mv
    ⊆ hyperedge_map_pre_isos_extending hg hg'
    ((prod_map (prod_map id Piso_map) Piso_map) ts_mhe_mv).
Proof.
  apply hyperedge_map_pre_isos_extending_aux_alt_correct.
Qed.

Lemma graph_pre_isos_alt_correct {T n m} (cohg cohg' : CospanHyperGraph T n m) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
  graph_pre_isos_alt cohg cohg' ⊆
  graph_pre_isos cohg cohg'.
Proof.
  unfold graph_pre_isos_alt, graph_pre_isos.
  case_decide; [|done].
  destruct (pupdates _ ∅) as [mio|] eqn:Hmio; [|apply list_subseteq_nil].
  apply extend_posmap_Piso_map in Hmio as Hmio'.
  change (Piso_map ∅) with (∅ :> Pmap positive) in Hmio'.
  rewrite Hmio'.
  cbn.
  apply hyperedge_map_pre_isos_extending_alt_correct.
Qed.

Section dec_equiv.

Context `{Equiv T, !RelDecision (≡@{T})}.

Fixpoint hyperedge_map_isos_extending_aux
  (hg hg' : list (positive * (HyperEdge T)))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => match hg' with | [] => [mhe_mv] | _::_ => [] end
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, t ≡ k_tio.2.1.1 /\
      length (k_tio.2.1.2) = length ins /\
      length (k_tio.2.2) = length outs) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← pupdate k k_tio.1 mhe_mv.1;
        mv' ← pupdates (zip (ins ++ outs) (k_tio.2.1.2 ++ k_tio.2.2))
          mhe_mv.2;
        Some (hyperedge_map_isos_extending_aux hg hg'rest
         (mhe', mv')))
  end.


Definition hyperedge_map_isos_extending
  (hg hg' : Pmap (HyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  hyperedge_map_isos_extending_aux (map_to_list hg)
    (map_to_list hg') mhe_mv.

Definition graph_isos {n m} (cohg cohg' : CospanHyperGraph T n m) :
  list (Piso * Piso) :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    default []
      (mv ← pupdates (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
      Some
      (hyperedge_map_isos_extending cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) (∅, mv)))
  else
    [].

Lemma hyperedge_map_isos_extending_aux_correct
  (hg hg' : list (positive * (HyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  Forall (uncurry equiv) ts_mhe_mv.1.1 ->
  hyperedge_map_isos_extending_aux hg hg' (ts_mhe_mv.1.2, ts_mhe_mv.2)
    ⊆ (λ tev, (tev.1.2, tev.2)) <$>
      (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ hyperedge_map_pre_isos_extending_aux_alt hg hg' ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv; induction hg as [|[k [[t i] o]] hg IHhg];
    intros hg' ts_mhe_mv; [intros Hts; cbn;
    destruct hg'; [|done]; cbn; now rewrite decide_True by done|].
  intros Hts.
  cbn.
  rewrite list_filter_bind.
  rewrite list_bind_fmap.
  unfold compose.
  rewrite list_select_and.
  rewrite list_bind_filter.
  apply list_bind_mono_r.
  intros [k' tio'] ([Hi Ho] & Hhg')%elem_of_list_select_perm_Prop.
  cbn.
  case_decide as Htt'; [|apply list_subseteq_nil].

  (* unfold prod_map at 7 8.
  cbn. *)
  destruct (pupdate k k'.1 ts_mhe_mv.1.2) as [mhe'|] eqn:Hmhe';
    [|now apply list_subseteq_nil].
  cbn.
  destruct (pupdates (zip (i ++ o) (k'.2.1.2 ++ k'.2.2)) ts_mhe_mv.2)
    as [mv'|] eqn:Hmv'; [|now apply list_subseteq_nil].
  cbn.
  apply (IHhg _ ((t, k'.2.1.1) :: ts_mhe_mv.1.1, mhe', mv')).
  constructor; [done|].
  auto.
Qed.


Lemma hyperedge_map_isos_extending_correct
  (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  Forall (uncurry equiv) ts_mhe_mv.1.1 ->
  hyperedge_map_isos_extending hg hg' (ts_mhe_mv.1.2, ts_mhe_mv.2)
    ⊆ (λ tev, (tev.1.2, tev.2)) <$>
      (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ hyperedge_map_pre_isos_extending_alt hg hg' ts_mhe_mv).
Proof.
  apply hyperedge_map_isos_extending_aux_correct.
Qed.

Lemma graph_isos_correct_aux {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  graph_isos cohg cohg' ⊆
  (λ tev, (tev.1.2, tev.2)) <$> (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ graph_pre_isos_alt cohg cohg').
Proof.
  unfold graph_isos, graph_pre_isos_alt.
  case_decide; [|apply list_subseteq_nil].
  destruct (pupdates _ ∅) as [mio|] eqn:Hmio; [|done].
  cbn.
  apply (hyperedge_map_isos_extending_correct _ _ ([], ∅, mio)).
  done.
Qed.


Lemma graph_isos_correct_aux_2 {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ '(mhe, mv),
    (norm_verts cohg) ≡ (norm_verts cohg'))
    (graph_isos cohg cohg').
Proof.
  rewrite Forall_forall.
  intros (mhe, mv) (((ts & _) & _) & [= <- <-] &
    [Hts Hin]%elem_of_list_filter)%graph_isos_correct_aux%elem_of_list_fmap.
  specialize (graph_pre_isos_alt_correct cohg cohg') as Hsub.
  specialize (Hsub _ (elem_of_list_fmap_1 _ _ _ Hin)).
  cbn in Hsub.
  specialize (graph_pre_isos_correct' cohg cohg') as Hcorr.
  rewrite Forall_forall in Hcorr.
  specialize (Hcorr _ Hsub).
  cbn in Hcorr.
  specialize (Hcorr Hts).
  now specialize (Hcorr (map_inverses_card_img _ _ (Piso_inverses mv))).
Qed.

Lemma graph_isos_test {n m} (cohg cohg' : CospanHyperGraph T n m) :
  match graph_isos cohg cohg' with
  | [] => False
  | _ :: _ => True
  end -> norm_verts cohg ≡ norm_verts cohg'.
Proof.
  pose proof (graph_isos_correct_aux_2 cohg cohg') as Hcorr.
  destruct (graph_isos _ _); [done|].
  rewrite Forall_cons in Hcorr.
  case_match.
  intros; apply Hcorr.
Qed.

Definition graph_iso_partial_test {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma graph_iso_partial_test_correct {n m} (cohg cohg' : CospanHyperGraph T n m) : 
  graph_iso_partial_test cohg cohg' = true -> 
  norm_verts cohg ≡ norm_verts cohg'.
Proof.
  intros Heq.
  apply graph_isos_test.
  revert Heq.
  unfold graph_iso_partial_test.
  now case_match.
Qed.

End dec_equiv.
