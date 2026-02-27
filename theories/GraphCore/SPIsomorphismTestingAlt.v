Require Export SPTensorGraph IsomorphismTestingAux.


Definition sphyperedge_map_eq_reqs {T} (hg hg' : Pmap (SPHyperEdge T)) :
  option (list (T * T)) :=
  (* if decide (map_relation (λ _ tio tio' =>
    (tio.1.2 = tio'.1.2 /\ tio.2 = tio'.2)) (λ _, False) (λ _, False) hg hg')
    then
    map_to_list (merge (fun mt mt' =>
      )) *)
  join_list (map_to_list (merge (fun mt mt' =>
    Some ('(t, v) ← mt;
      '(t', v') ← mt';
      if decide (v = v') then
        Some (t, t')
      else
        None
    )) hg hg')).*2.

Lemma sphyperedge_map_eq_reqs_correct_1 {T} (hg hg' : Pmap (SPHyperEdge T)) ts :
  sphyperedge_map_eq_reqs hg hg' = Some ts ->
  Forall (uncurry eq) ts ->
  hg = hg'.
Proof.
  intros Heq Hts.
  apply map_eq.
  intros i.
  apply option_eq.
  unfold sphyperedge_map_eq_reqs in Heq.
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
    destruct (hg !! i) as [[t v]|] eqn:Hgi,
      (hg' !! i) as [[t' v']|] eqn:Hg'i; cbn in Hmi;
    [|exfalso; done..].
    revert Hmi.
    intros [= Hmi].
    case_decide as Hparts; [|done].
    f_equiv.
    f_equal.
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

Lemma sphyperedge_map_eq_reqs_correct {T} (hg hg' : Pmap (SPHyperEdge T)) :
  (exists ts, sphyperedge_map_eq_reqs hg hg' = Some ts /\
  Forall (uncurry eq) ts) <->
  hg = hg'.
Proof.
  split; [intros (?&?&?); eauto using sphyperedge_map_eq_reqs_correct_1|].
  intros <-.
  unfold sphyperedge_map_eq_reqs.
  rewrite merge_diag.
  exists ((λ a, (a.2.1, a.2.1)) <$> map_to_list hg).
  split; [|rewrite Forall_fmap, Forall_forall; done].
  apply join_list_Some.
  rewrite (omap_ext _ (λ a, Some (Some (a.1, a.1)))). 2: {
    intros _ [t v] _.
    cbn.
    now rewrite decide_True.
  }
  rewrite <- map_fmap_alt.
  rewrite map_to_list_fmap.
  rewrite snds_prod_map, <- 2 list_fmap_compose.
  done.
Qed.




Definition spgraph_eq_reqs {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  option (list (T * T)) :=
  if decide (cosphg.(spinputs) = cosphg'.(spinputs) /\ cosphg.(spoutputs) = cosphg'.(spoutputs)
    /\ cosphg.(sphedges).(sphypervertices) = cosphg'.(sphedges).(sphypervertices)) then
    sphyperedge_map_eq_reqs cosphg.(sphedges).(sphyperedges) cosphg'.(sphedges).(sphyperedges)
  else
    None.

Lemma spgraph_eq_reqs_correct {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  (exists ts, spgraph_eq_reqs cosphg cosphg' = Some ts /\
    Forall (uncurry eq) ts) <->
  cosphg = cosphg'.
Proof.
  destruct cosphg as [[hg hv] ins outs], cosphg' as [[hg' hv'] ins' outs'].
  unfold spgraph_eq_reqs.
  cbn.
  case_decide as Haux.
  - rewrite sphyperedge_map_eq_reqs_correct.
    split; [intros ->; now repeat f_equal|].
    congruence.
  - naive_solver.
Qed.





Fixpoint gmultiset_pre_isos_extending_aux
  (hg hg' : list (positive * positive) (* lists of element and multiplicity *))
  (m : Pmap positive) : list (Pmap positive) :=
  match hg with
  | [] => match hg' with | [] => [m] | _::_ => [] end
  | (k, n) :: hg =>
    match m !! k with
    | Some mk =>
      list_select (λ k_n, k_n = (mk, n)) hg' ≫=
        λ '(_, hg'rest),
          gmultiset_pre_isos_extending_aux hg hg'rest m
    | None =>
      list_select (λ k_n, k_n.2 = n) hg' ≫=
        λ '(k_n, hg'rest),
          gmultiset_pre_isos_extending_aux hg hg'rest (<[k := k_n.1]> m)
    end
  end.

Definition gmultiset_pre_isos_extending (hg hg' : gmultiset positive)
  (m : Pmap positive) : list (Pmap positive) :=
  gmultiset_pre_isos_extending_aux (map_to_list hg.(gmultiset_car))
    (map_to_list hg'.(gmultiset_car)) m.

Fixpoint sphyperedge_map_pre_isos_extending_aux {T}
  (hg hg' : list (positive * (SPHyperEdge T)))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T * T) * Pmap positive * Pmap positive) :=
  match hg with
  | [] => match hg' with | [] => [ts_mhe_mv] | _::_ => [] end
  | (k, (t, v)) :: hg =>
    list_select (λ k_tv, size (k_tv.2.2) = size v) hg'
      ≫= λ '(k_tv, hg'rest),
      match extend_posmap_one k k_tv.1 ts_mhe_mv.1.2 with
      | None => []
      | Some mhe' =>
        mv' ← gmultiset_pre_isos_extending v k_tv.2.2 ts_mhe_mv.2;
        sphyperedge_map_pre_isos_extending_aux hg hg'rest
         ((t, k_tv.2.1) :: ts_mhe_mv.1.1, mhe', mv')
      end
  end.

Definition sphyperedge_map_pre_isos_extending {T} (hg hg' : Pmap (SPHyperEdge T))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T*T) * Pmap positive * Pmap positive) :=
  sphyperedge_map_pre_isos_extending_aux (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.

Definition spgraph_pre_isos {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  list (list (T * T) * Pmap positive * Pmap positive) :=
  if decide (size (spisolated_vertices cosphg) = size (spisolated_vertices cosphg')) then
    default []
      (mv ← extend_posmap (zip (cosphg.(spinputs) ++ cosphg.(spoutputs))
        (cosphg'.(spinputs) ++ cosphg'.(spoutputs))) ∅;
      Some
      (sphyperedge_map_pre_isos_extending cosphg.(sphedges).(sphyperedges)
        cosphg'.(sphedges).(sphyperedges) ([], ∅, mv)))
  else
    [].


Definition spgraph_iso_conditions {T n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) : list (list (T * T)) :=
  omap (λ '(ts, _, mv),
    if decide (size mv = size (map_img mv :> Pset)) then
      Some ts
    else None) (spgraph_pre_isos cosphg cosphg').

Lemma gmultiset_pre_isos_extending_aux_correct hg hg' m :
  Forall (λ m',
    length hg = length hg' /\
    m ⊆ m' /\
    dom m' = dom m ∪ list_to_set hg.*1 /\
    map_img m' =@{Pset} map_img m ∪ list_to_set hg'.*1 /\
    prod_map (m'!!.) id <$> hg ≡ₚ prod_map Some id <$> hg')
    (gmultiset_pre_isos_extending_aux hg hg' m).
Proof.
  revert m hg';
  induction hg as [|(k, n) hg IHhg]; intros m hg'.
  - destruct hg'; [|done].
    cbn.
    apply Forall_singleton.
    rewrite 2 union_empty_r_L.
    done.
  - cbn -[union].
    destruct (m !! k) as [mk|] eqn:Hmk.
    + rewrite Forall_bind, Forall_forall.
      intros (k_n, hg'rest) (-> & Hperm)%elem_of_list_select_perm_Prop.
      cbn -[union].
      eapply Forall_impl; [apply IHhg|].
      intros m' (Hlen & Hmm' & Hdom & Himg & Hmap).
      split; [rewrite Hperm; now f_equal/=|].
      split; [done|].
      split_and!.
      * rewrite Hdom.
        rewrite union_assoc_L.
        f_equal.
        apply elem_of_dom_2 in Hmk.
        set_solver + Hmk.
      * rewrite Himg.
        erewrite (list_to_set_perm_L hg'.*1) by now rewrite Hperm.
        cbn -[union].
        rewrite union_assoc_L.
        f_equal.
        apply (elem_of_map_img_2 (SA:=Pset)) in Hmk.
        set_solver + Hmk.
      * rewrite Hperm.
        cbn.
        f_equiv; [f_equal; revert Hmm'; now apply lookup_weaken|].
        apply Hmap.
    + rewrite Forall_bind, Forall_forall.
      intros ((k', _), hg'rest) ([= ->] & Hperm)%elem_of_list_select_perm_Prop.
      cbn -[union].
      eapply Forall_impl; [apply IHhg|].
      intros m' (Hlen & Hmm' & Hdom & Himg & Hmap).
      split_and!.
      * rewrite Hperm; now f_equal/=.
      * rewrite <- Hmm'.
        now apply insert_subseteq.
      * rewrite Hdom, dom_insert_L, (union_comm_L {[_]}), union_assoc_L.
        done.
      * rewrite Himg.
        erewrite (list_to_set_perm_L hg'.*1) by now rewrite Hperm.
        cbn -[union].
        rewrite map_img_insert_notin_L by done.
        now rewrite (union_comm_L {[_]}), union_assoc_L.
      * rewrite Hperm.
        cbn.
        f_equiv; [f_equal; revert Hmm'; apply lookup_weaken, lookup_insert|].
        done.
Qed.


Lemma gmultiset_pre_isos_extending_correct hg hg' m :
  Forall (λ m',
    size hg = size hg' /\
    m ⊆ m' /\
    dom m' = dom m ∪ set_map id (dom hg) /\
    map_img m' =@{Pset} map_img m ∪ set_map id (dom hg') /\
    gmultiset_map (m'!!.) hg = gmultiset_map Some hg')
    (gmultiset_pre_isos_extending hg hg' m).
Proof.
  unfold gmultiset_pre_isos_extending.
  eapply Forall_impl; [apply gmultiset_pre_isos_extending_aux_correct|].
  intros m' (Hlen & Hmm' & Hdom & Himg & Hperm).
  split_and!.
  - rewrite 2 gmultiset_size_alt.
    apply (fmap_Permutation snd) in Hperm.
    rewrite 2 snds_prod_map, 2 list_fmap_id in Hperm.
    apply Permutation_list_sum.
    now rewrite Hperm.
  - done.
  - rewrite Hdom.
    f_equal.
    apply leibniz_equiv_iff.
    replace hg with (GMultiSet hg.(gmultiset_car)) at 2 by now destruct hg.
    unfold dom, gmultiset_dom.
    rewrite ((leibniz_equiv_iff _ _).1 (dom_alt _)).
    rewrite set_map_list_to_set, list_fmap_id.
    done.
  - rewrite Himg.
    f_equal.
    apply leibniz_equiv_iff.
    replace hg' with (GMultiSet hg'.(gmultiset_car)) at 2 by now destruct hg'.
    unfold dom, gmultiset_dom.
    rewrite ((leibniz_equiv_iff _ _).1 (dom_alt _)).
    rewrite set_map_list_to_set, list_fmap_id.
    done.
  - rewrite 2 gmultiset_map_alt_car.
    now rewrite Hperm.
Qed.



Lemma sphyperedge_map_pre_isos_extending_aux_correct {T} hg hg' ts_mhe_mv :
  Forall (λ '(ts, mhe, mv),
    ts_mhe_mv.1.1 `suffix_of` ts /\
    ts_mhe_mv.1.2 ⊆ mhe /\
    ts_mhe_mv.2 ⊆ mv /\
    dom mhe = dom ts_mhe_mv.1.2 ∪ list_to_set hg.*1 /\
    dom mv = dom ts_mhe_mv.2 ∪ set_map id (⋃ (dom <$> hg.*2.*2)) /\
    map_img mv =@{Pset} map_img ts_mhe_mv.2 ∪ set_map id (⋃ (dom <$> hg'.*2.*2)) /\
    exists hg'', hg' ≡ₚ hg'' /\
    Forall2 (λ '(k, (t, v)) '(k', (t', v')),
      (t, t') ∈ ts /\
      mhe !! k = Some k' /\
      gmultiset_map (mv !!.) v = gmultiset_map Some v') hg hg''
    ) (@sphyperedge_map_pre_isos_extending_aux T hg hg' ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv;
  induction hg as [|[k [t v]] hg IHhg]; intros hg' tg_mhe_mv.
  1:{
    cbn.
    destruct hg'; [|constructor].
    apply Forall_singleton.
    destruct tg_mhe_mv as [[tg mhe] mv].
    cbn.
    do 3 (split; [done|]).
    do 3 (split; [now rewrite 1?set_map_empty, union_empty_r_L|]).
    exists [].
    split; [done|].
    constructor.
  }
  cbn -[union].
  rewrite Forall_bind.
  rewrite Forall_forall.
  intros ((k' & [t' v']) & hg'rest)
    [Hsize Hperm]%elem_of_list_select_perm_Prop.
  cbn -[union] in *.
  destruct (extend_posmap_one _ _ _) as [mhe'|] eqn:Hmhe'; [cbn -[union]|done].
  rewrite Forall_bind.
  eapply Forall_impl; [apply gmultiset_pre_isos_extending_correct|].
  intros mv' (_ & Hmv').
  cbn -[union].
  eapply Forall_impl; [apply IHhg|].
  intros [[ts mhe] mv].
  cbn -[union].
  intros (Hts & Hmhe & Hmv & Hdom_mhe & Hdom_mv & Himg_mv & Hex).
  apply extend_posmap_one_Some in Hmhe'.
  split_and!.
  - rewrite <- Hts.
    now apply suffix_cons_r.
  - now rewrite Hmhe'.1.
  - now rewrite Hmv'.1.
  - rewrite Hdom_mhe, Hmhe'.2.2.
    symmetry; apply union_assoc_L.
  - rewrite Hdom_mv, Hmv'.2.1.
    rewrite set_map_union_L.
    symmetry; apply union_assoc_L.
  - rewrite Himg_mv, Hmv'.2.2.1.
    rewrite Hperm.
    cbn -[union].
    rewrite set_map_union_L.
    symmetry; apply union_assoc_L.
  - destruct Hex as (hg'' & Hhg''perm & Halls).
    exists ((k', (t', v')) :: hg'').
    split; [now rewrite Hperm, Hhg''perm|].
    constructor; [|done].
    split; [revert Hts; apply elem_of_suffix; left|].
    split; [revert Hmhe; apply lookup_weaken, Hmhe'.2.1|].
    pose proof Hmv'.2.1 as Hall2.
    rewrite <- Hmv'.2.2.2.
    apply gmultiset_map_ext.
    intros a Ha%gmultiset_elem_of_dom.
    assert (Hamv' : a ∈ dom mv'). 1:{
      rewrite Hmv'.2.1.
      rewrite elem_of_union; right.
      rewrite elem_of_map.
      eauto.
    }
    apply elem_of_dom in Hamv' as [mv'a Hmv'a].
    rewrite Hmv'a.
    revert Hmv'a Hmv.
    apply lookup_weaken.
Qed.




Lemma sphyperedge_map_pre_isos_extending_correct {T} (hg hg' : Pmap (SPHyperEdge T))
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
      dom ts_mhe_mv.2 ∪ set_map id (⋃ (dom <$> (map_to_list hg).*2.*2)) /\
    map_img mv =@{Pset}
      map_img ts_mhe_mv.2 ∪ set_map id (⋃ (dom <$> (map_to_list hg').*2.*2)) /\
    map_relation (λ _ '(t', v') '(t, v),
      (t, t') ∈ ts /\
      v = v') (λ _ _, False) (λ _ _, False)
        (prod_map id (gmultiset_map Some) <$> hg')
        (prod_map id (gmultiset_map (mv !!.)) <$> kmap (Pmap_map mhe) hg))
  (sphyperedge_map_pre_isos_extending hg hg' ts_mhe_mv).
Proof.
  eapply Forall_impl; [apply sphyperedge_map_pre_isos_extending_aux_correct|].
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
      intros (k, [t v]) (k', [t' v']).
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
    intros [k [t v]] [k' [t' v']].
    cbn.
    intros (Htt' & Hkk' & Hvs).
    split_and!; try done.
    symmetry.
    unfold Pmap_map.
    now rewrite Hkk'.
Qed.



Lemma spgraph_pre_isos_correct_aux {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    size (spisolated_vertices cosphg) = size (spisolated_vertices cosphg') /\
    dom mhe = dom cosphg.(sphedges).(sphyperedges) /\
    (forall i j a, mhe !! i = Some a -> mhe !! j = Some a -> i = j) /\
    dom mv = spreferrenced_vertices cosphg /\
    map_img mv = spreferrenced_vertices cosphg' /\
    map_relation (λ _ '(t', v') '(t, v),
      (t, t') ∈ ts /\
      v = v') (λ _ _, False) (λ _ _, False)
        (prod_map id (gmultiset_map Some) <$> cosphg'.(sphedges).(sphyperedges))
        (prod_map id (gmultiset_map (mv !!.)) <$> kmap (Pmap_map mhe)
          cosphg.(sphedges).(sphyperedges)) /\
    (mv !!.) <$> vec_to_list cosphg.(spinputs) = Some <$> vec_to_list cosphg'.(spinputs) /\
    (mv !!.) <$> vec_to_list cosphg.(spoutputs) = Some <$> vec_to_list cosphg'.(spoutputs)
    )
    (spgraph_pre_isos cosphg cosphg').
Proof.
  unfold spgraph_pre_isos.
  case_decide as Hsize; [|easy].
  destruct (extend_posmap _ _) as [mvi|] eqn:Hmvi; [|easy].
  cbn.
  eapply Forall_impl; [apply sphyperedge_map_pre_isos_extending_correct|].
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
    unfold spreferrenced_vertices; f_equal;
    rewrite list_to_set_bind_L, set_map_union_list_L;
    f_equal; rewrite <- 3 list_fmap_compose;
    apply list_fmap_ext; intros _ [k [t v]] _; cbn;
    apply set_eq; intros ?;
    rewrite elem_of_list_to_set, gmultiset_elem_of_elements,
    elem_of_map; setoid_rewrite gmultiset_elem_of_dom; set_solver +|].
  split; [rewrite Himg_mv, Himg_mvi;
    unfold spreferrenced_vertices; f_equal;
    rewrite list_to_set_bind_L, set_map_union_list_L;
    f_equal; rewrite <- 3 list_fmap_compose;
    apply list_fmap_ext; intros _ [k [t v]] _; cbn;
    apply set_eq; intros ?;
    rewrite elem_of_list_to_set, gmultiset_elem_of_elements,
    elem_of_map; setoid_rewrite gmultiset_elem_of_dom; set_solver +|].
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


Lemma spgraph_pre_isos_correct {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    Forall (uncurry eq) ts ->
    size (dom mv :> Pset) = size (map_img mv :> Pset) ->
    spisomorphic (norm_spverts cosphg) (norm_spverts cosphg'))
    (spgraph_pre_isos cosphg cosphg').
Proof.
  eapply Forall_impl; [apply spgraph_pre_isos_correct_aux|].
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
    apply spisolated_referrenced_disjoint.
  }
  eapply (spisomorphic_of_partial_inj_dom' _ _
    (Pmap_map (misol ∪ mv)) (Pmap_map mhe)).
  - apply Pmap_map_inj_on.
    1:{
      rewrite dom_union.
      rewrite Hdom_misol, Hdom_mv.
      now rewrite vertices_norm_spverts, vertices_decomp.
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
      apply spisolated_referrenced_disjoint.
  - apply Pmap_map_inj_on; [now rewrite Hdom_mhe|].
    apply Hmhe_inj.
  - symmetry.
    apply cosphg_ext; cbn; cycle 1.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Hins.
      rewrite 2 list_lookup_fmap in Hins.
      destruct ((vec_to_list (spinputs cosphg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (spinputs cosphg')) !! i) as [ii'|] eqn:Hii'; [|done].
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
      destruct ((vec_to_list (spoutputs cosphg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (spoutputs cosphg')) !! i) as [ii'|] eqn:Hii'; [|done].
      intros [= <-] [= <-].
      cbn in Houts |- *.
      revert Houts.
      intros [= Hmv_ii].
      unfold Pmap_map.
      eapply lookup_union_Some_r in Hmv_ii as Hun_ii; [|eauto].
      now rewrite Hun_ii.
    + apply sphg_ext. 2:{
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
      transitivity ((prod_map id (gmultiset_map (Pmap_map mv)) <$>
          kmap (Pmap_map mhe) (sphedges cosphg).(sphyperedges)) :> Pmap _).
      1: {
        apply map_fmap_ext; intros fi [t v] (i & Hi & <-)%lookup_kmap_Some_2.
        cbn.
        f_equal.
        apply gmultiset_map_ext.
        intros k Hk.
        unfold Pmap_map.
        rewrite lookup_union.
        enough (misol !! k = None) as -> by now rewrite (left_id_L None _).
        apply not_elem_of_dom.
        rewrite Hdom_misol.
        intros Href%spisolated_referrenced_disjoint; apply Href.
        unfold spreferrenced_vertices.
        apply elem_of_union; right.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        exists (i, (t, v)).
        split; [rewrite gmultiset_elem_of_elements; apply Hk|].
        now apply elem_of_map_to_list.
      }
      apply map_eq; intros i.
      specialize (Heq i).
      cbn in Heq.
      rewrite 2 lookup_fmap in Heq.
      rewrite lookup_fmap.
      destruct (_ !! _) as [tio'|], (_ !! _) as [tio|] eqn:Htv;
        cbn in Heq; [|easy..].
      destruct tio' as [t' v'],
        tio as [t v].
      cbn.
      f_equal.
      cbn in Heq.
      destruct Heq as (Htt' & Hvs').
      f_equal.
      * rewrite Forall_forall in Hts.
        apply (Hts _ Htt').
      * apply (f_equal (gmultiset_map (default inhabitant))) in Hvs' as Hvs.
        rewrite 2 gmultiset_map_compose in Hvs.
        unfold compose in Hvs.
        cbn in Hvs.
        rewrite gmultiset_map_id in Hvs.
        rewrite <- Hvs.
        apply gmultiset_map_ext.
        intros a Hv.
        unfold Pmap_map.
        enough (a ∈ dom mv) as Hadom by now apply elem_of_dom in Hadom as [? ->].
        rewrite Hdom_mv.
        unfold spreferrenced_vertices.
        apply union_subseteq_r.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        apply lookup_kmap_Some_2 in Htv as (i' & Hi' & <-).
        exists (i', (t, v)).
        split; [now rewrite gmultiset_elem_of_elements|].
        now apply elem_of_map_to_list.
Qed.


Lemma spgraph_pre_isos_correct' `{Equiv T} {n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    Forall (uncurry equiv) ts ->
    size (dom mv :> Pset) = size (map_img mv :> Pset) ->
    (norm_spverts cosphg) ≡ (norm_spverts cosphg'))
    (spgraph_pre_isos cosphg cosphg').
Proof.
  eapply Forall_impl; [apply spgraph_pre_isos_correct_aux|].
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
    apply spisolated_referrenced_disjoint.
  }
  etransitivity; [
  eapply rtc_once, or_introl, (spisomorphic_of_partial_inj_dom' _ _
    (Pmap_map (misol ∪ mv)) (Pmap_map mhe)), eq_refl|].
  - apply Pmap_map_inj_on.
    1:{
      rewrite dom_union.
      rewrite Hdom_misol, Hdom_mv.
      now rewrite vertices_norm_spverts, vertices_decomp.
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
      apply spisolated_referrenced_disjoint.
  - apply Pmap_map_inj_on; [now rewrite Hdom_mhe|].
    apply Hmhe_inj.
  - apply rtc_once, or_intror.
    apply mk_cosphg_eq; cbn.
    + apply vec_to_list_inj2.
      apply (list_eq_same_length _ _ _ eq_refl);
      [now rewrite 2 length_vec_to_list|].
      rewrite length_vec_to_list.
      intros i a b Hi.
      rewrite vec_to_list_map, list_lookup_fmap.
      apply (f_equal (.!! i)) in Hins.
      rewrite 2 list_lookup_fmap in Hins.
      destruct ((vec_to_list (spinputs cosphg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (spinputs cosphg')) !! i) as [ii'|] eqn:Hii'; [|done].
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
      destruct ((vec_to_list (spoutputs cosphg)) !! i) as [ii|] eqn:Hii; [|done].
      destruct ((vec_to_list (spoutputs cosphg')) !! i) as [ii'|] eqn:Hii'; [|done].
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
      replace (_ <$> _) with ((prod_map id (gmultiset_map (Pmap_map mv)) <$>
          kmap (Pmap_map mhe) (sphedges cosphg).(sphyperedges)) :> Pmap _).
      2: {
        symmetry.
        apply map_fmap_ext; intros fi [t v] (i & Hi & <-)%lookup_kmap_Some_2.
        cbn.
        f_equal.
        apply gmultiset_map_ext.
        intros k Hk.
        unfold Pmap_map.
        rewrite lookup_union.
        enough (misol !! k = None) as -> by now rewrite (left_id_L None _).
        apply not_elem_of_dom.
        rewrite Hdom_misol.
        intros Href%spisolated_referrenced_disjoint; apply Href.
        unfold spreferrenced_vertices.
        apply elem_of_union; right.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        exists (i, (t, v)).
        split; [rewrite gmultiset_elem_of_elements; apply Hk|].
        now apply elem_of_map_to_list.
      }
      intros i.
      specialize (Heq i).
      cbn in Heq.
      rewrite 2 lookup_fmap in Heq.
      rewrite lookup_fmap.
      destruct (_ !! _) as [tio'|], (_ !! _) as [tio|] eqn:Htv;
        cbn in Heq; [| easy||constructor..].
      destruct tio' as [t' v'],
        tio as [t v].
      cbn.
      f_equal.
      cbn in Heq.
      destruct Heq as (Htt' & Hvs').
      constructor.
      split; cbn.
      * rewrite Forall_forall in Hts.
        apply (Hts _ Htt').
      * apply (f_equal (gmultiset_map (default inhabitant))) in Hvs' as Hvs.
        rewrite 2 gmultiset_map_compose in Hvs.
        unfold compose in Hvs.
        cbn in Hvs.
        rewrite gmultiset_map_id in Hvs.
        rewrite <- Hvs.
        apply gmultiset_map_ext.
        intros a Hv.
        unfold Pmap_map.
        enough (a ∈ dom mv) as Hadom by now apply elem_of_dom in Hadom as [? ->].
        rewrite Hdom_mv.
        unfold spreferrenced_vertices.
        apply union_subseteq_r.
        rewrite elem_of_list_to_set, elem_of_list_bind.
        apply lookup_kmap_Some_2 in Htv as (i' & Hi' & <-).
        exists (i', (t, v)).
        split; [now rewrite gmultiset_elem_of_elements|].
        now apply elem_of_map_to_list.
Qed.



Lemma spgraph_iso_conditions_correct_aux {T n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ ts, ts.*1 = ts.*2 ->
    spisomorphic (norm_spverts cosphg) (norm_spverts cosphg'))
    (spgraph_iso_conditions cosphg cosphg').
Proof.
  rewrite Forall_forall.
  intros ts ([[ts' mhe'] mv'] & Htms & Hts)%elem_of_list_omap.
  case_decide as Hsize; [|done].
  revert Hts.
  intros [= ->].
  pose proof (spgraph_pre_isos_correct cosphg cosphg') as Hall.
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


Lemma spgraph_iso_conditions_correct {T n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) i :
  match (spgraph_iso_conditions cosphg cosphg' !! i) with
  | None => False
  | Some ts => ts.*1 = ts.*2
  end ->
  spisomorphic (norm_spverts cosphg) (norm_spverts cosphg').
Proof.
  case_match eqn:Hmi; [|done].
  apply elem_of_list_lookup_2 in Hmi.
  revert Hmi.
  refine ((Forall_forall (λ ts, ts.*1 = ts.*2 -> _) _).1 _ _).
  apply spgraph_iso_conditions_correct_aux.
Qed.





Fixpoint gmultiset_pre_isos_extending_aux_alt
  (hg hg' : list (positive * positive) (* lists of element and multiplicity *))
  (m : Piso) : list Piso :=
  match hg with
  | [] => match hg' with | [] => [m] | _::_ => [] end
  | (k, n) :: hg =>
    match m.(Piso_map) !! k with
    | Some mk =>
      list_select (λ k_n, k_n = (mk, n)) hg' ≫=
        λ '(_, hg'rest),
          gmultiset_pre_isos_extending_aux_alt hg hg'rest m
    | None =>
      list_select (λ k_n, k_n.2 = n) hg' ≫=
        λ '(k_n, hg'rest),
          default []
          (gmultiset_pre_isos_extending_aux_alt hg hg'rest <$>
            pupdate k k_n.1 m)
    end
  end.

Definition gmultiset_pre_isos_extending_alt (hg hg' : gmultiset positive)
  (m : Piso) : list (Piso) :=
  gmultiset_pre_isos_extending_aux_alt (map_to_list hg.(gmultiset_car))
    (map_to_list hg'.(gmultiset_car)) m.

Fixpoint sphyperedge_map_pre_isos_extending_aux_alt {T}
  (hg hg' : list (positive * (SPHyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  list (list (T * T) * Piso * Piso) :=
  match hg with
  | [] => match hg' with | [] => [ts_mhe_mv] | _::_ => [] end
  | (k, (t, v)) :: hg =>
    list_select (λ k_tv, size (k_tv.2.2) = size v) hg'
      ≫= λ '(k_tv, hg'rest),
      match pupdate k k_tv.1 ts_mhe_mv.1.2 with
      | None => []
      | Some mhe' =>
        mv' ← gmultiset_pre_isos_extending_alt v k_tv.2.2 ts_mhe_mv.2;
        sphyperedge_map_pre_isos_extending_aux_alt hg hg'rest
         ((t, k_tv.2.1) :: ts_mhe_mv.1.1, mhe', mv')
      end
  end.

Definition sphyperedge_map_pre_isos_extending_alt {T} (hg hg' : Pmap (SPHyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  list (list (T*T) * Piso * Piso) :=
  sphyperedge_map_pre_isos_extending_aux_alt (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.

Definition spgraph_pre_isos_alt {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  list (list (T * T) * Piso * Piso) :=
  if decide (size (spisolated_vertices cosphg) = size (spisolated_vertices cosphg')) then
    default []
      (mv ← pupdates (zip (cosphg.(spinputs) ++ cosphg.(spoutputs))
        (cosphg'.(spinputs) ++ cosphg'.(spoutputs))) ∅;
      Some
      (sphyperedge_map_pre_isos_extending_alt cosphg.(sphedges).(sphyperedges)
        cosphg'.(sphedges).(sphyperedges) ([], ∅, mv)))
  else
    [].

Lemma gmultiset_pre_isos_extending_aux_alt_correct hg hg' m :
  Piso_map <$> gmultiset_pre_isos_extending_aux_alt hg hg' m ⊆
  gmultiset_pre_isos_extending_aux hg hg' (Piso_map m).
Proof.
  revert hg' m; induction hg as [|[k n] hg IHhg];
    intros hg' m; [destruct hg'; done|].
  cbn.
  destruct (m.(Piso_map) !! k) as [mk|] eqn:Hmk.
  - rewrite list_bind_fmap.
    apply list_bind_mono_r.
    intros [k_n hg'rest] (Hk_n & Hhg')%elem_of_list_select_perm_Prop.
    apply IHhg.
  - rewrite list_bind_fmap.
    apply list_bind_mono_r.
    intros [k_n hg'rest] (Hk_n & Hhg')%elem_of_list_select_perm_Prop.
    destruct (pupdate k k_n.1 m) as [m'|] eqn:Hm';
      [|now apply list_subseteq_nil].
    cbn.
    rewrite IHhg.
    now apply pupdate_correct_insert in Hm' as ->.
Qed.

Lemma gmultiset_pre_isos_extending_alt_correct hg hg' m :
  Piso_map <$> gmultiset_pre_isos_extending_alt hg hg' m ⊆
  gmultiset_pre_isos_extending hg hg' (Piso_map m).
Proof.
  apply gmultiset_pre_isos_extending_aux_alt_correct.
Qed.

Lemma sphyperedge_map_pre_isos_extending_aux_alt_correct {T}
  (hg hg' : list (positive * (SPHyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
    sphyperedge_map_pre_isos_extending_aux_alt hg hg' ts_mhe_mv
    ⊆ sphyperedge_map_pre_isos_extending_aux hg hg'
    ((prod_map (prod_map id Piso_map) Piso_map) ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv; induction hg as [|[k [t vs]] hg IHhg];
    intros hg' ts_mhe_mv; [destruct hg'; done|].
  cbn.
  rewrite list_bind_fmap.
  apply list_bind_mono_r.
  intros [k' tio'] (Hvs & Hhg')%elem_of_list_select_perm_Prop.
  unfold prod_map at 3 4.
  cbn.
  destruct (pupdate k k'.1 ts_mhe_mv.1.2) as [mhe'|] eqn:Hmhe';
    [|now apply list_subseteq_nil].
  apply extend_posmap_one_Piso_map' in Hmhe' as Hmhe''.
  rewrite Hmhe''.
  unfold prod_map at 5 6.
  cbn.
  rewrite list_bind_fmap.
  rewrite <- (list_bind_mono_l _ _ _
    (gmultiset_pre_isos_extending_alt_correct _ _ _)).
  rewrite list_fmap_bind.
  apply list_bind_mono_r.
  intros; apply IHhg.
Qed.

Lemma sphyperedge_map_pre_isos_extending_alt_correct {T}
  (hg hg' : Pmap (SPHyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
    sphyperedge_map_pre_isos_extending_alt hg hg' ts_mhe_mv
    ⊆ sphyperedge_map_pre_isos_extending hg hg'
    ((prod_map (prod_map id Piso_map) Piso_map) ts_mhe_mv).
Proof.
  apply sphyperedge_map_pre_isos_extending_aux_alt_correct.
Qed.

Lemma spgraph_pre_isos_alt_correct {T n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  (prod_map (prod_map id Piso_map) Piso_map) <$>
  spgraph_pre_isos_alt cohg cohg' ⊆
  spgraph_pre_isos cohg cohg'.
Proof.
  unfold spgraph_pre_isos_alt, spgraph_pre_isos.
  case_decide; [|done].
  destruct (pupdates _ ∅) as [mio|] eqn:Hmio; [|apply list_subseteq_nil].
  apply extend_posmap_Piso_map in Hmio as Hmio'.
  change (Piso_map ∅) with (∅ :> Pmap positive) in Hmio'.
  rewrite Hmio'.
  cbn.
  apply sphyperedge_map_pre_isos_extending_alt_correct.
Qed.


Section dec_equiv.

Context `{Equiv T, !RelDecision (≡@{T})}.

Fixpoint sphyperedge_map_isos_extending_aux
  (hg hg' : list (positive * (SPHyperEdge T)))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => match hg' with | [] => [mhe_mv] | _::_ => [] end
  | (k, (t, v)) :: hg =>
    list_select (λ k_tv, t ≡ k_tv.2.1 /\ size (k_tv.2.2) = size v) hg'
      ≫= λ '(k_tv, hg'rest),
      match pupdate k k_tv.1 mhe_mv.1 with
      | None => []
      | Some mhe' =>
        mv' ← gmultiset_pre_isos_extending_alt v k_tv.2.2 mhe_mv.2;
        sphyperedge_map_isos_extending_aux hg hg'rest
         (mhe', mv')
      end
  end.


Definition sphyperedge_map_isos_extending
  (hg hg' : Pmap (SPHyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  sphyperedge_map_isos_extending_aux (map_to_list hg)
    (map_to_list hg') mhe_mv.

Definition spgraph_isos {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  list (Piso * Piso) :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    default []
      (mv ← pupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
      Some
      (sphyperedge_map_isos_extending cohg.(sphedges).(sphyperedges)
        cohg'.(sphedges).(sphyperedges) (∅, mv)))
  else
    [].

Lemma sphyperedge_map_isos_extending_aux_correct
  (hg hg' : list (positive * (SPHyperEdge T)))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  Forall (uncurry equiv) ts_mhe_mv.1.1 ->
  sphyperedge_map_isos_extending_aux hg hg' (ts_mhe_mv.1.2, ts_mhe_mv.2)
    ⊆ (λ tev, (tev.1.2, tev.2)) <$>
      (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ sphyperedge_map_pre_isos_extending_aux_alt hg hg' ts_mhe_mv).
Proof.
  revert hg' ts_mhe_mv; induction hg as [|[k [t v]] hg IHhg];
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
  intros [k_n' hg'rest] (Hvs & Hhg')%elem_of_list_select_perm_Prop.
  cbn.
  case_decide as Htt'; [|apply list_subseteq_nil].
  destruct (pupdate k k_n'.1 ts_mhe_mv.1.2) as [mhe'|] eqn:Hmhe';
    [|now apply list_subseteq_nil].
  cbn.
  rewrite (list_bind_mono_r _ _ _
    (fun mv' _ => IHhg hg'rest ((t, k_n'.2.1) :: ts_mhe_mv.1.1, mhe', mv')
    (List.Forall_cons (uncurry equiv) (_,_) _ Htt' Hts))).
  rewrite list_filter_bind, list_bind_fmap.
  done.
Qed.


Lemma sphyperedge_map_isos_extending_correct
  (hg hg' : Pmap (SPHyperEdge T))
  (ts_mhe_mv : list (T * T) * Piso * Piso) :
  Forall (uncurry equiv) ts_mhe_mv.1.1 ->
  sphyperedge_map_isos_extending hg hg' (ts_mhe_mv.1.2, ts_mhe_mv.2)
    ⊆ (λ tev, (tev.1.2, tev.2)) <$>
      (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ sphyperedge_map_pre_isos_extending_alt hg hg' ts_mhe_mv).
Proof.
  apply sphyperedge_map_isos_extending_aux_correct.
Qed.

Lemma spgraph_isos_correct_aux {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_isos cohg cohg' ⊆
  (λ tev, (tev.1.2, tev.2)) <$> (filter (λ tev, Forall (uncurry equiv) tev.1.1)
        $ spgraph_pre_isos_alt cohg cohg').
Proof.
  unfold spgraph_isos, spgraph_pre_isos_alt.
  case_decide; [|apply list_subseteq_nil].
  destruct (pupdates _ ∅) as [mio|] eqn:Hmio; [|done].
  cbn.
  apply (sphyperedge_map_isos_extending_correct _ _ ([], ∅, mio)).
  done.
Qed.


Lemma spgraph_isos_correct_aux_2 {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  Forall (λ '(mhe, mv),
    (norm_spverts cohg) ≡ (norm_spverts cohg'))
    (spgraph_isos cohg cohg').
Proof.
  rewrite Forall_forall.
  intros (mhe, mv) (((ts & _) & _) & [= <- <-] &
    [Hts Hin]%elem_of_list_filter)%spgraph_isos_correct_aux%elem_of_list_fmap.
  specialize (spgraph_pre_isos_alt_correct cohg cohg') as Hsub.
  specialize (Hsub _ (elem_of_list_fmap_1 _ _ _ Hin)).
  cbn in Hsub.
  specialize (spgraph_pre_isos_correct' cohg cohg') as Hcorr.
  rewrite Forall_forall in Hcorr.
  specialize (Hcorr _ Hsub).
  cbn in Hcorr.
  specialize (Hcorr Hts).
  now specialize (Hcorr (map_inverses_card_img _ _ (Piso_inverses mv))).
Qed.

Lemma spgraph_isos_test {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  match spgraph_isos cohg cohg' with
  | [] => False
  | _ :: _ => True
  end -> norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  pose proof (spgraph_isos_correct_aux_2 cohg cohg') as Hcorr.
  destruct (spgraph_isos _ _); [done|].
  rewrite Forall_cons in Hcorr.
  case_match.
  intros; apply Hcorr.
Qed.

Definition spgraph_iso_partial_test {n m} (cohg cohg' : CospanSPHyperGraph T n m) : bool :=
  match spgraph_isos cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma spgraph_iso_partial_test_correct {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test cohg cohg' = true ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  intros Heq.
  apply spgraph_isos_test.
  revert Heq.
  unfold spgraph_iso_partial_test.
  now case_match.
Qed.





Fixpoint gmultiset_pre_isos_extending_aux_alt'
  (hg hg' : list (positive * positive) (* lists of element and multiplicity *))
  (m : WPiso) : list WPiso :=
  match hg with
  | [] => match hg' with | [] => [m] | _::_ => [] end
  | (k, n) :: hg =>
    match m.(WPiso_map) !! k with
    | Some mk =>
      list_select (λ k_n, k_n = (mk, n)) hg' ≫=
        λ '(_, hg'rest),
          gmultiset_pre_isos_extending_aux_alt' hg hg'rest m
    | None =>
      list_select (λ k_n, k_n.2 = n) hg' ≫=
        λ '(k_n, hg'rest),
          default []
          (gmultiset_pre_isos_extending_aux_alt' hg hg'rest <$>
            wpupdate k k_n.1 m)
    end
  end.

Fixpoint sphyperedge_map_isos_extending_aux'
  (hg hg' : list (positive * (T * list (positive * positive))))
  (mhe_mv : WPiso * WPiso) :
  list (WPiso * WPiso) :=
  match hg with
  | [] => match hg' with | [] => [mhe_mv] | _::_ => [] end
  | (k, (t, v)) :: hg =>
    list_select (λ k_tv, t ≡ k_tv.2.1 /\
      sum_list_with Pos.to_nat (k_tv.2.2).*2 =
      sum_list_with Pos.to_nat v.*2) hg'
      ≫= λ '(k_tv, hg'rest),
      match wpupdate k k_tv.1 mhe_mv.1 with
      | None => []
      | Some mhe' =>
        mv' ← gmultiset_pre_isos_extending_aux_alt' v k_tv.2.2 mhe_mv.2;
        sphyperedge_map_isos_extending_aux' hg hg'rest
         (mhe', mv')
      end
  end.

Definition sphyperedge_map_isos_extending'
  (hg hg' : Pmap (SPHyperEdge T)) (mhe_mv : WPiso * WPiso) :
  list (WPiso * WPiso) :=
  sphyperedge_map_isos_extending_aux'
    (prod_map id (prod_map id (map_to_list (M:=gmap positive positive) ∘ gmultiset_car)) <$>
      (map_to_list hg :> list (positive * (T * gmultiset positive))))
    (prod_map id (prod_map id (map_to_list (M:=gmap positive positive) ∘ gmultiset_car)) <$>
      (map_to_list hg' :> list (positive * (T * gmultiset positive))))
    mhe_mv.

Definition spgraph_isos' {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  list (WPiso * WPiso) :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    default []
      (mv ← wpupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
      Some
      (sphyperedge_map_isos_extending' cohg.(sphedges).(sphyperedges)
        cohg'.(sphedges).(sphyperedges) (∅, mv)))
  else
    [].


Definition spgraph_iso_partial_test' {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) : bool :=
  match spgraph_isos' cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.


Lemma gmultiset_pre_isos_extending_aux_alt'_correct hg hg' m :
  gmultiset_pre_isos_extending_aux_alt' hg hg' (Piso_to_weak m) =
  Piso_to_weak <$> gmultiset_pre_isos_extending_aux_alt hg hg' m.
Proof.
  revert hg' m; induction hg as [|(k, n) hg IHhg]; intros hg' m;
  [now destruct hg'|].
  cbn.
  case_match eqn:Hmk.
  cbn.
  - rewrite list_bind_fmap.
    apply list_bind_ext; [|done].
    intros (kn', hg'rest).
    now rewrite IHhg.
  - rewrite list_bind_fmap.
    apply list_bind_ext; [|done].
    intros (kn', hg'rest).
    rewrite wpupdate_correct.
    destruct (pupdate k kn'.1 m) as [m'|]; [|done].
    cbn.
    apply IHhg.
Qed.



Lemma list_decomps_aux_fmap {A B} (f : A -> B) (l l' : list A) :
  list_decomps_aux (f <$> l') (f <$> l) =
    prod_map (prod_map (fmap (M:=list) f) f) (fmap (M:=list) f) <$>
      list_decomps_aux l' l.
Proof.
  revert l';
  induction l; [done|intros l'].
  cbn.
  f_equal.
  rewrite <- IHl.
  now rewrite fmap_app.
Qed.

Lemma list_decomps_fmap {A B} (f : A -> B) (l : list A) :
  list_decomps (f <$> l) =
    prod_map (prod_map (fmap (M:=list) f) f) (fmap (M:=list) f) <$>
      list_decomps l.
Proof.
  apply (list_decomps_aux_fmap _ _ []).
Qed.

Lemma list_removals_fmap {A B} (f : A -> B) (l : list A) :
  list_removals (f <$> l) = prod_map f (fmap (M:=list) f) <$> list_removals l.
Proof.
  unfold list_removals.
  rewrite list_decomps_fmap.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext; intros _ [[]] _; cbn; now rewrite fmap_app.
Qed.

Lemma list_select_fmap {A B} (P : B -> Prop) `{HP : forall b, Decision (P b)}
  (f : A -> B) (l : list A) :
  list_select P (f <$> l) = prod_map f (fmap (M:=list) f) <$> list_select (P ∘ f) l.
Proof.
  unfold list_select.
  rewrite list_removals_fmap.
  now rewrite list_filter_fmap.
Qed.

Lemma gmultiset_size_alt' `{Countable A} (m : gmultiset A) :
  size m = sum_list_with Pos.to_nat (map_to_list (gmultiset_car m)).*2.
Proof.
  rewrite gmultiset_size_alt.
  remember (_.*2) as l eqn:Hl.
  clear Hl.
  unfold list_sum.
  induction l; cbn; congruence.
Qed.

Lemma list_select_iff {A} (P Q : A -> Prop)
  `{HP : forall a, Decision (P a), HQ : forall a, Decision (Q a)} l :
  (forall a, a ∈ l -> P a <-> Q a) ->
  list_select P l = list_select Q l.
Proof.
  intros HPQ.
  unfold list_select.
  apply list_filter_iff_strong.
  intros (a & l') (hd & tl & -> & <-)%elem_of_list_removals.
  apply HPQ.
  cbn.
  set_solver +.
Qed.



Lemma sphyperedge_map_isos_extending_aux'_correct ktio ktio' mhe_mv :
  sphyperedge_map_isos_extending_aux'
    (prod_map id (prod_map id (map_to_list ∘ gmultiset_car)) <$> ktio)
    (prod_map id (prod_map id (map_to_list ∘ gmultiset_car)) <$> ktio')
    (prod_map Piso_to_weak Piso_to_weak mhe_mv) =
  prod_map Piso_to_weak Piso_to_weak <$>
    sphyperedge_map_isos_extending_aux ktio ktio' mhe_mv.
Proof.
  revert ktio' mhe_mv; induction ktio as [|[k [t v]] ktio IHktio];
    intros ktios' mhe_mv; [now destruct ktios'|].
  cbn.
  rewrite list_select_fmap.
  unfold compose at 4.
  simpl.
  rewrite list_fmap_bind, list_bind_fmap.
  apply list_bind_ext; [|
    apply list_select_iff; intros; now rewrite <- 2 gmultiset_size_alt'].
  intros (ktio' & ktios'rest).
  cbn.
  simpl.
  rewrite wpupdate_correct.
  destruct (pupdate k ktio'.1 mhe_mv.1) as [mhe'|] eqn:Hmhe'; [|done].
  cbn.
  rewrite gmultiset_pre_isos_extending_aux_alt'_correct.
  rewrite list_fmap_bind, list_bind_fmap.
  apply list_bind_ext; [|done].
  intros mv'.
  cbn.
  rewrite <- IHktio.
  done.
Qed.


Lemma sphyperedge_map_isos_extending'_correct ktio ktio' mhe_mv :
  sphyperedge_map_isos_extending' ktio ktio' (prod_map Piso_to_weak Piso_to_weak mhe_mv) =
  prod_map Piso_to_weak Piso_to_weak <$> sphyperedge_map_isos_extending ktio ktio' mhe_mv.
Proof.
  unfold sphyperedge_map_isos_extending'.
  rewrite sphyperedge_map_isos_extending_aux'_correct.
  done.
Qed.

Lemma spgraph_isos'_correct {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_isos' cohg cohg' =
  prod_map Piso_to_weak Piso_to_weak <$>
  spgraph_isos cohg cohg'.
Proof.
  unfold spgraph_isos', spgraph_isos.
  case_decide; [|done].
  rewrite WPiso_empty_correct, wpupdates_correct.
  destruct (pupdates _ _); [cbn|done].
  apply (sphyperedge_map_isos_extending'_correct _ _ (_, _)).
Qed.

Lemma spgraph_iso_partial_test'_eq {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test' cohg cohg' = spgraph_iso_partial_test cohg cohg'.
Proof.
  unfold spgraph_iso_partial_test, spgraph_iso_partial_test'.
  rewrite spgraph_isos'_correct.
  now destruct (spgraph_isos _ _).
Qed.

Lemma spgraph_iso_partial_test'_correct {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test' cohg cohg' = true ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  rewrite spgraph_iso_partial_test'_eq.
  apply spgraph_iso_partial_test_correct.
Qed.



Fixpoint vertex_map_of_sections
  (vs : list (list (positive * positive) * list (positive * positive)))
  (m : Piso) : option Piso :=
  match vs with
  | [] => Some m
  | (vin, vout) :: vs =>
    list_first_omap (vertex_map_of_sections vs)
      $ gmultiset_pre_isos_extending_aux_alt vin vout m
  end.

Definition vertex_sections_of_alignment
  (ms : list (gmultiset positive * gmultiset positive)) :
    list (list (positive * positive) * list (positive * positive)) :=
  ((λ '((i1, o1), (i2, o2)),
    (map_to_list (gmultiset_car (i1 ∩ i2)),
    map_to_list (gmultiset_car (o1 ∩ o2)))) <$> list_ordpairs ms) ++
  ((λ '(i, o),  (map_to_list (gmultiset_car i),
    map_to_list (gmultiset_car o))) <$> ms).

Definition vertex_map_of_alignment
  (m : Piso) (ktios : list ((positive * (T * gmultiset positive)) *
    (positive * (T * gmultiset positive)))) : option Piso :=
  vertex_map_of_sections (vertex_sections_of_alignment
    ((λ ktio_ktio', (ktio_ktio'.1.2.2, ktio_ktio'.2.2.2)) <$> ktios)) m.





Definition maybe_vertex_map (m : Piso)
  (ktios ktios' : list (positive * (T * gmultiset positive))) :
  option Piso :=
  list_first_omap (vertex_map_of_alignment m)
    (partial_permutations (λ ktio ktio', ktio.2.1 ≡ ktio'.2.1 /\
      size ktio.2.2 = size ktio'.2.2) ktios ktios').


Definition spgraph_isos_fast {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  option Piso :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    mv ← pupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
    maybe_vertex_map mv (map_to_list cohg.(sphedges).(sphyperedges))
        (map_to_list cohg'.(sphedges).(sphyperedges))
  else
    None.


Definition spgraph_iso_partial_test_fast
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) : bool :=
  match spgraph_isos_fast cohg cohg' with
  | None => false
  | Some _ => true
  end.



Lemma vertex_map_of_sections_correct vs m m' :
  vertex_map_of_sections vs m = Some m' ->
  m.(Piso_map) ⊆ m'.(Piso_map) /\
  Forall (λ '(vin, vout),
    prod_map (m'.(Piso_map) !!.) id <$> vin
      ≡ₚ prod_map Some id <$> vout) vs.
Proof.
  revert m m'; induction vs as [|(vin, vout) vs IHvs]; intros m m';
  [intros [= <-]; done|].
  cbn.
  intros (m'' & Hm'' & Hvmap%IHvs)%list_first_omap_Some.
  apply (elem_of_list_fmap_1 Piso_map),
    gmultiset_pre_isos_extending_aux_alt_correct in Hm'' as Hm''_alt.
  pose proof (gmultiset_pre_isos_extending_aux_correct vin vout m) as Hall.
  rewrite Forall_forall in Hall.
  apply Hall in Hm''_alt.
  split.
  - rewrite <- Hvmap.1.
    apply Hm''_alt.
  - constructor; [|apply Hvmap].
    rewrite <- Hm''_alt.2.2.2.2.
    apply eq_reflexivity, list_fmap_ext.
    intros i (k, n) Hi.
    cbn.
    f_equal.
    apply elem_of_list_lookup_2 in Hi as Hi'.
    apply (elem_of_list_fmap_1 (prod_map (m''.(Piso_map) !!.) id)) in Hi'.
    rewrite Hm''_alt.2.2.2.2 in Hi'.
    cbn in Hi'.
    rewrite elem_of_list_fmap in Hi'.
    destruct Hi' as ((k', n') & [= Hm''k <-] & _).
    rewrite Hm''k.
    specialize Hvmap.1.
    now apply lookup_weaken.
Qed.

Lemma vertex_map_of_alignment_correct ktios m m' :
  vertex_map_of_alignment m ktios = Some m' ->
  m.(Piso_map) ⊆ m'.(Piso_map) /\
  Forall (λ '(ktv, ktv'),
    gmultiset_map (m'.(Piso_map) !!.) ktv.2.2
      = gmultiset_map Some (ktv').2.2) ktios.
Proof.
  unfold vertex_map_of_alignment.
  intros Heq%vertex_map_of_sections_correct.
  split; [apply Heq.1|].
  specialize Heq.2 as Hall.
  unfold vertex_sections_of_alignment in Hall.
  apply Forall_app in Hall as [_ Hall].
  rewrite 2 Forall_fmap in Hall.
  apply (Forall_impl _ _ _ Hall).
  intros (ktv, ktv').
  cbn.
  intros Hmap.
  rewrite 2 gmultiset_map_alt_car.
  rewrite Hmap.
  done.
Qed.


(* Lemma compose_PermutationA {A} (R1 R2 : relation A)
  `{HR1 : !Transitive R1, HR2 : !Transitive R2} :
  rel_compose (PermutationA R1) (PermutationA R2) ⊆
  PermutationA (rel_compose R1 R2).
Proof.
  apply relation_subseteq_iff.
  intros l l'' (l' & Hll' & Hl'l'').
  induction Hll'.
  - apply PermutationA_nil in Hl'l'' as ->.
    constructor.
  -



Lemma PermutationA_commute {A} (R1 R2 : relation A) :
  rel_compose R1 R2 ⊆ rel_compose R2 R1 ->
  rel_compose (PermutationA R2) (PermutationA R1)
  ⊆ rel_compose (PermutationA R1) (PermutationA R2).
Proof.
  intros HR12.
  apply relation_subseteq_iff.
  intros l l'' (l' & Hll' & Hl'l'').



Lemma PermutationA_compose {A} (R1 R2 : relation A)
  `{HR1 : !Transitive R1, HR2 : !Transitive R2} l l' :
  PermutationA (rel_compose R1 R2) l l' ->
  rel_compose (PermutationA R1) (PermutationA R2) l l'.
Proof.
  intros Hl.
  induction Hl; [unfold rel_compose; eauto using PermutationA|
  |unfold rel_compose; eauto using PermutationA|].
  - firstorder idtac.
    unfold rel_compose.
    eauto using PermutationA.
  - eapply rel_compose_trans; eauto using PermutationA.

    constructor.


  unfold rel_compose in *; firstorder (eauto using PermutationA)].
  firstorder idtac.
  unfold rel_compose; eauto using PermutationA.
  unfold rel_compose in *. *)





Lemma spisomorphic_of_map_to_list_perm {n m}
  (mv : Pmap positive) (cohg cohg' : CospanSPHyperGraph T n m) :
  vertices cohg ⊆ dom mv ->
  map_inj mv ->
  set_map (mv !!!.) cohg.(sphedges).(sphypervertices) = cohg'.(sphedges).(sphypervertices) ->
  PermutationA (rel_preimage snd eq)
  (prod_map id (prod_map id (gmultiset_map (mv !!!.))) <$>
    map_to_list cohg.(sphedges).(sphyperedges))
    (map_to_list cohg'.(sphedges).(sphyperedges)) ->
  vmap (mv !!!.) cohg.(spinputs) = cohg'.(spinputs) ->
  vmap (mv !!!.) cohg.(spoutputs) = cohg'.(spoutputs) ->
  spisomorphic cohg cohg'.
Proof.
  intros Hdom Hinj Hvs Hes Hins Houts.

  apply (PermutationA_decompose _) in Hes as Hes'.
  destruct Hes' as (es' & Hes'perm & Hes'eq).

  set (mhe := (list_to_map (zip es'.*1
    (map_to_list cohg'.(sphedges).(sphyperedges)).*1) :> Pmap positive)).

  apply eqlistA_length in Hes'eq as Hlen.

  assert (Hdome : dom mhe = dom cohg.(sphedges).(sphyperedges)). 1:{
    unfold mhe.
    apply leibniz_equiv_iff.
    rewrite dom_list_to_map.
    rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
    rewrite <- Hes'perm.
    rewrite fsts_prod_map, list_fmap_id.
    symmetry.
    apply dom_alt.
  }

  assert (Hinje : map_inj mhe). 1:{
    apply map_inj_list_to_map.
    - rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
      rewrite <- Hes'perm.
      rewrite fsts_prod_map, list_fmap_id.
      apply NoDup_fst_map_to_list.
    - rewrite snd_zip by now rewrite 2 length_fmap, Hlen.
      apply NoDup_fst_map_to_list.
  }

  eapply (spisomorphic_of_partial_inj_dom' _ _
    (mv !!!.) (mhe !!!.)).
  - intros i j [mvi Hmvi]%Hdom%elem_of_dom [mvj Hmvj]%Hdom%elem_of_dom.
    rewrite 2 lookup_total_alt, Hmvi, Hmvj.
    cbn.
    intros <-.
    eapply Hinj; eauto.
  - rewrite <- Hdome.
    intros i j [mvi Hmvi]%elem_of_dom [mvj Hmvj]%elem_of_dom.
    rewrite 2 lookup_total_alt, Hmvi, Hmvj.
    cbn.
    intros <-.
    eapply Hinje; eauto.
  - symmetry.
    apply cosphg_ext; [|done..].
    cbn.
    apply sphg_ext; [|done].
    cbn.
    unfold kmap.
    rewrite <- list_to_map_fmap.
    etransitivity; [|apply list_to_map_to_list].
    symmetry.
    apply list_to_map_proper; [apply NoDup_fst_map_to_list|].
    symmetry.
    transitivity (prod_map (mhe !!!.) id <$>
      (prod_map id (prod_map id (gmultiset_map (mv !!!.))) <$>
      map_to_list cohg.(sphedges).(sphyperedges))).
    1:{
      rewrite <- 2 list_fmap_compose.
      done.
    }
    rewrite Hes'perm.
    apply eq_reflexivity.
    apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap|].
    intros i [k tv] [k' tv'] Hi.
    rewrite list_lookup_fmap.

    apply eqlistA_altdef in Hes'eq.
    rewrite Forall2_lookup in Hes'eq.
    destruct (es' !! i) as [es'i|] eqn:Hes'i; [cbn|done].
    destruct (map_to_list _ !! i) as [mi|] eqn:Hmi; [cbn|done].
    intros [= <- <-] [= Hmieq].
    specialize (Hes'eq i).
    rewrite Hes'i, Hmi in Hes'eq.
    rewrite <- option_relation_Forall2 in Hes'eq.
    cbn in Hes'eq.
    hnf in Hes'eq.
    rewrite Hes'eq, Hmieq.
    f_equal.
    apply lookup_total_correct.
    apply elem_of_list_to_map.
    1:{
      rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
      rewrite <- Hes'perm.
      rewrite fsts_prod_map, list_fmap_id.
      apply NoDup_fst_map_to_list.
    }
    apply elem_of_list_lookup.
    exists i.
    rewrite lookup_zip_Some.
    rewrite 2 list_lookup_fmap, Hes'i, Hmi, Hmieq.
    done.
Qed.

Lemma spequiv_of_map_to_list_perm_equiv `{Equivalence T equiv} {n m}
  (mv : Pmap positive) (cohg cohg' : CospanSPHyperGraph T n m) :
  vertices cohg ⊆ dom mv ->
  map_inj mv ->
  set_map (mv !!!.) cohg.(sphedges).(sphypervertices) = cohg'.(sphedges).(sphypervertices) ->
  PermutationA (rel_preimage snd equiv)
  (prod_map id (prod_map id (gmultiset_map (mv !!!.))) <$>
    map_to_list cohg.(sphedges).(sphyperedges))
    (map_to_list cohg'.(sphedges).(sphyperedges)) ->
  vmap (mv !!!.) cohg.(spinputs) = cohg'.(spinputs) ->
  vmap (mv !!!.) cohg.(spoutputs) = cohg'.(spoutputs) ->
  cohg ≡ cohg'.
Proof.
  intros Hdom Hinj Hvs Hes Hins Houts.

  apply (PermutationA_decompose _) in Hes as Hes'.
  destruct Hes' as (es' & Hes'perm & Hes'eq).

  set (mhe := (list_to_map (zip es'.*1
    (map_to_list cohg'.(sphedges).(sphyperedges)).*1) :> Pmap positive)).

  apply eqlistA_length in Hes'eq as Hlen.

  assert (Hdome : dom mhe = dom cohg.(sphedges).(sphyperedges)). 1:{
    unfold mhe.
    apply leibniz_equiv_iff.
    rewrite dom_list_to_map.
    rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
    rewrite <- Hes'perm.
    rewrite fsts_prod_map, list_fmap_id.
    symmetry.
    apply dom_alt.
  }

  assert (Hinje : map_inj mhe). 1:{
    apply map_inj_list_to_map.
    - rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
      rewrite <- Hes'perm.
      rewrite fsts_prod_map, list_fmap_id.
      apply NoDup_fst_map_to_list.
    - rewrite snd_zip by now rewrite 2 length_fmap, Hlen.
      apply NoDup_fst_map_to_list.
  }
  transitivity (mk_cosphg (mk_sphg (list_to_map $ zip_with (λ e mc,
    (mc.1, (e.2.1, mc.2.2))) es' (map_to_list cohg'.(sphedges).(sphyperedges)))
    cohg'.(sphedges).(sphypervertices)) cohg'.(spinputs) cohg'.(spoutputs)).
  2:{
    apply cosphg_eq_subrelation.
    apply mk_cosphg_eq; [done..|].
    cbn.
    split; [|done].
    cbn.
    rewrite <- (list_to_map_to_list (sphyperedges _)) at 2.
    apply map_equiv_map_relation.
    apply map_relation_list_to_map.
    apply Forall2_lookup.
    intros i.
    rewrite eqlistA_altdef, Forall2_lookup in Hes'eq.
    rewrite lookup_zip_with.
    induction (Hes'eq i) as [x y Hxy|]; [|done].
    cbn.
    constructor.
    cbn.
    split; [done|].
    split; [|done].
    apply Hxy.
  }
  apply spisomorphic_subrelation.
  eapply (spisomorphic_of_partial_inj_dom' _ _
    (mv !!!.) (mhe !!!.)).
  - intros i j [mvi Hmvi]%Hdom%elem_of_dom [mvj Hmvj]%Hdom%elem_of_dom.
    rewrite 2 lookup_total_alt, Hmvi, Hmvj.
    cbn.
    intros <-.
    eapply Hinj; eauto.
  - rewrite <- Hdome.
    intros i j [mvi Hmvi]%elem_of_dom [mvj Hmvj]%elem_of_dom.
    rewrite 2 lookup_total_alt, Hmvi, Hmvj.
    cbn.
    intros <-.
    eapply Hinje; eauto.
  - symmetry.
    apply cosphg_ext; [|done..].
    cbn.
    apply sphg_ext; [|done].
    cbn.
    unfold kmap.
    rewrite <- list_to_map_fmap.
    etransitivity; [|apply list_to_map_to_list].
    symmetry.
    apply list_to_map_proper; [apply NoDup_fst_map_to_list|].
    symmetry.
    transitivity (prod_map (mhe !!!.) id <$>
      (prod_map id (prod_map id (gmultiset_map (mv !!!.))) <$>
      map_to_list cohg.(sphedges).(sphyperedges))).
    1:{
      rewrite <- 2 list_fmap_compose.
      done.
    }
    rewrite map_to_list_to_map. 2:{
      rewrite fmap_zip_with.
      cbn.
      rewrite zip_with_to_fmap_r by done.
      apply NoDup_fst_map_to_list.
    }
    rewrite Hes'perm.
    apply eq_reflexivity.
    apply (fun H => list_eq_same_length _ _ _ H eq_refl);
    [now rewrite length_fmap, length_zip_with; lia|].
    rewrite length_fmap.
    intros i [k tv] [k' tv'] Hi.
    rewrite list_lookup_fmap.

    apply eqlistA_altdef in Hes'eq.
    rewrite Forall2_lookup in Hes'eq.
    rewrite lookup_zip_with.
    destruct (es' !! i) as [es'i|] eqn:Hes'i; [cbn|done].
    destruct (map_to_list _ !! i) as [mi|] eqn:Hmi; [cbn|done].
    intros [= <- <-] [= Hmi1 Htv'].
    specialize (Hes'eq i).
    rewrite Hes'i, Hmi in Hes'eq.
    rewrite <- option_relation_Forall2 in Hes'eq.
    cbn in Hes'eq.
    hnf in Hes'eq.
    f_equal.
    + apply lookup_total_correct.
      apply elem_of_list_to_map.
      1:{
        rewrite fst_zip by now rewrite 2 length_fmap, Hlen.
        rewrite <- Hes'perm.
        rewrite fsts_prod_map, list_fmap_id.
        apply NoDup_fst_map_to_list.
      }
      apply elem_of_list_lookup.
      exists i.
      rewrite lookup_zip_Some.
      rewrite 2 list_lookup_fmap, Hes'i, Hmi.
      cbn.
      rewrite Hmi1.
      done.
    + rewrite (surjective_pairing es'i.2).
      rewrite <- Htv'.
      f_equal.
      apply Hes'eq.2.
Qed.


Lemma spequiv_of_map_to_list_perm_equiv' `{Equivalence T equiv} {n m}
  (mv : Pmap positive) (cohg cohg' : CospanSPHyperGraph T n m) :
  vertices cohg ⊆ dom mv ->
  map_inj mv ->
  set_map (mv !!.) cohg.(sphedges).(sphypervertices) =@{gset _}
    set_map Some cohg'.(sphedges).(sphypervertices) ->
  PermutationA (rel_preimage snd (prod_relation equiv eq))
  (prod_map id (prod_map id (gmultiset_map (mv !!.))) <$>
    map_to_list cohg.(sphedges).(sphyperedges))
  (prod_map id (prod_map id (gmultiset_map Some)) <$>
    map_to_list cohg'.(sphedges).(sphyperedges)) ->
  vmap (mv !!.) cohg.(spinputs) = vmap Some cohg'.(spinputs) ->
  vmap (mv !!.) cohg.(spoutputs) = vmap Some cohg'.(spoutputs) ->
  cohg ≡ cohg'.
Proof.
  intros Hdom Hinj Hvs Hes Hins Houts.
  apply (spequiv_of_map_to_list_perm_equiv mv).
  - done.
  - done.
  - apply (f_equal (set_map (D:=Pset) (default inhabitant))) in Hvs.
    rewrite 2 set_map_compose_L in Hvs.
    rewrite set_map_id_L in Hvs.
    apply Hvs.
  - eapply (fmap_PermutationA (RB:=rel_preimage snd equiv)
      (prod_map id (prod_map id (gmultiset_map (default inhabitant))))) in Hes.
    2:{
      unfold rel_preimage.
      intros x y Hxy.
      simpl.
      split; [apply Hxy.1|].
      simpl.
      f_equal.
      apply Hxy.2.
    }
    rewrite <- 2 list_fmap_compose in Hes.
    unfold compose in Hes.
    simpl in Hes.
    erewrite list_fmap_ext in Hes by now intros; rewrite gmultiset_map_compose.
    etransitivity; [apply Hes|].

    erewrite (list_fmap_ext _ _
      (map_to_list cohg'.(sphedges).(sphyperedges))) by
      now intros; rewrite gmultiset_map_compose, gmultiset_map_id.
    now rewrite list_fmap_id' by now intros (? & ? & ?).
  - specialize (f_equal (vmap (default inhabitant)) Hins).
    rewrite 2 Vector.map_map, Vector.map_id.
    now intros <-.
  - specialize (f_equal (vmap (default inhabitant)) Houts).
    rewrite 2 Vector.map_map, Vector.map_id.
    now intros <-.
Qed.


Lemma spreferrenced_vertices_set_spverts {n m} (cohg : CospanSPHyperGraph T n m)
  vs : spreferrenced_vertices (set_spverts cohg vs) = spreferrenced_vertices cohg.
Proof.
  done.
Qed.

Lemma spreferrenced_vertices_relabel_spgraph f {n m} (cohg : CospanSPHyperGraph T n m) :
  spreferrenced_vertices (relabel_spgraph f cohg) = set_map f (spreferrenced_vertices cohg).
Proof.
  unfold spreferrenced_vertices; cbn.
  rewrite set_map_union_L, set_map_list_to_set_L.
  f_equal; [now rewrite 2 vec_to_list_map, fmap_app|].
  rewrite set_map_list_to_set_L.
  rewrite map_to_list_fmap.
  rewrite list_fmap_bind, list_bind_fmap.
  apply set_eq.
  intros k.
  rewrite 2 elem_of_list_to_set, 2 elem_of_list_bind.
  apply exists_iff.
  intros ktio.
  simpl.
  rewrite elements_gmultiset_map.
  done.
Qed.

Lemma spreferrenced_vertices_reindex_spgraph f `{Hf : !Inj eq eq f} {n m} (cohg : CospanSPHyperGraph T n m) :
  spreferrenced_vertices (reindex_spgraph f cohg) = spreferrenced_vertices cohg.
Proof.
  unfold spreferrenced_vertices; cbn.
  f_equal.
  rewrite (map_to_list_kmap _).
  rewrite list_fmap_bind.
  done.
Qed.

Lemma spisomorphic_of_set_spverts_empty_isomorphic `{Equivalence T equiv} {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  size (spisolated_vertices cohg) = size (spisolated_vertices cohg') ->
  spisomorphic (set_spverts cohg ∅) (set_spverts cohg' ∅) ->
  spisomorphic (norm_spverts cohg) (norm_spverts cohg').
Proof.
  intros Hverts.
  intros (fv & fe & Hfv & Hfe & Heq)%spisomorphic_exists.
  apply (size_set_eq_exists_map (M:=Pmap)) in Hverts as Hmv'.
  destruct Hmv' as (mv' & Hdommv' & Himgmv' & Hinj).

  assert (Himgfv : forall v, v ∈ spreferrenced_vertices cohg ->
    fv v ∈ spreferrenced_vertices cohg'). 1:{
    intros v Hv.
    apply (f_equal spreferrenced_vertices) in Heq.
    rewrite spreferrenced_vertices_set_spverts in Heq.
    rewrite Heq.
    rewrite spreferrenced_vertices_relabel_spgraph,
      (spreferrenced_vertices_reindex_spgraph _).
    rewrite spreferrenced_vertices_set_spverts.
    now apply elem_of_map_2.
  }

  eapply (spisomorphic_of_partial_inj_dom' _ _
    (λ i, default (fv i) (mv' !! i)) fe).
  - intros i j.
    rewrite vertices_decomp, 2 elem_of_union.
    rewrite spisolated_vertices_norm_spverts, spreferrenced_vertices_norm_spverts.
    intros [Hii|Hir];
    [apply Hdommv' in Hii as Hmi;
    apply elem_of_dom in Hmi as [mi Hmi];
    rewrite Hmi; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmi as Hmii;
    rewrite Himgmv' in Hmii
    |replace (mv' !! i) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%spisolated_referrenced_disjoint);
     cbn;
     specialize (Himgfv i Hir) as Hfir];
    (intros [Hji|Hjr];
    [apply Hdommv' in Hji as Hmj;
    apply elem_of_dom in Hmj as [mj Hmj];
    rewrite Hmj; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmj as Hmji;
    rewrite Himgmv' in Hmji
    |replace (mv' !! j) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%spisolated_referrenced_disjoint);
     cbn;
     specialize (Himgfv j Hjr) as Hfjr]).
    + intros <-.
      revert Hmi Hmj.
      apply Hinj.
    + intros ->.
      now apply spisolated_referrenced_disjoint in Hmii.
    + intros <-.
      now apply spisolated_referrenced_disjoint in Hmji.
    + apply Hfv.
  - intros ? ? ? ?; apply Hfe.
  - apply cosphg_ext; [apply sphg_ext|..].
    + cbn.
      etransitivity; [apply (f_equal (sphyperedges ∘ sphedges) Heq)|].
      cbn.
      apply map_fmap_ext.
      intros _ tv (i & -> & Hitv)%(lookup_kmap_Some _).
      apply pair_eq, conj; [done|].
      apply gmultiset_map_ext.
      intros v Hv.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (spisolated_referrenced_disjoint cohg) _ _).
      apply elem_of_map_to_list in Hitv.
      unfold spreferrenced_vertices.
      apply elem_of_union_r.
      apply elem_of_list_to_set.
      apply elem_of_list_bind.
      exists (i, tv).
      rewrite gmultiset_elem_of_elements.
      done.
    + cbn.
      apply leibniz_equiv_iff in Hdommv', Himgmv'.
      rewrite <- Hdommv', <- Himgmv'.
      apply set_eq.
      intros k.
      clear.
      set_unfold.
      rewrite elem_of_map_img.
      setoid_rewrite elem_of_dom.
      apply exists_iff.
      intros i.
      split; [now intros ->|].
      now intros [-> [? ->]].
    + cbn.
      etransitivity; [apply (f_equal spinputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (spisolated_referrenced_disjoint cohg) _ _).
      unfold spreferrenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      now apply elem_of_app; left.
    + cbn.
      etransitivity; [apply (f_equal spoutputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (spisolated_referrenced_disjoint cohg) _ _).
      unfold spreferrenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      now apply elem_of_app; right.
Qed.


Lemma set_spverts_set_spverts {n m} (cohg : CospanSPHyperGraph T n m)
  vs vs' : set_spverts (set_spverts cohg vs) vs' = set_spverts cohg vs'.
Proof.
  done.
Qed.

Lemma spisolated_vertices_set_spverts_spisolated_vertices
  {n m} (cohg : CospanSPHyperGraph T n m) :
  spisolated_vertices (set_spverts cohg (spisolated_vertices cohg)) =
  spisolated_vertices cohg.
Proof.
  unfold spisolated_vertices at 1 2.
  cbn.
  rewrite spreferrenced_vertices_set_spverts.
  unfold spisolated_vertices.
  now rewrite difference_twice_L.
Qed.

Lemma spequiv_of_set_spverts_empty_equiv `{Equivalence T equiv} {n m}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  size (spisolated_vertices cohg) = size (spisolated_vertices cohg') ->
  set_spverts cohg ∅ ≡ set_spverts cohg' ∅ ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  intros Hverts.
  intros (cohg'' & Hiso & Hequiv)%cosphg_equiv_alt.

  transitivity (norm_spverts (
      set_spverts cohg'' (spisolated_vertices cohg'))).
  - replace cohg'' with (set_spverts
    (set_spverts cohg'' (spisolated_vertices cohg')) ∅) in Hiso. 2:{
      apply cosphg_ext; [|done..].
      apply sphg_ext; [done|].
      cbn.
      symmetry.
      now rewrite Hequiv.2.2.2.
    }
    apply spisomorphic_of_set_spverts_empty_isomorphic in Hiso. 2:{
      rewrite Hequiv, set_spverts_set_spverts.
      rewrite Hverts.
      now rewrite spisolated_vertices_set_spverts_spisolated_vertices.
    }
    now rewrite Hiso.
  - rewrite Hequiv.
    apply eq_reflexivity.
    rewrite set_spverts_set_spverts.
    unfold norm_spverts.
    rewrite set_spverts_set_spverts.
    now rewrite spisolated_vertices_set_spverts_spisolated_vertices.
Qed.



Lemma norm_spverts_equiv_of_map_to_list_perm_equiv `{Equivalence T equiv} {n m}
  (mv : Pmap positive) (cohg cohg' : CospanSPHyperGraph T n m) :
  spreferrenced_vertices cohg ⊆ dom mv ->
  map_inj mv ->
  size (spisolated_vertices cohg) = size (spisolated_vertices cohg') ->
  PermutationA (rel_preimage snd (prod_relation equiv eq))
  (prod_map id (prod_map id (gmultiset_map (mv !!.))) <$>
    map_to_list cohg.(sphedges).(sphyperedges))
  (prod_map id (prod_map id (gmultiset_map Some)) <$>
    map_to_list cohg'.(sphedges).(sphyperedges)) ->
  vmap (mv !!.) cohg.(spinputs) = vmap Some cohg'.(spinputs) ->
  vmap (mv !!.) cohg.(spoutputs) = vmap Some cohg'.(spoutputs) ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  intros Hdom Hinj Hverts Hperm Hins Houts.
  apply spequiv_of_set_spverts_empty_equiv; [done|].
  apply (spequiv_of_map_to_list_perm_equiv' mv); [|done..].
  rewrite vertices_decomp.
  rewrite spreferrenced_vertices_set_spverts.
  unfold spisolated_vertices.
  rewrite spreferrenced_vertices_set_spverts.
  cbn -[difference].
  rewrite <- Hdom.
  generalize (spreferrenced_vertices cohg).
  set_solver +.
Qed.



Lemma maybe_vertex_map_correct m ktios ktios' m' :
  maybe_vertex_map m ktios ktios' = Some m' ->
  m.(Piso_map) ⊆ m' /\
  exists ktios'',
  Forall2 (λ ktv ktv',
    ktv.2.1 ≡ ktv'.2.1 /\
    gmultiset_map (m'.(Piso_map)!!.) ktv.2.2 =
    gmultiset_map Some ktv'.2.2) ktios ktios'' /\
    ktios'' ≡ₚ ktios'.
Proof.
  unfold maybe_vertex_map.
  intros (ktioss & Hktios%elem_of_partial_permutations &
    Hm'%vertex_map_of_alignment_correct)%list_first_omap_Some.
  split; [apply Hm'.1|].
  rewrite <- Hktios.2.1.
  exists ktioss.*2.
  split; [|apply Hktios.2.2].
  apply Forall2_fmap, Forall_Forall2_diag.
  eapply Forall_impl; [eapply Forall_and, conj, Hm'.2; apply Hktios.1|].
  intros (ktv, ktv').
  cbn.
  easy.
Qed.


Lemma spgraph_isos_fast_correct {n m} `{Equivalence T equiv}
  (cohg cohg' : CospanSPHyperGraph T n m)
  mv : spgraph_isos_fast cohg cohg' = Some mv ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  unfold spgraph_isos_fast.
  case_decide as Hsize; [|done].
  intros (mv' & Hmv' & Hmaybe)%bind_Some.
  apply maybe_vertex_map_correct in Hmaybe as Hmaybe'.
  destruct Hmaybe' as (Hsubs & (sphe & Hall2 & Hsphe)).
  apply pupdates_correct in Hmv' as Hmv'_alt.
  rewrite zip_with_app, Forall_app in Hmv'_alt by now rewrite 2 length_vec_to_list.
  destruct Hmv'_alt as [Hins Houts].
  apply (norm_spverts_equiv_of_map_to_list_perm_equiv mv).
  - apply subseteq_dom in Hsubs as Hdoms.
    unfold spreferrenced_vertices.
    rewrite union_subseteq.
    split.
    + apply pupdates_correct in Hmv' as Hmv'_alt.
      rewrite Forall_lookup in Hmv'_alt.
      intros v [i Hi]%elem_of_list_to_set%elem_of_list_lookup.
      apply lookup_lt_Some in Hi as Hilt.
      rewrite length_app, 2 length_vec_to_list in Hilt.
      assert (is_Some ((spinputs cohg' ++ spoutputs cohg') !! i)) as
        [v' Hv'] by now rewrite lookup_lt_is_Some, length_app, 2 length_vec_to_list.
      apply elem_of_dom.
      exists v'.
      revert Hsubs.
      apply lookup_weaken.
      apply (Hmv'_alt i (v, v')).
      rewrite lookup_zip_with.
      cbn in Hi.
      rewrite Hi, Hv'.
      done.
    + intros v ([k tvs] & Hv & [i Hktvs]%elem_of_list_lookup
        )%elem_of_list_to_set%elem_of_list_bind.
      rewrite Forall2_lookup in Hall2.
      specialize (Hall2 i).
      cbn in Hktvs.
      rewrite <- option_relation_Forall2, Hktvs in Hall2.
      cbn in Hall2, Hv.
      destruct (sphe !! i) as [tvs'|]; [|done].
      destruct Hall2 as [_ Hall2].
      apply (f_equal elements), (eq_reflexivity (RA:=Permutation)) in Hall2.
      rewrite 2 elements_gmultiset_map in Hall2.
      apply (elem_of_list_fmap_1 (mv.(Piso_map) !!.)) in Hv.
      rewrite Hall2, elem_of_list_fmap in Hv.
      apply elem_of_dom.
      destruct Hv as (y & Hy & _).
      now exists y.
  - apply Piso_map_inj.
  - done.
  - symmetry.
    apply PermutationA_iff_exists_Forall2_Permutation.
    eexists.
    split; [rewrite <- Hsphe; reflexivity|].
    symmetry.
    apply Forall2_fmap.
    apply Hall2.
  - apply vec_eq; intros i.
    rewrite 2 vlookup_map.
    rewrite Forall_lookup in Hins.
    revert Hsubs.
    apply lookup_weaken.
    apply (Hins i (_, _)).
    rewrite lookup_zip_with.
    rewrite 2 lookup_vec_to_list_fin.
    done.
  - apply vec_eq; intros i.
    rewrite 2 vlookup_map.
    rewrite Forall_lookup in Houts.
    revert Hsubs.
    apply lookup_weaken.
    apply (Houts i (_, _)).
    rewrite lookup_zip_with.
    rewrite 2 lookup_vec_to_list_fin.
    done.
Qed.


Lemma spgraph_iso_partial_test_fast_correct {n m} `{Equivalence T equiv}
  (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test_fast cohg cohg' = true ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  unfold spgraph_iso_partial_test_fast.
  case_match; [|done].
  intros _.
  eapply spgraph_isos_fast_correct; eauto.
Qed.





Definition maybe_vertex_map' (m : Piso)
  (ktios ktios' : list (positive * (T * gmultiset positive))) :
  option Piso :=
  first_omap_partial_permutations (λ ktio ktio', ktio.2.1 ≡ ktio'.2.1 /\
      size ktio.2.2 = size ktio'.2.2)
      (vertex_map_of_alignment m) ktios ktios'.


Definition spgraph_isos_fast' {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  option Piso :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    mv ← pupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
    maybe_vertex_map' mv (map_to_list cohg.(sphedges).(sphyperedges))
        (map_to_list cohg'.(sphedges).(sphyperedges))
  else
    None.


Definition spgraph_iso_partial_test_fast' {n m} (cohg cohg' : CospanSPHyperGraph T n m) : bool :=
  match spgraph_isos_fast' cohg cohg' with
  | None => false
  | Some _ => true
  end.

Lemma maybe_vertex_map'_correct m ktios ktios' :
  maybe_vertex_map' m ktios ktios' = maybe_vertex_map m ktios ktios'.
Proof.
  unfold maybe_vertex_map'.
  rewrite first_omap_partial_permutations_correct.
  done.
Qed.

Lemma spgraph_isos_fast'_correct {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_isos_fast' cohg cohg' = spgraph_isos_fast cohg cohg'.
Proof.
  unfold spgraph_isos_fast'.
  unfold spgraph_isos_fast.
  case_decide; [|done].
  apply option_bind_ext; [|done].
  intros mv.
  now rewrite maybe_vertex_map'_correct.
Qed.


Lemma spgraph_iso_partial_test_fast'_correct
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test_fast' cohg cohg' = spgraph_iso_partial_test_fast cohg cohg'.
Proof.
  unfold spgraph_iso_partial_test_fast'.
  now rewrite spgraph_isos_fast'_correct.
Qed.


Fixpoint vertex_map_of_sections''
  (vs : list (list (positive * positive) * list (positive * positive)))
  (m : WPiso) : option WPiso :=
  match vs with
  | [] => Some m
  | (vin, vout) :: vs =>
    list_first_omap (vertex_map_of_sections'' vs)
      $ gmultiset_pre_isos_extending_aux_alt' vin vout m
  end.


Definition vertex_map_of_alignment''
  {T} (m : WPiso) (ktios : list ((positive * (T * gmultiset positive)) *
    (positive * (T * gmultiset positive)))) : option WPiso :=
  vertex_map_of_sections'' (vertex_sections_of_alignment
    ((λ ktio_ktio', (ktio_ktio'.1.2.2, ktio_ktio'.2.2.2)) <$> ktios)) m.

Definition maybe_vertex_map'' `{Equiv T, RelDecision T T equiv}
  (m : WPiso)
  (ktios ktios' : list (positive * (T * gmultiset positive))) :
  option WPiso :=
  first_omap_partial_permutations (λ ktio ktio', ktio.2.1 ≡ ktio'.2.1 /\
      size ktio.2.2 = size ktio'.2.2)
      (vertex_map_of_alignment'' m) ktios ktios'.


Definition spgraph_isos_fast'' `{Equiv T, RelDecision T T equiv}
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  option WPiso :=
  if decide (size (spisolated_vertices cohg) = size (spisolated_vertices cohg')) then
    mv ← wpupdates (zip (cohg.(spinputs) ++ cohg.(spoutputs))
        (cohg'.(spinputs) ++ cohg'.(spoutputs))) ∅;
    maybe_vertex_map'' mv (map_to_list cohg.(sphedges).(sphyperedges))
        (map_to_list cohg'.(sphedges).(sphyperedges))
  else
    None.


Definition spgraph_iso_partial_test_fast'' `{Equiv T, RelDecision T T equiv}
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) : bool :=
  match spgraph_isos_fast'' cohg cohg' with
  | None => false
  | Some _ => true
  end.

Lemma fmap_list_first_omap {A B C} (f : A -> option B) (g : B -> C) l :
  g <$> list_first_omap f l = list_first_omap (fmap g ∘ f) l.
Proof.
  induction l; [done|].
  cbn.
  case_match; cbn; done.
Qed.

Lemma list_first_omap_ext {A B} (f g : A -> option B) (l : list A) :
  (forall a, a ∈ l -> f a = g a) ->
  list_first_omap f l = list_first_omap g l.
Proof.
  rewrite <- Forall_forall.
  intros Hl.
  induction Hl; [done|].
  cbn.
  do 2 case_match; congruence.
Qed.

Lemma vertex_map_of_sections''_correct vs m :
  vertex_map_of_sections'' vs (Piso_to_weak m) =
    Piso_to_weak <$> vertex_map_of_sections vs m.
Proof.
  revert m; induction vs as [|(k, v) vs IHvs]; [done|intros m].
  cbn.
  rewrite gmultiset_pre_isos_extending_aux_alt'_correct.
  rewrite list_first_omap_fmap, fmap_list_first_omap.
  apply list_first_omap_ext.
  intros mv _.
  cbn.
  done.
Qed.

Lemma vertex_map_of_alignment''_correct vs m :
  vertex_map_of_alignment'' (Piso_to_weak m) vs =
    Piso_to_weak <$> vertex_map_of_alignment m vs.
Proof.
  unfold vertex_map_of_alignment''.
  now rewrite vertex_map_of_sections''_correct.
Qed.

Lemma maybe_vertex_map''_correct m ktios ktios' :
  maybe_vertex_map'' (Piso_to_weak m) ktios ktios' =
  Piso_to_weak <$> maybe_vertex_map m ktios ktios'.
Proof.
  rewrite <- maybe_vertex_map'_correct.
  unfold maybe_vertex_map'', maybe_vertex_map'.
  rewrite 2 first_omap_partial_permutations_correct.
  rewrite fmap_list_first_omap.
  apply list_first_omap_ext.
  intros; apply vertex_map_of_alignment''_correct.
Qed.

Lemma spgraph_isos_fast''_correct {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_isos_fast'' cohg cohg' = Piso_to_weak <$> spgraph_isos_fast cohg cohg'.
Proof.
  unfold spgraph_isos_fast''.
  unfold spgraph_isos_fast.
  case_decide; [|done].
  rewrite WPiso_empty_correct.
  rewrite wpupdates_correct, option_fmap_bind, option_bind_fmap.
  apply option_bind_ext; [|done].
  intros mv.
  cbn.
  now rewrite maybe_vertex_map''_correct.
Qed.


Lemma spgraph_iso_partial_test_fast''_correct_aux
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test_fast'' cohg cohg' = spgraph_iso_partial_test_fast cohg cohg'.
Proof.
  rewrite <- spgraph_iso_partial_test_fast'_correct.
  unfold spgraph_iso_partial_test_fast''.
  rewrite spgraph_isos_fast''_correct.
  symmetry.
  unfold spgraph_iso_partial_test_fast'.
  rewrite spgraph_isos_fast'_correct.
  now case_match.
Qed.

Lemma spgraph_iso_partial_test_fast''_correct `{Equivalence T equiv}
  {n m} (cohg cohg' : CospanSPHyperGraph T n m) :
  spgraph_iso_partial_test_fast'' cohg cohg' = true ->
  norm_spverts cohg ≡ norm_spverts cohg'.
Proof.
  rewrite spgraph_iso_partial_test_fast''_correct_aux.
  apply spgraph_iso_partial_test_fast_correct.
Qed.

End dec_equiv.



