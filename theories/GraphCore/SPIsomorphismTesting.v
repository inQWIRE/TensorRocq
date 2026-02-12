Require Export SPTensorGraph.

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

Fixpoint mayzip {A B} (l : list A) (l' : list B) : option (list (A * B)) :=
  match l, l' with
  | [], [] => Some []
  | a :: l, b :: l' => ((a,b)::.) <$> mayzip l l'
  | _, _ => None
  end.

Lemma mayzip_Some {A B} (l : list A) (l' : list B) ll :
  mayzip l l' = Some ll <->
  length l = length l' /\ ll = zip l l'.
Proof.
  revert l' ll; induction l as [|a l IHl]; intros [|b l'];
  [cbn; clear; naive_solver|easy..|].
  intros [|(a', b') ll]; [split; [|easy]; cbn; now destruct (mayzip _ _)|].
  cbn.
  rewrite fmap_Some.
  setoid_rewrite IHl.
  clear.
  naive_solver.
Qed.

Lemma mayzip_is_Some {A B} (l : list A) (l' : list B) :
  is_Some (mayzip l l') <-> length l = length l'.
Proof.
  unfold is_Some.
  setoid_rewrite mayzip_Some.
  naive_solver.
Qed.

Lemma mayzip_fmap_l {A B C} (f : A -> B) (l : list A) (l' : list C) :
  mayzip (f <$> l) l' = (fmap (M:=list) (prod_map f id)) <$> mayzip l l'.
Proof.
  apply option_eq.
  intros ll.
  rewrite mayzip_Some.
  rewrite length_fmap.
  rewrite fmap_Some.
  setoid_rewrite mayzip_Some.
  rewrite zip_fmap_l.
  naive_solver.
Qed.

Lemma mayzip_fmap_r {A B C} (f : B -> C) (l : list A) (l' : list B) :
  mayzip l (f <$> l') = (fmap (M:=list) (prod_map id f)) <$> mayzip l l'.
Proof.
  apply option_eq.
  intros ll.
  rewrite mayzip_Some.
  rewrite length_fmap.
  rewrite fmap_Some.
  setoid_rewrite mayzip_Some.
  rewrite zip_fmap_r.
  naive_solver.
Qed.

Definition extend_posmap_one k v (m : Pmap positive) : option (Pmap positive) :=
  match m !! k with
  | None => Some (<[k := v]> m)
  | Some v' =>
    if decide (v = v') then
      Some m
    else
      None
  end.

Lemma extend_posmap_one_Some k v m m' :
  extend_posmap_one k v m = Some m' ->
  m ⊆ m' /\
  m' !! k = Some v /\
  dom m' = dom m ∪ {[k]}.
Proof.
  unfold extend_posmap_one.
  destruct (m !! k) as [mk|] eqn:Hmk.
  - case_decide as Heq; [|done].
    intros [= <-].
    subst mk.
    split; [done|].
    split; [done|].
    apply elem_of_dom_2 in Hmk.
    set_solver.
  - intros [= <-].
    split; [now apply insert_subseteq|].
    split; [now rewrite lookup_insert|].
    rewrite dom_insert_L.
    apply union_comm_L.
Qed.


Fixpoint extend_posmap (l : list (positive * positive))
  (m : Pmap positive) : option (Pmap positive) :=
  match l with
  | [] => Some m
  | kv :: l =>
    match m !! kv.1 with
    | None => extend_posmap l (<[kv.1 := kv.2]> m)
    | Some v' =>
      if decide (kv.2 = v') then
        extend_posmap l m
      else
        None
    end
  end.

Lemma extend_posmap_cons k v l m :
  extend_posmap ((k, v) :: l) m =
  extend_posmap_one k v m ≫= extend_posmap l.
Proof.
  cbn.
  unfold extend_posmap_one.
  now case_match; [case_decide|].
Qed.

Lemma extend_posmap_Some l m m' :
  extend_posmap l m = Some m' ->
  m ⊆ m' /\
  Forall (λ kv, m' !! kv.1 = Some kv.2) l /\
  dom m' = dom m ∪ list_to_set l.*1 /\
  map_img m' =@{Pset} map_img m ∪ list_to_set l.*2.
Proof.
  revert m; induction l as [|(k,v) l IHl]; intros m.
  - cbn.
    intros [= <-].
    split; [done|].
    split; [constructor|].
    now rewrite 2 union_empty_r_L.
  - cbn -[union].
    destruct (m !! k) as [mk|] eqn:Hmk.
    + case_decide as Hvk; [|done].
      subst mk.
      intros (Hm & Hall & Hdom & Himg)%IHl.
      split; [done|].
      split; [constructor; [|done];
        revert Hm; now apply lookup_weaken|].
      rewrite Hdom, Himg.
      rewrite 2 union_assoc_L.
      split; f_equal;
      [apply elem_of_dom_2 in Hmk|
      apply (elem_of_map_img_2 (SA:=Pset)) in Hmk];
      set_solver +Hmk.
    + intros (Hm & Hall & Hdom & Himg)%IHl.
      split; [rewrite <- Hm; now apply insert_subseteq|].
      split; [|split; [apply leibniz_equiv_iff; rewrite Hdom, dom_insert;
        intros x; rewrite 4 elem_of_union; tauto|
        apply leibniz_equiv_iff; rewrite Himg, map_img_insert,
          delete_notin by done; intros x; rewrite 4 elem_of_union; tauto]].
      constructor; [|done].
      cbn.
      revert Hm.
      apply lookup_weaken, lookup_insert.
Qed.


Lemma extend_posmap_Some' l m m' :
  extend_posmap l m = Some m' ->
  m ⊆ m' /\
  Forall2 (λ k v, m' !! k = Some v) l.*1 l.*2 /\
  dom m' = dom m ∪ list_to_set l.*1.
Proof.
  intros (Hm & Hall & Hdom & Himg)%extend_posmap_Some.
  split; [done|].
  split; [|done].
  rewrite Forall2_lookup.
  rewrite Forall_lookup in Hall.
  intros i.
  rewrite 2 list_lookup_fmap.
  destruct (l !! i) as [li|] eqn:Hli; [|constructor].
  cbn.
  constructor.
  now apply (Hall i).
Qed.


Lemma extend_posmap_Some_fmap l m m' :
  extend_posmap l m = Some m' ->
  (m' !!.) <$> l.*1 = Some <$> l.*2.
Proof.
  intros (Hm & Heq & Hdom)%extend_posmap_Some.
  rewrite <- 2 list_fmap_compose.
  apply list_fmap_ext.
  intros _ (k, v) Hkv%elem_of_list_lookup_2.
  rewrite Forall_forall in Heq.
  now apply Heq in Hkv.
Qed.

Lemma extend_posmap_app l l' m :
  extend_posmap (l ++ l') m =
  extend_posmap l m ≫= extend_posmap l'.
Proof.
  revert m; induction l as [|(k, v) l IHl]; intros m; [done|].
  cbn -[extend_posmap].
  rewrite 2 extend_posmap_cons.
  destruct (extend_posmap_one _ _ _); [|done].
  cbn.
  apply IHl.
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


Definition gmultiset_pre_isos_extending (hg hg' : gmultiset positive)
  (m : Pmap positive) : list (Pmap positive) :=
  gmultiset_pre_isos_extending_aux (map_to_list hg.(gmultiset_car))
    (map_to_list hg'.(gmultiset_car)) m.

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
    now rewrite Hperm.
  - done.
  - rewrite Hdom.
    f_equal.
    apply leibniz_equiv_iff.
    replace hg with (GMultiSet hg.(gmultiset_car)) at 2 by now destruct hg.
    unfold dom, gmultiset_dom.
    rewrite dom_alt.
    rewrite set_map_list_to_set, list_fmap_id.
    done.
  - rewrite Himg.
    f_equal.
    apply leibniz_equiv_iff.
    replace hg' with (GMultiSet hg'.(gmultiset_car)) at 2 by now destruct hg'.
    unfold dom, gmultiset_dom.
    rewrite dom_alt.
    rewrite set_map_list_to_set, list_fmap_id.
    done.
  - rewrite 2 gmultiset_map_alt_car.
    now rewrite Hperm.
Qed.

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


(* Lemma sphyperedge_map_pre_isos_extending_aux_correct' {T} hg hg' ts_mhe_mv :
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
    ) (@sphyperedge_map_pre_isos_extending_aux T hg hg' ts_mhe_mv). *)

Definition sphyperedge_map_pre_isos_extending {T} (hg hg' : Pmap (SPHyperEdge T))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T*T) * Pmap positive * Pmap positive) :=
  sphyperedge_map_pre_isos_extending_aux (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.


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

Definition spreferrenced_vertices {T n m} (cosphg : CospanSPHyperGraph T n m) :
  Pset :=
  list_to_set (cosphg.(spinputs) ++ cosphg.(spoutputs))
    ∪ list_to_set (map_to_list (cosphg.(sphedges).(sphyperedges)) ≫=
    λ k_flu : (positive*(SPHyperEdge T)), (elements k_flu.2.2)).

Definition spisolated_vertices {T n m} (cosphg : CospanSPHyperGraph T n m) :
  Pset :=
  cosphg.(sphedges).(sphypervertices)
    ∖ spreferrenced_vertices cosphg.

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

Lemma vertices_decomp {T n m} (cosphg : CospanSPHyperGraph T n m) :
  vertices cosphg = spisolated_vertices cosphg ∪ spreferrenced_vertices cosphg.
Proof.
  unfold vertices, spisolated_vertices.
  rewrite difference_union_L.
  unfold vertices_sphg, spreferrenced_vertices.
  apply set_eq.
  intros ?.
  rewrite 4 elem_of_union; tauto.
Qed.

Lemma isolated_referrenced_disjoint {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spisolated_vertices cosphg ## spreferrenced_vertices cosphg.
Proof.
  unfold spisolated_vertices.
  now apply disjoint_difference_l1.
Qed.

Definition set_spverts {T n m} (cosphg : CospanSPHyperGraph T n m)
  (vs : Pset) : CospanSPHyperGraph T n m :=
  mk_cosphg (mk_sphg cosphg.(sphedges).(sphyperedges) vs) cosphg.(spinputs) cosphg.(spoutputs).

Definition norm_verts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  CospanSPHyperGraph T n m := set_spverts cosphg (spisolated_vertices cosphg).

Lemma spreferrenced_vertices_norm_verts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spreferrenced_vertices (norm_verts cosphg) = spreferrenced_vertices cosphg.
Proof.
  reflexivity.
Qed.

Lemma spisolated_vertices_norm_verts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  spisolated_vertices (norm_verts cosphg) = spisolated_vertices cosphg.
Proof.
  unfold spisolated_vertices.
  cbn.
  unfold spisolated_vertices.
  rewrite spreferrenced_vertices_norm_verts.
  apply difference_twice_L.
Qed.


Lemma vertices_norm_verts {T n m} (cosphg : CospanSPHyperGraph T n m) :
  vertices (norm_verts cosphg) = vertices cosphg.
Proof.
  now rewrite 2 vertices_decomp,
    spisolated_vertices_norm_verts, spreferrenced_vertices_norm_verts.
Qed.

Lemma spgraph_pre_isos_correct {T n m} (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ '(ts, mhe, mv),
    Forall (uncurry eq) ts ->
    size (dom mv :> Pset) = size (map_img mv :> Pset) ->
    spisomorphic (norm_verts cosphg) (norm_verts cosphg'))
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
    apply isolated_referrenced_disjoint.
  }
  eapply (spisomorphic_of_partial_inj_dom' _ _
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
        intros Href%isolated_referrenced_disjoint; apply Href.
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



Definition spgraph_iso_conditions {T n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) : list (list (T * T)) :=
  omap (λ '(ts, _, mv),
    if decide (size mv = size (map_img mv :> Pset)) then
      Some ts
    else None) (spgraph_pre_isos cosphg cosphg').

Lemma spgraph_iso_conditions_correct_aux {T n m}
  (cosphg cosphg' : CospanSPHyperGraph T n m) :
  Forall (λ ts, ts.*1 = ts.*2 ->
    spisomorphic (norm_verts cosphg) (norm_verts cosphg'))
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
  spisomorphic (norm_verts cosphg) (norm_verts cosphg').
Proof.
  case_match eqn:Hmi; [|done].
  apply elem_of_list_lookup_2 in Hmi.
  revert Hmi.
  refine ((Forall_forall (λ ts, ts.*1 = ts.*2 -> _) _).1 _ _).
  apply spgraph_iso_conditions_correct_aux.
Qed.









