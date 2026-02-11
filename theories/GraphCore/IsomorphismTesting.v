Require Export TensorGraph.

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

Lemma Forall_zip_with {A B C} (P : C -> Prop) (f : A -> B -> C)
  (l : list A) (l' : list B) :
  length l = length l' ->
  Forall P (zip_with f l l') <->
  Forall2 (λ a b, P (f a b)) l l'.
Proof.
  intros Hlen%Forall2_same_length.
  induction Hlen; [easy|].
  cbn.
  rewrite Forall_cons, Forall2_cons, IHHlen.
  done.
Qed.

Definition abs_vertices {T} (hg : (HyperEdge T)) : Pset :=
  list_to_set (hg.1.2 ++ hg.2).

Add Parametric Morphism `{SemiSet A SA, !LeibnizEquiv SA} :
  (@union_list SA _ _) with signature
  Permutation ==> eq as union_list_perm_L.
Proof.
  intros l l' Hperm.
  apply set_eq; intros x.
  rewrite 2 elem_of_union_list.
  now setoid_rewrite Hperm.
Qed.

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

Definition hyperedge_map_pre_isos_extending {T} (hg hg' : Pmap (HyperEdge T))
  (ts_mhe_mv : list (T * T) * Pmap positive * Pmap positive) :
  list (list (T*T) * Pmap positive * Pmap positive) :=
  hyperedge_map_pre_isos_extending_aux (map_to_list hg)
    (map_to_list hg') ts_mhe_mv.


Lemma map_relation_insert `{FinMap K M} {A B} P Q R
  (m : M A) (m' : M B) k a b :
  P k a b ->
  map_relation P Q R m m' ->
  map_relation P Q R (<[k := a]> m) (<[k := b]> m').
Proof.
  intros Hab Hrel i.
  rewrite 2 lookup_insert_case.
  case_decide; [now subst|].
  apply Hrel.
Qed.

Lemma map_relation_empty `{FinMap K M} {A B} P Q R :
  map_relation P Q R (∅ :> M A) (∅ :> M B).
Proof.
  intros i.
  now rewrite 2 lookup_empty.
Qed.

Lemma map_relation_list_to_map `{FinMap K M} {A B} P Q R
  (l : list (K * A)) (l' : list (K * B)) :
  Forall2 (λ ka kb, ka.1 = kb.1 /\ P ka.1 ka.2 kb.2) l l' ->
  map_relation P Q R (list_to_map l :> M A) (list_to_map l' :> M B).
Proof.
  intros Halls.
  induction Halls as [|(k, a) (k', b) l l' [[= <-] Hab]]; [apply map_relation_empty|].
  cbn.
  now apply map_relation_insert.
Qed.

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

Definition referrenced_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  Pset :=
  list_to_set (cohg.(inputs) ++ cohg.(outputs))
    ∪ list_to_set (map_to_list cohg.(hedges).(hyperedges)
     ≫= λ k_flu, k_flu.2.1.2 ++ k_flu.2.2).

Definition isolated_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  Pset :=
  cohg.(hedges).(hypervertices)
    ∖ referrenced_vertices cohg.

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

Lemma list_to_set_bind `{SemiSet B SB} {A} (f : A -> list B) (l : list A) :
  list_to_set (l ≫= f) ≡@{SB} ⋃ (list_to_set ∘ f <$> l).
Proof.
  intros x.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite elem_of_union_list.
  setoid_rewrite elem_of_list_fmap.
  cbn.
  split.
  - intros (y & Hx & Hy).
    eexists.
    split; [exists y; split; [reflexivity|done]|].
    now rewrite elem_of_list_to_set.
  - intros (? & (? & -> & ?) & Hx%elem_of_list_to_set).
    eauto.
Qed.

Lemma list_to_set_bind_L `{SemiSet B SB, !LeibnizEquiv SB} {A}
  (f : A -> list B) (l : list A) :
  list_to_set (l ≫= f) =@{SB} ⋃ (list_to_set ∘ f <$> l).
Proof.
  unfold_leibniz.
  apply list_to_set_bind.
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

Lemma size_set_eq_exists_map `{FinMapDom K M SK,
  !Elements K SK, !FinSet K SK, FinSet A SA}
  (X : SK) (Y : SA) :
  size X = size Y ->
  exists (m : M A),
    dom m ≡ X /\
    map_img m ≡ Y /\
    forall i j a,
      m !! i = Some a -> m !! j = Some a -> i = j.
Proof.
  intros Hsize.
  exists (list_to_map (zip (elements X) (elements Y))).
  split_and!.
  - rewrite dom_list_to_map, fst_zip by apply eq_reflexivity, Hsize.
    apply list_to_set_elements.
  - rewrite map_img_list_to_map by now
      rewrite fst_zip by apply eq_reflexivity, Hsize;
      apply NoDup_elements.
    rewrite snd_zip by apply eq_reflexivity, symmetry, Hsize.
    apply list_to_set_elements.
  - intros i j a Hi Hj.
    rewrite <- elem_of_list_to_map in Hi, Hj by now
      rewrite fst_zip by apply eq_reflexivity, Hsize;
      apply NoDup_elements.
    rewrite elem_of_list_lookup in Hi, Hj.
    destruct Hi as (ii & Hii).
    destruct Hj as (ij & Hij).
    rewrite lookup_zip_with in Hii, Hij.
    destruct (elements X !! ii) as [Xii|] eqn:HXii; [|done].
    destruct (elements X !! ij) as [Xij|] eqn:HXij; [|done].
    destruct (elements Y !! ii) as [Yii|] eqn:HYii; [|done].
    destruct (elements Y !! ij) as [Yij|] eqn:HYij; [|done].
    cbn in *.
    revert Hii Hij.
    intros [= -> ->] [= -> ->].
    enough (ii = ij) by congruence.
    revert HYii HYij.
    apply NoDup_lookup, NoDup_elements.
Qed.

Lemma Pmap_map_inj_on (X : Pset) (m : Pmap positive) :
  X ⊆ dom m ->
  (forall i j a, m !! i = Some a -> m !! j = Some a -> i = j) ->
  (forall i j, i ∈ X -> j ∈ X -> Pmap_map m i = Pmap_map m j -> i = j).
Proof.
  intros HX Hminj i j [mi Hmi]%HX%elem_of_dom [mj Hmj]%HX%elem_of_dom.
  unfold Pmap_map.
  rewrite Hmi, Hmj.
  cbn.
  intros <-.
  eauto.
Qed.

Lemma map_disjoint_union_inj `{FinMap K M} {A} (m m' : M A) :
  m ##ₘ m' ->
  (forall i j a, m !! i = Some a -> m !! j = Some a -> i = j) ->
  (forall i j a, m' !! i = Some a -> m' !! j = Some a -> i = j) ->
  (forall i j a, m !! i = Some a -> m' !! j = Some a -> False) ->
  (forall i j a, (m ∪ m') !! i = Some a -> (m ∪ m') !! j = Some a -> i = j).
Proof.
  intros Hmm' Hm Hm' Himg.
  intros i j a.
  rewrite map_disjoint_alt in Hmm'.
  specialize (Hmm' i) as Hi.
  specialize (Hmm' j) as Hj.
  rewrite 2 lookup_union.
  destruct (m !! i) eqn:Hmi, (m' !! i) eqn:Hm'i; [now destruct Hi|..|easy];
  destruct (m !! j) eqn:Hmj, (m' !! j) eqn:Hm'j; [now destruct Hj|..|easy];
  cbn;
  intros [= ->] [= ->];
  solve [eauto|exfalso; eauto].
Qed.

Lemma vertices_decomp {T n m} (cohg : CospanHyperGraph T n m) :
  vertices cohg = isolated_vertices cohg ∪ referrenced_vertices cohg.
Proof.
  unfold vertices, isolated_vertices.
  rewrite difference_union_L.
  unfold vertices_hg, referrenced_vertices.
  apply set_eq.
  intros ?.
  rewrite 4 elem_of_union; tauto.
Qed.

Lemma isolated_referrenced_disjoint {T n m} (cohg : CospanHyperGraph T n m) :
  isolated_vertices cohg ## referrenced_vertices cohg.
Proof.
  unfold isolated_vertices.
  now apply disjoint_difference_l1.
Qed.

Definition set_verts {T n m} (cohg : CospanHyperGraph T n m)
  (vs : Pset) : CospanHyperGraph T n m :=
  mk_cohg (mk_hg cohg.(hedges).(hyperedges) vs) cohg.(inputs) cohg.(outputs).

Definition norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  CospanHyperGraph T n m := set_verts cohg (isolated_vertices cohg).

Lemma referrenced_vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  referrenced_vertices (norm_verts cohg) = referrenced_vertices cohg.
Proof.
  reflexivity.
Qed.

Lemma isolated_vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  isolated_vertices (norm_verts cohg) = isolated_vertices cohg.
Proof.
  unfold isolated_vertices.
  cbn.
  unfold isolated_vertices.
  rewrite referrenced_vertices_norm_verts.
  apply difference_twice_L.
Qed.


Lemma vertices_norm_verts {T n m} (cohg : CospanHyperGraph T n m) :
  vertices (norm_verts cohg) = vertices cohg.
Proof.
  now rewrite 2 vertices_decomp,
    isolated_vertices_norm_verts, referrenced_vertices_norm_verts.
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



Definition graph_iso_conditions {T n m}
  (cohg cohg' : CospanHyperGraph T n m) : list (list (T * T)) :=
  omap (λ '(ts, _, mv),
    if decide (size mv = size (map_img mv :> Pset)) then
      Some ts
    else None) (graph_pre_isos cohg cohg').

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
  








