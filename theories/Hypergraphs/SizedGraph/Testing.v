From TensorRocq Require Import Isomorphism.Testing Isomorphism.IsoAux SizedGraph.Definitions.

Definition restrict_map `{ElemOf K SK, !RelDecision (∈@{SK}), Filter (K * A) MA}
  (d : SK) (m : MA) : MA :=
  filter (λ ka, ka.1 ∈ d) m.


Lemma lookup_restrict_map `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k :
  restrict_map d m !! k = _ ← guard (k ∈ d); m !! k.
Proof.
  unfold restrict_map.
  rewrite map_lookup_filter.
  cbn.
  rewrite option_bind_comm.
  apply option_bind_ext, reflexivity.
  intros Hk.
  apply bind_with_Some.
Qed.

Lemma lookup_restrict_map_Some `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k a :
  restrict_map d m !! k = Some a <-> m !! k = Some a /\ k ∈ d.
Proof.
  rewrite lookup_restrict_map.
  rewrite bind_Some.
  split; [naive_solver|case_guard; naive_solver].
Qed.

Lemma lookup_restrict_map_is_Some `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k :
  is_Some (restrict_map d m !! k) <-> is_Some (m !! k) /\ k ∈ d.
Proof.
  unfold is_Some.
  setoid_rewrite lookup_restrict_map_Some.
  naive_solver.
Qed.

Lemma lookup_restrict_map_None `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k :
  restrict_map d m !! k = None <-> m !! k = None \/ k ∉ d.
Proof.
  rewrite lookup_restrict_map.
  case_guard; [|naive_solver].
  cbn.
  naive_solver.
Qed.

Lemma lookup_restrict_map_not_elem_None `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k :
  k ∉ d -> restrict_map d m !! k = None.
Proof.
  rewrite lookup_restrict_map_None; auto.
Qed.

Lemma lookup_restrict_map_elem `{FinMap K M, ElemOf K SK, !RelDecision (∈@{SK})}
  {A} (d : SK) (m : M A) k :
  k ∈ d -> restrict_map d m !! k = m !! k.
Proof.
  rewrite lookup_restrict_map.
  case_guard; easy.
Qed.

Lemma dom_restrict_map `{FinMapDom K M D, !RelDecision (∈@{D})}
  {A} (d : D) (m : M A) :
  dom (restrict_map d m) ≡ d ∩ dom m.
Proof.
  intros x.
  rewrite elem_of_intersection, 2 elem_of_dom.
  rewrite lookup_restrict_map_is_Some.
  naive_solver.
Qed.

Lemma dom_restrict_map_L `{FinMapDom K M D, !RelDecision (∈@{D}), !LeibnizEquiv D}
  {A} (d : D) (m : M A) :
  dom (restrict_map d m) = d ∩ dom m.
Proof.
  apply leibniz_equiv_iff, dom_restrict_map.
Qed.

Lemma lookup_kmap_None' `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) {A} (m : M1 A) (k : K2) :
  (kmap f m :> M2 A) !! k = None <->
  forall l, is_Some (m !! l) -> f l <> k.
Proof.
  induction m using map_first_key_ind.
  - rewrite kmap_empty.
    setoid_rewrite lookup_empty.
    setoid_rewrite is_Some_alt.
    naive_solver.
  - rewrite kmap_insert_first_key by done.
    rewrite lookup_insert_None.
    setoid_rewrite lookup_insert_is_Some'.
    rewrite IHm.
    naive_solver congruence.
Qed.

Lemma kmap_union_full_gen_dom `{FinMapDom K1 M1 SK1, FinMap K2 M2}
  (f : K1 -> K2) {A} (m m' : M1 A) :
  set_Forall2 (fun i j => f i = f j -> i = j) (dom m ∪ dom m') ->
  kmap f (m ∪ m') =@{M2 A} kmap f m ∪ kmap f m'.
Proof.
  intros Hf.
  apply map_eq; intros i.
  rewrite lookup_union.
  apply option_eq; intros a.
  rewrite lookup_kmap_Some_full_gen_dom by now rewrite dom_union.
  rewrite union_Some.
  rewrite lookup_kmap_Some_full_gen_dom
    by (eapply set_Forall2_mono, Hf; [done| apply union_subseteq_l]).
  rewrite lookup_kmap_Some_full_gen_dom
    by (eapply set_Forall2_mono, Hf; [done| apply union_subseteq_r]).
  rewrite lookup_kmap_None'.
  setoid_rewrite lookup_union.
  setoid_rewrite union_Some.
  split.
  - intros (j & Hmj & <-).
    destruct Hmj as [|[Hmj Hm'j]]; [eauto|].
    right.
    split; [|eauto].
    intros l Hl%elem_of_dom.
    intros ->%Hf.
    + now apply not_elem_of_dom in Hmj.
    + now apply elem_of_union_l.
    + apply elem_of_dom_2 in Hm'j.
      now apply elem_of_union_r.
  - intros [(j & Hmj & <-)|[Hfj (j & Hm'j & <-)]]; [eauto|].
    exists j.
    split; [|done].
    right.
    split; [|done].
    apply eq_None_not_Some.
    now intros Hj%Hfj.
Qed.

Lemma kmap_restrict_map `{FinMapDom K1 M1 SK1, Elements K1 SK1, !FinSet K1 SK1,
  FinMap K2 M2, SemiSet K2 SK2}
  `{!RelDecision (∈@{SK1}), !RelDecision (∈@{SK2})}
  (f : K1 -> K2) (d : SK1) {A} (m : M1 A) :
  set_Forall2 (fun i j => f i = f j -> i = j) (d ∪ dom m) ->
  kmap f (restrict_map d m) =@{M2 A} restrict_map (set_map f d :> SK2) (kmap f m).
Proof.
  intros Hf.
  apply map_eq; intros i.
  apply option_eq; intros a.
  rewrite lookup_restrict_map_Some.
  rewrite lookup_kmap_Some_full_gen_dom.
  2:{
    rewrite dom_restrict_map.
    eapply set_Forall2_mono, Hf; [done|apply union_subseteq_l', intersection_subseteq_l].
  }
  setoid_rewrite lookup_restrict_map_Some.
  rewrite lookup_kmap_Some_full_gen_dom.
  2:{
    eapply set_Forall2_mono, Hf; [done|apply union_subseteq_r].
  }
  split.
  - intros (j & [Hmj Hid] & <-).
    split; [|now apply elem_of_map_2].
    eauto.
  - intros [(j & Hmj & <-) (j' & Hfj' & Hj')%elem_of_map].
    apply Hf in Hfj' as <-.
    + eauto.
    + apply elem_of_dom_2 in Hmj.
      now apply elem_of_union_r.
    + now apply elem_of_union_l.
Qed.



Lemma scohg_vert_eq_alt' {N T n m} (cohg cohg' : SizedCospanHyperGraph N T n m) :
  cohg ≡ᵥ cohg' <->
  inputs cohg = inputs cohg' /\
  outputs cohg = outputs cohg' /\
  hyperedges cohg = cohg' /\
  isolated_vertices cohg = isolated_vertices cohg' /\
  forall v, v ∈ vertices cohg ->
  cohg.(sized_map) !! v = cohg'.(sized_map) !! v.
Proof.
  rewrite scohg_vert_eq_alt.
  apply and_iff_from_l; [done|]; intros Hins _.
  apply and_iff_from_l; [done|]; intros Houts _.
  apply and_iff_from_l; [done|]; intros Hhg _.
  apply and_iff_from_l; [done|]; intros Hiso _.
  replace (_ ∪ _) with (vertices cohg); [done|].
  rewrite <- (union_idemp_L (vertices cohg)) at 1.
  f_equal.
  rewrite 2 vertices_decomp.
  f_equal; [done|].
  rewrite 2 referenced_vertices_decomp.
  f_equal; [congruence|].
  unfold referenced_vertices_hg.
  now rewrite Hhg.
Qed.

#[export] Instance referenced_vertices_hg_equiv `{Equiv T} :
  Proper (rel_preimage hyperedges (≡) ==> (=)) (@referenced_vertices_hg T).
Proof.
  intros hg hg' Hhg%map_to_list_equiv.
  unfold referenced_vertices_hg.
  induction Hhg as [|? ? ? ? Ha]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L _ (_ ≫= _)).
  f_equal; [|done].
  f_equal.
  f_equal; apply Ha.
Qed.


Definition scohg_equiv_alt {N} `{Equiv T, Equivalence T equiv} {n m}
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ scohg' <-> scohg.(inputs) = scohg'.(inputs) /\ scohg.(outputs) = scohg'.(outputs) /\
    isolated_vertices scohg = isolated_vertices scohg' /\ hyperedges scohg ≡ hyperedges scohg' /\
    forall v, v ∈ vertices scohg -> scohg.(sized_map) !! v = scohg'.(sized_map) !! v.
Proof.
  rewrite scohg_equiv_alt_rel.
  split.
  - intros (scohg1 & Hheq & Hveq).
    split_and!.
    + rewrite Hheq.1.1.
      now apply scohg_vert_eq_alt in Hveq.
    + rewrite Hheq.1.2.1.
      now apply scohg_vert_eq_alt in Hveq.
    + erewrite isolated_vertices_cohg_eq by apply Hheq.
      now apply scohg_vert_eq_alt in Hveq.
    + specialize (f_equal (hyperedges ∘ hedges) Hveq.1).
      cbn.
      intros <-.
      apply Hheq.
    + erewrite vertices_cohg_eq by apply Hheq.
      rewrite Hheq.2.
      now apply scohg_vert_eq_alt' in Hveq.
  - intros (Hins & Houts & Hiso & Hhg & Hm).
    set (scohg'' := (mk_scohg (mk_cohg (mk_hg (hyperedges scohg') (hypervertices scohg))
      scohg.(inputs) scohg.(outputs) ) (scohg.(sized_map)))).
    exists scohg''.
    split.
    + split; [|done].
      split_and!; [done..|].
      split; [|done].
      apply Hhg.
    + rewrite scohg_vert_eq_alt'.
      split_and!; [done..| |].
      * rewrite <- Hiso.
        unfold isolated_vertices.
        f_equal.
        rewrite 2 referenced_vertices_decomp.
        f_equal.
        now apply referenced_vertices_hg_equiv.
      * intros v Hv; apply Hm.
        revert Hv.
        revert v.
        change (vertices scohg'' ⊆ vertices scohg).
        apply eq_reflexivity.
        rewrite 2 vertices_vertices_hg_decomp.
        f_equal.
        rewrite 2 vertices_hg_decomp.
        f_equal.
        symmetry.
        apply referenced_vertices_hg_equiv.
        done.
Qed.

Definition set_sized_verts {N T n m} (scohg : SizedCospanHyperGraph N T n m)
  (v : Pset) : SizedCospanHyperGraph N T n m :=
  mk_scohg (set_verts scohg v) (restrict_map (vertices (set_verts scohg v))
    scohg.(sized_map)).

Lemma set_sized_verts_scohg_vert_eq {N T n m} (v : Pset)
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  v ⊆ vertices scohg ->
  scohg ≡ᵥ scohg' ->
  set_sized_verts scohg v ≡ᵥ set_sized_verts scohg' v.
Proof.
  intros Hv [Heq Hsm].
  apply (set_verts_cohg_vert_eq v) in Heq.
  split; [apply Heq|].
  cbn.
  rewrite 2 vertices_set_verts.
  intros k Hk'.
  assert (Hk : k ∈ vertices scohg). 1:{
    apply elem_of_union in Hk' as [Hk' | Hk'%Hv]; [|done].
    rewrite vertices_decomp.
    now apply elem_of_union_r.
  }
  apply Hsm in Hk.
  apply (f_equal referenced_vertices) in Heq.
  rewrite 2 referenced_vertices_norm_verts, 2 referenced_vertices_set_verts in Heq.
  rewrite <- Heq.
  rewrite 2 lookup_restrict_map.
  rewrite <- Hk.
  done.
Qed.

Lemma set_sized_verts_scohg_vert_eq_alt {N T n m} (v : Pset)
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' ->
  (scohg ≡ᵥ scohg' -> forall x, x ∈ v -> scohg.(sized_map) !! x = scohg'.(sized_map) !! x) ->
  set_sized_verts scohg v ≡ᵥ set_sized_verts scohg' v.
Proof.
  intros Heq Hv.
  specialize (Hv Heq).
  destruct Heq as [Heq Hsm].
  apply (f_equal referenced_vertices) in Heq as Heqv.
  rewrite 2 referenced_vertices_norm_verts in Heqv.

  apply (set_verts_cohg_vert_eq v) in Heq.
  split; [apply Heq|].
  cbn.
  rewrite 2 vertices_set_verts.
  rewrite <- Heqv.
  intros k Hk'.
  apply elem_of_union in Hk' as [Hk' | Hk'%Hv].
  - rewrite 2 lookup_restrict_map_elem by now apply elem_of_union_l.
    apply Hsm.
    rewrite vertices_decomp.
    now apply elem_of_union_r.
  - rewrite 2 lookup_restrict_map.
    rewrite <- Hk'.
    done.
Qed.


(* FIXME: MOve *)
Lemma map_inj_insert_gen `{FinMap K M} {A} (m : M A) k a :
  (forall k', m !! k' <> Some a) ->
  map_inj m -> map_inj (<[k := a]> m).
Proof.
  intros Ha Hm l l' b.
  rewrite 2 lookup_insert_case.
  repeat case_decide; [congruence..|].
  apply Hm.
Qed.

Lemma map_inj_insert_img `{FinMap K M, SemiSet A SA} (m : M A) k a :
  a ∉@{SA} map_img m ->
  map_inj m -> map_inj (<[k := a]> m).
Proof.
  intros Ha; apply map_inj_insert_gen.
  now rewrite not_elem_of_map_img in Ha.
Qed.

Lemma map_inj_empty `{FinMap K M} {A} : map_inj (∅ :> M A).
Proof.
  intros ? ? ?.
  now rewrite lookup_empty.
Qed.

Lemma not_elem_of_fst_map_to_list `{FinMap K M} {A} (m : M A) (k : K) :
  k ∉ (map_to_list m).*1 <-> m !! k = None.
Proof.
  destruct (m !! k) as [a|] eqn:Hma.
  - split; [|easy].
    apply elem_of_map_to_list, (elem_of_list_fmap_1 fst) in Hma.
    easy.
  - split; [easy|].
    intros _.
    rewrite not_elem_of_list_fmap.
    intros [k' a] Hk'%elem_of_map_to_list.
    cbn; congruence.
Qed.

Lemma set_fmap_perm_eq_exists_map_aux `{FinMap A M} {B} (f g : A -> B)
  (l l' : list A) : NoDup l -> NoDup l' -> f <$> l ≡ₚ g <$> l' ->
  exists (m : M A), (m!!.) <$> l ≡ₚ Some <$> l' /\ map_inj m /\
    (map_to_list m).*1 ≡ₚ l /\ (map_to_list m).*2 ≡ₚ l' /\
    map_Forall (fun k k' => f k = g k') m.
Proof.
  intros Hl; revert l'.
  induction Hl as [|a l Hal Hl IHl].
  - intros l' ? ->%symmetry%Permutation_nil_r%fmap_nil_inv.
    exists ∅.
    split; [done|].
    split; [apply map_inj_empty|].
    rewrite map_to_list_empty.
    split; [done|].
    split; [done|].
    apply map_Forall_empty.
  - intros l' Hl' Hll'.
    cbn in Hll'.
    apply Permutation_cons_inv_l in Hll' as (gl'1 & gl'2 & Hgl' & Hfl).
    apply fmap_app_inv in Hgl' as (l1' & [|b l2'] & -> & [= Hab ->] & ->).
    fold (g <$> l2') in Hfl.
    rewrite <- Permutation_middle, NoDup_cons in Hl'.
    destruct Hl' as (Hb & Hl').
    rewrite <- fmap_app in Hfl.
    apply IHl in Hfl; [|done].
    destruct Hfl as (m & Hml & Hminj & Hm1 & Hm2 & Hmall).
    exists (<[a := b]> m).
    split_and!.
    * rewrite fmap_app.
      cbn.
      rewrite <- Permutation_middle.
      rewrite lookup_insert.
      constructor.
      rewrite <- fmap_app, <- Hml.
      apply eq_reflexivity.
      apply list_fmap_ext.
      intros _ a' Ha'%elem_of_list_lookup_2.
      apply lookup_insert_ne; set_solver + Ha' Hal.
    * apply map_inj_insert_gen, Hminj.
      intros k' Hmk'%elem_of_map_to_list%(elem_of_list_fmap_1 snd).
      rewrite Hm2 in Hmk'.
      now apply Hb.
    * rewrite map_to_list_insert; [constructor; apply Hm1|].
      apply not_elem_of_fst_map_to_list.
      now rewrite Hm1.
    * rewrite <- Permutation_middle.
      rewrite map_to_list_insert; [constructor; apply Hm2|].
      apply not_elem_of_fst_map_to_list.
      now rewrite Hm1.
    * now apply map_Forall_insert_2.
Qed.


Lemma set_fmap_perm_eq_exists_map `{FinMap A M, FinSet A SA} {B} (f g : A -> B)
  (l l' : SA) : f <$> elements l ≡ₚ g <$> elements l' ->
  exists (m : M A), (m!!.) <$> elements l ≡ₚ Some <$> elements l' /\ map_inj m /\
    (map_to_list m).*1 ≡ₚ elements l /\ (map_to_list m).*2 ≡ₚ elements l' /\
    map_Forall (fun k k' => f k = g k') m.
Proof.
  intros Hll'.
  apply set_fmap_perm_eq_exists_map_aux, Hll'; apply NoDup_elements.
Qed.


Lemma set_fmap_perm_eq_exists_map' `{FinMapDom A M SA, Elements A SA,
  !FinSet A SA, !LeibnizEquiv SA} {B} (f g : A -> B)
  (l l' : SA) : f <$> elements l ≡ₚ g <$> elements l' ->
  exists (m : M A), (m!!.) <$> elements l ≡ₚ Some <$> elements l' /\
    map_inj m /\
    dom m = l /\ map_img m = l' /\
    map_Forall (fun k k' => f k = g k') m.
Proof.
  intros (m & Hml & Hminj & Hdom & Himg & Hall)%set_fmap_perm_eq_exists_map.
  exists m.
  split_and!; try done.
  - apply leibniz_equiv_iff.
    now rewrite dom_alt, Hdom, list_to_set_elements.
  - apply leibniz_equiv_iff.
    now rewrite map_img_alt, Himg, list_to_set_elements.
Qed.

#[export] Instance scohg_equiv_syntactic_eq
  {N} `{Equiv T, Equivalence T equiv} {n m} : subrelation (≡@{SizedCospanHyperGraph N T n m}) scohg_syntactic_eq.
Proof.
  intros scohg scohg' Heq%scohg_equiv_alt'_rel.
  rewrite <- norm_sized_verts_vert_eq, Heq, norm_sized_verts_vert_eq.
  done.
Qed.

Lemma scohg_vert_eq_set_verts_isolated_verts {N T n m}
  (scohg : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ set_sized_verts scohg (isolated_vertices scohg).
Proof.
  split.
  - apply cohg_vert_eq_set_verts_isolated_vertices.
  - cbn.
    intros v Hv.
    rewrite vertices_set_verts.
    rewrite union_comm_L, <- vertices_decomp.
    now rewrite lookup_restrict_map_elem by done.
Qed.

Lemma scohg_vert_eq_set_verts_isolated_verts_norm_sized_verts {N T n m}
  (scohg : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ set_sized_verts (norm_sized_verts scohg) (isolated_vertices scohg).
Proof.
  rewrite <- isolated_vertices_norm_verts.
  rewrite <- (norm_sized_verts_vert_eq scohg) at 1.
  rewrite scohg_vert_eq_set_verts_isolated_verts at 1.
  done.
Qed.

Lemma map_extension_inj `{FinMapDom K M D} `{SemiSet A SA} (f : K -> A) (m : M A)
  (d : D) : map_inj m -> set_Forall2 (fun k l => f k = f l -> k = l) (d ∖ dom m) ->
    set_Forall (fun k => f k ∉@{SA} map_img m) (d ∖ dom m) ->
    set_Forall2 (fun k l => default (f k) (m !! k) = default (f l) (m !! l) -> k = l) d.
Proof.
  intros Hminj Hfinj Hfdisj k l Hk Hl.
  destruct (m !! k) as [mk|] eqn:Hmk, (m !! l) as [ml|] eqn:Hml; cbn.
  - intros <-.
    eapply Hminj; eauto.
  - intros ->.
    exfalso.
    apply (Hfdisj l).
    + apply not_elem_of_dom in Hml.
      now apply elem_of_difference.
    + apply elem_of_map_img; eauto.
  - intros <-.
    exfalso.
    apply (Hfdisj k).
    + apply not_elem_of_dom in Hmk.
      now apply elem_of_difference.
    + apply elem_of_map_img; eauto.
  - apply Hfinj.
    + apply not_elem_of_dom in Hmk.
      now apply elem_of_difference.
    + apply not_elem_of_dom in Hml.
      now apply elem_of_difference.
Qed.

(* FIXME: Move *)
Lemma referenced_vertices_alt_vertices {T n m} (cohg : CospanHyperGraph T n m) :
  referenced_vertices cohg = vertices cohg ∖ isolated_vertices cohg.
Proof.
  rewrite isolated_vertices_alt_vertices.
  rewrite difference_difference_r_L.
  rewrite difference_diag_L, union_empty_l_L.
  symmetry.
  rewrite intersection_comm_L.
  apply subseteq_intersection_L.
  rewrite vertices_decomp.
  apply union_subseteq_r.
Qed.

(* FIXME: Move *)
Lemma restrict_map_union_l `{Set_ K SK, !RelDecision (∈@{SK}), FinMap K M}
  (X Y : SK) {A} (m : M A) :
  restrict_map (X ∪ Y) m = restrict_map X m ∪ restrict_map Y m.
Proof.
  unfold restrict_map.
  rewrite <- map_filter_or.
  apply map_filter_ext.
  set_unfold; done.
Qed.

Lemma restrict_map_restrict_map `{Set_ K SK, !RelDecision (∈@{SK}), FinMap K M}
  (X Y : SK) {A} (m : M A) :
  restrict_map X (restrict_map Y m) = restrict_map (X ∩ Y) m.
Proof.
  apply map_eq; intros i.
  apply option_eq; intros a.
  rewrite 3 lookup_restrict_map_Some.
  rewrite elem_of_intersection.
  tauto.
Qed.

Lemma restrict_map_restrict_map_subseteq `{Set_ K SK, !RelDecision (∈@{SK}), FinMap K M}
  (X Y : SK) {A} (m : M A) :
  X ⊆ Y ->
  restrict_map X (restrict_map Y m) = restrict_map X m.
Proof.
  intros HXY.
  apply map_eq; intros i.
  apply option_eq; intros a.
  rewrite 3 lookup_restrict_map_Some.
  set_solver.
Qed.

Lemma sized_map_norm_sized_verts {N T n m} (scohg : SizedCospanHyperGraph N T n m) :
  sized_map (norm_sized_verts scohg) = restrict_map (vertices scohg) scohg.(sized_map).
Proof.
  done.
Qed.

Lemma scohg_syntactic_eq_of_set_sized_verts_empty_scohg_syntactic_eq
  {N} `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : SizedCospanHyperGraph N T n m) :
  (cohg.(sized_map) !!.) <$> elements (isolated_vertices cohg) ≡ₚ
    (cohg'.(sized_map) !!.) <$> elements (isolated_vertices cohg') ->
  (set_sized_verts cohg ∅) ≡ₛ (set_sized_verts cohg' ∅) ->
  cohg ≡ₛ cohg'.
Proof.
  intros Hverts.
  intros (cohg'' & fv & fe & Hfv & Hfe & Hheq & Heq)%scohg_syntactic_eq_exists.
  apply (set_fmap_perm_eq_exists_map' (M:=Pmap)) in Hverts as Hmv'.
  destruct Hmv' as (mv' & Hmv'isol & Hmv'inj & Hdommv' & Himgmv' & Hmv'all).

  assert (Himgfv : forall v, v ∈ referenced_vertices cohg ->
    fv v ∈ referenced_vertices cohg'). 1:{
    intros v Hv.
    apply (f_equal (referenced_vertices ∘ sized_cospan)) in Heq.
    cbn in Heq.
    rewrite referenced_vertices_set_verts in Heq.
    rewrite Heq.
    rewrite referenced_vertices_relabel_graph,
      (referenced_vertices_reindex_graph _).
    rewrite <- referenced_vertices_norm_verts.
    erewrite <- referenced_vertices_cohg_eq by apply Hheq.1.
    cbn.
    rewrite referenced_vertices_norm_verts.
    rewrite referenced_vertices_set_verts.
    now apply elem_of_map_2.
  }

  (* refine ((elem_of_relation (_, _)).1 _). *)

  (* rewrite cohg_syntactic_eq_alt. *)
  (* apply elem_of_relation. *)
  (* cbn. *)

  assert (Hrefvert : referenced_vertices cohg = referenced_vertices cohg''). 1:{
    rewrite <- (referenced_vertices_norm_verts cohg'').
    erewrite <- (referenced_vertices_cohg_eq_Proper _ (norm_verts _)) by apply Hheq.1.
    cbn.
    rewrite referenced_vertices_norm_verts.
    rewrite referenced_vertices_set_verts.
    done.
  }

  transitivity (mk_scohg (set_verts cohg'' (isolated_vertices cohg))
    (restrict_map (referenced_vertices cohg'') (sized_map cohg'')
      ∪ restrict_map (isolated_vertices cohg) cohg.(sized_map))).
  1:{
    apply (subrel' equiv).
    apply scohg_equiv_alt.
    split_and!; [apply Hheq.1..| | |].
    - cbn.
      rewrite isolated_vertices_set_verts.
      rewrite <- Hrefvert.
      symmetry.
      apply difference_twice_L.
    - apply Hheq.1.2.2.
    - cbn.
      intros v.
      rewrite <- Hrefvert.
      rewrite vertices_decomp.
      rewrite lookup_union.
      intros [Hvisol|Hvref]%elem_of_union.
      + pose proof Hvisol as Hvisol'.
        unfold isolated_vertices in Hvisol'.
        apply elem_of_difference in Hvisol' as [Hvhyp Hvnref].
        rewrite lookup_restrict_map_not_elem_None by done.
        rewrite lookup_restrict_map_elem by done.
        now rewrite (left_id_L None _).
      + rewrite lookup_restrict_map_elem by done.
        rewrite lookup_restrict_map_not_elem_None by set_solver + Hvref.
        rewrite (right_id_L None _).
        pose proof Hheq.2 as Hrw.
        rewrite 2 sized_map_norm_sized_verts in Hrw.
        cbn in Hrw.
        rewrite restrict_map_restrict_map_subseteq in Hrw by done.

        apply (f_equal (.!!v)) in Hrw.
        revert Hrw.
        rewrite vertices_set_verts.
        rewrite union_empty_r_L.
        rewrite lookup_restrict_map_elem by done.
        rewrite lookup_restrict_map_elem by
          (rewrite Hrefvert in Hvref; rewrite vertices_decomp; now apply elem_of_union_r).
        done.
  }

  rewrite (scohg_vert_eq_set_verts_isolated_verts_norm_sized_verts cohg').
  apply (subrel' sized_isomorphic).
  assert (Hextinj :
    set_Forall2 (fun i j =>
    default (fv i) (mv' !! i) = default (fv j) (mv' !! j) → i = j)
    (vertices cohg)). 1:{
    refine (map_extension_inj (SA:=Pset) _ _ _ _ _ _).
    + done.
    + intros ? ? ? ?; apply Hfv.
    + rewrite Hdommv'.
      rewrite <- referenced_vertices_alt_vertices.
      intros k Hk%Himgfv.
      rewrite Himgmv'.
      apply not_elem_of_difference.
      now right.
  }
  eapply (sized_isomorphic_of_partial_inj_dom' _ _
    (λ i, default (fv i) (mv' !! i)) fe).
  - unfold sized_vertices.
    cbn.
    rewrite vertices_set_verts.
    rewrite <- Hrefvert.
    rewrite (union_comm_L _ (isolated_vertices _)), <- vertices_decomp.
    rewrite dom_union_L.
    rewrite 2 dom_restrict_map_L.
    pose proof (vertices_decomp cohg) as Hvertcohg.
    intros i j Hi' Hj'.
    assert (Hi : i ∈ vertices cohg) by (rewrite Hvertcohg in *; set_solver + Hi').
    assert (Hj : j ∈ vertices cohg) by (rewrite Hvertcohg in *; set_solver + Hj').
    clear Hi' Hj'.
    apply Hextinj; done.
  - intros ? ? ? ?; apply Hfe.
  - apply scohg_ext; [apply cohg_ext; [apply hg_ext|..]|].
    + cbn.
      apply (f_equal (hyperedges ∘ hedges ∘ sized_cospan)) in Heq.
      cbn in Heq.
      rewrite Heq.
      rewrite <- 2 kmap_fmap'.
      f_equal.
      apply map_fmap_ext.
      intros i tio Hitio.
      apply relabel_abs_ext_strong.
      intros v Hv.
      rewrite (not_elem_of_dom _ _).1; [done|].
      rewrite Hdommv'.
      apply not_elem_of_difference.
      right.
      rewrite Hrefvert.
      apply elem_of_map_to_list in Hitio.
      apply elem_of_app in Hv.
      set_solver + Hitio Hv.
    + cbn.
      unfold set_map.
      rewrite <- (list_to_set_elements_L (isolated_vertices cohg')).
      apply list_to_set_perm_L.
      symmetry.
      transitivity (default xH ∘ (mv' !!.) <$> (elements (isolated_vertices cohg))).
      * apply eq_reflexivity.
        apply list_fmap_ext.
        intros _ v Hv%elem_of_list_lookup_2%elem_of_elements.
        cbn.
        rewrite <- Hdommv', elem_of_dom in Hv.
        now destruct Hv as [? ->].
      * rewrite list_fmap_compose, Hmv'isol.
        rewrite <- list_fmap_compose.
        apply eq_reflexivity, list_fmap_id.
    + cbn.
      apply (f_equal (inputs ∘ sized_cospan)) in Heq.
      cbn in Heq.
      rewrite Heq.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext.
      intros _ v Hv%elem_of_list_lookup_2.
      rewrite (not_elem_of_dom _ _).1; [done|].
      rewrite Hdommv'.
      apply not_elem_of_difference; right.
      rewrite Hrefvert.
      set_solver + Hv.
    + cbn.
      apply (f_equal (outputs ∘ sized_cospan)) in Heq.
      cbn in Heq.
      rewrite Heq.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext.
      intros _ v Hv%elem_of_list_lookup_2.
      rewrite (not_elem_of_dom _ _).1; [done|].
      rewrite Hdommv'.
      apply not_elem_of_difference; right.
      rewrite Hrefvert.
      set_solver + Hv.
    + cbn.
      rewrite <- Hrefvert.
      rewrite kmap_union_full_gen_dom.
      2:{
        rewrite 2 dom_restrict_map_L.
        eapply set_Forall2_mono, Hextinj; [done|].
        rewrite vertices_decomp, union_comm_L.
        apply union_mono; apply intersection_subseteq_l.
      }
      change (filter _ _) with (restrict_map (vertices cohg') cohg'.(sized_map)).
      rewrite vertices_set_verts, referenced_vertices_norm_verts.
      rewrite union_comm_L, <- vertices_decomp.
      rewrite restrict_map_restrict_map_subseteq by done.

      rewrite (kmap_ext _ fv (restrict_map (referenced_vertices _) _)).
      2:{
        intros k a [_ Hk]%lookup_restrict_map_Some.
        rewrite (not_elem_of_dom _ _).1; [done|].
        rewrite Hdommv'.
        apply not_elem_of_difference.
        now right.
      }
      rewrite (kmap_restrict_map (SK2 := Pset)) by (intros ? ? ? ?; apply Hfv).
      apply (f_equal (referenced_vertices ∘ sized_cospan)) in Heq as Heqrv.
      cbn in Heqrv.
      rewrite referenced_vertices_set_verts, referenced_vertices_relabel_graph,
        (referenced_vertices_reindex_graph _) in Heqrv.
      rewrite vertices_decomp.
      rewrite union_comm_L.
      rewrite restrict_map_union_l.
      rewrite Heqrv.
      rewrite <- Hrefvert.

      apply (f_equal sized_map) in Heq as Heqm.
      cbn in Heqm.
      rewrite vertices_set_verts, union_empty_r_L in Heqm.
      rewrite Heqrv in Heqm.
      rewrite <- Heqm, <- Hrefvert, restrict_map_restrict_map_subseteq by done.
      f_equal.
      apply map_eq; intros i.
      apply option_eq; intros a.
      rewrite lookup_restrict_map_Some.
      rewrite lookup_kmap_Some_full_gen_dom. 2:{
        eapply set_Forall2_mono, Hextinj; [done|].
        rewrite dom_restrict_map_L.
        rewrite vertices_decomp.
        apply union_subseteq_l', intersection_subseteq_l.
      }
      setoid_rewrite lookup_restrict_map_Some.
      split.
      * intros (Hm'i & Hi).
        rewrite <- Himgmv' in Hi.
        apply elem_of_map_img in Hi as (j & Hj).
        exists j.
        apply Hmv'all in Hj as Hij.
        rewrite Hj.
        split; [|done].
        split; [congruence|].
        apply elem_of_dom_2 in Hj.
        now rewrite Hdommv' in Hj.
      * intros (j & [Hmj Hj] & Hmv'j).
        rewrite <- Hdommv' in Hj.
        apply elem_of_dom in Hj as Hj'.
        destruct Hj' as (mv'j & Hji).
        rewrite Hji in Hmv'j.
        cbn in Hmv'j.
        subst mv'j.
        apply Hmv'all in Hji as Hmji.
        rewrite <- Hmji.
        split; [done|].
        rewrite <- Himgmv'.
        revert Hji.
        apply elem_of_map_img_2.
Qed.

Lemma kmap_restrict_map_to_restrict_map_gen
  `{FinMapDom K1 M1 SK1, Elements K1 SK1, !FinSet K1 SK1,
  FinMap K2 M2, SemiSet K2 SK2}
  `{!RelDecision (∈@{SK1}), !RelDecision (∈@{SK2})}
  `{Inhabited K2}
  (mk : M1 K2) (f : K1 -> K2) `{Hf : !Inj eq eq f}
   (d : SK1) (cd : SK2) {A} (m1 : M1 A) (m2 : M2 A) :
  d ⊆ dom mk ->
  set_map f d = cd ->
  map_Forall (λ k v, m1 !! k = m2 !! v) mk ->
  (forall k v, mk !! k = Some v -> f k = v) ->
  kmap f (restrict_map d m1) = restrict_map cd m2.
Proof.
  intros Hdommk Hcd Hmk Hfmk.
  apply map_eq; intros v.
  apply option_eq; intros a.
  rewrite (lookup_kmap_Some _).
  rewrite lookup_restrict_map_Some.
  subst cd.
  setoid_rewrite lookup_restrict_map_Some.
  rewrite elem_of_map.
  split.
  - intros (k & -> & Hm1k & Hkd).
    split; [|eauto].
    erewrite <- Hmk; [apply Hm1k|].
    apply Hdommk in Hkd as (mkk & Hmkk)%elem_of_dom.
    rewrite Hmkk.
    apply Hfmk in Hmkk.
    now f_equal.
  - intros [Hm2v (k & -> & Hkd)].
    exists k.
    split; [done|].
    split; [|done].
    erewrite Hmk; [apply Hm2v|].
    apply Hdommk in Hkd as (mkk & Hmkk)%elem_of_dom.
    rewrite Hmkk.
    apply Hfmk in Hmkk.
    now f_equal.
Qed.

(* FIXME: Move *)
Lemma referenced_vertices_hg_reindex_hg {T} (f : positive -> positive)
  `{Hf : !Inj eq eq f} (hg : HyperGraph T) :
  referenced_vertices_hg (reindex_hg f hg) = referenced_vertices_hg hg.
Proof.
  unfold referenced_vertices_hg.
  cbn.
  rewrite (map_to_list_kmap _).
  rewrite list_fmap_bind.
  done.
Qed.
Lemma referenced_vertices_hg_relabel_hg {T} (f : positive -> positive)
  (hg : HyperGraph T) :
  referenced_vertices_hg (relabel_hg f hg) = set_map f (referenced_vertices_hg hg).
Proof.
  unfold referenced_vertices_hg.
  cbn.
  rewrite map_to_list_fmap.
  rewrite list_fmap_bind.
  rewrite set_map_list_to_set_L.
  rewrite list_bind_fmap.
  f_equal.
  apply list_bind_ext, reflexivity.
  intros [idx [[t i] o]].
  rewrite fmap_app.
  done.
Qed.

Lemma scohg_syntactic_eq_of_is_edges_iso_isolated_vertices {N} `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : SizedCospanHyperGraph N T n m) mv :
  (cohg.(sized_map) !!.) <$> elements (isolated_vertices cohg) ≡ₚ
    (cohg'.(sized_map) !!.) <$> elements (isolated_vertices cohg') ->
  is_edges_iso mv (map_to_list cohg.(hedges).(hyperedges)).*2
    (map_to_list cohg'.(hedges).(hyperedges)).*2 ->
  map_inj mv ->
  map_Forall (λ k v, cohg.(sized_map) !! k = cohg'.(sized_map) !! v) mv ->
  (mv !!.) <$> (inputs cohg ++ outputs cohg) =
  Some <$> (inputs cohg' ++ outputs cohg') ->
  cohg ≡ₛ cohg'.
Proof.
  intros Hverts Hiso Hinj Hty Hio.
  specialize (is_edges_iso_dom_mv _ _ _ Hiso) as Hmvdom.
  rewrite <- 2 vec_to_list_app in Hio.
  rewrite <- 2 vec_to_list_map in Hio.
  apply vec_to_list_inj2 in Hio.
  rewrite 2 Vector.map_append in Hio.
  apply (inj2 vapp) in Hio as [Hins Houts].
  pose proof (conj (f_equal vec_to_list Hins) (f_equal vec_to_list Houts)) as [Hins' Houts'].
  rewrite 2 vec_to_list_map in Hins'.
  rewrite 2 vec_to_list_map in Houts'.
  apply fmap_lookup_Some_dom_eq in Hins' as Hmvins.
  apply fmap_lookup_Some_dom_eq in Houts' as Hmvouts.


  apply scohg_syntactic_eq_of_set_sized_verts_empty_scohg_syntactic_eq; [done|].
  apply exists_edge_map_of_is_edges_iso in Hiso; [|now apply NoDup_fst_map_to_list..].
  destruct Hiso as (mhe & Hmhe & Hpermeq).
  rewrite (sized_iso_relabel_reindex _ (Pmap_injmap mv) mhe).
  apply (subrel' scohg_eq).
  assert (Hmvdom' : referenced_vertices cohg ⊆ dom mv). 1:{
    apply union_least.
    - apply fmap_lookup_Some_dom_eq in Hins', Houts'.
      rewrite list_to_set_app_L.
      now apply union_least.
    - set_solver +Hmvdom.
  }
  split.
  2:{
    cbn.
    rewrite 2 vertices_set_verts, 2 union_empty_r_L.
    apply (kmap_restrict_map_to_restrict_map_gen mv _).
    - done.
    - rewrite (set_map_ext_L _ (mv!!!.)) by
        now intros; apply Pmap_injmap_correct', elem_of_dom, Hmvdom'.
      rewrite 2 referenced_vertices_decomp.
      rewrite set_map_union_L.
      f_equal.
      + rewrite set_map_list_to_set_L.
        f_equal.
        apply (f_equal (fmap (default inhabitant))) in Hins', Houts'.
        rewrite <- 2 list_fmap_compose, list_fmap_id in Hins', Houts'.
        rewrite <- Hins', <- Houts'.
        rewrite fmap_app.
        done.
      + specialize (referenced_vertices_hg_equiv
        (reindex_graph mhe (relabel_graph (mv!!!.) cohg)) cohg') as Heq.
        tspecialize Heq.
        1:{
          unfold rel_preimage.
          cbn.
          apply map_equiv_by_map_to_list.
          etransitivity.
          - apply (Permutation_PermutationA _).
            apply (map_to_list_kmap _).
          - rewrite map_to_list_fmap.
            rewrite <- list_fmap_compose.
            apply Hpermeq.
        }
        rewrite <- Heq.
        cbn.
        rewrite (referenced_vertices_hg_reindex_hg _), 
        referenced_vertices_hg_relabel_hg.
        done.
    - done.
    - apply Pmap_injmap_correct.
  }
  cbn.
  rewrite (relabel_graph_ext_strong _ (mv !!!.)).
  2:{
    intros i.
    rewrite (vertices_reindex_graph _).
    rewrite vertices_set_verts, union_empty_r_L.
    intros Hi.
    apply Pmap_injmap_correct'.
    apply elem_of_dom.
    unfold referenced_vertices in Hi.
    apply elem_of_union in Hi.
    set_solver +Hmvins Hmvouts Hmvdom Hi.
  }
  apply fmap_lookup_Some_lookup_total in Hins', Houts'.
  rewrite <- vec_to_list_map in Hins', Houts'.
  apply vec_to_list_inj2 in Hins', Houts'.
  apply (subrel' cohg_eq).
  split; [done|].
  split; [done|].
  split; [|done].
  apply map_equiv_by_map_to_list.
  cbn.
  rewrite map_to_list_fmap.
  rewrite <- Hpermeq.
  apply (Permutation_PermutationA _).
  rewrite (map_to_list_kmap _).
  rewrite <- list_fmap_compose.
  done.
Qed.

























Section dec_equiv.

Context `{Equiv T, !RelDecision (≡@{T})}.

Fixpoint hyperedge_map_isos_extending_aux
  (hg hg' : list (HyperEdge T))
  (mv : Piso) : list Piso :=
  match hg with
  | [] => match hg' with | [] => [mv] | _::_ => [] end
  | (t, ins, outs) :: hg =>
    list_select (λ tio, t ≡ tio.1.1 /\
      length (tio.1.2) = length ins /\
      length (tio.2) = length outs) hg' ≫= λ '(tio, hg'rest),
      default [] (
        mv' ← pupdates (zip (ins ++ outs) (tio.1.2 ++ tio.2)) mv;
        Some (hyperedge_map_isos_extending_aux hg hg'rest
         mv'))
  end.

Definition hyperedge_map_isos_extending
  (hg hg' : Pmap (HyperEdge T)) (mv : Piso) : list Piso :=
  hyperedge_map_isos_extending_aux (map_to_list hg).*2 (map_to_list hg').*2 mv.

Definition graph_isos {n m} (cohg cohg' : CospanHyperGraph T n m) :
  list Piso :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    default []
      (mv ← pupdates (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
      Some
      (hyperedge_map_isos_extending cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) mv))
  else
    [].


Lemma hyperedge_map_isos_extending_aux_correct `{Equivalence T equiv}
  (hg hg' : list (HyperEdge T)) (mv : Piso) :
  Forall (λ mv', mv.(Piso_map) ⊆ mv'.(Piso_map) /\ is_edges_iso mv'.(Piso_map) hg hg')
    (hyperedge_map_isos_extending_aux hg hg' mv).
Proof.
  revert hg' mv; induction hg as [|[[t i] o] hg IHhg];
    intros hg' mv; [cbn;
    destruct hg'; [|done]; do 2 constructor; [done|constructor]|].
  cbn.
  rewrite Forall_bind.
  rewrite Forall_forall.
  intros [tio' hg''] ((Ht & Hi & Ho) & Hhg')%elem_of_list_select_perm_Prop.
  cbn.
  destruct (pupdates (zip (i ++ o) _) mv)
    as [mv'|] eqn:Hmv'; [|now constructor].
  cbn.

  eapply Forall_impl; [apply IHhg|].
  cbn.
  intros mv'' [Hmv'mv'' Hmv''].
  rewrite Hhg'.
  split.
  - apply pupdates_correct_extends in Hmv'.
    now transitivity mv'.
  - destruct tio' as [[t' i'] o'].
    apply pupdates_correct_fmap in Hmv' as Hio; [|rewrite 2 length_app; now f_equal].
    cbn in *.
    rewrite 2 fmap_app in Hio.
    apply app_inj_len_l in Hio as [Hmv'i Hmv'o]; [|now rewrite 2 length_fmap].

    apply is_edges_iso_cons.
    + done.
    + done.
    + revert Hmv'i; now apply fmap_lookup_weaken.
    + revert Hmv'o; now apply fmap_lookup_weaken.
Qed.


Lemma hyperedge_map_isos_extending_correct `{Equivalence T equiv}
  (hg hg' : Pmap (HyperEdge T)) (mv : Piso) :
  Forall (λ mv', mv.(Piso_map) ⊆ mv'.(Piso_map) /\ is_edges_iso mv'.(Piso_map)
    (map_to_list hg).*2 (map_to_list hg').*2)
    (hyperedge_map_isos_extending hg hg' mv).
Proof.
  apply hyperedge_map_isos_extending_aux_correct.
Qed.

Lemma graph_isos_correct_aux `{Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ mv : Piso,
    size (isolated_vertices cohg) = size (isolated_vertices cohg') /\
    is_edges_iso mv (map_to_list cohg.(hedges).(hyperedges)).*2
      (map_to_list cohg'.(hedges).(hyperedges)).*2 /\
    (mv.(Piso_map) !!.) <$> (inputs cohg ++ outputs cohg) =
    Some <$> (inputs cohg' ++ outputs cohg'))
  (graph_isos cohg cohg').
Proof.
  unfold graph_isos.
  case_decide; [|constructor].
  destruct (pupdates _ ∅) as [mio|] eqn:Hmio; [|done].
  cbn.
  eapply Forall_impl; [apply hyperedge_map_isos_extending_correct|].
  cbn.
  intros mv'.
  intros (Hmiomv' & Hiso).
  split; [done|].
  split; [done|].
  apply (fmap_lookup_weaken mio.(Piso_map)); [done|].
  apply pupdates_correct_fmap with ∅.
  - now rewrite 2 length_app, 4 length_vec_to_list.
  - done.
Qed.


Lemma graph_isos_correct `{Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  Forall (λ _, cohg ≡ₛ cohg')
    (graph_isos cohg cohg').
Proof.
  eapply Forall_impl; [apply graph_isos_correct_aux|].
  cbn.
  intros mv (Hsize & Hiso & Hio).
  apply cohg_syntactic_eq_of_is_edges_iso_isolated_vertices with mv; try done.
  apply Piso_map_inj.
Qed.

Lemma graph_isos_test `{Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  match graph_isos cohg cohg' with
  | [] => False
  | _ :: _ => True
  end -> cohg ≡ₛ cohg'.
Proof.
  pose proof (graph_isos_correct cohg cohg') as Hcorr.
  destruct (graph_isos _ _); [done|].
  rewrite Forall_cons in Hcorr.
  easy.
Qed.

Definition graph_iso_partial_test {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma graph_iso_partial_test_correct `{Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  graph_iso_partial_test cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  intros Heq.
  apply graph_isos_test.
  revert Heq.
  unfold graph_iso_partial_test.
  now case_match.
Qed.



Fixpoint weak_hyperedge_map_isos_extending_aux
  (hg hg' : list (HyperEdge T))
  (mv : WPiso) : list WPiso :=
  match hg with
  | [] => match hg' with | [] => [mv] | _::_ => [] end
  | (t, ins, outs) :: hg =>
    list_select (λ tio, t ≡ tio.1.1 /\
      length (tio.1.2) = length ins /\
      length (tio.2) = length outs) hg' ≫= λ '(tio, hg'rest),
      default [] (
        mv' ← wpupdates (zip (ins ++ outs) (tio.1.2 ++ tio.2)) mv;
        Some (weak_hyperedge_map_isos_extending_aux hg hg'rest
         mv'))
  end.

Definition weak_hyperedge_map_isos_extending
  (hg hg' : Pmap (HyperEdge T)) (mv : WPiso) : list WPiso :=
  weak_hyperedge_map_isos_extending_aux (map_to_list hg).*2 (map_to_list hg').*2 mv.

Definition weak_graph_isos {n m} (cohg cohg' : CospanHyperGraph T n m) :
  list WPiso :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    default []
      (mv ← wpupdates (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
      Some
      (weak_hyperedge_map_isos_extending cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) mv))
  else
    [].

Lemma weak_hyperedge_map_isos_extending_aux_correct hg hg' (mv : Piso) :
  weak_hyperedge_map_isos_extending_aux hg hg' (Piso_to_weak mv) =
  Piso_to_weak <$> hyperedge_map_isos_extending_aux hg hg' mv.
Proof.
  revert hg' mv; induction hg as [|[[t i] o] hg IHhg]; intros hg' mv;
  [destruct hg'; done|].
  cbn.
  rewrite list_bind_fmap.
  apply list_bind_ext, reflexivity.
  intros [[[]] ?].
  rewrite wpupdates_correct.
  rewrite option_fmap_bind.
  cbn.
  destruct (pupdates _ mv); [|done].
  cbn.
  apply IHhg.
Qed.

Lemma weak_hyperedge_map_isos_extending_correct hg hg' (mv : Piso) :
  weak_hyperedge_map_isos_extending hg hg' (Piso_to_weak mv) =
  Piso_to_weak <$> hyperedge_map_isos_extending hg hg' mv.
Proof.
  apply weak_hyperedge_map_isos_extending_aux_correct.
Qed.

Lemma weak_graph_isos_correct {n m} (cohg cohg' : CospanHyperGraph T n m) :
  weak_graph_isos cohg cohg' = Piso_to_weak <$> graph_isos cohg cohg'.
Proof.
  unfold weak_graph_isos, graph_isos.
  case_decide; [|done].
  rewrite WPiso_empty_correct, wpupdates_correct.
  destruct (pupdates _ _); [|done].
  cbn.
  apply weak_hyperedge_map_isos_extending_correct.
Qed.

Definition weak_graph_iso_partial_test {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match weak_graph_isos cohg cohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma weak_graph_iso_partial_test_correct `{Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  weak_graph_iso_partial_test cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  intros Heq.
  apply (graph_iso_partial_test_correct cohg cohg').
  revert Heq.
  unfold weak_graph_iso_partial_test, graph_iso_partial_test.
  rewrite weak_graph_isos_correct.
  now destruct (graph_isos _ _).
Qed.


Fixpoint opt_weak_hyperedge_map_isos_extending_aux
  (hg hg' : list (HyperEdge T))
  (mv : WPiso) : option WPiso :=
  match hg with
  | [] => match hg' with | [] => Some mv | _::_ => None end
  | (t, ins, outs) :: hg =>
    list_first_omap
    (λ '(tio, hg'rest),
        mv' ← wpupdates (zip (ins ++ outs) (tio.1.2 ++ tio.2)) mv;
        opt_weak_hyperedge_map_isos_extending_aux hg hg'rest
         mv')
    (list_select (λ tio, t ≡ tio.1.1 /\
      length (tio.1.2) = length ins /\
      length (tio.2) = length outs) hg')
  end.

Definition opt_weak_hyperedge_map_isos_extending
  (hg hg' : Pmap (HyperEdge T)) (mv : WPiso) : option WPiso :=
  opt_weak_hyperedge_map_isos_extending_aux (map_to_list hg).*2 (map_to_list hg').*2 mv.

Definition opt_weak_graph_iso {n m} (cohg cohg' : CospanHyperGraph T n m) :
  option WPiso :=
  if decide (size (isolated_vertices cohg) = size (isolated_vertices cohg')) then
    mv ← wpupdates (zip (cohg.(inputs) ++ cohg.(outputs))
        (cohg'.(inputs) ++ cohg'.(outputs))) ∅;
    opt_weak_hyperedge_map_isos_extending cohg.(hedges).(hyperedges)
        cohg'.(hedges).(hyperedges) mv
  else
    None.


Lemma opt_weak_hyperedge_map_isos_extending_aux_correct hg hg' mv :
  opt_weak_hyperedge_map_isos_extending_aux hg hg' mv =
  head (weak_hyperedge_map_isos_extending_aux hg hg' mv).
Proof.
  revert hg' mv; induction hg as [|[[t i] o] hg IHhg]; intros hg' mv;
  [destruct hg'; done|].
  cbn.
  rewrite list_first_omap_eq_head_bind.
  symmetry.
  rewrite head_bind.
  f_equal.
  apply list_bind_ext, reflexivity.
  intros [[[]] ?].
  cbn.
  destruct (wpupdates _ mv); [|done].
  cbn.
  rewrite IHhg.
  done.
Qed.

Lemma opt_weak_hyperedge_map_isos_extending_correct hg hg' mv :
  opt_weak_hyperedge_map_isos_extending hg hg' mv =
  head (weak_hyperedge_map_isos_extending hg hg' mv).
Proof.
  apply opt_weak_hyperedge_map_isos_extending_aux_correct.
Qed.

Lemma opt_weak_graph_iso_correct {n m} (cohg cohg' : CospanHyperGraph T n m) :
  opt_weak_graph_iso cohg cohg' = head (weak_graph_isos cohg cohg').
Proof.
  unfold weak_graph_isos, opt_weak_graph_iso.
  case_decide; [|done].
  destruct (wpupdates _ _); [|done].
  cbn.
  apply opt_weak_hyperedge_map_isos_extending_correct.
Qed.

Definition opt_weak_graph_iso_partial_test {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match opt_weak_graph_iso cohg cohg' with
  | None => false
  | Some _ => true
  end.

Lemma opt_weak_graph_iso_partial_test_correct `{Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  opt_weak_graph_iso_partial_test cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  intros Heq.
  apply (weak_graph_iso_partial_test_correct cohg cohg').
  revert Heq.
  unfold weak_graph_iso_partial_test, opt_weak_graph_iso_partial_test.
  rewrite opt_weak_graph_iso_correct.
  now destruct (weak_graph_isos _ _).
Qed.


Fixpoint hyperedge_map_monos_extending_aux
  (hg hg' : list (positive * (HyperEdge T)))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => [mhe_mv]
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, t ≡ k_tio.2.1.1 /\
      length (k_tio.2.1.2) = length ins /\
      length (k_tio.2.2) = length outs) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← pupdate k k_tio.1 mhe_mv.1;
        mv' ← pupdates (zip (ins ++ outs) (k_tio.2.1.2 ++ k_tio.2.2))
          mhe_mv.2;
        Some (hyperedge_map_monos_extending_aux hg hg'rest
         (mhe', mv')))
  end.


Definition hyperedge_map_monos_extending
  (hg hg' : Pmap (HyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  hyperedge_map_monos_extending_aux (map_to_list hg)
    (map_to_list hg') mhe_mv.

Definition graph_monos {i j n m} (subcohg : CospanHyperGraph T i j)
  (cohg : CospanHyperGraph T n m) :
  list (Piso * Piso) :=
  if decide (size (isolated_vertices subcohg) <= size (isolated_vertices cohg)) then
    hyperedge_map_monos_extending subcohg.(hedges).(hyperedges)
        cohg.(hedges).(hyperedges) (∅, ∅)
  else
    [].


(* Definition graph_matches {i j n m} (subcohg : CospanHyperGraph T i j)
  (cohg : CospanHyperGraph T n m) :
  list (list positive) *)



End dec_equiv.



































Definition sized_graph_isos {N} `{EqDecision N} `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : list (Piso) :=
  filter (λ mv,
    Forall (λ kv, scohg.(sized_map) !! kv.1 = scohg'.(sized_map) !! kv.2)
      (map_to_list mv.(Piso_map))) (graph_isos scohg scohg').

Lemma sized_graph_isos_correct {N} `{EqDecision N} `{Equiv T, Equivalence T equiv, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) :
  Forall (λ _, scohg ≡ₛ scohg') (sized_graph_isos scohg scohg').
Proof.
  unfold sized_graph_isos.
  rewrite Forall_filter.
Admitted.

Definition sized_graph_iso_partial_test {N} `{EqDecision N}
  `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : bool :=
  match sized_graph_isos scohg scohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma sized_graph_iso_partial_test_correct {N} `{EqDecision N}
  `{Equiv T, Equivalence T equiv, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) :
  sized_graph_iso_partial_test scohg scohg' = true ->
  scohg ≡ₛ scohg'.
Proof.
  pose proof (sized_graph_isos_correct scohg scohg') as Hiso.
  unfold sized_graph_iso_partial_test.
  case_match; [done|].
  now rewrite Forall_cons in Hiso.
Qed.




Section dec_equiv.

Context {N} `{EqDecision N} `{Equiv T, !RelDecision (≡@{T})}.


Fixpoint sized_hyperedge_map_monos_extending_aux
  (hg hg' : list (positive *
    (T * list (positive * option N) * list (positive * option N))))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => [mhe_mv]
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, t ≡ k_tio.2.1.1 /\
      (k_tio.2.1.2).*2 = ins.*2 /\
      (k_tio.2.2).*2 = outs.*2) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← pupdate k k_tio.1 mhe_mv.1;
        mv' ← pupdates (zip (ins ++ outs).*1 (k_tio.2.1.2 ++ k_tio.2.2).*1)
          mhe_mv.2;
        Some (sized_hyperedge_map_monos_extending_aux hg hg'rest
         (mhe', mv')))
  end.


Definition sized_hyperedge_map_monos_extending
  (ms : Pmap N) (ms' : Pmap N)
  (hg hg' : Pmap (HyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  sized_hyperedge_map_monos_extending_aux
    (prod_map id (relabel_abs (λ k, (k, ms !! k))) <$> map_to_list hg)
    (prod_map id (relabel_abs (λ k, (k, ms' !! k))) <$> map_to_list hg')
    mhe_mv.

Definition sized_graph_monos {i j n m} (subscohg : SizedCospanHyperGraph N T i j)
  (scohg : SizedCospanHyperGraph N T n m) :
  list (Piso * Piso) :=
  if decide (size (isolated_vertices subscohg) <= size (isolated_vertices scohg)) then
    sized_hyperedge_map_monos_extending subscohg.(sized_map) scohg.(sized_map)
      subscohg.(hyperedges)
        scohg.(hyperedges) (∅, ∅)
  else
    [].

End dec_equiv.
split; [done|].