From TensorRocq Require Import CospanHyperGraph.Definitions.
From TensorRocq Require Import Isomorphism.IsoAux.

(* In this file, we define an efficient graph isomorphism testing function
  which we verify to be correct [graph_iso_partial_test]. *)

(* Definition is _edge_iso {T} (mv : Pmap positive) (e e' : HyperEdge T) :=
  (mv !!.) <$> e.1.2 = Some <$> e'.1.2 /\
  (mv !!.) <$> e.2 = Some <$> e'.2. *)

Definition is_edges_iso `{Equiv T} (mv : Pmap positive)
  (es es' : list (HyperEdge T)) :=
  PermutationA (prod_relation (prod_relation equiv eq) eq)
    ((prod_map (prod_map id (fmap (M:=list) (mv!!.))) (fmap (M:=list) (mv!!.))) <$> es)
    ((prod_map (prod_map id (fmap (M:=list) Some)) (fmap (M:=list) Some)) <$> es').

#[export] Instance is_edges_iso_perm `{Equiv T, Equivalence T equiv} mv :
  Proper (Permutation ==> Permutation ==> iff) (is_edges_iso (T:=T) mv).
Proof.
  intros es1 es2 Hes es1' es2' Hes'.
  unfold is_edges_iso.
  f_equiv; apply (Permutation_PermutationA _);
  [rewrite Hes|rewrite Hes'];
  done.
Qed.

(* FIXME: Move *)
Lemma PermutationA_eq {A} (l l' : list A) : PermutationA eq l l' <-> Permutation l l'.
Proof.
  split; [|apply (Permutation_PermutationA _)].
  intros (l'' & Hll'' & Hl''l'%eqlistA_altdef%list_eq_Forall2)%(PermutationA_decompose _).
  now subst.
Qed.
Lemma fmap_lookup_Some_dom `{FinMapDom K M SK} {A}
  (m : M A) (ks : list K) (vs : list A) :
  (m !!.) <$> ks ≡ Some <$> vs ->
  list_to_set ks ⊆ dom m.
Proof.
  intros Hmks v Hv%elem_of_list_to_set%(elem_of_list_fmap_1 (m!!.)).
  rewrite Hmks in Hv.
  apply elem_of_dom.
  set_solver + Hv.
Qed.
Lemma fmap_lookup_Some_dom_perm `{FinMapDom K M SK} {A}
  (m : M A) (ks : list K) (vs : list A) :
  (m !!.) <$> ks ≡ₚ Some <$> vs ->
  list_to_set ks ⊆ dom m.
Proof.
  intros Hmks v Hv%elem_of_list_to_set%(elem_of_list_fmap_1 (m!!.)).
  rewrite Hmks in Hv.
  apply elem_of_dom.
  set_solver + Hv.
Qed.
Lemma fmap_lookup_Some_dom_eq `{FinMapDom K M SK} {A}
  (m : M A) (ks : list K) (vs : list A) :
  (m !!.) <$> ks = Some <$> vs ->
  list_to_set ks ⊆ dom m.
Proof.
  intros Hmks v Hv%elem_of_list_to_set%(elem_of_list_fmap_1 (m!!.)).
  rewrite Hmks in Hv.
  apply elem_of_dom.
  set_solver + Hv.
Qed.



Lemma is_edges_iso_dom_mv `{Equiv T, Equivalence T equiv} mv es es' :
  is_edges_iso (T:=T) mv es es' ->
  forall v, (exists i_tio, i_tio ∈ es /\ v ∈ i_tio.1.2 ++ i_tio.2)
  -> v ∈ dom mv.
Proof.
  unfold is_edges_iso.
  intros Hperm.
  (* apply (fmap_PermutationA (prod_map snd id) _) in Hperm as Hperm.
  rewrite 2 snds_prod_map in Hperm.
  apply PermutationA_eq in Hperm. *)
  apply (fun HP => fmap_PermutationA (RB:=eq) (prod_map snd id) HP) in Hperm as Hperm%PermutationA_eq.
  2:{
    intros [[t i] o] [[t' i'] o'].
    unfold prod_relation.
    simpl.
    naive_solver.
  }
  rewrite <- 2 list_fmap_compose in Hperm.

  pose proof (fun x Hx => (elem_of_Permutation_proper x _ _ Hperm).1 Hx) as Helem.
  intros v (i_tio & Hi_tio & Hv).
  specialize (Helem _ (elem_of_list_fmap_1 _ _ _ Hi_tio)).
  (* apply (elem_of_list_fmap_1 snd) in Helem.
  rewrite snds_prod_map, list_fmap_id in Helem.
  rewrite snds_prod_map in Helem. *)
  destruct i_tio as [[t ins] outs].
  simpl in Helem.
  apply elem_of_list_fmap in Helem as ([[t' ins'] outs'] & [= Hins Houts] & _).
  apply fmap_lookup_Some_dom_eq in Hins, Houts.
  simpl in Hv.
  apply elem_of_app in Hv as [Hv|Hv]; [apply Hins|apply Houts];
  set_solver +Hv.
Qed.


Lemma is_edges_iso_submap `{Equiv T, Equivalence T equiv} mv mv' (es es' : list (HyperEdge T)) :
  mv ⊆ mv' ->
  is_edges_iso mv es es' ->
  is_edges_iso mv' es es'.
Proof.
  intros Hmv Hiso.
  pose proof Hiso as Hperm.
  unfold is_edges_iso in Hperm |- *.
  rewrite <- Hperm.
  apply eq_reflexivity.
  apply list_fmap_ext; intros _ tio Htio%elem_of_list_lookup_2.
  specialize (is_edges_iso_dom_mv _ _ _ Hiso) as Hdom.
  destruct tio as [[t i] o].
  simpl.
  f_equal; [f_equal|]; apply list_fmap_ext;
  intros _ v Hv%elem_of_list_lookup_2;
  specialize (Hdom v);
  tspecialize Hdom by set_solver +Htio Hv;
  apply elem_of_dom in Hdom as [v' Hv'];
  rewrite Hv';
  revert Hv' Hmv; apply lookup_weaken.
Qed.


Lemma is_edges_iso_cons `{Equiv T, Equivalence T equiv} mv
  (es es' : list (HyperEdge T)) t t' i i' o o' :
  is_edges_iso mv es es' ->
  t ≡ t' ->
  (mv !!.) <$> i = Some <$> i' ->
  (mv !!.) <$> o = Some <$> o' ->
  is_edges_iso mv ((t, i, o) :: es) ((t', i', o') :: es').
Proof.
  intros Hiso Ht Hi Ho.
  unfold is_edges_iso.
  cbn.
  constructor; [|apply Hiso].
  done.
Qed.

Lemma option_Forall2_is_Some `{RA : relation A} ma ma' :
  option_Forall2 RA ma ma' -> is_Some ma <-> is_Some ma'.
Proof.
  rewrite 2 is_Some_alt.
  now intros [].
Qed.

Lemma PermutationA_lookup `{RA : relation A, HRA : Equivalence A RA}
  (l l' : list A) :
  PermutationA RA l l' <-> length l = length l' /\
  exists f, Inj eq eq f /\ forall i, option_Forall2 RA (l !! i) (l' !! (f i)).
Proof.
  split.
  - intros HA.
    split; [now apply PermutationA_length in HA|].
    induction HA.
    + exists id.
      split; [apply _|].
      done.
    + destruct IHHA as (f & Hf & Hfi).
      exists (λ n, match n with | O => O | S n' => S (f n') end).
      split.
      * intros [] []; [done..|].
        now intros [= ->%(inj f)].
      * intros []; [now constructor|apply Hfi].
    + exists (λ n, match n with | 0 => 1 | 1 => 0 | n => n end).
      split.
      * intros [|[]] [|[]]; easy.
      * intros [|[]]; easy.
    + destruct IHHA1 as (f & Hf & Hfi), IHHA2 as (g & Hg & Hgi).
      exists (g ∘ f).
      split; [apply _|].
      intros i.
      cbn.
      rewrite <- Hgi.
      auto.
  - remember (length l) as n eqn:Hl.
    rewrite (symmetry_iff eq n) in Hl |- *.
    revert l l' Hl; induction n; intros l l' Hl (Hl' & f & Hf & Hfi).
    + destruct l, l'; [|exfalso; done..].
      constructor.
    + destruct l as [|a l]; [easy|].
      cbn in Hl.
      injection Hl as Hl.
      specialize (Hfi 0) as Ha.
      cbn in Ha.
      symmetry in Ha.
      rewrite option_Forall2_alt in Ha.
      destruct (l' !! (f 0)) as [lf0|] eqn:Hlf0; [|done].
      apply elem_of_list_split_length in Hlf0 as Hl'split.
      destruct Hl'split as (l1' & l2' & Hl'dec & Hf0l1).
      rewrite <- Ha.
      rewrite Hl'dec.
      apply (PermutationA_cons_app _).
      apply IHn; [done|].
      subst l'.
      split; [revert Hl'; clear; rewrite ?length_app; cbn; lia|].
      exists (fun n => if decide (f (S n) < length l1') then f (S n) else (f (S n) - 1)).
      split.
      * intros i j.
        specialize (not_inj (f:=f) 0 (S i) ltac:(done)) as HfSi.
        specialize (not_inj (f:=f) 0 (S j) ltac:(done)) as HfSj.
        specialize (inj f (S i) (S j)).
        do 2 case_decide; lia.
      * intros i.
        specialize (Hfi (S i)).
        cbn in Hfi.
        specialize (not_inj (f:=f) 0 (S i) ltac:(done)) as HfSi.
        case_decide as Hsmall.
        --now rewrite lookup_app_l in Hfi |- * by lia.
        --rewrite lookup_app_r in Hfi |- * by lia.
          rewrite lookup_cons_ne_0 in Hfi by lia.
          rewrite Hfi.
          f_equiv.
          lia.
Qed.

Lemma PermutationA_lookup' `{RA : relation A, HRA : Equivalence A RA}
  (l l' : list A) :
  PermutationA RA l l' <-> length l = length l' /\
  exists f, Inj eq eq f /\ (forall i, i < length l <-> f i < length l) /\
  forall i, option_Forall2 RA (l !! i) (l' !! (f i)).
Proof.
  rewrite PermutationA_lookup.
  split; [|firstorder].
  intros (? & f & Hf & Hfi).
  split; [done|].
  exists f.
  split; [done|].
  split; [|done].
  intros i.
  specialize (Hfi i).
  apply option_Forall2_is_Some in Hfi.
  rewrite 2 lookup_lt_is_Some in Hfi.
  congruence.
Qed.


Lemma Permutation_lookup {A} (l l' : list A) :
  Permutation l l' <-> length l = length l' /\
  exists f, Inj eq eq f /\ forall i, l !! i = l' !! (f i).
Proof.
  split.
  - intros HA.
    split; [now apply Permutation_length in HA|].
    induction HA.
    + exists id.
      split; [apply _|].
      done.
    + destruct IHHA as (f & Hf & Hfi).
      exists (λ n, match n with | O => O | S n' => S (f n') end).
      split.
      * intros [] []; [done..|].
        now intros [= ->%(inj f)].
      * intros []; [now constructor|apply Hfi].
    + exists (λ n, match n with | 0 => 1 | 1 => 0 | n => n end).
      split.
      * intros [|[]] [|[]]; easy.
      * intros [|[]]; easy.
    + destruct IHHA1 as (f & Hf & Hfi), IHHA2 as (g & Hg & Hgi).
      exists (g ∘ f).
      split; [apply _|].
      intros i.
      cbn.
      rewrite <- Hgi.
      auto.
  - remember (length l) as n eqn:Hl.
    rewrite (symmetry_iff eq n) in Hl |- *.
    revert l l' Hl; induction n; intros l l' Hl (Hl' & f & Hf & Hfi).
    + destruct l, l'; [|exfalso; done..].
      constructor.
    + destruct l as [|a l]; [easy|].
      cbn in Hl.
      injection Hl as Hl.
      specialize (Hfi 0) as Ha.
      cbn in Ha.
      symmetry in Ha.
      apply elem_of_list_split_length in Ha as Hl'split.
      destruct Hl'split as (l1' & l2' & Hl'dec & Hf0l1).
      rewrite Hl'dec.
      apply (Permutation_cons_app _).
      apply IHn; [done|].
      subst l'.
      split; [revert Hl'; clear; rewrite ?length_app; cbn; lia|].
      exists (fun n => if decide (f (S n) < length l1') then f (S n) else (f (S n) - 1)).
      split.
      * intros i j.
        specialize (not_inj (f:=f) 0 (S i) ltac:(done)) as HfSi.
        specialize (not_inj (f:=f) 0 (S j) ltac:(done)) as HfSj.
        specialize (inj f (S i) (S j)).
        do 2 case_decide; lia.
      * intros i.
        specialize (Hfi (S i)).
        cbn in Hfi.
        specialize (not_inj (f:=f) 0 (S i) ltac:(done)) as HfSi.
        case_decide as Hsmall.
        --now rewrite lookup_app_l in Hfi |- * by lia.
        --rewrite lookup_app_r in Hfi |- * by lia.
          rewrite lookup_cons_ne_0 in Hfi by lia.
          etransitivity; [apply Hfi|].
          f_equiv.
          lia.
Qed.

Lemma Permutation_lookup' {A} (l l' : list A) :
  Permutation l l' <-> length l = length l' /\
  exists f, Inj eq eq f /\ (forall i, i < length l <-> f i < length l) /\
  forall i, l !! i = l' !! (f i).
Proof.
  rewrite Permutation_lookup.
  split; [|firstorder].
  intros (? & f & Hf & Hfi).
  split; [done|].
  exists f.
  split; [done|].
  split; [|done].
  intros i.
  specialize (Hfi i).
  apply (f_equiv is_Some) in Hfi.
  rewrite 2 lookup_lt_is_Some in Hfi.
  congruence.
Qed.


Lemma Permutation_lookup'' {A} (l l' : list A) :
  Permutation l l' <-> length l = length l' /\
  exists f, Inj eq eq f /\ (forall i, i < length l <-> f i < length l) /\
  forall i x, l !! i = Some x -> l' !! f i = Some x.
Proof.
  rewrite Permutation_lookup'.
  split; [naive_solver congruence|].
  intros [Hlen (f & Hf & Hflt & Hfi)].
  split; [done|].
  exists f.
  split; [done|].
  split; [done|].
  intros i.
  destruct_decide (decide (i < length l)) as Hilt.
  - apply lookup_lt_is_Some in Hilt as [li Hli].
    rewrite Hli.
    symmetry.
    now apply Hfi.
  - rewrite (lookup_ge_None _ _).2 by lia.
    symmetry.
    apply lookup_ge_None.
    apply Nat.nlt_ge.
    rewrite <- Hlen.
    now rewrite <- Hflt.
Qed.

Lemma fmap_lookup_Some_lookup_total `{FinMap K M} `{Inhabited A}
  (m : M A) (l : list K) (l' : list A) :
  (m !!.) <$> l = Some <$> l' -> (m !!!.) <$> l = l'.
Proof.
  rewrite 2 list_eq_Forall2.
  rewrite Forall2_fmap, Forall2_fmap_l.
  intros Hll'.
  eapply Forall2_impl; [apply Hll'|].
  cbn.
  apply lookup_total_correct.
Qed.


Lemma exists_edge_map_of_is_edges_iso `{Equiv T, Equivalence T equiv}
  mv (es es' : list (positive * HyperEdge T)) :
  NoDup es.*1 -> NoDup es'.*1 ->
  is_edges_iso mv es.*2 es'.*2 ->
  exists mhe,
    Inj eq eq mhe /\
    PermutationA (prod_relation eq equiv)
      (prod_map mhe (relabel_abs (mv!!!.)) <$> es) es'.
Proof.
  intros Hes Hes' Hiso.
  apply PermutationA_lookup' in Hiso as (Hlen & f & Hf & Hflt & Hfi).
  rewrite 4 length_fmap in Hlen.
  rewrite 2 length_fmap in Hflt.

  specialize (partial_injection_extension es.*1 (λ p, default p (list_index p es.*1 ≫= (es'.*1!!.) ∘ f)))
    as Hmhe.
  tspecialize Hmhe.
  1:{
    rewrite ForallPairs_forall.
    intros p q [ip Hip]%list_index_is_Some [iq Hiq]%list_index_is_Some.
    rewrite Hip, Hiq.
    cbn.
    apply list_index_Some in Hip as [Hesip _], Hiq as [Hesiq _].
    apply lookup_lt_Some in Hesip as Hip, Hesiq as Hiq.
    rewrite length_fmap, Hflt, Hlen in Hip, Hiq.
    rewrite <- (length_fmap fst) in Hip, Hiq.
    apply lookup_lt_is_Some in Hip as [p' Hp'], Hiq as [q' Hq'].
    rewrite Hp', Hq'.
    cbn.
    intros <-.
    apply (NoDup_lookup _ (f ip) (f iq) p') in Hes' as Hes'%(inj f); [|done..].
    congruence.
  }
  destruct Hmhe as (mhe & Hinj & Hmhe).
  exists mhe.
  split; [apply _|].
  apply PermutationA_lookup'.
  rewrite length_fmap.
  split; [done|].
  exists f.
  split; [done|].
  split; [done|].
  intros i.
  rewrite list_lookup_fmap.
  destruct (es !! i) as [[idx tio]|] eqn:Htio.
  2:{
    apply lookup_ge_None in Htio.
    cbn.
    rewrite option_Forall2_alt.
    enough (es' !! f i = None) as -> by done.
    apply lookup_ge_None.
    apply Nat.nlt_ge in Htio.
    apply Nat.nlt_ge.
    now rewrite <- Hlen, <- Hflt.
  }
  cbn.
  destruct (es' !! f i) as [[idx' tio']|] eqn:Htio'.
  2:{
    apply lookup_lt_Some in Htio.
    apply lookup_ge_None in Htio'.
    apply Nat.nlt_ge in Htio'.
    now rewrite <- Hlen, <- Hflt in Htio'; exfalso.
  }
  constructor.
  split; cbn.
  - rewrite Forall_forall in Hmhe.
    apply elem_of_list_lookup_2 in Htio as Hidx.
    specialize (Hmhe idx (elem_of_list_fmap_1 fst _ _ Hidx)).
    rewrite Hmhe.
    apply (f_equal (fmap fst)) in Htio.
    rewrite <- list_lookup_fmap in Htio.
    cbn in Htio.
    rewrite <- list_index_Some_NoDup in Htio by done.
    rewrite Htio.
    cbn.
    rewrite list_lookup_fmap.
    now rewrite Htio'.
  - specialize (Hfi i).
    rewrite 4 list_lookup_fmap in Hfi.
    rewrite Htio, Htio' in Hfi.
    cbn in Hfi.
    rewrite option_Forall2_alt in Hfi.
    clear i Htio Htio'.
    destruct tio as [[t i] o], tio' as [[t' i'] o'], Hfi as [[Ht Hi] Ho].
    cbn in *.
    split; [split|]; cbn.
    + done.
    + now apply fmap_lookup_Some_lookup_total.
    + now apply fmap_lookup_Some_lookup_total.
Qed.


Lemma norm_verts_isomorphic_of_set_verts_empty_isomorphic {T} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  size (isolated_vertices cohg) = size (isolated_vertices cohg') ->
  isomorphic (set_verts cohg ∅) (set_verts cohg' ∅) ->
  isomorphic (norm_verts cohg) (norm_verts cohg').
Proof.
  intros Hverts.
  intros (fv & fe & Hfv & Hfe & Heq)%isomorphic_exists.
  apply (size_set_eq_exists_map (M:=Pmap)) in Hverts as Hmv'.
  destruct Hmv' as (mv' & Hdommv' & Himgmv' & Hinj).

  assert (Himgfv : forall v, v ∈ referenced_vertices cohg ->
    fv v ∈ referenced_vertices cohg'). 1:{
    intros v Hv.
    apply (f_equal referenced_vertices) in Heq.
    rewrite referenced_vertices_set_verts in Heq.
    rewrite Heq.
    rewrite referenced_vertices_relabel_graph,
      (referenced_vertices_reindex_graph _).
    rewrite referenced_vertices_set_verts.
    now apply elem_of_map_2.
  }

  eapply (isomorphic_of_partial_inj_dom' _ _
    (λ i, default (fv i) (mv' !! i)) fe).
  - intros i j.
    rewrite vertices_decomp, 2 elem_of_union.
    rewrite isolated_vertices_norm_verts, referenced_vertices_norm_verts.
    intros [Hii|Hir];
    [apply Hdommv' in Hii as Hmi;
    apply elem_of_dom in Hmi as [mi Hmi];
    rewrite Hmi; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmi as Hmii;
    rewrite Himgmv' in Hmii
    |replace (mv' !! i) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%isolated_referenced_disjoint);
     cbn;
     specialize (Himgfv i Hir) as Hfir];
    (intros [Hji|Hjr];
    [apply Hdommv' in Hji as Hmj;
    apply elem_of_dom in Hmj as [mj Hmj];
    rewrite Hmj; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmj as Hmji;
    rewrite Himgmv' in Hmji
    |replace (mv' !! j) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%isolated_referenced_disjoint);
     cbn;
     specialize (Himgfv j Hjr) as Hfjr]).
    + intros <-.
      revert Hmi Hmj.
      apply Hinj.
    + intros ->.
      now apply isolated_referenced_disjoint in Hmii.
    + intros <-.
      now apply isolated_referenced_disjoint in Hmji.
    + apply Hfv.
  - intros ? ? ? ?; apply Hfe.
  - apply cohg_ext; [apply hg_ext|..].
    + cbn.
      etransitivity; [apply (f_equal (hyperedges ∘ hedges) Heq)|].
      cbn.
      apply map_fmap_ext.
      intros _ tv (i & -> & Hitv)%(lookup_kmap_Some _).
      apply relabel_abs_ext_strong.
      intros v Hv.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      apply elem_of_map_to_list in Hitv.
      unfold referenced_vertices.
      apply elem_of_union_r.
      apply elem_of_list_to_set.
      apply elem_of_list_bind.
      exists (i, tv).
      eauto.
    + cbn.
      apply leibniz_equiv_iff in Hdommv', Himgmv'.
      rewrite 2 vertices_decomp.
      rewrite set_map_union_L.
      f_equal.
      * rewrite <- Hdommv', <- Himgmv'.
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
      * apply (f_equal referenced_vertices) in Heq.
        rewrite referenced_vertices_relabel_graph, (referenced_vertices_reindex_graph _) in Heq.
        rewrite 2 referenced_vertices_set_verts in Heq.
        rewrite Heq.
        apply set_map_ext_L.
        intros x Hx.
        rewrite (not_elem_of_dom _ _).1; [done|].
        rewrite Hdommv'.
        unfold isolated_vertices.
        rewrite not_elem_of_difference.
        now right.
    + cbn.
      etransitivity; [apply (f_equal inputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      unfold referenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      now apply elem_of_app; left.
    + cbn.
      etransitivity; [apply (f_equal outputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      unfold referenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      now apply elem_of_app; right.
Qed.



Lemma set_verts_set_verts {T} {n m} (cohg : CospanHyperGraph T n m)
  vs vs' : set_verts (set_verts cohg vs) vs' = set_verts cohg vs'.
Proof.
  done.
Qed.

Lemma set_verts_norm_verts {T} {n m} (cohg : CospanHyperGraph T n m)
  vs : set_verts (norm_verts cohg) vs = set_verts cohg vs.
Proof.
  done.
Qed.

Lemma isolated_vertices_set_verts_isolated_vertices
  {T} {n m} (cohg : CospanHyperGraph T n m) :
  isolated_vertices (set_verts cohg (isolated_vertices cohg)) =
  isolated_vertices cohg.
Proof.
  unfold isolated_vertices at 1 2.
  cbn.
  rewrite referenced_vertices_set_verts.
  unfold isolated_vertices.
  now rewrite difference_twice_L.
Qed.

(* FIXME: Move *)
#[export] Instance set_verts_cohg_vert_eq {T n m} (v : Pset) :
  Proper (cohg_vert_eq ==> cohg_vert_eq) (fun cohg => @set_verts T n m cohg v).
Proof.
  intros cohg cohg' Heq.
  unfold cohg_vert_eq.
  unfold norm_verts.
  rewrite 2 set_verts_set_verts.
  apply cohg_ext; [|apply (f_equal inputs Heq)|apply (f_equal outputs Heq)].
  apply hg_ext; [apply (f_equal (hyperedges ∘ hedges) Heq)|].
  cbn.
  rewrite 2 vertices_decomp.
  unfold isolated_vertices.
  cbn.
  rewrite 2 referenced_vertices_set_verts.
  rewrite <- referenced_vertices_norm_verts, (Heq : _ = _).
  now rewrite referenced_vertices_norm_verts.
Qed.

Lemma cohg_vert_eq_set_verts_isolated_vertices {T n m}
  (cohg : CospanHyperGraph T n m) :
  cohg ≡ᵥ set_verts cohg (isolated_vertices cohg).
Proof.
  apply cohg_vert_eq_alt_vertices.
  do 3 (split; [done|]).
  rewrite 2 vertices_decomp.
  unfold isolated_vertices.
  cbn.
  rewrite referenced_vertices_set_verts.
  rewrite difference_twice_L.
  done.
Qed.

Lemma vertices_set_verts {T n m} (cohg : CospanHyperGraph T n m) v :
  vertices (set_verts cohg v) = referenced_vertices cohg ∪ v.
Proof.
  rewrite vertices_vertices_hg_decomp.
  rewrite vertices_hg_decomp.
  cbn.
  change (referenced_vertices_hg _) with (referenced_vertices_hg cohg).
  rewrite referenced_vertices_decomp.
  now rewrite union_comm_L, union_assoc_L.
Qed.

Lemma isolated_vertices_set_verts {T n m} (cohg : CospanHyperGraph T n m) v :
  isolated_vertices (set_verts cohg v) = v ∖ referenced_vertices cohg.
Proof.
  done.
Qed.

(*
Lemma struct_isomorphic_set_verts_size_eq_isolated {T n m}
  (cohg : CospanHyperGraph T n m) (v : Pset) :
  size (isolated_vertices cohg) = size v ->
  cohg ≡ᵢ set_verts cohg v.
Proof.
  intros Hisol.
  rewrite (cohg_vert_eq_set_verts_isolated_vertices cohg) at 1.
  apply (size_set_eq_exists_map (M:=Pmap)) in Hisol as Hmv'.
  destruct Hmv' as (mv' & Hdommv' & Himgmv' & Hinj).
  apply (subrel' isomorphic).
  apply (isomorphic_of_partial_inj' _ _ (λ v, default v (mv' !! v)) id); [|easy|].
  - rewrite vertices_set_verts, union_comm_L, <- vertices_decomp.
    intros i j Hi Hj.
    destruct


  apply isomorphic_exists. *)

(* Lemma elem_of_PermutationA {A} {RA : relation A} (l l' : list A) x :  *)




Lemma cohg_syntactic_eq_of_set_verts_empty_cohg_syntactic_eq `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) :
  size (isolated_vertices cohg) = size (isolated_vertices cohg') ->
  (set_verts cohg ∅) ≡ₛ (set_verts cohg' ∅) ->
  cohg ≡ₛ cohg'.
Proof.
  intros Hverts.
  intros (cohg'' & fv & fe & Hfv & Hfe & Hheq & Heq)%cohg_syntactic_eq_exists.
  apply (size_set_eq_exists_map (M:=Pmap)) in Hverts as Hmv'.
  destruct Hmv' as (mv' & Hdommv' & Himgmv' & Hinj).

  assert (Himgfv : forall v, v ∈ referenced_vertices cohg ->
    fv v ∈ referenced_vertices cohg'). 1:{
    intros v Hv.
    apply (f_equal referenced_vertices) in Heq.
    rewrite referenced_vertices_set_verts in Heq.
    rewrite Heq.
    rewrite referenced_vertices_relabel_graph,
      (referenced_vertices_reindex_graph _).
    rewrite <- referenced_vertices_norm_verts.
    rewrite <- Hheq.
    rewrite referenced_vertices_norm_verts.
    rewrite referenced_vertices_set_verts.
    now apply elem_of_map_2.
  }

  (* refine ((elem_of_relation (_, _)).1 _). *)

  (* rewrite cohg_syntactic_eq_alt. *)
  (* apply elem_of_relation. *)
  (* cbn. *)
  transitivity (set_verts cohg'' (isolated_vertices cohg)).
  1:{
    unshelve erewrite <- (subrel' cohg_vert_eq (R2:=cohg_syntactic_eq)
      (set_verts_cohg_vert_eq _ _ _ (norm_verts_vert_eq cohg''))); shelve_unifiable.
    rewrite <- Hheq.
    rewrite set_verts_norm_verts, set_verts_set_verts.
    now rewrite <- cohg_vert_eq_set_verts_isolated_vertices.
  }
  rewrite (cohg_vert_eq_set_verts_isolated_vertices cohg').
  apply (subrel' isomorphic).
  eapply (isomorphic_of_partial_inj_dom' _ _
    (λ i, default (fv i) (mv' !! i)) fe).
  - intros i j.
    rewrite vertices_set_verts.
    rewrite <- referenced_vertices_norm_verts, <- Hheq, referenced_vertices_norm_verts.
    rewrite referenced_vertices_set_verts.
    rewrite (union_comm_L _ _).
    rewrite 2 elem_of_union.


    (* unfold isolated_vertices. *)

    (* rewrite isolated_vertices_norm_verts, referenced_vertices_norm_verts. *)
    intros [Hii|Hir];
    [apply Hdommv' in Hii as Hmi;
    apply elem_of_dom in Hmi as [mi Hmi];
    rewrite Hmi; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmi as Hmii;
    rewrite Himgmv' in Hmii
    |replace (mv' !! i) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%isolated_referenced_disjoint);
     cbn;
     specialize (Himgfv i Hir) as Hfir];
    (intros [Hji|Hjr];
    [apply Hdommv' in Hji as Hmj;
    apply elem_of_dom in Hmj as [mj Hmj];
    rewrite Hmj; cbn; apply (elem_of_map_img_2 (SA:=Pset)) in Hmj as Hmji;
    rewrite Himgmv' in Hmji
    |replace (mv' !! j) with (@None positive) by
      (now symmetry; apply not_elem_of_dom; rewrite Hdommv';
      intros ?%isolated_referenced_disjoint);
     cbn;
     specialize (Himgfv j Hjr) as Hfjr]).
    + intros <-.
      revert Hmi Hmj.
      apply Hinj.
    + intros ->.
      now apply isolated_referenced_disjoint in Hmii.
    + intros <-.
      now apply isolated_referenced_disjoint in Hmji.
    + apply Hfv.
  - intros ? ? ? ?; apply Hfe.
  - apply cohg_ext; [apply hg_ext|..].
    + cbn.
      etransitivity; [apply (f_equal (hyperedges ∘ hedges) Heq)|].
      cbn.
      apply map_fmap_ext.
      intros _ tv (i & -> & Hitv)%(lookup_kmap_Some _).
      apply relabel_abs_ext_strong.
      intros v Hv.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      apply elem_of_map_to_list in Hitv.
      unfold referenced_vertices.
      apply elem_of_union_r.
      apply elem_of_list_to_set.
      apply elem_of_list_bind.
      destruct Hheq as (_ & _ & [Hhg _]).
      apply map_to_list_equiv in Hhg.
      rewrite Forall2_lookup in Hhg.
      cbn in Hhg.
      apply elem_of_list_lookup in Hitv as (j & Hj).
      specialize (Hhg j).
      rewrite Hj in Hhg.
      rewrite option_Forall2_alt in Hhg.
      destruct ((map_to_list (hyperedges cohg)) !! j) as [(i' & tv')|] eqn:Htv; [|done].
      destruct Hhg as [[= ->] Htv'].
      apply elem_of_list_lookup_2 in Htv.
      exists (i, tv').
      cbn.
      simpl in Htv'.
      rewrite Htv'.2, Htv'.1.2.
      eauto.
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
      etransitivity; [apply (f_equal inputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      unfold referenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      pose proof Hheq.1 as Hrw.
      cbn in Hrw.
      now apply elem_of_app; left; congruence.
    + cbn.
      etransitivity; [apply (f_equal outputs Heq)|].
      cbn.
      apply vec_to_list_inj2.
      rewrite 2 vec_to_list_map.
      apply list_fmap_ext; intros _ v Hv%elem_of_list_lookup_2.
      enough (mv' !! v = None) as -> by done.
      apply not_elem_of_dom.
      rewrite Hdommv'.
      refine (disjoint_sym _ _ (isolated_referenced_disjoint cohg) _ _).
      unfold referenced_vertices.
      apply elem_of_union_l.
      apply elem_of_list_to_set.
      pose proof Hheq.2.1 as Hrw.
      cbn in Hrw.
      now apply elem_of_app; right; congruence.
Qed.

(* FIXME: Move *)
#[export] Instance vapp_inj2 {A n m} : Inj2 eq eq eq (@Vector.append A n m).
Proof.
  intros vl wl vr wr.
  intros Heq.
  apply (f_equal vsplitl) in Heq as Hl.
  apply (f_equal vsplitr) in Heq.
  rewrite 2 vsplitr_app in Heq.
  rewrite 2 vsplitl_app in Hl.
  done.
Qed.

Lemma map_equiv_by_map_to_list `{FinMap K M} `{Equiv A, Equivalence A equiv}
  (m m' : M A) :
  PermutationA (prod_relation eq equiv)
    (map_to_list m) (map_to_list m') <->
  m ≡ m'.
Proof.
  split; [|intros Heq%map_to_list_equiv; induction Heq; constructor; auto].
  intros Hperm.
  apply PermutationA_iff_exists_Forall2_Permutation in Hperm as (l'' & Hperm & Hequiv).
  transitivity (list_to_map l'' :> M A).
  - rewrite <- (list_to_map_to_list m).
    apply eq_reflexivity.
    apply list_to_map_proper, Hperm.
    apply NoDup_fst_map_to_list.
  - rewrite <- (list_to_map_to_list m').
    now apply list_to_map_equiv.
Qed.


Lemma cohg_syntactic_eq_of_is_edges_iso_isolated_vertices `{Equiv T, Equivalence T equiv} {n m}
  (cohg cohg' : CospanHyperGraph T n m) mv :
  size (isolated_vertices cohg) = size (isolated_vertices cohg') ->
  is_edges_iso mv (map_to_list cohg.(hedges).(hyperedges)).*2
    (map_to_list cohg'.(hedges).(hyperedges)).*2 ->
  map_inj mv ->
  (mv !!.) <$> (inputs cohg ++ outputs cohg) =
  Some <$> (inputs cohg' ++ outputs cohg') ->
  cohg ≡ₛ cohg'.
Proof.
  intros Hverts Hiso Hinj Hio.
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


  apply cohg_syntactic_eq_of_set_verts_empty_cohg_syntactic_eq; [done|].
  apply exists_edge_map_of_is_edges_iso in Hiso; [|now apply NoDup_fst_map_to_list..].
  destruct Hiso as (mhe & Hmhe & Hpermeq).
  rewrite (iso_relabel_reindex _ (Pmap_injmap mv) mhe).
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

Lemma pupdates_correct_fmap (ks vs : list positive) m m' :
  length ks = length vs ->
  pupdates (zip ks vs) m = Some m' ->
  (m'.(Piso_map) !!.) <$> ks = Some <$> vs.
Proof.
  intros Hlen Hm'%pupdates_correct.
  rewrite Forall_zip_with in Hm' by done.
  apply list_eq_Forall2, Forall2_fmap.
  done.
Qed.

Lemma fmap_lookup_weaken `{FinMap K M} {A} (m m' : M A)
  (ks : list K) (vs : list A) :
  m ⊆ m' -> (m!!.) <$> ks = Some <$> vs -> (m'!!.) <$> ks = Some <$> vs.
Proof.
  intros Hm.
  rewrite 2 list_eq_Forall2, 2 Forall2_fmap.
  intros Hall.
  eapply Forall2_impl; [apply Hall|].
  cbn.
  eauto using lookup_weaken.
Qed.

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

Lemma head_bind {A B} (f : A -> list B) (l : list A) :
  head (l ≫= f) = head (l ≫= from_option (λ x, [x]) [] ∘ head ∘ f).
Proof.
  induction l; [done|].
  cbn.
  destruct (f a); done.
Qed.

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



