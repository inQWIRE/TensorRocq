From stdpp Require Export pmap.
Require Import Aux_pos Aux_relset.


Record Piso := mk_Piso' {
  Piso_map : Pmap positive;
  Piso_invmap : Pmap positive;
  Piso_inverses' : Is_true (bool_decide (map_inverses Piso_map Piso_invmap));
}.

#[global] Coercion Piso_map : Piso >-> Pmap.

#[export] Instance Piso_equiv : Equiv Piso :=
  fun m m' => m.(Piso_map) = m'.(Piso_map) /\
    m.(Piso_invmap) = m'.(Piso_invmap).

#[export] Instance Piso_equivalence : @Equivalence Piso equiv.
Proof.
  apply rel_intersection_equiv; refine (rel_preimage_equiv _ _ _).
Qed.

#[export] Instance Piso_leibniz : LeibnizEquiv Piso.
Proof.
  intros [m mi Hmi] [m' mi' Hmi'] [[= <-] [= <-]].
  f_equal.
  apply proof_irrel.
Qed.

Lemma Piso_inverses m : map_inverses m.(Piso_map) m.(Piso_invmap).
Proof.
  refine (bool_decide_unpack _ _).
  apply Piso_inverses'.
Qed.

Definition mk_Piso (m mi : Pmap positive) (Hmmi : map_inverses m mi) : Piso :=
  mk_Piso' m mi (bool_decide_pack _ Hmmi).


Lemma Piso_equiv_iff (m m' : Piso) : m ≡ m' <->
  m.(Piso_map) = m'.(Piso_map).
Proof.
  split; [now intros []|].
  intros Hmap.
  split; [done|].
  apply map_inverses_inj_r with m.(Piso_map).
  - apply Piso_inverses.
  - rewrite Hmap.
    apply Piso_inverses.
Qed.


#[export] Instance Piso_empty : Empty Piso :=
  mk_Piso ∅ ∅ map_inverses_empty.

Definition Piso_inverse (m : Piso) : Piso :=
  mk_Piso m.(Piso_invmap) m.(Piso_map)
    ((map_inverses_comm _ _).1 (Piso_inverses m)).

Add Parametric Morphism : Piso_inverse with signature equiv ==> equiv
  as Piso_inverse_proper.
Proof.
  now intros ? ? [].
Qed.

#[export] Instance Piso_delete : Delete positive Piso :=
  fun k m =>
  mk_Piso (delete k m.(Piso_map)) _
    (map_inverses_delete_case _ _ k (Piso_inverses m)).

Add Parametric Morphism : (@delete positive Piso _) with signature
  eq ==> equiv ==> equiv as Piso_delete_proper.
Proof.
  intros k m m' [Hm Hmi].
  split; [now unfold delete; cbn; f_equal|].
  unfold delete; cbn.
  rewrite <- Hm.
  case_match; [f_equal|]; apply Hmi.
Qed.


Definition pinsert (k v : positive) (m : Piso) : option Piso :=
  match m.(Piso_map) !! k as mk
    return (mk = None -> _) -> _ with
  | Some _ => fun _ => None
  | None => fun H =>
    match m.(Piso_invmap) !! v as mv return (mv = None -> _) -> _ with
    | Some _ => fun _ => None
    | None => fun H =>
  Some (mk_Piso (insert k v m.(Piso_map))
    (insert v k m.(Piso_invmap)) (H eq_refl))
    end (H eq_refl)
  end
    (map_inverses_insert_fresh m.(Piso_map) m.(Piso_invmap) k v (Piso_inverses m)).


(* Definition pinsert (k v : positive) (m : Piso) : option Piso :=
  match m.(Piso_map) !! k as mk, m.(Piso_invmap) !! v as mv
    return (mk = None -> mv = None -> _) -> _ with
  | None, None => fun H =>
    Some (mk_Piso (insert k v m.(Piso_map))
      (insert v k m.(Piso_invmap)) (H eq_refl eq_refl))
  | _, _ => fun _ => None
  end
    (map_inverses_insert_fresh m.(Piso_map) m.(Piso_invmap) k v m.(Piso_inverses)). *)

Lemma pinsert_correct k v (m : Piso) m' :
  pinsert k v m = Some m' ->
  m'.(Piso_map) = <[k := v]> m.(Piso_map).
Proof.
  unfold pinsert.
  generalize (map_inverses_insert_fresh m.(Piso_map) m.(Piso_invmap) k v (Piso_inverses m)).
  do 2 (case_match; [done|]).
  intros ? [= <-].
  done.
Qed.

Definition pupdate k v (m : Piso) : option Piso :=
  match (m :> Pmap _) !! k with
  | None => pinsert k v m
  | Some v' => if decide (v = v') then Some m else None
  end.

Lemma pupdate_correct k v m m' : pupdate k v m = Some m' ->
  m'.(Piso_map) !! k = Some v.
Proof.
  unfold pupdate.
  case_match eqn:Hmk; [now case_decide; congruence|].
  intros ->%pinsert_correct.
  apply lookup_insert.
Qed.

(* Fixpoint pinserts (kvs : list (positive * positive)) (m : Piso) : option Piso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    pinsert k v m ≫= pinserts kvs
  end.

Lemma pinserts_correct kvs m m' :
  pinserts kvs m = Some m' ->
  list_to_map kvs ∪ m.(Piso_map) ⊆@{Pmap _} m' /\
  list_to_set kvs.*1 ## dom m.(Piso_map) /\
  NoDup kvs.*1 /\ NoDup kvs.*2.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [intros [= <-]; cbn; now rewrite (map_empty_union _)|].
  cbn.
  intros (m'' & Heq%pinsert_correct & <-%IHkvs)%bind_Some.
  rewrite Heq.

  pose proof Heq as Heq'.
  pose proof Hkvs as Hkvs'.

  etransitivity
  rewrite Hkvs. *)


Fixpoint pupdates (kvs : list (positive * positive)) (m : Piso) : option Piso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    pupdates kvs m ≫= pupdate k v
  end.

Lemma pupdate_correct_subseteq k v m m' :
  pupdate k v m = Some m' ->
  <[k := v]> m.(Piso_map) ⊆ m'.(Piso_map).
Proof.
  unfold pupdate.
  case_match; [|now intros ->%pinsert_correct].
  case_decide; [|done].
  intros [= <-].
  subst.
  now apply eq_reflexivity, insert_id.
Qed.

Lemma pupdates_correct_subseteq kvs m m' :
  pupdates kvs m = Some m' ->
  list_to_map kvs ∪ m.(Piso_map) ⊆@{Pmap _} m'.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [intros [= <-]; cbn; now rewrite (map_empty_union _)|].
  cbn.
  intros (m'' & Heq & Hkvs)%bind_Some.
  apply pupdate_correct_subseteq in Hkvs as Hkvs'.
  rewrite <- Hkvs', <- insert_union_l.
  apply insert_mono.
  now apply IHkvs.
Qed.

Lemma pupdate_correct_extends k v m m' :
  pupdate k v m = Some m' ->
  m.(Piso_map) ⊆ m'.(Piso_map).
Proof.
  unfold pupdate.
  case_match eqn:Hmk; [|intros ->%pinsert_correct; now apply insert_subseteq].
  case_decide; [|done].
  now intros [= <-].
Qed.

Lemma pupdates_correct_extends kvs m m' :
  pupdates kvs m = Some m' ->
  m.(Piso_map) ⊆@{Pmap _} m'.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [now intros [= <-]|].
  cbn.
  intros (m'' & Heq & Hkvs)%bind_Some.
  apply pupdate_correct_extends in Hkvs as Hkvs'.
  rewrite <- Hkvs'.
  now apply IHkvs in Heq.
Qed.

Lemma pupdates_correct kvs m m' :
  pupdates kvs m = Some m' ->
  Forall (λ '(k, v), m'.(Piso_map) !! k = Some v) kvs.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [done|].
  intros Heq.
  constructor.
  - apply pupdates_correct_subseteq in Heq.
    cbn in Heq.
    revert Heq.
    apply lookup_weaken.
    rewrite <- insert_union_l.
    apply lookup_insert.
  - cbn in Heq.
    apply bind_Some in Heq as (m'' & Hkvs & Heq).
    apply IHkvs in Hkvs as Hall.
    eapply Forall_impl; [apply Hall|].
    intros (k', v') Hlook.
    apply pupdate_correct_extends in Heq.
    revert Heq.
    now apply lookup_weaken.
Qed.

Lemma pinsert_spec_1 k v m m' :
  pinsert k v m = Some m' -> m'.(Piso_map) = <[k := v]> m.(Piso_map) /\
    m'.(Piso_invmap) = <[v := k]> m.(Piso_invmap) /\
    (Piso_map m) !! k = None /\ (Piso_invmap m) !! v = None.
Proof.
  unfold pinsert.
  remember (map_inverses_insert_fresh _ _ _ _ _) as Hprf eqn:Hprfeq.
  clear Hprfeq.
  case_match; [done|].
  case_match; [done|].
  intros [= <-].
  done.
Qed.

Lemma pinsert_spec k v m m' :
  pinsert k v m = Some m' <-> m'.(Piso_map) = <[k := v]> m.(Piso_map) /\
    (Piso_map m) !! k = None /\ (Piso_invmap m) !! v = None.
Proof.
  split.
  - unfold pinsert.
    remember (map_inverses_insert_fresh _ _ _ _ _) as Hprf eqn:Hprfeq.
    clear Hprfeq.
    case_match; [done|].
    case_match; [done|].
    intros [= <-].
    done.
  - unfold pinsert.
    remember (map_inverses_insert_fresh _ _ _ _ _) as Hprf eqn:Hprfeq.
    clear Hprfeq.
    intros (Hm' & Hmk & Hmik).
    case_match; [done|].
    case_match; [done|].
    f_equal.
    apply leibniz_equiv_iff, Piso_equiv_iff.
    now cbn.
Qed.

Lemma pinsert_is_Some k v m :
  is_Some (pinsert k v m) <-> m.(Piso_map) !! k = None /\ m.(Piso_invmap) !! v = None.
Proof.
  split; [now intros [? ?%pinsert_spec]|].
  intros [Hm Hmi].
  unfold pinsert.
  remember (map_inverses_insert_fresh _ _ _ _ _) as Hprf eqn:Hprfeq.
  clear Hprfeq.
  case_match; [done|].
  case_match; [done|].
  trivial.
Qed.

Lemma pupdate_correct_insert k v m m' :
  pupdate k v m = Some m' -> m'.(Piso_map) = <[k := v]> m.(Piso_map).
Proof.
  unfold pupdate.
  destruct (m.(Piso_map) !! k) as [mk|] eqn:Hmk.
  - case_decide; [subst|done].
    intros [= <-].
    symmetry.
    now apply insert_id.
  - apply pinsert_correct.
Qed.

Lemma Piso_invmap_subseteq m m' :
  Piso_map m ⊆ Piso_map m' -> Piso_invmap m ⊆ Piso_invmap m'.
Proof.
  intros Hsubs.
  rewrite map_subseteq_spec in *.
  intros k v.
  rewrite <- 2 (Piso_inverses _ _ _).
  apply Hsubs.
Qed.

Lemma pinsert_comm_bind k1 v1 k2 v2 m :
  pinsert k1 v1 m ≫= pinsert k2 v2 = pinsert k2 v2 m ≫= pinsert k1 v1.
Proof.
  apply option_eq; intros m2.
  rewrite 2 bind_Some.
  split.
  - intros (m1 & (Heq & Heqi & Hmk1 & Hmiv1)%pinsert_spec_1 &
      (Heq' & Heqi' & Hm1k2 & Hmi1v2)%pinsert_spec_1).
    assert (Hins : is_Some (pinsert k2 v2 m)). 1:{
      apply pinsert_is_Some.
      rewrite Heq in Hm1k2.
      apply lookup_insert_None in Hm1k2.
      split; [apply Hm1k2|].
      rewrite Heqi in Hmi1v2.
      apply lookup_insert_None in Hmi1v2.
      apply Hmi1v2.
    }
    destruct Hins as (m3 & Hm3ins).
    pose proof Hm3ins as (Hm3 & Hmi3 & Hmk2 & Hmiv2)%pinsert_spec_1.
    exists m3.
    split; [done|].
    apply pinsert_spec.
    assert (Hk1k2 : k1 <> k2) by now rewrite Heq, lookup_insert_None in Hm1k2.
    assert (Hv1v2 : v1 <> v2) by now rewrite Heqi, lookup_insert_None in Hmi1v2.
    rewrite Hm3.
    rewrite lookup_insert_ne by done.
    rewrite Hmi3.
    rewrite lookup_insert_ne by done.
    split; [|done].
    rewrite Heq', Heq.
    now apply insert_commute.
  - intros (m1 & (Heq & Heqi & Hmk1 & Hmiv1)%pinsert_spec_1 &
      (Heq' & Heqi' & Hm1k2 & Hmi1v2)%pinsert_spec_1).
    assert (Hins : is_Some (pinsert k1 v1 m)). 1:{
      apply pinsert_is_Some.
      rewrite Heq in Hm1k2.
      apply lookup_insert_None in Hm1k2.
      split; [apply Hm1k2|].
      rewrite Heqi in Hmi1v2.
      apply lookup_insert_None in Hmi1v2.
      apply Hmi1v2.
    }
    destruct Hins as (m3 & Hm3ins).
    pose proof Hm3ins as (Hm3 & Hmi3 & Hmk2 & Hmiv2)%pinsert_spec_1.
    exists m3.
    split; [done|].
    apply pinsert_spec.
    assert (Hk1k2 : k1 <> k2) by now rewrite Heq, lookup_insert_None in Hm1k2.
    assert (Hv1v2 : v1 <> v2) by now rewrite Heqi, lookup_insert_None in Hmi1v2.
    rewrite Hm3.
    rewrite lookup_insert_ne by done.
    rewrite Hmi3.
    rewrite lookup_insert_ne by done.
    split; [|done].
    rewrite Heq', Heq.
    now apply insert_commute.
Qed.

Lemma pupdates_perm kvs kvs' m m' :
  kvs ≡ₚ kvs' -> pupdates kvs m = Some m' -> pupdates kvs' m = Some m'.
Proof.
  intros Hkvs.
  revert m m'.
  induction Hkvs; intros m m'.
  - done.
  - cbn.
    case_match; subst.
    intros (m'' & Hkvs' & Heq)%bind_Some.
    apply IHHkvs in Hkvs'.
    rewrite Hkvs'.
    now cbn.
  - cbn.
    destruct x as [k1 v1], y as [k2 v2].
    cbn.
    destruct (pupdates l m) as [m''|]; [|done].
    cbn.
    unfold pupdate at 2.
    case_match eqn:Hm''k1. 1:{
      case_decide; [|done].
      cbn.
      subst.
      intros Heq.
      rewrite Heq.
      cbn.
      apply pupdate_correct_extends in Heq as Heq'.
      unfold pupdate.
      eapply lookup_weaken in Hm''k1 as Hm'k1; [|eassumption].
      rewrite Hm'k1.
      now apply decide_True.
    }
    intros (m1 & Hm1 & Hupd)%bind_Some.
    revert Hupd.
    unfold pupdate at 1.
    apply pinsert_correct in Hm1 as Hm1eq.
    rewrite Hm1eq.
    rewrite lookup_insert_case.
    case_decide as Hk1k2. 1:{
      case_decide; [|done].
      intros [= <-].
      subst.
      unfold pupdate at 2.
      rewrite Hm''k1, Hm1.
      cbn.
      unfold pupdate.
      rewrite Hm1eq, lookup_insert.
      now apply decide_True.
    }
    case_match eqn:Hm''k2. 1:{
      case_decide; [|done].
      subst.
      intros [= <-].
      unfold pupdate at 2.
      rewrite Hm''k2.
      rewrite decide_True by done.
      cbn.
      unfold pupdate.
      rewrite Hm''k1.
      done.
    }
    intros Hm2.
    unfold pupdate at 2.
    rewrite Hm''k2.
    replace (Some m') with (pinsert k2 v2 m'' ≫= pinsert k1 v1);
    [|rewrite pinsert_comm_bind, Hm1; apply Hm2].
    destruct (pinsert k2 v2 m'') as [m3|] eqn:Hm3; [|done].
    cbn.
    unfold pupdate.
    apply pinsert_spec_1 in Hm3.
    rewrite Hm3.1.
    rewrite lookup_insert_ne by done.
    now rewrite Hm''k1.
  - eauto.
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

Lemma extend_posmap_one_Piso_map k v m m' :
  pinsert k v m = Some m' ->
  extend_posmap_one k v m.(Piso_map) = Some m'.(Piso_map).
Proof.
  intros Heq.
  apply pinsert_spec in Heq.
  unfold extend_posmap_one.
  rewrite Heq.2.1, Heq.1.
  done.
Qed.


Lemma extend_posmap_one_Piso_map' k v m m' :
  pupdate k v m = Some m' ->
  extend_posmap_one k v m.(Piso_map) = Some m'.(Piso_map).
Proof.
  unfold pupdate.
  case_match eqn:Hmk; [|apply extend_posmap_one_Piso_map].
  case_decide; [|done].
  subst.
  intros [= <-].
  unfold extend_posmap_one.
  rewrite Hmk.
  now apply decide_True.
Qed.

Lemma pupdates_app kvs kvs' m :
  pupdates (kvs ++ kvs') m =
  pupdates kvs' m ≫= pupdates kvs.
Proof.
  induction kvs as [|[k v] kvs IHkvs].
  - cbn.
    now destruct (pupdates kvs' m).
  - cbn.
    rewrite IHkvs.
    now rewrite option_bind_assoc.
Qed.

Lemma extend_posmap_Piso_map kvs m m' :
  pupdates kvs m = Some m' ->
  extend_posmap kvs m.(Piso_map) = Some m'.(Piso_map).
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs]; intros m m';
  [now intros [= <-]|].
  rewrite extend_posmap_cons.
  intros Heq.
  apply (pupdates_perm _ (kvs ++ [(k, v)])) in Heq as Heq'; [|solve_Permutation].
  rewrite pupdates_app in Heq'.
  cbn in Heq'.
  revert Heq'.
  intros (m'' & Hupd & Hkvs)%bind_Some.
  apply extend_posmap_one_Piso_map' in Hupd.
  rewrite Hupd.
  cbn.
  now apply IHkvs.
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


Record WPiso := mk_WPiso {
  WPiso_map : Pmap positive;
  WPiso_invmap : Pmap positive;
}.

#[export] Instance WPiso_empty : Empty WPiso := mk_WPiso ∅ ∅.

Definition wpinsert (k v : positive) (m : WPiso) : option WPiso :=
  match m.(WPiso_map) !! k with
  | Some _ => None
  | None =>
    match m.(WPiso_invmap) !! v with
    | Some _ => None
    | None =>
      Some (mk_WPiso (insert k v m.(WPiso_map))
        (insert v k m.(WPiso_invmap)))
    end
  end.

Definition wpupdate (k v : positive) (m : WPiso) : option WPiso :=
  match m.(WPiso_map) !! k with
  | Some v' => if decide (v = v') then Some m else None
  | None =>
    match m.(WPiso_invmap) !! v with
    | Some _ => None
    | None =>
      Some (mk_WPiso (insert k v m.(WPiso_map))
        (insert v k m.(WPiso_invmap)))
    end
  end.

Fixpoint wpupdates (kvs : list (positive * positive)) (m : WPiso) : option WPiso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    wpupdate k v m ≫= wpupdates kvs
  end.

Definition Piso_to_weak (m : Piso) : WPiso := mk_WPiso m.(Piso_map) m.(Piso_invmap).

Lemma WPiso_empty_correct : ∅ = Piso_to_weak ∅.
Proof.
  done.
Qed.

Lemma wpinsert_correct k v (m : Piso) :
  wpinsert k v (Piso_to_weak m) = Piso_to_weak <$> pinsert k v m.
Proof.
  unfold wpinsert, pinsert.
  generalize (map_inverses_insert_fresh m.(Piso_map) m.(Piso_invmap) k v (Piso_inverses m)).
  intros Heq.
  cbn.
  case_match; [done|].
  case_match; done.
Qed.

Lemma wpupdate_alt k v m :
  wpupdate k v m =
  match m.(WPiso_map) !! k with
  | Some v' => if decide (v = v') then Some m else None
  | None => wpinsert k v m
  end.
Proof.
  unfold wpupdate.
  case_match eqn:Hmk; [done|].
  unfold wpinsert.
  rewrite Hmk.
  done.
Qed.

Lemma wpupdate_correct k v (m : Piso) :
  wpupdate k v (Piso_to_weak m) = Piso_to_weak <$> pupdate k v m.
Proof.
  rewrite wpupdate_alt.
  unfold pupdate.
  cbn.
  case_match; [now case_decide|].
  apply wpinsert_correct.
Qed.

#[export] Instance pupdates_perm_Proper : 
  Proper ((≡ₚ) ==> eq ==> eq) pupdates.
Proof.
  intros kvs kvs' Hkvs m _ <-.
  apply option_eq; intros m'.
  split; now apply pupdates_perm.
Qed.

Lemma pupdates_cons_alt k v kvs m : 
  pupdates ((k, v) :: kvs) m = 
  pupdate k v m ≫= pupdates kvs.
Proof.
  rewrite (ltac:(solve_Permutation) : (k, v) :: kvs ≡ₚ kvs ++ [(k, v)]).
  rewrite pupdates_app.
  done.
Qed.

Lemma wpupdates_correct kvs (m : Piso) :
  wpupdates kvs (Piso_to_weak m) = Piso_to_weak <$> pupdates kvs m.
Proof.
  revert m; induction kvs as [|(k, v) kvs IHkvs]; intros m; [done|].
  rewrite pupdates_cons_alt.
  cbn.
  rewrite wpupdate_correct.
  rewrite option_bind_fmap, option_fmap_bind.
  apply option_bind_ext; [|done].
  intros m'.
  apply IHkvs.
Qed.



Fixpoint partial_permutations {A B} (R : A -> B -> Prop) `{HR : forall a b, Decision (R a b)}
  (l : list A) (l' : list B) : list (list (A * B)) :=
  match l with
  | [] => match l' with
    | [] => [[]]
    | _ :: _ => []
    end
  | a :: l => list_select (R a) l' ≫=
    λ '(b, l'), ((a, b) ::.) <$> partial_permutations R l l'
  end.

Lemma elem_of_partial_permutations {A B} (R : A -> B -> Prop) `{HR : forall a b, Decision (R a b)}
  (l : list A) (l' : list B) ll' :
  ll' ∈ partial_permutations R l l' <->
    Forall (uncurry R) ll' /\ ll'.*1 = l /\ ll'.*2 ≡ₚ l'.
Proof.
  revert l' ll'; induction l as [|a l IHl]; intros l' ll'.
  - destruct l'; [|split; cbn; [easy|
    intros (_ & ?%(f_equal length) & ?%(Permutation_length)); cbn in *;
    rewrite ?length_fmap in *; lia]].
    cbn.
    rewrite elem_of_list_singleton.
    split; [now intros ->|].
    now intros (_ & ->%fmap_nil_inv & _).
  - cbn.
    rewrite elem_of_list_bind, exists_pair.
    split.
    + intros (b & l'rest & (ll'' & -> & (Hll'' & Hfst & Hsnd)%IHl)%elem_of_list_fmap
      & [HRab Hl']%elem_of_list_select_perm_Prop).
      rewrite Forall_cons.
      cbn.
      split_and!; [done..| now f_equal|now rewrite Hl', Hsnd].
    + destruct ll' as [|(a', b) ll']; [easy|].
      rewrite Forall_cons; cbn.
      intros ((HRab & Hll') & [= -> Hfst] & (l'1 & l'2 & -> & Hsnd)%Permutation_cons_inv_l).
      exists b, (l'1 ++ l'2).
      split.
      * rewrite (elem_of_list_fmap_inj _).
        rewrite IHl.
        done.
      * rewrite elem_of_list_select.
        eauto.
Qed.

Local Open Scope nat_scope.

Fixpoint list_ordpairs {A} (l : list A) : list (A * A) :=
  match l with
  | [] => []
  | a :: l => ((a,.) <$> l) ++ list_ordpairs l
  end.



Lemma triangle_number_pred (n : nat) :
  (n + n * (n - 1) / 2 = (n + 1) * n / 2)%nat.
Proof.
  destruct n; [done|].
  cbn -[Nat.div Nat.mul].
  rewrite Nat.sub_0_r.
  rewrite 2 Nat.mul_succ_l, Nat.mul_add_distr_r, <- Nat.add_assoc.
  replace (1 * _ + _)%nat with (S n * 2)%nat by lia.
  rewrite Nat.div_add by lia.
  rewrite Nat.mul_succ_r.
  lia.
Qed.


Lemma length_list_ordpairs {A} (l : list A) :
  length (list_ordpairs l) = (length l * (length l - 1)) / 2.
Proof.
  induction l; [done|].
  cbn -[Nat.div Nat.mul].
  rewrite length_app, length_fmap, IHl.
  rewrite triangle_number_pred.
  f_equal; lia.
Qed.

Lemma elem_of_list_ordpairs {A} (l : list A) ab :
  ab ∈ list_ordpairs l <-> exists i j, i < j /\
    l !! i = Some ab.1 /\ l !! j = Some ab.2.
Proof.
  split.
  - revert ab; induction l; [easy|intros ab].
    cbn.
    rewrite elem_of_app, elem_of_list_fmap.
    intros [(b & -> & (i & Hi)%elem_of_list_lookup)|(i & j & Hij & Hli & Hlj)%IHl].
    + exists 0, (S i).
      split; [lia|easy].
    + exists (S i), (S j).
      split; [lia|easy].
  - intros (i & j & Hij & Hli & Hlj).
    revert l Hli j Hij Hlj;
    induction i as [|i IHi];
    intros l Hli j Hij Hlj.
    + destruct l as [|a l]; [easy|].
      cbn.
      rewrite elem_of_app.
      left.
      apply elem_of_list_fmap.
      exists ab.2.
      split; [now destruct ab; cbn in *; congruence|].
      destruct j; [lia|].
      cbn in Hlj.
      now apply elem_of_list_lookup_2 in Hlj.
    + destruct j; [lia|].
      destruct l as [|a l]; [easy|].
      cbn in *.
      apply elem_of_app; right.
      apply (IHi l Hli j); [lia|done].
Qed.


Fixpoint ofoldl {A B} (f : A -> B -> option A) (a : option A) (l : list B) : option A :=
  match a with
  | None => None
  | Some a =>
    match l with
    | [] => Some a
    | b :: l =>
      ofoldl f (f a b) l
    end
  end.


(* FIXME: Move *)
Definition list_first_omap {A B} (f : A -> option B) : list A -> option B :=
  fix list_first_omap l :=
  match l with
  | [] => None
  | a :: l =>
    match f a with
    | Some b => Some b
    | None => list_first_omap l
    end
  end.

Lemma list_first_omap_eq_head_bind {A B} (f : A -> option B) l :
  list_first_omap f l =
  head (x ← l; from_option (λ x, [x]) [] (f x)).
Proof.
  induction l; [done|].
  cbn.
  rewrite IHl.
  destruct (f a); reflexivity.
Qed.

Lemma list_first_omap_Some {A B} (f : A -> option B) l b :
  list_first_omap f l = Some b ->
  exists a, a ∈ l /\ f a = Some b.
Proof.
  rewrite list_first_omap_eq_head_bind.
  intros (a & Hb & Ha)%head_Some_elem_of%elem_of_list_bind.
  exists a; split; [easy|].
  destruct (f a); [|easy].
  cbn in Hb.
  rewrite elem_of_list_singleton in Hb.
  now subst.
Qed.

Lemma list_first_omap_bind {A B C} (f : A -> list B) (g : B -> option C)
  (l : list A) :
  list_first_omap g (l ≫= f) =
  list_first_omap (list_first_omap g ∘ f) l.
Proof.
  rewrite 2 list_first_omap_eq_head_bind.
  induction l; [done|].
  cbn.
  rewrite bind_app.
  rewrite 2 head_app, IHl.
  rewrite list_first_omap_eq_head_bind.
  case_match; done.
Qed.

Lemma list_first_omap_fmap {A B C} (f : A -> B) (g : B -> option C)
  (l : list A) :
  list_first_omap g (f <$> l) =
  list_first_omap (g ∘ f) l.
Proof.
  rewrite 2 list_first_omap_eq_head_bind.
  now rewrite list_fmap_bind.
Qed.


Fixpoint first_omap_partial_permutations
  {A B C} (R : A -> B -> Prop) `{HR : forall a b, Decision (R a b)}
  (f : list (A * B) -> option C)
  (l : list A) (l' : list B) : option C :=
  match l with
  | [] => match l' with
    | [] => f nil
    | _ :: _ => None
    end
  | a :: l => list_first_omap
      (λ '(b, l'), first_omap_partial_permutations R (λ ll', f ((a, b) :: ll'))
        l l') (list_select (R a) l')
  end.

Lemma first_omap_partial_permutations_correct
  {A B C} (R : A -> B -> Prop) `{HR : forall a b, Decision (R a b)}
  (f : list (A * B) -> option C) (l : list A) (l' : list B) :
  first_omap_partial_permutations R f l l' =
  list_first_omap f (partial_permutations R l l').
Proof.
  revert f l'; induction l; intros f l'.
  - destruct l'; [|done].
    cbn.
    now case_match.
  - cbn.
    rewrite list_first_omap_bind.
    rewrite 2 list_first_omap_eq_head_bind.
    f_equal.
    apply list_bind_ext; [|done].
    intros [b l'rest].
    cbn.
    rewrite IHl.
    rewrite list_first_omap_fmap.
    done.
Qed.


Lemma map_inj_subseteq `{FinMap K M} {A} (m m' : M A) :
  m ⊆ m' -> map_inj m' -> map_inj m.
Proof.
  intros Hm Hm' i j v Hmi Hmj.
  apply (fun H => lookup_weaken _ _ _ _ H Hm) in Hmi, Hmj.
  revert Hmi Hmj.
  apply Hm'.
Qed.

Lemma map_inverses_map_inj_l `{FinMap K1 M1, FinMap K2 M2}
  (m1 : M1 K2) (m2 : M2 K1) : map_inverses m1 m2 -> map_inj m1.
Proof.
  intros Hinj i j v.
  rewrite (Hinj i), (Hinj j).
  congruence.
Qed.

Lemma map_inverses_map_inj_r `{FinMap K1 M1, FinMap K2 M2}
  (m1 : M1 K2) (m2 : M2 K1) : map_inverses m1 m2 -> map_inj m2.
Proof.
  intros Hinj i j v.
  rewrite <- 2 (Hinj v).
  congruence.
Qed.

Lemma Piso_map_inj (m : Piso) : map_inj m.(Piso_map).
Proof.
  apply (map_inverses_map_inj_l _ _ (Piso_inverses m)).
Qed.








(* TODO: Unused? *)

Export SetoidList SetoidPermutation list.

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