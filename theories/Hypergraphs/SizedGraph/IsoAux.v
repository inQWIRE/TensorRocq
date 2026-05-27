From stdpp Require Export pmap.
From TensorRocq Require Import Aux_pos Aux_relset.
From TensorRocq Require Export Isomorphism.IsoAux.

(* FIXME: Move *)
Lemma map_Forall_map_inverses `{Lookup K1 K2 M1, Lookup K2 K1 M2}
  (R : K1 -> K2 -> Prop) (m1 : M1) (m2 : M2) :
  map_inverses m1 m2 -> map_Forall R m1 <-> map_Forall (flip R) m2.
Proof.
  unfold map_inverses, map_Forall.
  unfold flip.
  naive_solver.
Qed.


Record SPiso {R : relation positive} `{HR : !RelDecision R} := mk_SPiso' {
  SPiso_map : Pmap positive;
  SPiso_invmap : Pmap positive;
  SPiso_inverses' : Is_true (bool_decide (map_inverses SPiso_map SPiso_invmap));
  SPiso_prop' : Is_true (bool_decide (map_Forall R SPiso_map));
}.

#[global] Arguments SPiso _ {_} : assert.

#[global] Arguments mk_SPiso' {_ _} _ _ _ _ : assert.


Definition SPiso_Piso {R : relation positive} `{HR : !RelDecision R}
  (m : SPiso R) : Piso := mk_Piso' m.(SPiso_map) m.(SPiso_invmap) m.(SPiso_inverses').

#[global] Coercion SPiso_map : SPiso >-> Pmap.

#[global] Coercion SPiso_Piso : SPiso >-> Piso.



#[export] Instance SPiso_equiv {R HR} : Equiv (@SPiso R HR) :=
  fun m m' => m.(SPiso_map) = m'.(SPiso_map) /\
    m.(SPiso_invmap) = m'.(SPiso_invmap).


Lemma SPiso_inverses {R HR} (m : @SPiso R HR) :
  map_inverses m.(SPiso_map) m.(SPiso_invmap).
Proof.
  refine (bool_decide_unpack _ _).
  apply SPiso_inverses'.
Qed.


Lemma SPiso_prop {R HR} (m : @SPiso R HR) :
  map_Forall R m.(SPiso_map).
Proof.
  refine (bool_decide_unpack _ _).
  apply SPiso_prop'.
Qed.


Definition mk_SPiso {R HR} (m mi : Pmap positive) (Hmmi : map_inverses m mi)
  (HmR : map_Forall R m) : @SPiso R HR :=
  mk_SPiso' m mi (bool_decide_pack _ Hmmi) (bool_decide_pack _ HmR).

Definition SPiso_inverse {R HR} (m : @SPiso R HR) : SPiso (flip R) :=
  mk_SPiso m.(SPiso_invmap) m.(SPiso_map)
    ((map_inverses_comm _ _).1 (SPiso_inverses m))
    ((map_Forall_map_inverses R _ _ (SPiso_inverses m)).1 (SPiso_prop m)).


Section SPiso_facts.

Context {R : relation positive} `{HR : !RelDecision R}.

Let SPiso := (@SPiso R HR).

Implicit Types m : SPiso.


#[export] Instance SPiso_equivalence : @Equivalence SPiso equiv.
Proof.
  apply rel_intersection_equiv; refine (rel_preimage_equiv _ _ _).
Qed.

#[export] Instance SPiso_leibniz : LeibnizEquiv SPiso.
Proof.
  intros [m mi Hmi HmR] [m' mi' Hmi' HmR'] [[= <-] [= <-]].
  f_equal;
  apply proof_irrel.
Qed.



Lemma SPiso_equiv_iff (m m' : SPiso) : m ≡ m' <->
  m.(SPiso_map) = m'.(SPiso_map).
Proof.
  split; [now intros []|].
  intros Hmap.
  split; [done|].
  apply map_inverses_inj_r with m.(SPiso_map).
  - apply SPiso_inverses.
  - rewrite Hmap.
    apply SPiso_inverses.
Qed.


Add Parametric Morphism : SPiso_inverse with signature (≡@{SPiso}) ==> equiv
  as SPiso_inverse_proper.
Proof.
  now intros ? ? [].
Qed.

#[export] Instance SPiso_inverse_cancel : Cancel (@eq SPiso) SPiso_inverse SPiso_inverse.
Proof.
  intros m.
  apply leibniz_equiv_iff.
  easy.
Qed.

#[export] Instance SPiso_inverse_inj : Inj (@eq SPiso) eq (SPiso_inverse).
Proof.
  apply cancel_inj.
Qed.


#[export] Instance SPiso_empty : Empty SPiso :=
  mk_SPiso ∅ ∅ map_inverses_empty (map_Forall_empty _).


(*
#[export] Instance SPiso_delete : Delete positive SPiso :=
  fun k m =>
  mk_SPiso (delete k m.(SPiso_map)) _
    (map_inverses_delete_case _ _ k (SPiso_inverses m)).

Add Parametric Morphism : (@delete positive SPiso _) with signature
  eq ==> equiv ==> equiv as SPiso_delete_proper.
Proof.
  intros k m m' [Hm Hmi].
  split; [now unfold delete; cbn; f_equal|].
  unfold delete; cbn.
  rewrite <- Hm.
  case_match; [f_equal|]; apply Hmi.
Qed. *)


Definition spinsert (k v : positive) (m : SPiso) : option SPiso :=
  match decide_rel R k v with
  | left Hkv =>
    match m.(SPiso_map) !! k as mk
      return (mk = None -> _) -> _ with
    | Some _ => fun _ => None
    | None => fun H =>
      match m.(SPiso_invmap) !! v as mv return (mv = None -> _) -> _ with
      | Some _ => fun _ => None
      | None => fun H =>
    Some (mk_SPiso (insert k v m.(SPiso_map))
      (insert v k m.(SPiso_invmap)) (H eq_refl)
        (map_Forall_insert_2 R _ _ _ Hkv (SPiso_prop m)))
      end (H eq_refl)
    end
      (map_inverses_insert_fresh m.(SPiso_map) m.(SPiso_invmap) k v (SPiso_inverses m))
  | right _ => None
  end.


(* Definition pinsert (k v : positive) (m : SPiso) : option SPiso :=
  match m.(SPiso_map) !! k as mk, m.(SPiso_invmap) !! v as mv
    return (mk = None -> mv = None -> _) -> _ with
  | None, None => fun H =>
    Some (mk_SPiso (insert k v m.(SPiso_map))
      (insert v k m.(SPiso_invmap)) (H eq_refl eq_refl))
  | _, _ => fun _ => None
  end
    (map_inverses_insert_fresh m.(SPiso_map) m.(SPiso_invmap) k v m.(SPiso_inverses)). *)

Lemma spinsert_correct k v (m : SPiso) m' :
  spinsert k v m = Some m' ->
  pinsert k v m = Some (m' :> Piso).
Proof.
  unfold spinsert, pinsert.
  case_match; [|done].
  cbn.
  remember (map_inverses_insert_fresh _ _ _ _ _) as H' eqn:HH'.
  remember (map_inverses_insert_fresh _ _ _ _ _) as H'' eqn:HH'' in |- *.
  clear HH' HH''.
  revert H' H''.

  destruct (m.(SPiso_map) !! k); [easy|].
  destruct (m.(SPiso_invmap) !! v); [easy|].
  cbn.
  intros ? ? [= <-].
  f_equal.
  apply leibniz_equiv_iff.
  easy.
Qed.

Lemma spinsert_correct' k v (m : SPiso) m' :
  spinsert k v m = Some m' ->
  m'.(SPiso_map) = <[k := v]> m.(SPiso_map).
Proof.
  now intros ?%spinsert_correct%pinsert_correct.
Qed.

Definition spupdate k v (m : SPiso) : option SPiso :=
  match (m :> Pmap _) !! k with
  | None => spinsert k v m
  | Some v' => if decide (v = v') then Some m else None
  end.

Lemma spupdate_correct k v m m' : spupdate k v m = Some m' ->
  pupdate k v m = Some (m' :> Piso).
Proof.
  unfold spupdate, pupdate.
  cbn.
  destruct (m.(SPiso_map) !! k); [case_decide; [|done]; congruence|].
  apply spinsert_correct.
Qed.

Lemma spupdate_correct' k v m m' : spupdate k v m = Some m' ->
  m'.(SPiso_map) !! k = Some v.
Proof.
  now intros ?%spupdate_correct%pupdate_correct.
Qed.

(* Fixpoint pinserts (kvs : list (positive * positive)) (m : SPiso) : option SPiso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    pinsert k v m ≫= pinserts kvs
  end.

Lemma pinserts_correct kvs m m' :
  pinserts kvs m = Some m' ->
  list_to_map kvs ∪ m.(SPiso_map) ⊆@{Pmap _} m' /\
  list_to_set kvs.*1 ## dom m.(SPiso_map) /\
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


Fixpoint spupdates (kvs : list (positive * positive)) (m : SPiso) : option SPiso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    spupdates kvs m ≫= spupdate k v
  end.

Lemma spupdate_correct_subseteq k v m m' :
  spupdate k v m = Some m' ->
  <[k := v]> m.(SPiso_map) ⊆ m'.(SPiso_map).
Proof.
  unfold spupdate.
  case_match; [|now intros ->%spinsert_correct'].
  case_decide; [|done].
  intros [= <-].
  subst.
  now apply eq_reflexivity, insert_id.
Qed.

Lemma spupdates_correct_subseteq kvs m m' :
  spupdates kvs m = Some m' ->
  list_to_map kvs ∪ m.(SPiso_map) ⊆@{Pmap _} m'.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [intros [= <-]; cbn; now rewrite (map_empty_union _)|].
  cbn.
  intros (m'' & Heq & Hkvs)%bind_Some.
  apply spupdate_correct_subseteq in Hkvs as Hkvs'.
  rewrite <- Hkvs', <- insert_union_l.
  apply insert_mono.
  now apply IHkvs.
Qed.

Lemma spupdate_correct_extends k v m m' :
  spupdate k v m = Some m' ->
  m.(SPiso_map) ⊆ m'.(SPiso_map).
Proof.
  unfold spupdate.
  case_match eqn:Hmk; [|intros ->%spinsert_correct'; now apply insert_subseteq].
  case_decide; [|done].
  now intros [= <-].
Qed.

Lemma spupdates_correct_extends kvs m m' :
  spupdates kvs m = Some m' ->
  m.(SPiso_map) ⊆@{Pmap _} m'.
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [now intros [= <-]|].
  cbn.
  intros (m'' & Heq & Hkvs)%bind_Some.
  apply spupdate_correct_extends in Hkvs as Hkvs'.
  rewrite <- Hkvs'.
  now apply IHkvs in Heq.
Qed.


Lemma spupdates_correct kvs m m' :
  spupdates kvs m = Some m' ->
  pupdates kvs m = Some (m' :> Piso).
Proof.
  revert m m'; induction kvs as [|[k v] kvs IHkvs];
  intros m m'; [now intros [= <-]|].
  cbn.
  rewrite bind_Some.
  intros (m'' & Hm & Hm'').
  apply IHkvs in Hm.
  apply spupdate_correct in Hm''.
  rewrite Hm.
  apply Hm''.
Qed.

Lemma spupdates_correct' kvs m m' :
  spupdates kvs m = Some m' ->
  Forall (λ '(k, v), m'.(SPiso_map) !! k = Some v) kvs.
Proof.
  now intros ?%spupdates_correct%pupdates_correct.
Qed.

Lemma spinsert_spec_1 k v m m' :
  spinsert k v m = Some m' -> R k v /\ m'.(SPiso_map) = <[k := v]> m.(SPiso_map) /\
    m'.(SPiso_invmap) = <[v := k]> m.(SPiso_invmap) /\
    (SPiso_map m) !! k = None /\ (SPiso_invmap m) !! v = None.
Proof.
  intros Heq.
  split; [|generalize Heq; now intros ?%spinsert_correct%pinsert_spec_1].
  revert Heq.
  unfold spinsert.
  case_match; easy.
Qed.

Lemma spinsert_spec' k v m m' :
  spinsert k v m = Some m' <-> R k v /\ pinsert k v m = Some (m' :> Piso).
Proof.
  unfold spinsert, pinsert.
  case_match; [|split; intros; exfalso; naive_solver].
  cbn.
  remember (map_inverses_insert_fresh _ _ _ _ _) as H' eqn:HH'.
  remember (map_inverses_insert_fresh _ _ _ _ _) as H'' eqn:HH'' in |- *.
  clear HH' HH''.
  revert H' H''.

  destruct (m.(SPiso_map) !! k); [easy|].
  destruct (m.(SPiso_invmap) !! v); [easy|].
  cbn.
  intros ? ?.
  rewrite (@and_is_True_l (R k v)) by done.
  split.
  - intros [= <-].
    f_equal.
    apply leibniz_equiv_iff.
    easy.
  - intros [= Hm' Hminv].
    f_equal.
    apply leibniz_equiv_iff.
    split; done.
Qed.

Lemma spinsert_spec k v m m' :
  spinsert k v m = Some m' <-> R k v /\ m'.(SPiso_map) = <[k := v]> m.(SPiso_map) /\
    (SPiso_map m) !! k = None /\ (SPiso_invmap m) !! v = None.
Proof.
  rewrite spinsert_spec', pinsert_spec.
  done.
Qed.

Lemma spinsert_is_Some k v m :
  is_Some (spinsert k v m) <->
    R k v /\ m.(SPiso_map) !! k = None /\ m.(SPiso_invmap) !! v = None.
Proof.
  split; [now intros [? ?%spinsert_spec]|].
  intros [Hm Hmi].
  unfold spinsert.
  remember (map_inverses_insert_fresh _ _ _ _ _) as Hprf eqn:Hprfeq.
  clear Hprfeq.
  case_match; [|done].
  case_match; [easy|].
  case_match; easy.
Qed.

Lemma spupdate_correct_insert k v m m' :
  spupdate k v m = Some m' -> m'.(SPiso_map) = <[k := v]> m.(SPiso_map).
Proof.
  unfold spupdate.
  destruct (m.(SPiso_map) !! k) as [mk|] eqn:Hmk.
  - case_decide; [subst|done].
    intros [= <-].
    symmetry.
    now apply insert_id.
  - apply spinsert_correct'.
Qed.

Lemma SPiso_invmap_subseteq m m' :
  SPiso_map m ⊆ SPiso_map m' -> SPiso_invmap m ⊆ SPiso_invmap m'.
Proof.
  intros Hsubs.
  rewrite map_subseteq_spec in *.
  intros k v.
  rewrite <- 2 (SPiso_inverses _ _ _).
  apply Hsubs.
Qed.

Lemma spinsert_comm_bind k1 v1 k2 v2 m :
  spinsert k1 v1 m ≫= spinsert k2 v2 = spinsert k2 v2 m ≫= spinsert k1 v1.
Proof.
  apply option_eq; intros m2.
  rewrite 2 bind_Some.
  split.
  - intros (m1 & (HR1 & Heq & Heqi & Hmk1 & Hmiv1)%spinsert_spec_1 &
      (HR2 & Heq' & Heqi' & Hm1k2 & Hmi1v2)%spinsert_spec_1).
    assert (Hins : is_Some (spinsert k2 v2 m)). 1:{
      apply spinsert_is_Some.
      rewrite Heq in Hm1k2.
      apply lookup_insert_None in Hm1k2.
      split; [done|].
      split; [apply Hm1k2|].
      rewrite Heqi in Hmi1v2.
      apply lookup_insert_None in Hmi1v2.
      apply Hmi1v2.
    }
    destruct Hins as (m3 & Hm3ins).
    pose proof Hm3ins as (? & Hm3 & Hmi3 & Hmk2 & Hmiv2)%spinsert_spec_1.
    exists m3.
    split; [done|].
    apply spinsert_spec.
    split; [done|].
    assert (Hk1k2 : k1 <> k2) by now rewrite Heq, lookup_insert_None in Hm1k2.
    assert (Hv1v2 : v1 <> v2) by now rewrite Heqi, lookup_insert_None in Hmi1v2.
    rewrite Hm3.
    rewrite lookup_insert_ne by done.
    rewrite Hmi3.
    rewrite lookup_insert_ne by done.
    split; [|done].
    rewrite Heq', Heq.
    now apply insert_commute.
  - intros (m1 & (HR1 & Heq & Heqi & Hmk1 & Hmiv1)%spinsert_spec_1 &
      (HR2 & Heq' & Heqi' & Hm1k2 & Hmi1v2)%spinsert_spec_1).
    assert (Hins : is_Some (spinsert k1 v1 m)). 1:{
      apply spinsert_is_Some.
      rewrite Heq in Hm1k2.
      apply lookup_insert_None in Hm1k2.
      split; [done|].
      split; [apply Hm1k2|].
      rewrite Heqi in Hmi1v2.
      apply lookup_insert_None in Hmi1v2.
      apply Hmi1v2.
    }
    destruct Hins as (m3 & Hm3ins).
    pose proof Hm3ins as (? & Hm3 & Hmi3 & Hmk2 & Hmiv2)%spinsert_spec_1.
    exists m3.
    split; [done|].
    apply spinsert_spec.
    split; [done|].
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

Lemma spupdates_perm kvs kvs' m m' :
  kvs ≡ₚ kvs' -> spupdates kvs m = Some m' -> spupdates kvs' m = Some m'.
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
    destruct (spupdates l m) as [m''|]; [|done].
    cbn.
    unfold spupdate at 2.
    case_match eqn:Hm''k1. 1:{
      case_decide; [|done].
      cbn.
      subst.
      intros Heq.
      rewrite Heq.
      cbn.
      apply spupdate_correct_extends in Heq as Heq'.
      unfold spupdate.
      eapply lookup_weaken in Hm''k1 as Hm'k1; [|eassumption].
      rewrite Hm'k1.
      now apply decide_True.
    }
    intros (m1 & Hm1 & Hupd)%bind_Some.
    revert Hupd.
    unfold spupdate at 1.
    apply spinsert_correct' in Hm1 as Hm1eq.
    rewrite Hm1eq.
    rewrite lookup_insert_case.
    case_decide as Hk1k2. 1:{
      case_decide; [|done].
      intros [= <-].
      subst.
      unfold spupdate at 2.
      rewrite Hm''k1, Hm1.
      cbn.
      unfold spupdate.
      rewrite Hm1eq, lookup_insert.
      now apply decide_True.
    }
    case_match eqn:Hm''k2. 1:{
      case_decide; [|done].
      subst.
      intros [= <-].
      unfold spupdate at 2.
      rewrite Hm''k2.
      rewrite decide_True by done.
      cbn.
      unfold spupdate.
      rewrite Hm''k1.
      done.
    }
    intros Hm2.
    unfold spupdate at 2.
    rewrite Hm''k2.
    replace (Some m') with (spinsert k2 v2 m'' ≫= spinsert k1 v1);
    [|rewrite spinsert_comm_bind, Hm1; apply Hm2].
    destruct (spinsert k2 v2 m'') as [m3|] eqn:Hm3; [|done].
    cbn.
    unfold spupdate.
    apply spinsert_spec_1 in Hm3.
    rewrite Hm3.2.1.
    rewrite lookup_insert_ne by done.
    now rewrite Hm''k1.
  - eauto.
Qed.





Lemma spupdates_app kvs kvs' m :
  spupdates (kvs ++ kvs') m =
  spupdates kvs' m ≫= spupdates kvs.
Proof.
  induction kvs as [|[k v] kvs IHkvs].
  - cbn.
    now destruct (spupdates kvs' m).
  - cbn.
    rewrite IHkvs.
    now rewrite option_bind_assoc.
Qed.

Lemma extend_posmap_SPiso_map kvs m m' :
  spupdates kvs m = Some m' ->
  extend_posmap kvs m.(SPiso_map) = Some m'.(SPiso_map).
Proof.
  now intros ?%spupdates_correct%extend_posmap_Piso_map.
Qed.


#[export] Instance spupdates_perm_Proper :
  Proper ((≡ₚ) ==> eq ==> eq) spupdates.
Proof.
  intros kvs kvs' Hkvs m _ <-.
  apply option_eq; intros m'.
  split; now apply spupdates_perm.
Qed.

Lemma spupdates_cons_alt k v kvs m :
  spupdates ((k, v) :: kvs) m =
  spupdate k v m ≫= spupdates kvs.
Proof.
  rewrite (ltac:(solve_Permutation) : (k, v) :: kvs ≡ₚ kvs ++ [(k, v)]).
  rewrite spupdates_app.
  done.
Qed.


Lemma SPiso_map_inj (m : SPiso) : map_inj m.(SPiso_map).
Proof.
  apply (map_inverses_map_inj_l _ _ (SPiso_inverses m)).
Qed.

Lemma SPiso_invmap_inj (m : SPiso) : map_inj m.(SPiso_invmap).
Proof.
  apply (map_inverses_map_inj_l _ _ (SPiso_inverses (SPiso_inverse m))).
Qed.

End SPiso_facts.





Record WSPiso {R : relation positive} `{HR : !RelDecision R} := mk_WSPiso {
  WSPiso_map : Pmap positive;
  WSPiso_invmap : Pmap positive;
}.

#[global] Arguments WSPiso _ {_} : assert.

#[global] Arguments mk_WSPiso {_ _} _ _ : assert.

Definition SPiso_to_weak {R HR} (m : @SPiso R HR) : WSPiso R :=
  mk_WSPiso m.(SPiso_map) m.(SPiso_invmap).

Section WSPiso_facts.

Context {R : relation positive} `{HR : !RelDecision R}.

Let SPiso := (@SPiso R HR).
Let WSPiso := (@WSPiso R HR).

Implicit Types m : WSPiso.


#[export] Instance WSPiso_empty : Empty WSPiso := mk_WSPiso ∅ ∅.

Definition wspinsert (k v : positive) (m : WSPiso) : option WSPiso :=
  if decide_rel R k v then
    match m.(WSPiso_map) !! k with
    | Some _ => None
    | None =>
      match m.(WSPiso_invmap) !! v with
      | Some _ => None
      | None =>
        Some (mk_WSPiso (insert k v m.(WSPiso_map))
          (insert v k m.(WSPiso_invmap)))
      end
    end
  else None.

Definition wspupdate (k v : positive) (m : WSPiso) : option WSPiso :=
  match m.(WSPiso_map) !! k with
  | Some v' => if decide (v = v') then Some m else None
  | None =>
    match m.(WSPiso_invmap) !! v with
    | Some _ => None
    | None =>
      if decide_rel R k v then
        Some (mk_WSPiso (insert k v m.(WSPiso_map))
          (insert v k m.(WSPiso_invmap)))
      else None
    end
  end.

Fixpoint wspupdates (kvs : list (positive * positive)) (m : WSPiso) : option WSPiso :=
  match kvs with
  | [] => Some m
  | (k, v) :: kvs =>
    wspupdate k v m ≫= wspupdates kvs
  end.

Lemma WSPiso_empty_correct : ∅ = SPiso_to_weak ∅.
Proof.
  done.
Qed.

Lemma wspinsert_correct k v (m : SPiso) :
  wspinsert k v (SPiso_to_weak m) = SPiso_to_weak <$> spinsert k v m.
Proof.
  unfold wspinsert, spinsert.
  generalize (map_inverses_insert_fresh m.(SPiso_map) m.(SPiso_invmap) k v (SPiso_inverses m)).
  intros Heq.
  cbn.
  case_match; [|done].
  case_match; [done|].
  case_match; done.
Qed.

Lemma wspupdate_alt k v m :
  wspupdate k v m =
  match m.(WSPiso_map) !! k with
  | Some v' => if decide (v = v') then Some m else None
  | None => wspinsert k v m
  end.
Proof.
  unfold wspupdate.
  case_match eqn:Hmk; [done|].
  unfold wspinsert.
  rewrite Hmk.
  repeat first [done | case_match | case_decide].
Qed.

Lemma wspupdate_correct k v (m : SPiso) :
  wspupdate k v (SPiso_to_weak m) = SPiso_to_weak <$> spupdate k v m.
Proof.
  rewrite wspupdate_alt.
  unfold spupdate.
  cbn.
  case_match; [now case_decide|].
  apply wspinsert_correct.
Qed.


Lemma wspupdates_correct kvs (m : SPiso) :
  wspupdates kvs (SPiso_to_weak m) = SPiso_to_weak <$> spupdates kvs m.
Proof.
  revert m; induction kvs as [|(k, v) kvs IHkvs]; intros m; [done|].
  rewrite spupdates_cons_alt.
  cbn.
  rewrite wspupdate_correct.
  rewrite option_bind_fmap, option_fmap_bind.
  apply option_bind_ext; [|done].
  intros m'.
  apply IHkvs.
Qed.

End WSPiso_facts.















Fixpoint list_nth_bind {A B} (f : nat -> A -> B + nat)
  (n : nat) (l : list A) : B + nat :=
  match l with
  | [] => inr n
  | x :: l =>
    match f n x with
    | inl b => inl b
    | inr n' =>
      list_nth_bind f n' l
    end
  end.

Lemma list_nth_bind_eq_nth {A B} (f : A -> list B) n l :
  list_nth_bind (fun n a => from_option inl (inr (n - length (f a))) (f a !! n)) n l =
  from_option inl (inr (n - length (l ≫= f))) ((l ≫= f) !! n).
Proof.
  revert n; induction l; intros n;
  [cbn; now rewrite Nat.sub_0_r|].
  cbn.
  rewrite lookup_app.
  destruct (f a !! n); [done|cbn].
  rewrite IHl.
  do 2 f_equal.
  rewrite length_app.
  lia.
Qed.

Lemma list_nth_bind_ext {A B} (f g : nat -> A -> B + nat) n l :
  (forall n x, x ∈ l -> f n x = g n x) ->
  list_nth_bind f n l = list_nth_bind g n l.
Proof.
  intros Hl'.
  assert (Hl : Forall (fun x => forall n, f n x = g n x) l) by
    (rewrite Forall_forall; naive_solver).
  clear Hl'.
  revert n;
  induction Hl as [|x l Hx Hl IHl]; [done|]; intros n.
  cbn.
  rewrite <- Hx.
  case_match; [done|].
  auto.
Qed.