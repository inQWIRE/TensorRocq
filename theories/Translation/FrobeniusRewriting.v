From TensorRocq Require Import GraphRewriting CospanHyperGraph.Facts.

#[export] Instance exists_option_Some_prop_dec {A} (P : A -> Prop)
  `{HP : forall a, Decision (P a)} (ma : option A) :
    Decision (exists a, ma = Some a /\ P a).
  destruct ma as [a|].
  - refine (cast_if (decide (P a))).
    + abstract (eauto).
    + abstract (naive_solver).
  - right.
    abstract (naive_solver).
Defined.

#[local] Instance exists_elem_of_FinSet_dec `{FinSet A SA} (X : SA) :
  Decision (exists x, x ∈ X).
  refine (cast_if (decide (0 < size X))).
  - abstract (now apply size_pos_elem_of).
  - abstract (assert (Hsize : size X = 0) by lia;
    apply size_empty_iff in Hsize;
    now intros (? & []%Hsize%elem_of_empty)).
Defined.


(* Local Hint Extern 0 (Decision (exists X, ?ma = Some X /\ @?f X)) =>
  notypeclasses refine (exists_option_Some_prop_dec f ma) : typeclass_instances. *)

Definition map_preimage `{Lookup K V M, ElemOf K SK, Lookup V SK MV}
  (m : M) (mpre : MV) :=
  (forall k v, m !! k = Some v <-> exists X, mpre !! v = Some X /\ k ∈ X) /\
  (forall v X, mpre !! v = Some X -> exists k, k ∈ X).

Lemma map_preimage_alt `{Lookup K V M, ElemOf K SK, Lookup V SK MV}
  (m : M) (mpre : MV) : map_preimage m mpre <->
  map_Forall (λ k v, exists X, mpre !! v = Some X /\ k ∈ X) m /\
  map_Forall (λ v X, set_Forall (λ k, m !! k = Some v) X /\
    exists k, k ∈ X) mpre.
Proof.
  split.
  - intros Hpreim.
    split.
    + intros k v Hkv.
      apply Hpreim in Hkv as (X & -> & Hk).
      eauto.
    + intros v X HvX.
      split.
      * intros k Hk.
        rewrite (Hpreim.1 k v).
        eauto.
      * now apply Hpreim.2 in HvX.
  - intros [Hm Hmpre].
    split.
    + intros k v.
      split.
      * intros Hkv.
        apply Hm in Hkv.
        destruct (mpre !! v); [|done].
        cbn in Hkv.
        eauto.
      * intros (X & HX & HkX).
        apply Hmpre in HX.
        now apply HX in HkX.
    + now intros v X [_ HvX]%Hmpre.
Qed.

#[export] Instance map_preimage_dec `{FinMap K M, FinSet K SK, RelDecision K SK elem_of,
  FinMap V MV} (m : M V) (mpre : MV SK) : Decision (map_preimage m mpre).
  refine (cast_if (decide (
    map_Forall (λ k v, exists X, mpre !! v = Some X /\ k ∈ X) m /\
  map_Forall (λ v X, set_Forall (λ k, m !! k = Some v) X /\
    exists k, k ∈ X) mpre)));
  abstract (now rewrite map_preimage_alt).
Defined.

Lemma map_preimage_unique_l `{FinMap K M, ElemOf K SK, Lookup V SK MV}
  (m m' : M V) (mpre : MV) :
  map_preimage m mpre -> map_preimage m' mpre ->
  m = m'.
Proof.
  intros Hm Hm'.
  apply map_eq; intros k.
  apply option_eq; intros v.
  rewrite (Hm.1 k v), (Hm'.1 k v).
  done.
Qed.

Lemma map_preimage_spec_r `{FinMapDom K M SK, Elements K SK, !FinSet K SK,
  !LeibnizEquiv SK, FinMap V MV} (m : M V) (mpre : MV SK) :
  map_preimage m mpre ->
  forall v X,
  mpre !! v = Some X <->
  X ≠ ∅ /\
  X = dom (filter (λ kv, kv.2 = v) m).
Proof.
  intros Hm v X.
  split.
  - intros Hv.
    apply Hm.2 in Hv as HXne.
    destruct HXne as (k & Hk).
    split; [now intros HX; now rewrite HX, elem_of_empty in Hk|].
    symmetry.
    apply dom_filter_L.
    cbn.
    intros k'.
    apply map_preimage_alt in Hm as Hm'.
    destruct Hm' as [Hm' Hmpre].
    apply Hmpre in Hv as HX.
    split.
    + intros Hk'%(HX.1).
      eauto.
    + intros (v' & Hv'%Hm' & ->).
      rewrite Hv in Hv'.
      now destruct Hv' as (_ & [= <-] & ?).
  - intros [HXne ->].
    apply set_choose_L in HXne as Hk.
    destruct Hk as (k & (_ & (Hmkv & [= ->])%map_lookup_filter_Some)%elem_of_dom).
    apply map_preimage_alt in Hm as [Hm Hmpre].
    apply Hm in Hmkv as (X' & Hmprev & Hk).
    rewrite Hmprev.
    f_equal.
    symmetry.
    apply dom_filter_L.
    cbn.
    cbn.
    intros k'.
    apply Hmpre in Hmprev as HX.
    split.
    + intros Hk'%(HX.1).
      eauto.
    + intros (v' & Hv'%Hm & ->).
      rewrite Hmprev in Hv'.
      now destruct Hv' as (_ & [= <-] & ?).
Qed.

Lemma map_preimage_unique_r `{FinMapDom K M SK, Elements K SK, !FinSet K SK,
  !LeibnizEquiv SK, FinMap V MV}
  (m : M V) (mpre mpre' : MV SK) :
  map_preimage m mpre -> map_preimage m mpre' ->
  mpre = mpre'.
Proof.
  intros Hmpre Hmpre'.
  apply map_eq; intros v.
  apply option_eq; intros X.
  rewrite (map_preimage_spec_r _ _ Hmpre), (map_preimage_spec_r _ _ Hmpre').
  done.
Qed.

Record Psurj := mk_Psurj' {
  Psurj_map : Pmap positive;
  Psurj_invmap : Pmap Pset;
  Psurj_preimage' :
    bool_decide (map_preimage Psurj_map Psurj_invmap)
}.


#[global] Coercion Psurj_map : Psurj >-> Pmap.

#[export] Instance Psurj_equiv : Equiv Psurj :=
  fun m m' => m.(Psurj_map) = m'.(Psurj_map) /\
    m.(Psurj_invmap) = m'.(Psurj_invmap).

#[export] Instance Psurj_equivalence : @Equivalence Psurj equiv.
Proof.
  apply rel_intersection_equiv; refine (rel_preimage_equiv _ _ _).
Qed.

#[export] Instance Psurj_leibniz : LeibnizEquiv Psurj.
Proof.
  intros [m mi Hmi] [m' mi' Hmi'] [[= <-] [= <-]].
  f_equal.
  apply proof_irrel.
Qed.

Lemma Psurj_preimage m : map_preimage m.(Psurj_map) m.(Psurj_invmap).
Proof.
  refine (bool_decide_unpack _ _).
  apply Psurj_preimage'.
Qed.

Definition mk_Psurj (m : Pmap positive) mi (Hmmi : map_preimage m mi) : Psurj :=
  mk_Psurj' m mi (bool_decide_pack _ Hmmi).


Lemma Psurj_equiv_iff (m m' : Psurj) : m ≡ m' <->
  m.(Psurj_map) = m'.(Psurj_map).
Proof.
  split; [now intros []|].
  intros Hmap.
  split; [done|].
  apply map_preimage_unique_r with m.(Psurj_map).
  - apply Psurj_preimage.
  - rewrite Hmap.
    apply Psurj_preimage.
Qed.

Lemma map_preimage_empty `{FinMap K M, ElemOf K SK, FinMap V MV} :
  map_preimage (∅ :> M V) (∅ :> MV SK).
Proof.
  hnf.
  setoid_rewrite lookup_empty.
  naive_solver.
Qed.

(* FIXME: Move *)
Lemma lookup_partial_alter_case `{FinMap K M} {A} (m : M A) f k k' :
  partial_alter f k m !! k' = if decide (k = k') then f (m !! k) else m !! k'.
Proof.
  case_decide.
  - subst; apply lookup_partial_alter.
  - now apply lookup_partial_alter_ne.
Qed.

Lemma map_preimage_disjoint_r `{FinMap K M, SemiSet K SK, FinMap V MV}
  (m : M V) (mpre : MV SK) (Hm : map_preimage m mpre) v v' X X' k :
  mpre !! v = Some X -> mpre !! v' = Some X' -> k ∈ X -> k ∈ X' -> v = v'.
Proof.
  intros Hv Hv' HkX HkX'.
  apply map_preimage_alt in Hm as [_ Hmpre].
  apply Hmpre in Hv, Hv'.
  apply Hv.1 in HkX.
  apply Hv'.1 in HkX'.
  congruence.
Qed.

(* Lemma map_preimage_inj_l `{FinMap K M, SemiSet K SK, FinMap V MV}
  (m : M V) (mpre : MV SK) (Hm : map_preimage m mpre) k k' v :
  m !! k = Some v -> m !! k' = Some v ->
  mpre !! v
  mpre !! v = Some X -> mpre !! v' = Some X' -> k ∈ X -> k ∈ X' -> v = v'. *)

(* FIXME: Move *)
Lemma size_pos_iff_elem_of `{FinSet A C} (X : C) :
  0 < size X <-> exists x, x ∈ X.
Proof.
  split; [apply size_pos_elem_of|].
  intros Hx.
  enough (size X <> 0) by lia.
  intros HX%size_empty_iff.
  now destruct Hx as (? & []%HX%elem_of_empty).
Qed.


Lemma map_preimage_insert `{FinMap K M, FinSet K SK, FinMap V MV}
  (m : M V) (mpre : MV SK) k v :
  map_preimage m mpre ->
  map_preimage (<[k := v]> m) (
    match m !! k with
    | None =>
      partial_alter (λ X, Some $ from_option ({[k]} ∪.) {[k]} X) v mpre
    | Some v' =>
      partial_alter (λ X, Some $ from_option ({[k]} ∪.) {[k]} X) v
        (partial_alter (λ mX,
          X ← mX;
          let X' := X ∖ {[k]} in
          if decide (0 < size X') then Some X' else None) v' mpre)
    end).
Proof.
  intros Hm.
  destruct (m !! k) as [v'|] eqn:Hmk.
  - split.
    + intros k1 v1.
      rewrite lookup_insert_case.
      case_decide as Hk.
      1:{
        subst k1.
        rewrite lookup_partial_alter_case.
        case_decide as Hvv'.
        - subst v1.
          split; [|done].
          intros _.
          eexists; split; [done|].
          destruct (partial_alter _ _ _ !! _); [apply elem_of_union_l|];
            now apply elem_of_singleton_2.
        - split; [now intros [= ->]|].
          intros (X & HlookX & HkX).
          exfalso.
          rewrite lookup_partial_alter_case in HlookX.
          case_decide as Hv'v1.
          + apply Hvv'.
            subst v'.
            apply bind_Some in HlookX as (X' & HX' & HX'X).
            cbn in HX'X.
            case_decide as HX; [|done].
            injection HX'X as <-.
            contradict HkX.
            set_solver - Hm Hmk Hvv' HX' HX.
          + apply Hv'v1.
            apply Hm in Hmk as (X' & Hv' & HkX').
            eapply (map_preimage_disjoint_r _ _ Hm); eauto.
       }
       rewrite lookup_partial_alter_case.
       case_decide as Hvv1.
       1:{
        subst v1.
        rewrite lookup_partial_alter_case.
        case_decide as Hvv'.
        - subst v'.
          rewrite Hm.1.
          split.
          + intros (X & Hmprev & Hk1).
            eexists; split; [done|].
            rewrite Hmprev.
            cbn.
            rewrite decide_True. 2:{
              rewrite size_pos_iff_elem_of.
              exists k1.
              apply elem_of_difference.
              split; [done|].
              now apply not_elem_of_singleton.
            }
            cbn.
            apply elem_of_union_r.
            apply elem_of_difference.
            split; [done|].
            now apply not_elem_of_singleton.
          + intros (_ & [= <-] & Hk1X).
            destruct (mpre !! v) as [X|] eqn:Hmprev.
            2:{
              exfalso.
              cbn in Hk1X.
              now apply elem_of_singleton, symmetry in Hk1X.
            }
            cbn in Hk1X.
            case_decide; [|exfalso; set_solver].
            cbn in Hk1X.
            exists X.
            split; [done|].
            set_solver.
        - rewrite Hm.1.
          split.
          + intros (? & -> & ?).
            eexists; split; [done|].
            cbn.
            now apply elem_of_union_r.
          + intros (? & [= <-] & Hk1).
            destruct (mpre !! v); [|cbn in Hk1; exfalso; set_solver].
            cbn in Hk1.
            eexists; split; [done|].
            set_solver.
      }
      rewrite lookup_partial_alter_case.
      case_decide as Hv'v1.
      1:{
        subst v1.
        rewrite Hm.1.
        split.
        + intros (X & HX & Hk1).
          rewrite HX.
          cbn.
          eexists.
          rewrite decide_True. 2:{
            rewrite size_pos_iff_elem_of.
            exists k1.
            apply elem_of_difference.
            split; [done|].
            now apply not_elem_of_singleton.
          }
          split; [done|].
          set_solver.
        + intros (X' & (X & HX & HfX)%bind_Some & Hk1).
          rewrite HX.
          cbn in HfX.
          case_decide; [|done].
          injection HfX as <-.
          set_solver.
      }
      apply Hm.
    + intros v1 X.
      rewrite lookup_partial_alter_Some.
      intros [[-> [= <-]] | [Hvv1 Hlook]];
      [exists k; unfold from_option; case_match; set_solver|].
      revert Hlook.

      rewrite lookup_partial_alter_Some, bind_Some.
      intros [[<- (X' & HX' & HX)] | [_ Hmprev%(Hm.2)]]; [|done].
      cbv zeta in HX.
      case_decide; [|done].
      injection HX as <-.
      now apply size_pos_elem_of.
  - split.
    2:{
      intros v' X.
      rewrite lookup_partial_alter_Some.
      intros [[-> [= <-]] | [_ Hmprev%(Hm.2)]];
      [exists k; unfold from_option; case_match; set_solver|done].
    }
    intros k' v'.
    rewrite lookup_insert_case, lookup_partial_alter_case.
    case_decide as Hk.
    1:{
      subst k'.
      split.
      - intros [= <-].
        rewrite decide_True by done.
        eexists; split; [done|].
        destruct (mpre !! _); [apply elem_of_union_l|];
          now apply elem_of_singleton_2.
      - case_decide; [now intros _; subst|].
        intros (X & HmpreX & HkX).
        exfalso.
        apply map_preimage_alt in Hm as [_ Hmpre].
        apply Hmpre in HmpreX.
        apply HmpreX.1 in HkX.
        congruence.
    }
    rewrite Hm.1.
    case_decide; [|done].
    subst v'.
    destruct (mpre !! v) as [X|]; cbn.
    + split; intros (? & [= <-] & ?); eexists; (split; [done|]);
      [apply elem_of_union_r|]; [done|set_solver].
    + split; [naive_solver|].
      intros (? & [= <-] & []%elem_of_singleton%symmetry%Hk).
Qed.

Definition Pmap_preimage (p : Pmap positive) : Pmap Pset :=
  set_to_map (λ v, (v, dom (filter (λ kv, kv.2 = v) p))) (map_img p :> Pset).

Lemma map_preimage_Pmap_preimage p : map_preimage p (Pmap_preimage p).
Proof.
  apply map_preimage_alt.
  split.
  - intros k v Hkv.
    apply (elem_of_map_img_2 (SA:=Pset)) in Hkv as Hv.
    unfold Pmap_preimage.
    eexists.
    rewrite lookup_set_to_map by done.
    split; [now exists v|].
    apply elem_of_dom.
    unfold is_Some. 
    setoid_rewrite map_lookup_filter_Some.
    cbn.
    rewrite Hkv.
    eauto.
  - unfold Pmap_preimage.
    intros v X HX.
    rewrite lookup_set_to_map in HX by done.
    destruct HX as (_ & Hv & [= -> <-]).
    apply elem_of_map_img in Hv as (k & Hkv).
    split.
    + intros k' [v' Hk']%elem_of_dom.
      now apply map_lookup_filter_Some in Hk' as [-> [= <-]].
    + exists k.
      apply elem_of_dom.
      eexists.
      rewrite map_lookup_filter_Some.
      eauto.
Qed.

Definition Psurj_of_Pmap p : Psurj :=
  mk_Psurj p (Pmap_preimage p) (map_preimage_Pmap_preimage p).

Definition frob_enlarge_graph {T n m}
  (cohg : CospanHyperGraph T n m)
    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *)
    CospanHyperGraph T (j + i + n) m :=
  mk_cohg
    (mk_hg
      (map_imap (λ e tio,
        if decide (is_Some (me.(Psurj_invmap) !! e)) then None
          else
            Some $ relabel_abs (λ v,
              if decide (is_Some (mv.(Psurj_invmap) !! v)) then
                (encode (e, v))~1~1
              else
                v~0~1)
              tio) (hyperedges cohg))
      (set_omap (λ v, if decide (is_Some (mv.(Psurj_invmap) !! v))
        then None else Some v~0~1) (vertices cohg)))
    (vmap xO (subouts +++ subins) +++ vmap (xI ∘ xO) (inputs cohg)) (* TODO: What should we do on the boundary here??? *)
    (vmap (xI ∘ xO) (outputs cohg)).



(* The nontrivial fibers of g : frob_enlarge_graph cohg -> cohg
  all (TODO: Check) arise from the boundary K; specifically,
  a valid match should satisfy that the only vertices in the image
  of mv are vertices in K *)
(*
Definition frob_fiber {T n m}
  {i j} (subins : vec positive i) (subouts : vec positive j)
  (enlarged_cohg : CospanHyperGraph T (j + i + n) m)
  (k : positive) : Pset :=
  set_omap (λ v,
    match v with
    | v'~1 => if decide (v' = v)) (vertices enlarged_cohg).

    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *) :
      list Pset :=

Definition frob_fibers {T n m}
  (cohg : CospanHyperGraph T n m)
    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *) :
      list Pset :=

*)


