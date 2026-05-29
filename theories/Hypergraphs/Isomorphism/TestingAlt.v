From TensorRocq Require Import CospanHyperGraph.Definitions.
From TensorRocq Require Import Isomorphism.IsoAux.




(* Want: mapping from vertices to edges *)

Definition vertex_map_union (m m' : Pmap (Pset * Pset)) :=
  union_with (fun '(i, o) '(i', o') => Some (i ∪ i', o ∪ o')) m m'.

Fixpoint vertex_map_aux {T} (hg : list (positive * (T * list positive * list positive))) :
  Pmap (Pset * Pset) :=
  match hg with
  | [] => ∅
  | (idx, (t, ins, outs)) :: hg =>
    vertex_map_union (list_to_map ((λ i, (i, ({[idx]}, ∅))) <$> ins))
      $
      vertex_map_union (list_to_map ((λ i, (i, (∅, {[idx]}))) <$> outs))
        (vertex_map_aux hg)
  end.

Definition vertex_map {T} (hg : Pmap (T * list positive * list positive)) :=
  vertex_map_aux (map_to_list hg).

#[export] Instance HyperEdge_equiv_dec `{Equiv T, !RelDecision (≡@{T})} :
  RelDecision (≡@{HyperEdge T}) :=
  fun '(t, ins, outs) '(t', ins', outs') =>
  _.

(* Fixpoint map_equiv_dec_aux `{EqDecision K, Equiv A, !RelDecision (≡@{T})}
map_to_list_proper *)

#[program] Instance map_equiv_dec `{FinMap K M, Equiv A, !RelDecision (≡@{A})} :
  RelDecision (≡@{M A}) | 100 := fun m m' =>
  cast_if (decide (Forall2 (prod_relation eq equiv) (map_to_list m) (map_to_list m'))).
Next Obligation.
  intros.
  rewrite <- (list_to_map_to_list m), <- (list_to_map_to_list m').
  now apply list_to_map_equiv.
Qed.
Next Obligation.
  intros.
  pose proof map_to_list_proper as Hprop.
  setoid_rewrite eqlistA_altdef in Hprop.
  naive_solver.
Qed.


Fixpoint Pmap_ne_forallb {A} (P : positive -> A -> bool) (m : Pmap_ne A) : bool :=
  match m with
  | PNode001 r => Pmap_ne_forallb (P ∘ xI) r
  | PNode010 a => P xH a
  | PNode011 a r => P xH a && Pmap_ne_forallb (P ∘ xI) r
  | PNode100 l => Pmap_ne_forallb (P ∘ xO) l
  | PNode101 l r => Pmap_ne_forallb (P ∘ xO) l && Pmap_ne_forallb (P ∘ xI) r
  | PNode110 l a => Pmap_ne_forallb (P ∘ xO) l && P xH a
  | PNode111 l a r => Pmap_ne_forallb (P ∘ xO) l && P xH a && Pmap_ne_forallb (P ∘ xI) r
  end.

Definition Pmap_forallb {A} (P : positive -> A -> bool) (m : Pmap A) : bool :=
  match m with
  | PEmpty => true
  | PNodes m => Pmap_ne_forallb P m
  end.

Lemma Pmap_ne_forallb_correct {A} (P : positive -> A -> bool) m :
  Pmap_ne_forallb P m <-> map_Forall (λ k a, P k a) m.
Proof.
  revert P; induction m; intros P;
  cbn; rewrite ?andb_True, ?IHm, ?IHm1, ?IHm2;
  (split; [intros ?; destruct_and?;
    intros []; (done || (intros ? [= <-]; done) || repeat_on_hyps ltac:(fun H => apply H))
    |]);
  intros Hall; split_and?; tryif apply (Hall xH) then done else
  (intros k; try apply (Hall (k~1)) || apply (Hall (k~0))) || generalize Logic.I.
Qed.

Lemma Pmap_forallb_correct {A} (P : positive -> A -> bool) (m : Pmap A) :
  Pmap_forallb P m <-> map_Forall (λ k a, P k a) m.
Proof.
  destruct m.
  - easy.
  - apply Pmap_ne_forallb_correct.
Qed.


Definition Pmap_value_relation_decb {A B}
  (R : A -> B -> bool) (P : A -> bool) (Q : B -> bool)
  (m : Pmap A) (m' : Pmap B) :=
  Pmap_forallb (λ _ v, v) (merge (fun ma mb => match ma, mb with
    | Some a, Some b => Some (R a b)
    | Some a, None => Some (P a)
    | None, Some b => Some (Q b)
    | None, None => None
    end) m m').

Lemma Pmap_value_relation_decb_correct {A B}
  (R : A -> B -> bool) (P : A -> bool) (Q : B -> bool) m m' :
  Pmap_value_relation_decb R P Q m m' <->
  map_relation (λ k, R) (λ k, P) (λ k, Q) m m'.
Proof.
  unfold Pmap_value_relation_decb.
  rewrite Pmap_forallb_correct.
  apply forall_iff; intros k.
  rewrite lookup_merge.
  destruct (m !! k), (m' !! k); cbn; naive_solver.
Qed.

Definition option_relationb {A B} (R : A -> B -> bool)
  (P : A -> bool) (Q : B -> bool) (ma : option A) (mb : option B) : bool :=
  match ma, mb with
  | Some a, Some b => R a b
  | Some a, None => P a
  | None, Some b => Q b
  | None, None => true
  end.

Lemma option_relationb_True {A B} (R : A -> B -> bool) P Q ma mb :
  option_relationb R P Q ma mb <-> option_relation R P Q ma mb.
Proof.
  destruct ma, mb; naive_solver.
Qed.

Definition option_Forall2b {A B} (R : A -> B -> bool)
  (ma : option A) (mb : option B) : bool :=
  match ma, mb with
  | Some a, Some b => R a b
  | None, None => true
  | _, _ => false
  end.

Lemma option_Forall2b_True {A B} (R : A -> B -> bool) ma mb :
  option_Forall2b R ma mb <-> option_Forall2 R ma mb.
Proof.
  rewrite <- option_relation_Forall2.
  destruct ma, mb; naive_solver.
Qed.

Definition Pmap_ne_value_relation_decb {A B}
  (R : A -> B -> bool) (P : A -> bool) (Q : B -> bool)
  (m : Pmap_ne A) (m' : Pmap_ne B) :=
  Pmap_forallb (λ _ v, v) (pmap.Pmap_ne_merge (fun ma mb => match ma, mb with
    | Some a, Some b => Some (R a b)
    | Some a, None => Some (P a)
    | None, Some b => Some (Q b)
    | None, None => None
    end) m m').

Lemma Pmap_ne_value_relation_decb_correct {A B}
  (R : A -> B -> bool) (P : A -> bool) (Q : B -> bool) m m' :
  Pmap_ne_value_relation_decb R P Q m m' <->
  map_relation (λ k, R) (λ k, P) (λ k, Q) m m'.
Proof.
  unfold Pmap_ne_value_relation_decb.
  rewrite Pmap_forallb_correct.
  apply forall_iff; intros k.
  pose proof (fun f => lookup_merge (C:=bool) f (PNodes m) (PNodes m') k) as Hlook.
  cbn in Hlook.
  rewrite Hlook.
  unfold lookup at 1 2.
  cbn.
  destruct (m !! k), (m' !! k); cbn; naive_solver.
Qed.

#[local] Instance maybe_Pmap_ne {A} : Maybe (@PNodes A) := fun m =>
  match m with
  | PNodes m => Some m
  | PEmpty => None
  end.

Fixpoint Pmap_ne_equivb {A B} (P : A -> B -> bool)
  (m : Pmap_ne A) (m' : Pmap_ne B) {struct m} : bool :=
  pmap.Pmap_ne_case m $ λ ml ma mr,
  pmap.Pmap_ne_case m' $ λ ml' mb mr',
  option_Forall2b (Pmap_ne_equivb P) (maybe PNodes ml) (maybe PNodes ml') &&
  option_Forall2b P ma mb &&
  option_Forall2b (Pmap_ne_equivb P) (maybe PNodes mr) (maybe PNodes mr').

Definition Pmap_equivb {A B} (P : A -> B -> bool)
  (m : Pmap A) (m' : Pmap B) : bool :=
  match m, m' with
  | PNodes m, PNodes m' => Pmap_ne_equivb P m m'
  | PEmpty, PEmpty => true
  | _, _ => false
  end.

Lemma PNode_equiv {A B} (P : A -> B -> Prop)
  ml ma mr ml' mb mr' :
  map_relation (λ _, P) (λ _ _, False) (λ _ _, False)
    (pmap.PNode ml ma mr) (pmap.PNode ml' mb mr') <->
  map_relation (λ _, P) (λ _ _, False) (λ _ _, False) ml ml' /\
  option_Forall2 P ma mb /\
  map_relation (λ _, P) (λ _ _, False) (λ _ _, False) mr mr'.
Proof.
  split.
  - intros Hall.
    split_and!.
    + intros k.
      specialize (Hall (k~0)).
      now rewrite 2 pmap.Pmap_lookup_PNode in Hall.
    + specialize (Hall xH).
      rewrite <- option_relation_Forall2.
      now rewrite 2 pmap.Pmap_lookup_PNode in Hall.
    + intros k.
      specialize (Hall (k~1)).
      now rewrite 2 pmap.Pmap_lookup_PNode in Hall.
  - intros [Hl [Ha%option_relation_Forall2 Hr]].
    intros k.
    rewrite 2 pmap.Pmap_lookup_PNode.
    case_match; subst; auto.
Qed.

Lemma Pmap_equivb_correct {A B} (P : A -> B -> bool)
  (m : Pmap A) (m' : Pmap B) :
  Pmap_equivb P m m' <->
  map_relation (λ _, P) (λ _ _, False) (λ _ _, False) m m'.
Proof.
  revert m';
  induction m as [|ml ma mr Hvalid IHml IHmr] using pmap.Pmap_ind;
  intros m';
  induction m' as [|ml' mb mr' Hvalid' _ _] using pmap.Pmap_ind.
  - cbn.
    split; [|done].
    intros _.
    intros k.
    done.
  - cbn.
    assert (Hm' : exists m', pmap.PNode ml' mb mr' = PNodes m') by
      now destruct ml', mb, mr'; eauto.
    destruct Hm' as [m' Hm'eq].
    rewrite Hm'eq.
    split; [done|].
    specialize (pmap.Pmap_ne_lookup_not_None m') as (i & Hi).
    intros HF.
    specialize (HF i).
    unfold lookup in HF; cbn in HF.
    now destruct (m' !! i).
  - cbn.
    assert (Hm : exists m, pmap.PNode ml ma mr = PNodes m) by
      now destruct ml, ma, mr; eauto.
    destruct Hm as [m Hmeq].
    rewrite Hmeq.
    split; [done|].
    specialize (pmap.Pmap_ne_lookup_not_None m) as (i & Hi).
    intros HF.
    specialize (HF i).
    unfold lookup in HF; cbn in HF.
    now destruct (m !! i).
  - rewrite PNode_equiv.
    rewrite <- IHml, <- IHmr.
    rewrite <- option_Forall2b_True, <- 2 andb_True.
    rewrite andb_assoc.
    destruct ml, ma, mr, ml', mb, mr'; done.
Qed.

(* TODO: Why isn't this faster??? *)
(* #[export, program] Instance Pmap_equiv_dec `{Equiv A, !RelDecision (≡@{A})} : RelDecision (≡@{Pmap A}) :=
fun m m' => cast_if (decide (Pmap_equivb (fun a b => bool_decide (a ≡ b)) m m')).
Next Obligation.
  intros A EqA EqAdec m m'.
  rewrite Pmap_equivb_correct.
  rewrite map_equiv_map_relation.
  intros Hall k.
  specialize (Hall k).
  cbn.
  destruct (m !! k), (m' !! k); [|done..].
  now apply bool_decide_spec in Hall.
Qed.
Next Obligation.
  intros A EqA EqAdec m m'.
  rewrite Pmap_equivb_correct.
  rewrite map_equiv_map_relation.
  intros HF Hall; apply HF.
  intros k.
  specialize (Hall k).
  cbn.
  destruct (m !! k), (m' !! k); [|done..].
  now apply bool_decide_spec.
Qed. *)





(* 
Fixpoint Pmap_ne_equivb {A B} (P : A -> B -> bool)
  (m : Pmap_ne A) (m' : Pmap_ne B) : bool :=
  match m, m' with
  | PNode001 r, PNode001 r' => Pmap_ne_equivb P r r'
  | PNode010 a, PNode010 b => P a b
  | PNode100 l, PNode100 l' => Pmap_ne_equivb P l l'
  | PNode011 a r, PNode011 b r' => P a b && Pmap_ne_equivb P r r'
  | PNode101 l r, PNode101 l' r' => Pmap_ne_equivb P l l' && Pmap_ne_equivb P r r'
  | PNode110 l a, PNode110 l' b => P a b && Pmap_ne_equivb P l l'
  | PNode111 l a r, PNode111 l' b r' =>
    P a b && Pmap_ne_equivb P l l' && Pmap_ne_equivb P r r'
  | _, _ => false
  end. *)




Section def.

Local Open Scope lazy_bool_scope.

Definition CospanHyperGraph_equiv_dec_bool `{Equiv T, !RelDecision (≡@{T})}
  {n m} : CospanHyperGraph T n m -> CospanHyperGraph T n m -> bool :=
  fun '(mk_cohg hg ins outs) '(mk_cohg hg' ins' outs') =>
  (Vector.eqb _ Pos.eqb ins ins' &&&
  Vector.eqb _ Pos.eqb outs outs' &&&
  bool_decide (vertices (mk_cohg hg ins outs) = vertices (mk_cohg hg' ins' outs')) &&&
  let '(mk_hg hg _) := hg in
  let '(mk_hg hg' _) := hg' in
  bool_decide (hg ≡ hg')).

End def.

Lemma CospanHyperGraph_equiv_dec_bool_correct `{Equiv T, Equivalence T equiv, !RelDecision (≡@{T})}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  CospanHyperGraph_equiv_dec_bool cohg cohg' <->
    cohg ≡ cohg'.
Proof.
  unfold CospanHyperGraph_equiv_dec_bool.
  destruct cohg as [hg ins outs], cohg' as [hg' ins' outs'].
  rewrite 3 lazy_andb_True.
  rewrite 2 (Is_true_true (Vector.eqb _ _ _ _)).
  rewrite 2 Vector.eqb_eq by apply Pos.eqb_eq.
  rewrite bool_decide_spec.
  rewrite cohg_equiv_alt'_rel.
  destruct hg as [hg hv], hg' as [hg' hv'].
  unfold cohg_eq.
  cbn.
  unfold hypergraph_equiv.
  unfold equiv at 3.
  cbn.
  rewrite <- !(and_assoc _).
  do 2 f_equiv.
  rewrite (and_comm _).
  rewrite bool_decide_spec.
  done.
Qed.

#[export] Instance CospanHyperGraph_equiv_dec `{Equiv T, Equivalence T equiv, !RelDecision (≡@{T})}
  {n m} : RelDecision (≡@{CospanHyperGraph T n m}) :=
  fun cohg cohg' =>
  match CospanHyperGraph_equiv_dec_bool cohg cohg' as b return (b <-> _) -> _ with
  | true => fun Hequiv => left (Hequiv.1 Logic.I)
  | false => fun Hequiv => right (fun Heq => False_rect _ (Hequiv.2 Heq))
  end (CospanHyperGraph_equiv_dec_bool_correct cohg cohg').


(* #[export] Instance CospanHyperGraph_equiv_dec `{Equiv T, !RelDecision (≡@{T})}
  {n m} : RelDecision (≡@{CospanHyperGraph T n m}) :=
  fun *)


(* We assume monogamy, so we have the following simplifications:
  - We only ever take the first or second element of the vertex map
  - We don't need to maintain a proof of injectivity (we don't do this yet, but
    this replaces Piso with Pmap positive) *)

Definition pupdate' (k v : positive) (m : Piso) : option (Piso * bool) :=
  match m.(Piso_map) !! k with
  | Some v' => if decide (v = v') then Some (m, true) else None
  | None => (., false) <$> pinsert k v m
  end.

Definition wpupdate' (k v : positive) (m : WPiso) : option (WPiso * bool) :=
  match m.(WPiso_map) !! k with
  | Some v' => if decide (v = v') then Some (m, true) else None
  | None => (., false) <$> wpinsert k v m
  end.


(* The atomic action is trying to extend a partial morphism by a single vertex,
  starting at a base edge *)
(* Fixpoint vertex_map_based_iso_extend_by_vert_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (v v' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ← pupdate' v v' mv;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ← vinc !! v;
      '(v'_ins, v'_outs) ← vinc' !! v;
      @Some (list _) (let v_ins' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_ins :> Pset)) in
      let v_outs' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_outs :> Pset)) in
      let v'_ins' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_ins :> Pset)) in
      let v'_outs' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_outs :> Pset)) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      edge_pairings ≫=
      λ e_s,
      foldr (fun '(e, e') mhe_mvs =>
        mhe_mvs ≫= fun mhe_mv =>
          vertex_map_based_iso_extend_by_edge_pair fuel vinc vinc' einc einc' mhe_mv e e')
        [(mhe, mv)] e_s)
    )
  end

with vertex_map_based_iso_extend_by_edge_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (e e' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    default [] (
      '(t, ins, outs) ← einc !! e;
      '(t', ins', outs') ← einc' !! e';
      if decide_rel equiv t t' then
        ins_ins' ← mayzip ins ins';
        outs_outs' ← mayzip outs outs';
        Some (
      foldr (fun '(v, v') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_vert_pair fuel vinc vinc' einc einc' mhe_mv v v')
          [mhe_mv] (ins_ins' ++ outs_outs')
        )
      else None
    )
  end. *)

(* The atomic action is trying to extend a partial morphism by a single vertex,
  starting at a base edge *)
(* Fixpoint vertex_map_based_iso_extend_by_vert_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (v v' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ← pupdate' v v' mv;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ← vinc !! v;
      '(v'_ins, v'_outs) ← vinc' !! v;
      Some (let v_ins' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_ins :> Pset)) in
      let v_outs' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_outs :> Pset)) in
      let v'_ins' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_ins :> Pset)) in
      let v'_outs' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_outs :> Pset)) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      edge_pairings ≫=
      λ e_s,
      foldr (fun '(e, e') mhe_mvs =>
        mhe_mvs ≫= fun mhe_mv =>
          vertex_map_based_iso_extend_by_edge_pair fuel vinc vinc' einc einc' mhe_mv e e')
        [(mhe, mv)] e_s)
    )
  end

with vertex_map_based_iso_extend_by_edge_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (e e' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    default [] (
      '(t, ins, outs) ← einc !! e;
      '(t', ins', outs') ← einc' !! e';
      if decide_rel equiv t t' then
        ins_ins' ← mayzip ins ins';
        outs_outs' ← mayzip outs outs';
        Some (
      foldr (fun '(v, v') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_vert_pair fuel vinc vinc' einc einc' mhe_mv v v')
          [mhe_mv] (ins_ins' ++ outs_outs')
        )
      else None
    )
  end. *)

(*
Fixpoint vertex_map_based_iso_extend_by_vert_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (v v' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ← pupdate' v v' mv;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ← vinc !! v;
      '(v'_ins, v'_outs) ← vinc' !! v;
      @Some (list _) (let v_ins' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_ins :> Pset)) in
      let v_outs' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_outs :> Pset)) in
      let v'_ins' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_ins :> Pset)) in
      let v'_outs' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_outs :> Pset)) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      if decide (edge_pairings = nil) then
        [(mhe, mv')]
      else
        ((edge_pairings ≫=
        λ e_s,
        foldr (fun '(e, e') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_edge_pair fuel vinc vinc' einc einc' mhe_mv e e')
          [(mhe, mv')] e_s) :> list _))
    )
  end

with vertex_map_based_iso_extend_by_edge_pair `{Equiv T, !RelDecision (≡@{T})}
  (fuel : nat)
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  (mhe_mv : Piso * Piso)
  (e e' : positive) {struct fuel} : list (Piso * Piso) :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mhe', unchanged) ← pupdate' e e' mhe;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(t, ins, outs) ← einc !! e;
      '(t', ins', outs') ← einc' !! e';
      if decide_rel equiv t t' then
        ins_ins' ← mayzip ins ins';
        outs_outs' ← mayzip outs outs';
        @Some (list _) (
      foldr (fun '(v, v') mhe_mvs =>
          (mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_vert_pair fuel vinc vinc' einc einc' mhe_mv v v')
            )
          [(mhe', mv)] (ins_ins' ++ outs_outs')
        )
      else None
    )
  end. *)

(* FIXME: Move *)
Notation "m ≫=@{ M } f" := (mbind (M:=M) f m) (at level 60, right associativity, only parsing) : stdpp_scope.

Notation "x ←@{ A } y ; z" := (y ≫= (λ x : A, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ←@{ A } y ; z" := (y ≫= (λ x : A, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.


Definition vertex_map_based_iso_extend_by_vert_pair `{Equiv T, !RelDecision (≡@{T})}
  (vinc vinc' : Pmap (Pset * Pset))
  (einc einc' : Pmap (T * list positive * list positive))
  : forall
  (fuel : nat)
  (mhe_mv : Piso * Piso)
  (v v' : positive), list (Piso * Piso) :=
  fix go fuel mhe_mv v v' {struct fuel} :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ←@{Piso * bool} pupdate' v v' mv;
      if unchanged :> bool return option (list (Piso * Piso)) then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ←@{Pset * Pset} vinc !! v;
      '(v'_ins, v'_outs) ←@{Pset * Pset} vinc' !! v;
      @Some (list _) (let v_ins' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_ins :> Pset)) in
      let v_outs' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (elements (v_outs :> Pset)) in
      let v'_ins' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_ins :> Pset)) in
      let v'_outs' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (elements (v'_outs :> Pset)) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      if decide (edge_pairings = nil) then
        [(mhe, mv')]
      else
        ((edge_pairings ≫=@{list}
        λ e_s,
        foldr (fun '(e, e') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            let '(mhe, mv) := mhe_mv in
            default [] (
              '(mhe', unchanged) ←@{Piso * bool} pupdate' e e' mhe;
              if unchanged :> bool then
                Some [(mhe, mv)]
              else
              '(t, ins, outs) ←@{T * list positive * list positive} einc !! e;
              '(t', ins', outs') ←@{T * list positive * list positive} einc' !! e';
              if decide_rel equiv t t' then
                ins_ins' ←@{list _} mayzip ins ins';
                outs_outs' ←@{list _} mayzip outs outs';
                @Some (list _) (
              foldr (fun '(v, v') mhe_mvs =>
                  (mhe_mvs ≫=@{list} fun mhe_mv =>
                    go fuel mhe_mv v v')
                    )
                  [(mhe', mv)] (ins_ins' ++ outs_outs')
                )
              else None
            ))
          [(mhe, mv')] e_s) :> list _))
    )
  end.

Definition graph_vertex_map {T n m} (cohg : CospanHyperGraph T n m) :=
  vertex_map cohg ∪ list_to_map ((., (∅, ∅)) <$> elements (vertices cohg)).

Definition graph_isos_by_vertex_map `{Equiv T, !RelDecision (≡@{T})}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : list (Piso * Piso) :=
  let einc : Pmap _ := cohg in let einc' : Pmap _ := cohg' in
  let vinc := graph_vertex_map cohg in let vinc' := graph_vertex_map cohg' in
  let fuel := size einc + size einc' + size vinc + size vinc'  in
  foldr (fun '(v, v') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_vert_pair vinc vinc' einc einc' fuel mhe_mv v v')
          [(∅, ∅)] (zip (inputs cohg ++ outputs cohg) (inputs cohg' ++ outputs cohg')).

Definition test_graph_isos_by_vertex_map `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos_by_vertex_map cohg cohg' with
  | [] => false
  | (mhe, mv) :: _ =>
  default false (
    isol_pairs ← mayzip
      (filter (λ v, mv.(Piso_map) !! v = None) (elements (vertices cohg)))
      (filter (λ v, mv.(Piso_invmap) !! v = None) (elements (vertices cohg')));
    mv' ← pupdates isol_pairs mv;
    Some $
    bool_decide (relabel_graph (Pmap_injmap mv'.(Piso_map))
      (reindex_graph (Pmap_injmap mhe.(Piso_map)) cohg) ≡ cohg')
  )
  end.

Lemma test_graph_isos_by_vertex_map_correct `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  test_graph_isos_by_vertex_map cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  unfold test_graph_isos_by_vertex_map.
  case_match; [done|].
  case_match; subst.
  destruct (mayzip _ _); [|done].
  cbn.
  destruct (pupdates _ _) as [mv'|]; [|done].
  cbn.
  intros Heq%bool_decide_eq_true.
  rewrite <- Heq.
  apply (subrel' isomorphic).
  constructor; apply Pmap_injmap_inj, Piso_map_inj.
Qed.



Definition vertex_map_based_iso_extend_by_vert_pair' `{Equiv T, !RelDecision (≡@{T})}
  (vinc vinc' : Pmap (list positive * list positive))
  (einc einc' : Pmap (T * list positive * list positive))
  : forall
  (fuel : nat)
  (mhe_mv : Piso * Piso)
  (v v' : positive), list (Piso * Piso) :=
  fix go fuel mhe_mv v v' {struct fuel} :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ←@{Piso * bool} pupdate' v v' mv;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ←@{list positive * list positive} vinc !! v;
      '(v'_ins, v'_outs) ←@{list positive * list positive} vinc' !! v;
      @Some (list _) (let v_ins' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (v_ins :> list positive) in
      let v_outs' : list positive := filter (λ e, (mhe.(Piso_map) !! e) = None) (v_outs :> list positive) in
      let v'_ins' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (v'_ins :> list positive) in
      let v'_outs' : list positive := filter (λ e, (mhe.(Piso_invmap) !! e) = None) (v'_outs :> list positive) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      if decide (edge_pairings = nil) then
        [(mhe, mv')]
      else
        ((edge_pairings ≫=@{list}
        λ e_s,
        foldr (fun '(e, e') mhe_mvs =>
          mhe_mvs ≫=@{list} fun mhe_mv =>
            let '(mhe, mv) := mhe_mv in
            default [] (
              '(mhe', unchanged) ←@{Piso * bool} pupdate' e e' mhe;
              if unchanged :> bool then
                Some [(mhe, mv)]
              else
              '(t, ins, outs) ←@{T * list positive * list positive} einc !! e;
              '(t', ins', outs') ←@{T * list positive * list positive} einc' !! e';
              if decide_rel equiv t t' then
                ins_ins' ←@{list (positive * positive)} mayzip ins ins';
                outs_outs' ←@{list (positive * positive)} mayzip outs outs';
                @Some (list _) (
              foldr (fun '(v, v') mhe_mvs =>
                  (mhe_mvs ≫=@{list} fun mhe_mv =>
                    go fuel mhe_mv v v')
                    )
                  [(mhe', mv)] (ins_ins' ++ outs_outs')
                )
              else None
            ))
          [(mhe, mv')] e_s) :> list _))
    )
  end.


Definition graph_isos_by_vertex_map' `{Equiv T, !RelDecision (≡@{T})}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : list (Piso * Piso) :=
  let einc : Pmap _ := cohg in let einc' : Pmap _ := cohg' in
  let vinc := prod_map elements elements <$> graph_vertex_map cohg in
  let vinc' := prod_map elements elements <$> graph_vertex_map cohg' in
  let fuel := size einc + size einc' + size vinc + size vinc'  in
  foldr (fun '(v, v') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            vertex_map_based_iso_extend_by_vert_pair' vinc vinc' einc einc' fuel mhe_mv v v')
          [(∅, ∅)] (zip (inputs cohg ++ outputs cohg) (inputs cohg' ++ outputs cohg')).

Definition test_graph_isos_by_vertex_map' `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos_by_vertex_map' cohg cohg' with
  | [] => false
  | (mhe, mv) :: _ =>
  default false (
    isol_pairs ← mayzip
      (filter (λ v, mv.(Piso_map) !! v = None) (elements (vertices cohg)))
      (filter (λ v, mv.(Piso_invmap) !! v = None) (elements (vertices cohg')));
    mv' ← pupdates isol_pairs mv;
    Some $
    bool_decide (relabel_graph (Pmap_injmap mv'.(Piso_map))
      (reindex_graph (Pmap_injmap mhe.(Piso_map)) cohg) ≡ cohg')
  )
  end.


Definition test_graph_isos_by_vertex_map'' `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match graph_isos_by_vertex_map' cohg cohg' with
  | [] => false
  | (mhe, mv) :: _ =>
  default false (
    isol_pairs ← mayzip
      (filter (λ v, mv.(Piso_map) !! v = None) (elements (vertices cohg)))
      (filter (λ v, mv.(Piso_invmap) !! v = None) (elements (vertices cohg')));
    mv' ← pupdates isol_pairs mv;
    Some $
    bool_decide (
      map_Forall (λ k _, is_Some (mhe.(Piso_map) !! k)) (hyperedges cohg) /\
    relabel_graph (mv'.(Piso_map)!!!.)
      (reindex_graph (mhe.(Piso_map)!!!.) cohg) ≡ cohg')
  )
  end.

(* FIXME: Move *)
Lemma map_inj_lookup_total `{FinMapDom K M D} `{Inhabited A}
  (m : M A) : map_inj m ->
  set_Forall2 (λ i j, m !!! i = m !!! j -> i = j) (dom m).
Proof.
  intros Hm i j (mi & Hmi)%elem_of_dom (mj & Hmj)%elem_of_dom.
  rewrite 2 lookup_total_alt, Hmi, Hmj.
  cbn.
  intros <-.
  eapply Hm; eauto.
Qed.

Lemma map_inj_lookup_total' `{FinMapDom K M D} `{Inhabited A}
  (X : D) (m : M A) : map_inj m -> X ⊆ dom m ->
  set_Forall2 (λ i j, m !!! i = m !!! j -> i = j) X.
Proof.
  intros Hm ->.
  now apply map_inj_lookup_total.
Qed.

Lemma test_graph_isos_by_vertex_map''_correct_aux `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m)
  (mv mhe : Pmap positive) :
  map_inj mv -> map_inj mhe ->
  vertices cohg ⊆ dom mv ->
  dom (hyperedges cohg) ⊆ dom mhe ->
  relabel_graph (mv!!!.)
      (reindex_graph (mhe!!!.) cohg) ≡ cohg' ->
  cohg ≡ₛ cohg'.
Proof.
  intros Hmv Hmhe Hdommv Hdommhe <-.
  apply (subrel' isomorphic).
  eapply isomorphic_of_partial_inj_dom', reflexivity.
  - now apply map_inj_lookup_total'.
  - now apply map_inj_lookup_total'.
Qed.



Lemma test_graph_isos_by_vertex_map''_correct `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  test_graph_isos_by_vertex_map'' cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  unfold test_graph_isos_by_vertex_map''.
  destruct (graph_isos_by_vertex_map' _ _) as [|[mhe mv] _]; [done|].
  destruct (mayzip _ _) as [isol_isol'|] eqn:Hisol; [|done].
  cbn.
  destruct (pupdates _ _) as [mv'|] eqn:Hmv'; [|done].
  cbn.
  intros [Hall Heq]%bool_decide_eq_true.
  revert Heq.
  apply test_graph_isos_by_vertex_map''_correct_aux.
  - apply Piso_map_inj.
  - apply Piso_map_inj.
  - intros v Hv.
    destruct_decide (decide (v ∈ dom mv.(Piso_map))) as Hvmv.
    + apply pupdates_correct_extends, subseteq_dom in Hmv'.
      now apply Hmv', Hvmv.
    + apply pupdates_correct in Hmv'.
      apply mayzip_Some in Hisol as [Hlen ->].
      assert (Hvel : v ∈ filter (λ k, mv.(Piso_map) !! k = None) (elements (vertices cohg))).
      1:{
        apply elem_of_list_filter.
        split; [now apply not_elem_of_dom|].
        now apply elem_of_elements.
      }
      apply elem_of_list_lookup in Hvel as [i Hi].
      apply lookup_lt_Some in Hi as Hilt.
      rewrite <- (Nat.min_id (length _)) in Hilt.
      rewrite Hlen in Hilt at 2.
      rewrite <- length_zip in Hilt.
      apply lookup_lt_is_Some in Hilt as [[v' u] Hvv'].
      rewrite Forall_lookup in Hmv'.
      specialize (Hmv' i _ Hvv').
      apply lookup_zip_Some in Hvv' as [Hv' Hu].
      rewrite Hi in Hv'.
      injection Hv' as <-.
      now apply elem_of_dom_2 in Hmv'.
  - intros e [tio Htio]%elem_of_dom.
    now apply Hall in Htio as He%elem_of_dom.
Qed.


Definition weak_vertex_map_based_iso_extend_by_vert_pair' `{Equiv T, !RelDecision (≡@{T})}
  (vinc vinc' : Pmap (list positive * list positive))
  (einc einc' : Pmap (T * list positive * list positive))
  : forall
  (fuel : nat)
  (mhe_mv : WPiso * WPiso)
  (v v' : positive), list (WPiso * WPiso) :=
  fix go fuel mhe_mv v v' {struct fuel} :=
  match fuel with
  | 0 => []
  | S fuel =>
    let '(mhe, mv) := mhe_mv in
    default [] (
      '(mv', unchanged) ←@{WPiso * bool} wpupdate' v v' mv;
      if unchanged :> bool then
        Some [(mhe, mv)]
      else
      '(v_ins, v_outs) ← vinc !! v;
      '(v'_ins, v'_outs) ← vinc' !! v;
      @Some (list _) (let v_ins' : list positive := filter (λ e, (mhe.(WPiso_map) !! e) = None) (v_ins :> list positive) in
      let v_outs' : list positive := filter (λ e, (mhe.(WPiso_map) !! e) = None) (v_outs :> list positive) in
      let v'_ins' : list positive := filter (λ e, (mhe.(WPiso_invmap) !! e) = None) (v'_ins :> list positive) in
      let v'_outs' : list positive := filter (λ e, (mhe.(WPiso_invmap) !! e) = None) (v'_outs :> list positive) in
      let edge_pairings : list (list (positive * positive)) :=
        map (uncurry app) (list_prod (map (zip v_ins') (permutations v'_ins'))
          (map (zip v_outs') (permutations v'_outs'))) in
      if decide (edge_pairings = nil) then
        [(mhe, mv')]
      else
        ((edge_pairings ≫=
        λ e_s,
        foldr (fun '(e, e') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            let '(mhe, mv) := mhe_mv in
            default [] (
              '(mhe', unchanged) ←@{WPiso * bool} wpupdate' e e' mhe;
              if unchanged :> bool then
                Some [(mhe, mv)]
              else
              '(t, ins, outs) ← einc !! e;
              '(t', ins', outs') ← einc' !! e';
              if decide_rel equiv t t' then
                ins_ins' ← mayzip ins ins';
                outs_outs' ← mayzip outs outs';
                @Some (list _) (
              foldr (fun '(v, v') mhe_mvs =>
                  (mhe_mvs ≫= fun mhe_mv =>
                    go fuel mhe_mv v v')
                    )
                  [(mhe', mv)] (ins_ins' ++ outs_outs')
                )
              else None
            ))
          [(mhe, mv')] e_s) :> list _))
    )
  end.


Definition weak_graph_isos_by_vertex_map' `{Equiv T, !RelDecision (≡@{T})}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : list (WPiso * WPiso) :=
  let einc : Pmap _ := cohg in let einc' : Pmap _ := cohg' in
  let vinc := prod_map elements elements <$> graph_vertex_map cohg in
  let vinc' := prod_map elements elements <$> graph_vertex_map cohg' in
  let fuel := size einc + size einc' + size vinc + size vinc'  in
  foldr (fun '(v, v') mhe_mvs =>
          mhe_mvs ≫= fun mhe_mv =>
            weak_vertex_map_based_iso_extend_by_vert_pair' vinc vinc' einc einc' fuel mhe_mv v v')
          [(∅, ∅)] (zip (inputs cohg ++ outputs cohg) (inputs cohg' ++ outputs cohg')).

(* FIXME: Move *)
Lemma dist_from_option {A B C} (g : B -> C) (f : A -> B) (d : B) ma :
  g (from_option f d ma) = from_option (g ∘ f) (g d) ma.
Proof.
  now destruct ma.
Qed.
Lemma dist_default {A B} (f : A -> B) (d : A) (ma : option A) :
  f (default d ma) = default (f d) (f <$> ma).
Proof.
  now destruct ma.
Qed.
Lemma wpupdate'_correct k v m :
  wpupdate' k v (Piso_to_weak m) = prod_map Piso_to_weak id <$> pupdate' k v m.
Proof.
  unfold wpupdate', pupdate'.
  cbn.
  case_match; [case_decide; done|].
  rewrite wpinsert_correct.
  rewrite <- 2 option_fmap_compose.
  done.
Qed.


Lemma weak_vertex_map_based_iso_extend_by_vert_pair'_correct `{Equiv T, !RelDecision (≡@{T})}
  (vinc vinc' : Pmap (list positive * list positive)) (einc einc' : Pmap (HyperEdge T))
  (fuel : nat) (mhe_mv : Piso * Piso) v v' :
  weak_vertex_map_based_iso_extend_by_vert_pair'
    vinc vinc' einc einc'
    fuel (prod_map Piso_to_weak Piso_to_weak mhe_mv) v v' =
  prod_map Piso_to_weak Piso_to_weak <$>
  vertex_map_based_iso_extend_by_vert_pair' vinc vinc' einc einc' fuel mhe_mv v v'.
Proof.
  revert mhe_mv v v'; induction fuel; intros mhe_mv v v'; [done|].
  cbv delta [weak_vertex_map_based_iso_extend_by_vert_pair'
    vertex_map_based_iso_extend_by_vert_pair'] beta fix match.
  destruct mhe_mv as [mhe mv].
  rewrite dist_default, fmap_nil.
  cbv delta [prod_map fst snd] beta match.
  rewrite wpupdate'_correct.
  rewrite option_fmap_bind, option_bind_fmap.
  f_equal.
  apply option_bind_ext, reflexivity.
  intros [mv' unchanged].
  cbv delta [compose prod_map fst snd] beta match.
  change (id ?x) with x.
  destruct unchanged; [done|].
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros [v_ins v_outs].
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros [v'_ins v'_outs].
  change (?f <$> Some ?x) with (Some (f x)).
  f_equal.
  set (v_ins' := filter _ v_ins).
  set (v'_ins' := filter _ v'_ins).
  set (v_outs' := filter _ v_outs).
  set (v'_outs' := filter _ v'_outs).
  cbv zeta.
  set (edge_pairings := map (uncurry _) _).
  case_decide; [done|].
  rewrite list_bind_fmap.
  apply list_bind_ext, reflexivity.
  intros e_s.
  change ([(Piso_to_weak mhe, Piso_to_weak mv')])
    with (prod_map Piso_to_weak Piso_to_weak <$> [(mhe, mv')]).
  generalize [(mhe, mv')] as mhe_mvs.
  induction e_s as [|(e, e') e_s IHe_s]; [done|].
  intros mhe_mvs.
  cbn.
  rewrite list_bind_fmap.
  rewrite IHe_s.
  clear IHe_s.
  rewrite list_fmap_bind.
  apply list_bind_ext, reflexivity.
  intros [mhe_ mv_].
  cbn.
  rewrite (dist_default (fmap _)).
  f_equal.
  rewrite wpupdate'_correct.
  rewrite option_bind_fmap, option_fmap_bind.
  apply option_bind_ext, reflexivity.
  intros [mhe_' unchanged].
  destruct unchanged; [done|].
  cbn.
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros [[t ins] outs].
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros [[t' ins'] outs'].
  case_decide; [|done].
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros ins_ins'.
  rewrite option_bind_fmap.
  apply option_bind_ext, reflexivity.
  intros outs_outs'.
  cbn.
  f_equal.
  change ([(Piso_to_weak mhe_', Piso_to_weak mv_)])
    with (prod_map Piso_to_weak Piso_to_weak <$> [(mhe_', mv_)]).
  clear - IHfuel.
  generalize [(mhe_', mv_)] as mhe_mvs.
  clear - IHfuel.
  generalize (ins_ins' ++ outs_outs') as vs.
  clear ins_ins' outs_outs'.
  intros vs.
  induction vs as [|(v, v') vs IHvs]; [done|]; intros mhe_mvs.
  cbn.
  rewrite IHvs.
  rewrite list_fmap_bind, list_bind_fmap.
  apply list_bind_ext, reflexivity.
  intros (mhe, mv).
  apply IHfuel.
Qed.

Lemma weak_graph_isos_by_vertex_map'_correct `{Equiv T, !RelDecision (≡@{T})}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  weak_graph_isos_by_vertex_map' cohg cohg' =
  prod_map Piso_to_weak Piso_to_weak <$> graph_isos_by_vertex_map' cohg cohg'.
Proof.
  unfold weak_graph_isos_by_vertex_map'.
  unfold graph_isos_by_vertex_map'.
  remember (zip _ _) as vs eqn:Hvs.
  clear Hvs.
  induction vs as [|(v, v') vs IHvs]; [done|].
  cbn.
  rewrite IHvs.
  rewrite list_fmap_bind, list_bind_fmap.
  apply list_bind_ext, reflexivity.
  intros mhe_mv.
  cbn.
  apply weak_vertex_map_based_iso_extend_by_vert_pair'_correct.
Qed.

(*
Definition weak_test_graph_isos_by_vertex_map' `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match weak_graph_isos_by_vertex_map' cohg cohg' with
  | [] => false
  | (mhe, mv) :: _ =>
  (* default false (
    isol_pairs ← mayzip
      (filter (λ v, mv.(WPiso_map) !! v = None) (elements (vertices cohg)))
      (filter (λ v, mv.(WPiso_invmap) !! v = None) (elements (vertices cohg')));
    mv' ← wpupdates isol_pairs mv;
    Some $ *)
    bool_decide (relabel_graph (Pmap_injmap mv.(WPiso_map))
      (reindex_graph (Pmap_injmap mhe.(WPiso_map)) cohg) ≡ cohg')
  (* ) *)
  end. *)


Definition weak_test_graph_isos_by_vertex_map'' `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  match weak_graph_isos_by_vertex_map' cohg cohg' with
  | [] => false
  | (mhe, mv) :: _ =>
  default false (
    isol_pairs ← mayzip
      (filter (λ v, mv.(WPiso_map) !! v = None) (elements (vertices cohg)))
      (filter (λ v, mv.(WPiso_invmap) !! v = None) (elements (vertices cohg')));
    mv' ← wpupdates isol_pairs mv;
    Some $
    bool_decide (
      map_Forall (λ k _, is_Some (mhe.(WPiso_map) !! k)) (hyperedges cohg) /\
      relabel_graph (mv'.(WPiso_map)!!!.)
      (reindex_graph (mhe.(WPiso_map)!!!.) cohg) ≡ cohg')
  )
  end.

Lemma weak_test_graph_isos_by_vertex_map''_correct_aux
  `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  weak_test_graph_isos_by_vertex_map'' cohg cohg' = test_graph_isos_by_vertex_map'' cohg cohg'.
Proof.
  unfold weak_test_graph_isos_by_vertex_map'', test_graph_isos_by_vertex_map''.
  rewrite weak_graph_isos_by_vertex_map'_correct.
  destruct (graph_isos_by_vertex_map' cohg cohg') as [|[mhe mv] ?]; [done|].
  cbn.
  f_equal.
  apply option_bind_ext, reflexivity.
  intros vs.
  rewrite wpupdates_correct.
  rewrite option_fmap_bind.
  done.
Qed.

Lemma weak_test_graph_isos_by_vertex_map''_correct
  `{Equiv T, !RelDecision (≡@{T}), Equivalence T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) :
  weak_test_graph_isos_by_vertex_map'' cohg cohg' = true ->
  cohg ≡ₛ cohg'.
Proof.
  rewrite weak_test_graph_isos_by_vertex_map''_correct_aux.
  apply test_graph_isos_by_vertex_map''_correct.
Qed.







(* 

#[local] Instance pos_equiv : Equiv positive := eq.
#[local] Instance nat_equiv : Equiv nat := eq.


Definition PathGraph {T} {n : nat}
  (v : vec T n) : CospanHyperGraph T 1 1 :=
  mk_cohg (mk_hg (list_to_map
    (imap (λ i t, (Pos.of_succ_nat i,
      (t, [Pos.of_succ_nat i], [Pos.of_succ_nat (S i)]))) v)) ∅)
    [# xH] [# Pos.of_succ_nat n ].

Definition BinTreeGraphLayer {T} (n : nat) (t : T) :
  CospanHyperGraph T (2 * n) n :=
  mk_cohg (mk_hg
    (list_to_map
      ((λ i, (Pos.of_succ_nat i, (t,
        xO ∘ Pos.of_succ_nat <$> [2 * i; S (2*i)],
          [xI (Pos.of_succ_nat i)]))) <$> seq 0 n)
    )
    ∅)
    (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (2 * n)))
    (vmap (xI ∘ Pos.of_succ_nat) (vseq 0 n)).

Fixpoint BinTreeGraph {T} {n : nat} (v : vec T n) :
  CospanHyperGraph T (2 ^ n) 1 :=
  match v with
  | [#] => id_graph 1
  | t ::: v => compose_graphs (BinTreeGraphLayer _ t) (BinTreeGraph v)
  end.


From TensorRocq Require Import GraphTermAux Isomorphism.Testing.


(* Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 150) in
  weak_test_graph_isos_by_vertex_map' (PathGraph v) (PathGraph v). *)


Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 9) in
  weak_test_graph_isos_by_vertex_map'' (BinTreeGraph v) (BinTreeGraph v).


Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 3000) in
  (* map_fold (fun k a m => (k +
    Pos.of_succ_nat (sum_list_with Pos.to_nat (elements a.1 ++ elements a.2)) + m)%positive) xH  *)
    size (graph_vertex_map (PathGraph v)).
  (* test_graph_isos_by_vertex_map (PathGraph v) (PathGraph v). *)
Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 30) in
  test_graph_isos_by_vertex_map (PathGraph v) (PathGraph v).

Time
Eval vm_compute in
  let v := (vseq 0 30) in
  graph_iso_partial_test (PathGraph v) (PathGraph v).

Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 150) in
  test_graph_isos_by_vertex_map (PathGraph v) (PathGraph v).

Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 150) in
  test_graph_isos_by_vertex_map' (PathGraph v) (PathGraph v).

Time
Eval vm_compute in
  let v := vmap (λ _, xH) (vseq 0 150) in
  weak_test_graph_isos_by_vertex_map' (PathGraph v) (PathGraph v).

Local Notation "'mk_Piso''' m mi" := (mk_Piso' m mi _) (at level 10).

Goal
  let v := vmap (Pos.of_succ_nat ) $ vseq 0 2 in
  graph_isos_by_vertex_map (PathGraph v) (PathGraph v) = [].

  vm_compute.


cbv zeta.
vm_eval (PathGraph _).

unfold graph_isos_by_vertex_map.
cbn [inputs outputs hedges hyperedges].
vm_eval (vertex_map _).
do 2 vm_eval (size _).
cbn [vec_to_list app zip].
cbn [foldr mbind list_bind].
rewrite app_nil_r.
cbn [Nat.add].
vm_compute.
etransitivity.
1:{
vm_compute.
apply list_bind_ext; [reflexivity|].

cbn [vertex_map_based_iso_extend_by_vert_pair].

vm_eval (pupdate' 3 3 _).


cbn [mbind option_bind].

(* remember  as x eqn:Hx. *)

vm_eval (PNodes _ !! 3%positive).
cbn [mbind option_bind].
cbn [from_option id].


vm_eval (map (uncurry app) _).

Optimize Heap.

vm_eval (decide (_ = nil)).



cbn [foldr mbind list_bind].
rewrite 2 app_nil_r.



cbn

vm_eval (vertex_map_based_iso_extend_by_vert_pair _ _ _ _ _ _ _ _).

cbv delta [vertex_map_based_iso_extend_by_vert_pair] fix.
fold @vertex_map_based_iso_extend_by_vert_pair.




Eval vm_compute in
  map_to_list (
    (PathGraph (vseq 0 2)) :> Pmap _).
Eval vm_compute in
  map_to_list (prod_map elements elements <$>
    vertex_map (PathGraph (vseq 0 2))).


Eval lazy in
  let v := vseq 0 0 in (PathGraph v).
  test_graph_isos_by_vertex_map (PathGraph v) (PathGraph v). *)



