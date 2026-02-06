Require Import TensorGraph.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.
From stdpp Require Export pmap gmap.


(* An implementation of double pushout (DPO) rewriting *)

Definition fun_to_map `{Insert A B M, Empty M, Elements A SA}
  (f : A -> B) (X : SA) : M :=
  set_to_map (fun a => (a, f a)) X.

Lemma lookup_fun_to_map `{FinMap K M, FinSet K SK, !RelDecision (∈@{SK})} {A}
  (f : K -> A) (X : SK) k :
  (fun_to_map f X :> M A) !! k = if decide (k ∈ X) then Some (f k) else None.
Proof.
  unfold fun_to_map.
  case_decide as Hk.
  - rewrite lookup_set_to_map by done.
    eauto.
  - apply eq_None_not_Some.
    intros (? & Heq).
    rewrite lookup_set_to_map in Heq by done.
    now destruct Heq as (_ & ? & [= -> <-]).
Qed.


Lemma lookup_fun_to_map_Some `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k a :
  (fun_to_map f X :> M A) !! k = Some a <->
  k ∈ X /\ f k = a.
Proof.
  unfold fun_to_map.
  rewrite lookup_set_to_map by done.
  naive_solver.
Qed.

Lemma lookup_fun_to_map_None `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  (fun_to_map f X :> M A) !! k = None <->
  k ∉ X.
Proof.
  unfold fun_to_map.
  rewrite eq_None_not_Some.
  unfold is_Some.
  setoid_rewrite lookup_set_to_map; [|done].
  naive_solver.
Qed.

Lemma lookup_fun_to_map_Some_1 `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  k ∈ X ->
  (fun_to_map f X :> M A) !! k = Some (f k).
Proof.
  now rewrite lookup_fun_to_map_Some.
Qed.

Lemma lookup_fun_to_map_None_1 `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  k ∉ X ->
  (fun_to_map f X :> M A) !! k = None.
Proof.
  now rewrite lookup_fun_to_map_None.
Qed.


Lemma lookup_fun_to_map_is_Some `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  is_Some ((fun_to_map f X :> M A) !! k) <-> k ∈ X.
Proof.
  unfold is_Some.
  setoid_rewrite lookup_fun_to_map_Some.
  naive_solver.
Qed.

Lemma dom_fun_to_map_gen `{FinMapDom K M SK, FinSet K SK'} {A}
  (f : K -> A) (X : SK') :
  dom (fun_to_map f X :> M A) ≡@{SK} set_map id X.
Proof.
  intros x.
  rewrite elem_of_dom.
  rewrite lookup_fun_to_map_is_Some.
  set_solver.
Qed.

Lemma dom_fun_to_map_gen_L `{FinMapDom K M SK, FinSet K SK', !LeibnizEquiv SK} {A}
  (f : K -> A) (X : SK') :
  dom (fun_to_map f X :> M A) =@{SK} set_map id X.
Proof.
  unfold_leibniz; apply dom_fun_to_map_gen.
Qed.

Lemma dom_fun_to_map `{FinMapDom K M SK, !Elements K SK, !FinSet K SK} {A}
  (f : K -> A) (X : SK) :
  dom (fun_to_map f X :> M A) ≡@{SK} X.
Proof.
  now rewrite dom_fun_to_map_gen, set_map_id.
Qed.

Lemma dom_fun_to_map_L `{FinMapDom K M SK, !Elements K SK,
  !FinSet K SK, !LeibnizEquiv SK} {A}
  (f : K -> A) (X : SK) :
  dom (fun_to_map f X :> M A) =@{SK} X.
Proof.
  unfold_leibniz; apply dom_fun_to_map.
Qed.

Lemma fun_to_map_union `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) :
  fun_to_map f (X ∪ Y) =@{M A} fun_to_map f X ∪ fun_to_map f Y.
Proof.
  apply map_eq.
  intros k.
  apply option_eq; intros fk.
  rewrite lookup_union, union_Some.
  rewrite 3 lookup_fun_to_map_Some.
  rewrite elem_of_union.
  rewrite lookup_fun_to_map_None.
  pose proof @elem_of_dec_slow.
  destruct_decide (decide (k ∈ X)); tauto.
Qed.

Lemma fmap_fun_to_map `{FinMap K M, FinSet K SK} {A B} (f : K -> A) (g : A -> B)
  (X : SK) :
  g <$> fun_to_map f X =@{M B} fun_to_map (g ∘ f) X.
Proof.
  apply map_eq; intros k.
  apply option_eq; intros fk.
  rewrite lookup_fmap, fmap_Some.
  setoid_rewrite lookup_fun_to_map_Some.
  naive_solver.
Qed.

(* Lemma kmap_fun_to_map `{FinMap K1 M1, FinSet K1 SK1, FinMap K2 M2, FinSet K2 SK2}
  {A} (f : K1 -> A) (g : K1 -> K2) (X : SK1) :
  kmap g (fun_to_map f X :> M1 A) =@{M2 A}
    set_to_map (fun a => (g a, f a)) X. *)
Lemma fun_to_map_singleton
  `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (k : K) :
  fun_to_map f ({[k]}:>SK) =@{M A} {[k := f k]}.
Proof.
  unfold fun_to_map, set_to_map.
  rewrite elements_singleton.
  done.
Qed.

Lemma fun_to_map_difference `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) :
  fun_to_map f (X ∖ Y) =@{M A} fun_to_map f X ∖ fun_to_map f Y.
Proof.
  apply map_eq.
  intros k.
  apply option_eq; intros fk.
  rewrite lookup_difference_Some.
  rewrite 2 lookup_fun_to_map_Some, lookup_fun_to_map_None.
  rewrite elem_of_difference.
  tauto.
Qed.

Lemma fun_to_map_disjoint `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) : X ## Y -> fun_to_map f X ##ₘ (fun_to_map f Y :> M A).
Proof.
  intros HXY.
  rewrite map_disjoint_alt.
  intros k.
  pose proof @elem_of_dec_slow.
  rewrite 2 lookup_fun_to_map_None.
  destruct_decide (decide (k ∈ X)).
  - right.
    now intros ?; apply (HXY k).
  - left.
    now intros ?; apply (HXY k).
Qed.

Section DPO.


  Context {T : Type}.


  (* Definition new_vertex_between {n m} (l r : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T n m. *)

  (* Definition disjoint_union (hg : Pmap (T * list positive * list positive))

  Definition add_vertex (tg : CospanHyperGraph T) (e : positive * positive) : CospanHyperGraph T.
  apply mk_cohg.
  - destruct e.

    admit.
  - exact tg.2.1.
  - exact tg.2.2. *)



  Fixpoint propogate_subst {n} (ps : vec (positive * positive) n) : vec (positive * positive) n :=
  match n, ps with
  | 0, _ => [#]
  | (S k), _ =>
    let (p, p') := Vector.hd ps in
    let ps' := Vector.tl ps in
      (p, p') ::: propogate_subst (vmap (relabel_delt ({[p := p']})) ps')
  end.


  Fixpoint subst_by_vec {n} (ps : vec (positive * positive) n) (p : positive) : positive :=
    match ps with
    | [#] => p
    | (a, b) ::: ps' => subst_by_vec ps' ({[a := b]} p)
    end.

  (* Reserved Notation "tgl ; tgr" (at level 50). *)
  Definition compose_safe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs :=
        propogate_subst (vzip (vmap (bcons false) tgl.(outputs)) (vmap (bcons true) tgr.(inputs))) in
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) -> tgl.(hedges) ⊎ tgr.(hedges) <- (vmap (bcons true) tgr.(outputs))).

  Definition compose {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs)
      (tgl.(inputs) -> tgl.(hedges) ∪ tgr.(hedges) <- tgr.(outputs)).

Lemma compose_safe_to_compose {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  compose_safe tgl tgr = compose
    (reindex_graph (bcons false) (relabel_graph (bcons false) tgl))
    (reindex_graph (bcons true) (relabel_graph (bcons true) tgr)).
Proof.
  reflexivity.
Qed.

(* Definition graph_disj {n m n' m'} (tg : CospanHyperGraph T n m)
  (tg' : CospanHyperGraph T n' m') : Prop :=
   *)

Lemma relabel_hg_union f (hg hg' : HyperGraph T) :
  relabel_hg f (hg ∪ hg') =
  relabel_hg f hg ∪ relabel_hg f hg'.
Proof.
  apply hg_ext; cbn.
  - now rewrite map_fmap_union.
  - now rewrite set_map_union_L.
Qed.

(* Lemma propogate_subst_vmap {n} (fl fr : positive -> positive)
  `{Hfl : !Inj eq eq fl, Hfr : !Inj eq eq fr} 
  (Hf : forall i j, fl i <> fr j) (v : vec _ n) :
  v.*1 ## v.*2 ->
  propogate_subst (vmap (prod_map fl fr) v) =
  vmap (prod_map fl fr) (propogate_subst v).
Proof.
  revert v; induction n as [|n IHn]; [refine (vec_0_inv _ _);done|
    refine (vec_S_inv _ _)].
  intros (p, q) v.
  cbn.
  intros Hdisj.
  f_equal.
  rewrite <- IHn.
  f_equal.
  apply vec_eq; intros i.
  rewrite 2 Vector.map_map, 2 vlookup_map.
  destruct (v !!! i) as (pi, qi).
  cbn.
  rewrite fn_lookup_singleton_case.
  rewrite fn_lookup_singleton_ne by eauto.

  rewrite fnlookup
  f_equiv.


Lemma compose_relabel_graph {n m o} fl fr
  `{Hfl : !Inj eq eq fl, Hfr : !Inj eq eq fr}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  vertices tgl ## vertices tgr ->
  compose (relabel_graph fl tgl) (relabel_graph fr tgr) =
  relabel_graph (
    Pmap_map (fun_to_map fl (vertices tgl) ∪
      fun_to_map fr (vertices tgr))) (compose tgl tgr).
Proof.
  intros Hdisj.
  apply cohg_ext.
  - cbn.
    rewrite relabel_hg_compose.
    rewrite 2 relabel_hg_union, 2 relabel_hg_compose.
    f_equal.
    + apply relabel_hg_ext_strong.
      intros i Hi.
      rewrite vzip_map.




Lemma compose_isomorphic {n m o}
  (tgl tgl' : CospanHyperGraph T n m) (tgr tgr' : CospanHyperGraph T m o) :
  isomorphic tgl tgl' -> isomorphic tgr tgr' ->
  isomorphic (compose tgl tgr) (compose tgl' tgr').
Proof.
  intros (fle & flv & Hfle & Hflv & ->)%isomorphic_exists
    (fre & frv & Hfre & Hfrv & ->)%isomorphic_exists.
  apply isomorphic_exists.
  exists (pos_map fle fre), (pos_map flv frv).
  split; [apply _|].
  split; [apply _|].


Lemma compose_graphs_alt_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  isomorphic (compose_graphs_alt tgl tgr)
    (compose_safe tgl tgr).
Proof. *)



End DPO.

