From stdpp Require Export pmap gmap decidable.
Require Import TensorGraph.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.


(* An implementation of double pushout (DPO) rewriting *)

Lemma vsplitl_map {A B n m} (f : A -> B) (v : vec A (n + m)) :
  vsplitl (vmap f v) = vmap f (vsplitl v).
Proof.
  induction v using vec_add_inv.
  rewrite Vector.map_append.
  now rewrite 2 vsplitl_app.
Qed.
Lemma vsplitr_map {A B n m} (f : A -> B) (v : vec A (n + m)) :
  vsplitr (vmap f v) = vmap f (vsplitr v).
Proof.
  induction v using vec_add_inv.
  rewrite Vector.map_append.
  now rewrite 2 vsplitr_app.
Qed.

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

Local Open Scope nat_scope.

Section DPO.

  Context {T : Type}.

  Fixpoint propogate_subst {n} (ps : vec (positive * positive) n) : vec (positive * positive) n :=
  match n, ps with
  | 0, _ => [#]
  | (S k), _ =>
    let (p, p') := Vector.hd ps in
    let ps' := Vector.tl ps in
      (p, p') ::: propogate_subst (vmap (prod_map {[p := p']} {[p := p']}) ps')
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
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) -> 
      hg_add_vertices (tgl.(hedges) ⊎ tgr.(hedges)) (list_to_set (vmap (bcons true) tgr.(inputs))) <- (vmap (bcons true) tgr.(outputs))).

  Definition compose {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs)
      (tgl.(inputs) -> 
        hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set tgr.(inputs)) 
          <- tgr.(outputs)).

  Definition compose_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    tgl.(inputs) ->  hg_add_vertices (tgl.(hedges) ∪ tgr.(hedges)) (list_to_set (tgr.(inputs))) <- tgr.(outputs).

Lemma compose_safe_to_compose {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  compose_safe tgl tgr = compose
    (reindex_graph (bcons false) (relabel_graph (bcons false) tgl))
    (reindex_graph (bcons true) (relabel_graph (bcons true) tgr)).
Proof.
  reflexivity.
Qed.

Lemma subst_by_vec_id {n} : forall v : vec positive n, forall p : positive,
  subst_by_vec (propogate_subst (vzip_with pair v v)) p = p.
Proof.
  induction v.
  - easy.
  - intros.
    simpl.
    rewrite Vector.map_ext with (g:=(λ x : _, x)).
    + rewrite Vector.map_id.
      rewrite fn_lookup_singleton_case.
      case_decide; subst; auto.
    + intros.
      destruct a.
      simpl.
      rewrite 2 fn_lookup_singleton_case.
      case_decide; case_decide; subst; reflexivity.
Qed.

Lemma compose_to_compose_unsafe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : 
  tgl.(outputs) = tgr.(inputs) -> 
  compose tgl tgr = compose_unsafe tgl tgr.
Proof.
  intros.
  unfold compose.
  rewrite H.
  unfold relabel_graph.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite Vector.map_ext with (g:=(λ x : _, x)).
  rewrite Vector.map_id.
  simpl.
  rewrite relabel_hg_id'.
  reflexivity.
  all: apply subst_by_vec_id.
Qed.


Lemma relabel_hg_union f (hg hg' : HyperGraph T) :
  relabel_hg f (hg ∪ hg') =
  relabel_hg f hg ∪ relabel_hg f hg'.
Proof.
  apply hg_ext; cbn.
  - now rewrite map_fmap_union.
  - now rewrite set_map_union_L.
Qed.



Lemma apply_fn_lookup_singleton `{EqDecision A, EqDecision B}
  (f : A -> B) `{Hf : !Inj eq eq f} (a b c : A) :
  f ({[a := b]} c) = {[f a := f b]} (f c).
Proof.
  rewrite fn_lookup_singleton_case.
  case_decide as Hac.
  - subst.
    now rewrite fn_lookup_singleton.
  - now rewrite fn_lookup_singleton_ne by now intros ?%(inj f).
Qed.

Lemma propogate_subst_vmap {n} (fl : positive -> positive)
  `{Hfl : !Inj eq eq fl} (v : vec _ n) :
  (* v.*1 ## v.*2 -> *)
  propogate_subst (vmap (prod_map fl fl) v) =
  vmap (prod_map fl fl) (propogate_subst v).
Proof.
  revert v; induction n as [|n IHn]; [refine (vec_0_inv _ _);done|
    refine (vec_S_inv _ _)].
  intros (p, q) v.
  cbn.
  (* intros Hdisj. *)
  f_equal.
  rewrite <- IHn.
  f_equal.
  apply vec_eq; intros i.
  rewrite 2 Vector.map_map, 2 vlookup_map.
  destruct (v !!! i) as (pi, qi).
  cbn.
  now rewrite 2 (apply_fn_lookup_singleton fl).
Qed.

Lemma susbt_by_vec_propogate_helper n i o
  (insl outsl : vec positive n) (p' : positive) :
  subst_by_vec (propogate_subst
       (vzip_with pair (vmap {[o := i]} outsl) (vmap {[o := i]} insl))) p' =
  subst_by_vec (propogate_subst
      (vmap (prod_map {[o := i]} {[o := i]}) (vzip_with pair outsl insl))) p'.
Proof.
  revert i o insl outsl p'.
  induction n; intros i o;
  [do 2 refine (vec_0_inv _ _); done|].
  refine (vec_S_inv _ _).
  intros i' insl.
  refine (vec_S_inv _ _).
  intros o' outsl p.
  cbn.
  rewrite <- vzip_map.
  rewrite IHn.
  f_equal.
  f_equal.
  rewrite vzip_map.
  done.
Qed.

Lemma inputs_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(inputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (vsplitr tg.(inputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append].
  rewrite 2 vsplitl_app, vsplitr_app.
  cbn.
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite vsplitr_map, vsplitr_app.
  rewrite Vector.map_map.
  apply Vector.map_ext.
  intros p.
  apply susbt_by_vec_propogate_helper.
Qed.


Lemma outputs_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(outputs) =
  vmap (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (vsplitr tg.(outputs)).
Proof.
  induction n; [cbn; now rewrite Vector.map_id|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append].
  rewrite 2 vsplitl_app, vsplitr_app.
  cbn.
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite vsplitr_map, vsplitr_app.
  rewrite Vector.map_map.
  apply Vector.map_ext.
  intros p.
  apply susbt_by_vec_propogate_helper.
Qed.

Lemma hg_add_vertices_empty (hg : HyperGraph T) :
  hg_add_vertices hg ∅ = hg.
Proof.
  apply hg_ext; [done|].
  cbn -[union].
  apply union_empty_l_L.
Qed.

Lemma hg_add_vertices_union (hg : HyperGraph T) vs vs' :
  hg_add_vertices (hg_add_vertices hg vs) vs' =
  hg_add_vertices hg (vs ∪ vs').
Proof.
  apply hg_ext; [done|].
  cbn -[union].
  rewrite (union_assoc_L _).
  f_equal.
  apply union_comm_L.
Qed.

Lemma relabel_hg_add_vertices f (hg : HyperGraph T) vs :
  relabel_hg f (hg_add_vertices hg vs) =
  hg_add_vertices (relabel_hg f hg) (set_map f vs).
Proof.
  apply hg_ext; [done|].
  cbn.
  now rewrite set_map_union_L.
Qed.


Lemma hedges_add_top_loops {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  (add_top_loops tg).(hedges) =
  relabel_hg (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
      (hg_add_vertices tg.(hedges)
      (list_to_set (vsplitl tg.(inputs)))).
Proof.
  induction n; [cbn; now rewrite relabel_hg_id, hg_add_vertices_empty|].
  cbn [add_top_loops].
  rewrite IHn.
  destruct tg as [hg ins outs].
  (* cbn in ins, outs. *)
  induction ins as [insl insr] using vec_add_inv.
  induction outs as [outsl outsr] using vec_add_inv.
  induction insl as [i insl] using vec_S_inv.
  induction outsl as [o outsl] using vec_S_inv.
  cbn -[Vector.append union].
  rewrite 2 vsplitl_app.
  cbn -[union].
  rewrite 2 vsplitl_map, 2 vsplitl_app.
  rewrite 4 relabel_hg_add_vertices, hg_add_vertices_union.
  f_equal.
  - rewrite relabel_hg_compose.
    apply relabel_hg_ext.
    intros p; cbn.
    now rewrite susbt_by_vec_propogate_helper.
  - rewrite <- set_map_union_L.
    rewrite vec_to_list_map, <- (set_map_list_to_set_L (SA:=Pset)).
    rewrite <- set_map_union_L.
    rewrite set_map_compose_L.
    apply set_map_ext_L.
    intros ? _.
    cbn.
    apply susbt_by_vec_propogate_helper.
Qed.

Lemma add_top_loops_alt {n m m'}
  (tg : CospanHyperGraph T (n + m) (n + m')) :
  add_top_loops tg = 
  relabel_graph (subst_by_vec (propogate_subst
    (vzip (vsplitl tg.(outputs))
      (vsplitl tg.(inputs)))))
    (vsplitr tg.(inputs) -> 
      hg_add_vertices tg.(hedges) (list_to_set (vsplitl tg.(inputs))) 
      <- vsplitr tg.(outputs)).
Proof.
  apply cohg_ext.
  - apply hedges_add_top_loops.
  - apply inputs_add_top_loops.
  - apply outputs_add_top_loops.
Qed.



Lemma compose_graphs_alt_aux_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs_aux tgl tgr) =
    compose tgl tgr.
Proof.
  rewrite add_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  reflexivity.
Qed.

Lemma compose_graphs_alt_correct {n m o}
  (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) :
  add_top_loops (swapped_stack_graphs tgl tgr) =
    compose_safe tgl tgr.
Proof.
  rewrite add_top_loops_alt.
  cbn.
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  rewrite <- 2 reindex_relabel_hg.
  done.
Qed.

Section Paths.

  Context (H : HyperGraph T).

  Definition successor (h h' : HyperEdge T) :=
    exists p, In p (h.1.2) /\ In p (h'.2).

  Definition predecessor (h h' : HyperEdge T) :=
    exists p, In p (h'.1.2) /\ In p (h.2).

  Lemma succ_pred_symm (h h' : HyperEdge T) :
    successor h h' <-> predecessor h' h.
  Proof.
    split;
      intros [x []];
      exists x;
      auto.
  Qed.

  Definition path (h h' : HyperEdge T) : Prop :=
    (tc successor) h h'.

  Definition pred_path (h h' : HyperEdge T) :=
    (tc predecessor) h h'.

  (* Definition path_pred_path_symm (h h' : HyperEdge T) :
    path h h' <-> pred_path h' h.
  Proof.
    split.
    intros.
    - induction H0.
      + apply tc_once.
        now rewrite succ_pred_symm in H0.
      + 
        rewrite IHtc.
    - intros [x y | x y].
      +  *)


End Paths.

Definition decompose_left {n m} (G : CospanHyperGraph T n m) (L : HyperGraph T) : CospanHyperGraph T n m :=
  G.(inputs) -> {|
    hyperedges := ∅;
    hypervertices := ∅
  |} <- G.(outputs).


End DPO.

