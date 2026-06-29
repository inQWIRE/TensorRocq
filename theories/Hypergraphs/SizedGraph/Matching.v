From TensorRocq Require Import tc BW.
From TensorRocq Require Import Isomorphism.IsoAux Isomorphism.Testing CospanHyperGraph.Definitions
  CospanHyperGraph.Ops SizedGraph.Definitions 
  SizedGraph.Testing SizedGraph.ToUnsized SizedPropsGraphs SizedProps.
Require Ltac2.Ltac2.

From TensorRocq Require Import CospanHyperGraph.Matching.

Local Existing Instance Countable_Equiv.




Definition make_size_label_indexed_edge_map {N T} `{Countable N, Countable T}
  (sizemap : Pmap N)
  (es : Pmap (T * list positive * list positive)) :
  gPmap (T * list N * list N) (list (positive * list positive * list positive)) :=
  kimerge (M2:=gPmap _) (fun idx '(t, ins, outs) =>
    ((t, omap (sizemap !!.) ins, omap (sizemap !!.) outs), (idx, ins, outs))) es.

Definition make_size_aligned_edge_list {N T}
  (es es' : gPmap (T * list N * list N) (list (positive * list positive * list positive))) :
  list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)) :=
  let m' := merge (M:=Pmap) (fun me me' =>
    (λ e, from_option (e,.) (e, []) me') <$> me) es es' in
  (map_to_list m').*2.

Definition make_size_indexed_vertex_map {N} `{Countable N}
  (sizemap : Pmap N)
  (vs : list positive) :
  gPmap (N) (list positive) :=
  kimerge_aux (M2:=gPmap _) (fun v n =>
    (n, v)) (omap (λ v, (v,.) <$> sizemap !! v) vs).



(* Definition update_frobenius_edge_match
  (boundary : Pset) (e e' : positive * list positive * list positive)
  (me_mv : Piso * Psurj) : option (Piso * Psurj) :=
  let '(me, mv) := me_mv in
  let '(idx, ins, outs) := e in
  let '(idx', ins', outs') := e' in
  me' ← pupdate idx idx' me;
  mv' ← spupdates boundary (zip (ins ++ outs) (ins' ++ outs')) mv;
  Some (me', mv'). *)

(* Fixpoint frobenius_edge_matchings_extending_aux_aligned
  (boundary : Pset)
  (es_es' : list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)))
    (* The edges of subcohg and cohg, aligned by label and in/outdegrees *)
  (me_mv : Piso * Psurj) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Psurj) :=
  match es_es' with
  | [] => [me_mv]
  | (es, es') :: es_es' =>
    ofold_sublistings (update_frobenius_edge_match boundary) es es' me_mv ≫=
    frobenius_edge_matchings_extending_aux_aligned boundary es_es'
  end. *)


Definition sized_frobenius_edge_matchings_extending {N T} `{Countable N, Countable T}
  (sizemap sizemap' : Pmap N)
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *)
  (me_mv : Piso * Psurj) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Psurj) :=
  frobenius_edge_matchings_extending_aux_aligned boundary
    (make_size_aligned_edge_list (make_size_label_indexed_edge_map sizemap es)
      (make_size_label_indexed_edge_map sizemap' es')) me_mv.

Definition sized_frobenius_edge_matchings {N T} `{Countable N, Countable T}
  (sizemap sizemap' : Pmap N)
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Psurj) :=
  let vmap := vertex_map es' in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Psurj_map) !!.) boundary in

    map_Forall
      (fun v' _ =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Psurj_invmap)
  ) $
    sized_frobenius_edge_matchings_extending sizemap sizemap' boundary es es' (∅, ∅).


(* Definition graph_boundary {T n m} (cohg : CospanHyperGraph T n m) : Pset :=
  list_to_set (cohg.(inputs) ++ cohg.(outputs)). *)


Fixpoint sized_frobenius_vertex_matchings_extending {N} `{Countable N}
  (vs : list (positive * N))
  (codom_verts : gPmap N (list positive))
  (mv : Pmap positive) : list (Pmap positive) :=
  match vs with
  | [] => [mv]
  | (v, n) :: vs =>
    if decide (is_Some (mv !! v)) then
      (* v is already assigned! Nothing to do *)
      sized_frobenius_vertex_matchings_extending vs codom_verts mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      v' ← codom_verts !!! n;
      sized_frobenius_vertex_matchings_extending vs codom_verts (<[v := v']> mv)
  end.



Definition sized_frobenius_graph_matchings {N T} `{Countable N, Countable T}
  {i j} (subcohg : SizedCospanHyperGraph N T i j)
  {n m} (cohg : SizedCospanHyperGraph N T n m) : list (Piso * Pmap positive * Pset) :=
  let boundary := graph_boundary subcohg in
  let sizemap := subcohg.(sized_map) in
  let sizemap' := cohg.(sized_map) in
  '(me, mv) ← sized_frobenius_edge_matchings sizemap sizemap' boundary subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Psurj_invmap) !! v = None) (vertices cohg) in
  let sized_codom_verts := make_size_indexed_vertex_map sizemap' codom_verts in
  (λ mv', (me, mv', (set_map (mv'!!!.) (graph_boundary subcohg))))
    <$> sized_frobenius_vertex_matchings_extending
    (omap (λ v, (v,.) <$> sizemap !! v) (inputs subcohg ++ outputs subcohg))
    sized_codom_verts mv.



(*
Definition update_bimonog_edge_match (e e' : positive * list positive * list positive)
  (me_mv : Piso * Piso) : option (Piso * Piso) :=
  let '(me, mv) := me_mv in
  let '(idx, ins, outs) := e in
  let '(idx', ins', outs') := e' in
  me' ← pupdate idx idx' me;
  mv' ← pupdates (zip (ins ++ outs) (ins' ++ outs')) mv;
  Some (me', mv'). *)

(* Fixpoint bimonog_edge_matchings_extending_aux_aligned
  (es_es' : list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)))
    (* The edges of subcohg and cohg, aligned by label and in/outdegrees *)
  (me_mv : Piso * Piso) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Piso) :=
  match es_es' with
  | [] => [me_mv]
  | (es, es') :: es_es' =>
    ofold_sublistings update_bimonog_edge_match es es' me_mv ≫=
    bimonog_edge_matchings_extending_aux_aligned es_es'
  end. *)


Definition sized_bimonog_edge_matchings_extending {N T} `{Countable N, Countable T}
  (sizemap sizemap' : Pmap N)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *)
  (me_mv : Piso * Piso) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Piso) :=
  bimonog_edge_matchings_extending_aux_aligned
    (make_size_aligned_edge_list (make_size_label_indexed_edge_map sizemap es)
      (make_size_label_indexed_edge_map sizemap' es')) me_mv.

Definition sized_bimonog_edge_matchings {N T} `{Countable N, Countable T}
  (sizemap sizemap' : Pmap N)
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Piso) :=
  let vmap := vertex_map es' in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Piso_map) !!.) boundary in
    (* FIXME: Is there some test I can do here to help with bimonogamy? *)
    map_Forall
      (fun _ v' =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Piso_map)
  ) $
    sized_bimonog_edge_matchings_extending sizemap sizemap' es es' (∅, ∅).


(* NB: This is ONLY for boundary vertices of (bi)monogamous hypergraphs! *)
Fixpoint sized_bimonog_vertex_matchings_extending {N} `{Countable N}
  (vs : list (positive * N))
  (codom_verts : gPmap N (list positive))
  (mv : Pmap positive) : list (Pmap positive) :=
  match vs with
  | [] => [mv]
  | (v, n) :: vs =>
    if decide (is_Some (mv !! v)) then
      (* v is already assigned! Nothing to do *)
      sized_bimonog_vertex_matchings_extending vs codom_verts mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      '(v', n_verts') ← sublistings_aux [] (codom_verts !!! n);
      let codom_verts' := partial_alter (fmap (λ _, n_verts')) n codom_verts in
      sized_bimonog_vertex_matchings_extending vs codom_verts' (<[v := v']> mv)
  end.

Definition sized_bimonog_graph_matchings {N T} `{Countable N, Countable T}
  {i j} (subcohg : SizedCospanHyperGraph N T i j)
  {n m} (cohg : SizedCospanHyperGraph N T n m) : list (Piso * Pmap positive * Pset) :=
  let boundary := graph_boundary subcohg in
  let sizemap := subcohg.(sized_map) in
  let sizemap' := cohg.(sized_map) in
  '(me, mv) ← sized_bimonog_edge_matchings sizemap sizemap' boundary subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Piso_invmap) !! v = None) (vertices cohg) in
  let sized_codom_verts := make_size_indexed_vertex_map sizemap' codom_verts in
  (λ mv', (me, mv', (set_map (mv'!!!.) (graph_boundary subcohg))))
    <$> sized_bimonog_vertex_matchings_extending
    (omap (λ v, (v,.) <$> sizemap !! v) (inputs subcohg ++ outputs subcohg))
    sized_codom_verts mv.




Definition sized_monog_edge_matchings {N T} `{Countable N, Countable T}
  (sizemap sizemap' : Pmap N)
  (boundary : Pset) (cohg_succs : prel)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Piso) :=
  let vmap := vertex_map es' in
  let cohg_succ := hg_succ_aux vmap in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Piso_map) !!.) boundary in

    map_Forall
      (fun _ v' =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Piso_map) /\
      (* Convexity : *)
      let es' : Pset := dom me.(Piso_invmap) in
      es' ## prel_img cohg_succs (prel_img cohg_succ es' ∖ es')
  ) $
    sized_bimonog_edge_matchings_extending sizemap sizemap' es es' (∅, ∅).



(* NB: This is ONLY for boundary vertices of monogamous hypergraphs! *)
Fixpoint sized_monog_vertex_matchings_extending {N} `{Countable N}
  (vs : list (positive * N))
  (codom_verts : gPmap N (list positive))
  (mv : Piso) : list (Piso) :=
  match vs with
  | [] => [mv]
  | (v, n) :: vs =>
    if decide (is_Some (mv.(Piso_map) !! v)) then
      (* v is already assigned! Nothing to do *)
      sized_monog_vertex_matchings_extending vs codom_verts mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      '(v', n_verts') ← sublistings_aux [] (codom_verts !!! n);
      let codom_verts' := partial_alter (fmap (λ _, n_verts')) n codom_verts in
      from_option (sized_monog_vertex_matchings_extending vs codom_verts') [] (pupdate v v' mv)
  end.

Definition sized_monog_graph_matchings {N T} `{Countable N, Countable T}
  {i j} (subcohg : SizedCospanHyperGraph N T i j)
  {n m} (cohg : SizedCospanHyperGraph N T n m) (cohg_succs : prel) : list (Piso * Piso) :=
  let boundary := graph_boundary subcohg in
  let sizemap := subcohg.(sized_map) in
  let sizemap' := cohg.(sized_map) in
  '(me, mv) ← sized_monog_edge_matchings sizemap sizemap' boundary cohg_succs subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Piso_invmap) !! v = None) (vertices cohg) in
  let sized_codom_verts := make_size_indexed_vertex_map sizemap' codom_verts in
  (λ mv', (me, mv'))
    <$> sized_monog_vertex_matchings_extending
    (omap (λ v, (v,.) <$> sizemap !! v) (inputs subcohg ++ outputs subcohg))
    sized_codom_verts mv.




(*
Definition explode_step (arities : Pmap (list nat))
  (p : positive) : Pmap (list nat) * positive :=
  match arities !! p with
  | None => (arities, xO p)
  | Some l => (alter tl p arities, xI $ encode (p, hd 0 l))
  end.

Definition explode_list (arities : Pmap (list nat))
  (ps : list positive) : Pmap (list nat) * list positive :=
  foldr (λ p '(ar, ps), let '(ar', p') := explode_step ar p in
    (ar', p' :: ps)) (arities, []) ps.


Fixpoint explode_vec (arities : Pmap (list nat))
  {n} (ps : vec positive n) : Pmap (list nat) * vec positive n :=
  match ps with
  | [#] => (arities, [#])
  | p ::: ps =>
    let '(ar, ps) := explode_vec arities ps in
    let '(ar', p') := explode_step ar p in
    (ar', p' ::: ps)
  end.

Definition explode_hypergraph_aux {T} (arities : Pmap (list nat))
  (hg : Pmap (T * list positive * list positive)) :
  Pmap (list nat) * Pmap (T * list positive * list positive) :=
  map_fold (λ k '(t, ins, outs) '(ar, m),
    let '(ar, ins') := explode_list ar ins in
    let '(ar, outs') := explode_list ar outs in
    (ar, <[k := (t, ins', outs')]> m)) (arities, ∅) hg.

Definition explode_hypergraph {T} (arities : Pmap (list nat))
  (hg : HyperGraph T) : Pmap (list nat) * HyperGraph T :=
  let '(ar, hg') := explode_hypergraph_aux arities hg.(hyperedges) in
  (ar, mk_hg hg'
    (set_bind (λ p,
      match arities !! p with
      | None => {[xO p]}
      | Some l =>
        list_to_set ((λ k, xI $ encode (p, k)) <$> l)
      end) hg.(hypervertices))).

Definition explode_cohg {T n m} (arities : Pmap (list nat))
  (cohg : CospanHyperGraph T n m) : Pmap (list nat) * CospanHyperGraph T n m :=
  let '(ar, ins) := explode_vec arities cohg.(inputs) in
  let '(ar, outs) := explode_vec ar cohg.(outputs) in
  let '(ar, hg) := explode_hypergraph ar cohg.(hedges) in
  (ar, mk_cohg hg ins outs). *)

Definition explode_sized_map {N} (arities : Pmap (list nat))
  (sizemap : Pmap N) : Pmap N :=
  map_bind (λ v n, match arities !! v with
    | None => {[xO v := n]}
    | Some ks =>
      list_to_map ((λ k, (xI (encode (v, k)), n)) <$> ks)
    end) sizemap.

Definition explode_scohg {N T n m} (arities : Pmap (list nat))
  (scohg : SizedCospanHyperGraph N T n m) : Pmap (list nat) * SizedCospanHyperGraph N T n m :=
  let sizemap := explode_sized_map arities scohg.(sized_map) in
  let '(ar, cohg) := explode_cohg arities scohg in
  (ar, mk_scohg cohg sizemap).


(* FIXME: Move *)
Definition bw_sized_graph_of_sized_graph {N} `{EqDecision N} {T n m}
  (scohg : SizedCospanHyperGraph N T (bsize n) (bsize m)) : option (BWSizedCospanHyperGraph N T n m) :=
  match decide (sized_inputs scohg = Some <$> btree_elems n /\ sized_outputs scohg = Some <$> btree_elems m) with
  | left Heq => Some {|
      bw_scohg := scohg; bw_inputs := proj1 Heq; bw_outputs := proj2 Heq|}
  | right _ => None
  end.

Lemma sized_inputs_cast_sized_graph {N T} {n m n' m'}
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  sized_inputs (cast_sized_graph Hn Hm scohg) = sized_inputs scohg.
Proof.
  unfold sized_inputs.
  unfold cast_sized_graph.
  cbn.
  rewrite inputs_cast_graph.
  rewrite vec_to_list_cast.
  done.
Qed.

Lemma sized_outputs_cast_sized_graph {N T} {n m n' m'}
  (Hn : n = n') (Hm : m = m') (scohg : SizedCospanHyperGraph N T n m) :
  sized_outputs (cast_sized_graph Hn Hm scohg) = sized_outputs scohg.
Proof.
  unfold sized_outputs.
  unfold cast_sized_graph.
  cbn.
  rewrite outputs_cast_graph.
  rewrite vec_to_list_cast.
  done.
Qed.

Definition bw_sized_graph_of_cast_sized_graph {N} `{EqDecision N} {T} (n m : btree N)
  {n' m' : nat}
  (scohg : SizedCospanHyperGraph N T n' m') : option (BWSizedCospanHyperGraph N T n m).
  refine
  match decide (sized_inputs scohg = Some <$> btree_elems n /\ sized_outputs scohg = Some <$> btree_elems m) with
  | left Heq => Some {|
      bw_scohg := cast_sized_graph (_ Heq.1) (_ Heq.2) scohg; bw_inputs :=
      eq_trans (sized_inputs_cast_sized_graph _ _ _) (proj1 Heq); 
      bw_outputs := 
      eq_trans (sized_outputs_cast_sized_graph _ _ _) (proj2 Heq)|}
  | right _ => None
  end.
  - abstract (now intros Hins%(f_equal length);
    rewrite length_sized_inputs, length_fmap, length_btree_elems in Hins).
  - abstract (now intros Houts%(f_equal length);
    rewrite length_sized_outputs, length_fmap, length_btree_elems in Houts).
Defined.




(* #[program] Definition default_bw_sized_graph {N T} (n m : btree N) :  *)




Definition exploded_sized_context {N T}
  {i j} (subcohg : SizedCospanHyperGraph N T i j)
  {n m} (cohg : SizedCospanHyperGraph N T n m)
  (me : Piso) (mv : Pmap positive) (true_bnd : Pset) :
  Pmap (list positive) * SizedCospanHyperGraph N T n m :=

  (* let mv_bnd_map := restrict_map (graph_boundary subcohg) mv.(Piso_map) in
  let mv_boundary_img_cohg : Pset := map_img mv_bnd in *)
  let mv_boundary_img_cohg := true_bnd in

  let context : SizedCospanHyperGraph N T n m :=
    mk_scohg (mk_cohg (mk_hg
      (filter (λ k_tio, me.(Piso_invmap) !! k_tio.1 = None) (hyperedges cohg))
      (* TODO: Check that leaving these vertices in is OK *)
      (hypervertices cohg (* ∪ mv_boundary_img_cohg *)))
      cohg.(inputs)
      cohg.(outputs))
      (sized_map cohg) in

  let deg := cohg_degree_map context in
  let bnd_deg : Pmap nat := restrict_map mv_boundary_img_cohg deg in
  let bnd_deg_ars : Pmap (list nat) := seq O <$> bnd_deg in
  let '(_, exploded_context) := explode_scohg bnd_deg_ars context in
    (* ^ This is the exploded context; we just need to give a record of
      the g-equivalence classes. These are pretty trivial to generate, though *)

  let g_equiv_classes := map_imap
    (λ p (ar : list _), Some $ (((λ k, xI $ encode (p, k)) <$> ar))) bnd_deg_ars in
  (g_equiv_classes, exploded_context).

Definition exploded_interfaced_sized_context {N T}
  {i j} (subcohg : SizedCospanHyperGraph N T i j)
  {n m} (cohg : SizedCospanHyperGraph N T n m)
  (me : Piso) (mv : Pmap positive) (true_bnd : Pset) :
  (Pmap blocks * SizedCospanHyperGraph N T n ((i + j) + m))%type :=
  let '(g_equiv_classes, exploded_context) :=
  exploded_sized_context subcohg cohg me mv true_bnd in

  (* TODO: Fix this: Relabel to ensure disjointness with the added boundary *)
  let g_equiv_classes : Pmap (list positive) := fmap (M:=list) xI <$> g_equiv_classes in
  let exploded_context := relabel_sized_graph xI exploded_context in
  (* let mv := xI <$> mv in  *) (* NB: We don't relabel mv because
    it's used to say where in the _original_ graph each element of the
    boundary lands; we're just changing our names for the new context *)
  let subsizemap := subcohg.(sized_map) in
  let exploded_interfaced_context :=
    mk_scohg (mk_cohg exploded_context exploded_context.(inputs)
      (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j)) +++ exploded_context.(outputs)))
      (exploded_context.(sized_map) ∪
        list_to_map (omap (M:=list) (λ '(idx, p), (xO (Pos.of_succ_nat idx),.) <$> (subsizemap !! p))
          (vzip (vseq 0 (i + j)) (subcohg.(inputs) +++ subcohg.(outputs))))) in (* TODO: I'm not sure if adding this is necessary, but it seems probable *)

  let subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs) in

    (* Equivalence classes of interface vertices for _g_ *)
  let interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)) in

    (* Equivalence classes of interface vertices for _f_ *)
  let f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes in

  (* Now, I'm ASSUMING (TODO: triple-check this [AN: I have found direct evidence
     in the paper]) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

  let g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes in

  (merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks, exploded_interfaced_context).

Definition exploded_interfaced_bw_sized_context {N} `{EqDecision N} {T}
  {i j} (subcohg : BWSizedCospanHyperGraph N T i j)
  {n m} (cohg : BWSizedCospanHyperGraph N T n m)
  (me : Piso) (mv : Pmap positive) (true_bnd : Pset) :
  option (Pmap blocks * BWSizedCospanHyperGraph N T n ((i + j) + m)) :=
  let '(f_g_equiv_classes, ctx) := exploded_interfaced_sized_context subcohg cohg me mv true_bnd in
  (f_g_equiv_classes,.) <$> bw_sized_graph_of_sized_graph (m:=(i + j) + m) ctx.

Definition bw_sized_graph_runit_r {N T} {n m} (scohg : BWSizedCospanHyperGraph N T n (0 + m)) :
  BWSizedCospanHyperGraph N T n m := {|
    bw_scohg := scohg :> SizedCospanHyperGraph N T (bsize n) (bsize m);
    bw_inputs := scohg.(bw_inputs);
    bw_outputs := scohg.(bw_outputs);
  |}.

Definition make_bw_sized_pushout {N T} {i j} (subcohg : BWSizedCospanHyperGraph N T i j)
  {n m} (context : BWSizedCospanHyperGraph N T n ((i + j) + m)) : BWSizedCospanHyperGraph N T n m :=
  bw_sized_graph_runit_r (compose_bw_sized_graphs context (stack_bw_sized_graphs
    (* (wrapunder_l subcohg) *)
    (compose_bw_sized_graphs (stack_bw_sized_graphs subcohg (id_bw_sized_graph j)) (cap_bw_sized_graph j))
    (id_bw_sized_graph m))).


(* Fixpoint quotient_maps_aux (f_g_equiv_classes : Pmap blocks) : list (Pmap positive) := *)

(* Definition quotient_maps (f_g_equiv_classes : Pmap blocks) : list (Pmap positive) :=
  map_fold (λ _ (bl : blocks) (maps : list (Pmap positive)),
    bl' ← partitions_joining_mildly_inefficient bl;
    (partition_quotient bl' ∪.) <$> maps) [∅] f_g_equiv_classes. *)


Definition quotiented_sized_contexts {N T}
  (f_g_equiv_classes : Pmap blocks)
  {n ijm} (exploded_interfaced_context : SizedCospanHyperGraph N T n ijm) :
  list (SizedCospanHyperGraph N T n ijm) :=
  (λ m, relabel_sized_graph (Pmap_map m) exploded_interfaced_context) <$> quotient_maps f_g_equiv_classes.

Fixpoint remove_sized_vertex {N} `{EqDecision N}
  (n : N) (vs : list (positive * N)) : option (list (positive * N)) :=
  match vs with
  | [] => None
  | v :: vs => if decide (n = v.2) then Some vs else (v::.) <$> remove_sized_vertex n vs
  end.

Fixpoint subtracted_sized_vertices {N} `{EqDecision N}
  (us vs : list (positive * N)) : option (list (positive * N)) :=
  match us with
  | [] => Some vs
  | (u, n) :: us => remove_sized_vertex n vs ≫= subtracted_sized_vertices us
  end.

Definition all_sized_frobenius_precontexts {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m))) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  match subtracted_sized_vertices sub_isol cohg_isol with
  | None => []
  | Some new_cohg_isol =>

    let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in

  (* Next, we get a candidate matching *)

    '(me, mv, _) ← sized_frobenius_graph_matchings subscohg scohg;
    let '(f_g_equiv_classes, exploded_interfaced_context) :=
      exploded_interfaced_sized_context subscohg scohg me mv (map_img mv) in
    quotiented_sized_contexts f_g_equiv_classes exploded_interfaced_context
  end.

Definition all_sized_frobenius_contexts {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (BWSizedCospanHyperGraph N T n ((i + j) + m)) :=
  omap bw_sized_graph_of_sized_graph $ all_sized_frobenius_precontexts subscohg scohg.


Definition select_sized_frobenius_context
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m)
  (match_number quotient_number : nat) : option (BWSizedCospanHyperGraph N T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  new_cohg_isol ← subtracted_sized_vertices sub_isol cohg_isol;
  let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in
  (* Next, we get a candidate matching *)

  '(me, mv, _) ← sized_frobenius_graph_matchings subscohg scohg !! match_number;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_sized_context subscohg scohg me mv (map_img mv) in
  quot_ctx ← (quotiented_sized_contexts f_g_equiv_classes exploded_interfaced_context
      !! quotient_number) :> option (SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)));
  bw_sized_graph_of_sized_graph quot_ctx.

Definition sized_frobenius_graph_rewriting_correctness
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : nat * bool :=
  let ctxs := all_sized_frobenius_precontexts subscohg scohg in
  let len := length ctxs in
  (len, forallb (λ ctx : SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)),
    default false (
      bwctx ←@{option} bw_sized_graph_of_sized_graph ctx;
      Some $ default_sized_graph_iso_test scohg (make_bw_sized_pushout subscohg
        (bwctx :> BWSizedCospanHyperGraph N T n (i + j + m))))) ctxs).


Definition sized_frobenius_graph_rewriting_correctness'
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (option bool) :=
  let ctxs := all_sized_frobenius_precontexts subscohg scohg in
  (λ ctx : SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)),
      bwctx ←@{option} bw_sized_graph_of_sized_graph ctx;
      Some $ default_sized_graph_iso_test scohg (make_bw_sized_pushout subscohg
        (bwctx :> BWSizedCospanHyperGraph N T n (i + j + m)))) <$> ctxs.


(* Compute frobenius_graph_rewriting_correctness'
  (bw_sized_graph_of_tensor (N:=nat) true (bnode (!0) (!2)) 0)
  (stack_bw_sized_graphs (bw_sized_graph_of_tensor true (bnode (!0) (!2)) 0)
    (bw_sized_graph_of_tensor true (bnode (!0) (!2)) 0)). *)



(* FIXME: Ideally, I'd like to better understand the bimonogamous case
  so we can replace this filter hack with something much better. For now,
  there's a paper to write. *)


Definition all_sized_bimonog_precontexts {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m))) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  match subtracted_sized_vertices sub_isol cohg_isol with
  | None => []
  | Some new_cohg_isol =>

    let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in

  (* Next, we get a candidate matching *)

    '(me, mv, _) ← sized_bimonog_graph_matchings subscohg scohg;
    let '(f_g_equiv_classes, exploded_interfaced_context) :=
      exploded_interfaced_sized_context subscohg scohg me mv (map_img mv) in
    filter (λ scohg, is_bimonogamousb scohg.(sized_cospan)) $ quotiented_sized_contexts f_g_equiv_classes exploded_interfaced_context
  end.

Definition all_sized_bimonog_contexts {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (BWSizedCospanHyperGraph N T n ((i + j) + m)) :=
  omap bw_sized_graph_of_sized_graph $ all_sized_bimonog_precontexts subscohg scohg.


Definition select_sized_bimonog_context
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m)
  (match_number quotient_number : nat) : option (BWSizedCospanHyperGraph N T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  new_cohg_isol ← subtracted_sized_vertices sub_isol cohg_isol;
  let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in
  (* Next, we get a candidate matching *)

  '(me, mv, _) ← sized_bimonog_graph_matchings subscohg scohg !! match_number;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_sized_context subscohg scohg me mv (map_img mv) in
  quot_ctx ← (filter (λ scohg, is_bimonogamousb scohg.(sized_cospan))
    (quotiented_sized_contexts f_g_equiv_classes exploded_interfaced_context)
      !! quotient_number) :> option (SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)));
  bw_sized_graph_of_sized_graph quot_ctx.

Definition sized_bimonog_graph_rewriting_correctness
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : nat * bool :=
  let ctxs := all_sized_bimonog_precontexts subscohg scohg in
  let len := length ctxs in
  (len, forallb (λ ctx : SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)),
    default false (
      bwctx ←@{option} bw_sized_graph_of_sized_graph ctx;
      Some $ default_sized_graph_iso_test scohg (make_bw_sized_pushout subscohg
        (bwctx :> BWSizedCospanHyperGraph N T n (i + j + m))))) ctxs).


Definition sized_bimonog_graph_rewriting_correctness'
  {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (option bool) :=
  let ctxs := all_sized_bimonog_precontexts subscohg scohg in
  (λ ctx : SizedCospanHyperGraph N T (bsize n) (bsize ((i + j) + m)),
      bwctx ←@{option} bw_sized_graph_of_sized_graph ctx;
      Some $ default_sized_graph_iso_test scohg (make_bw_sized_pushout subscohg
        (bwctx :> BWSizedCospanHyperGraph N T n (i + j + m)))) <$> ctxs.



Definition sized_monog_graph_decomp {N T}
  {i j} (subscohg : SizedCospanHyperGraph N T i j)
  {n m} (scohg : SizedCospanHyperGraph N T n m)
  (cohg_succs : prel)
  (me mv : Piso) : {k : nat & SizedCospanHyperGraph N T n (k + i) * SizedCospanHyperGraph N T (k + j) m}%type :=
  let '(existT k (C1, C2)) := monog_graph_decomp subscohg scohg cohg_succs me mv in
  let SC1 := mk_scohg C1 scohg.(sized_map) in
  let SC2 := mk_scohg C2 scohg.(sized_map) in
  existT k (SC1, SC2).

Definition make_bw_sized_monog_pushout {N T i j}
  (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (context : {k & BWSizedCospanHyperGraph N T n (k + i) * BWSizedCospanHyperGraph N T (k + j) m}%type) :
    BWSizedCospanHyperGraph N T n m :=
  let '(existT k (C1, C2)) := context in
  compose_bw_sized_graphs (compose_bw_sized_graphs C1 (stack_bw_sized_graphs (id_bw_sized_graph k) subscohg)) C2.

Definition all_sized_monog_precontexts {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m)
  : list {k : nat & SizedCospanHyperGraph N T (bsize n) (k + bsize i)
    * SizedCospanHyperGraph N T (k + bsize j) (bsize m)}%type :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)


  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  match subtracted_sized_vertices sub_isol cohg_isol with
  | None => []
  | Some new_cohg_isol =>

    let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in
    let cohg_succs := hg_succs scohg in

    (* Next, we get a candidate matching *)
    (λ '(me, mv), sized_monog_graph_decomp subscohg scohg cohg_succs me mv)
      <$> sized_monog_graph_matchings subscohg scohg cohg_succs
  end.

Definition bw_sized_monog_context_of_sized_monog_context {N T}
  `{EqDecision N} {i j n m : btree N}
  (ctx : {k : nat & SizedCospanHyperGraph N T (bsize n) (k + bsize i)
    * SizedCospanHyperGraph N T (k + bsize j) (bsize m)}%type) :
  option {k : btree N & BWSizedCospanHyperGraph N T n (k + i)
    * BWSizedCospanHyperGraph N T (k + j) m}%type :=
  let '(existT k (SC1, SC2)) := ctx in
  bk ←@{option} btree_of_list <$>
    (join_list ((SC1.(sized_map)!!.) <$> (vec_to_list (vsplitl SC1.(outputs)))));
  BSC1 ← bw_sized_graph_of_cast_sized_graph (n) (bk + i) SC1;
  BSC2 ← bw_sized_graph_of_cast_sized_graph (bk + j) (m) SC2;
  Some $ existT bk (BSC1, BSC2).

Definition select_bw_sized_monog_context {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m)
  (match_number : nat)
  : option {k : btree N & BWSizedCospanHyperGraph N T n (k + i)
    * BWSizedCospanHyperGraph N T (k + j) m}%type :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)

  let sub_isol := omap (λ v, (v,.)<$> subscohg.(sized_map) !! v)
      $ elements (isolated_vertices subscohg) in
  let cohg_isol := omap (λ v, (v,.)<$> scohg.(sized_map) !! v)
      $ elements (isolated_vertices scohg) in
  new_cohg_isol ← subtracted_sized_vertices sub_isol cohg_isol;
  let scohg := (set_sized_verts scohg (list_to_set (new_cohg_isol.*1))) in
  let cohg_succs := hg_succs scohg in

  (* Next, we get a candidate matching *)
  '(me, mv) ← sized_monog_graph_matchings subscohg scohg cohg_succs !! match_number;

  bw_sized_monog_context_of_sized_monog_context
    (sized_monog_graph_decomp subscohg scohg cohg_succs me mv).




Definition sized_monog_graph_rewriting_correctness {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : nat * bool :=
  
  let ctxs := all_sized_monog_precontexts subscohg scohg in
  let len := length ctxs in
  (len, forallb (λ ctx,
    default false (
      bwctx ←@{option} bw_sized_monog_context_of_sized_monog_context ctx;
      Some $ default_sized_graph_iso_test scohg (make_bw_sized_monog_pushout subscohg
        bwctx))) ctxs).


Definition sized_monog_graph_rewriting_correctness' {N T} `{Countable N, Countable T}
  {i j} (subscohg : BWSizedCospanHyperGraph N T i j)
  {n m} (scohg : BWSizedCospanHyperGraph N T n m) : list (option bool) :=
  let ctxs := all_sized_monog_precontexts subscohg scohg in
  (λ ctx, bwctx ←@{option} bw_sized_monog_context_of_sized_monog_context ctx;
    Some $ default_sized_graph_iso_test scohg (make_bw_sized_monog_pushout subscohg
        bwctx)) <$> ctxs.








From stdpp Require Import strings.

Local Open Scope positive_scope.

(* FIXME: Move *)
#[global] Arguments mk_bscohg {N T n m} & (bw_scohg bw_inputs bw_outputs) : assert.
(* 
Definition test_graph_33_lhs : BWSizedCospanHyperGraph positive string (!1) (!1) :=
  mk_bscohg (mk_scohg (mk_cohg ∅
    [# 1] [# 1]
  ) {[1 := 1]}) eq_refl eq_refl.

Definition test_graph_33_rhs : CospanHyperGraph string 1 1 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ]} ∅)
    [# 1] [# 3]
  )%positive%string.

Definition test_graph_34_lhs : CospanHyperGraph string 1 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [1], [4]) ; 4 := ("g", [4], [5]) ]} ∅)
    [# 1] [# 3; 5]
  )%positive%string.

Definition test_graph_34_rhs : CospanHyperGraph string 1 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [1], [4]) ; 4 := ("f", [4], [5]) ;
    5 := ("g", [5], [6]) ; 6 := ("g", [6], [7]) ]} ∅)
    [# 1] [# 3; 7]
  )%positive%string.

(*
Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_lhs test_graph_34_rhs) in
    lazymatch r with
    | (39%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).
Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_lhs test_graph_34_lhs) in
    lazymatch r with
    | (29%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).

Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs test_graph_34_lhs) in
    lazymatch r with
    | (2%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).

Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs test_graph_34_rhs) in
    lazymatch r with
    | (2%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).
*)

Definition test_graph_34_layer n : CospanHyperGraph string n (n * 2) :=
  (fix go n : CospanHyperGraph string n (n * 2) :=
    match n with
    | 0 => id_graph 0
    | S n => stack_graphs test_graph_34_rhs (go n)
    end) n.

Fixpoint test_graph_34_exploded n : CospanHyperGraph string 1 (2 ^ n) :=
  match n with
  | 0 => id_graph 1
  | S n =>
    cast_graph eq_refl (Nat.mul_comm (2^n) 2) $ compose_graphs (test_graph_34_exploded n)
      (test_graph_34_layer _)
  end.


Definition test_graph_33_layer k : CospanHyperGraph string k k :=
  (fix go k : CospanHyperGraph string k k :=
    match k with
    | 0 => id_graph 0
    | S k => stack_graphs test_graph_33_rhs (go k)
    end) k.

Definition test_graph_33_array n k : CospanHyperGraph string k k :=
  (fix go n : CospanHyperGraph string k k :=
    match n with
    | 0 => id_graph k
    | S n => compose_graphs (test_graph_33_layer k) (go n)
    end) n.

(* Compute pretty (hg_succs test_graph_33_rhs). *)

Definition test_graph_33_rhs_stack2 : CospanHyperGraph string 2 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [4], [5]) ; 5 := ("g", [5], [6]) ]} ∅)
    [# 1; 4] [# 3; 6]
  )%positive%string.

(* Compute is_monogamousb (test_graph_33_array 3 2). *)

(* Compute monog_graph_rewriting_correctness test_graph_33_rhs_stack2
  (test_graph_33_array 3 2). *)

(* Compute monog_graph_rewriting_correctness (stack_graphs (id_graph 1)
test_graph_33_rhs_stack2) (test_graph_33_array 3 2). *)

(* Succeed Compute ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs_stack2
        (test_graph_33_array 2 2)) in
    lazymatch r with
    | (12%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)

(* Compute monog_graph_rewriting_correctness' test_graph_33_rhs test_graph_33_rhs_stack2. *)

(* Compute pretty $ monog_graph_matchings
  test_graph_33_rhs test_graph_33_rhs_stack2 (hg_succs test_graph_33_rhs_stack2). *)


(* Compute pretty $ uncurry (monog_graph_decomp test_graph_33_rhs test_graph_33_rhs_stack2
  (hg_succs test_graph_33_rhs_stack2)) <$> monog_graph_matchings
  test_graph_33_rhs test_graph_33_rhs_stack2 (hg_succs test_graph_33_rhs_stack2). *)

(* Compute pretty $ monog_graph_matchings test_graph_33_rhs test_graph_33_rhs (hg_succs test_graph_33_rhs). *)

(* Compute monog_graph_rewriting_correctness' test_graph_33_rhs test_graph_33_rhs. (test_graph_33_array 2 2). *)


(*
Definition test_graph_cap_lhs : CospanHyperGraph string 2 0 := cap_graph 1.
Definition test_graph_cap_rhs : CospanHyperGraph string 2 0 :=
  (mk_cohg (mk_hg {[1 := ("f", [1;2], [])]} ∅) [#1;2] [#])%positive.

  Time
Compute pretty $ all_bimonog_contexts test_graph_cap_lhs (test_graph_33_array 2 3) !! 10.

Compute filter is_bimonogamousb $ all_bimonog_contexts test_graph_cap_lhs (test_graph_33_array 2 2). *)



(* Compute is_bimonogamousb (@cup_graph positive 2). *)

(* Time Compute is_bimonogamousb (test_graph_33_array 10 10). *)

(* Compute length $ all_frobenius_contexts test_graph_33_rhs (test_graph_33_array 3 3). *)
(* Compute  test_graph_33_rhs (test_graph_33_array 3 3). *)
(* Compute is_bimonogamousb <$> all_frobenius_contexts test_graph_33_rhs (test_graph_33_array 3 3). *)


(* Compute frobenius_graph_rewriting_correctness test_graph_33_rhs (test_graph_34_exploded 3). *)

(* Definition Plist_idxmap (l : list positive) : Pmap positive :=
  list_to_map (imap (λ i p, (p, Pos.of_succ_nat i)) l).

Definition reduce_graph {T n m} (cohg : CospanHyperGraph T n m) : CospanHyperGraph T n m :=
  let fe := Plist_idxmap (map_to_list (hyperedges cohg)).*1 in
  let fv := Plist_idxmap (elements (vertices cohg)) in
  relabel_graph (fv !!!.) (reindex_graph (fe !!!.) cohg). *)

(* Compute pretty $ (reduce_graph (test_graph_34_exploded 3)). *)

(* Time Compute
  let cohg := ((* reduce_graph *) (test_graph_34_exploded 2)) in
  monog_graph_rewriting_correctness test_graph_33_rhs cohg. *)


Module PaperExample.


(* #[local] Instance pretty_blocks_letter : Pretty blocks :=
  (fun p =>
  "[" ++ String.concat "; "
    ((λ '(_, b), "{[" ++ String.concat "; " (pth_letter <$>
      merge_sort Pos.lt (elements b)) ++ "]}") <$> p) ++ "]")%string. *)

Local Open Scope positive_scope.
Local Open Scope list_scope.


Definition frel := make_blocks [ {[1; 2]}; {[3; 4]} ]%positive.
Definition grel := make_blocks [ {[1; 2; 3; 4]} ]%positive.

Section perms.
Local Notation a := 1%positive.
Local Notation b := 2%positive.
Local Notation c := 3%positive.
Local Notation d := 4%positive.
Local Notation e := 5%positive.




Definition correct_perms : list blocks :=
  (make_blocks <$> [[{[a;b;c;d]}];
[{[a]};{[b;c;d]}];
[{[b]};{[a;c;d]}];
[{[a;c]};{[b;d]}];
[{[c]};{[a;b;d]}];
[{[d]};{[a;b;c]}];
[{[a;d]};{[b;c]}];
[{[a;c]};{[b]};{[d]}];
[{[a;d]};{[b]};{[c]}];
[{[b;c]};{[a]};{[d]}];
[{[b;d]};{[a]};{[c]}]])%positive.

End perms.

(* Compute pretty (filter (λ p, join_partitions p frel = grel) (partitions 4)). *)

(* Compute bool_decide (filter (λ p, join_partitions p frel = grel) (partitions 4) ≡ₚ correct_perms). *)

Module Example1.

Local Definition i : nat := 2.
Local Definition j : nat := 2.

Local Definition subcohg : CospanHyperGraph string i j :=
  mk_cohg ∅ [#1; 1] [#2; 2].

Local Definition cohg : CospanHyperGraph string 0 0 :=
  mk_cohg (mk_hg {[ 1 := ("e", [1], [1])]} ∅) [#] [#].

(* Succeed Compute
    ltac:(let r := eval vm_compute in (frobenius_graph_rewriting_correctness subcohg cohg) in
    lazymatch r with
    | (61%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)

Local Definition all_contexts := all_frobenius_contexts subcohg cohg.

(* Compute length all_contexts. *)

Definition remove_dupsA {A} (R : relation A) `{!RelDecision R} : list A -> list A :=
  fix remove_dupsA (l : list A) :=
  match l with
  | [] => []
  | x :: l => if decide (Exists (R x) l) then remove_dupsA l
    else x :: remove_dupsA l
  end.

Definition remove_dupsb {A} (R : A -> A -> bool) : list A -> list A :=
  fix remove_dupsb (l : list A) :=
  match l with
  | [] => []
  | x :: l => if existsb (R x) l then remove_dupsb l
    else x :: remove_dupsb l
  end.

Definition ascii_newline : Ascii.ascii := Ascii.ascii_of_pos 10.
Definition string_newline : string := Eval lazy in String ascii_newline EmptyString.

(* Compute ("[" ++ String.concat string_newline (pretty <$> all_contexts) ++ "]")%string. *)

(* Compute length (remove_dupsb (@Testing.opt_weak_graph_iso_partial_test _ eq _ _ _) all_contexts).
Time Compute length (@remove_dupsA _ (@Testing.opt_weak_graph_iso_partial_test _ eq _ _ _)
  (λ _ _, _) all_contexts). *)

(* Time Compute frobenius_graph_rewriting_correctness subcohg cohg. *)




Local Definition mv : Pmap positive :=
  {[1 := 1; 2 := 1]}.

Local Definition me : Piso := ∅.

Local Definition true_bnd : Pset := {[1]}.

Local Definition g_equiv_classes_exploded_context :=
  exploded_context subcohg cohg me mv true_bnd.

Local Definition g_equiv_classes := g_equiv_classes_exploded_context.1.
Local Definition exploded_context := g_equiv_classes_exploded_context.2.



Local Definition exploded_interfaced_context :=
    mk_cohg exploded_context exploded_context.(inputs)
      (exploded_context.(outputs) +++ vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j))).

Local Definition subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs).

    (* Equivalence classes of interface vertices for _g_ *)
Local Definition interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)).

    (* Equivalence classes of interface vertices for _f_ *)
Local Definition f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes.

  (* Now, I'm ASSUMING (TODO: triple-check this) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

Local Definition g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes.

(* Compute pretty g_equiv_classes_blocks. *)

Local Definition f_g_equiv_classes :=
  merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks.

(* Compute pretty f_g_equiv_classes. *)

Local Definition block_1 : blocks := f_g_equiv_classes !!! 1.

Local Definition fully_quotiented_contexts :=
  Eval vm_compute in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

(* Compute length fully_quotiented_contexts. *)

Local Instance cohg_empty {T n m} : Empty (CospanHyperGraph T n m) :=
  mk_cohg ∅ (fun_to_vec (λ _, xH)) (fun_to_vec (λ _, xH)).

Local Instance cohg_inhabited {T n m} : Inhabited (CospanHyperGraph T n m) :=
  populate $ mk_cohg ∅ (fun_to_vec (λ _, xH)) (fun_to_vec (λ _, xH)).


(* Compute forallb (graph_iso_partial_test cohg)
  (make_pushout subcohg <$> fully_quotiented_contexts). *)


(* Compute pretty block_1. *)

(* Compute length $ partitions_joining_wildly_inefficient block_1.
Compute length $ partitions_joining_mildly_inefficient block_1. *)






#[export] Instance maybe_Npos : Maybe Npos :=
  fun n =>
  match n with
  | N0 => None
  | Npos p => Some p
  end.

Definition map_partition (f : positive -> positive) (p : blocks) : blocks :=
  (λ '(bmin, bset), let bset' := set_map f bset in
    (default bmin (maybe Npos (Pset_min bset')), bset')) <$> p.

Definition block_1_quotiented : blocks :=
  map (λ '(bmin, _), (bmin, {[bmin]})) block_1.

(* Compute length $ partitions_joining_wildly_inefficient block_1_quotiented. *)

(* TODO: Investigate / think about if this is a valid way to cut down on the
  number of resulting graphs, or if it's unsafe [AN: I think this cuts down
    to something like the number of distinct pushouts, but it's cutting down
    based on the boundary non-injectivity of subcohg—which is not ultimately
    what we care about! Possibly if we modify this idea to use the boundary
    of the RHS of the rewrite, we can make it work...]*)
(* Compute length $
  remove_dups
  $
  remove_dups ∘ merge_sort (rel_preimage fst Pos.lt) ∘ map_partition (partition_quotient block_1 !!!.) <$>
  partitions_joining_wildly_inefficient block_1. *)



(* Compute (bool_decide ((map_partition (partition_quotient block_1 !!!.) block_1) = block_1_quotiented)). *)

End Example1.


Module Example_bell.

Definition graph_X n : CospanHyperGraph positive (N.to_nat n) 0 :=
  mk_cohg
    (mk_hg
      (list_to_map ((λ p, (p, (p, [p], []))) <$> pseq 1 n)) ∅)
      (fun_to_vec (λ p, Pos.of_succ_nat p)) [#].

Definition graph_Z n : CospanHyperGraph positive 0 0 :=
  mk_cohg
    (mk_hg
      (list_to_map ((λ p, (p, (p, [xH], []))) <$> pseq 1 n)) ∅) [#] [#].

(* Succeed Compute
    ltac:(let r := eval vm_compute in (frobenius_graph_rewriting_correctness (graph_X 1) (graph_Z 2)) in
    lazymatch r with
    | (1%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)


Local Definition i : nat := 1.
Local Definition j : nat := 0.

Local Definition n : nat := 0.
Local Definition m : nat := 0.

Local Definition subcohg : CospanHyperGraph positive i j :=
  graph_X 1.

Local Definition cohg : CospanHyperGraph positive n m :=
  graph_Z 2.

(* Compute frobenius_graph_rewriting_correctness subcohg
  (relabel_graph (Pos.add (xO $ xO (Pos.of_succ_nat (i + j)))) cohg). *)

Local Definition all_contexts := all_frobenius_contexts subcohg cohg.

(* Compute pretty $ all_contexts !! 1. *)

(* Compute opt_weak_graph_iso_partial_test cohg ∘
  make_pushout subcohg <$> all_contexts. *)

Local Open Scope positive_scope.

(* Compute pretty $ frobenius_edge_matchings_extending
  (graph_boundary subcohg) subcohg cohg (∅, ∅).

Compute pretty $ frobenius_graph_matchings subcohg cohg. *)

Local Definition me : Piso :=
  mk_Piso'' {[1 := 1]}.

Local Definition mv : Psurj :=
  Psurj_of_Pmap {[1 := 1]}.


Local Definition true_bnd : Pset := set_map (mv.(Psurj_map) !!!.) (graph_boundary subcohg).



Local Definition g_equiv_classes_exploded_context :=
  exploded_context subcohg cohg me mv true_bnd.

Local Definition g_equiv_classes :=
  map xI <$>
  g_equiv_classes_exploded_context.1.
Local Definition exploded_context :=
  relabel_graph xI
  g_equiv_classes_exploded_context.2.
Local Definition mv' :=
  (* xI <$>  *)
  mv.(Psurj_map).

(* Compute pretty g_equiv_classes.

Compute pretty exploded_context. *)





Local Definition exploded_interfaced_context :=
    mk_cohg exploded_context exploded_context.(inputs)
      (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j)) +++ exploded_context.(outputs)).

Local Definition subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs).

    (* Equivalence classes of interface vertices for _g_ *)
Local Definition interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv' !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)).

    (* Equivalence classes of interface vertices for _f_ *)
Local Definition f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes.

  (* Now, I'm ASSUMING (TODO: triple-check this) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

Local Definition g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes.

(* Compute pretty g_equiv_classes_blocks. *)

Local Definition f_g_equiv_classes :=
  merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks.

(* Compute pretty exploded_interfaced_context.

Compute pretty f_g_equiv_classes. *)

(* Compute pretty $ quotient_maps f_g_equiv_classes.

(* Compute pretty f_g_equiv_classes. *)

Local Definition block_1 : blocks := f_g_equiv_classes !!! 1. *)

Local Definition fully_quotiented_contexts :=
  Eval vm_compute in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

(* Compute frobenius_graph_rewriting_correctness subcohg cohg. *)

(* Compute pretty fully_quotiented_contexts.

Compute pretty (make_pushout subcohg <$> fully_quotiented_contexts).
Compute pretty cohg.

Compute pretty (@opt_weak_graph_iso_partial_test _ eq _ _ _ cohg ∘ make_pushout subcohg <$> fully_quotiented_contexts). *)




(* Compute pretty matching. *)
(*
Compute let '(me, mv, true_bnd) := matching in
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  length $ quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← frobenius_graph_matchings subcohg cohg;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.



Local Definition i : nat := 2.
Local Definition j : nat := 2.

Local Definition subcohg : CospanHyperGraph string i j :=
  mk_cohg ∅ [#1; 1] [#2; 2].

Local Definition cohg : CospanHyperGraph string 0 0 :=
  mk_cohg (mk_hg {[ 1 := ("e", [1], [1])]} ∅) [#] [#].


Time Compute frobenius_graph_rewriting_correctness subcohg cohg. *)

End Example_bell.



End PaperExample.


Module Bug1.
Local Open Scope positive_scope.
Definition Glhs:=
  mk_cohg (mk_hg {[ 1 := (1, [], [3; 5]) ]} ∅) [#] [#3; 5]
  : CospanHyperGraph positive 0 2.
Definition Gtgt :=
  mk_cohg (mk_hg {[ 3 := (3, [5; 9], [7]); 4 := (1, [8], [138; 9]);
    42 := (3, [74; 138], []);
    66 := (1, [], [74; 5]) ]} {[ 5; 9; 74; 138 ]}) [#8] [#7]
  : CospanHyperGraph positive 1 1.

(* Compute bimonog_graph_rewriting_correctness Glhs Gtgt. *)
(* Should be (1, true) *)


(* Compute pretty $ bimonog_graph_matchings Glhs Gtgt.

Definition me : Piso := mk_Piso'' {[ 1 := 66 ]}.
Definition mv : Pmap positive := {[ 3 := 74; 5 := 5 ]}.

Definition contexts :=
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context Glhs Gtgt me mv (map_img mv) in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

Compute is_bimonogamousb <$> (make_pushout Glhs <$> contexts).






Compute bimonog_graph_rewriting_correctness Glhs Gtgt. *)


End Bug1. *)