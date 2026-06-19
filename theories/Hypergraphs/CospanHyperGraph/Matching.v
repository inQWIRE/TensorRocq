From TensorRocq Require Import Isomorphism.IsoAux CospanHyperGraph.Definitions.

(* A matching of cospans of hypergraphs subcohg into cohg is a subgraph
  homomorphism (concretely, a pair of maps fv and fe on the vertices and
  edges preserving incidence, i.e. for every edge (idx, (t, ins, outs)) of subcohg,
    (fe idx, (t, fv <$> ins, fv <$> outs)) is an edge of cohg) such that
  a) fe is injective
  b) fv is injective _except_ possibly on the boundary/interface of subcohg
  c) for every vertex v of the interior of subcohg, every edge e' of
    cohg incident to v is in the image of fe

  Given these three conditions, we can construct _a_ pushout complement
  (in the category of hypergraphs, so not necessarily maintaining
    acyclicity or monogamy) by removing the image of the interior of subcohg
  from cohg and (TODO: HOW????) handling the boundary
    (TODO: Follow up. AN: I feel like there's some way to handle this
    progressively vertex-by-vertex on the boundary. Even though this has
    been presented as a two-step, global process (construct a whole exploded
    graph, then figure out how to quotient) it seems we should simply be
    able to enumerate the positions a given vertex can go in. I'll explore
    this for bimonogamous in this file, then maybe try to extend.)
  *)

(* NB: IN THIS FILE I WILL ASSUME EDGE LABELS ARE [Countable].
  This is so I can use [Pmap]s to index edges by label _and_ degrees. *)

(* How to construct a matching:
  As a zeroeth step, we match all isolated vertices (this match is unique,
    if it exists)
  First, we have to match all the edges.
    1. We construct a map from (label, indegree, outdegree) to the list of
      edge indices in cohg with that label, indegree, and outdegree,
      and do the same for subcohg.
    2. Using these maps, we enumerate all the possible edge matches

  Second, we have to extend these matchings subordinate to the

*)

Fixpoint sublistings_aux {B} (l'revhd l' : list B) : list (B * list B) :=
  match l' with
  | [] => []
  | b :: l' =>
    (b, rev_append l'revhd l') :: sublistings_aux (b :: l'revhd) l'
  end.

Fixpoint sublistings {A B} (l : list A) (l' : list B) : list (list (A * B)) :=
  match l with
  | [] => [[]]
  | a :: l =>
    '(b, l') ← sublistings_aux [] l';
    ((a, b) ::.) <$> sublistings l l'
  end.

Fixpoint ofold_sublistings {A B C} (f : A -> B -> C -> option C)
  (l : list A) (l' : list B) (acc : C) : list C :=
  match l with
  | [] => [acc]
  | a :: l =>
    '(b, l'') ← sublistings_aux [] l';
    match f a b acc with
    | None => []
    | Some acc' =>
      ofold_sublistings f l l'' acc'
    end
  end.

Definition kimerge `{forall A, MapFold K1 A (M1 A)}
  `{forall A, PartialAlter K2 A (M2 A)}
  `{forall A, Empty (M2 A)} {A B}
  (f : K1 -> A -> K2 * B) (m : M1 A) : M2 (list B) :=
  map_fold (fun k1 a (m' : M2 (list B)) =>
    let '(k2, b) := f k1 a in
    partial_alter (fun a_s =>
      Some (from_option (b ::.) [b] a_s)) k2 m')
  (∅ :> M2 (list B)) m.





(* Compute sublistings [1;2] [1;2;3].
Time
Compute ofold_sublistings (fun n m res =>
  if decide (Nat.divide n m) then Some ((n, m) :: res) else None)
  (seq 2 4) (seq 1 10) []. *)

Definition update_edge_match (e e' : positive * list positive * list positive)
  (me_mv : Piso * Piso) : option (Piso * Piso) :=
  let '(me, mv) := me_mv in
  let '(idx, ins, outs) := e in
  let '(idx', ins', outs') := e' in
  me' ← pupdate idx idx' me;
  mv' ← pupdates (zip (ins ++ outs) (ins' ++ outs')) mv;
  Some (me', mv').

Fixpoint edge_matchings_extending_aux_aligned
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
    ofold_sublistings update_edge_match es es' me_mv ≫=
    edge_matchings_extending_aux_aligned es_es'
  end.

Definition make_label_indexed_edge_map `{Countable T}
  (es : Pmap (T * list positive * list positive)) :
  gPmap (T * N * N) (list (positive * list positive * list positive)) :=
  kimerge (M2:=gPmap _) (fun idx '(t, ins, outs) =>
    ((t, lengthN ins, lengthN outs), (idx, ins, outs))) es.

Definition make_aligned_edge_list {T}
  (es es' : gPmap (T * N * N) (list (positive * list positive * list positive))) :
  list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)) :=
  let m' := merge (M:=Pmap) (fun me me' =>
    (λ e, from_option (e,.) (e, []) me') <$> me) es es' in
  (map_to_list m').*2.

Definition edge_matchings_extending `{Countable T}
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
  edge_matchings_extending_aux_aligned
    (make_aligned_edge_list (make_label_indexed_edge_map es)
      (make_label_indexed_edge_map es')) me_mv.

Definition edge_matchings `{Countable T}
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Piso) :=
  (* let vmap := vertex_map es' in
  filter (
    fun '(me, mv) =>
    map_Forall
      (fun _ v' =>
        Is_true match vmap !! v' with
        | None => true
        | Some (inc_es, inc_es') =>
          let incident_edges := inc_es ∪ inc_es' in
          Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
            me.(Piso_invmap)
        end)
      mv.(Piso_map)
  ) $ *)
    edge_matchings_extending es es' (∅, ∅).



From stdpp Require Import strings.

Definition test_graph_33_lhs : CospanHyperGraph string 1 1 :=
  (mk_cohg ∅
    [# 1] [# 1]
  )%positive%string.

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

Local Open Scope positive_scope.

Compute
  map_to_list $ elements <$> 
  (uncurry union <$> vertex_map (hyperedges test_graph_34_lhs)).

Time
Compute
  let f := fun m =>
  merge_sort (rel_preimage fst Pos.lt) $ map_to_list (m.(Piso_map)) in
  prod_map f f <$> edge_matchings_extending (hyperedges test_graph_33_rhs)
  (hyperedges test_graph_34_lhs) (∅, ∅).


