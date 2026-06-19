Require Export Setoid. 
From stdpp Require Export base list.
From TensorRocq Require Import Aux_relset Aux_pos.






(* Heuristic for ordering input lists (hence edges): which have 
  more lower inputs? *)

Definition pos_lists_earlier (ins1 ins2 : list positive) : Z :=
  foldr (λ '(i1, i2), Z.add (Z.sgn (Z.pos_sub i1 i2))) 0%Z (cprod ins1 ins2).





From TensorRocq Require Import HyperGraph.


Definition get_extractable_edges {T} (inputs : Pset)
  (edges : Pmap (HyperEdge T)) :=
  filter (λ ktio, Forall (.∈ inputs) ktio.2.1.2) edges.

Fixpoint get_simultaneously_extractable_edges_aux {T} (inputs : list positive) 
  (n : nat) (es : list (positive * HyperEdge T)) : 
  list (positive * HyperEdge T) * (list positive * list (positive * HyperEdge T)) :=
  match n with 
  | 0 => ([], (inputs, es))
  | S n' =>
    match es with 
    | [] => ([], (inputs, []))
    | ktio :: es => 
      if decide (Forall (.∈ inputs) ktio.2.1.2) then 
        prod_map (ktio ::.) id $ get_simultaneously_extractable_edges_aux 
          (filter (.∉ ktio.2.1.2) inputs) n es
      else
        prod_map id (prod_map id (ktio ::.)) $ get_simultaneously_extractable_edges_aux inputs n es
    end
  end.

Definition get_simultaneously_extractable_edges {T} (inputs : list positive) 
  (es : Pmap (HyperEdge T)) : list (positive * HyperEdge T) * (list positive * Pmap (HyperEdge T)) :=
  prod_map id (prod_map id list_to_map) $ 
    let es' := map_to_list es in 
    get_simultaneously_extractable_edges_aux inputs (length es') es'.



Definition sort_extracted_edges {T} (es : list (positive * HyperEdge T)) :
  list (positive * HyperEdge T) :=
  merge_sort (rel_preimage (λ ktio, ktio.2.1.2) 
    (λ ins1 ins2, (pos_lists_earlier ins1 ins2) < 0)%Z) es.



