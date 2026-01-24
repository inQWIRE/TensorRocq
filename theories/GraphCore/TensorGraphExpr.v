Require Export TensorGraph Aux_pos.

Require Export TensorExprDBSyntax.

(* Semantics of TensorGraphs into tensor expressions *)


Section TensorGraphExpr.

Context {T : Type}.

Let TensorGraph := (TensorGraph T).

Implicit Types tg : TensorGraph.

Definition input_edges (linternal lexternal : list labedge) 
  (k : nat) : list var :=
  ((rel ∘ Pos.of_succ_nat ∘ fst) <$> 
    node_input_edges k linternal) ++
  ((loc ∘ bcons false ∘ Pos.of_succ_nat ∘ fst) <$> 
    node_input_edges k lexternal).

Definition output_edges (linternal lexternal : list labedge) 
  (k : nat) : list var :=
  ((rel ∘ Pos.of_succ_nat ∘ fst) <$> 
    node_output_edges k linternal) ++
  ((loc ∘ bcons false ∘ Pos.of_succ_nat ∘ fst) <$> 
    node_output_edges k lexternal).



Definition mk_node (linternal lexternal : list labedge)
  (k : nat) :=
  (Pos.of_succ_nat k, input_edges linternal lexternal k,
    output_edges linternal lexternal k).




Definition graph_tensorlist_semantics (tg : TensorGraph) : tensorlist :=
  mk_tl (const 0%nat <$> internal_edges tg)
    (mk_node (i_internal_edges tg) (i_external_edges tg) <$> 
      (map_to_list (fst tg)).*1).

End TensorGraphExpr.