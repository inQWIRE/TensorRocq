(* A file containing rewriting theory, especially for rewriting in 
  autonomous and frobenius categories *)

From TensorRocq Require Import CospanHyperGraph.Definitions
  Isomorphism.IsoAux Isomorphism.Testing CospanHyperGraph.Matching
  Props.Prop.PropGraphTerm.



Definition nth_frobenius_context 
  `{Countable T}
  {i j} (lhs : CospanHyperGraph T i j) 
  {n m} (cohg : CospanHyperGraph T n m) 
  (match_number : nat) : 
  option (CospanHyperGraph T n (i + j + m)) :=
  ctx ← all_frobenius_contexts lhs cohg !! match_number;
  if opt_weak_graph_iso_partial_test (make_pushout lhs ctx) cohg
    then Some ctx
  else None.



