Require Export TensorGraph GraphRewriting TensorGraphExpr 
  TensorGraphSemantics TensorGraphFacts.

Definition hypergraph_apply_hom {T T'} (f : T -> T') 
 (hg : HyperGraph T) : HyperGraph T' :=
  mk_hg (prod_map (prod_map f id) id <$> hg.(hyperedges)) hg.(hypervertices).

Definition graph_apply_hom {T T'} (f : T -> T') 
  {n m} (cohg : CospanHyperGraph T n m) : CospanHyperGraph T' n m :=
  mk_cohg (hypergraph_apply_hom f cohg.(hedges)) cohg.(inputs) cohg.(outputs).