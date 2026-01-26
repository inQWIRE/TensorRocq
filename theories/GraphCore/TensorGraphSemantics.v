Require Export TensorGraphExpr.
Require Export TensorExprDBSemantics.

(* Semantics of tensor graphs into (semi)rings, via tensor expressions *)


Section TensorGraphSemantics.

Context {R A T : Type}.

Let TensorGraph := (TensorGraph T).

Implicit Types tg : TensorGraph.

Definition graph_V : nat -> Type := fun _ => A.
Definition graph_Vsum `{Summable A} : forall k, Summable (graph_V k)
  := fun _ => _.



(* Combine input and output maps to get the local variable map *)
Definition graph_ml (minput : gmap nat A) (moutput : gmap nat A) :
  Pmap (Vval graph_V) :=
  @mk_Vval graph_V 0 <$> gmaps_to_Pmap minput moutput.


Definition graph_tensor_to_V_n_args
  {n m} (t : vec A n -> vec A m -> R) :=
  tensor_to_V_n_args_aux graph_V 0 (uncurry t ∘ Vector.splitat n).



Definition graph_mabs `{TensorLike R A T} 
  (tg : TensorGraph) : Pmap (@Vfunc R graph_V) :=
  kmap (Pos.of_succ_nat) $ map_imap (fun k (dt : T) =>
    (* let node := mk_node (i_internal_edges tg) (i_external_edges tg) n in *)
    let inarity := in_arity tg.2 k in
    let outarity := out_arity tg.2 k in
    Some $ mk_Vfunc graph_V (replicate (inarity + outarity) O)
      (graph_tensor_to_V_n_args (interpretTensor dt inarity outarity))
    ) tg.1.

Definition graph_map_semantics 
  `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} `{TensT : TensorLike R A T}
  (tg : TensorGraph)
  (minput : gmap nat A) (moutput : gmap nat A) : R :=
  tl_total_semantics (SR:=SR) graph_V (Vsum:=graph_Vsum)
    (graph_mabs tg)
    ∅
    (graph_ml minput moutput)
    (graph_tensorlist_semantics tg).




Definition graph_list_semantics 
  `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} `{TensT : TensorLike R A T}
  (tg : TensorGraph) (ins : list A) (outs : list A) : R :=
  graph_map_semantics tg
    (list_to_map $ zip (sorted_inputs tg) ins)
    (list_to_map $ zip (sorted_outputs tg) outs).

Definition graph_vector_semantics 
  `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} `{TensT : TensorLike R A T}
  (tg : TensorGraph) (ins : vec A (graph_insize tg)) (outs : vec A (graph_outsize tg)) : R :=
  graph_list_semantics tg (vec_to_list ins) (vec_to_list outs).

End TensorGraphSemantics.
