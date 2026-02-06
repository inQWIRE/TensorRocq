Require Export TensorGraphExpr.
Require Export TESemantics.

(* Semantics of tensor graphs into (semi)rings, via tensor expressions *)


Section TensorGraphSemantics.

Context {R A T : Type}.

Let TensorGraph := (CospanHyperGraph T).



(* Combine input and output maps to get the local variable map *)
Definition graph_ml (minput : gmap nat A) (moutput : gmap nat A) :
  Pmap A := gmaps_to_Pmap minput moutput.

Definition graph_mabs `{TensorLike R A T}
  (tm : Pmap (T * list positive * list positive)) : Pmap (@DimensionlessTensor R A) :=
  interpretTensor ∘ fst ∘ fst <$> tm.

Definition graph_map_semantics `{SR : SemiRing R rO rI radd rmul req} 
  `{!Summable A, !EqDecision A} `{TensT : TensorLike R A T}
  {n m} (tg : TensorGraph n m)
  (minput : gmap nat A) (moutput : gmap nat A) : R :=
  ntl_total_semantics (SR:=SR)
    (graph_mabs tg.(hedges))
    (graph_ml minput moutput)
    (graph_namedtensorlist_semantics tg).



Definition graph_semantics `{SR : SemiRing R rO rI radd rmul req} 
  `{!Summable A, !EqDecision A} `{TensT : TensorLike R A T}
  {n m} (tg : TensorGraph n m) : @Tensor R n m A :=
  namedtensorlist_to_tensor (SR:=SR) (graph_mabs tg.(hedges))
    (vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n)) 
    (vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m))
    (graph_namedtensorlist_semantics tg).


Lemma graph_semantics_to_contl `{SR : SemiRing R rO rI radd rmul req} 
  `{!Summable A, !EqDecision A} `{TensT : TensorLike R A T}
  {n m} (tg : TensorGraph n m) :
  graph_semantics (SR:=SR) tg = 
  contl_semantics (graph_mabs tg.(hedges)) (graph_contl_semantics tg).
Proof.
  reflexivity.
Qed.

End TensorGraphSemantics.
