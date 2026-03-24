Require Export Syntax TensorGraph.Definitions TensorGraph.Expr.

(* Semantics of tensor graphs into (semi)rings, via tensor expressions *)


Section TensorGraphSemantics.

Context `{TensT : TensorLike R rO rI radd rmul req A T, !EqDecision A}.

Let TensorGraph := (CospanHyperGraph T).



(* Combine input and output maps to get the local variable map *)
Definition graph_ml (minput : gmap nat A) (moutput : gmap nat A) :
  Pmap A := gmaps_to_Pmap minput moutput.

Definition graph_mabs (tm : Pmap (T * list positive * list positive)) : 
  Pmap (@DimensionlessTensor R A) :=
  interpretTensor ∘ fst ∘ fst <$> tm.

Definition graph_map_semantics
  {n m} (tg : TensorGraph n m)
  (minput : gmap nat A) (moutput : gmap nat A) : R :=
  ntl_total_semantics (SR:=SR)
    (graph_mabs tg.(hedges))
    (graph_ml minput moutput)
    (graph_namedtensorlist_semantics tg).



Definition graph_semantics
  {n m} (tg : TensorGraph n m) : @Tensor R n m A :=
  namedtensorlist_to_tensor (SR:=SR) (graph_mabs tg.(hedges))
    (vmap (bcons false ∘ Pos.of_succ_nat) (vseq 0 n)) 
    (vmap (bcons true ∘ Pos.of_succ_nat) (vseq 0 m))
    (graph_namedtensorlist_semantics tg).

#[global] Arguments graph_semantics {_ _} _ _ _ / : assert.

Definition cohg_semantic_eq {n m} (tg tg' : TensorGraph n m) :=
  graph_semantics tg ≡ graph_semantics tg'.

#[export] Instance cohg_semantic_eq_equivalence {n m} : 
  Equivalence (@cohg_semantic_eq n m) := rel_preimage_equiv _ _ _.

Lemma graph_semantics_to_contl
  {n m} (tg : TensorGraph n m) :
  graph_semantics tg = 
  contl_semantics (graph_mabs tg.(hedges)) (graph_contl_semantics tg).
Proof.
  reflexivity.
Qed.

Lemma graph_semantics_norm_verts
  {n m} (cohg : TensorGraph n m) :
  graph_semantics (norm_verts cohg) = 
  graph_semantics cohg.
Proof.
  unfold graph_semantics.
  rewrite graph_namedtensorlist_semantics_norm_verts.
  reflexivity.
Qed.

#[export] Instance cohg_vert_eq_semantic_eq {n m} : 
  subrelation cohg_vert_eq (@cohg_semantic_eq n m).
Proof.
  intros cohg cohg' Hnorm.
  unfold cohg_semantic_eq.
  rewrite <- graph_semantics_norm_verts, Hnorm, graph_semantics_norm_verts.
  done.
Qed.


End TensorGraphSemantics.

Notation "cohg ≡ₜ cohg'" := (cohg_semantic_eq cohg%cohg cohg'%cohg) 
  (at level 70) : cohg_scope.

Notation "cohg '≡ₜ@{' TensT '}' cohg'" := 
  (cohg_semantic_eq (TensT:=TensT) cohg%cohg cohg'%cohg) 
  (at level 70, only parsing) : cohg_scope.

#[export] Hint Mode TensorLike - - - - - - - - - - + - - : typeclass_instances.

Add Parametric Morphism `{TensT : TensorLike R rO rI radd rmul req A T, 
  !EqDecision A} {n m} : (graph_semantics (TensT:=TensT) (n:=n) (m:=m)) 
  with signature cohg_semantic_eq ==> equiv as graph_semantics_semantic_eq.
Proof.
  done.
Qed.
