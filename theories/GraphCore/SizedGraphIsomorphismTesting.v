Require Export IsomorphismTesting SizedGraph.



Definition sized_graph_isos {N} `{EqDecision N} `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : list (Piso * Piso) :=
  filter (λ mhe_mv,
    Forall (λ kv, scohg.(sized_map) !! kv.1 = scohg'.(sized_map) !! kv.2)
      (map_to_list mhe_mv.2.(Piso_map))) (graph_isos scohg scohg').

Lemma sized_graph_isos_correct {N} `{EqDecision N} `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : 
  Forall (λ _, scohg ≡ₛ scohg') (sized_graph_isos scohg scohg').
Proof.
Admitted.

Definition sized_graph_iso_partial_test {N} `{EqDecision N} 
  `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : bool :=
  match sized_graph_isos scohg scohg' with
  | [] => false
  | _ :: _ => true
  end.

Lemma sized_graph_iso_partial_test_correct {N} `{EqDecision N} 
  `{Equiv T, !RelDecision (≡@{T})}
  {n m} (scohg scohg' : SizedCospanHyperGraph N T n m) : 
  sized_graph_iso_partial_test scohg scohg' = true -> 
  scohg ≡ₛ scohg'.
Proof.
  pose proof (sized_graph_isos_correct scohg scohg') as Hiso.
  unfold sized_graph_iso_partial_test.
  case_match; [done|].
  now rewrite Forall_cons in Hiso.
Qed.




Section dec_equiv.

Context {N} `{EqDecision N} `{Equiv T, !RelDecision (≡@{T})}.


Fixpoint sized_hyperedge_map_monos_extending_aux
  (hg hg' : list (positive * 
    (T * list (positive * option N) * list (positive * option N))))
  (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  match hg with
  | [] => [mhe_mv]
  | (k, (t, ins, outs)) :: hg =>
    list_select (λ k_tio, t ≡ k_tio.2.1.1 /\
      (k_tio.2.1.2).*2 = ins.*2 /\
      (k_tio.2.2).*2 = outs.*2) hg' ≫= λ '(k_tio, hg'rest),
      default [] (mhe' ← pupdate k k_tio.1 mhe_mv.1;
        mv' ← pupdates (zip (ins ++ outs).*1 (k_tio.2.1.2 ++ k_tio.2.2).*1)
          mhe_mv.2;
        Some (sized_hyperedge_map_monos_extending_aux hg hg'rest
         (mhe', mv')))
  end.


Definition sized_hyperedge_map_monos_extending
  (ms : Pmap N) (ms' : Pmap N)
  (hg hg' : Pmap (HyperEdge T)) (mhe_mv : Piso * Piso) :
  list (Piso * Piso) :=
  sized_hyperedge_map_monos_extending_aux 
    (prod_map id (relabel_abs (λ k, (k, ms !! k))) <$> map_to_list hg)
    (prod_map id (relabel_abs (λ k, (k, ms' !! k))) <$> map_to_list hg')
    mhe_mv.

Definition sized_graph_monos {i j n m} (subscohg : SizedCospanHyperGraph N T i j)
  (scohg : SizedCospanHyperGraph N T n m) :
  list (Piso * Piso) :=
  if decide (size (isolated_vertices subscohg) <= size (isolated_vertices scohg)) then
    sized_hyperedge_map_monos_extending subscohg.(sized_map) scohg.(sized_map) 
      subscohg.(hyperedges)
        scohg.(hyperedges) (∅, ∅)
  else
    [].

End dec_equiv.