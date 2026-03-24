Require Export TensorGraph AProp.


(* FIXME: Move *)
Tactic Notation "vm_eval" uconstr(pat) :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in *;
  vm_compute in Hx;
  subst x.



Fixpoint Astacks {T A} {n : A -> nat} {m : A -> nat}
  (f : forall a, AProp T (n a) (m a)) (l : list A) : AProp T (sum_list_with n l) (sum_list_with m l) :=
  match l with
  | [] => Aid 0
  | a :: l => f a * Astacks f l
  end.

(* FIXME: Move *)
Definition rel_preimage_dec {A B} (f : A -> B) (R : relation B) :
  RelDecision R -> RelDecision (rel_preimage f R) := fun HR x y => HR (f x) (f y).

#[export] Hint Extern 0 (RelDecision (rel_preimage ?f ?R)) => 
  notypeclasses refine (rel_preimage_dec f R _) : typeclass_instances.

Definition rel_preimage_dec' {A B} (f : A -> B) (R : relation B) x y :
  Decision (R (f x) (f y)) -> Decision (rel_preimage f R x y) := λ H, H.

#[export] Hint Extern 0 (Decision (rel_preimage ?f ?R ?x ?y)) => 
  notypeclasses refine (rel_preimage_dec' f R x y _) : typeclass_instances.


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

(* Heuristic for ordering input lists (hence edges): which have 
  more lower inputs? *)

Definition pos_lists_earlier (ins1 ins2 : list positive) : Z :=
  foldr (λ '(i1, i2), Z.add (Z.sgn (Z.pos_sub i1 i2))) 0%Z (cprod ins1 ins2).

Definition sort_extracted_edges {T} (es : list (positive * HyperEdge T)) :
  list (positive * HyperEdge T) :=
  merge_sort (rel_preimage (λ ktio, ktio.2.1.2) 
    (λ ins1 ins2, (pos_lists_earlier ins1 ins2) < 0)%Z) es.

(* Relabel a graph to have inputs 1 .. n *)
Definition norm_graph_inputs {T n m} (cohg : CospanHyperGraph T n m) : CospanHyperGraph T n m :=
  relabel_graph (λ p, default p ((cohg.(inputs) :> list _) !! (pos_to_nat_pred p))) cohg.

Definition layer_to_stack {T n} (es : list (HyperEdge T)) 
  (inputs : vec positive n) : option (AProp T n (n + sum_list_with (length ∘ snd) es - 
    sum_list_with (length ∘ snd ∘ fst) es)) :=
    (Apad_nonsquare_l (Astacks (fun tio => Agen tio.1.1 (length tio.1.2) (length tio.2))
    es) n).

Definition layer_to_aprop {T n} (es : list (HyperEdge T)) 
  (inputs : vec positive n) : option (AProp T n (n + sum_list_with (length ∘ snd) es - 
    sum_list_with (length ∘ snd ∘ fst) es) * list positive) :=
  let es_inputs := foldr app [] es.*1.*2 in 
  let es_outputs := foldr app [] es.*2 in
  let unused_inputs := filter (.∉ es_inputs) (vec_to_list inputs) in 
  t ← layer_to_stack es inputs;
  Some ((aprop_of_sw n (((λ k, default (pos_to_nat_pred k) $ list_index k inputs)
    <$> (es_inputs ++ unused_inputs)))  ;' (* TODO: Check this is the right permutation!!!! *)
  t)%aprop, es_outputs ++ unused_inputs).

Definition aprop_perm_of_empty_graph {T n m}
  (inputs : vec positive n) (outputs : vec positive m) : option (AProp T n m) :=
  match decide (n = m) with
  | right _ => None
  | left Hnm => 
    Some (cast_aprop eq_refl Hnm (aprop_of_sw n ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) <$> vec_to_list outputs)))%aprop
  end.

Fixpoint graph_to_term_aux {T n m} (depth : nat) 
  (hg : Pmap (HyperEdge T)) (inputs : vec positive n) (outputs : vec positive m) :
    option (AProp T n m) :=
  
  match hg with 
  | PEmpty =>
    aprop_perm_of_empty_graph inputs outputs
  | PNodes _ => 
    match depth with
    | 0 => None
    | S depth =>
      let '(es, (_, hg')) := 
        get_simultaneously_extractable_edges inputs hg in
      '(tl, inputs') ← layer_to_aprop es.*2 inputs;
      tr ← graph_to_term_aux depth hg' (list_to_vec inputs') outputs;
      tl' ← ocast_aprop tl;
      Some (tl' ;' tr)%aprop
    end  
  end.


Definition graph_to_term {T n m} (cohg : CospanHyperGraph T n m) : option (AProp T n m) :=
  graph_to_term_aux (size (hyperedges cohg)) (hyperedges cohg) (inputs cohg) (outputs cohg).







Section Example.


#[local] Instance Equiv_bool : Equiv bool := eq.

Local Notation "'correct' ap" :=
  (from_option (λ t, AProp_graph_eq t ap)%aprop False (graph_to_term (AProp_graph_semantics ap)))
  (at level 10, only parsing).

Example test_HG2T_Aswap11 : 
  correct (@Aswap bool 1 1).
Proof.
  remember (graph_to_term _) as x eqn:Hx.
  vm_compute in Hx.
  subst.
  cbn.
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.


Local Notation "'correct_perm' ap" :=
  (from_option (λ t, AProp_graph_eq t ap)%aprop False 
    (aprop_perm_of_empty_graph (AProp_graph_semantics ap).(inputs)
      (AProp_graph_semantics ap).(outputs)))
  (at level 10, only parsing).

Example test_HG2T_sw120_alt : 
  correct (Aswap 1 1 * @Aid bool 1 ;' Aid 1 * Aswap 1 1).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.

Example test_HG2T_sw120 : 
  correct (sw [1;2;0] :> AProp bool _ _).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.


Example test_HG2T_sw201 : 
  correct (sw [2;0;1] :> AProp bool _ _).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.



Example test_HG2T_gen11 : 
  correct (Agen true 1 1).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.

Example test_HG2T_gen11_11 : 
  correct (Agen true 1 1 * Agen false 1 1).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.


Example test_HG2T_gen12_11 : 
  correct (Agen true 1 2 ;' Agen false 1 1 * Aid 1).
Proof.
  unfold from_option.
  case_match eqn:Heq; vm_compute in Heq; [|done].
  revert Heq.
  intros [= <-].
  apply graph_iso_partial_test_correct; vm_compute; done.
Qed.


Example bug_case_1 : 
  let G := ([#74%positive; 19%positive] ->
       mk_hg
         (list_to_map
             [(32%positive, (true, [], [68%positive]))])
         {[19%positive; 74%positive]} <- [#19%positive; 68%positive; 74%positive]) in 
  forall ap,
  graph_to_term G = Some ap ->
  G ≡ₛ AProp_graph_semantics ap.
Proof.
  cbv zeta.


  vm_eval (graph_to_term _).
  intros _ [= <-].
  apply graph_iso_partial_test_correct.
  vm_compute.
  done.

  (* unfold graph_to_term.
  vm_compute (size _).
  unfold graph_to_term_aux.
  vm_eval (hyperedges _).
  vm_eval (get_simultaneously_extractable_edges _ _).
  vm_eval (inputs _).
  unfold layer_to_aprop.
  vm_eval (fmap (M:=list) _ _).
  vm_eval (fmap (M:=list) _ _).
  vm_eval (layer_to_aprop _ _).
  cbn. *)
Qed.
    


End Example.