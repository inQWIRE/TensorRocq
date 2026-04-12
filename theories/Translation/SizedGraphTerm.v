From TensorRocq Require Export SizedCospanHyperGraph MProp GraphTermAux.


Fixpoint remove_first `{EqDecision A} (a : A) (l : list A) : list A :=
  match l with 
  | [] => []
  | b :: l => if decide (a = b) then l else b :: remove_first a l
  end.

Fixpoint list_mdifference `{EqDecision A} (n m : list A) : list A :=
  match m with 
  | [] => n
  | x :: m => 
    list_mdifference (remove_first x n) m
  end.



Section Helpers.

Context  `{MD : Monoid M mO madd meq} `{MEQ : !RelDecision meq}.


Notation "0" := mO.
Notation "x '==' y" := (meq x y) (at level 70).
Infix "+" := madd.

(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Meq_equivalence : Equivalence meq := meq_equivalence.
Local Existing Instance Meq_equivalence.

Let Madd_proper : Proper (meq ==> meq ==> meq) madd := madd_proper.
Local Existing Instance Madd_proper.

Implicit Type smap : Pmap M.

Fixpoint Mstacks {T A} {n : A -> M} {m : A -> M}
  (f : forall a, MProp M T (n a) (m a)) (l : list A) : 
    MProp M T (Mlist_sum (n <$> l)) (Mlist_sum (m <$> l)) :=
  match l with
  | [] => Mid mO
  | a :: l => Mstack (f a) (Mstacks f l)
  end.

Let size (smap : Pmap M) := (λ i, default mO (smap !! i)).


(* Definition sized_layer_to_stack {T n} smap (es : list (HyperEdge T)) 
  (inputs : vec positive n) : option 
    (MProp M T (Mlist_sum (size smap <$> vec_to_list inputs))
      (Mlist_sum (size smap <$> 
        (list_mdifference inputs (flat_map (snd ∘ fst) es))))
      n (n + sum_list_with (length ∘ snd) es - 
    sum_list_with (length ∘ snd ∘ fst) es)) :=
    (AProp.Apad_nonsquare_l (Astacks (fun tio => Agen tio.1.1 (length tio.1.2) (length tio.2))
    es) n). *)

Definition layer_to_mprop {T n} smap (es : list (HyperEdge T)) 
  (inputs : vec positive n) : option (MProp M T 
    (Mlist_sum (MD:=MD)(vec_to_list (vmap (size smap) inputs)))
    (Mlist_sum (MD:=MD) (((λ tio, Mlist_sum (size smap <$> tio.2)) <$> es))
    + Mlist_sum (MD:=MD) (size smap <$> (filter (.∉ foldr app [] es.*1.*2) (vec_to_list inputs))))
     * list positive) :=
  let es_inputs := foldr app [] es.*1.*2 in 
  let es_outputs := foldr app [] es.*2 in
  let unused_inputs := filter (.∉ es_inputs) (vec_to_list inputs) in 
  let estack := Mstacks (fun tio =>
    Mgen tio.1.1 (Mlist_sum (size smap <$> tio.1.2))
      (Mlist_sum (size smap <$> tio.2))) es in 
  let perm := (mprop_of_sw (vmap (size smap) inputs) 
    ((λ k, default (pos_to_nat_pred k) $ list_index k inputs)
    <$> (es_inputs ++ unused_inputs))) in
  t ← Mocompose perm (Mstack estack (Mid (Mlist_sum (size smap <$> unused_inputs))));
  Some (t, es_outputs ++ unused_inputs).


Definition mprop_perm_of_empty_sized_graph {T n m} smap
  (inputs : vec positive n) (outputs : vec positive m) : 
    option (MProp M T (Mlist_sum (vmap (size smap) inputs))
      (Mlist_sum (vmap (size smap) outputs))) :=
    ocast_mprop_r _ ((mprop_of_sw (vmap (size smap) inputs) 
      ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) 
        <$> vec_to_list outputs))).


Fixpoint sized_graph_to_term_aux {T n m} (depth : nat) 
  smap
  (hg : Pmap (HyperEdge T)) (inputs : vec positive n) (outputs : vec positive m) :
    option (MProp M T (Mlist_sum (vmap (size smap) inputs))
      (Mlist_sum (vmap (size smap) outputs))) :=
  
  match hg with 
  | PEmpty =>
    mprop_perm_of_empty_sized_graph smap inputs outputs
  | PNodes _ => 
    match depth with
    | 0 => None
    | S depth =>
      let '(es, (_, hg')) := 
        get_simultaneously_extractable_edges inputs hg in
      '(tl, inputs') ← layer_to_mprop smap es.*2 inputs;
      tr ← sized_graph_to_term_aux depth smap hg' (list_to_vec inputs') outputs;
      Mocompose tl tr ≫= ocast_mprop_r _
      (* tl' ← ocast_aprop tl;
      Some (tl' ;' tr)%aprop *)
    end  
  end.


Definition sized_graph_to_term {T n m} (scohg : SizedCospanHyperGraph M T n m) : 
  option (MProp M T (Mlist_sum (vmap (size scohg.(sized_map)) scohg.(inputs)))
      (Mlist_sum (vmap (size scohg.(sized_map)) scohg.(outputs)))) :=
  sized_graph_to_term_aux (base.size (hyperedges scohg)) (scohg.(sized_map)) 
    (hyperedges scohg) (inputs scohg) (outputs scohg).






Definition MProp_graph_eq `{FMD : !FreeMonoid M X} 
  `{Equiv T} {n m} (mp mp' : MProp M T n m) :=
  (MProp_sized_graph_semantics mp ≡ₛ MProp_sized_graph_semantics mp')%scohg.

End Helpers.

From TensorRocq Require Import MProp.Automation.
(* FIXME: MOve *)
#[export] Instance btree_equiv_dec `{EqDecision A} : RelDecision (≡@{btree A}) :=
  rel_preimage_dec _ _ _.

Definition Mcompose_cast `{MD : Monoid M mO madd meq} `{!RelDecision meq} {T n m m' o} 
  (mp1 : MProp M T n m) (mp2 : MProp M T m' o) (Hm : meq m m') : 
  MProp M T n o :=
  Mcompose mp1 (Mcompose (Massoc' Hm) mp2).

Notation "x ;'' y" := (ltac:(refine (Mcompose_cast x%mprop y%mprop _);
  match goal with 
  |- ?g => (* idtac g;  *)compute_done
  end))
  (at level 50, left associativity, only parsing) : mprop_scope.

Section Example.



#[local] Instance Equiv_bool : Equiv bool := eq.

Local Notation "'correct' ap" :=
  (from_option (λ t, MProp_graph_eq t ap) False 
    (sized_graph_to_term (map_sized_graph mdecomp_inv $ MProp_sized_graph_semantics ap) ≫= ocast_mprop _ _ ))
  (at level 10, only parsing).

Example test_HG2T_Aswap11 : 
  correct (Mswap (T:=bool) (bleaf true) (bleaf false)).
Proof.
  vm_eval (sized_graph_to_term _).
  cbn.
  vm_eval (ocast_mprop _ _ _).
  cbn.
  apply sized_graph_iso_partial_test_correct.
  vm_compute.
  reflexivity.
Qed.

Example test_HG2T_sw120_alt : 
  correct (Mswap (bleaf true) (bleaf false) * 
    Mid (T:=bool) (bnode (bleaf true) (bleaf false)) ;''
    Mid (T:=bool) (bleaf false) * Mswap (bnode (bleaf true) (bleaf true)) (bleaf false))%mprop.
Proof.
  vm_eval (mbind _ _);
  cbn;
  apply sized_graph_iso_partial_test_correct;
  vm_compute;
  reflexivity.
Qed.

(* Example test_HG2T_sw120 : 
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
Qed. *)



Example test_HG2T_gen11 : 
  correct (Mgen true (bleaf true) (bleaf false)).
Proof.
  vm_eval (mbind _ _);
  cbn;
  apply sized_graph_iso_partial_test_correct;
  vm_compute;
  reflexivity.
Qed.

Example test_HG2T_gen11_11 : 
  correct (Mgen true (bleaf false) (bleaf true) ;' Mgen false (bleaf true) (bleaf true)).
Proof.
  vm_eval (mbind _ _);
  cbn;
  apply sized_graph_iso_partial_test_correct;
  vm_compute;
  reflexivity.
Qed.


Example test_HG2T_gen12_11 : 
  correct (Mgen true (bempty) (bnode (bleaf true) (bleaf false)) ;' Mgen false (bleaf true) (bleaf false) * Mid (bleaf false)).
Proof.
  
  vm_eval (mbind _ _);
  cbn;
  apply sized_graph_iso_partial_test_correct;
  vm_compute;
  reflexivity.
Qed.

(* 
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
Qed. *)
    


End Example.