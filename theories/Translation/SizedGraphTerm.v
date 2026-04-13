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

(* FIXME: Move *)
Definition Mcompose_cast `{MD : Monoid M mO madd meq} {T n m m' o}
  (mp1 : MProp M T n m) (mp2 : MProp M T m' o) (Hm : meq m m') :
  MProp M T n o :=
  Mcompose (cast_mprop (MD.(meq_equivalence).(Equivalence_Reflexive) _) Hm mp1) mp2.

Lemma vremove_vmap `(f : A -> B) {n} (i : fin n) (v : vec A n) :
  vremove i (vmap f v) = vmap f (vremove i v).
Proof.
  induction n as [| n IHn]; inv_all_vec_fin; [done|].
  cbn [vmap].
  destruct n; [by inv_all_vec_fin|].
  inv_all_vec_fin; [done|].
  change (vremove (FS ?i) (?x ::: ?v)) with (x ::: vremove i v).
  rewrite IHn.
  done.
Qed.
Lemma apply_sw_vmap `(f : A -> B) {n} (v : vec A n) (l : list nat) :
  apply_sw (vmap f v) l = vmap f (apply_sw v l).
Proof.
  revert v l; induction n as [|n IHn]; intros v l; [done|].
  cbn.
  case_decide.
  - refine (match n with
    | 1 => _
    | _ => _
    end v); cycle 1; [|easy..].
    intros vs.
    inv_all_vec_fin.
    cbn.
    now case_decide.
  - destruct l; [done|].
    case_decide; [|done].
    rewrite vremove_vmap.
    cbn.
    rewrite IHn.
    rewrite vlookup_map.
    done.
Qed.


Section Helpers.

Context  `{MD : Monoid M mO madd meq} (* `{MEQ : !RelDecision meq} *)
  `{FMD : !FreeMonoid M X} `{EQX : EqDecision X}.


Notation "0" := mO.
Notation "x '==' y" := (meq x y) (at level 70).
Infix "+" := madd.

(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Meq_equivalence : Equivalence meq := meq_equivalence.
Local Existing Instance Meq_equivalence.

Let Madd_proper : Proper (meq ==> meq ==> meq) madd := madd_proper.
Local Existing Instance Madd_proper.


Implicit Type smap : Pmap X.

Fixpoint Mstacks {T A} {n : A -> M} {m : A -> M}
  (f : forall a, MProp M T (n a) (m a)) (l : list A) :
    MProp M T (Mlist_sum (n <$> l)) (Mlist_sum (m <$> l)) :=
  match l with
  | [] => Mid mO
  | a :: l => Mstack (f a) (Mstacks f l)
  end.

Definition sizeX (smap : Pmap X) := (λ i, default mO (mdecomp_inv <$> (smap !! i))).


(* FIXME: Move *)
Lemma fmap_concat `(f : A -> B) (ls : list (list A)) : 
  f <$> concat ls = concat (fmap (M:=list) f <$> ls).
Proof.
  induction ls; [done|].
  cbn.
  rewrite fmap_app.
  f_equal; auto.
Qed.
Lemma Mlist_sum_concat (ls : list (list M)) : 
  Mlist_sum (concat ls) == Mlist_sum (Mlist_sum <$> ls).
Proof.
  induction ls; [done|].
  cbn.
  rewrite Mlist_sum_app.
  now f_equiv.
Qed.

Lemma layer_to_aprop_prf {T n} {smap} {es : list (HyperEdge T)}
  {inputs : vec positive n} {es_inputs unused_inputs} : 
  apply_sw inputs ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) <$>
     es_inputs ++ unused_inputs) =@{list _}
  flat_map (λ tio, tio.1.2) es ++ unused_inputs ->
  Mlist_sum (apply_sw (vmap (sizeX smap) inputs)
     ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) <$>
      es_inputs ++ unused_inputs)) ==
  Mlist_sum ((λ tio, Mlist_sum (sizeX smap <$> tio.1.2)) <$> es) +
  Mlist_sum (sizeX smap <$> unused_inputs).
Proof.
  intros Heq.
  rewrite <- Mlist_sum_app.
  rewrite apply_sw_vmap, vec_to_list_map.
  rewrite Heq.
  rewrite fmap_app, 2 Mlist_sum_app.
  f_equiv.
  rewrite flat_map_concat_map.
  change @map with (@fmap list _).
  rewrite fmap_concat.
  rewrite Mlist_sum_concat.
  rewrite <- 2 list_fmap_compose.
  done.
Qed.

Definition layer_to_mprop {T n} smap (es : list (HyperEdge T))
  (inputs : vec positive n) : option (MProp M T
    (Mlist_sum (MD:=MD)(vec_to_list (vmap (sizeX smap) inputs)))
    (Mlist_sum (MD:=MD) (((λ tio, Mlist_sum (sizeX smap <$> tio.2)) <$> es))
    + Mlist_sum (MD:=MD) (sizeX smap <$> (filter (.∉ foldr app [] es.*1.*2) (vec_to_list inputs))))
     * list positive) :=
  (let es_inputs := foldr app [] es.*1.*2 in
  let es_outputs := foldr app [] es.*2 in
  let unused_inputs := filter (.∉ es_inputs) (vec_to_list inputs) in
  let estack := Mstacks (fun tio =>
    Mgen tio.1.1 (Mlist_sum (sizeX smap <$> tio.1.2))
      (Mlist_sum (sizeX smap <$> tio.2))) es in
  let perm := (mprop_of_sw (vmap (sizeX smap) inputs)
    ((λ k, default (pos_to_nat_pred k) $ list_index k inputs)
    <$> (es_inputs ++ unused_inputs))) in
  Heq ← guard (apply_sw inputs ((λ k, default (pos_to_nat_pred k) $ list_index k inputs)
    <$> (es_inputs ++ unused_inputs)) =@{list _}
    flat_map (λ tio, tio.1.2) es ++ unused_inputs);
  let t := Mcompose_cast perm (Mstack estack (Mid (Mlist_sum (sizeX smap <$> unused_inputs)))) 
  (layer_to_aprop_prf Heq) in
  Some (t, es_outputs ++ unused_inputs)).

Lemma mprop_perm_of_empty_sized_graph_prf {n m} {smap}
  {inputs : vec positive n} {outputs : vec positive m} : 
  apply_sw (vmap (smap !!.) inputs)
    ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) <$>
     (vec_to_list outputs)) =@{list _} vmap (smap !!.) outputs ->
  Mlist_sum
    (apply_sw (vmap (sizeX smap) inputs)
     ((λ k, default (pos_to_nat_pred k) (list_index k inputs)) <$>
      (vec_to_list outputs))) == Mlist_sum (vmap (sizeX smap) outputs).
Proof.
  intros Heq.
  unfold sizeX.
  (* change (size smap) with (default mO ∘ (fmap mdecomp_inv) ∘ (smap !!.)). *)
  setoid_rewrite <- (Vector.map_map _ _ _ (smap !!.) (default mO ∘ (fmap mdecomp_inv))).
  rewrite vec_to_list_map, <- Heq.
  rewrite apply_sw_vmap, vec_to_list_map.
  done.
Qed.


Definition mprop_perm_of_empty_sized_graph {T n m} smap
  (inputs : vec positive n) (outputs : vec positive m) :
    option (MProp M T (Mlist_sum (vmap (sizeX smap) inputs))
      (Mlist_sum (vmap (sizeX smap) outputs))) :=
    Heq ← guard (apply_sw (vmap (smap !!.) inputs) 
      ((λ k, default (pos_to_nat_pred k) (list_index k inputs))
        <$> vec_to_list outputs) =@{list _} vmap (smap !!.) outputs);
    Some (((mprop_of_sw (vmap (sizeX smap) inputs)
      ((λ k, default (pos_to_nat_pred k) (list_index k inputs))
        <$> vec_to_list outputs))) ;' Massoc' 
        (mprop_perm_of_empty_sized_graph_prf Heq)).

Lemma sized_graph_to_term_aux_prf {T n smap}
  {es : list (positive * HyperEdge T)} {inputs : vec positive n}
  {inputs'} :
  (λ i : positive, smap !! i) <$> flat_map (λ tio : positive * HyperEdge T, tio.2.2) es ++
  filter (λ x : positive, x ∉ foldr app [] es.*2.*1.*2) (vec_to_list inputs) =
  (λ i : positive, smap !! i) <$> inputs' ->
  Mlist_sum ((λ tio : HyperEdge T, Mlist_sum (sizeX smap <$> tio.2)) <$> es.*2) +
  Mlist_sum (sizeX smap <$> filter (λ x : positive, x ∉ foldr app [] es.*2.*1.*2) (vec_to_list inputs)) ==
  Mlist_sum (vmap (sizeX smap) (list_to_vec inputs')).
Proof.
  intros Heq.
  unfold sizeX.
  setoid_rewrite <- (Vector.map_map _ _ _ (smap !!.) (default mO ∘ (fmap mdecomp_inv))).
  rewrite 2 vec_to_list_map, vec_to_list_to_vec, <- Heq.
  rewrite <- (list_fmap_compose _ (default 0 ∘ _)).
  unfold compose.
  fold (sizeX smap).
  rewrite fmap_app, Mlist_sum_app.
  f_equiv.
  rewrite flat_map_concat_map.
  change @map with (@fmap list _).
  rewrite fmap_concat.
  rewrite Mlist_sum_concat.
  rewrite <- 3 list_fmap_compose.
  done.
Qed.


Fixpoint sized_graph_to_term_aux {T n m} (depth : nat)
  smap
  (hg : Pmap (HyperEdge T)) (inputs : vec positive n) (outputs : vec positive m) :
    option (MProp M T (Mlist_sum (vmap (sizeX smap) inputs))
      (Mlist_sum (vmap (sizeX smap) outputs))) :=

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
      Heq ← guard ((smap !!.) <$> (flat_map (λ tio, tio.2.2) es ++ 
        filter (λ x : positive, x ∉ foldr app [] es.*2.*1.*2) (vec_to_list inputs))
        = (smap !!.) <$> inputs');
      Some (tl ;' Massoc' (sized_graph_to_term_aux_prf Heq) ;' tr)
      (* Mocompose tl tr ≫= ocast_mprop_r _ *)
      (* tl' ← ocast_aprop tl;
      Some (tl' ;' tr)%aprop *)
    end
  end.



Definition sized_graph_to_term {T n m} (scohg : SizedCospanHyperGraph X T n m) :
  option (MProp M T (Mlist_sum (vmap (sizeX scohg.(sized_map)) scohg.(inputs)))
      (Mlist_sum (vmap (sizeX scohg.(sized_map)) scohg.(outputs)))) :=
  sized_graph_to_term_aux (size (hyperedges scohg)) (scohg.(sized_map))
    (hyperedges scohg) (inputs scohg) (outputs scohg).






Definition MProp_graph_eq `{FMD : !FreeMonoid M X}
  `{Equiv T} {n m} (mp mp' : MProp M T n m) :=
  (MProp_sized_graph_semantics mp ≡ₛ MProp_sized_graph_semantics mp')%scohg.

End Helpers.

From TensorRocq Require Import BW.
(* FIXME: MOve *)
#[export] Instance btree_equiv_dec `{EqDecision A} : RelDecision (≡@{btree A}) :=
  rel_preimage_dec _ _ _.


Notation "x ;'' y" := (ltac:(refine (Mcompose_cast x%mprop y%mprop _);
  match goal with
  |- ?g => (* idtac g;  *)compute_done
  end))
  (at level 50, left associativity, only parsing) : mprop_scope.

Section Example.



#[local] Instance Equiv_bool : Equiv bool := eq.

Local Notation "'correct' ap" :=
  (from_option (λ t, MProp_graph_eq t ap) False
    (sized_graph_to_term (MProp_sized_graph_semantics ap) ≫= ocast_mprop _ _ ))
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
  vm_compute (sizeX _).
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