Require Export Homomorphism AProp FreeSemiRing GraphTerm Isomorphism.IsoAux.


(* FIXME: Move *)
Lemma DoublePushout_with_struct_isomorphic {T n m}
  (H : CospanHyperGraph T n m) (G : HyperGraph T)
  L {ni nj} (i : vec _ ni) (j : vec _ nj) G' :
  (i -> G <- j) ≡ᵢ G' ->
  DoublePushout_with H G L i j ≡ᵢ
  let ins := list_to_set (inputs H) in
  let outs := list_to_set (outputs H) in
  let isolated := isolated_vertices H in
  let L1 := decompose_L1 H L in
  let C1 := decompose_C1 H L ins in
  let C2 := decompose_C2 H L C1 isolated outs in
  let k := list_to_vec (elements (decompose_kset H L C1 isolated ins outs)) in
  compose_graphs (inputs H -> C1 <- k +++ i)
    (compose_graphs (stack_graphs (k -> ∅ <- k) G')
       (k +++ j -> C2 <- outputs H)).
Proof.
  intros Hiso.
  unfold DoublePushout_with.
  f_equiv.
  f_equiv.
  f_equiv.
  done.
Qed.




(* FIXME: Move *)
Lemma hd_elem_of {A} (a : A) (l : list A) : l <> [] ->
  hd a l ∈ l.
Proof.
  destruct l; [easy|constructor].
Qed.


Lemma graph_to_term_correctness `{Equiv T} {n m} (cohg : CospanHyperGraph T n m) ap :
  graph_to_term cohg = Some ap ->
  cohg ≡ₛ AProp_graph_semantics ap ->
  cohg ≡ₛ AProp_graph_semantics ap.
Proof.
  done.
Qed.

(* FIXME: Move *)
Definition graph_to_term' `{Inhabited T} {n m} (cohg : CospanHyperGraph T n m) :
  AProp T n m :=
  default (Agen inhabitant n m) (graph_to_term cohg).


Definition graph_rewrite_helper `{Inhabited T} `{Equiv T, RelDecision T T equiv}
  {n m} (GTarg : CospanHyperGraph T n m)
  {i j} (GLHS : CospanHyperGraph T i j) (match_number : nat) :
  option {k & (CospanHyperGraph T n (k + i) *
    CospanHyperGraph T (k + j) m)%type} :=
  match prod_map Piso_map Piso_map <$> (graph_monos GLHS GTarg !! match_number) with
  | None => None
  | Some mhe_mv =>
    Some $
    let GLHS_L := (relabel_graph (Pmap_injmap mhe_mv.2) $
      reindex_graph (Pmap_injmap mhe_mv.1) GLHS) in
    let L := (map_to_list mhe_mv.1).*2 in
    let ins := list_to_set (inputs GTarg) in
    let outs := list_to_set (outputs GTarg) in
    let isolated := isolated_vertices GTarg in
    let L1 := decompose_L1 GTarg L in
    let C1 := decompose_C1 GTarg L ins in
    let C2 := decompose_C2 GTarg L C1 isolated outs in
    let klist := elements (decompose_kset GTarg
      (map_to_list mhe_mv.1).*2 C1 isolated ins outs) in
    (* let k := list_to_vec klist in *)
    existT (length (klist)) (
    (* graph_to_term' *) (inputs GTarg -> C1 <- list_to_vec klist +++ inputs GLHS_L),
      (* graph_to_term'  *)(list_to_vec klist +++ outputs GLHS_L -> C2 <- outputs GTarg))
  end.


Definition aprop_is_id {T n m} (ap : AProp T n m) : option (n = m) :=
  match ap with
  | Aid _ => Some eq_refl
  | _ => None
  end.

Fixpoint cleanup_id_stack {T n m} (ap : AProp T n m) : AProp T n m :=
  match ap in AProp _ n m return AProp _ n m with
  | @Astack _ n1 m1 n2 m2 ap1 ap2 =>
    let ap1' := cleanup_id_stack ap1 in
    let ap2' := cleanup_id_stack ap2 in
    match aprop_is_id ap1' with
    | Some Heq1 =>
      match decide (n1 = 0) with
      | left Hn10 =>
        cast_aprop (eq_sym (eq_trans (f_equal (λ k, k + _) Hn10) (Nat.add_0_l _)))
          (eq_sym (eq_trans (f_equal (λ k, k + _) (eq_trans (eq_sym Heq1) Hn10)) (Nat.add_0_l _))) ap2'
      | right _ =>
        match aprop_is_id ap2' with
        | Some Heq2 =>
          cast_aprop eq_refl (f_equal2 Nat.add Heq1 Heq2) (Aid (_ + _))
        | None => ap1' * ap2'
        end
      end
    | None =>
      match aprop_is_id ap2' with
      | Some Heq2 =>
        match decide (n2 = 0) with
        | left Hn20 =>
          cast_aprop (eq_sym (eq_trans (f_equal (Nat.add _) Hn20) (Nat.add_0_r _)))
          (eq_sym (eq_trans (f_equal (Nat.add _) (eq_trans (eq_sym Heq2) Hn20)) (Nat.add_0_r _))) ap1'
        | right _ =>
          ap1' * ap2'
        end
      | None =>
        ap1' * ap2'
      end
    end
  | @Acompose _ i j k ap1 ap2 =>
    let ap1' := cleanup_id_stack ap1 in
    match aprop_is_id ap1' with
    | Some Heq =>
      cast_aprop (eq_sym Heq) eq_refl (cleanup_id_stack ap2)
    | None =>
      let ap2' := cleanup_id_stack ap2 in
      match aprop_is_id ap2' with
      | Some Heq =>
        cast_aprop eq_refl Heq ap1'
      | None =>
        ap1' ;' ap2'
      end
    end
  | Aswap k l =>
    match decide (k = 0) with
    | left Hk => cast_aprop
        (eq_sym (eq_trans (f_equal (λ k, k + _) Hk) (Nat.add_0_l _)))
        (eq_sym (eq_trans (f_equal (λ k, _ + k) Hk) (Nat.add_0_r _)))
        (Aid l)
    | right _ =>
      match decide (l = 0) with
      | left Hl => cast_aprop
          (eq_sym (eq_trans (f_equal (λ k, _ + k) Hl) (Nat.add_0_r _)))
          (eq_sym (eq_trans (f_equal (λ k, k + _) Hl) (Nat.add_0_l _)))
          (Aid k)
      | right _ => Aswap k l
      end
    end
  | x => x
  end.

Definition term_rewrite_helper `{Inhabited T} `{Equiv T, RelDecision T T equiv}
  {n m} (Targ : AProp T n m) {i j} (LHS : AProp T i j) (match_number : nat) :
  option {k & (AProp T n (k + i) * AProp T (k + j) m)%type} :=
  match graph_rewrite_helper (AProp_graph_semantics Targ)
    (AProp_graph_semantics LHS) match_number with
  | Some (existT k (C1, C2)) =>
    Some $ existT k (graph_to_term' C1, graph_to_term' C2)
  | None => None
  end.

Definition mk_aprop_surrounds {T n m i j k}
  (C1 : AProp T n (k + i)) (L : AProp T i j) (C2 : AProp T (k + j) m) : AProp T n m :=
  C1 ;' Aid k * L ;' C2.

Lemma term_rewrite_helper_correctness
  `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A, EqA : EqDecision A, WFA : WFSummable A}
  `{Equiv T, Equivalence T equiv, RelDecision T T equiv,
    Inhabited T} `{TensT : !TensorLike R A T}
  {n m} (Targ : AProp T n m) {i j} (LHS RHS : AProp T i j) (match_number : nat) :
  AProp_semantics (TensT:=TensT) LHS ≡ AProp_semantics (TensT:=TensT) RHS ->
  (match term_rewrite_helper Targ LHS match_number with
   | None => True
   | Some (existT k (C1, C2)) =>
    (Targ ≡ₐ mk_aprop_surrounds C1 LHS C2)%aprop ->
    AProp_semantics (TensT:=TensT) Targ ≡ AProp_semantics (TensT:=TensT)
    (mk_aprop_surrounds C1 RHS C2)
  end).
Proof.
  remember (term_rewrite_helper _ _ _) as x.
  clear Heqx.
  intros Heq.
  destruct x as [ [k [C1 C2] ]|]; [|done].
  intros Hiso.
  rewrite <- AProp_graph_semantics_correct.
  unfold AProp_graph_eq in Hiso.
  erewrite (graph_semantics_syntactic_eq _ _ Hiso).
  rewrite AProp_graph_semantics_correct.
  cbn.
  apply compose_tensor_mor; [|done].
  apply compose_tensor_mor; [done|].
  apply stack_tensor_mor; [done|].
  done.
Qed.


