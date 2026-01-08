Require Import Summable.
Require StringCustomNotation.

From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

Require Import Aux_stdpp.

Require Import TensorExprSyntax.


(* FIXME: Move *)
Fixpoint collate `{Empty M} `{Insert K (list A) M} `{Lookup K (list A) M}
  (l : list (K * A)) : M :=
  match l with 
  | [] => ∅ 
  | (k, a) :: l => 
    let c := (collate l :> M) in 
    <[k := a :: default [] (c !! k)]> c
  end.


(* FIXME: Move *)
Fixpoint collate_alt `{Empty M} `{PartialAlter K (list A) M}
  (l : list (K * A)) : M :=
  match l with 
  | [] => ∅ 
  | (k, a) :: l => 
    partial_alter (fun mk => 
      Some (a :: default [] mk)) k (collate_alt l)
  end.

(* TODO: Gneralize this list-to-option function? *)
Lemma lookup_collate {K M A} `{FinMap K M} (l : list (K * A)) k : 
  (collate l :> M (list A)) !! k = 
    let l := (filter (λ kv, kv.1 = k) l).*2 in 
    if decide (l = []) then None else Some l.
Proof.
  induction l as [|[k' a] l IHl].
  - cbn.
    by rewrite lookup_empty, decide_True.
  - cbn.
    destruct_decide (decide (k' = k)) as Hk'.
    + subst.
      rewrite lookup_insert.
      rewrite IHl.
      symmetry.
      rewrite decide_False by done.
      cbn.
      destruct ((filter _ _).*2); reflexivity.
    + rewrite lookup_insert_ne by done.
      exact IHl.
Qed.

Lemma delete_collate {K M A} `{FinMap K M} (l : list (K * A)) k : 
  delete k (collate l :> M (list A)) = collate (filter (λ kv, kv.1 ≠ k) l).
Proof.
  induction l as [|[k' a] l IHl]; [apply delete_empty|].
  cbn.
  rewrite decide_not.
  case_decide as Hk'.
  - subst.
    by rewrite delete_insert_delete.
  - rewrite delete_insert_ne by done.
    cbn.
    f_equal; [|apply IHl].
    do 2 f_equal.
    rewrite 2 lookup_collate.
    f_equal_let.
    setoid_rewrite list_filter_filter.
    f_equal.
    apply list_filter_iff.
    intros; firstorder congruence.
Qed.

Lemma collate_Permutation {K M A} `{FinMap K M} (l : list (K * A)) :
  flat_map (fun '(k, vs) => (k ,.) <$> vs) (map_to_list (collate l :> 
    M (list A))) ≡ₚ l.
Proof.
  revert l.
  apply (Nat.measure_induction _ length _).
  intros l IHl.
  destruct l as [|[k v] l].
  - cbn.
    by rewrite map_to_list_empty.
  - cbn.
    rewrite <- insert_delete_insert.
    rewrite map_to_list_insert by apply lookup_delete.
    rewrite delete_collate.
    cbn [flat_map].
    rewrite IHl by now
      eapply Nat.le_lt_trans; [apply length_filter|constructor].
    erewrite <- (filter_with_neg_Permutation (P:= (λ kv, kv.1 = k)) l) at 3.
    rewrite app_comm_cons.
    f_equiv.
    rewrite lookup_collate.
    cbn.
    case_decide as Hfilt; [now destruct (filter _ _)|].
    cbn.
    f_equiv.
    rewrite <- list_fmap_compose.
    clear IHl Hfilt.
    induction l as [|[k' v'] l IHl]; [done|].
    cbn.
    case_decide.
    + cbn.
      subst.
      now rewrite IHl.
    + apply IHl.
Qed.

Definition map_is_empty `{MapFold K A M} (m : M) : bool := 
  map_fold (fun _ _ _ => false) true m.

Lemma map_is_empty_spec {K A M} `{FinMap K M} (m : M A) : 
  map_is_empty m = true <-> m = ∅.
Proof.
  unfold map_is_empty.
  induction m using map_ind.
  - now rewrite map_fold_empty.
  - rewrite map_fold_insert_L by easy.
    split; [easy|].
    intros Heq%(f_equal (.!! i)).
    revert Heq.
    now simplify_map_eq.
Qed.



Notation Pset_to_gset s :=
  (list_to_set (C:=gset string) (strings.pos_to_string <$> elements s)).

Notation gmap_to_Pmap s :=
  (list_to_map (M:=Pmap string) (prod_map strings.string_to_pos id <$> map_to_list s)).

Notation Pmap_to_gmap s :=
  (list_to_map (M:=gmap string string) (prod_map strings.pos_to_string id <$> map_to_list s)).

Fixpoint extend_map_of_abstract_pair (lbound rbound : Pset)
  (m : Pmap Idx) (l r : list Idx) : option (Pmap Idx) :=
  match l, r with 
  | [], [] => Some m
  | hl :: l, hr :: r => 
    let phl := strings.string_to_pos hl in 
    let phr := strings.string_to_pos hr in 
    (* TODO: Refactor to match on both decide (ph[lr] ∉ [lr]bound)*)
    if bool_decide (phl ∉ lbound) then 
      if bool_decide (hl = hr /\ phr ∉ rbound) then 
        extend_map_of_abstract_pair lbound rbound m l r
      else None
    else
      if bool_decide (phr ∉ rbound) then None else
      match m !! phl with 
      | Some mhl => 
        if bool_decide (mhl = hr) then 
          extend_map_of_abstract_pair lbound rbound m l r
        else None
      | None => 
        extend_map_of_abstract_pair lbound rbound (<[phl := hr]> m) l r
      end
  | _, _ => None
  end.

Definition extend_match_of_abstract_tensor_args 
  (lbound rbound : Pset) : forall (m : Pmap Idx) 
  (labs rabs : list (list Idx * list Idx)), option (Pmap Idx) := 
  Eval cbv delta [list_bind from_option mbind option_bind] beta in 
  fix extend_match_of_abstract_tensor_args m labs rabs :=
  match labs with 
  | [] => match rabs with
    | [] => Some m
    | _ => None
    end
  | (lowl, upl) :: labs => 
    list_first_omap (fun '((lowr, upr), rrest) => 
      m' ← extend_map_of_abstract_pair lbound rbound m lowl lowr;
         m'' ← extend_map_of_abstract_pair lbound rbound m' upl upr;
         extend_match_of_abstract_tensor_args m'' labs rrest)
         (list_removals rabs)
  end.



Definition match_tensorlist_fast_aux 
  (lbound rbound : Pset) 
    (labs rabs : list (Idx * list Idx * list Idx)) : 
  option (Pmap Idx) :=
  map_fold 
    (B:=Pmap (list (list Idx * list Idx)) -> option (Pmap Idx)) 
    (fun k largs IHlargs rargm => 
    rargs ← rargm !! k;
    m ← IHlargs (delete k rargm);
    extend_match_of_abstract_tensor_args lbound rbound m largs rargs
    ) (fun rargm => if map_is_empty rargm then Some ∅ else None)
    (collate (M:=Pmap _) ((λ '(f, low, up), (encode f, (low, up))) <$> labs))
    (collate (M:=Pmap _) ((λ '(f, low, up), (encode f, (low, up))) <$> rabs)).


Definition match_tensorlist_fast (tl tl' : tensorlist) : option (gmap Idx Idx) :=
  let lbound := list_to_set (C:=Pset) (strings.string_to_pos <$> tl.(tl_sums).*2) in 
  let rbound := list_to_set (C:=Pset) (strings.string_to_pos <$> tl'.(tl_sums).*2) in 
  (λ m, Pmap_to_gmap m) <$> match_tensorlist_fast_aux lbound rbound 
    tl.(tl_abstracts) tl'.(tl_abstracts).

#[global]
Instance string_to_pos_inj : Inj eq eq strings.string_to_pos.
Proof.
  intros ? ? Heq%(f_equal strings.pos_to_string).
  now rewrite 2 strings.pos_to_string_string_to_pos in Heq.
Qed.

Lemma gmap_to_Pmap_to_gmap (m : gmap string string) : 
  Pmap_to_gmap (gmap_to_Pmap m) = m.
Proof.
  (* rewrite map_to_list_to_map. *)
  apply map_eq.
  intros i.
  destruct (m !! i) as [mi|] eqn:Hmi.
  - apply elem_of_list_to_map.
    + rewrite fsts_prod_map.
      rewrite map_to_list_to_map.
      2: {
        rewrite fsts_prod_map.
        apply NoDup_fmap_2; [apply _|].
        apply NoDup_fst_map_to_list.
      }
      rewrite fsts_prod_map.
      rewrite <- list_fmap_compose.
      rewrite (list_fmap_ext _ id) by 
        now intros; apply strings.pos_to_string_string_to_pos.
      rewrite list_fmap_id.
      apply NoDup_fst_map_to_list.
    + rewrite elem_of_list_fmap.
      exists (strings.string_to_pos i, mi).
      cbn.
      rewrite strings.pos_to_string_string_to_pos.
      split; [easy|].
      rewrite elem_of_map_to_list.
      apply lookup_kmap_Some; [apply _|].
      eauto.
  - apply not_elem_of_list_to_map.
    rewrite fsts_prod_map.
    rewrite elem_of_list_fmap.
    intros (y & -> & Hy).
    revert Hy.
    rewrite <- (elem_of_list_to_set (C:=Pset)).
    rewrite <- dom_alt.
    intros Hy.
    apply dom_kmap in Hy; [|apply _].
    revert Hy.
    rewrite elem_of_map.
    intros (x & -> & Hx).
    rewrite strings.pos_to_string_string_to_pos in Hmi.
    now apply not_elem_of_dom in Hmi.
Qed.

Lemma gset_to_Pset_to_gset (s : gset string) : 
  Pset_to_gset (gset_to_Pset s) = s.
Proof.
  apply set_eq.
  intros x.
  etransitivity; [apply elem_of_map|].
  split.
  - intros (? & -> & (? & -> & ?)%elem_of_map).
    now rewrite strings.pos_to_string_string_to_pos.
  - intros Hx.
    eexists.
    split; [|apply elem_of_map; eauto].
    now rewrite strings.pos_to_string_string_to_pos.
Qed.



Fixpoint tl_times_aux_base_r_alt (avoid : gset Idx)
  (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) :
  tensorlist
  (* list (Ty * Idx) * list (Idx * list Idx * list Idx) *) := 
  match rsums with 
  | [] => mk_tl [] (labs ++ rabs)
  | (ty, var) :: rsums' => 
      let var' := fresh_var var avoid in 
      (* let rsums'' := relabel_one_in_sums var var' rsums' in  *)
      let rabs' := relabel_one_in_abs var var' rabs in
      tl_cons_sum ty var' 
        (tl_times_aux_base_r_alt (avoid ∪ ({[var']} ∖ {[var]})) labs 
        rsums' rabs')
    
  end.


Fixpoint tl_times_aux_l_alt (avoid : gset Idx)
  (lsums : list (Ty * Idx)) (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) :
  tensorlist
  (* list (nat * Idx) * list (Idx * list Idx * list Idx) *) :=
  match lsums with 
  | [] => 
    tl_times_aux_base_r_alt avoid labs rsums rabs
  | (ty, var) :: lsums' => 
    
      let var' := fresh_var var avoid in 
      (* let rsums'' := relabel_one_in_sums var var' rsums' in  *)
      let labs' := relabel_one_in_abs var var' labs in
      tl_cons_sum ty var' (tl_times_aux_l_alt (avoid ∪ ({[var']} ∖ {[var]})) 
        lsums' labs' rsums rabs
        )
  end.

Definition tl_times_aux_alt (avoid : gset Idx)
  (lsums : list (Ty * Idx)) (labs : list (Idx * list Idx * list Idx))
  (rsums : list (Ty * Idx)) (rabs : list (Idx * list Idx * list Idx)) :
  tensorlist :=
  tl_times_aux_l_alt avoid lsums labs rsums rabs.

Definition tl_times_alt (l r : tensorlist) : tensorlist :=
  let avoid := (tl_varset l) ∪ (tl_varset r) in
  tl_times_aux_alt avoid (l.(tl_sums)) (l.(tl_abstracts))
    (r.(tl_sums)) (r.(tl_abstracts)).

Fixpoint tensorlist_of_tensorexpr_alt (te : tensorexpr) : tensorlist :=
  match te with 
  | tone => tlone
  | tabstract idx lower upper => mk_tl [] [(idx, lower, upper)]
  | tproduct l r => tl_times_alt (tensorlist_of_tensorexpr_alt l) (tensorlist_of_tensorexpr_alt r)
  | tsum var ty smd => 
    tl_cons_sum ty var (tensorlist_of_tensorexpr_alt smd)
  end.





Fixpoint rindex `{EqDecision A} (l : list A) (a : A) : option nat :=
  match l with 
  | [] => None
  | a' :: l => 
    match rindex l a with
    | Some i => Some (S i)
    | None => if decide (a' = a) then Some 0 else None
    end
  end.

Lemma rindex_is_Some `{EqDecision A} (l : list A) a : 
  is_Some (rindex l a) <-> a ∈ l.
Proof.
  induction l; [cbn; rewrite elem_of_nil; split; now intros []|].
  cbn.
  rewrite elem_of_cons.
  case_decide as Ha'.
  - destruct (rindex l a); split; auto.
  - destruct IHl. 
    destruct (rindex l a); split; [now auto..|].
    intros [|]; [congruence|auto].
Qed.

Lemma lookup_rindex `{EqDecision A} l (a : A) i : 
  rindex l a = Some i -> 
  l !! i = Some a.
Proof.
  revert i; induction l as [|a' l IHl]; intros i.
  - easy.
  - cbn.
    destruct (rindex l a) as [i'|].
    + intros [= <-].
      cbn.
      auto.
    + case_decide as Ha'; [|easy].
      subst.
      now intros [= <-].
Qed.

Lemma rindex_Some `{EqDecision A} l (a : A) i : 
  rindex l a = Some i <-> l !! i = Some a /\ 
    forall j, i < j -> l !! j ≠ Some a.
Proof.
  revert i; 
  induction l as [|a' l IHl]; intros i; [easy|].
  cbn.
  destruct (rindex l a) as [i'|] eqn:Hridx.
  - specialize (IHl i').
    pose proof (proj1 IHl eq_refl) as [Hli' Hi'max].
    split.
    + intros [= <-].
      split; [easy|].
      intros []; [easy|].
      intros ?.
      cbn.
      apply Hi'max; lia.
    + destruct i as [|i].
      * intros [_ Hf].
        specialize (Hf (S i') ltac:(lia)).
        cbn in Hf.
        exfalso; now apply Hf.
      * cbn.
        intros [Hli Himax].
        do 2 f_equal.
        enough (~ (i < i' \/ i' < i)) by lia.
        intros [Hii' | Hi'i].
        --specialize (Himax (S i') ltac:(lia)).
          easy.
        --specialize (Hi'max i Hi'i).
          easy.
  - clear IHl.
    assert (Hnin : a ∉ l). 1:{
      rewrite <- rindex_is_Some, Hridx.
      auto.
    }
    case_decide as Ha'.
    + destruct i as [|i].
      * subst. 
        split; [|easy].
        split; [easy|].
        intros [|j] ?; [easy|].
        cbn.
        rewrite elem_of_list_lookup in Hnin.
        eauto. 
      * split; [now intros [=]|].
        cbn.
        now intros [?%elem_of_list_lookup_2 _].
    + split; [easy|].
      intros [[]%elem_of_list_lookup_2%elem_of_cons _];
      exfalso; auto.
Qed.



Definition relabel_tldb_abs {A B} (f : A -> B) 
  abs : list (Idx * list B * list B) :=
  fmap (M:=list)
      (λ '(abs, low, up), (abs, f <$> low, f <$> up)) abs.

Record tensorlistdebruijn := mk_tldb {
  tldb_sums : list Ty;
  tldb_abstracts : list (Idx * list (nat + Idx) * list (nat + Idx))
}.

Definition relabel_tldb f tldb := 
  mk_tldb tldb.(tldb_sums) (relabel_tldb_abs f tldb.(tldb_abstracts)).

Definition sum_elim {A B C} (f : A -> C) (g : B -> C) : A + B -> C :=
  fun ab => match ab with | inl a => f a | inr b => g b end.

Definition tldb_to_tl (vars : list Idx) (tldb : tensorlistdebruijn) : tensorlist :=
  mk_tl (zip tldb.(tldb_sums) vars)
    (relabel_tldb_abs (sum_elim (vars !!!.) id) tldb.(tldb_abstracts)).


Definition tl_to_tldb (tl : tensorlist) : tensorlistdebruijn :=
  {|
    tldb_sums := tl.(tl_sums).*1;
    tldb_abstracts :=
      let vars := tl.(tl_sums).*2 in  
      relabel_tldb_abs (λ v, from_option inl (inr v) 
        (rindex vars v)) tl.(tl_abstracts)
  |}.

Lemma tl_to_tldb_to_tl tl : 
  tldb_to_tl (tl.(tl_sums).*2) (tl_to_tldb tl) = tl.
Proof.
  destruct tl as [sums abs].
  cbn.
  unfold tldb_to_tl, tl_to_tldb.
  cbn.
  rewrite zip_fst_snd.
  f_equal.
  rewrite <- list_fmap_compose.
  erewrite list_fmap_ext; [apply list_fmap_id|].
  intros _ [[f low] up] _.
  cbn.
  rewrite <- 2 list_fmap_compose.
  rewrite (list_fmap_ext _ id low), (list_fmap_ext _ id up), 2 list_fmap_id; [easy|..].
  - intros _ x _.
    cbn.
    destruct (rindex _ _) as [i|] eqn:Hridx; [|easy].
    cbn.
    apply list_lookup_total_correct.
    now apply lookup_rindex.
  - intros _ x _.
    cbn.
    destruct (rindex _ _) as [i|] eqn:Hridx; [|easy].
    cbn.
    apply list_lookup_total_correct.
    now apply lookup_rindex.
Qed.

Definition tldb_times tl tl' :=
  {|
    tldb_sums := tl.(tldb_sums) ++ tl'.(tldb_sums);
    tldb_abstracts :=
      let l := length tl.(tldb_sums) in 
      tl.(tldb_abstracts) ++ 
      relabel_tldb_abs (sum_map (Nat.add l) id)
         tl'.(tldb_abstracts)
  |}.


Fixpoint te_to_tldb (te : tensorexpr) : tensorlistdebruijn :=
  match te with 
  | tone => mk_tldb [] []
  | tabstract f low up => mk_tldb [] [(f, inr <$> low, inr <$> up)]
  | tproduct tel ter => tldb_times (te_to_tldb tel) (te_to_tldb ter)
  | tsum var ty smd =>
    let tl := (te_to_tldb smd) in 
    mk_tldb (ty :: tl.(tldb_sums)) $
    relabel_tldb_abs (sum_elim (inl ∘ S) 
      (fun v => if decide (v = var) then inl O else inr v))
      tl.(tldb_abstracts)
  end.


Definition tldb_free_varset tldb : gset Idx :=
  list_to_set (flat_map 
    (λ '(_, low, up), omap (sum_elim (λ _, None) Some) (low ++ up))
    tldb.(tldb_abstracts)).

Definition tensorlist_of_tensorexpr_alt_db (te : tensorexpr) : tensorlist :=
  let tldb := te_to_tldb te in 
  tldb_to_tl (fresh_list (length tldb.(tldb_sums)) 
  (tldb_free_varset tldb)) tldb.


Require TensorExprSemantics.

Section tldb_semantics.


Context `{SR : SemiRing R rO rI radd rmul req}.

Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70). 
Infix "+" := radd. 
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.


Context (V : Ty -> Type).
Context `{Vsum : forall n, Summable (V n)}.

Import TensorExprSemantics.

Definition tldb_abstract_semantics (abs : @abscontext R V)
  (vars : varcontext V) (bound : list (Vval V)) 
  (absidx : Idx) (lower upper : list (nat + Idx)) :=
  default rO (args ← join_list 
    (sum_elim (bound !!.) (vars !!.) <$> (lower ++ upper));
      fval ← abs !! absidx;
      Vapplys V fval args).

Fixpoint tldb_total_semantics_aux (abs : @abscontext R V)
  (vars : varcontext V) (bound : list (Vval V)) 
  (sums : list Ty) 
  (abstracts : list (Idx * list (nat + Idx) * list (nat + Idx))) : R :=
  match sums with 
  | [] => fold_right (fun '(f, low, up) => 
    rmul (tldb_abstract_semantics abs vars bound f low up)) rI abstracts
  | ty :: sums => 
    sum_of (fun x : V ty => 
      tldb_total_semantics_aux abs vars (bound ++ [mk_Vval V x]) sums abstracts)
  end.

Definition tldb_total_semantics abs vars tldb :=
  tldb_total_semantics_aux abs vars [] 
    tldb.(tldb_sums) tldb.(tldb_abstracts).

(* Lemma tldb_to_tl_correct_base abs vars varnames tldb : 
  Forall_fresh (dom vars) varnames ->
  tl_total_semantics V abs vars (tldb_to_tl varnames tldb) =
  tldb_total_semantics abs vars tldb. *)

Lemma total_semantics_tproducts abs vars tes : 
  total_semantics V abs vars (tproducts tes) ==
  foldr (λ te acc, total_semantics V abs vars te * acc) 1 tes.
Proof.
  induction tes; [reflexivity|]; cbn; ring [IHtes].
Qed.

(* FIXME: Move *)
Lemma foldr_ext_strong {A B} {RA : relation A} 
  `{!Reflexive RA} `{!Transitive RA}
  (f g : B -> A -> A) x l : 
  (forall b, Proper (RA ==> RA) (f b)) ->
  (forall b a, b ∈ l -> RA (f b a) (g b a)) -> 
  RA (foldr f x l) (foldr g x l).
Proof.
  intros Hf Hfg.
  induction l; [done|].
  cbn.
  erewrite Hf by now apply IHl; intros; apply Hfg; constructor.
  apply Hfg.
  constructor.
Qed.


(* FIXME: Move *)
Lemma elem_of_flat_map `(f : A -> list B) l b : 
  b ∈ flat_map f l <-> exists a, a ∈ l /\ b ∈ f a.
Proof.
  setoid_rewrite elem_of_list_In.
  now rewrite in_flat_map.
Qed.

Definition wf_tldb tldb : Prop :=
  forall n, inl n ∈ flat_map 
    (λ '(_, low, up), (low ++ up))
    tldb.(tldb_abstracts) -> n < length tldb.(tldb_sums).

Ltac tspecialize_with C tac :=
  match type of C with
  | forall _ : ?A, _ => 
    let H := fresh in 
    assert (H : A); [
      tac | specialize (C H); clear H
    ]
  end.

Tactic Notation "tspecialize" uconstr(C) "by" tactic3(tac) :=
  tspecialize_with C ltac:(solve [tac]).

Tactic Notation "tspecialize" uconstr(C) :=
  tspecialize_with C ltac:(idtac).

Lemma tldb_to_tl_correct_aux abs vars varnames 
  named_bound sums abstracts : 
  length sums <= length varnames ->
  tldb_free_varset (mk_tldb sums abstracts) ⊆ dom vars ->
  Forall_fresh (dom vars) (named_bound.*1 ++ varnames) ->
  (forall n, inl n ∈ flat_map 
    (λ '(_, low, up), (low ++ up))
    abstracts -> n < length named_bound + length sums) ->
  tl_total_semantics V abs 
    (list_to_map (reverse named_bound) ∪ vars :> gmap _ _) 
    (mk_tl 
      (zip sums varnames)
      (relabel_tldb_abs (sum_elim (named_bound.*1 ++ varnames !!!.) id)
        abstracts)
      ) ==
  tldb_total_semantics_aux abs vars named_bound.*2 sums abstracts.
Proof.
  cbn.
  revert varnames named_bound;
  induction sums; intros varnames named_bound Hlen Hdom Hfresh Hwf.
  - cbn.
    rewrite total_semantics_tproducts.
    unfold relabel_tldb_abs.
    rewrite 2 foldr_fmap.
    apply foldr_ext_strong; [solve_proper|].
    intros [[f low] up] acc Hf.
    f_equiv.
    cbn.
    unfold tldb_abstract_semantics, abstract_semantics.
    f_equiv.
    f_equal.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ v Hv%elem_of_list_lookup_2.
    cbn.
    destruct v as [n | v]; cbn.
    + specialize (Hwf n).
      cbn in Hwf.
      rewrite elem_of_flat_map in Hwf.
      tspecialize Hwf by now exists (f, low, up); eauto.
      rewrite Nat.add_0_r in Hwf.
      rewrite lookup_total_app_l by now simpl_list.
      unfold varcontext.
      rewrite lookup_union.
      rewrite list_lookup_total_alt.
      rewrite 2 list_lookup_fmap.
      apply lookup_lt_is_Some_2 in Hwf as Hsome.
      destruct Hsome as [[name val] Hn].
      rewrite Hn.
      cbn.
      apply Forall_fresh_NoDup in Hfresh as HNoDup.
      apply elem_of_list_lookup_2 in Hn as Hnameval.
      rewrite elem_of_list_to_map in Hnameval by 
        now apply NoDup_app in HNoDup as [? _].
      erewrite list_to_map_proper; [|
        rewrite reverse_Permutation; 
        now apply NoDup_app in HNoDup as [? _]|apply reverse_Permutation].
      rewrite Hnameval.
      destruct (vars !! name); reflexivity.
    + unfold varcontext. 
      apply lookup_union_r.
      apply not_elem_of_dom.
      rewrite dom_list_to_map_L, elem_of_list_to_set.
      rewrite reverse_Permutation.
      enough (Hen : v ∉ named_bound.*1 ++ varnames) by
        now apply not_elem_of_app in Hen.
      intros Hen%(Forall_fresh_elem_of _ _ _ Hfresh).
      apply Hen.
      apply Hdom.
      rewrite elem_of_list_to_set, elem_of_flat_map.
      exists (f, low, up); split; [easy|].
      rewrite elem_of_list_omap.
      eauto.
  - destruct varnames as [|name varnames]; [easy|]. 
    cbn.
    apply sum_of_ext; intros x.
    specialize (IHsums varnames (named_bound ++ [(name, mk_Vval V x)])).
    tspecialize IHsums by now cbn in *; lia.
    specialize (IHsums Hdom).
    tspecialize IHsums by now rewrite fmap_app, <- app_assoc.
    tspecialize IHsums by now
      intros n Hen%Hwf; revert Hen; simpl_list; cbn; lia.
    rewrite 2 fmap_app in IHsums.
    cbn in IHsums.
    rewrite <- IHsums.
    rewrite reverse_snoc, list_to_map_cons.
    rewrite <- app_assoc.
    cbn.
    rewrite <- insert_union_l.
    reflexivity.
Qed.


Lemma tldb_to_tl_correct_aux_alt abs vars varnames 
  named_bound sums abstracts : 
  length sums <= length varnames ->
  (* tldb_free_varset (mk_tldb sums abstracts) ⊆ dom vars -> *)
  NoDup (named_bound.*1 ++ varnames) ->
  list_to_set (named_bound.*1 ++ varnames) ## tldb_free_varset (mk_tldb sums abstracts) ->
  (forall n, inl n ∈ flat_map 
    (λ '(_, low, up), (low ++ up))
    abstracts -> n < length named_bound + length sums) ->
  tl_total_semantics V abs 
    (list_to_map (reverse named_bound) ∪ vars :> gmap _ _) 
    (mk_tl 
      (zip sums varnames)
      (relabel_tldb_abs (sum_elim (named_bound.*1 ++ varnames !!!.) id)
        abstracts)
      ) ==
  tldb_total_semantics_aux abs vars named_bound.*2 sums abstracts.
Proof.
  cbn.
  revert varnames named_bound;
  induction sums; intros varnames named_bound Hlen HNoDup Hdisj Hwf.
  - cbn.
    rewrite total_semantics_tproducts.
    unfold relabel_tldb_abs.
    rewrite 2 foldr_fmap.
    apply foldr_ext_strong; [solve_proper|].
    intros [[f low] up] acc Hf.
    f_equiv.
    cbn.
    unfold tldb_abstract_semantics, abstract_semantics.
    f_equiv.
    f_equal.
    f_equal.
    rewrite <- fmap_app, <- list_fmap_compose.
    apply list_fmap_ext.
    intros _ v Hv%elem_of_list_lookup_2.
    cbn.
    destruct v as [n | v]; cbn.
    + specialize (Hwf n).
      cbn in Hwf.
      rewrite elem_of_flat_map in Hwf.
      tspecialize Hwf by now exists (f, low, up); eauto.
      rewrite Nat.add_0_r in Hwf.
      rewrite lookup_total_app_l by now simpl_list.
      unfold varcontext.
      rewrite lookup_union.
      rewrite list_lookup_total_alt.
      rewrite 2 list_lookup_fmap.
      apply lookup_lt_is_Some_2 in Hwf as Hsome.
      destruct Hsome as [[name val] Hn].
      rewrite Hn.
      cbn.
      apply elem_of_list_lookup_2 in Hn as Hnameval.
      rewrite elem_of_list_to_map in Hnameval by 
        now apply NoDup_app in HNoDup as [? _].
      erewrite list_to_map_proper; [|
        rewrite reverse_Permutation; 
        now apply NoDup_app in HNoDup as [? _]|apply reverse_Permutation].
      rewrite Hnameval.
      destruct (vars !! name); reflexivity.
    + unfold varcontext. 
      apply lookup_union_r.
      apply not_elem_of_dom.
      rewrite dom_list_to_map_L, elem_of_list_to_set.
      rewrite reverse_Permutation.
      enough (Hen : v ∉ named_bound.*1 ++ varnames) by
        now apply not_elem_of_app in Hen.
      intros Hnin.
      specialize (Hdisj v).
      tspecialize Hdisj by now rewrite elem_of_list_to_set.
      apply Hdisj.
      rewrite elem_of_list_to_set, elem_of_flat_map.
      exists (f, low, up); split; [easy|].
      rewrite elem_of_list_omap.
      eauto.
  - destruct varnames as [|name varnames]; [easy|]. 
    cbn.
    apply sum_of_ext; intros x.
    specialize (IHsums varnames (named_bound ++ [(name, mk_Vval V x)])).
    tspecialize IHsums by now cbn in *; lia.
    rewrite fmap_app, <- app_assoc in IHsums.
    specialize (IHsums HNoDup Hdisj).
    tspecialize IHsums by now
      intros n Hen%Hwf; revert Hen; simpl_list; cbn; lia.
    cbn in IHsums.
    revert IHsums. 
    rewrite reverse_snoc, list_to_map_cons.
    cbn.
    rewrite <- insert_union_l.
    intros ->.
    rewrite fmap_app.
    reflexivity.
Qed.

Lemma fst_zip_gen {A B} (l : list A) (k : list B) : 
  (zip l k).*1 = take (length k) l.
Proof.
  revert k;
  induction l; intros k.
  - cbn; now rewrite take_nil.
  - destruct k; [easy|].
    cbn.
    f_equal.
    apply IHl.
Qed.

Lemma snd_zip_gen {A B} (l : list A) (k : list B) : 
  (zip l k).*2 = take (length l) k.
Proof.
  revert k;
  induction l; intros k.
  - reflexivity.
  - destruct k; [easy|].
    cbn.
    f_equal.
    apply IHl.
Qed.

Lemma tldb_free_varset_correct_gen varnames tldb : 
  length tldb.(tldb_sums) = length varnames ->
  wf_tldb tldb ->
  tldb_free_varset tldb ∖ 
    list_to_set varnames = 
  tl_free_varset (tldb_to_tl varnames tldb).
Proof.
  intros Hlen Hwf.
  destruct tldb as [sums abstracts].
  unfold tldb_to_tl, tl_free_varset.
  cbn.
  rewrite snd_zip by now apply eq_reflexivity.
  apply set_eq.
  intros v.
  set_unfold.
  do 4 setoid_rewrite exists_pair.
  do 2 setoid_rewrite pair_eq.
  setoid_rewrite elem_of_list_omap.
  split.
  - intros [(f & low & up & ([_ | v'] & Hpv & [= ->]) & Hf) Hnin].
    split; [|easy]. 
    eexists.
    split; cycle 1.
    + exists f, (sum_elim (λ i : nat, varnames !!! i) id <$> low), 
        (sum_elim (λ i : nat, varnames !!! i) id <$> up).
      split; [rewrite <- fmap_app; reflexivity|].
      eauto 10.
    + rewrite elem_of_list_fmap.
      now exists (inr v).
  - intros [(? & Hvm & _ & _ & _ & -> & f & low & up & 
      [[-> ->] ->] & Helem) Hnin].
    split; [|easy]. 
    exists f, low, up.
    split; [|easy].
    exists (inr v).
    split; [|easy].
    rewrite <- fmap_app, elem_of_list_fmap in Hvm.
    destruct Hvm as ([p | v'] & -> & Hin).
    + specialize (Hwf p).
      tspecialize Hwf by now 
        cbn; rewrite elem_of_flat_map; exists (f, low, up); auto.
      cbn in Hwf.
      cbn in *.
      rewrite Hlen in Hwf.
      now apply elem_of_list_lookup_total_2 in Hwf.
    + easy.
Qed.

Lemma total_semantics_trivial abs vars te v : 
   v ∉ dom vars -> v ∈ te_free_varset te ->
  total_semantics V abs vars te == 0.
Proof.
  revert vars;
  induction te; intros vars Hvdom Hvfree.
  - contradict Hvfree; easy.
  - cbn.
    unfold abstract_semantics.
    apply eq_reflexivity.
    transitivity (default 0 None); [|easy].
    f_equal.
    rewrite bind_None; left.
    rewrite eq_None_not_Some.
    rewrite join_list_is_Some.
    intros Hen; apply Hen; clear Hen.
    cbn in Hvfree.
    rewrite elem_of_list_to_set in Hvfree.
    unfold varcontext in Hvdom.
    rewrite not_elem_of_dom in Hvdom.
    rewrite <- Hvdom.
    now apply (elem_of_list_fmap_1 (vars !!.) _ v).
  - cbn in *.
    rewrite elem_of_union in Hvfree.
    destruct Hvfree.
    + rewrite IHte1 by done; ring.
    + rewrite IHte2 by done; ring.
  - cbn.
    erewrite sum_of_ext; [refine sum_of_0|].
    intros x.
    cbn in *.
    unfold varcontext in *.
    apply IHte; set_solver +Hvfree Hvdom.
Qed.

Lemma tldb_total_semantics_trivial abs vars tldb v : 
  v ∉ dom vars -> v ∈ tldb_free_varset tldb ->
  tldb_total_semantics abs vars tldb == 0.
Proof.
  destruct tldb as [sums abstracts].
  cbn.
  intros Hvdom Hvfree.
  (* rewrite <- difference_empty_L, <- list_to_set_nil in Hvfree. *)
  generalize (@nil (Vval V)) as bound.
  (* generalize (@nil Idx) as bound. *)

  induction sums; intros bound.
  - cbn.
    rewrite elem_of_list_to_set, elem_of_flat_map in Hvfree.
    destruct Hvfree as (a & Ha & Hv).
    revert Hv.
    induction Ha as [[[f low] up]|[[f low] up] [[f' low'] up'] rest IHabs].
    + cbn.
      intros ([_|_] & Hv & [= ->])%elem_of_list_omap.
      etransitivity; [|apply rmul_0_l].
      f_equiv; [|reflexivity].
      unfold tldb_abstract_semantics.
      transitivity (default 0 None); [|easy].
      apply eq_reflexivity.
      f_equal.
      rewrite bind_None; left.
      rewrite eq_None_not_Some.
      rewrite join_list_is_Some.
      intros Hen; apply Hen; clear Hen.
      unfold varcontext in Hvdom.
      rewrite not_elem_of_dom in Hvdom.
      rewrite elem_of_list_fmap.
      exists (inr v).
      cbn.
      easy.
    + intros Hz%IHHa.
      cbn.
      rewrite Hz.
      ring.
  - cbn.
    erewrite sum_of_ext; [refine sum_of_0|].
    intros x.
    apply IHsums.
Qed.

Lemma wf_tldb_alt tldb : 
  wf_tldb tldb <->
  set_Forall
    (sum_elim (λ n, n < length (tldb_sums tldb)) (λ _ : Idx, True))
    (list_to_set
       (flat_map (λ '(y, up), let '(_, low) := y in low ++ up)
          (tldb_abstracts tldb)) :> gset (nat + Idx)).
Proof.
  unfold wf_tldb, set_Forall.
  setoid_rewrite elem_of_list_to_set.
  split.
  - intros Hl []; [|easy].
    apply Hl.
  - intros Hlr n.
    apply Hlr.
Qed.

#[global] Instance wf_tldb_dec tldb : Decision (wf_tldb tldb). 
  refine (cast_if (set_Forall_dec 
    (sum_elim (λ n, n < length tldb.(tldb_sums)) (λ _ : Idx, True))
    (list_to_set (flat_map 
    (λ '(_, low, up), (low ++ up))
    tldb.(tldb_abstracts)) :> gset (nat + Idx)))).
  - intros []; cbn; apply _.
  - abstract (by rewrite wf_tldb_alt). 
  - abstract (by rewrite wf_tldb_alt).
Defined. 

(* Lemma not_wf_tldb_trivial_semantics tldb : 
  ~ wf_tldb tldb ->  *)

Lemma tldb_to_tl_correct abs vars varnames tldb : 
  length tldb.(tldb_sums) = length varnames ->
  Forall_fresh (tldb_free_varset tldb) varnames ->
  wf_tldb tldb ->
  tl_total_semantics V abs vars (tldb_to_tl varnames tldb) ==
  tldb_total_semantics abs vars tldb.
Proof.
  intros Hlen [HNoDup Hdisj]%Forall_fresh_alt Hwf.
  destruct_decide (decide (tldb_free_varset tldb ⊆ dom vars))
    as Hsub.
  - destruct tldb as [sums abstracts].
    cbn in *.
    specialize (tldb_to_tl_correct_aux_alt abs vars varnames [] sums abstracts)
      as Hrw.
    rewrite <- Hrw.
    + cbn.
      rewrite map_empty_union.
      reflexivity.
    + now rewrite Hlen.
    + apply HNoDup.
    + now intros ? ?%elem_of_list_to_set%Hdisj.
    + apply Hwf.
  - change (~ (set_Forall (.∈ dom vars) (tldb_free_varset tldb))) in Hsub.
    apply not_set_Forall_Exists in Hsub; [|apply _].
    destruct Hsub as (v & Hv & Hvnimpl).
    cbn in Hvnimpl.
    unfold tl_total_semantics.
    rewrite total_semantics_trivial; eauto.
    2: {
      rewrite <- tl_free_varset_correct.
      rewrite <- tldb_free_varset_correct_gen by easy.
      apply elem_of_difference.
      split; [easy|].
      rewrite elem_of_list_to_set.
      now intros ?%Hdisj.
    }
    symmetry.
    now apply (tldb_total_semantics_trivial _ _ _ v).
Qed.

Lemma tl_to_tldb_wf tl : 
  wf_tldb (tl_to_tldb tl).
Proof.
  intros n.
  rewrite elem_of_flat_map.
  cbn.
  rewrite 2 exists_pair.
  intros (f & low' & up' & ([[f' low] up] & [= <- -> ->] & Hf)%elem_of_list_fmap & Hin).
  rewrite <- fmap_app, elem_of_list_fmap in Hin.
  destruct Hin as (y & Heq & _).
  destruct (rindex _ _) eqn:Hridx; [|easy].
  cbn in Heq.
  revert Heq.
  intros [= <-].
  apply rindex_Some in Hridx as [Hlook%lookup_lt_Some _].
  now rewrite !length_fmap in *.
Qed.

Lemma tldb_times_semantics vars abs tldb tldb' :
  wf_tldb tldb -> wf_tldb tldb' ->
  tldb_total_semantics vars abs (tldb_times tldb tldb') ==
  tldb_total_semantics vars abs tldb * tldb_total_semantics vars abs tldb'.
Proof.
  destruct tldb as [sums abstracts], tldb' as [sums' abstracts'].
  unfold wf_tldb.
  cbn.
  change (length sums) with (length (@nil (Vval V)) + length sums)%nat.
  intros Hwf Hwf'.
  revert Hwf.
  generalize (@nil (Vval V)) at 1 2 3 4 5 as bound.
  induction sums as [|ty sums IHsums]; intros bound Hwf.
  - cbn.
    replace bound with (bound ++ []) at 1 by now simpl_list.
    revert Hwf'.
    change (length sums') with (length (@nil (Vval V)) + length sums')%nat.
    generalize (@nil (Vval V)) as bound'.
    induction sums' as [|ty' sums' IHsums']; intros bound' Hwf'.
    + cbn.
      rewrite foldr_app, foldr_fmap.
      rewrite Nat.add_0_r in Hwf.
      induction abstracts as [|[[f low] up] abstracts IHabs].
      * cbn.
        rewrite rmul_1_l.
        apply foldr_ext_strong; [intros [[]]; solve_proper|].
        intros [[f low] up] acc Hf.
        f_equiv.
        rewrite Nat.add_0_r.
        unfold tldb_abstract_semantics.
        f_equiv.
        f_equal.
        f_equal.
        rewrite <- fmap_app, <- list_fmap_compose.
        apply list_fmap_ext.
        intros _ [p | v] _; cbn; [|easy].
        rewrite lookup_app_r by lia.
        f_equal; lia.
      * cbn.
        rewrite <- rmul_assoc.
        f_equiv.
        2: {
          apply IHabs.
          intros n Hn. 
          apply Hwf.
          cbn; apply elem_of_app, or_intror, Hn.
        }
        unfold tldb_abstract_semantics.
        f_equiv.
        f_equal.
        f_equal.
        apply list_fmap_ext.
        intros _ [p | v] Hin%elem_of_list_lookup_2; cbn; [|easy].
        apply lookup_app_l.
        apply Hwf.
        set_solver +Hin.
    + cbn.
      rewrite sum_of_distr_r.
      apply sum_of_ext; intros x.
      rewrite <- app_assoc.
      apply IHsums'. 
      intros ? Hen%Hwf'; revert Hen.
      simpl_list; cbn; lia.
  - cbn.
    rewrite sum_of_distr_l.
    apply sum_of_ext; intros x.
    rewrite <- IHsums by now 
      intros ? Hen%Hwf; revert Hen;
      simpl_list; cbn; lia.
    rewrite length_app, <- Nat.add_assoc.
    reflexivity.
Qed.

Lemma tldb_times_wf tldb tldb' : 
  wf_tldb tldb -> wf_tldb tldb' -> 
  wf_tldb (tldb_times tldb tldb').
Proof.
  destruct tldb as [sums abstracts], tldb' as [sums' abstracts'].
  unfold wf_tldb.
  cbn.
  intros Hwf Hwf'.
  rewrite length_app, flat_map_app.
  intros n [?%Hwf | Hr]%elem_of_app; [lia|].
  specialize (Hwf' (n - length sums)).
  tspecialize Hwf'; [|lia].
  revert Hr.
  rewrite 2 elem_of_flat_map, 4 exists_pair.
  intros (f & low' & up' & ([[f' low] up] & [= <- -> ->] & Hf)%elem_of_list_fmap & Hin).
  exists f, low, up.
  split; [easy|].
  rewrite <- fmap_app, elem_of_list_fmap in Hin.
  destruct Hin as ([n' | _] & [= ->] & Hin).
  now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Lemma te_to_tldb_wf te : 
  wf_tldb (te_to_tldb te).
Proof.
  induction te.
  - easy.
  - hnf. cbn.
    set_solver +.
  - cbn.
    now apply tldb_times_wf.
  - cbn.
    hnf.
    cbn.
    intros [|n] Hn; [lia|].
    apply -> Nat.succ_lt_mono.
    apply IHte.
    revert Hn.
    rewrite 2 elem_of_flat_map, 4 exists_pair.
    intros (f & low' & up' & ([[f' low] up] & [= <- -> ->] & Hf)%elem_of_list_fmap & Hin).
    exists f, low, up.
    split; [easy|].
    rewrite <- fmap_app, elem_of_list_fmap in Hin.
    destruct Hin as ([n' | v] & [= Heq] & Hin).
    + now subst.
    + now case_decide.
Qed.

Lemma tldb_total_semantics_sum_alt_aux abs vars 
  bound bound' val name sums abstracts : 
  name ∉ tldb_free_varset (mk_tldb sums abstracts) ->
  tldb_total_semantics_aux abs vars (bound ++ val :: bound') sums abstracts ==
  tldb_total_semantics_aux abs (<[name := val]> vars) (bound ++ bound') sums
    (relabel_tldb_abs (sum_elim 
      (λ n, if decide (length bound <= n) then 
        (if decide (n = length bound) then 
          (inr name) else (inl (pred n)))
        else (inl n)) inr)
      abstracts).
Proof.
  cbn.
  intros Hfree.
  revert bound';
  induction sums; intros bound'.
  - cbn.
    induction abstracts as [|[[f low] up] abstracts IHabs]; [reflexivity|].
    cbn.
    rewrite IHabs by set_solver +Hfree.
    f_equiv; [|reflexivity].
    unfold tldb_abstract_semantics.
    rewrite <- fmap_app, <- list_fmap_compose.
    erewrite list_fmap_ext; [reflexivity|].
    intros _ [p | v] Hv%elem_of_list_lookup_2.
    + cbn.
      case_decide; [rewrite lookup_app_r by lia; case_decide|].
      * subst.
        rewrite Nat.sub_diag.
        cbn.
        unfold varcontext.
        now rewrite lookup_insert.
      * cbn.
        rewrite lookup_cons_ne_0 by lia.
        rewrite lookup_app_r; f_equal; lia.
      * rewrite lookup_app_l by lia.
        cbn.
        now rewrite lookup_app_l by lia.
    + cbn.
      unfold varcontext.
      rewrite lookup_insert_ne; [easy|].
      intros ->.
      apply Hfree.
      rewrite elem_of_list_to_set.
      cbn.
      apply elem_of_app; left.
      apply elem_of_list_omap.
      now exists (inr v).
  - cbn.
    apply sum_of_ext; intros x.
    rewrite <- 2 app_assoc, <- app_comm_cons.
    rewrite IHsums.
    reflexivity.
Qed.

Lemma tldb_total_semantics_sum_alt abs vars 
  ty name sums abstracts : 
  name ∉ tldb_free_varset (mk_tldb sums abstracts) ->
  tldb_total_semantics abs vars (mk_tldb (ty :: sums) abstracts) ==
  ∑ x : V ty, tldb_total_semantics abs 
    (<[name := mk_Vval V x]> vars) (mk_tldb sums 
      (relabel_tldb_abs (sum_elim (
        λ n, match n with | O => inr name | S n' => inl n' end) inr) 
        abstracts)).
Proof.
  intros Hfree.
  cbn.
  apply sum_of_ext; intros x.
  specialize (tldb_total_semantics_sum_alt_aux abs vars [] [] (mk_Vval V x) name).
  cbn.
  intros ->; [|easy].
  f_equiv.
  apply list_fmap_ext.
  intros _ [[f low] up] _.
  f_equal; [f_equal|];
  apply list_fmap_ext; intros _ [[] | v] _; cbn;
  repeat case_decide; reflexivity + lia.
Qed.

(* FIXME: Move *)
Lemma list_fmap_id' `(f : A -> A) (l : list A) : 
  (forall a, a ∈ l -> f a = a) ->
  f <$> l = l.
Proof.
  intros Hf.
  etransitivity; [|apply list_fmap_id].
  apply list_fmap_ext; intros _ ? ?%elem_of_list_lookup_2.
  now apply Hf.
Qed.

Lemma te_to_tldb_correct abs vars te : 
  tldb_total_semantics abs vars (te_to_tldb te) ==
  total_semantics V abs vars te.
Proof.
  revert vars;
  induction te; intros vars.
  - easy.
  - cbn.
    rewrite rmul_1_r.
    unfold tldb_abstract_semantics, abstract_semantics.
    rewrite <- fmap_app, <- list_fmap_compose, (unfold @compose).
    cbn.
    reflexivity.
  - cbn [te_to_tldb].
    rewrite tldb_times_semantics, IHte1, IHte2 by apply te_to_tldb_wf.
    cbn.
    reflexivity.
  - (* set (name := fresh_var "" (tldb_free_varset (te_to_tldb te))).
    pose proof (fresh_var_fresh "" (tldb_free_varset (te_to_tldb te))) as Hname. *)
    cbn [te_to_tldb].
    rewrite (tldb_total_semantics_sum_alt _ _ _ reg).
    + cbn -[tldb_total_semantics].
      apply sum_of_ext; intros x.
      rewrite <- IHte.
      f_equiv.
      destruct (te_to_tldb te) as [sums abstracts].
      f_equal.
      unfold relabel_tldb_abs.
      rewrite <- list_fmap_compose.
      etransitivity; [|apply list_fmap_id].
      apply list_fmap_ext; intros _ [[f low] up] _.
      cbn.
      rewrite <- 2 list_fmap_compose.
      eenough (Hen : _).
      rewrite 2 (list_fmap_id' _ _ (λ x _, Hen x)); [reflexivity|..].
      intros [[] | v]; cbn; [reflexivity..|].
      now case_decide; subst.
    + cbn.
      rewrite elem_of_list_to_set, elem_of_flat_map.
      intros ([[f low'] up'] & 
        ([[f' low] up] & [= <- -> ->] & Hf)%elem_of_list_fmap & Hin).
      rewrite <- fmap_app, elem_of_list_omap in Hin.
      destruct Hin as ([|v] & Hv & [= ->]).
      rewrite elem_of_list_fmap in Hv.
      destruct Hv as ([] & [= Heq] & ?).
      now case_decide; congruence.
Qed.


Lemma tensorlist_of_tensorexpr_alt_db_correct_apply abs vars te : 
  total_semantics V abs vars (tensorlist_of_tensorexpr_alt_db te) 
    == total_semantics V abs vars te.
Proof.
  fold (tl_total_semantics (SR:=SR) V abs vars 
    (tensorlist_of_tensorexpr_alt_db te)).
  unfold tensorlist_of_tensorexpr_alt_db.
  rewrite tldb_to_tl_correct.
  - apply te_to_tldb_correct.
  - now rewrite length_fresh_list.
  - apply Forall_fresh_list.
  - apply te_to_tldb_wf.
Qed. 

Lemma tensorlist_of_tensorexpr_alt_db_correct te : 
  teq (SR:=SR) V (tensorlist_of_tensorexpr_alt_db te) te.
Proof.
  intros abs vars.
  apply tensorlist_of_tensorexpr_alt_db_correct_apply.
Qed. 


Lemma tensorexpr_eqb_correct_apply_db abs vars te te' :
  tensorlist_eqb (tensorlist_of_tensorexpr_alt_db te)
    (tensorlist_of_tensorexpr_alt_db te') = true ->
  req (total_semantics V abs vars te) (total_semantics V abs vars te').
Proof.
  intros Heq%(tensorlist_eqb_correct (SR:=SR) V).
  rewrite <- tensorlist_of_tensorexpr_alt_db_correct_apply.
  rewrite (Heq abs).
  apply tensorlist_of_tensorexpr_alt_db_correct_apply.
Qed.



Fixpoint extend_map_of_abstract_pair_db
  (m : Pmap positive) (l r : list (positive + Idx)) : option (Pmap positive) :=
  match l, r with 
  | [], [] => Some m
  | inl hl :: l, inl hr :: r => 
    match m !! hl with 
    | Some mhl => 
      if bool_decide (mhl = hr) then 
        extend_map_of_abstract_pair_db m l r
      else None
    | None => extend_map_of_abstract_pair_db (<[hl := hr]> m) l r
    end
  | inr hl :: l, inr hr :: r => 
    if bool_decide (hl = hr) then 
      extend_map_of_abstract_pair_db m l r
    else None
  | _, _ => None
  end.

Fixpoint extend_match_of_abstract_tensors_db (m : Pmap positive)
  (labs rabs : list (Idx * list (positive + Idx) * list (positive + Idx))) 
    : option (Pmap positive) :=
  match labs with 
  | [] => match rabs with
    | [] => Some m
    | _ => None
    end
  | (fl, lowl, upl) :: labs => 
    list_first_omap (fun '((_, lowr, upr), rrest) => 
      m' ← extend_map_of_abstract_pair_db m lowl lowr;
         m'' ← extend_map_of_abstract_pair_db m' upl upr;
         extend_match_of_abstract_tensors_db m'' labs rrest)
      (list_select (fun '(fr, _, _) => fl = fr) rabs)
    (* head ('((_, lowr, upr), rrest) ← list_select (fun '(fr, _, _) => fl = fr) rabs;
      from_option (λ x, [x]) [] 
        (m' ← extend_map_of_abstract_pair lbound rbound m lowl lowr;
         m'' ← extend_map_of_abstract_pair lbound rbound m' upl upr;
         extend_match_of_abstract_tensors lbound rbound m'' labs rrest)
      ) *)
  end.

Definition match_tensorlistdebruijn 
  (tl tl' : tensorlistdebruijn) : option (Pmap positive) :=
  let labs := relabel_tldb_abs (sum_map Pos.of_succ_nat id) tl.(tldb_abstracts) in 
  let rabs := relabel_tldb_abs (sum_map Pos.of_succ_nat id) tl'.(tldb_abstracts) in
  extend_match_of_abstract_tensors_db ∅ labs rabs.

Local Open Scope lazy_bool_scope.

Definition tensorlistdebruijn_eqb
  (tl tl' : tensorlistdebruijn) : bool :=
  let '(mk_tldb sums abstracts) := tl in 
  let '(mk_tldb sums' abstracts') := tl' in 
  bool_decide (sums ≡ₚ sums') &&&
  let labs := relabel_tldb_abs (sum_map Pos.of_succ_nat id) abstracts in 
  let rabs := relabel_tldb_abs (sum_map Pos.of_succ_nat id) abstracts' in
  match extend_match_of_abstract_tensors_db ∅ labs rabs with
  | None => false
  | Some m => 
    let tym := list_to_map (M:=Pmap nat) 
      (imap (λ i v, (Pos.of_succ_nat i, v)) sums) in  
    let tym' := list_to_map (M:=Pmap nat) 
      (imap (λ i v, (Pos.of_succ_nat i, v)) sums') in 
    bool_decide (map_Forall (fun v v' => 
      tym !! v = 
      tym' !! v') m)
  end.

Lemma tensorlistdebruijn_eqb_correct_apply abs vars te te' : 
  tensorlistdebruijn_eqb (te_to_tldb te) (te_to_tldb te') = true ->
  req (total_semantics V abs vars te) (total_semantics V abs vars te').
Proof.
Admitted.

(* Lemma tl_to_tldb_correct_aux abs vars bound sums abstracts : 
  tldb_total_semantics abs vars (tl_to_tldb (mk_tl sums abstracts)) =
  tl_total_semantics V abs 
    (fold_right (uncurry insert) vars
      (imap )) (mk_tl sums abstracts.
Proof.
  destruct tl as [sums abstracts].
  cbn.
  

Lemma tl_to_tldb_correct abs vars tl : 
  tldb_total_semantics abs vars (tl_to_tldb tl) =
  tl_total_semantics V abs vars tl.
Proof.
  destruct tl as [sums abstracts].
  cbn. *)
  

(* Lemma tldb_to_tl_indep vars vars' tldb : 
  (forall x ∈ vars, x ∉ ) *)

End tldb_semantics.