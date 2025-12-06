(* Extra bits for stdpp *)
From stdpp Require Import decidable.

Lemma exists_dsig {A} {P Q : A -> Prop} `{forall x, Decision (P x)} : 
  (exists x : dsig P, Q (`x)) <-> exists x, P x /\ Q x.
Proof.
  split.
  - intros ((x & p) & q).
    cbn in *.
    apply bool_decide_unpack in p.
    eauto.
  - intros (x & p & q).
    now exists (dexist x p).
Qed.

Lemma exists_and_dsig {A} {P Q R : A -> Prop} 
  `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} : 
  (exists x : dsig (λ a, P a /\ Q a), R (`x)) <-> 
    exists (x : dsig P), Q (`x) /\ R (`x).
Proof.
  rewrite exists_dsig.
  setoid_rewrite <- (and_assoc _).
  now rewrite <- exists_dsig.
Qed.

From stdpp Require Import prelude.


Fixpoint join_list {A} (l : list (option A)) : option (list A) :=
  match l with 
  | [] => Some []
  | None :: _ => None
  | Some x :: ml => 
      l ← join_list ml;
      Some (x :: l)
  end.


Lemma join_list_Some {A} (l : list (option A)) l' : 
  join_list l = Some l' <-> l = Some <$> l'.
Proof.
  revert l'; induction l as [|a l IHl]; intros l'.
  - cbn.
    split; [now intros [= <-]|].
    now destruct l'.
  - cbn.
    destruct a; [|now destruct l'].
    rewrite bind_Some.
    setoid_rewrite IHl.
    destruct l'; [naive_solver|].
    naive_solver.
Qed.

Lemma join_list_is_Some {A} (l : list (option A)) : 
  is_Some (join_list l) <-> None ∉ l.
Proof.
  unfold is_Some.
  setoid_rewrite join_list_Some.
  induction l as [|a l IHl].
  - cbn.
    split; try easy.
    now exists [].
  - rewrite not_elem_of_cons, <- IHl.
    split.
    + intros (l' & Hl').
      destruct l' as [|a' l']; [easy|].
      cbn in Hl'.
      injection Hl'.
      intros -> ->.
      eauto.
    + intros [Ha (l' & Hl')].
      destruct a as [a|]; [|easy].
      exists (a :: l'); cbn; congruence.
Qed.


From stdpp Require Import strings fin_maps pmap gmap hlist.
From stdpp Require Import pretty.

(* FIXME: Move to Aux_stdpp *)
Lemma bind_is_Some {A B} (f : A -> option B) (mx : option A) : 
  is_Some (mx ≫= f) <-> is_Some mx /\ forall x, mx = Some x -> is_Some (f x).
Proof.
  destruct mx.
  - cbn.
    naive_solver.
  - cbn.
    rewrite 2 is_Some_alt.
    firstorder.
Qed.

Ltac f_equal_let :=
  let H := fresh in 
  match goal with 
  | |- (let '_ := ?x in _) = (let '_ := ?y in _) => 
    enough (H : x = y) by now first [rewrite H | rewrite <- H]
  | |- (let _ := ?x in _) = (let _ := ?y in _) => 
    enough (H : x = y) by now first [rewrite H | rewrite <- H]
  end.


Lemma lookup_insert_case `{FinMap K M} {A} (m : M A) (i j : K) (x : A) : 
  <[i:=x]> m !! j = if decide (i = j) then Some x else m !! j.
Proof.
  case_decide; now simplify_map_eq.
Qed.

Lemma NoDup_fmap_iff {A B} (f : A -> B) (l : list A) : 
  NoDup (f <$> l) <->
  NoDup l /\
  forall a a', a ∈ l -> a' ∈ l -> f a = f a' -> a = a'.
Proof.
  split; [|intros []; now apply NoDup_fmap_2_strong].
  intros Hmap.
  split; [now apply NoDup_fmap_1 in Hmap|].
  intros a a' (ia & Hia)%elem_of_list_lookup (ia' & Hia')%elem_of_list_lookup.
  intros Hfas.
  enough (ia = ia') by congruence.
  apply (NoDup_lookup (f <$> l) _ _ (f a) Hmap);
  rewrite list_lookup_fmap;
  [now rewrite Hia|].
  now rewrite Hia', Hfas.
Qed.

Lemma fsts_prod_map {A B C D} (f : A -> C) (g : B -> D) (l : list (A * B)) : 
  (prod_map f g <$> l).*1 = f <$> (l.*1).
Proof.
  rewrite <- 2 list_fmap_compose.
  reflexivity.
Qed.

Lemma snds_prod_map {A B C D} (f : A -> C) (g : B -> D) (l : list (A * B)) : 
  (prod_map f g <$> l).*2 = g <$> (l.*2).
Proof.
  rewrite <- 2 list_fmap_compose.
  reflexivity.
Qed.

  

Lemma disjoint_difference_l
  `{Set_ A C} `{!RelDecision (@elem_of A C _)} (X Y Z : C) : 
  X ∖ Y ## Z <-> X ∩ Z ⊆ Y. 
Proof.
  split; [set_solver|].
  intros HXZ x.
  set_solver.
Qed.

Lemma disjoint_difference_symm
  `{Set_ A C} (X Y Z : C) : 
  X ∖ Y ## Z <-> X ## Z ∖ Y.
Proof.
  set_solver.
Qed.


Lemma not_elem_of_drop_iff {A} (l : list A) a i :
  a ∉ drop i l <->
  (forall j a', i <= j -> l !! j = Some a' -> a' <> a).
Proof.
  rewrite elem_of_list_lookup.
  setoid_rewrite lookup_drop.
  split.
  - intros Hnex j a' Hij Hlook ->.
    apply Hnex.
    exists (j - i).
    rewrite <- Hlook.
    f_equal; lia.
  - intros Hlook (j & Hj).
    apply (Hlook (i + j) a); [lia|easy|easy].
Qed.

Lemma not_elem_of_drop_S_iff {A} (l : list A) a i :
  a ∉ drop (S i) l <->
  (forall j a', i < j -> l !! j = Some a' -> a' <> a).
Proof.
  apply not_elem_of_drop_iff.
Qed.


Lemma list_nil_iff {A} (l : list A) : l = [] <-> l ≡ [].
Proof.
  split; [now intros ->|].
  intros Hl.
  destruct l; set_solver.
Qed.

Lemma NoDup_list_eq_singleton_iff {A} (l : list A) a : NoDup l ->
  l = [a] <-> l ≡ [a].
Proof.
  intros Hdup.
  split; [intros ->; set_solver|].
  intros Hl.
  destruct l as [|a' l]; [set_solver|].
  rewrite NoDup_cons in Hdup.
  f_equal; [set_solver|].
  apply list_nil_iff.
  intros x.
  split; [|easy].
  intros Hx.
  assert (x ∈ [a]) as ->%elem_of_list_singleton by now rewrite <- Hl; right.
  enough (a' = a) by now subst.
  apply elem_of_list_singleton.
  now rewrite <- Hl; left.
Qed.

Lemma NoDup_list_eq_singleton_iff' {A} (l : list A) a : NoDup l ->
  l = [a] <-> a ∈ l /\ (forall b, b ∈ l -> b = a).
Proof.
  intros Hdup.
  rewrite NoDup_list_eq_singleton_iff by easy.
  set_solver.
Qed.

Lemma last_filter_Some `{P : A -> Prop} `{∀ a, Decision (P a)} l a :
  last (filter P l) = Some a <-> exists i, l !! i = Some a /\ P a /\ forall j a', i < j -> 
    l !! j = Some a' -> ~ P a'.
Proof.
  split.
  1: {
    revert a;
    induction l as [|a' l IHl]; [easy|]; intros a.
    cbn.
    case_decide as HPa'.
    - rewrite last_cons.
      destruct (last (filter P l)) as [a''|] eqn:Hlf.
      + intros [= ->].
        specialize (IHl a eq_refl) as (i & Hi & HPa & Higt).
        exists (S i).
        split; [apply Hi|].
        split; [easy|].
        intros [|j] ab Hij; [lia|].
        apply Higt; lia.
      + intros [= ->].
        exists 0.
        split; [easy|].
        split; [easy|].
        intros [|j] a' Hj; [lia|].
        cbn.
        intros Hlj HPa.
        rewrite last_None in Hlf.
        apply (elem_of_nil a').
        rewrite <- Hlf.
        apply elem_of_list_filter.
        split; [easy|].
        now apply elem_of_list_lookup_2 in Hlj.
    - intros (i & Hi & HPa & Hgt)%IHl.
      exists (S i).
      split; [easy|].
      split; [easy|].
      intros [|j] a'' Hj; [lia|].
      cbn.
      apply Hgt; lia.
  }
  1:{
    intros (i & Hi & HPa & Hnotin).
    revert l Hi Hnotin;
    induction i; intros l Hi Hnotin.
    - destruct l; [easy|].
      cbn in Hi.
      injection Hi; intros ->.
      cbn.
      rewrite decide_True by easy.
      rewrite last_cons.
      rewrite (fun H => proj2 (last_None _) H); [easy|].
      apply list_nil_iff.
      intros x.
      rewrite elem_of_nil.
      split; [|easy].
      rewrite elem_of_list_filter.
      rewrite elem_of_list_lookup.
      intros (Px & j & Hj).
      specialize (Hnotin (S j) x ltac:(lia) Hj).
      easy.
    - destruct l as [|a' l]; [easy|].
      cbn.
      cbn in Hi.
      case_decide; [|apply IHi; [easy|]; intros j ? ?; apply (Hnotin (S j)); lia].
      rewrite last_cons.
      destruct (last (filter P l)) as [lst|] eqn:Hlst.
      + rewrite <- Hlst.
        apply IHi; [easy|].
        intros j ? ?; apply (Hnotin (S j)); lia.
      + exfalso.
        apply last_None in Hlst.
        apply (filter_nil_not_elem_of _ _ _ Hlst HPa).
        now apply elem_of_list_lookup_2 in Hi.
  }
Qed.


Definition finv {A B C} `{Elements A C}
  `{EqDecision B} `{Inhabited A}
  (dom : C) (f : A -> B) : B -> A :=
  fun b => 
    default inhabitant (
      head (filter (fun a => f a = b) (elements dom))
    ).

Lemma finv_right_inverse {A B C} `{FinSet A C} `{Inhabited A} `{EqDecision B}
  (dom : C) (f : A -> B) b : (exists a, a ∈ dom /\ f a = b) ->
    f (finv dom f b) = b.
Proof.
  intros (a & Hadom & Hfa).
  unfold finv.
  destruct (head (filter (λ a, f a = b) (elements dom))) as [a'|] eqn:Hfilt.
  - apply head_Some_elem_of, elem_of_list_filter in Hfilt.
    easy.
  - exfalso.
    apply head_None in Hfilt.
    rewrite <- (elem_of_nil a), <- Hfilt.
    apply elem_of_list_filter; set_solver.
Qed.

Lemma finv_double_left_inverse {A B C} `{FinSet A C} `{Inhabited A} `{EqDecision B}
  (dom : C) (f : A -> B) a : a ∈ dom ->
    f (finv dom f (f a)) = f a.
Proof.
  intros Hadom.
  apply finv_right_inverse; eauto.
Qed.

Lemma finv_left_inverse {A B C} `{FinSet A C} `{Inhabited A} `{EqDecision B}
  (dom : C) (f : A -> B) a : a ∈ dom -> 
    (forall a a', a ∈ dom -> a' ∈ dom -> f a = f a' -> a = a') ->
    finv dom f (f a) = a.
Proof.
  intros Hadom Hfinj.
  unfold finv.
  replace (filter (λ a', f a' = f a) (elements dom)) with [a]; [easy|].
  symmetry.
  apply NoDup_list_eq_singleton_iff'; [apply NoDup_filter, NoDup_elements|].
  split; [now apply elem_of_list_filter; split; [|apply elem_of_elements]|].
  intros b (Hfb & Hbdom%elem_of_elements)%elem_of_list_filter.
  auto.
Qed.



Lemma app_inj_len_l {A} (l m l' m' : list A) : 
  length l = length l' -> 
  l ++ m = l' ++ m' -> 
  l = l' /\ m = m'.
Proof.
  intros Hlen Heq.
  apply (f_equal (take (length l))) in Heq as Heql.
  rewrite take_app_length, Hlen, take_app_length in Heql.
  subst l'.
  split; [easy|].
  now apply app_inv_head in Heq.
Qed.

Lemma app_inj_len_r {A} (l m l' m' : list A) : 
  length m = length m' -> 
  l ++ m = l' ++ m' -> 
  l = l' /\ m = m'.
Proof.
  intros Hlen Heq.
  specialize (f_equal length Heq).
  simpl_list.
  intros Hlens.
  apply app_inj_len_l; easy + lia.
Qed.



Lemma list_to_set_concat {A C} `{Set_ A C} (l : list (list A)) : 
  list_to_set (concat l) ≡@{C} ⋃ (list_to_set <$> l).
Proof.
  induction l; [reflexivity|].
  now cbn; rewrite list_to_set_app, IHl.
Qed.

Lemma list_to_set_concat_L {A C} `{Set_ A C} `{!LeibnizEquiv C} (l : list (list A)) : 
  list_to_set (concat l) =@{C} ⋃ (list_to_set <$> l).
Proof.
  unfold_leibniz.
  apply list_to_set_concat.
Qed.



Lemma NoDup_list_bind {A B} (f : A -> list B) l : 
  NoDup l -> 
    (forall a, a ∈ l -> NoDup (f a)) ->
    (forall a a' b, a ∈ l -> a' ∈ l -> a <> a' -> 
      b ∈ f a -> b ∉ f a') ->
  NoDup (l ≫= f).
Proof.
  intros Hdup Hfdup Hinj.
  induction Hdup; [constructor|].
  cbn.
  apply NoDup_app.
  split; [now apply Hfdup; left|].
  split; [|apply IHHdup; set_solver].
  intros b Hbx.
  rewrite elem_of_list_bind.
  intros (y & Hby & Hy).
  revert Hbx Hby.
  apply Hinj; set_solver.
Qed.



Lemma map_img_list_to_map `{FinMap K M} `{Set_ A SA} 
  (l : list (K * A)) : 
  NoDup l.*1 ->
  map_img (list_to_map l :> M A) ≡@{SA} list_to_set l.*2.
Proof.
  intros Hl.
  rewrite map_img_alt.
  now rewrite map_to_list_to_map by easy.
Qed.

Lemma map_img_list_to_map_L `{FinMap K M} `{Set_ A SA} `{!LeibnizEquiv SA}
  (l : list (K * A)) : 
  NoDup l.*1 ->
  map_img (list_to_map l :> M A) =@{SA} list_to_set l.*2.
Proof.
  unfold_leibniz.
  apply map_img_list_to_map.
Qed.




Fixpoint list_decomps_aux {A} (pre l : list A) : list (list A * A * list A) :=
  match l with 
  | [] => []
  | a :: l => 
    (pre, a, l) :: list_decomps_aux (pre ++ [a]) l
  end.

Definition list_decomps {A} (l : list A) : list (list A * A * list A) :=
  list_decomps_aux [] l.
  

Lemma elem_of_list_decomps_aux {A} (pre l : list A) : 
  forall hd a tl, (hd, a, tl) ∈ list_decomps_aux pre l <->
    hd ++ [a] ++ tl = pre ++ l /\
    length (pre) <= length (hd).
Proof.
  revert pre; induction l; intros pre hd b tl.
  - cbn.
    split; [easy|].
    intros (Heq%(f_equal length) & Hlen).
    revert Heq.
    simpl_list.
    cbn.
    lia.
  - cbn.
    rewrite elem_of_cons.
    rewrite IHl.
    split.
    + intros [[= -> -> ->] | [Heq Hlen]]; [easy|].
      rewrite <- app_assoc in Heq.
      split; [apply Heq|].
      rewrite <- Hlen.
      simpl_list; cbn; lia.
    + intros [Heq Hlen].
      destruct_decide (decide (length pre = length hd)) as Hleneq.
      * left.
        apply app_inj_len_l in Heq; [|easy].
        now destruct Heq as [-> [= -> ->]].
      * right.
        rewrite <- app_assoc.
        split; [easy|].
        simpl_list; cbn; lia.
Qed.

Lemma elem_of_list_decomps {A} (l : list A) : 
  forall hd a tl, (hd, a, tl) ∈ list_decomps l <->
    hd ++ [a] ++ tl = l.
Proof.
  intros hd a tl.
  unfold list_decomps.
  rewrite elem_of_list_decomps_aux.
  naive_solver lia.
Qed.

(* FIXME: Move *)
Lemma exists_pair {A B} (P : A * B -> Prop) : 
  (exists ab, P ab) <-> exists a, exists b, P (a, b).
Proof.
  split.
  - intros [[] ?]; eauto.
  - intros (?&?&?); eauto.
Qed.

Definition list_removals {A} (l : list A) : list (A * list A) :=
  (λ '(hd, a, tl), (a, hd ++ tl)) <$> list_decomps l.

Lemma elem_of_list_removals {A} (l : list A) a hd_tl : 
  (a, hd_tl) ∈ list_removals l <-> exists hd tl, hd_tl = hd ++ tl /\ 
    hd ++ [a] ++ tl = l.
Proof.
  unfold list_removals.
  rewrite elem_of_list_fmap.
  rewrite 2 exists_pair.
  setoid_rewrite pair_eq.
  setoid_rewrite elem_of_list_decomps.
  naive_solver.
Qed.


Lemma elem_of_list_removals_perm {A} (l : list A) a hd_tl : 
  (a, hd_tl) ∈ list_removals l -> l ≡ₚ a :: hd_tl.
Proof.
  rewrite elem_of_list_removals.
  intros (hd & tl & -> & <-).
  quote_Permutation.
  apply rlist.eval_Permutation.
  cbn.
  compute_done.
Qed.

Definition list_select `(P : A -> Prop)
  `{forall (a : A), Decision (P a)} (l : list A) : list (A * list A) :=
  filter (fun a_rst => P (fst a_rst)) (list_removals l).


Lemma elem_of_list_select {A} `(P : A -> Prop)
  `{forall (a : A), Decision (P a)} (l : list A) a hd_tl : 
  (a, hd_tl) ∈ list_select P l <-> P a /\ exists hd tl, hd_tl = hd ++ tl /\ 
    hd ++ [a] ++ tl = l.
Proof.
  unfold list_select.
  rewrite elem_of_list_filter.
  now rewrite elem_of_list_removals.
Qed.


Lemma elem_of_list_select_perm {A} `(P : A -> Prop)
  `{forall (a : A), Decision (P a)} (l : list A) a hd_tl : 
  (a, hd_tl) ∈ list_select P l -> l ≡ₚ a :: hd_tl.
Proof. 
  intros [_ (? & ? & -> & <-)]%elem_of_list_select.
  solve_Permutation.
Qed. 


Definition gmap_map `{Countable A} (m : gmap A A) : A -> A :=
  fun a => default a (m !! a).

Lemma gmap_map_correct `{Countable A} (m : gmap A A) a b : 
  m !! a = Some b -> gmap_map m a = b.
Proof.
  unfold gmap_map.
  now intros ->.
Qed.

Lemma gmap_map_idemp `{Countable A} (m : gmap A A) a : 
  a ∉ dom m -> gmap_map m a = a.
Proof.
  intros Ha.
  unfold gmap_map.
  unfold default.
  case_match eqn:Heq; [|reflexivity].
  now apply elem_of_dom_2 in Heq.
Qed.



Lemma elem_of_from_option_list_singleton {A} (a : A) (ma : option A) : 
  a ∈ from_option (λ x, [x]) [] ma <->
  ma = Some a.
Proof.
  destruct ma; cbn; set_solver.
Qed.


Lemma filter_with_iff_neg_Permutation {A} {P Q : A -> Prop} 
  `{∀ a, Decision (P a)} `{∀ a, Decision (Q a)} l : 
  (∀ a, P a <-> ~ Q a) -> 
  filter P l ++ filter Q l ≡ₚ l.
Proof.
  intros HPQ.
  induction l; [easy|].
  cbn.
  case_decide.
  - rewrite decide_False by now apply HPQ.
    cbn.
    now rewrite IHl.
  - case_decide; [|exfalso; naive_solver].
    rewrite <- IHl at 3.
    solve_Permutation.
Qed.

Lemma filter_with_neg_Permutation {A} {P : A -> Prop} 
  `{∀ a, Decision (P a)} l : 
  filter P l ++ filter (λ a, ~ P a) l ≡ₚ l.
Proof.
  rewrite Permutation_app_comm.
  now apply filter_with_iff_neg_Permutation.
Qed.

Lemma filter_neg_with_Permutation {A} {P : A -> Prop} 
  `{∀ a, Decision (P a)} l : 
  filter (λ a, ~ P a) l ++ filter P l ≡ₚ l.
Proof.
  now apply filter_with_iff_neg_Permutation.
Qed.



Lemma fmap_Permuation_iff_exists {A B} (f : A -> B) (l : list A) l' : 
  f <$> l ≡ₚ l' <-> 
  exists l'', l ≡ₚ l'' /\ f <$> l'' = l'.
Proof.
  split.
  - revert l'; induction l as [|a l IHl]; intros l'.
    + cbn.
      intros ->%Permutation_nil.
      eauto.
    + cbn.
      intros Hperm.
      assert (Hal' : f a ∈ l') by now rewrite <- Hperm; left.
      apply elem_of_list_split in Hal' as Ha'l'.
      destruct Ha'l' as (fl'1 & fl'2 & Heq).
      subst l'.
      specialize (IHl (fl'1 ++ fl'2) (Permutation_cons_app_inv _ _ Hperm)).
      destruct IHl as (l'' & Hl & Hfl'').
      apply fmap_app_inv in Hfl'' as (l'1 & l'2 & Hl'1 & Hl'2 & Hl'').
      exists (l'1 ++ a :: l'2).
      split; [rewrite Hl; subst; solve_Permutation|].
      rewrite fmap_app; cbn.
      congruence.
  - intros (? & Hperm & Heq).
    now rewrite Hperm, <- Heq.
Qed.


Lemma size_map_img_le_size_dom `{FinMapDom K M SK}
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA} (m : M A) : 
  size (map_img m :> SA) <= size (dom m).
Proof.
  induction m using map_first_key_ind.
  - now rewrite map_img_empty, dom_empty, 2 size_empty.
  - rewrite dom_insert.
    assert (Hid : i ∉ dom m) by (now apply not_elem_of_dom).
    rewrite size_union by set_solver.
    rewrite size_singleton.
    transitivity (1 + size (map_img m :> SA))%nat; [|lia].
    etransitivity; [eapply subseteq_size; apply map_img_insert_subseteq|].
    rewrite size_union_alt, size_singleton.
    apply Nat.add_le_mono_l.
    apply subseteq_size, subseteq_difference_l; reflexivity.
Qed.

Lemma map_dom_img_lt_card_iff `{FinMapDom K M SK}
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA} `{!RelDecision (∈@{SA})}
    (m : M A) : 
  size (map_img m :> SA) < size (dom m) <-> 
  exists i j a, m !! i = Some a /\ m !! j = Some a /\ i <> j.
Proof.
  split.
  - induction m using map_first_key_ind; 
    [now rewrite dom_empty, map_img_empty, 2 size_empty|].
    rewrite dom_insert, map_img_insert_notin by easy.
    assert (Hid : i ∉ dom m) by (now apply not_elem_of_dom).
    destruct_decide (decide (x ∈@{SA} map_img m)) as Hx.
    + apply elem_of_map_img_1 in Hx as (j & Hj).
      intros _.
      exists i, j, x.
      enough (i <> j) by now 
      rewrite lookup_insert, lookup_insert_ne.
      intros ->.
      now apply elem_of_dom_2 in Hj.
    + rewrite 2 (size_union {[_]}) by set_solver.
      rewrite 2 size_singleton.
      intros (j & k & a & Hj & Hk & Hjk)%Nat.succ_lt_mono%IHm.
      exists j, k, a.
      rewrite lookup_insert_ne by (intros ->; now apply elem_of_dom_2 in Hj).
      rewrite lookup_insert_ne by (intros ->; now apply elem_of_dom_2 in Hk).
      easy.
  - intros (i & j & a & Hi & Hj & Hij).
    rewrite <- (insert_delete m i a Hi).
    rewrite map_img_insert_notin, dom_insert by apply lookup_delete.
    rewrite <- (insert_delete (delete i m) j a) by now rewrite lookup_delete_ne.
    rewrite map_img_insert_notin, dom_insert by apply lookup_delete.
    rewrite (union_assoc _), (union_idemp _).
    rewrite size_union_alt, 
      (size_union {[i]}), (size_union {[j]}), 3 size_singleton by set_solver.
    eapply Nat.le_lt_trans; [apply -> Nat.succ_le_mono; 
      apply subseteq_size, subseteq_difference_l; reflexivity|].
    pose proof (size_map_img_le_size_dom (delete j (delete i m)) (SA:=SA)).
    lia.
Qed.

Lemma map_dom_img_eq_card_iff_inj `{FinMapDom K M SK}
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA} `{!RelDecision (∈@{SA})}
    (m : M A) : 
  size (dom m) = size (map_img m :> SA) <-> 
  forall i j a, m !! i = Some a -> m !! j = Some a -> i = j.
Proof.
  split.
  - intros Hsize.
    assert (Hn : ~ size (map_img m :> SA) < size (dom m)) by lia.
    rewrite map_dom_img_lt_card_iff in Hn.
    intros i j a Hi Hj.
    apply dec_stable.
    intros Hij.
    apply Hn.
    naive_solver.
  - intros Hinj.
    specialize (size_map_img_le_size_dom m (SA:=SA)).
    enough (~ size (map_img m :> SA) < size (dom m)) by lia.
    rewrite map_dom_img_lt_card_iff.
    naive_solver.
Qed.

Lemma map_dom_img_eq_card_iff_NoDup `{FinMapDom K M SK}
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA} `{!RelDecision (∈@{SA})}
    (m : M A) : 
  size (dom m) = size (map_img m :> SA) <-> 
  NoDup (map_to_list m).*2.
Proof.
  rewrite map_dom_img_eq_card_iff_inj.
  rewrite NoDup_alt.
  setoid_rewrite list_lookup_fmap.
  setoid_rewrite fmap_Some.
  split.
  - intros Hinj i j a.
    intros ([k a'] & Hk & Ha') ([k' a''] & Hk' & Ha'').
    cbn in Ha', Ha''.
    subst a' a''.
    apply elem_of_list_lookup_2 in Hk as Hka.
    apply elem_of_list_lookup_2 in Hk' as Hk'a.
    rewrite elem_of_map_to_list in * |-.
    assert (k = k') by eauto.
    subst k'.
    now apply (NoDup_lookup _ _ _ (k,a) (NoDup_map_to_list m)).
  - intros HNoDup.
    intros k k' a Hka Hk'a.
    apply elem_of_map_to_list in Hka as Hka'.
    apply elem_of_map_to_list in Hk'a as Hk'a'.
    apply elem_of_list_lookup_1 in Hka' as [i Hi].
    apply elem_of_list_lookup_1 in Hk'a' as [j Hj].
    enough (i = j) by congruence.
    apply (HNoDup _ _ a); eexists (_, a); eauto.
Qed.


Lemma elem_of_list_fmap_prod_map {A B C D} 
  (f : A -> C) (g : B -> D) (l : list (A * B)) cd : 
  cd ∈ prod_map f g <$> l <-> 
  exists a b, (a, b) ∈ l /\ f a = cd.1 /\ g b = cd.2.
Proof.
  destruct cd as [c d].
  rewrite elem_of_list_fmap.
  rewrite exists_pair.
  cbn.
  naive_solver.
Qed.

Lemma fsts_prod_swap {A B} (l : list (A * B)) : 
  (prod_swap <$> l).*1 = l.*2.
Proof.
  induction l as [|[]]; cbn; f_equal; easy.
Qed.

Lemma snds_prod_swap {A B} (l : list (A * B)) : 
  (prod_swap <$> l).*2 = l.*1.
Proof.
  induction l as [|[]]; cbn; f_equal; easy.
Qed.

Lemma lookup_list_to_map_gen `{FinMap K M} {A} 
  (l : list (K * A)) k : 
    (list_to_map l :> M A) !! k = snd <$> head (filter (λ kv, kv.1 = k) l).
Proof.
  induction l as [|[k' a'] l IHl].
  - cbn.
    now rewrite lookup_empty.
  - cbn.
    rewrite lookup_insert_case.
    case_decide; [reflexivity|].
    apply IHl.
Qed.

Lemma list_to_map_eq_fold_right `{FinMap K M} {A} 
  (l : list (K * A)) : (list_to_map l :> M A) = foldr (λ p, <[p.1:=p.2]>) ∅ l.
Proof.
  induction l; cbn; f_equal; congruence.
Qed.


Lemma gmap_map_inj_on `{Countable A} (m : gmap A A) (X : gset A) : 
  (forall i j a, m !! i = Some a -> m !! j = Some a -> i = j) -> 
  X ⊆ dom m -> 
  forall a b, a ∈ X -> b ∈ X -> gmap_map m a = gmap_map m b -> a = b.
Proof.
  intros Hinj HX a b [ma Hma]%HX%elem_of_dom [mb Hmb]%HX%elem_of_dom.
  rewrite (gmap_map_correct _ _ _ Hma), (gmap_map_correct _ _ _ Hmb).
  intros ->.
  eauto.
Qed.


Lemma list_to_set_equiv `{SemiSet A C} (l l' : list A) : 
  list_to_set l ≡@{C} list_to_set l' <-> l ≡ l'.
Proof.
  rewrite set_equiv.
  setoid_rewrite elem_of_list_to_set.
  reflexivity.
Qed.

Lemma list_to_set_subseteq `{SemiSet A C} (l l' : list A) : 
  list_to_set l ⊆@{C} list_to_set l' <-> l ⊆ l'.
Proof.
  unfold subseteq, set_subseteq_instance, list_subseteq.
  setoid_rewrite elem_of_list_to_set.
  reflexivity.
Qed.


Notation "'unfold' x" := (ltac:(let x' := eval unfold x in x in 
  exact (eq_refl : x = x'))) (at level 10, only parsing).


Lemma decide_not `{HNP : Decision (~ P)} `{HP : Decision P} {A} (x y : A) : 
  (if @decide (~ P) HNP then x else y) = 
  (if @decide P HP then y else x).
Proof.
  now do 2 case_decide.
Qed.



Notation gset_to_Pset s := 
  (list_to_set (C:=Pset) $ strings.string_to_pos <$> elements s).


Lemma elem_of_gset_string_to_Pset (s : gset string) p : 
  p ∈@{Pset} gset_to_Pset s <->
  exists y, y ∈ s /\ p = encode y.
Proof.
  rewrite elem_of_list_to_set, elem_of_list_fmap.
  setoid_rewrite elem_of_elements.
  naive_solver.
Qed.

Lemma elem_of_gset_string_to_Pset' (s : gset string) (x : string) :
  encode x ∈ gset_to_Pset s <-> x ∈ s.
Proof.
  rewrite elem_of_gset_string_to_Pset.
  naive_solver.
Qed.

Lemma gset_to_Pset_inj (s s' : gset string) : 
  gset_to_Pset s = gset_to_Pset s' -> s = s'.
Proof.
  intros Heq.
  apply set_eq; intros x.
  by rewrite <- 2 elem_of_gset_string_to_Pset', Heq.
Qed.


Lemma list_bind_ext_strong {A B} (f g : A -> list B) (l : list A) :
  (forall a, a ∈ l -> f a = g a) ->
  l ≫= f = l ≫= g.
Proof.
  induction l; [reflexivity|];
  intros Hfg.
  cbn.
  rewrite Hfg by now left.
  f_equal.
  apply IHl; intros; apply Hfg; now right.
Qed.

Lemma caps_eq_r_weaken `{FinSet A SA} (X Y Z Z' : SA) : 
  Z ⊆ Z' -> X ∩ Z' ≡ Y ∩ Z' -> X ∩ Z ≡ Y ∩ Z.
Proof.
  set_solver.
Qed.

Lemma caps_eq_r_weaken_L `{FinSet A SA} `{!LeibnizEquiv SA} (X Y Z Z' : SA) : 
  Z ⊆ Z' -> X ∩ Z' = Y ∩ Z' -> X ∩ Z = Y ∩ Z.
Proof.
  unfold_leibniz.
  apply caps_eq_r_weaken.
Qed.


Lemma guard_is_Some `{Decision P} {A} (x : A) : 
  is_Some (guard P ≫= λ _, Some x) <-> P.
Proof.
  case_guard; cbn; [done|]; by split; [intros ?%is_Some_None|].
Qed.

Lemma list_fmap_filter_inv 
  `(f : A -> B) (g : B -> A) `{!Cancel eq g f} 
  {P : A -> Prop} `{∀ a, Decision (P a)} l : 
  f <$> filter P l =@{list B} filter (P ∘ g) (f <$> l).
Proof.
  induction l; [done|].
  cbn.
  rewrite (decide_ext (P (g _)) (P a)) by 
    now rewrite (cancel g f).
  unfold filter in *.
  rewrite <- IHl.
  by case_decide.
Qed.

Lemma list_filter_fmap 
  `(f : A -> B)
  {P : B -> Prop} `{∀ a, Decision (P a)} l : 
  filter P (f <$> l) =@{list B} f <$> filter (P ∘ f) l.
Proof.
  induction l; [done|].
  cbn.
  by case_decide;
  unfold filter in *;
  rewrite IHl.
Qed.

Lemma list_filter_iff_strong {A} (P1 P2 : A -> Prop)
  `{∀ a, Decision (P1 a)} `{∀ a, Decision (P2 a)} (l : list A) : 
  (∀ a, a ∈ l -> P1 a <-> P2 a) ->
  filter P1 l = filter P2 l.
Proof.
  unfold filter.
  induction l; [done|].
  intros HP.
  cbn.
  unfold filter.
  erewrite decide_ext by now apply HP; left.
  rewrite IHl by now intros; apply HP; right.
  reflexivity.
Qed.
