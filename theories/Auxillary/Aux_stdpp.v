(* Extra bits for stdpp *)
Require Combinators.
Require Import SetoidList SetoidPermutation.
From stdpp Require Import decidable.
Require Import Aux.

From stdpp Require Import prelude functions.


From stdpp Require Import strings fin_maps gmultiset pmap gmap hlist.
From stdpp Require Import pretty.

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


Lemma elem_of_list_select_perm_Prop {A} `(P : A -> Prop)
  `{forall (a : A), Decision (P a)} (l : list A) a hd_tl :
  (a, hd_tl) ∈ list_select P l -> P a /\ l ≡ₚ a :: hd_tl.
Proof.
  intros [? (? & ? & -> & <-)]%elem_of_list_select.
  split; [easy|solve_Permutation].
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
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA}
    (m : M A) :
  size (map_img m :> SA) < size (dom m) <->
  exists i j a, m !! i = Some a /\ m !! j = Some a /\ i <> j.
Proof.
  assert (RelDecision (∈@{SA})) by apply elem_of_dec_slow.
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
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA}
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
  `{!Elements K SK} `{!FinSet K SK} `{FinSet A SA}
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

Notation "'unfold' x 'in' y" := (ltac:(let y' := eval unfold x in y in
  exact (eq_refl : y = y'))) (at level 10, only parsing).


Notation "'unfolded' x" := (ltac:(let x' := eval unfold x in x in
  exact x')) (at level 10, only parsing).

Notation "'unfolded' x 'in' y" := (ltac:(let y' := eval unfold x in y in
  exact y')) (at level 10, only parsing).

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




Module pfin.

Local Open Scope positive_scope.


Inductive pfin : positive -> Set :=
  | PFO_H {p} : pfin (p~0)
  | PFO_O {p} : pfin p -> pfin (p~0)
  | PFO_I {p} : pfin p -> pfin (p~0)
  | PFI_H {p} : pfin (p~1)
  | PFI_SH {p} : pfin (p~1)
  | PFI_SO {p} : pfin p -> pfin (p~1)
  | PFI_SI {p} : pfin p -> pfin (p~1).

Declare Scope pfin_scope.
Bind Scope pfin_scope with pfin.
Delimit Scope pfin_scope with pfin.

Local Open Scope pfin_scope.

Fixpoint pfin_to_pos {p} (i : pfin p) : positive :=
  match i with
  | PFO_H => 1
  | PFO_O i => (pfin_to_pos i)~0
  | PFO_I i => (pfin_to_pos i)~1
  | PFI_H => 1
  | PFI_SH => 2
  | PFI_SO i => Pos.succ (pfin_to_pos i)~0
  | PFI_SI i => Pos.succ (pfin_to_pos i)~1
  end.


Lemma pfin_to_pos_lt {p} (i : pfin p) :
  pfin_to_pos i < p.
Proof.
  induction i; cbn; lia.
Qed.

Definition pfin_1_inv (P : pfin 1 -> Type) (i : pfin 1) : P i :=
  match i with | PFO_H | PFO_O _ | PFO_I _
  | PFI_H | PFI_SH | PFI_SO _ | PFI_SI _ =>
    fun devil => False_rect (@ID) devil end.

Definition pfin_xO_inv {p} (P : pfin p~0 -> Type) (H1 : P PFO_H)
  (HxO : forall i, P (PFO_O i)) (HxI : forall i, P (PFO_I i)) :
  forall i, P i :=
  fun i =>
  match i as i' in pfin p return
    forall (P : pfin p -> Type),
    match p as p' return (pfin p' -> Type) -> (pfin p' -> Type) with
    | p~0 => fun P i => _ -> _ -> _ -> P i
    | _ => fun P _ => True
    end P i' with
  | PFO_H => fun P H1 _ _ => H1
  | PFO_O i => fun P _ HxO _ => HxO i
  | PFO_I i => fun P _ _ HxI => HxI i
  | PFI_H
  | PFI_SH
  | PFI_SO _
  | PFI_SI _ => fun _ => Logic.I
  end P H1 HxO HxI.

Definition pfin_xI_inv {p} (P : pfin p~1 -> Type) (H1 : P PFI_H)
  (H2 : P PFI_SH)
  (HxO : forall i, P (PFI_SO i)) (HxI : forall i, P (PFI_SI i)) :
  forall i, P i :=
  fun i =>
  match i as i' in pfin p return
    forall (P : pfin p -> Type),
    match p as p' return (pfin p' -> Type) -> (pfin p' -> Type) with
    | p~1 => fun P i => _ -> _ -> _ -> _ -> P i
    | _ => fun P _ => True
    end P i' with
  | PFI_H => fun P H1 _ _ _ => H1
  | PFI_SH => fun P _ H2 _ _ => H2
  | PFI_SO i => fun P _ _ HxO _ => HxO i
  | PFI_SI i => fun P _ _ _ HxI => HxI i
  | PFO_H
  | PFO_O _
  | PFO_I _ => fun _ => Logic.I
  end P H1 H2 HxO HxI.

Definition PFI_S {p} (i : pfin p~0) : pfin p~1 :=
  pfin_xO_inv _ PFI_SH PFI_SO PFI_SI i.

Definition pfin_xI_inv' {p} (P : pfin p~1 -> Type)
  (H1 : P PFI_H) (HS : forall i, P (PFI_S i)) i : P i :=
  pfin_xI_inv P H1 (HS PFO_H) (fun i => HS (PFO_O i))
    (fun i => HS (PFO_I i)) i.

Definition pfin_rect' (P : forall p, pfin p -> Type)
  (HO_1 : forall p, P p~0 PFO_H) (HI_1 : forall p, P p~1 PFI_H)
  (HxO : forall p i, P p i -> P p~0 (PFO_O i))
  (HxI : forall p i, P p i -> P p~0 (PFO_I i))
  (HS : forall p i, P p~0 i -> P p~1 (PFI_S i)) : forall p i, P p i :=
  fix go p :=
  match p with
  | 1 => pfin_1_inv _
  | p~0 => pfin_xO_inv (P p~0) (HO_1 _)
    (fun i => HxO _ _ (go _ i)) (fun i => HxI _ _ (go _ i))
  | p~1 => pfin_xI_inv' (P p~1) (HI_1 _)
    (fun i => HS _ _ (pfin_xO_inv (P p~0) (HO_1 _)
    (fun i => HxO _ _ (go _ i)) (fun i => HxI _ _ (go _ i)) i))
  end.

Definition pfin_1 {p} : pfin (Pos.succ p) :=
  match p with
  | 1 => PFO_H
  | p~0 => PFI_H
  | p~1 => PFO_H
  end.

Fixpoint pfin_S {p} : pfin p -> pfin (Pos.succ p) :=
  match p with
  | 1 => pfin_1_inv _
  | p~0 => PFI_S
  | p~1 => pfin_xI_inv _ (PFO_O pfin_1) (PFO_I pfin_1)
    (fun i => PFO_O (pfin_S i)) (fun i => PFO_I (pfin_S i))
  end.

Lemma pfin_1_to_pos {p} : pfin_to_pos (@pfin_1 p) = 1.
Proof.
  now destruct p.
Qed.

Lemma pfin_S_to_pos {p} (i : pfin p) :
  pfin_to_pos (pfin_S i) = Pos.succ (pfin_to_pos i).
Proof.
  induction i; cbn; rewrite 1?pfin_1_to_pos; lia.
Qed.


Local Lemma lt_xI_xO_inv {i p} : i~1 < p~0 -> i < p.
Proof.
  lia.
Qed.

Local Lemma lt_SxI_xI_inv {i p} : Pos.succ i~1 < p~1 -> i < p.
Proof.
  lia.
Qed.

Fixpoint pos_to_pfin (i p : positive) : i < p -> pfin p :=
  match p with
  | xH => fun H => False_rect (pfin 1) (Pos.nlt_1_r i H)
  | p~0 => match i with
    | xH => fun _ => PFO_H
    | i~0 => fun H => PFO_O (pos_to_pfin i p H)
    | i~1 => fun H => PFO_I (pos_to_pfin i p
      (lt_xI_xO_inv H))
    end
  | p~1 =>
    Pos.peano_rect (fun i => i < p~1 -> pfin p~1)
      (fun _ => PFI_H)
      (fun i _ =>
      match i with
      | xH => fun _ => PFI_SH
      | i~0 => fun H => PFI_SO (pos_to_pfin i p H)
      | i~1 => fun H => PFI_SI (pos_to_pfin i p (lt_SxI_xI_inv H))
      end) i
  end.

Lemma pfin_to_pos_to_pfin {p} (i : pfin p) H :
  pos_to_pfin (pfin_to_pos i) p H = i.
Proof.
  induction i; cbn; rewrite 1?Pos.peano_rect_succ, 1?IHi;
    try reflexivity.
Qed.

Lemma pos_to_pfin_to_pos i p H :
  pfin_to_pos (pos_to_pfin i p H) = i.
Proof.
  revert i H; induction p; intros i H; [destruct i..|lia];
  cbn; rewrite ?IHp; try reflexivity.
  destruct i using Pos.peano_case; [reflexivity|].
  rewrite Pos.peano_rect_succ.
  change (Pos.succ (i~0)) with i~1.
  cbn.
  rewrite IHp.
  reflexivity.
Qed.


Fixpoint pos_to_pfin_opt (i p : positive) : option (pfin p) :=
  match p with
  | xH => None
  | p~0 => match i with
    | xH => Some (PFO_H)
    | i~0 => PFO_O <$> (pos_to_pfin_opt i p)
    | i~1 => PFO_I <$> (pos_to_pfin_opt i p)
    end
  | p~1 =>
    Pos.peano_rect (fun i => option (pfin p~1))
      (Some PFI_H)
      (fun i _ =>
      match i with
      | xH => Some PFI_SH
      | i~0 => PFI_SO <$> (pos_to_pfin_opt i p)
      | i~1 => PFI_SI <$> (pos_to_pfin_opt i p)
      end) i
  end.


Lemma pos_to_pfin_opt_is_Some i p :
  is_Some (pos_to_pfin_opt i p) <-> i < p.
Proof.
  revert i; induction p; intros i; cbn.
  - destruct i using Pos.peano_case.
    + cbn.
      split; [lia|auto].
    + rewrite Pos.peano_rect_succ.
      destruct i; [cbn; rewrite 1?fmap_is_Some, IHp; lia..|].
      split; [lia|auto].
  - destruct i; [cbn; rewrite 1?fmap_is_Some, IHp; lia..|].
    split; [lia|auto].
  - split; [intros []%is_Some_None|lia].
Qed.

Lemma pos_to_pfin_opt_correct i p H :
  pos_to_pfin_opt i p = Some (pos_to_pfin i p H).
Proof.
  revert i H; induction p; intros i H; cbn.
  - destruct i using Pos.peano_case; [reflexivity|].
    rewrite 2 Pos.peano_rect_succ.
    now destruct i; [cbn; erewrite IHp..|].
  - now destruct i; [cbn; erewrite IHp..|].
  - lia.
Qed.

End pfin.

Module pvec.

#[universes(template)]
Inductive pvec (A : Type) : positive -> Type :=
  | pvnil : pvec A 1
  | pvxO {p} (aH : A) (pO : pvec A p) (pI : pvec A p) : pvec A p~0
  | pvxI {p} (aH aSH : A) (pO : pvec A p) (pI : pvec A p) : pvec A p~1.

(*
Inductive pfin : positive -> Set :=
  | PFO_H {p} : pfin (p~0)
  | PFO_O {p} : pfin p -> pfin (p~0)
  | PFO_I {p} : pfin p -> pfin (p~0)
  | PFI_H {p} : pfin (p~1)
  | PFI_SH {p} : pfin (p~1)
  | PFI_SO {p} : pfin p -> pfin (p~1)
  | PFI_SI {p} : pfin p -> pfin (p~1). *)
End pvec.



(* A predicate saying a map to a domain [D] has types specified by
  the map [mT], according to the typing function [ty : D -> T]. A
  canonical example is [D = {t : T & P t}] for some dependent type
  [P], whence [ty = projT1]. *)
Definition map_is_typed {K D T MD MT} `{Lookup K D MD, Lookup K T MT}
  (ty : D -> T) (mT : MT) (mD : MD) : Prop :=
  forall k, ty <$> mD !! k = mT !! k.

Definition map_is_subtyped {K D T MD MT} `{Lookup K D MD, Lookup K T MT}
  (ty : D -> T) (mT : MT) (mD : MD) : Prop :=
  forall k t, mT !! k = Some t -> ty <$> mD !! k = Some t.

Lemma map_is_typed_alt {K D T M} `{∀ A, Lookup K A (M A)}
  (ty : D -> T) (mT : M T) (mD : M D) :
  map_is_typed ty mT mD <-> map_relation (λ _ t d, ty d = t)
    (λ _ _, False) (λ _ _, False) mT mD.
Proof.
  unfold map_relation, map_is_typed.
  apply forall_iff; intros k.
  destruct (mD !! k), (mT !! k); naive_solver.
Qed.

Lemma map_is_subtyped_alt {K D T M} `{∀ A, Lookup K A (M A)}
  (ty : D -> T) (mT : M T) (mD : M D) :
  map_is_subtyped ty mT mD <-> map_relation (λ _ t d, ty d = t)
    (λ _ _, False) (λ _ _, True) mT mD.
Proof.
  unfold map_relation, map_is_subtyped.
  apply forall_iff; intros k.
  unfold option_relation.
  destruct (mD !! k), (mT !! k); naive_solver.
Qed.



Section typed_map.

Context {D T} `{FinMapDom K M SK} (ty : D -> T).

(* Local Notation map_is_typed := (@map_is_typed K D T (M D) (M T) _ _ ty). *)

Implicit Types (mD : M D) (mT : M T).

Lemma map_is_typed_dom mD mT :
  map_is_typed ty mT mD -> dom mD ≡ dom mT.
Proof.
  set_unfold.
  setoid_rewrite elem_of_dom.
  intros Hrw k.
  rewrite <- (Hrw k).
  now rewrite fmap_is_Some.
Qed.

Lemma map_is_typed_domL `{!LeibnizEquiv SK} mD mT :
  map_is_typed ty mT mD -> dom mD = dom mT.
Proof.
  unfold_leibniz.
  apply map_is_typed_dom.
Qed.

Lemma map_is_typed_iff_fmap_eq mD mT :
  map_is_typed ty mT mD <-> ty <$> mD = mT.
Proof.
  rewrite (map_eq_iff _ mT).
  apply forall_iff; intros k.
  now rewrite lookup_fmap.
Qed.

Lemma map_is_typed_empty_l mD : map_is_typed ty (∅ :> M T) mD <-> mD = ∅.
Proof.
  rewrite map_is_typed_iff_fmap_eq.
  apply fmap_empty_iff.
Qed.

Lemma map_is_typed_empty_r mT : map_is_typed ty mT (∅ :> M D) <-> mT = ∅.
Proof.
  rewrite map_is_typed_iff_fmap_eq.
  now rewrite fmap_empty.
Qed.

Lemma map_is_typed_insert_l k t mT mD :
  mT !! k = None ->
  map_is_typed ty (<[k := t]> mT) mD <->
  ty <$> mD !! k = Some t /\
  map_is_typed ty mT (delete k mD).
Proof.
  rewrite 2 map_is_typed_iff_fmap_eq.
  intros Hk.
  split.
  - intros (d & mD' & -> & HmD't & -> & ->)%(fmap_insert_inv _ _ _ _ _ Hk).
    rewrite lookup_insert.
    split; [reflexivity|].
    now rewrite delete_insert by done.
  - intros [HmDk <-].
    rewrite fmap_delete.
    rewrite insert_delete; [easy|].
    now rewrite lookup_fmap.
Qed.

Lemma map_is_typed_insert_l_gen k t mT mD :
  map_is_typed ty (<[k := t]> mT) mD <->
  ty <$> mD !! k = Some t /\
  map_is_typed ty (delete k mT) (delete k mD).
Proof.
  destruct (mT !! k) as [mTk|] eqn:HmTk;
    [|now rewrite map_is_typed_insert_l, (delete_notin mT)].
  rewrite <- map_is_typed_insert_l by apply lookup_delete.
  f_equiv.
  now rewrite insert_delete_insert.
Qed.

Lemma map_is_typed_insert_l' k t mT mD :
  mT !! k = None ->
  map_is_typed ty (<[k := t]> mT) mD <->
  exists d mD', ty d = t /\ mD = <[k := d]> mD' /\
    mD' !! k = None /\
    map_is_typed ty mT mD'.
Proof.
  intros HmTk.
  rewrite map_is_typed_insert_l by easy.
  split.
  - destruct (mD !! k) as [d|] eqn:Hd; [|easy].
    cbn.
    intros [[= <-] Hty].
    exists d, (delete k mD).
    now rewrite insert_delete, lookup_delete by auto.
  - intros (d & mD' & <- & -> & HmD'k & Hty).
    now rewrite delete_insert, lookup_insert by auto.
Qed.

Lemma map_is_typed_insert_r k d mT mD :
  mD !! k = None ->
  map_is_typed ty mT (<[k := d]> mD) <->
  mT !! k = Some (ty d) /\
  map_is_typed ty (delete k mT) mD.
Proof.
  rewrite 2 map_is_typed_iff_fmap_eq.
  intros Hk.
  split.
  - rewrite fmap_insert.
    intros <-.
    rewrite delete_insert by now rewrite lookup_fmap, Hk.
    now split; [rewrite lookup_insert|].
  - rewrite fmap_insert.
    intros [HmTk ->].
    now apply insert_delete.
Qed.

Lemma map_is_typed_insert_2 k d t mT mD :
  ty d = t ->
  map_is_typed ty mT mD ->
  map_is_typed ty (<[k:=t]> mT) (<[k:=d]> mD).
Proof.
  intros Ht Hty k'.
  rewrite 2 lookup_insert_case.
  case_decide; [now f_equal/=|].
  apply Hty.
Qed.

Lemma map_is_subtyped_iff_restriction_is_typed mT mD :
  map_is_subtyped ty mT mD <->
  map_is_typed ty mT (filter (λ kv, is_Some (mT !! kv.1)) mD).
Proof.
  unfold map_is_subtyped, map_is_typed.
  setoid_rewrite map_lookup_filter.
  cbn.
  split.
  - intros Hst k.
    destruct (mT !! k) as [t|] eqn:Ht.
    + cbn.
      apply Hst in Ht as Htyd.
      destruct (mD !! k) as [d|] eqn:Hd; [|easy].
      cbn in Htyd.
      revert Htyd.
      intros [= <-].
      cbn.
      case_guard as HSome; [|now rewrite is_Some_alt in HSome].
      reflexivity.
    + cbn.
      destruct (mD !! k); [|reflexivity].
      cbn.
      case_guard as HSome; cbn; now rewrite is_Some_alt in HSome.
  - intros Hty.
    intros k t Hmt.
    specialize (Hty k).
    rewrite Hmt in Hty.
    rewrite <- Hty.
    destruct (mD !! k); [|reflexivity].
    cbn.
    clear Hty.
    case_guard as HSome; cbn; now rewrite is_Some_alt in HSome.
Qed.


Lemma map_is_subtyped_iff_submap_is_typed mT mD :
  map_is_subtyped ty mT mD <->
  exists mD', mD' ⊆ mD /\ map_is_typed ty mT mD'.
Proof.
  split.
  - intros Hst.
    eexists; split; [|apply map_is_subtyped_iff_restriction_is_typed; eauto].
    apply map_filter_subseteq.
  - intros (mD' & HmD' & Hty).
    intros k t Hmk.
    specialize (Hty k).
    rewrite Hmk in Hty.
    destruct (mD' !! k) as [d'|] eqn:Hd'; [|easy].
    cbn in Hty.
    pose proof (lookup_weaken _ _ _ _ Hd' HmD') as Hd''.
    rewrite Hd''.
    cbn.
    easy.
Qed.

Lemma map_is_typed_None k mT mD :
  map_is_typed ty mT mD ->
  mT !! k = None <-> mD !! k = None.
Proof.
  intros <-%map_is_typed_iff_fmap_eq.
  rewrite lookup_fmap.
  apply fmap_None.
Qed.


Lemma map_is_typed_None_l k mT mD :
  map_is_typed ty mT mD ->
  mT !! k = None -> mD !! k = None.
Proof.
  apply map_is_typed_None.
Qed.

Lemma map_is_typed_None_r k mT mD :
  map_is_typed ty mT mD ->
  mD !! k = None -> mT !! k = None.
Proof.
  apply map_is_typed_None.
Qed.

End typed_map.



Definition and2pair {A B} (ab : A /\ B) : A * B :=
  match ab with
  | conj a b => (a, b)
  end.
(* Enable using .1 and .2 notations for proj1 and proj2 *)
Coercion and2pair : and >-> prod.

Definition map_inverses `{Lookup A B MA, Lookup B A MB}
  (ma : MA) (mb : MB) : Prop :=
  forall a b, ma !! a = Some b <-> mb !! b = Some a.

Lemma map_inverses_insert_fresh `{FinMap A MA, FinMap B MB}
  (ma : MA B) (mb : MB A) a b :
  map_inverses ma mb ->
  ma !! a = None -> mb !! b = None ->
  map_inverses (<[a := b]> ma) (<[b := a]> mb).
Proof.
  intros Hab Hma Hmb a' b'.
  rewrite 2 lookup_insert_case.
  generalize (Hab a' b').
  case_decide as Ha; case_decide as Hb; subst; easy || naive_solver.
Qed.

(* TODO: Extend to gmap *)
Fixpoint Pmap_ne_dom_subseteqb
  {A B} (ma : Pmap_ne A) (mb : Pmap_ne B) : bool :=
  match ma with
  | PNode001 mar => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match mbr with
    | PNodes mbr => Pmap_ne_dom_subseteqb mar mbr
    | _ => false
    end)
  | PNode010 a => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match b with
    | Some _ => true
    | _ => false
    end)
  | PNode011 a mar => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match b, mbr with
    | Some _, PNodes mbr => Pmap_ne_dom_subseteqb mar mbr
    | _, _ => false
    end)
  | PNode100 mal => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match mbl with
    | PNodes mbl => Pmap_ne_dom_subseteqb mal mbl
    | _ => false
    end)
  | PNode101 mal mar => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match mbl, mbr with
    | PNodes mbl, PNodes mbr =>
      if Pmap_ne_dom_subseteqb mal mbl then
        Pmap_ne_dom_subseteqb mar mbr
      else false
    | _, _ => false
    end)
  | PNode110 mal a => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match mbl, b with
    | PNodes mbl, Some _ => Pmap_ne_dom_subseteqb mal mbl
    | _, _ => false
    end)
  | PNode111 mal a mar => pmap.Pmap_ne_case mb (fun mbl b mbr =>
    match mbl, b, mbr with
    | PNodes mbl, Some _, PNodes mbr =>
      if Pmap_ne_dom_subseteqb mal mbl then
        Pmap_ne_dom_subseteqb mar mbr
      else false
    | _, _, _ => false
    end)
  end.

Definition Pmap_dom_subseteqb
  {A B} (ma : Pmap A) (mb : Pmap B) : bool :=
  match ma with
  | PEmpty => true
  | PNodes ma => match mb with
    | PNodes mb => Pmap_ne_dom_subseteqb ma mb
    | _ => false
    end
  end.


Lemma forall_positive {P : positive -> Prop} :
  (forall p, P p) <->
  P xH /\ (forall p, P (xO p)) /\ (forall p, P (xI p)).
Proof.
  split; [auto|].
  intros (?&?&?) []; auto.
Qed.

Lemma is_Some_None_iff {A} : @is_Some A None <-> False.
Proof.
  split; now intros [].
Qed.

Lemma is_Some_Some_iff {A} a : @is_Some A (Some a) <-> True.
Proof.
  easy.
Qed.


Lemma False_impl {P} : (False -> P) <-> True.
Proof.
  easy.
Qed.

Lemma impl_True {A} : (A -> True) <-> True.
Proof.
  easy.
Qed.

Lemma True_impl {A} : (True -> A) <-> A.
Proof.
  tauto.
Qed.

Lemma lazy_andb_True (b c : bool) : Is_true (if b then c else false) <-> b /\ c.
Proof.
  now destruct b, c.
Qed.

Lemma Pmap_ne_not_empty {A} (m : Pmap_ne A) : ~ (forall p, ~ (is_Some (m !! p))).
Proof.
  intros HF.
  now destruct (pmap.Pmap_ne_lookup_not_None m) as
    (p & []%not_eq_None_Some%HF).
Qed.

Local Lemma Pmap_ne_not_empty_alt {A B} (m : Pmap_ne A) :
  ~ (forall p, is_Some (m !! p) -> @is_Some B None).
Proof.
  setoid_rewrite is_Some_None_iff.
  apply Pmap_ne_not_empty.
Qed.

Lemma Pmap_ne_dom_subseteqb_correct {A B} (ma : Pmap_ne A) (mb : Pmap_ne B) :
  Pmap_ne_dom_subseteqb ma mb <->
    forall i, is_Some (ma !! i) -> is_Some (mb !! i).
Proof.
  revert mb; induction ma; intros mb; cbn.
  - rewrite forall_positive; cbn.
    setoid_rewrite is_Some_None_iff.
    setoid_rewrite False_impl.
    destruct mb; cbn;
    first [split; [exact (False_rect _)|intros; destruct_and!;
      eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite IHma; easy].
  - rewrite forall_positive; cbn.
    setoid_rewrite is_Some_None_iff.
    setoid_rewrite False_impl.
    rewrite is_Some_Some_iff.
    rewrite is_Some_alt.
    destruct mb; cbn; easy.
  - rewrite forall_positive; cbn.
    setoid_rewrite is_Some_None_iff.
    setoid_rewrite False_impl.
    rewrite is_Some_Some_iff.
    rewrite is_Some_alt.
    destruct mb; cbn;
    (* destruct mb; cbn;  *)
    first [easy | split; [exact (False_rect _)|intros; destruct_and!;
      eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite IHma; easy].
  - rewrite forall_positive; cbn.
    setoid_rewrite is_Some_None_iff.
    setoid_rewrite False_impl.
    destruct mb; cbn;
    first [split; [exact (False_rect _)|intros; destruct_and!;
      eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite IHma; easy].
  - rewrite forall_positive; cbn.
    rewrite is_Some_None_iff.
    rewrite False_impl.
    destruct mb; cbn;
    first [split; [exact (False_rect _)|intros; destruct_and!;
      eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite lazy_andb_True, IHma1, IHma2; tauto].
  - rewrite forall_positive; cbn.
    setoid_rewrite is_Some_None_iff.
    setoid_rewrite False_impl.
    rewrite is_Some_Some_iff, True_impl, is_Some_alt.
    destruct mb; cbn;
    first [easy | split; [exact (False_rect _)|intros; destruct_and!;
      easy || eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite IHma; easy].
  - rewrite forall_positive; cbn.
    rewrite is_Some_Some_iff, True_impl, is_Some_alt.
    destruct mb; cbn;
    first [easy | split; [exact (False_rect _)|intros; destruct_and!;
      easy || eapply Pmap_ne_not_empty_alt; eassumption] |
      rewrite lazy_andb_True, IHma1, IHma2; tauto].
Qed.


Lemma Pmap_dom_subseteqb_correct_impl {A B} (ma : Pmap A) (mb : Pmap B) :
  Pmap_dom_subseteqb ma mb <->
    forall i, is_Some (ma !! i) -> is_Some (mb !! i).
Proof.
  unfold Pmap_lookup, lookup.
  destruct ma; [split; [now intros ? ? []|easy]|destruct mb]; cbn.
  - split; [easy|].
    apply Pmap_ne_not_empty_alt.
  - apply Pmap_ne_dom_subseteqb_correct.
Qed.

Lemma Pmap_dom_subseteqb_correct {A B} (ma : Pmap A) (mb : Pmap B) :
  Pmap_dom_subseteqb ma mb <->
    dom ma ⊆ dom mb.
Proof.
  rewrite Pmap_dom_subseteqb_correct_impl.
  apply forall_iff; intros p.
  now rewrite 2 elem_of_dom.
Qed.

Lemma Pmap_dom_subseteqb_correct' {A B} (ma : Pmap A) (mb : Pmap B) :
  if (Pmap_dom_subseteqb ma mb) then
    dom ma ⊆ dom mb
  else
    ~ dom ma ⊆ dom mb.
Proof.
  generalize (Pmap_dom_subseteqb_correct ma mb); now case_match; naive_solver.
Qed.


#[global] Instance Pmap_dom_subseteq_dec {A B} (ma : Pmap A) (mb : Pmap B) :
  Decision (dom ma ⊆ dom mb) :=
  match Pmap_dom_subseteqb ma mb as b return ((if b then _ else _ :> Prop) -> _) with
  | true => left
  | false => right
  end (Pmap_dom_subseteqb_correct' ma mb).

Local Lemma dom_Pset (ma : Pset) : dom (ma.(mapset.mapset_car)) = ma.
Proof.
  destruct ma as [ma]; cbn.
  unfold dom, Pmap_dom, mapset.mapset_dom.
  f_equal.
  etransitivity; [|apply map_fmap_id].
  apply map_fmap_ext.
  now intros ? [].
Qed.

Notation Pset_subseteqb ma mb :=
  (Pmap_dom_subseteqb ma.(mapset.mapset_car) mb.(mapset.mapset_car)).

Lemma Pset_subseteqb_correct (ma : Pset) (mb : Pset) :
  Pset_subseteqb ma mb <->
    ma ⊆ mb.
Proof.
  rewrite Pmap_dom_subseteqb_correct.
  rewrite 2 dom_Pset.
  reflexivity.
Qed.

Lemma Pset_subseteqb_correct' (ma : Pset) (mb : Pset) :
  if Pset_subseteqb ma mb then
    ma ⊆ mb
  else
    ~ ma ⊆ mb.
Proof.
  (* destruct ma as [ma], mb as [mb].  *)
  cbn.
  pose proof (Pmap_dom_subseteqb_correct'
    ma.(mapset.mapset_car) mb.(mapset.mapset_car)) as Hen.
  rewrite 2 dom_Pset in Hen.
  apply Hen.
Qed.

#[global] Instance Pset_subseteq_dec (ma : Pset) (mb : Pset) :
  Decision (ma ⊆ mb) :=
  match Pset_subseteqb ma mb
    as b return ((if b then _ else _ :> Prop) -> _) with
  | true => left
  | false => right
  end (Pset_subseteqb_correct' ma mb).


(*

Fixpoint Pmap_ne_relation_dec {A B} (P : positive -> A -> B -> Prop)
  (PA : positive -> A -> Prop) (PB : positive -> B -> Prop)
  `{HP : forall i a b, Decision (P i a b)}
  `{HPA : forall i a, Decision (PA i a)}
  `{HPB : forall i b, Decision (PB i b)}
  (ma : Pmap_ne A) : forall mb : Pmap_ne B, Decision (map_relation P PA PB ma mb) :=
  match ma with
  | PNode001 *)


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



Lemma imap_to_zip_with_seq {A B} (f : nat -> A -> B) (l : list A) :
  imap f l = zip_with f (seq 0 (length l)) l.
Proof.
  revert f; induction l; intros f; [reflexivity|].
  cbn.
  f_equal.
  rewrite IHl, <- fmap_S_seq, zip_with_fmap_l.
  reflexivity.
Qed.

Lemma fmap_zip_with {A B C D} (f : A -> B -> C) (g : C -> D) l l' :
  g <$> zip_with f l l' = zip_with (λ a b, g (f a b)) l l'.
Proof.
  revert l'; induction l; [reflexivity|].
  intros []; [reflexivity|].
  cbn.
  congruence.
Qed.

Lemma fmap_lookup_total_seq `{Inhabited A} (l : list A) :
  (l !!!.) <$> seq 0 (length l) = l.
Proof.
  induction l; [reflexivity|].
  cbn.
  f_equal.
  rewrite <- fmap_S_seq, <- list_fmap_compose.
  apply IHl.
Qed.

Lemma zip_fmap_l {A B C} (f : A -> B) l (l' : list C) :
  zip (f <$> l) l' = prod_map f id <$> zip l l'.
Proof.
  rewrite fmap_zip_with, zip_with_fmap_l.
  reflexivity.
Qed.

Lemma zip_fmap_r {A B C} (f : B -> C) (l : list A) (l' : list B) :
  zip l (f <$> l') = prod_map id f <$> zip l l'.
Proof.
  rewrite fmap_zip_with, zip_with_fmap_r.
  reflexivity.
Qed.

Lemma perm_exists_perm_seq {A} (l l' : list A) :
  l ≡ₚ l' -> exists idxs, idxs ≡ₚ seq 0 (length l) /\
    imap pair l ≡ₚ zip idxs l'.
Proof.
  intros Hperm.
  induction Hperm.
  - exists [].
    cbn.
    split; reflexivity.
  - destruct IHHperm as (idxs & Hidxs & Hcorr).
    exists (0 :: (S <$> idxs))%nat.
    split.
    + cbn.
      rewrite Hidxs.
      rewrite fmap_S_seq.
      reflexivity.
    + cbn.
      f_equiv.
      transitivity ((prod_map S id) <$> imap pair l).
      * rewrite fmap_imap.
        apply eq_reflexivity.
        reflexivity.
      * rewrite Hcorr.
        rewrite zip_with_fmap_l.
        rewrite fmap_zip_with.
        reflexivity.
  - exists (1 :: 0 :: seq 2 (length l))%nat.
    split; [solve_Permutation|].
    cbn.
    rewrite imap_to_zip_with_seq, <- 2 fmap_S_seq, 2 zip_with_fmap_l.
    solve_Permutation.
  - destruct IHHperm1 as (idxs & Hidxs & Hmap),
      IHHperm2 as (idxs' & Hidxs' & Hmap').
    exists ((idxs !!!.) <$> idxs').
    split.
    + rewrite Hidxs'.
      replace (length l') with (length idxs). 2:{
        apply Permutation_length in Hidxs, Hidxs', Hperm1.
        rewrite length_seq in *.
        congruence.
      }
      rewrite fmap_lookup_total_seq.
      apply Hidxs.
    + rewrite Hmap.
      rewrite zip_fmap_l.
      rewrite <- Hmap'.
      rewrite imap_to_zip_with_seq.
      rewrite <- zip_fmap_l.
      replace (length l') with (length idxs). 2:{
        apply Permutation_length in Hidxs, Hidxs', Hperm1.
        rewrite length_seq in *.
        congruence.
      }
      now rewrite fmap_lookup_total_seq.
Qed.


Definition enumerate {A} (l : list A) : list (nat * A) :=
  imap pair l.

Lemma elem_of_enumerate {A} (l : list A) n a :
  (n, a) ∈ enumerate l <-> l !! n = Some a.
Proof.
  unfold enumerate.
  rewrite elem_of_lookup_imap.
  naive_solver.
Qed.


Lemma default_is_Some_ext_mor_gen {B} {R : relation B} (d d' : B)
  (mb mb' : option B) : R d d' ->
  (forall b, mb = Some b -> mb' = None -> R b d') ->
  (forall b', mb = None -> mb' = Some b' -> R d b') ->
  (forall b b', mb = Some b -> mb' = Some b' -> R b b') ->
  R (default d mb) (default d' mb').
Proof.
  destruct mb, mb'; cbn; eauto.
Qed.
Lemma default_is_Some_ext_mor {B} {R : relation B} (d d' : B)
  (mb mb' : option B) :
  (is_Some mb <-> is_Some mb') ->
  R d d' ->
  (forall b b', mb = Some b -> mb' = Some b' -> R b b') ->
  R (default d mb) (default d' mb').
Proof.
  intros HSome Hd HR.
  rewrite 2 is_Some_alt in HSome.
  destruct mb, mb'; cbn; naive_solver.
Qed.
Lemma not_elem_of_list_fmap {A B} (f : A -> B) (l : list A) (b : B) :
  b ∉ f <$> l <-> forall a, a ∈ l -> f a ≠ b.
Proof.
  rewrite elem_of_list_fmap.
  naive_solver.
Qed.
Lemma Permutation_swap_app_app {A} (l1 l2 l3 l4 : list A) :
  (l1 ++ l2) ++ (l3 ++ l4) ≡ₚ (l1 ++ l3) ++ (l2 ++ l4).
Proof.
  solve_Permutation.
Qed.


Lemma Forall_filter {A} (P Q : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  Forall Q (filter P l) <-> Forall (fun a => P a -> Q a) l.
Proof.
  induction l; [now split; constructor|].
  cbn.
  case_decide as HPa.
  - rewrite 2 Forall_cons, IHl. tauto.
  - rewrite Forall_cons, IHl. tauto.
Qed.

Lemma fmap_const {A B} (l : list A) (b : B) :
  const b <$> l = replicate (length l) b.
Proof.
  induction l; cbn; f_equal; assumption.
Qed.


Lemma length_list_filter_ext {A B} (P : A -> Prop) (Q : B -> Prop)
  `{HP : forall a, Decision (P a)} `{HQ : forall b, Decision (Q b)}
  (l : list A) (l' : list B) :
  Forall2 (λ a b, P a <-> Q b) l l' ->
  length (filter P l) = length (filter Q l').
Proof.
  intros Hall.
  induction Hall; [reflexivity|].
  cbn.
  unshelve (erewrite decide_ext by eassumption); [auto|].
  case_decide; cbn; f_equal; easy.
Qed.



Lemma list_map_fmap :
  @map = @fmap _ list_fmap.
Proof. reflexivity. Qed.
(* TODO: Name here seems backwards, but follows list_fmap_bind... *)
Lemma list_bind_fmap {A B C} (f : A -> list B) (g : B -> C) l :
  g <$> (l ≫= f) = l ≫= (λ a, g <$> f a).
Proof.
  induction l; [reflexivity|].
  cbn.
  now rewrite fmap_app, IHl.
Qed.
Lemma list_bind_flat_map :
  list_bind = flat_map.
Proof. reflexivity. Qed.
Lemma list_bind_assoc {A B C} (f : A -> list B) (g : B -> list C) l :
  (l ≫= f) ≫= g = l ≫= mbind g ∘ f.
Proof.
  induction l; [reflexivity|cbn].
  now rewrite bind_app, IHl.
Qed.
Lemma bind_pointwise_Permutation_strong {A B} (f g : A -> list B) l l' :
  (∀ a, a ∈ l -> f a ≡ₚ g a) ->
  l ≡ₚ l' ->
  l ≫= f ≡ₚ l' ≫= g.
Proof.
  intros Hfg <-.
  rewrite <- Forall_forall in Hfg.
  induction Hfg; cbn; [reflexivity|].
  f_equiv; auto.
Qed.
Lemma list_bind_nil_r {A B} (lA : list A) :
  lA ≫= (λ _, @nil B) = [].
Proof.
  now induction lA.
Qed.
Lemma list_bind_nil_r' {A B} (lA : list A) f :
  (∀ a, a ∈ lA -> f a = @nil B) ->
  lA ≫= f = [].
Proof.
  rewrite <- Forall_forall.
  intros Hall.
  induction Hall; [reflexivity|].
  cbn.
  now rewrite IHHall, app_nil_r.
Qed.
Lemma list_bind_cons_r {A B} l (f : A -> B) (g : A -> list B) :
  l ≫= (λ x, f x :: g x) ≡ₚ (f <$> l) ++ l ≫= g.
Proof.
  induction l; cbn; [|rewrite IHl]; solve_Permutation.
Qed.
Lemma list_bind_singleton_r {A B} l (f : A -> B) :
  l ≫= (λ x, [f x]) = (f <$> l).
Proof.
  reflexivity.
Qed.
Lemma list_bind_app_r {A B} l (f g : A -> list B) :
  l ≫= (λ x, f x ++ g x) ≡ₚ (l ≫= f) ++ l ≫= g.
Proof.
  induction l; cbn; [|rewrite IHl]; solve_Permutation.
Qed.
Lemma list_bind_comm {A B C} (f : A -> B -> list C) l l' :
  (l ≫= (λ a, l' ≫= λ b, f a b)) ≡ₚ
  (l' ≫= (λ b, l ≫= λ a, f a b)).
Proof.
  induction l; [cbn; now rewrite list_bind_nil_r|cbn].
  now rewrite list_bind_app_r, IHl.
Qed.


Add Parametric Morphism {A B} : fmap with signature
  pointwise_relation A (@eq B) ==> (@eq (list A)) ==> (@eq (list B)) as list_fmap_mor.
Proof.
  intros; unfold pointwise_relation;
  apply list_fmap_ext; auto.
Qed.


Definition set_Forall2 `{ElemOf A C} (R : relation A) (s : C) : Prop :=
  forall a a', a ∈ s -> a' ∈ s -> R a a'.

Add Parametric Morphism `{ElemOf A C} : (@set_Forall2 A C _) with signature
  pointwise_relation A (pointwise_relation A iff) ==> (≡) ==> iff as set_Forall2_ext.
Proof.
  intros R R' HR s s' Hs.
  apply forall_iff; intros a.
  apply forall_iff; intros a'.
  rewrite Hs.
  apply forall_iff; intros Ha.
  apply forall_iff; intros Ha'.
  apply HR.
Qed.

Add Parametric Morphism `{ElemOf A C} : (@set_Forall2 A C _) with signature
  pointwise_relation A (pointwise_relation A impl) --> (⊆) ==> flip impl as set_Forall2_mono.
Proof.
  intros R R' HR s s' Hs.
  unfold impl, set_Forall2.
  intros Has a a' Ha Ha'.
  apply HR.
  now apply Has; apply Hs.
Qed.

Lemma set_Forall2_list_to_set `{SemiSet A C} (R : relation A) (l : list A) :
  set_Forall2 R (list_to_set l :> C) <-> ForallPairs R l.
Proof.
  unfold set_Forall2, ForallPairs.
  setoid_rewrite elem_of_list_to_set.
  now setoid_rewrite elem_of_list_In.
Qed.
(* FIXME: Move *)
Lemma ForallPairs_forall {A} {R : relation A} (l : list A) :
  ForallPairs R l <-> forall a b, a ∈ l -> b ∈ l -> R a b.
Proof.
  unfold ForallPairs.
  now setoid_rewrite elem_of_list_In.
Qed.
Section invfun.
Context `{Inhabited (B -> A), EqDecision B} .
Definition invfun (f : A -> B) (dom : list A) : B -> A :=
  λ b, default (inhabitant b) (ia ← list_find (eq b) (f <$> dom); dom !! ia.1).
Lemma invfun_rinv (f : A -> B) (dom : list A) b :
  b ∈ f <$> dom ->
  f (invfun f dom b) = b.
Proof.
  intros Hb.
  unfold invfun.
  destruct (list_find_elem_of (eq b) (f <$> dom) b Hb eq_refl)
    as [ia Hia].
  rewrite Hia.
  cbn.
  destruct ia as [i b'].
  apply list_find_Some in Hia.
  rewrite list_lookup_fmap in Hia.
  cbn.
  destruct Hia as (Hlook & <- & ?).
  destruct (dom !! i) in *; cbn in *; congruence.
Qed.
Lemma invfun_linv (f : A -> B) (dom : list A) a :
  (ForallPairs (λ a a', f a = f a' -> a = a') dom) ->
  a ∈ dom ->
  invfun f dom (f a) = a.
Proof.
  intros Hinj Ha.
  unfold invfun.
  apply (elem_of_list_fmap_1 f) in Ha as Hfa.
  destruct (list_find_elem_of (eq (f a)) (f <$> dom) _ Hfa eq_refl)
    as [ia Hia].
  rewrite Hia.
  cbn.
  destruct ia as [i b'].
  apply list_find_Some in Hia.
  rewrite list_lookup_fmap in Hia.
  cbn.
  destruct Hia as (Hlook & <- & ?).
  destruct (dom !! i) as [a'|] eqn:Ha' in *; [cbn in *|easy].
  apply ((ForallPairs_forall _).1 Hinj).
  - by apply elem_of_list_lookup_2 in Ha'.
  - easy.
  - congruence.
Qed.
Lemma invfun_inj (f : A -> B) (dom : list A) :
  ForallPairs (λ a a', f a = f a' -> a = a') dom ->
  ForallPairs (λ a a', invfun f dom a = invfun f dom a' -> a = a') (f <$> dom).
Proof.
  intros Hinj.
  rewrite ForallPairs_forall.
  intros ? ? (a & -> & Ha)%elem_of_list_fmap (b & -> & Hb)%elem_of_list_fmap.
  rewrite 2 invfun_linv by easy; now intros ->.
Qed.
End invfun.
Lemma set_map_list_to_set `{FinSet A SA, SemiSet B SB}
  (f : A -> B) (l : list A) :
  set_map f (list_to_set l :> SA) ≡@{SB} list_to_set (f <$> l).
Proof.
  intros x.
  rewrite elem_of_map.
  setoid_rewrite elem_of_list_to_set.
  symmetry; apply elem_of_list_fmap.
Qed.
Lemma set_map_list_to_set_L `{FinSet A SA, SemiSet B SB, !LeibnizEquiv SB}
  (f : A -> B) (l : list A) :
  set_map f (list_to_set l :> SA) =@{SB} list_to_set (f <$> l).
Proof.
  unfold_leibniz; apply set_map_list_to_set.
Qed.
Lemma kmap_id `{FinMap K M} {A} (m : M A) :
  kmap id m = m.
Proof.
  apply map_eq.
  intros.
  apply (lookup_kmap id m i).
Qed.
Lemma map_Forall_inj_iff `{FinMap K M} {A K'}
  (f : K -> K') (m : M A) :
  map_Forall (λ i _, map_Forall (λ j _, f i = f j -> i = j) m) m <->
  ForallPairs (λ i j, f i = f j -> i = j) (map_to_list m).*1.
Proof.
  unfold map_Forall; rewrite ForallPairs_forall.
  split.
  - intros Hinj _ _ ([a x] & [= ->] & Ha%elem_of_map_to_list)%elem_of_list_fmap
    ([b y] & [= ->] & Hb%elem_of_map_to_list)%elem_of_list_fmap.
    eauto.
  - intros Hinj a x Ha%elem_of_map_to_list%(elem_of_list_fmap_1 fst)
      b y Hb%elem_of_map_to_list%(elem_of_list_fmap_1 fst).
    now apply Hinj.
Qed.


Lemma dif_dist {P Q} {A B} (f : A -> B) (b : {P} + {Q}) (x y : A) :
  f (if b then x else y) = if b then f x else f y.
Proof.
  now destruct b.
Qed.


(* FIXME: Move *)
Lemma rev_reverse {A} (l : list A) :
  rev l = reverse l.
Proof.
  induction l; [reflexivity|].
  now rewrite reverse_cons, <- IHl.
Qed.

Lemma rev_append_reverse {A} (l l' : list A) :
  rev_append l l' = reverse l ++ l'.
Proof.
  now rewrite rev_append_rev, rev_reverse.
Qed.

Lemma union_eq_l {A} (ma ma' : option A) :
  is_Some ma -> ma ∪ ma' = ma.
Proof.
  now destruct ma, ma'; intros [].
Qed.


Lemma list_fmap_to_bind {A B} (f : A -> B) (l : list A) :
  f <$> l = x ← l; [f x].
Proof.
  now rewrite <- list_bind_singleton_r.
Qed.


Lemma list_bind_cprod {A B C} (f : A * B -> list C) l k :
  cprod l k ≫= f = l ≫= λ x, k ≫= λ y, f (x, y).
Proof.
  unfold list_cprod, cprod.
  rewrite list_bind_assoc.
  apply list_bind_ext; [|reflexivity].
  intros a.
  cbn.
  rewrite list_fmap_bind.
  reflexivity.
Qed.

Lemma list_bind_to_cprod {A B C} (f : A -> B -> list C) l k :
  (l ≫= λ x, k ≫= λ y, f x y) =
  cprod l k ≫= uncurry f.
Proof.
  rewrite list_bind_cprod; reflexivity.
Qed.

Notation vzip := (vzip_with pair).

Lemma vzip_with_map_l {n} {A B C D} (f : B -> C -> D) (g : A -> B)
  (v : vec A n) (w : vec C n) :
  vzip_with f (vmap g v) w =
  vzip_with (f ∘ g) v w.
Proof.
  vec_double_ind v w.
  - done.
  - cbn.
    congruence.
Qed.

Lemma vzip_with_map_r {n} {A B C D} (f : A -> C -> D) (g : B -> C)
  (v : vec A n) (w : vec B n) :
  vzip_with f v (vmap g w) =
  vzip_with (λ a b, f a (g b)) v w.
Proof.
  vec_double_ind v w.
  - done.
  - cbn.
    congruence.
Qed.

Lemma vzip_with_map {n} {A B C D E} (f : B -> D -> E) (g : A -> B) (h : C -> D)
  (v : vec A n) (w : vec C n) :
  vzip_with f (vmap g v) (vmap h w) =
  vzip_with (λ a b, f (g a) (h b)) v w.
Proof.
  vec_double_ind v w.
  - done.
  - cbn.
    congruence.
Qed.

Lemma vzip_with_app `(f : A -> B -> C) {n m} (v w : vec _ n)
  (v' w' : vec _ m) :
    vzip_with f (v +++ v') (w +++ w') =
    vzip_with f v w +++ vzip_with f v' w'.
Proof.
  vec_double_ind v w; [done|].
  cbn.
  congruence.
Qed.

Lemma vmap_zip_with {A B C D} (f : A -> B -> C) (g : C -> D)
  {n} (v : vec A n) (w : vec B n) :
  vmap g (vzip_with f v w) = vzip_with (λ a b, g (f a b)) v w.
Proof.
  vec_double_ind v w; cbn; congruence.
Qed.

Lemma vzip_map_l {A B C} (f : A -> B) {n} (v : vec A n) (w : vec C n) :
  vzip (vmap f v) w = vmap (prod_map f id) $ vzip v w.
Proof.
  vec_double_ind v w; cbn; congruence.
Qed.

Lemma vzip_map_r {A B C} (f : B -> C) {n} (v : vec A n) (w : vec B n) :
  vzip v (vmap f w) = vmap (prod_map id f) $ vzip v w.
Proof.
  vec_double_ind v w; cbn; congruence.
Qed.

Lemma vzip_map {A B C D} (f : A -> B) (g : C -> D)
  {n} (v : vec A n) (w : vec C n) :
  vzip (vmap f v) (vmap g w) = vmap (prod_map f g) $ vzip v w.
Proof.
  vec_double_ind v w; cbn; congruence.
Qed.



Lemma delete_list_to_map `{FinMap K M} {A}
  (l : list (K * A)) k :
  delete k (list_to_map l :> M A) =
  list_to_map (filter (λ ka, ka.1 ≠ k) l).
Proof.
  induction l; [apply delete_empty|].
  cbn.
  case_decide as Hak.
  - cbn.
    setoid_rewrite <- IHl.
    now apply delete_insert_ne.
  - rewrite Hak.
    rewrite delete_insert_delete.
    apply IHl.
Qed.



Lemma kmap_list_to_map `{FinMap K1 M1, FinMap K2 M2} {A} f `{Hf : !Inj eq eq f}
  (l : list (K1 * A)) :
  kmap f (list_to_map l :> M1 A) =@{M2 A}
    list_to_map (fmap (prod_map f id) l).
Proof.
  unfold kmap.
  induction l as [l IHl] using (Nat.measure_induction _ length).
  destruct l; [cbn; now rewrite map_to_list_empty|].
  cbn.
  rewrite <- insert_delete_insert.
  erewrite list_to_map_proper.
  2: {
    rewrite fsts_prod_map.
    apply (NoDup_fmap _).
    apply NoDup_fst_map_to_list.
  }
  2:{
    rewrite map_to_list_insert by now rewrite lookup_delete.
    cbn.
    done.
  }
  cbn.
  symmetry.
  rewrite <- insert_delete_insert.
  change ((prod_map _ _ _).1) with (f p.1).
  rewrite delete_list_to_map.
  rewrite list_filter_fmap.
  unfold compose.
  rewrite delete_list_to_map.
  f_equal.
  rewrite IHl by now cbn; apply -> Nat.succ_le_mono; apply length_filter.
  f_equal.
  f_equal.
  apply list_filter_iff.
  intros []; cbn.
  split; [now intros ? ->|].
  now intros ? ->%(inj _).
Qed.



Lemma fmap_elements `{FinSet A SA, FinSet B SB} (f : A -> B) `{!Inj eq eq f} (X : SA) :
  f <$> elements X ≡ₚ
  elements (set_map f X :> SB).
Proof.
  apply NoDup_Permutation;
  [apply (NoDup_fmap_2 _ _), NoDup_elements|apply NoDup_elements|].
  set_solver.
Qed.


Lemma fmap_to_map_imap `{FinMap K M} `(f : A -> B) (m : M A) :
  f <$> m =@{M B} map_imap (λ _ a, Some (f a)) m.
Proof.
  apply map_eq.
  intros k.
  rewrite lookup_fmap, map_lookup_imap.
  now destruct (m !! k).
Qed.
Lemma map_fmap_imap `{FinMap K M} `(f : K -> A -> option B) `(g : B -> C) (m : M A) :
  g <$> map_imap f m =@{M C} map_imap (λ k a, g <$> (f k a)) m.
Proof.
  rewrite fmap_to_map_imap, map_imap_compose.
  reflexivity.
Qed.
Lemma elements_union `{FinSet A SA} (X Y : SA) :
  elements (X ∪ Y) ≡ₚ elements X ++ elements (Y ∖ X).
Proof.
  assert (RelDecision (∈@{SA})) by apply elem_of_dec_slow.
  rewrite <- elements_disj_union by set_solver.
  apply elements_proper.
  intros x.
  destruct_decide (decide (x ∈ X));
  set_solver.
Qed.
Lemma filter_elements `{FinSet A SA} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (X : SA) :
  filter P (elements X) ≡ₚ elements (filter P X).
Proof.
  apply NoDup_Permutation;
  [apply NoDup_filter, NoDup_elements|apply NoDup_elements|].
  intros x.
  now rewrite elem_of_list_filter, 2 elem_of_elements, elem_of_filter.
Qed.



#[export] Instance fn_empty {A} : Empty (A -> A) := id.
#[export] Instance fn_singleton `{EqDecision A} : SingletonM A A (A -> A) :=
  fun a b => fun c => if decide (a = c) then b else c.

Lemma fn_lookup_singleton `{EqDecision A} (a b : A) :
  {[a := b]} a = b.
Proof.
  now apply decide_True.
Qed.

Lemma fn_lookup_singleton_ne `{EqDecision A} (a b c : A) : a <> c ->
  {[a := b]} c = c.
Proof.
  apply decide_False.
Qed.

Lemma fn_lookup_singleton_case `{EqDecision A} (a b c : A) :
  {[a := b]} c = if decide (a = c) then b else c.
Proof.
  reflexivity.
Qed.

Lemma fn_lookup_insert_to_compose `{EqDecision A} (a b : A) (f : A -> A) (c : A) :
  f b = b ->
  <[a := b]> f c =
  f ({[a:=b]} c).
Proof.
  unfold insert, fn_insert; cbn.
  rewrite fn_lookup_singleton_case.
  case_decide; easy.
Qed.


Lemma fn_lookup_insert_case `{EqDecision A} (a b : A) (f : A -> A) (c : A) :
  <[a := b]> f c =
  if decide (a = c) then b else f c.
Proof.
  reflexivity.
Qed.
Lemma set_map_fn_singleton `{FinSet A SA, EqDecision A, !RelDecision (∈@{SA})}
  (a b : A) (X : SA) :
  set_map {[a := b]} X ≡
  X ∖ {[a]} ∪ if decide (a ∈ X) then {[b]} else ∅.
Proof.
  set_unfold.
  setoid_rewrite fn_lookup_singleton_case.
  intros x.
  split.
  - intros (y & -> & Hy).
    case_decide as Hay.
    + subst y.
      rewrite decide_True by easy.
      right.
      now apply elem_of_singleton.
    + now left.
  - intros [[Hx Hxa]|Hxdec].
    + exists x.
      now rewrite decide_False.
    + case_decide as Ha; [|now apply elem_of_empty in Hxdec].
      apply elem_of_singleton in Hxdec.
      subst b.
      exists a.
      now rewrite decide_True.
Qed.
Lemma set_map_fn_singleton_L `{FinSet A SA, EqDecision A, !RelDecision (∈@{SA}),
  !LeibnizEquiv SA}
  (a b : A) (X : SA) :
  set_map {[a := b]} X =
  X ∖ {[a]} ∪ if decide (a ∈ X) then {[b]} else ∅.
Proof.
  unfold_leibniz.
  apply set_map_fn_singleton.
Qed.
Lemma set_omap_None `{FinSet A SA, SemiSet B SB} (X : SA) :
  set_omap (fun _ => None) X ≡@{SB} ∅.
Proof.
  set_solver.
Qed.
Lemma set_omap_None_strong `{FinSet A SA, SemiSet B SB} (f : A -> option B)
  (X : SA) : (forall a, a ∈ X -> f a = None) ->
  set_omap f X ≡@{SB} ∅.
Proof.
  intros Hf.
  set_unfold.
  intros x (? & ? & Heq%Hf).
  now rewrite Heq in *.
Qed.
Lemma set_omap_Some `{FinSet A SA, SemiSet A SB} (X : SA) :
  set_omap Some X ≡@{SB} set_map id X.
Proof.
  set_solver.
Qed.

Lemma and_iff_from_l {P Q R S} :
  (P <-> Q) -> (P -> Q -> (R <-> S)) ->
  P /\ R <-> Q /\ S.
Proof.
  tauto.
Qed.

Lemma and_iff_from_r {P Q R S} :
  (P <-> Q) -> (P -> Q -> (R <-> S)) ->
  R /\ P <-> S /\ Q.
Proof.
  tauto.
Qed.

Lemma set_omap_Some_strong `{FinSet A SA, SemiSet A SB} (f : A -> option A)
  (X : SA) : (forall a, a ∈ X -> f a = Some a) ->
  set_omap f X ≡@{SB} set_map id X.
Proof.
  intros Hf.
  set_unfold.
  intros x.
  apply exists_iff; intros a.
  apply and_iff_from_r; [done|].
  intros ->%Hf _.
  split; congruence.
Qed.


Lemma kmap_insert_first_key `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) `(m : M1 A) (i : K1) a :
    m !! i = None ->
    map_first_key (<[i:=a]> m) i ->
    kmap f (<[i:=a]> m) = <[f i:=a]> (kmap f m :> M2 A).
Proof.
  intros Hmi Hi.
  unfold kmap.
  rewrite map_to_list_insert_first_key by easy.
  reflexivity.
Qed.

Lemma lookup_kmap_full_gen `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) `(m : M1 A) (i : K1) :
    map_Forall (λ j _, map_Forall (λ k _, f j = f k -> j = k) m) m ->
    (forall j, m !! j = None -> map_Forall (λ k _, f k ≠ f j) m) ->
    (kmap f m :> M2 A) !! f i = m !! i.
Proof.
  intros Hinj Hsafe;
  revert Hinj Hsafe i;
  induction m as [|i a m Hmi Hfirst IHm] using map_first_key_ind;
  [now intros; rewrite kmap_empty, 2 lookup_empty|].
  rewrite 2 map_Forall_insert by easy.
  intros [[_ Hinj_i] Hinj].
  setoid_rewrite map_Forall_insert; [|easy].
  setoid_rewrite lookup_insert_None.
  intros Hsafe i'.
  rewrite kmap_insert_first_key by easy.
  rewrite lookup_insert_case.
  case_decide as Hfii'.
  - enough (i = i') by now subst; rewrite lookup_insert.
    destruct (m !! i') as [mi'|] eqn:Hmi'.
    + now apply (Hinj_i i' mi' Hmi').
    + apply dec_stable.
      intros Hne.
      specialize (Hsafe _ (conj Hmi' Hne)).
      easy.
  - rewrite IHm.
    + rewrite lookup_insert_ne; [easy|].
      now intros ->.
    + apply (map_Forall_impl _ _ _ Hinj).
      intros j _.
      rewrite map_Forall_insert by easy.
      easy.
    + intros j Hj.
      destruct_decide (decide (j = i)) as Hji.
      * subst.
        intros j x Hmj.
        symmetry.
        apply Hinj_i in Hmj as Hfij.
        now intros ->%Hfij; congruence.
      * now apply Hsafe.
Qed.

Lemma lookup_kmap_Some_2 `{FinMap K1 M1, FinMap K2 M2} {A}
  (f : K1 -> K2) (m : M1 A) (j : K2) x :
  (kmap f m :> M2 A) !! j = Some x ->
  exists i : K1, m !! i = Some x /\ f i = j.
Proof.
  induction m as [|j' a m Hmj Hfirst IHm] using map_first_key_ind;
    [now rewrite kmap_empty, lookup_empty|].
  rewrite kmap_insert_first_key by easy.
  rewrite lookup_insert_Some.
  intros [[Hj' <-] | [Hj (i & Hmi & Hfi)%IHm]].
  - exists j'.
    now rewrite lookup_insert.
  - exists i.
    split; [|easy].
    rewrite lookup_insert_ne by congruence.
    easy.
Qed.

Lemma lookup_kmap_Some_1_full_gen `{FinMap K1 M1, FinMap K2 M2} {A}
  (f : K1 -> K2) (m : M1 A) (i : K1) x :
  m !! i = Some x ->
  map_Forall (λ j _, f i = f j -> i = j) m ->
  (kmap f m :> M2 A) !! f i = Some x.
Proof.
  induction m as [|j' a m Hmj Hfirst IHm] using map_first_key_ind;
    [now rewrite lookup_empty|].
  rewrite lookup_insert_case.
  case_decide as Hj'.
  - intros [= <-] _.
    subst j'.
    rewrite kmap_insert_first_key by easy.
    now rewrite lookup_insert.
  - intros Hmi.
    rewrite map_Forall_insert by easy.
    intros [Hij' Hall].
    specialize (IHm Hmi Hall).
    rewrite kmap_insert_first_key by easy.
    now rewrite lookup_insert_ne by now intros ?%eq_sym%Hij'; congruence.
Qed.

Lemma lookup_kmap_Some_full_gen `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) `(m : M1 A) (j : K2) a :
    map_Forall (λ j _, map_Forall (λ k _, f j = f k -> j = k) m) m ->
    (* (forall j, m !! j = None -> map_Forall (λ k _, f k ≠ f j) m) -> *)
    (kmap f m :> M2 A) !! j = Some a <->
    exists i, m !! i = Some a /\ f i = j.
Proof.
  intros Hinj.
  split; [apply lookup_kmap_Some_2|].
  intros (i & Hmi & <-).
  apply lookup_kmap_Some_1_full_gen; [easy|].
  apply (Hinj i a Hmi).
Qed.

Lemma lookup_kmap_Some_full_gen_dom `{FinMapDom K1 M1 SK1, FinMap K2 M2}
  (f : K1 -> K2) `(m : M1 A) (j : K2) a :
    set_Forall2 (λ i j, f i = f j -> i = j) (dom m :> SK1) ->
    (* (forall j, m !! j = None -> map_Forall (λ k _, f k ≠ f j) m) -> *)
    (kmap f m :> M2 A) !! j = Some a <->
    exists i, m !! i = Some a /\ f i = j.
Proof.
  intros Hinj.
  apply lookup_kmap_Some_full_gen.
  intros i ai Hai i' ai' Hai'.
  apply Hinj; apply elem_of_dom; eauto.
Qed.



Lemma NoDup_fmap_1_strong {A B} (f : A -> B) (l : list A) :
  NoDup (f <$> l) ->
  forall a b, a ∈ l -> b ∈ l -> f a = f b -> a = b.
Proof.
  rewrite NoDup_alt.
  intros Hdup a b
    (i & Ha)%elem_of_list_lookup (j & Hb)%elem_of_list_lookup Hfab.
  specialize (Hdup i j (f a)).
  rewrite 2 list_lookup_fmap in Hdup.
  tspecialize Hdup by now rewrite Ha.
  tspecialize Hdup by now rewrite Hb, Hfab.
  subst.
  congruence.
Qed.

Lemma NoDup_subseteq_same_length_Permutation {A} (l l' : list A) :
  NoDup l' -> l' ⊆ l -> length l' = length l ->
  l ≡ₚ l'.
Proof.
  intros Hl'; revert l;
  induction Hl' as [|a l' IHl']; [now intros []|].
  intros l Hl.
  specialize (Hl a ltac:(constructor)) as Hal.
  apply elem_of_list_split in Hal as (l1 & l2 & ->).
  specialize (IHHl' (l1 ++ l2)).
  tspecialize IHHl'.
  - intros b Hb.
    assert (b <> a) by congruence.
    specialize (Hl _ (elem_of_list_further _ _ _ Hb)).
    rewrite elem_of_app, elem_of_cons in Hl.
    rewrite elem_of_app.
    tauto.
  - simpl_list; cbn.
    intros Heq.
    rewrite <- IHHl' by now simpl_list; lia.
    solve_Permutation.
Qed.

Lemma map_Forall_list_to_map `{FinMap K M} {A} {P : K -> A -> Prop}
  (l : list (K * A)) :
  NoDup l.*1 ->
  map_Forall P (list_to_map l :> M A) <->
  Forall (uncurry P) l.
Proof.
  intros Hdup.
  induction l as [|(k, a) l IHl].
  - cbn.
    split; [|intros; apply map_Forall_empty].
    constructor.
  - cbn.
    rewrite fmap_cons, NoDup_cons in Hdup.
    destruct Hdup as [Hk Hdup].
    cbn in Hk.
    tspecialize IHl by easy.
    rewrite map_Forall_insert by now apply not_elem_of_list_to_map.
    now rewrite Forall_cons, IHl.
Qed.


Lemma kmap_list_to_map_eq_of_perm_NoDup `{FinMap K1 M1, FinMap K2 M2} {A}
  (f : K1 -> K2) (l : list (K1 * A)) (m : M2 A) :
  NoDup l.*1 ->
  prod_map f id <$> l ≡ₚ map_to_list m ->
  kmap f (list_to_map l) = m.
Proof.
  intros Hl Hfl.
  apply map_eq; intros i.
  apply option_eq.
  intros x.
  rewrite lookup_kmap_Some_full_gen. 2:{
    rewrite map_Forall_list_to_map by easy.
    rewrite Forall_forall.
    intros (k' & a') Hk'a'.
    cbn.
    rewrite map_Forall_list_to_map by easy.
    rewrite Forall_forall.
    intros (k'' & a'') Hk''a''.
    cbn.
    pose proof (NoDup_fst_map_to_list m) as Hm.
    rewrite <- Hfl in Hm.
    rewrite fsts_prod_map in Hm.
    pose proof (NoDup_fmap_1_strong _ _ Hm) as Hfinj.
    apply (elem_of_list_fmap_1 fst) in Hk'a', Hk''a''.
    now apply Hfinj.
  }
  split.
  - intros (k & Hk & Hfk).
    rewrite <- elem_of_list_to_map in Hk by easy.
    apply (elem_of_list_fmap_1 (prod_map f id)) in Hk.
    rewrite Hfl in Hk.
    apply elem_of_map_to_list in Hk.
    cbn in *.
    now subst i.
  - intros Hi%elem_of_map_to_list.
    rewrite <- Hfl in Hi.
    apply elem_of_list_fmap in Hi as ((k, a) & [= -> <-] & Hx).
    exists k.
    split; [|easy].
    now apply elem_of_list_to_map.
Qed.

Lemma lookup_list_to_map_imap `{FinMap K M} {A B}
  (f : nat -> K) `{Hf : !Inj (=) (=) f} (g : A -> B) (l : list A) (i : nat) :
  (list_to_map (imap (λ n a, (f n, g a)) l) :> M B) !! f i =
  g <$> l !! i.
Proof.
  apply option_eq.
  intros b.
  rewrite <- elem_of_list_to_map by now
    rewrite fmap_imap; unfold compose; cbn;
    rewrite imap_seq_0; apply NoDup_fmap_2; [|apply NoDup_seq].
  rewrite elem_of_lookup_imap.
  split.
  - now intros (i' & a & [= <-%(inj f) ->] & ->).
  - destruct (l !! i) as [a|] eqn:Hli; [|easy].
    cbn.
    intros [= <-]; eauto.
Qed.

Lemma dom_kmap' `{FinMapDom K1 M1 SK1, FinMapDom K2 M2 SK2}
  `{!Elements K1 SK1, !FinSet K1 SK1} {A}
  (f : K1 -> K2) (m : M1 A)
  : dom (kmap f m :> M2 A) ≡ set_map f (dom m).
Proof.
  induction m as [|i a m Hmi Hfirst IHm] using map_first_key_ind;
  [now rewrite kmap_empty, 2 dom_empty, set_map_empty|].
  rewrite kmap_insert_first_key by easy.
  now rewrite 2 dom_insert, set_map_union, set_map_singleton, IHm.
Qed.

Lemma dom_kmap_L' `{FinMapDom K1 M1 SK1, FinMapDom K2 M2 SK2}
  `{!Elements K1 SK1, !FinSet K1 SK1, !LeibnizEquiv SK2} {A}
  (f : K1 -> K2) (m : M1 A)
  : dom (kmap f m :> M2 A) = set_map f (dom m).
Proof.
  unfold_leibniz.
  apply dom_kmap'.
Qed.


Lemma set_Forall2_map `{FinSet A SA, SemiSet B SB} P (f : A -> B) (X : SA) :
  set_Forall2 P (set_map f X :> SB) <->
  set_Forall2 (λ i j, P (f i) (f j)) X.
Proof.
  unfold set_Forall2.
  setoid_rewrite elem_of_map.
  naive_solver.
Qed.
Lemma kmap_fmap' `{FinMap K1 M1, FinMap K2 M2}
  (f : K1 -> K2) `(g : A -> B) (m : M1 A) :
  kmap f ((g <$> m) :> M1 B) =@{M2 B}
  g <$> kmap f m.
Proof.
  induction m using map_first_key_ind;
    [now rewrite fmap_empty, 2 kmap_empty, fmap_empty|].
  rewrite fmap_insert, 2 kmap_insert_first_key,
    fmap_insert; [congruence|easy..| |].
  - now rewrite lookup_fmap, fmap_None.
  - eapply map_first_key_dom'; [|eassumption].
    intros j.
    rewrite 2 lookup_insert_case.
    case_decide; [easy|].
    now rewrite lookup_fmap, fmap_is_Some.
Qed.
Lemma set_map_ext `{FinSet A SA, SemiSet B SB} (f g : A -> B) (X : SA) :
  (forall x, x ∈ X -> f x = g x) ->
  set_map f X ≡@{SB} set_map g X.
Proof.
  set_solver.
Qed.
Lemma set_map_ext_L `{FinSet A SA, SemiSet B SB, !LeibnizEquiv SB}
  (f g : A -> B) (X : SA) : (forall x, x ∈ X -> f x = g x) ->
  set_map f X =@{SB} set_map g X.
Proof.
  unfold_leibniz.
  apply set_map_ext.
Qed.
Lemma set_map_id `{FinSet A SA} (X : SA) :
  set_map id X ≡ X.
Proof.
  set_solver.
Qed.
Lemma set_map_id_L `{FinSet A SA, !LeibnizEquiv SA} (X : SA) :
  set_map id X = X.
Proof.
  unfold_leibniz; apply set_map_id.
Qed.
Lemma set_map_compose `{FinSet A SA, FinSet B SB, SemiSet C SC}
  (f : A -> B) (g : B -> C) (X : SA) :
  set_map g (set_map f X :> SB) ≡@{SC} set_map (g ∘ f) X.
Proof.
  set_solver.
Qed.
Lemma set_map_compose_L `{FinSet A SA, FinSet B SB, SemiSet C SC, !LeibnizEquiv SC}
  (f : A -> B) (g : B -> C) (X : SA) :
  set_map g (set_map f X :> SB) =@{SC} set_map (g ∘ f) X.
Proof.
  unfold_leibniz; apply set_map_compose.
Qed.

Lemma NoDup_list_prod {A B} (l : list A) (l' : list B) :
  NoDup l -> NoDup l' -> NoDup (list_prod l l').
Proof.
  intros Hl Hl'.
  induction Hl; [constructor|].
  cbn.
  apply NoDup_app.
  split_and!.
  - now apply (NoDup_fmap _).
  - intros (a, b) (? & [= <- <-] & Hb)%elem_of_list_fmap.
    rewrite <- list_cprod_list_prod.
    rewrite elem_of_list_cprod.
    cbn; tauto.
  - easy.
Qed.


Lemma vec_to_list_to_list {A n} (v : vec A n) :
  vec_to_list v = Vector.to_list v.
Proof.
  induction v; cbn; f_equal; easy.
Qed.

Fixpoint vseq (start len : nat) : vec nat len :=
  match len with
  | O => [#]
  | S len => start ::: vseq (S start) len
  end.
Lemma vec_to_list_seq start len :
  vec_to_list (vseq start len) = seq start len.
Proof.
  revert start; induction len; intros start; cbn; f_equal; done.
Qed.
Lemma vlookup_seq start len (i : fin len) :
  vseq start len !!! i =
  start + i.
Proof.
  pose proof (lookup_seq_lt start len i (fin_to_nat_lt i)) as Hlook.
  rewrite <- vec_to_list_seq, <- vlookup_lookup' in Hlook.
  destruct Hlook as (Hlt & <-).
  f_equal.
  apply fin_to_nat_inj.
  now rewrite fin_to_nat_to_fin.
Qed.
Lemma vseq_app len1 len2 start :
  vseq start (len1 + len2) =
  vseq start len1 +++ vseq (start + len1) len2.
Proof.
  apply vec_to_list_inj2.
  rewrite vec_to_list_app, 3 vec_to_list_seq.
  apply seq_app.
Qed.

Lemma vseq_fun_to_vec start len :
  vseq start len =
  fun_to_vec (fun i => start + i).
Proof.
  revert start; induction len; [done|intros start].
  cbn.
  f_equal; [lia|].
  rewrite IHlen.
  apply vec_eq.
  intros i.
  rewrite 2 lookup_fun_to_vec.
  cbn.
  lia.
Qed.

Lemma cast_id {A n} (v : vec A n) H :
  Vector.cast v H = v.
Proof.
  revert H; induction v; intros ?; cbn; f_equal; auto.
Qed.
Lemma vec_to_list_rev {A} {n} (v : vec A n) :
  vec_to_list (Vector.rev v) = reverse v.
Proof.
  rewrite 2 vec_to_list_to_list, Vector.to_list_rev.
  now rewrite rev_reverse.
Qed.
Lemma vec_to_list_cast {A} {n m} (v : vec A n) (H : n = m) :
  vec_to_list (Vector.cast v H) = v.
Proof.
  subst.
  now rewrite cast_id.
Qed.
Lemma vec_rev_cons_alt {A} {n} (a : A) (v : vec A n) :
  Vector.rev (a ::: v) = Vector.cast (Vector.rev v +++ [#a]) (Nat.add_comm n 1).
Proof.
  apply vec_to_list_inj2.
  rewrite vec_to_list_rev, vec_to_list_cast, vec_to_list_app,
    vec_to_list_rev.
  cbn -[reverse].
  rewrite reverse_cons.
  reflexivity.
Qed.

Lemma fin_rev_pf {i n} : i < n -> n - S i < n.
Proof.
  lia.
Qed.

Definition fin_rev {n} (i : fin n) : fin n :=
  nat_to_fin (fin_rev_pf $ fin_to_nat_lt i).

Lemma fin_to_nat_rev {n} (i : fin n) :
  fin_rev i =@{nat} n - S i.
Proof.
  apply fin_to_nat_to_fin.
Qed.

Lemma vlookup_rev {A n} (v : vec A n) i :
  Vector.rev v !!! i =
  v !!! fin_rev i.
Proof.
  symmetry.
  apply vlookup_lookup.
  assert (Hvi : is_Some (vec_to_list (Vector.rev v) !! (i:>nat))) by now
    apply lookup_lt_is_Some;
    rewrite length_vec_to_list;
    apply fin_to_nat_lt.

  destruct Hvi as [vi Hvi].
  replace (_ !!! i) with vi. 2:{
    symmetry.
    apply vlookup_lookup' in Hvi as [? <-];
    f_equal;
    apply fin_to_nat_inj;
    now rewrite fin_to_nat_to_fin.
  }
  rewrite vec_to_list_rev, reverse_lookup in Hvi by
    now rewrite length_vec_to_list; apply fin_to_nat_lt.
  rewrite <- Hvi.
  now rewrite fin_to_nat_rev, length_vec_to_list.
Qed.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.








Lemma size_set_eq_exists_map `{FinMapDom K M SK,
  !Elements K SK, !FinSet K SK, FinSet A SA}
  (X : SK) (Y : SA) :
  size X = size Y ->
  exists (m : M A),
    dom m ≡ X /\
    map_img m ≡ Y /\
    forall i j a,
      m !! i = Some a -> m !! j = Some a -> i = j.
Proof.
  intros Hsize.
  exists (list_to_map (zip (elements X) (elements Y))).
  split_and!.
  - rewrite dom_list_to_map, fst_zip by apply eq_reflexivity, Hsize.
    apply list_to_set_elements.
  - rewrite map_img_list_to_map by now
      rewrite fst_zip by apply eq_reflexivity, Hsize;
      apply NoDup_elements.
    rewrite snd_zip by apply eq_reflexivity, symmetry, Hsize.
    apply list_to_set_elements.
  - intros i j a Hi Hj.
    rewrite <- elem_of_list_to_map in Hi, Hj by now
      rewrite fst_zip by apply eq_reflexivity, Hsize;
      apply NoDup_elements.
    rewrite elem_of_list_lookup in Hi, Hj.
    destruct Hi as (ii & Hii).
    destruct Hj as (ij & Hij).
    rewrite lookup_zip_with in Hii, Hij.
    destruct (elements X !! ii) as [Xii|] eqn:HXii; [|done].
    destruct (elements X !! ij) as [Xij|] eqn:HXij; [|done].
    destruct (elements Y !! ii) as [Yii|] eqn:HYii; [|done].
    destruct (elements Y !! ij) as [Yij|] eqn:HYij; [|done].
    cbn in *.
    revert Hii Hij.
    intros [= -> ->] [= -> ->].
    enough (ii = ij) by congruence.
    revert HYii HYij.
    apply NoDup_lookup, NoDup_elements.
Qed.

Lemma list_to_set_bind `{SemiSet B SB} {A} (f : A -> list B) (l : list A) :
  list_to_set (l ≫= f) ≡@{SB} ⋃ (list_to_set ∘ f <$> l).
Proof.
  intros x.
  rewrite elem_of_list_to_set, elem_of_list_bind.
  rewrite elem_of_union_list.
  setoid_rewrite elem_of_list_fmap.
  cbn.
  split.
  - intros (y & Hx & Hy).
    eexists.
    split; [exists y; split; [reflexivity|done]|].
    now rewrite elem_of_list_to_set.
  - intros (? & (? & -> & ?) & Hx%elem_of_list_to_set).
    eauto.
Qed.

Lemma list_to_set_bind_L `{SemiSet B SB, !LeibnizEquiv SB} {A}
  (f : A -> list B) (l : list A) :
  list_to_set (l ≫= f) =@{SB} ⋃ (list_to_set ∘ f <$> l).
Proof.
  unfold_leibniz.
  apply list_to_set_bind.
Qed.

Lemma map_relation_insert `{FinMap K M} {A B} P Q R
  (m : M A) (m' : M B) k a b :
  P k a b ->
  map_relation P Q R m m' ->
  map_relation P Q R (<[k := a]> m) (<[k := b]> m').
Proof.
  intros Hab Hrel i.
  rewrite 2 lookup_insert_case.
  case_decide; [now subst|].
  apply Hrel.
Qed.

Lemma map_relation_empty `{FinMap K M} {A B} P Q R :
  map_relation P Q R (∅ :> M A) (∅ :> M B).
Proof.
  intros i.
  now rewrite 2 lookup_empty.
Qed.

Lemma map_relation_list_to_map `{FinMap K M} {A B} P Q R
  (l : list (K * A)) (l' : list (K * B)) :
  Forall2 (λ ka kb, ka.1 = kb.1 /\ P ka.1 ka.2 kb.2) l l' ->
  map_relation P Q R (list_to_map l :> M A) (list_to_map l' :> M B).
Proof.
  intros Halls.
  induction Halls as [|(k, a) (k', b) l l' [[= <-] Hab]]; [apply map_relation_empty|].
  cbn.
  now apply map_relation_insert.
Qed.

Lemma Forall_zip_with {A B C} (P : C -> Prop) (f : A -> B -> C)
  (l : list A) (l' : list B) :
  length l = length l' ->
  Forall P (zip_with f l l') <->
  Forall2 (λ a b, P (f a b)) l l'.
Proof.
  intros Hlen%Forall2_same_length.
  induction Hlen; [easy|].
  cbn.
  rewrite Forall_cons, Forall2_cons, IHHlen.
  done.
Qed.

Add Parametric Morphism `{SemiSet A SA, !LeibnizEquiv SA} :
  (@union_list SA _ _) with signature
  Permutation ==> eq as union_list_perm_L.
Proof.
  intros l l' Hperm.
  apply set_eq; intros x.
  rewrite 2 elem_of_union_list.
  now setoid_rewrite Hperm.
Qed.

Lemma map_disjoint_union_inj `{FinMap K M} {A} (m m' : M A) :
  m ##ₘ m' ->
  (forall i j a, m !! i = Some a -> m !! j = Some a -> i = j) ->
  (forall i j a, m' !! i = Some a -> m' !! j = Some a -> i = j) ->
  (forall i j a, m !! i = Some a -> m' !! j = Some a -> False) ->
  (forall i j a, (m ∪ m') !! i = Some a -> (m ∪ m') !! j = Some a -> i = j).
Proof.
  intros Hmm' Hm Hm' Himg.
  intros i j a.
  rewrite map_disjoint_alt in Hmm'.
  specialize (Hmm' i) as Hi.
  specialize (Hmm' j) as Hj.
  rewrite 2 lookup_union.
  destruct (m !! i) eqn:Hmi, (m' !! i) eqn:Hm'i; [now destruct Hi|..|easy];
  destruct (m !! j) eqn:Hmj, (m' !! j) eqn:Hm'j; [now destruct Hj|..|easy];
  cbn;
  intros [= ->] [= ->];
  solve [eauto|exfalso; eauto].
Qed.


Definition map_inj `{Lookup K A M} (m : M) :=
  forall i j a, m !! i = Some a -> m !! j = Some a -> i = j.

(* FIXME: Fix lemma in Aux_stdpp to not use dom (just use size m, not size (dom m)),
  and then remove dom requirement here *)
Lemma map_inj_iff_size_img `{FinMapDom K M SK, !Elements K SK, !FinSet K SK,
  FinSet A SA} (m : M A) :
  map_inj m <-> size (dom m) = size (map_img m :> SA).
Proof.
  symmetry.
  pose proof @elem_of_dec_slow.
  apply map_dom_img_eq_card_iff_inj.
Qed.


Lemma set_map_union_list `{FinSet A SA, SemiSet B SB} (f : A -> B)
  (l : list SA) :
  set_map f (⋃ l) ≡@{SB} ⋃ (set_map f <$> l).
Proof.
  induction l; [set_solver|].
  cbn.
  rewrite set_map_union.
  now f_equiv.
Qed.

Lemma set_map_union_list_L `{FinSet A SA, SemiSet B SB, !LeibnizEquiv SB}
  (f : A -> B) (l : list SA) :
  set_map f (⋃ l) =@{SB} ⋃ (set_map f <$> l).
Proof.
  unfold_leibniz.
  apply set_map_union_list.
Qed.







Lemma gmultiset_map_ext `{Countable A, Countable B} (m : gmultiset A)
  (f g : A -> B) (Hfg : forall a, a ∈ m -> f a = g a) :
  gmultiset_map f m = gmultiset_map g m.
Proof.
  rewrite 2 gmultiset_map_alt.
  f_equal.
  apply list_fmap_ext; intros _ a Ha%elem_of_list_lookup_2%gmultiset_elem_of_elements.
  auto.
Qed.

Lemma gmultiset_map_id `{Countable A} (m : gmultiset A) :
  gmultiset_map id m = m.
Proof.
  apply gmultiset_eq.
  intros x.
  change x with (id x) at 1.
  now rewrite (multiplicity_gmultiset_map _ _ _ _).
Qed.

Lemma list_to_set_disj_elements `{Countable A} (m : gmultiset A) :
  list_to_set_disj (elements m) = m.
Proof.
  rewrite <- (gmultiset_map_id m) at 2.
  now rewrite gmultiset_map_alt, list_fmap_id.
Qed.

Lemma elements_list_to_set_disj `{Countable A} (l : list A) :
  elements (list_to_set_disj l :> gmultiset A) ≡ₚ l.
Proof.
  induction l; [done|].
  cbn -[disj_union].
  rewrite gmultiset_elements_disj_union, IHl, gmultiset_elements_singleton.
  done.
Qed.

Lemma gmultiset_map_compose `{Countable A, Countable B, Countable C}
  (f : A -> B) (g : B -> C) (m : gmultiset A) :
  gmultiset_map g (gmultiset_map f m) = gmultiset_map (g ∘ f) m.
Proof.
  rewrite 3 gmultiset_map_alt.
  now rewrite elements_list_to_set_disj, list_fmap_compose.
Qed.

Lemma elements_gmultiset_map `{Countable A, Countable B} (m : gmultiset A)
  (f : A -> B) : elements (gmultiset_map f m) ≡ₚ f <$> elements m.
Proof.
  rewrite gmultiset_map_alt.
  apply elements_list_to_set_disj.
Qed.

Lemma gmultiset_size_alt `{Countable A} (m : gmultiset A) :
  size m = list_sum (Pos.to_nat <$> (map_to_list m.(gmultiset_car)).*2).
Proof.
  destruct m as [m].
  cbn.
  induction m as [|a n m Hma Hfst IHm] using map_first_key_ind;
    [rewrite map_to_list_empty; apply gmultiset_size_empty|].
  unfold size, gmultiset_size.
  cbn.
  rewrite map_to_list_insert_first_key by done.
  cbn.
  rewrite length_app, length_replicate.
  f_equal.
  apply IHm.
Qed.

Lemma gmultiset_map_alt_car `{Countable A, Countable B} (f : A -> B)
  (m : gmultiset A) :
  gmultiset_map f m =
  list_to_set_disj $
    (prod_map f id <$> map_to_list m.(gmultiset_car)) ≫=
    λ '(b, n), replicate (Pos.to_nat n) b.
Proof.
  rewrite gmultiset_map_alt.
  rewrite list_fmap_bind.
  unfold elements, gmultiset_elements.
  destruct m as [m].
  cbn.
  rewrite list_bind_fmap.
  f_equal.
  apply list_bind_ext; [|done]; intros [a p].
  cbn.
  now rewrite fmap_replicate.
Qed.


Definition vsplitl {A n m} (v : vec A (n + m)) : vec A n :=
  (Vector.splitat n v).1.
Definition vsplitr {A n m} (v : vec A (n + m)) : vec A m :=
  (Vector.splitat n v).2.
Lemma app_vsplit {A n m} (v : vec A (n + m)) :
  vsplitl v +++ vsplitr v = v.
Proof.
  apply symmetry, Vector.append_splitat, surjective_pairing.
Qed.
Lemma vsplit_eq {A n m} (v w : vec A (n + m)) :
  v = w <-> vsplitl v = vsplitl w /\ vsplitr v = vsplitr w.
Proof.
  split; [now intros ->|].
  intros [Hl Hr].
  rewrite <- (app_vsplit v), <- (app_vsplit w).
  congruence.
Qed.
Lemma vsplitl_app {A n m} (v : vec A n) (w : vec A m) :
  vsplitl (v +++ w) = v.
Proof.
  unfold vsplitl.
  now rewrite Vector.splitat_append.
Qed.
Lemma vsplitr_app {A n m} (v : vec A n) (w : vec A m) :
  vsplitr (v +++ w) = w.
Proof.
  unfold vsplitr.
  now rewrite Vector.splitat_append.
Qed.
Lemma vec_add_inv `(P : vec A (n + m) -> Prop)
  (HP : forall v w, P (v +++ w)) : forall v, P v.
Proof.
  intros v.
  rewrite <- app_vsplit.
  apply HP.
Qed.
Fixpoint vec_cast_opt {A n} (v : vec A n) : forall (m : nat), option (vec A m) :=
  match n, v with
  | 0, _ => fun m => match m with
    | 0 => Some [#]
    | S _ => None
    end
  | S n, _ => fun m => match m with
    | 0 => None
    | S m => (vhd v :::.) <$> vec_cast_opt (vtl v) m
    end
  end.
Lemma vec_cast_opt_spec {A n} (v : vec A n) m :
  vec_cast_opt v m = (guard (n = m) ≫= λ H, Some (Vector.cast v H)).
Proof.
  revert m; induction v; intros [|m]; [done..|].
  cbn.
  rewrite IHv.
  case_guard; case_guard; [|congruence..|done].
  cbn.
  do 3 f_equal; apply proof_irrel.
Qed.
Lemma vec_cast_opt_ne {A n} (v : vec A n) m :
  n <> m -> vec_cast_opt v m = None.
Proof.
  intros Hne.
  rewrite vec_cast_opt_spec.
  case_guard; done.
Qed.
Lemma vec_cast_opt_refl {A n} (v : vec A n) :
  vec_cast_opt v n = Some v.
Proof.
  rewrite vec_cast_opt_spec.
  case_guard; [|done].
  cbn.
  now rewrite cast_id.
Qed.
Lemma vec_cast_opt_eq {A n} (v : vec A n) {m} (H : n = m) :
  vec_cast_opt v m = Some (Vector.cast v H).
Proof.
  rewrite vec_cast_opt_spec.
  case_guard; [|done].
  cbn.
  do 2 f_equal; apply proof_irrel.
Qed.
Lemma vec_cast_opt_Some {A n} (v : vec A n) m w :
  vec_cast_opt v m = Some w <->
  exists H, w = Vector.cast v H.
Proof.
  split; [|now intros (Hw & ->); apply (vec_cast_opt_eq v Hw)].
  rewrite vec_cast_opt_spec.
  case_guard; [|done].
  cbn.
  intros [= <-].
  eauto.
Qed.
Lemma vec_cast_opt_is_Some {A n} (v : vec A n) m :
  is_Some (vec_cast_opt v m) <-> n = m.
Proof.
  rewrite is_Some_alt.
  rewrite vec_cast_opt_spec.
  case_guard; cbn; naive_solver.
Qed.

Lemma vsplitl_map {A B n m} (f : A -> B) (v : vec A (n + m)) :
  vsplitl (vmap f v) = vmap f (vsplitl v).
Proof.
  induction v using vec_add_inv.
  rewrite Vector.map_append.
  now rewrite 2 vsplitl_app.
Qed.
Lemma vsplitr_map {A B n m} (f : A -> B) (v : vec A (n + m)) :
  vsplitr (vmap f v) = vmap f (vsplitr v).
Proof.
  induction v using vec_add_inv.
  rewrite Vector.map_append.
  now rewrite 2 vsplitr_app.
Qed.

Definition fun_to_map `{Insert A B M, Empty M, Elements A SA}
  (f : A -> B) (X : SA) : M :=
  set_to_map (fun a => (a, f a)) X.

Lemma lookup_fun_to_map `{FinMap K M, FinSet K SK, !RelDecision (∈@{SK})} {A}
  (f : K -> A) (X : SK) k :
  (fun_to_map f X :> M A) !! k = if decide (k ∈ X) then Some (f k) else None.
Proof.
  unfold fun_to_map.
  case_decide as Hk.
  - rewrite lookup_set_to_map by done.
    eauto.
  - apply eq_None_not_Some.
    intros (? & Heq).
    rewrite lookup_set_to_map in Heq by done.
    now destruct Heq as (_ & ? & [= -> <-]).
Qed.


Lemma lookup_fun_to_map_Some `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k a :
  (fun_to_map f X :> M A) !! k = Some a <->
  k ∈ X /\ f k = a.
Proof.
  unfold fun_to_map.
  rewrite lookup_set_to_map by done.
  naive_solver.
Qed.

Lemma lookup_fun_to_map_None `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  (fun_to_map f X :> M A) !! k = None <->
  k ∉ X.
Proof.
  unfold fun_to_map.
  rewrite eq_None_not_Some.
  unfold is_Some.
  setoid_rewrite lookup_set_to_map; [|done].
  naive_solver.
Qed.

Lemma lookup_fun_to_map_Some_1 `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  k ∈ X ->
  (fun_to_map f X :> M A) !! k = Some (f k).
Proof.
  now rewrite lookup_fun_to_map_Some.
Qed.

Lemma lookup_fun_to_map_None_1 `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  k ∉ X ->
  (fun_to_map f X :> M A) !! k = None.
Proof.
  now rewrite lookup_fun_to_map_None.
Qed.


Lemma lookup_fun_to_map_is_Some `{FinMap K M, FinSet K SK} {A}
  (f : K -> A) (X : SK) k :
  is_Some ((fun_to_map f X :> M A) !! k) <-> k ∈ X.
Proof.
  unfold is_Some.
  setoid_rewrite lookup_fun_to_map_Some.
  naive_solver.
Qed.

Lemma dom_fun_to_map_gen `{FinMapDom K M SK, FinSet K SK'} {A}
  (f : K -> A) (X : SK') :
  dom (fun_to_map f X :> M A) ≡@{SK} set_map id X.
Proof.
  intros x.
  rewrite elem_of_dom.
  rewrite lookup_fun_to_map_is_Some.
  set_solver.
Qed.

Lemma dom_fun_to_map_gen_L `{FinMapDom K M SK, FinSet K SK', !LeibnizEquiv SK} {A}
  (f : K -> A) (X : SK') :
  dom (fun_to_map f X :> M A) =@{SK} set_map id X.
Proof.
  unfold_leibniz; apply dom_fun_to_map_gen.
Qed.

Lemma dom_fun_to_map `{FinMapDom K M SK, !Elements K SK, !FinSet K SK} {A}
  (f : K -> A) (X : SK) :
  dom (fun_to_map f X :> M A) ≡@{SK} X.
Proof.
  now rewrite dom_fun_to_map_gen, set_map_id.
Qed.

Lemma dom_fun_to_map_L `{FinMapDom K M SK, !Elements K SK,
  !FinSet K SK, !LeibnizEquiv SK} {A}
  (f : K -> A) (X : SK) :
  dom (fun_to_map f X :> M A) =@{SK} X.
Proof.
  unfold_leibniz; apply dom_fun_to_map.
Qed.

Lemma fun_to_map_union `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) :
  fun_to_map f (X ∪ Y) =@{M A} fun_to_map f X ∪ fun_to_map f Y.
Proof.
  apply map_eq.
  intros k.
  apply option_eq; intros fk.
  rewrite lookup_union, union_Some.
  rewrite 3 lookup_fun_to_map_Some.
  rewrite elem_of_union.
  rewrite lookup_fun_to_map_None.
  pose proof @elem_of_dec_slow.
  destruct_decide (decide (k ∈ X)); tauto.
Qed.

Lemma fmap_fun_to_map `{FinMap K M, FinSet K SK} {A B} (f : K -> A) (g : A -> B)
  (X : SK) :
  g <$> fun_to_map f X =@{M B} fun_to_map (g ∘ f) X.
Proof.
  apply map_eq; intros k.
  apply option_eq; intros fk.
  rewrite lookup_fmap, fmap_Some.
  setoid_rewrite lookup_fun_to_map_Some.
  naive_solver.
Qed.

(* Lemma kmap_fun_to_map `{FinMap K1 M1, FinSet K1 SK1, FinMap K2 M2, FinSet K2 SK2}
  {A} (f : K1 -> A) (g : K1 -> K2) (X : SK1) :
  kmap g (fun_to_map f X :> M1 A) =@{M2 A}
    set_to_map (fun a => (g a, f a)) X. *)
Lemma fun_to_map_singleton
  `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (k : K) :
  fun_to_map f ({[k]}:>SK) =@{M A} {[k := f k]}.
Proof.
  unfold fun_to_map, set_to_map.
  rewrite elements_singleton.
  done.
Qed.

Lemma fun_to_map_difference `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) :
  fun_to_map f (X ∖ Y) =@{M A} fun_to_map f X ∖ fun_to_map f Y.
Proof.
  apply map_eq.
  intros k.
  apply option_eq; intros fk.
  rewrite lookup_difference_Some.
  rewrite 2 lookup_fun_to_map_Some, lookup_fun_to_map_None.
  rewrite elem_of_difference.
  tauto.
Qed.

Lemma fun_to_map_disjoint `{FinMap K M, FinSet K SK} {A} (f : K -> A)
  (X Y : SK) : X ## Y -> fun_to_map f X ##ₘ (fun_to_map f Y :> M A).
Proof.
  intros HXY.
  rewrite map_disjoint_alt.
  intros k.
  pose proof @elem_of_dec_slow.
  rewrite 2 lookup_fun_to_map_None.
  destruct_decide (decide (k ∈ X)).
  - right.
    now intros ?; apply (HXY k).
  - left.
    now intros ?; apply (HXY k).
Qed.


Lemma option_bind_comm {A B C} (f : A -> B -> option C)
  (ma : option A) (mb : option B) :
  (ma ≫= λ a, mb ≫= λ b, f a b) =
  (mb ≫= λ b, ma ≫= λ a, f a b).
Proof.
  now destruct ma, mb.
Qed.

Lemma option_bind_fmap {A B C} (f : A -> option B) (g : B -> C)
  (ma : option A) :
  g <$> (ma ≫= f) = ma ≫= λ a, g <$> f a.
Proof.
  now destruct ma.
Qed.

Lemma option_fmap_bind {A B C} (f : A -> B) (g : B -> option C)
  (ma : option A) :
  ((f <$> ma) ≫= g) = ma ≫= g ∘ f.
Proof.
  now destruct ma.
Qed.

Lemma option_bind_assoc' {A B C} (f : A -> option B) (g : B -> option C)
  (ma : option A) :
  (ma ≫= f) ≫= g = ma ≫= λ a, f a ≫= g.
Proof.
  now destruct ma.
Qed.

Lemma join_list_fmap_mbind {A B} (f : A -> option B) (lm : list (option A)) :
  join_list (mbind f <$> lm) =
  l ← join_list lm;
  join_list (f <$> l).
Proof.
  induction lm as [|ma lm IHlm]; [reflexivity|].
  cbn.
  rewrite IHlm.
  destruct ma as [a|]; [|reflexivity].
  cbn.
  rewrite option_bind_assoc.
  destruct (join_list lm) as [l|]; [|now case_match].
  reflexivity.
Qed.

Add Parametric Morphism {A B} : (@mbind option _ A B) with signature
  pointwise_relation A eq ==> eq ==> eq as option_bind_mor.
Proof.
  intros; now apply option_bind_ext.
Qed.

Lemma join_list_app {A} (ml ml' : list (option A)) :
  join_list (ml ++ ml') =
  l ← join_list ml;
  (l ++.) <$> join_list ml'.
Proof.
  induction ml as [|ma ml IHml]; [cbn; now rewrite option_fmap_id|].
  cbn.
  rewrite IHml.
  case_match; [|reflexivity].
  cbn.
  rewrite 2 option_bind_assoc.
  unfold compose.
  cbn.
  setoid_rewrite option_fmap_bind.
  reflexivity.
Qed.

Lemma join_list_app' {A} (ml ml' : list (option A)) :
  join_list (ml ++ ml') =
  l' ← join_list ml';
  (.++ l') <$> join_list ml.
Proof.
  induction ml as [|ma ml IHml]; [cbn; now destruct (join_list ml')|].
  cbn.
  rewrite IHml.
  destruct ma as [a|].
  - rewrite option_bind_assoc.
    unfold compose.
    setoid_rewrite option_fmap_bind.
    reflexivity.
  - cbn.
    now destruct (join_list ml').
Qed.
Lemma option_fmap_to_bind {A B} (f : A -> B) (ma : option A) :
  f <$> ma = ma ≫= λ a, Some (f a).
Proof.
  reflexivity.
Qed.

Lemma option_bind_None_r {A B} (ma : option A) :
  (ma ≫= λ a, @None B) = None.
Proof.
  now destruct ma.
Qed.









Lemma join_list_Some_length {A} (ml : list (option A)) l :
  join_list ml = Some l ->
  length ml = length l.
Proof.
  intros Hlen%join_list_Some%(f_equal length).
  now rewrite length_fmap in Hlen.
Qed.



Lemma option_Forall2_alt {A B} (P : A -> B -> Prop) ma mb :
  option_Forall2 P ma mb <->
  match ma, mb with
  | Some a, Some b => P a b
  | None, None => True
  | _, _ => False
  end.
Proof.
  split; [now intros []|].
  destruct ma, mb; easy + now constructor.
Qed.
Lemma eqlistA_cons_iff `{eqA : relation A} {x x' : A} {l l' : list A} :
  eqlistA eqA (x :: l) (x' :: l') <-> eqA x x' /\ eqlistA eqA l l'.
Proof.
  split; [|now intros []; apply eqlistA_cons].
  intros Heq.
  inversion Heq; now subst.
Qed.
Lemma PermutationA_iff_exists_Forall2_Permutation
  `{RA : relation A} `{!Equivalence RA} l l' :
  PermutationA RA l l' <-> exists l'', l ≡ₚ l'' /\ Forall2 RA l'' l'.
Proof.
  split.
  - intros (l'' & Hl'' & Heq%eqlistA_altdef)%PermutationA_decompose; eauto.
  - intros (l'' & Hperm & Heq%eqlistA_altdef).
    etransitivity;
    [now apply Permutation_PermutationA; eauto|].
    now apply eqlistA_PermutationA.
Qed.



Lemma Forall2_iff_pred {A B} (P : A -> Prop) (Q : B -> Prop) (l : list A) l' :
  Forall2 (λ a b, P a <-> Q b) l l' ->
  Forall P l <-> Forall Q l'.
Proof.
  intros Hl.
  induction Hl; rewrite ?Forall_cons, ?Forall_nil; tauto.
Qed.


Lemma list_omap_fmap {A B C} (f : A -> B) (g : B -> option C) (l : list A) :
  omap g (f <$> l) = omap (g ∘ f) l.
Proof.
  induction l; [done|cbn]; case_match; f_equal; easy.
Qed.

Lemma join_list_Permutation {A} (ml ml' : list (option A)) :
  ml ≡ₚ ml' -> option_Forall2 Permutation (join_list ml) (join_list ml').
Proof.
  intros Hperm.
  pose proof (join_list_is_Some ml) as Hsome.
  rewrite Hperm in Hsome at 2.
  rewrite <- join_list_is_Some in Hsome.
  rewrite 2 is_Some_alt in Hsome.
  destruct (join_list ml) as [l|] eqn:Hl;
  destruct (join_list ml') as [l'|] eqn:Hl'; [|tauto..|];
  constructor.
  apply join_list_Some in Hl, Hl'.
  apply (f_equal (omap id)) in Hl, Hl'.
  rewrite list_omap_fmap in Hl, Hl'.
  unfold compose, id in Hl, Hl'.
  rewrite <- list_fmap_alt, list_fmap_id in Hl, Hl'.
  subst l l'.
  apply omap_Permutation.
  now rewrite Hperm.
Qed.


Lemma fmap_eqlistA `{RA : relation A, RB : relation B}
  (f : A -> B) {Hf : Proper (RA ==> RB) f} (l l' : list A) :
  eqlistA RA l l' -> eqlistA RB (f <$> l) (f <$> l').
Proof.
  intros Hl.
  induction Hl; cbn; eauto using eqlistA.
Qed.

Lemma fmap_PermutationA `{RA : relation A, RB : relation B}
  (f : A -> B) (Hf : Proper (RA ==> RB) f) (l l' : list A) :
  PermutationA RA l l' -> PermutationA RB (f <$> l) (f <$> l').
Proof.
  intros Hl.
  induction Hl; cbn; eauto using PermutationA.
Qed.


Lemma imap_to_imap_pair {A B} (f : nat -> A -> B) l :
  imap f l = uncurry f <$> imap pair l.
Proof.
  rewrite fmap_imap.
  reflexivity.
Qed.

Lemma zip_with_ext_strong {A B C} (f g : A -> B -> C)
  (l1 l2 : list A) (k1 k2 : list B) :
  (forall a b, a ∈ l1 -> b ∈ k1 -> f a b = g a b) ->
  l1 = l2 -> k1 = k2 ->
  zip_with f l1 k1 = zip_with g l2 k2.
Proof.
  intros Hfg <- <-.
  revert k1 Hfg; induction l1; intros k1 Hfg; [done|].
  destruct k1; [done|].
  cbn.
  f_equal; [|now apply IHl1; eauto using elem_of_list_further].
  apply Hfg; constructor.
Qed.


Fixpoint infinite_injection_aux `{Infinite A} (n : nat) : A * list A :=
  match n with
  | 0 => (fresh [], [])
  | S n' => let fn' := infinite_injection_aux n' in
    (fresh (fn'.1 :: fn'.2), fn'.1 :: fn'.2)
  end%nat.

Lemma infinite_injection_aux_fresh `{Infinite A} (n : nat):
  ((infinite_injection_aux n).1 :> A) ∉ (infinite_injection_aux n).2.
Proof.
  destruct n; apply infinite_is_fresh.
Qed.

Lemma infinite_injection_aux_contains `{Infinite A} (n m : nat) :
  (n < m)%nat ->
  uncurry cons (infinite_injection_aux n) ⊆@{list A} (infinite_injection_aux m).2.
Proof.
  intros Hlt.
  induction Hlt.
  - cbn.
    now destruct (infinite_injection_aux _).
  - cbn.
    rewrite IHHlt.
    now apply list_subseteq_cons.
Qed.

Definition infinite_injection `{Infinite A} (n : nat) : A :=
  (infinite_injection_aux n).1.

#[global] Instance infinite_injection_inj `{Infinite A} :
  Inj (=) (@eq A) infinite_injection.
Proof.
  eenough (Hen : _) by
  (intros n m; destruct (Nat.lt_trichotomy n m) as [Hnm | [-> | Hmn]];
  [exact (Hen n m Hnm)|easy|exact (fun H => eq_sym (Hen m n Hmn (eq_sym H)))]).
  intros n m Hnm.
  unfold infinite_injection.
  pose proof (infinite_injection_aux_fresh (A:=A) m) as Hfresh.
  pose proof (infinite_injection_aux_contains (A:=A) n m Hnm) as Hcont.
  rewrite (surjective_pairing (infinite_injection_aux n)) in Hcont.
  cbn in Hcont.
  intros Heq.
  rewrite Heq in Hcont.
  specialize (Hcont (infinite_injection_aux m).1 ltac:(constructor)).
  easy.
Qed.


Fixpoint infinite_injection_avoiding_aux `{Infinite A} (l : list A) (n : nat) :
  A * list A :=
  match n with
  | 0 => (fresh l, l)
  | S n' => let fn' := infinite_injection_avoiding_aux l n' in
    (fresh (fn'.1 :: fn'.2), fn'.1 :: fn'.2)
  end%nat.

Lemma infinite_injection_avoiding_aux_fresh `{Infinite A} (l : list A) (n : nat) :
  (infinite_injection_avoiding_aux l n).1 ∉ (infinite_injection_avoiding_aux l n).2.
Proof.
  destruct n; apply infinite_is_fresh.
Qed.

Lemma infinite_injection_avoiding_aux_contains `{Infinite A}
  (l : list A) (n m : nat) :
  (n < m)%nat ->
  uncurry cons (infinite_injection_avoiding_aux l n) ⊆
    (infinite_injection_avoiding_aux l m).2.
Proof.
  intros Hlt.
  induction Hlt.
  - cbn.
    now destruct (infinite_injection_avoiding_aux _).
  - cbn.
    rewrite IHHlt.
    now apply list_subseteq_cons.
Qed.


Lemma infinite_injection_avoiding_aux_contains_avoid `{Infinite A}
  (l : list A) (n : nat) :
  l ⊆ (infinite_injection_avoiding_aux l n).2.
Proof.
  induction n; [reflexivity|].
  cbn.
  now apply list_subseteq_cons.
Qed.

Definition infinite_injection_avoiding `{Infinite A} (l : list A) (n : nat) : A :=
  (infinite_injection_avoiding_aux l n).1.

#[global] Instance infinite_injection_avoiding_inj `{Infinite A} l :
  Inj (=) (@eq A) (infinite_injection_avoiding l).
Proof.
  eenough (Hen : _) by
  (intros n m; destruct (Nat.lt_trichotomy n m) as [Hnm | [-> | Hmn]];
  [exact (Hen n m Hnm)|easy|exact (fun H => eq_sym (Hen m n Hmn (eq_sym H)))]).
  intros n m Hnm.
  unfold infinite_injection_avoiding.
  pose proof (infinite_injection_avoiding_aux_fresh l m) as Hfresh.
  pose proof (infinite_injection_avoiding_aux_contains l n m Hnm) as Hcont.
  rewrite (surjective_pairing (infinite_injection_avoiding_aux l n)) in Hcont.
  cbn in Hcont.
  intros Heq.
  rewrite Heq in Hcont.
  specialize (Hcont (infinite_injection_avoiding_aux l m).1 ltac:(constructor)).
  easy.
Qed.

Lemma infinite_injection_avoiding_avoids `{Infinite A} (l : list A) (n : nat) :
  infinite_injection_avoiding l n ∉ l.
Proof.
  pose proof (infinite_injection_avoiding_aux_fresh l n) as Hfresh.
  now intros ?%(infinite_injection_avoiding_aux_contains_avoid l n).
Qed.



Lemma partial_injection_extension `{Countable A, Infinite B}
  (l : list A) (f : A -> B) :
    ForallPairs (λ i j, f i = f j → i = j) l ->
    exists (g : A -> B), Inj (=) (=) g /\ Forall (fun a => g a = f a) l.
Proof.
  intros Hlinj.
  set (g := infinite_injection_avoiding (f <$> l) ∘ Nat.pred ∘ Pos.to_nat).
  exists (λ a, if decide (a ∈ l) then f a else g (encode a)).
  split; [|now rewrite Forall_forall; intros a Ha; rewrite decide_True].
  intros a b.
  case_decide as Ha; case_decide as Hb.
  - now apply Hlinj; apply elem_of_list_In.
  - intros Heq%eq_sym.
    exfalso.
    apply (infinite_injection_avoiding_avoids (f <$> l) (Nat.pred $ Pos.to_nat (encode b))).
    subst g.
    cbn in Heq.
    rewrite Heq.
    now apply elem_of_list_fmap_1.
  - intros Heq.
    exfalso.
    apply (infinite_injection_avoiding_avoids (f <$> l) (Nat.pred $ Pos.to_nat (encode a))).
    subst g.
    cbn in Heq.
    rewrite Heq.
    now apply elem_of_list_fmap_1.
  - intros Heq.
    apply (inj encode).
    revert Heq.
    apply inj.
    unfold g.
    change (?x ∘ ?y ∘ ?z) with (x ∘ (y ∘ z)).
    apply (compose_inj _ eq), _.
    hnf; cbn; lia.
Qed.

Lemma set_Forall2_elements `{FinSet A SA} (R : relation A) (X : SA) :
  set_Forall2 R X <-> ForallPairs R (elements X).
Proof.
  rewrite <- (set_Forall2_list_to_set (C:=SA)).
  now rewrite list_to_set_elements.
Qed.

Lemma partial_injection_extension' `{Countable A, Infinite B, FinSet A SA}
  (X : SA) (f : A -> B) :
  set_Forall2 (λ i j, f i = f j → i = j) X ->
    exists (g : A -> B), Inj (=) (=) g /\ set_Forall (fun a => g a = f a) X.
Proof.
  rewrite set_Forall2_elements.
  intros (g & Hg & Hgeq%set_Forall_elements)%partial_injection_extension.
  eauto.
Qed.

Definition countable_order `{Countable A} (a b : A) : Prop :=
  (encode a < encode b)%positive.

#[export] Instance countable_order_StrictOrder `{Countable A} : StrictOrder (countable_order (A:=A)).
Proof.
  split; [|unfold countable_order, Transitive; intros; etransitivity; eauto].
  intros x.
  unfold countable_order, complement.
  lia.
Qed.

(* Lemma gmap_key_dec `{Countable A} p : Decision (gmap_key A p).
Proof.
  destruct (decode p :> option A) eqn:Hp.
   *)


Definition countable_order_initseg_aux `{Countable A} (n : nat) : list A :=
  omap (λ k, decode k ≫= λ b, guard (encode b = k) ;; Some b)
  (Pos.of_succ_nat <$> seq 0 n).


Definition countable_order_initseg `{Countable A} (a : A) : list A :=
  countable_order_initseg_aux (Nat.pred (Pos.to_nat (encode a))).

Lemma countable_order_initseg_lt `{Countable A} (a : A) :
  Forall (λ b, countable_order b a) (countable_order_initseg a).
Proof.
  rewrite Forall_forall.
  intros i (pi & Hpi & Hdecode)%elem_of_list_omap.
  assert (pi = encode i) as ->. 1:{
    apply bind_Some in Hdecode as (i' & Hdecode & Hdecenc).
    case_guard as Heq; [|done].
    cbn in Hdecenc.
    congruence.
  }
  apply elem_of_list_fmap in Hpi as (? & Heq & ?%elem_of_seq).
  unfold countable_order.
  lia.
Qed.

Lemma elem_of_countable_order_initseg `{Countable A} (a b : A) :
  b ∈ countable_order_initseg a <-> countable_order b a.
Proof.
  split.
  - pose proof (countable_order_initseg_lt a) as Ha.
    rewrite Forall_forall in Ha.
    apply Ha.
  - unfold countable_order.
    intros Henc.
    apply elem_of_list_omap.
    exists (encode b).
    split; [rewrite elem_of_list_fmap; exists (Nat.pred (Pos.to_nat (encode b)));
      rewrite elem_of_seq; lia|].
    rewrite decode_encode.
    cbn.
    now case_guard.
Qed.

Lemma countable_order_initseg_aux_mono `{Countable A} (n m : nat) :
  n <= m ->
  countable_order_initseg_aux (A:=A) n `prefix_of` countable_order_initseg_aux m.
Proof.
  intros Hab.
  replace m with (n + (m - n)) by lia.
  unfold countable_order_initseg_aux.
  rewrite seq_app.
  rewrite fmap_app, omap_app.
  now apply prefix_app_r.
Qed.

Lemma countable_order_initseg_mono `{Countable A} (a b : A) :
  countable_order a b ->
  countable_order_initseg a `prefix_of` countable_order_initseg b.
Proof.
  unfold countable_order.
  intros Hab.
  apply countable_order_initseg_aux_mono.
  lia.
Qed.

(* FIXME: Move *)
Lemma InA_eq {A} (a : A) l :
  InA eq a l <-> In a l.
Proof.
  split; [|apply (In_InA _)].
  intros ?%InA_alt; naive_solver.
Qed.

Lemma NoDupA_eq {A} (l : list A) :
  NoDupA eq l <-> NoDup l.
Proof.
  split; intros Hl; induction Hl; (repeat constructor); now rewrite ?InA_eq, ?elem_of_list_In in *.
Qed.

Lemma StronglySorted_lookup `(R : relation A) (l : list A) :
  StronglySorted R l <->
    forall i j, i < j ->
      option_relation R (λ _, True) (λ _, False) (l !! i) (l !! j).
Proof.
  split.
  - intros Hsort.
    induction Hsort as [|a l Hsort IHl Hal]; [now intros; rewrite 2 lookup_nil|].
    intros [|i] j Hij.
    + cbn.
      destruct j; [lia|].
      cbn.
      case_match eqn:Hlj; [|done].
      rewrite Forall_forall in Hal.
      apply Hal.
      now apply elem_of_list_lookup_2 in Hlj.
    + destruct j; [lia|].
      apply IHl.
      lia.
  - induction l as [|a l IHl]; intros Hl; [constructor|].
    constructor.
    + apply IHl.
      intros i j Hij.
      apply (Hl (S i) (S j)).
      lia.
    + rewrite Forall_lookup.
      intros j b Hjb.
      specialize (Hl 0 (S j) ltac:(lia)).
      cbn in Hl.
      unfold lookup in *.
      now rewrite Hjb in Hl.
Qed.


Lemma elem_of_countable_order_initseg_aux `{Countable A} (n : nat) (a : A) :
  a ∈ countable_order_initseg_aux n <->
  (encode a < Pos.of_succ_nat n)%positive.
Proof.
  split.
  - intros (_ & (k & -> & Hk%elem_of_seq)%elem_of_list_fmap & Hdecenc)%elem_of_list_omap.
    destruct (decode (Pos.of_succ_nat k)) as [a'|] eqn:Ha'; [|done].
    cbn in Hdecenc.
    case_guard as Henc; [cbn in Hdecenc|done].
    replace a' with a in * by congruence.
    lia.
  - intros Henc.
    apply elem_of_list_omap.
    exists (encode a).
    split; [apply elem_of_list_fmap; exists (Nat.pred (Pos.to_nat (encode a))); rewrite elem_of_seq; lia|].
    rewrite decode_encode.
    cbn.
    case_guard; done.
Qed.

Lemma countable_order_initseg_aux_Sorted `{Countable A} (n : nat) :
  Sorted countable_order (countable_order_initseg_aux n :> list A).
Proof.
  unfold countable_order_initseg_aux.
  induction n; [done|].
  replace (S n) with (n + 1) by lia.
  rewrite seq_app, fmap_app, omap_app.
  apply (SortA_app (eqA:=eq) _); [done|..].
  - cbn.
    case_match; repeat constructor.
  - cbn.
    case_match eqn:Hdec; [|easy].
    intros b c.
    rewrite 2 InA_eq.
    rewrite <- 2 elem_of_list_In.
    rewrite elem_of_list_singleton.
    intros Hb ->.
    apply elem_of_countable_order_initseg_aux in Hb.
    destruct (decode (Pos.of_succ_nat n)) as [a'|] eqn:Ha'; [|done].
    cbn in Hdec.
    case_guard as Henc; [cbn in Hdec|done].
    replace a' with a in * by congruence.
    unfold countable_order.
    lia.
Qed.


Lemma countable_order_initseg_aux_StronglySorted `{Countable A} (n : nat) :
  StronglySorted countable_order (countable_order_initseg_aux n :> list A).
Proof.
  apply Sorted_StronglySorted, countable_order_initseg_aux_Sorted.
  apply countable_order_StrictOrder.
Qed.

Lemma countable_order_initseg_aux_NoDup `{Countable A} (n : nat) :
  NoDup (countable_order_initseg_aux n :> list A).
Proof.
  apply NoDupA_eq.
  apply (SortA_NoDupA _ (ltA:=countable_order) (countable_order_StrictOrder) _).
  apply countable_order_initseg_aux_Sorted.
Qed.

Lemma max_list_with_elem_of_le {A} (f : A -> nat) a (l : list A) :
  a ∈ l -> f a <= max_list_with f l.
Proof.
  revert a.
  apply Forall_forall.
  induction l; constructor.
  - cbn; lia.
  - apply (Forall_impl _ _ _ IHl).
    cbn.
    lia.
Qed.

Lemma max_list_with_app {A} (f : A -> nat) (l l' : list A) :
  max_list_with f (l ++ l') =
  max_list_with f l `max` max_list_with f l'.
Proof.
  induction l; cbn; lia.
Qed.

Definition countably_infinite_encode_bound `{Countable A, Infinite A}
  (n : nat) : nat :=
  max_list_with (Pos.to_nat)
    (encode (A:=A) ∘ infinite_injection <$> seq 0 n).

Lemma countably_infinite_encode_bound_correct `{Countable A, Infinite A}
  (n : nat) :
  n <= length (countable_order_initseg_aux (A:=A) (countably_infinite_encode_bound (A:=A) n)).
Proof.
  rewrite <- (length_seq 0 n) at 1.
  rewrite <- (length_fmap (infinite_injection (A:=A))).
  apply NoDup_incl_length.
  - apply NoDup_ListNoDup.
    apply (NoDup_fmap _), NoDup_seq.
  - intros a.
    rewrite <- 2 elem_of_list_In.
    intros (k & -> & Hk)%elem_of_list_fmap.
    apply elem_of_countable_order_initseg_aux.
    unfold countably_infinite_encode_bound.
    pose proof (max_list_with_elem_of_le (Pos.to_nat) (encode (A:=A) (infinite_injection k))
      (encode (A:=A) ∘ infinite_injection <$> seq 0 n)) as Hk'.
    tspecialize Hk' by now refine (elem_of_list_fmap_1 _ _ _ Hk).
    lia.
Qed.

Lemma countably_infinite_encode_bound_mono `{Countable A, Infinite A}
  (n m : nat) : n <= m ->
  countably_infinite_encode_bound (A:=A) n
    <= countably_infinite_encode_bound (A:=A) m.
Proof.
  intros Hn.
  induction Hn; [done|].
  unfold countably_infinite_encode_bound in *.
  replace (S m) with (m + 1) by lia.
  rewrite seq_app, fmap_app, max_list_with_app.
  lia.
Qed.

(* FIXME: Move *)
Lemma NoDup_take {A} n (l : list A) :
  NoDup l -> NoDup (take n l).
Proof.
  rewrite <- (take_drop n l) at 1.
  now intros ?%NoDup_app.
Qed.
Lemma NoDup_drop {A} n (l : list A) :
  NoDup l -> NoDup (drop n l).
Proof.
  rewrite <- (take_drop n l) at 1.
  now intros ?%NoDup_app.
Qed.

Definition countably_infinite_bijection `{Countable A, Infinite A}
  (p : positive) : A :=
  default (fresh [])
    (countable_order_initseg_aux (countably_infinite_encode_bound (A:=A) (Pos.to_nat p))
     !! (Nat.pred (Pos.to_nat p))).

Definition countably_infinite_bijection_inv `{Countable A, Infinite A}
  (a : A) : positive :=
  Pos.of_succ_nat (length (countable_order_initseg a)).


#[export] Instance countably_infinite_bijection_mono `{Countable A, Infinite A} :
  Proper (Pos.lt ==> countable_order (A:=A)) countably_infinite_bijection.
Proof.
  intros k l Hkl.
  set (k' := Pos.to_nat k).
  set (l' := Pos.to_nat l).
  set (bnd := countably_infinite_encode_bound (A:=A) l').
  unfold countably_infinite_bijection.
  pose proof (countable_order_initseg_aux_Sorted (A:=A) bnd) as Hsort.
  apply Sorted_StronglySorted in Hsort; [|apply countable_order_StrictOrder].


  pose proof (countable_order_initseg_aux_mono (A:=A)
    (countably_infinite_encode_bound (A:=A) k') bnd) as Hkpref.
  tspecialize Hkpref by now apply countably_infinite_encode_bound_mono; lia.

  rewrite (fun H => prefix_lookup_lt _ _ _ H Hkpref) by
    now apply (fun H => Nat.lt_le_trans _ _ _ H
      (countably_infinite_encode_bound_correct (A:=A) _)); lia.
  fold l' bnd.
  set (a_s := countable_order_initseg_aux bnd).
  pose proof (countably_infinite_encode_bound_correct (A:=A) l') as Hlen.
  pose proof (countably_infinite_encode_bound_mono (A:=A) k' l' ltac:(lia)).
  assert (is_Some (a_s !! (Nat.pred k'))) as Hk'some by
    now apply lookup_lt_is_Some; subst a_s bnd k' l'; lia.
  assert (is_Some (a_s !! (Nat.pred l'))) as Hl'some by
    now apply lookup_lt_is_Some; subst a_s bnd k' l'; lia.
  destruct Hk'some as [a Ha].
  destruct Hl'some as [b Hb].
  fold k' l'.
  rewrite Ha, Hb.
  cbn.
  rewrite StronglySorted_lookup in Hsort.
  specialize (Hsort (Nat.pred k') (Nat.pred l') ltac:(lia)).
  fold a_s in Hsort.
  rewrite Ha, Hb in Hsort.
  now cbn in Hsort.
Qed.

#[export] Instance countably_infinite_bijection_inj `{Countable A, Infinite A} :
  Inj eq (=@{A}) countably_infinite_bijection.
Proof.
  intros k l.
  set (k' := Pos.to_nat k).
  set (l' := Pos.to_nat l).
  set (bnd := countably_infinite_encode_bound (A:=A) (max k' l')).
  unfold countably_infinite_bijection.
  pose proof (countable_order_initseg_aux_NoDup (A:=A) bnd) as Hdup.
  pose proof (countable_order_initseg_aux_mono (A:=A)
    (countably_infinite_encode_bound (A:=A) k') bnd) as Hkpref.
  tspecialize Hkpref by now apply countably_infinite_encode_bound_mono; lia.
  pose proof (countable_order_initseg_aux_mono (A:=A)
    (countably_infinite_encode_bound (A:=A) l') bnd) as Hlpref.
  tspecialize Hlpref by now apply countably_infinite_encode_bound_mono; lia.
  rewrite (fun H => prefix_lookup_lt _ _ _ H Hkpref) by
    now apply (fun H => Nat.lt_le_trans _ _ _ H
      (countably_infinite_encode_bound_correct (A:=A) _)); lia.
  rewrite (fun H => prefix_lookup_lt _ _ _ H Hlpref) by
    now apply (fun H => Nat.lt_le_trans _ _ _ H
      (countably_infinite_encode_bound_correct (A:=A) _)); lia.
  set (a_s := countable_order_initseg_aux bnd).
  pose proof (countably_infinite_encode_bound_correct (A:=A) (max k' l')) as Hlen.
  pose proof (countably_infinite_encode_bound_mono (A:=A) k' (max k' l') ltac:(lia)).
  pose proof (countably_infinite_encode_bound_mono (A:=A) l' (max k' l') ltac:(lia)).
  assert (is_Some (a_s !! (Nat.pred k'))) as Hk'some by
    now apply lookup_lt_is_Some; subst a_s bnd k' l'; lia.
  assert (is_Some (a_s !! (Nat.pred l'))) as Hl'some by
    now apply lookup_lt_is_Some; subst a_s bnd k' l'; lia.
  destruct Hk'some as [a Ha].
  destruct Hl'some as [b Hb].
  fold k' l'.
  rewrite Ha, Hb.
  cbn.
  intros <-.
  enough (Nat.pred k' = Nat.pred l') by lia.
  subst k' l'.
  revert Ha Hb.
  apply NoDup_lookup, Hdup.
Qed.


#[export] Instance countably_infinite_bijection_mono_inj `{Countable A, Infinite A} :
  Inj Pos.lt (countable_order (A:=A)) countably_infinite_bijection.
Proof.
  intros k l.
  destruct_decide (decide (l <= k)%positive) as Hkl.
  1: {
    destruct_decide (decide (l < k)%positive) as Hkllt.
    - apply (countably_infinite_bijection_mono (A:=A)) in Hkllt.
      intros HF.
      exfalso.
      eapply irreflexivity; [apply (countable_order_StrictOrder (A:=A)).(StrictOrder_Irreflexive)|].
      etransitivity; eauto.
    - replace k with l by lia.
      intros []%(irreflexivity _).
  }
  lia.
Qed.


Lemma countably_infinite_bijection_spec_gen `{Countable A, Infinite A}
  (p : positive) (a : A) : countably_infinite_bijection p = a <->
    exists n, countable_order_initseg_aux n !! Nat.pred (Pos.to_nat p) = Some a.
Proof.
  split.
  - unfold countably_infinite_bijection.
    assert (is_Some (countable_order_initseg_aux (A:=A)
      (countably_infinite_encode_bound (A:=A) (Pos.to_nat p))
      !! Nat.pred (Pos.to_nat p))) as Hsome.
    1:{
      apply lookup_lt_is_Some.
      eapply Nat.lt_le_trans; [|apply countably_infinite_encode_bound_correct].
      lia.
    }
    destruct Hsome as [b Hb].
    rewrite Hb.
    cbn.
    intros ->.
    eauto.
  - intros (n & Hp).
    unfold countably_infinite_bijection.
    pose proof (countable_order_initseg_aux_mono (A:=A)
      n (max n (countably_infinite_encode_bound (A:=A) (Pos.to_nat p)))) as Hnpref.
    tspecialize Hnpref by lia.
    pose proof (countable_order_initseg_aux_mono (A:=A)
      (countably_infinite_encode_bound (A:=A) (Pos.to_nat p))
      (max n (countably_infinite_encode_bound (A:=A) (Pos.to_nat p)))) as Hbpref.
    tspecialize Hbpref by lia.
    rewrite (fun H => prefix_lookup_lt _ _ _ H Hnpref) in Hp by now apply lookup_lt_Some in Hp.
    rewrite (fun H => prefix_lookup_lt _ _ _ H Hbpref) by
      now apply (fun H => Nat.lt_le_trans _ _ _ H
        (countably_infinite_encode_bound_correct (A:=A) _)); lia.
    rewrite Hp.
    done.
Qed.

(* Lemma countable_order_initseg_aux_take  *)

Lemma countable_order_initseg_aux_lookup_Some_1 `{Countable A} n m (a : A) :
  countable_order_initseg_aux n !! m = Some a ->
  length (countable_order_initseg a) = m.
Proof.
  intros Ha.
  transitivity (length (take m
    (countable_order_initseg_aux (A:=A) n))).
  2:{
    rewrite length_take.
    apply lookup_lt_Some in Ha.
    lia.
  }
  apply Permutation_length.
  apply NoDup_Permutation; [apply countable_order_initseg_aux_NoDup|
    apply NoDup_take, countable_order_initseg_aux_NoDup|].
  intros b.
  rewrite elem_of_countable_order_initseg.
  unfold countable_order.
  rewrite elem_of_take.
  pose proof (countable_order_initseg_aux_StronglySorted (A:=A) n) as Hsort.
  rewrite StronglySorted_lookup in Hsort.

  split.
  - intros Hlt.
    assert (Hb : b ∈ countable_order_initseg_aux n) by
      now apply elem_of_countable_order_initseg_aux;
        apply elem_of_list_lookup_2, elem_of_countable_order_initseg_aux in Ha; lia.
    apply elem_of_list_lookup in Hb as (i & Hi).
    exists i.
    split; [done|].
    assert (i <> m). 1:{
      intros ->.
      replace a with b in * by congruence.
      lia.
    }
    enough (~ (m < i)) by lia.
    intros HF%Hsort.
    rewrite Ha, Hi in HF.
    cbn in HF.
    unfold countable_order in HF.
    lia.
  - intros (i & Hi & Hip%Hsort).
    rewrite Hi, Ha in Hip.
    cbn in Hip.
    unfold countable_order in Hip.
    lia.
Qed.

Lemma countable_order_initseg_aux_lookup_Some `{Countable A} n m (a : A) :
  countable_order_initseg_aux n !! m = Some a <->
  length (countable_order_initseg a) = m /\ (encode a < Pos.of_succ_nat n)%positive.
Proof.
  split.
  - intros Ha.
    apply elem_of_list_lookup_2 in Ha as Ha'.
    apply elem_of_countable_order_initseg_aux in Ha'.
    split; [|done].
    now apply (countable_order_initseg_aux_lookup_Some_1 n).
  - intros [Hlen Henc].
    apply elem_of_countable_order_initseg_aux in Henc.
    apply elem_of_list_lookup in Henc as (i & Hi).
    apply countable_order_initseg_aux_lookup_Some_1 in Hi as Him.
    congruence.
Qed.




Lemma countably_infinite_bijection_spec `{Countable A, Infinite A}
  (p : positive) (a : A) : countably_infinite_bijection p = a <->
    length (countable_order_initseg a) = Nat.pred (Pos.to_nat p).
Proof.
  split.
  - rewrite countably_infinite_bijection_spec_gen.
    intros (n & Hpa).
    now apply countable_order_initseg_aux_lookup_Some_1 in Hpa.
  - intros Hlen.
    rewrite countably_infinite_bijection_spec_gen.
    exists (Pos.to_nat (encode a)).
    apply countable_order_initseg_aux_lookup_Some.
    split; [done|].
    lia.
Qed.


Lemma countably_infinite_bijection_to_inv_spec `{Countable A, Infinite A}
  (p : positive) (a : A) : countably_infinite_bijection p = a <->
    countably_infinite_bijection_inv a = p.
Proof.
  rewrite countably_infinite_bijection_spec.
  unfold countably_infinite_bijection_inv.
  lia.
Qed.

Lemma countably_infinite_bijection_inv_spec `{Countable A, Infinite A}
  (p : positive) (a : A) : countably_infinite_bijection_inv a = p <->
    length (countable_order_initseg a) = Nat.pred (Pos.to_nat p).
Proof.
  unfold countably_infinite_bijection_inv.
  lia.
Qed.


#[export] Instance countably_infinite_bijection_inv_linv `{Countable A, Infinite A} :
  Cancel eq (countably_infinite_bijection_inv (A:=A)) countably_infinite_bijection.
Proof.
  intros i.
  rewrite countably_infinite_bijection_inv_spec.
  now apply countably_infinite_bijection_spec.
Qed.

#[export] Instance countably_infinite_bijection_inv_rinv `{Countable A, Infinite A} :
  Cancel eq countably_infinite_bijection (countably_infinite_bijection_inv (A:=A)).
Proof.
  intros i.
  rewrite countably_infinite_bijection_spec.
  now apply countably_infinite_bijection_inv_spec.
Qed.

#[export] Instance countably_infinite_bijection_inv_inj `{Countable A, Infinite A} :
  Inj eq eq (countably_infinite_bijection_inv (A:=A)).
Proof.
  apply cancel_inj.
Qed.

Lemma countably_infinite_exists_bijection `{Countable A, Infinite A,
  Countable B, Infinite B} : exists (g : A -> B) (ginv : B -> A),
    Inj (=) (=) g /\
    Inj (=) (=) ginv /\ Cancel eq g ginv /\ Cancel eq ginv g.
Proof.
  exists (countably_infinite_bijection ∘ countably_infinite_bijection_inv),
    (countably_infinite_bijection ∘ countably_infinite_bijection_inv).
  split_and!.
  - apply _.
  - apply _.
  - intros i.
    cbn.
    now rewrite 2 (cancel _ _ _).
  - intros i.
    cbn.
    now rewrite 2 (cancel _ _ _).
Qed.

Lemma and_from_l {P Q} :
  P /\ (P -> Q) -> P /\ Q.
Proof.
  tauto.
Qed.

Lemma partial_bijection_extension `{Countable A, Infinite A,
  Countable B, Infinite B}
  (l : list A) (f : A -> B) :
    ForallPairs (λ i j, f i = f j → i = j) l ->
    exists (g : A -> B) (ginv : B -> A), Inj (=) (=) g /\
    Inj (=) (=) ginv /\ Cancel eq g ginv /\ Cancel eq ginv g /\
    Forall (fun a => g a = f a) l.
Proof.
  intros Hlinj.
  assert (Hcount1 : Countable (dsig (λ a, a ∉ l))) by apply _.
  assert (Hinf1 : Infinite (dsig (λ a, a ∉ l))). 1:{
    unshelve refine {|infinite_fresh l' :=
      dexist (infinite_fresh (l ++ (proj1_sig <$> l'))) _|}; try typeclasses eauto.
    - intros Hin.
      apply (infinite_is_fresh (l ++ (proj1_sig <$> l'))).
      apply elem_of_app; left; apply Hin.
    - intros l'.
      unfold fresh.
      intros Hin%(elem_of_list_fmap_1 proj1_sig).
      cbn in Hin.
      apply (infinite_is_fresh (l ++ (proj1_sig <$> l'))).
      apply elem_of_app; right; apply Hin.
    - intros l' l'' Hl'.
      unfold fresh.
      apply dsig_eq.
      cbn.
      f_equiv.
      f_equiv.
      now apply fmap_Permutation.
  }
  assert (Hcount2 : Countable (dsig (λ a, a ∉ f <$> l))) by apply _.
  assert (Hinf2 : Infinite (dsig (λ a, a ∉ f <$> l))). 1:{
    unshelve refine {|infinite_fresh l' :=
      dexist (infinite_fresh ((f <$> l) ++ (proj1_sig <$> l'))) _|}; try typeclasses eauto.
    - intros Hin.
      apply (infinite_is_fresh ((f <$> l) ++ (proj1_sig <$> l'))).
      apply elem_of_app; left; apply Hin.
    - intros l'.
      unfold fresh.
      intros Hin%(elem_of_list_fmap_1 proj1_sig).
      cbn in Hin.
      apply (infinite_is_fresh ((f <$> l) ++ (proj1_sig <$> l'))).
      apply elem_of_app; right; apply Hin.
    - intros l' l'' Hl'.
      unfold fresh.
      apply dsig_eq.
      cbn.
      f_equiv.
      f_equiv.
      now apply fmap_Permutation.
  }
  assert (Hinhab : Inhabited (B -> A)) by
    now enough (Inhabited A) by apply _; apply (populate (fresh [])).
  destruct (countably_infinite_exists_bijection (A:=dsig (.∉ l))
    (B:=dsig (.∉ f <$> l))) as (h & hinv & Hh & Hhinv & Hh_hinv & Hhinv_h).
  exists (fun a => match decide (a ∈ l) with
    | left Ha => f a
    | right Hna => ` (h (dexist a Hna))
    end),
    (fun a => match decide (a ∈ f <$> l) with
    | left Ha => invfun f l a
    | right Hna => ` (hinv (dexist a Hna))
    end).
  apply and_comm, and_assoc, and_comm, and_assoc.
  apply and_from_l, conj; [|intros (?&?&?); split; apply cancel_inj].
  split_and!.
  - intros fi.
    destruct_decide (decide (fi ∈ f <$> l)) as Hfi.
    + apply elem_of_list_fmap in Hfi as (i & -> & Hi).
      rewrite invfun_linv by done.
      case_decide; done.
    + case_decide as Hin; [contradict Hin; refine (proj2_dsig (P:=(.∉ l)) _)|].
      rewrite dexists_proj1.
      rewrite (cancel _ _ _).
      done.
  - intros i.
    destruct_decide (decide (i ∈ l)) as Hi.
    + apply (elem_of_list_fmap_1 f) in Hi as Hfi.
      case_decide; [|done].
      now apply invfun_linv.
    + case_decide as Hin; [contradict Hin; refine (proj2_dsig (P:=(.∉ f <$> l)) _)|].
      rewrite dexists_proj1.
      rewrite (cancel _ _ _).
      done.
  - rewrite Forall_forall.
    intros i Hi.
    case_decide; done.
Qed.



Lemma partial_bijection_extension' `{Countable A, Infinite A,
  Countable B, Infinite B, FinSet A SA} (X : SA) (f : A -> B) :
  set_Forall2 (λ i j, f i = f j → i = j) X ->
    exists (g : A -> B) (ginv : B -> A), Inj (=) (=) g /\
    Inj (=) (=) ginv /\ Cancel eq g ginv /\ Cancel eq ginv g /\
    set_Forall (fun a => g a = f a) X.
Proof.
  rewrite set_Forall2_elements.
  intros Hg%partial_bijection_extension.
  setoid_rewrite set_Forall_elements.
  exact Hg.
Qed.



Lemma kmap_ext `{FinMap K1 M1, FinMap K2 M2} {A}
  (f g : K1 -> K2) (m : M1 A) :
  (forall k a, m !! k = Some a -> f k = g k) ->
  kmap f m =@{M2 A} kmap g m.
Proof.
  intros Hfg.
  unfold kmap.
  f_equal.
  apply list_fmap_ext; intros _ (k, a) Hka%elem_of_list_lookup_2%elem_of_map_to_list.
  cbn.
  f_equal; eauto.
Qed.

Lemma set_union_eq_l `{SemiSet A C} (X Y : C) : Y ⊆ X ->
  X ∪ Y ≡ X.
Proof.
  set_solver.
Qed.



Lemma map_inverses_empty `{FinMap A MA, FinMap B MB} :
  map_inverses (∅ :> MA B) (∅ :> MB A).
Proof.
  intros ? ?.
  rewrite 2 lookup_empty.
  easy.
Qed.

Lemma map_inverses_comm `{Lookup A B MA, Lookup B A MB} (ma : MA) (mb : MB) :
  map_inverses ma mb <-> map_inverses mb ma.
Proof.
  unfold map_inverses. firstorder.
Qed.

Lemma map_inverses_card_img `{FinMapDom A MA SA, !Elements A SA,
  !FinSet A SA, FinMap B MB, FinSet B SB}
  (ma : MA B) (mb : MB A) :
  map_inverses ma mb ->
  size (dom ma :> SA) = size (map_img ma :> SB).
Proof.
  intros Hinv.

  rewrite map_dom_img_eq_card_iff_inj.
  intros ? ? ? ?%Hinv ?%Hinv.
  congruence.
Qed.

Lemma map_inverses_img `{FinMap A MA, FinMapDom B MB SB}
  (ma : MA B) (mb : MB A) :
    map_inverses ma mb ->
    map_img ma ≡@{SB} dom mb.
Proof.
  intros Hab x.
  rewrite elem_of_map_img, elem_of_dom.
  setoid_rewrite (fun x => Hab x).
  reflexivity.
Qed.


Lemma map_inverses_img_L `{FinMap A MA, FinMapDom B MB SB, !LeibnizEquiv SB}
  (ma : MA B) (mb : MB A) :
    map_inverses ma mb ->
    map_img ma =@{SB} dom mb.
Proof.
  unfold_leibniz.
  apply map_inverses_img.
Qed.


Lemma fold_right_map {A B C} (f : A -> B) (g : B -> C -> C) c l :
  fold_right g c (map f l) = fold_right (fun a c => g (f a) c) c l.
Proof.
  induction l; cbn; congruence.
Qed.
Local Instance fold_right_mor `{R : relation A} f
  (HProp : Morphisms.Proper (R ==> R ==> R) f) :
  Morphisms.Proper (R ==> eqlistA R ==> R) (fold_right f).
Proof.
  intros a a' Ha l l' Hl.
  revert a a' Ha.
  induction Hl; intros a a' Ha.
  - simpl.
    auto.
  - simpl.
    apply HProp; auto.
Qed.
Lemma fold_right_concat `{R : relation A} `{!Equivalence R} (f : A -> A -> A)
  {HfR : Proper (R ==> R ==> R)%signature f} (d : A)
  (Hd : forall a, R (f d a) a)
  (Hf : forall a b c, R (f (f a b) c) (f a (f b c))) ls :
  R (fold_right f d (concat ls))
  (fold_right f d (map (fun l => fold_right f d l) ls)).
Proof.
  induction ls; [reflexivity|].
  cbn.
  rewrite fold_right_app.
  rewrite IHls.
  remember (fold_right f d (map (fold_right f d) ls)) as v eqn:Heqv.
  clear Heqv.
  induction a; [now cbn; auto|].
  cbn.
  rewrite IHa.
  symmetry.
  apply Hf.
Qed.



Lemma vmap_id' {A n} (f : A -> A) (v : vec A n) :
  (forall a, a ∈ vec_to_list v -> f a = a) ->
  vmap f v = v.
Proof.
  rewrite <- Forall_forall, vec_to_list_to_list, <- Vector.to_list_Forall.
  intros Hall.
  induction Hall; [done|].
  cbn.
  congruence.
Qed.
Lemma zip_with_to_fmap_l {A B C} (f : A -> C) (l : list A) (k : list B) :
  length l = length k ->
  zip_with (λ a _, f a) l k = f <$> l.
Proof.
  intros Hall%Forall2_same_length.
  induction Hall; cbn; congruence.
Qed.
Lemma zip_with_to_fmap_r {A B C} (f : B -> C) (l : list A) (k : list B) :
  length l = length k ->
  zip_with (λ _ b, f b) l k = f <$> k.
Proof.
  intros Hall%Forall2_same_length.
  induction Hall; cbn; congruence.
Qed.


Definition vec_to_list_ind {A} (P : list A -> Type)
  (HP : forall n (v : vec A n), P v) : forall l, P l :=
  fun l => eq_rect _ P (HP _ (list_to_vec l)) _ (vec_to_list_to_vec l).



Lemma sumbool_same {P Q A} (HPQ : {P} + {Q}) (a : A) :
  (if HPQ then a else a) = a.
Proof.
  now destruct HPQ.
Qed.
Lemma decide_same `{Decision P} `(a : A) :
  (if decide P then a else a) = a.
Proof.
  apply sumbool_same.
Qed.


Lemma flat_map_to_list_bind `(f : A -> list B) (l : list A) :
  flat_map f l = l ≫= f.
Proof.
  now rewrite list_bind_flat_map.
Qed.


Lemma list_inj_exists_partial_inverse `{EqDecision A, EqDecision B,
  Inhabited (B -> A)}
  (dom : list A) (f : A -> B) :
  (forall a b, a ∈ dom -> b ∈ dom -> f a = f b -> a = b) ->
  exists (g : B -> A), forall a, a ∈ dom -> g (f a) = a.
Proof.
  induction dom; [now exists inhabitant|].
  intros Hf.
  tspecialize IHdom by now intros ? ? ? ?; apply Hf; now constructor.
  destruct IHdom as (g & Hg).
  exists (<[f a := a]> g).
  intros c [-> | Hc]%elem_of_cons.
  - apply fn_lookup_insert.
  - destruct_decide (decide (f c = f a)) as Hfc.
    + rewrite Hfc.
      rewrite fn_lookup_insert.
      symmetry.
      revert Hfc.
      apply Hf; apply elem_of_cons; auto.
    + rewrite fn_lookup_insert_ne by easy.
      now apply Hg.
Qed.


Lemma list_find_app `(P : X -> Prop) `{forall x, Decision (P x)} (l l' : list X) :
  list_find P (l ++ l') =
  list_find P l ∪ (prod_map (Nat.add (length l)) id <$> list_find P l').
Proof.
  induction l.
  - cbn.
    rewrite option_union_left_id.
    symmetry.
    etransitivity; [|apply option_fmap_id].
    apply option_fmap_ext; now intros [].
  - cbn.
    case_decide; [now rewrite union_Some_l|].
    rewrite IHl.
    destruct (list_find P l) as [[]|].
    + cbn.
      now rewrite 2 union_Some_l.
    + cbn.
      rewrite 2 option_union_left_id.
      rewrite <- option_fmap_compose.
      reflexivity.
Qed.



Definition make_vecs_map {A n m} (ins : vec positive n) (outs : vec positive m)
  (insv : vec A n) (outsv : vec A m) : Pmap A :=
  list_to_map (vzip ins insv) ∪ list_to_map (vzip outs outsv).

Lemma dom_make_vecs_map {A n m} (ins : vec _ n) (outs : vec _ m)
  (v w : vec A _) :
  dom (make_vecs_map ins outs v w) =
  list_to_set (ins ++ outs).
Proof.
  unfold_leibniz.
  unfold make_vecs_map.
  rewrite dom_union, 2 dom_list_to_map.
  rewrite 2 vec_to_list_zip_with, list_to_set_app.
  now rewrite 2 fst_zip by now rewrite 2 length_vec_to_list.
Qed.




Definition vremove {A n} (i : fin n) : vec A n -> vec A (pred n) :=
  Fin.t_rect (fun n _ => vec A n -> vec A (pred n)) (fun _ => Vector.tl)
  (fun n i => match i with
    | 0%fin => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    | FS i' => fun IHi v => Vector.hd v ::: IHi (Vector.tl v)
    end) n i.

Lemma vec_to_list_vremove {A n} (i : fin n) (v : vec A n) :
  vec_to_list (vremove i v) = delete (i:>nat) (v:>list A).
Proof.
  unfold vremove.
  revert v; induction i.
  - cbn.
    now apply vec_S_inv.
  - apply vec_S_inv.
    intros x v.
    cbn.
    destruct i.
    + cbn.
      f_equal.
      now destruct v using vec_S_inv.
    + cbn.
      f_equal.
      apply IHi.
Qed.



Lemma list_fmap_subseteq {A B} (f : A -> B) (l1 l2 : list A) :
  l1 ⊆ l2 -> f <$> l1 ⊆ f <$> l2.
Proof.
  intros Hl b (a & -> & ?%Hl)%elem_of_list_fmap.
  now apply elem_of_list_fmap_1.
Qed.

Lemma list_subseteq_app {A} {l1 l1' l2 l2' : list A} :
  l1 ⊆ l1' -> l2 ⊆ l2' -> l1 ++ l2 ⊆ l1' ++ l2'.
Proof.
  intros;
  apply list_subseteq_app_iff_l, conj;
    [apply list_subseteq_app_l|apply list_subseteq_app_r];
  done.
Qed.

Lemma uncurry_alt {A B C} (f : A -> B -> C) p :
  uncurry f p = f p.1 p.2.
Proof.
  now destruct p.
Qed.



Lemma NoDup_fmap_ind `(f : A -> B) (P : list A -> Prop)
  (Pnil : P []) (Pcons : forall a l, f a ∉ f <$> l -> NoDup (f <$> l) ->
    P l -> P (a :: l)) : forall l, NoDup (f <$> l) -> P l.
Proof.
  intros l.
  induction l; [easy|].
  cbn; rewrite NoDup_cons.
  intros []; eauto.
Qed.

Lemma zip_with_irrel_l {A B C} (f : B -> C) (l l' : list A) (k : list B) :
  length l = length l' ->
  zip_with (λ _ b, f b) l k = zip_with (λ _ b, f b) l' k.
Proof.
  intros Hall%Forall2_same_length.
  revert k;
  induction Hall; intros []; cbn; congruence.
Qed.

Lemma zip_with_irrel_r {A B C} (f : A -> C) (l : list A) (k k' : list B) :
  length k = length k' ->
  zip_with (λ a _, f a) l k = zip_with (λ a _, f a) l k'.
Proof.
  intros Hall%Forall2_same_length.
  revert l;
  induction Hall; intros []; cbn; congruence.
Qed.

Lemma map_to_list_disj_union `{FinMap K M} {A} (m1 m2 : M A) :
  m1 ##ₘ m2 ->
  map_to_list (m1 ∪ m2) ≡ₚ map_to_list m1 ++ map_to_list m2.
Proof.
  intros Hdisj.
  pose proof Hdisj as Hdisj'.
  rewrite map_disjoint_alt in Hdisj'.
  apply NoDup_Permutation.
  - apply NoDup_map_to_list.
  - apply NoDup_app; split_and!; try apply NoDup_map_to_list.
    intros (k, a) Hka%elem_of_map_to_list Hka'%elem_of_map_to_list.
    destruct (Hdisj' k); congruence.
  - intros (k, a).
    rewrite elem_of_app, 3 elem_of_map_to_list.
    rewrite lookup_union_Some by done.
    done.
Qed.
Lemma map_to_list_kmap `{FinMap K1 M1, FinMap K2 M2} (f : K1 -> K2)
  `{Hf : !Inj eq eq f} {A} (m : M1 A) :
  map_to_list (kmap f m :> M2 A) ≡ₚ prod_map f id <$> map_to_list m.
Proof.
  unfold kmap.
  apply map_to_list_to_map.
  rewrite fsts_prod_map, (NoDup_fmap _).
  apply NoDup_fst_map_to_list.
Qed.
Lemma map_disjoint_alt_neg `{FinMap K M} {A} (m1 m2 : M A) :
  m1 ##ₘ m2 <-> forall k a b, m1 !! k = Some a -> m2 !! k = Some b -> False.
Proof.
  rewrite map_disjoint_alt.
  apply forall_proper; intros k.
  rewrite 2 eq_None_not_Some.
  unfold is_Some.
  destruct (m1 !! k), (m2 !! k); naive_solver.
Qed.
Lemma kmap_inj2_disjoint `{FinMap K1 M1, FinMap K2 M2} {I} `{R : relation I} {A}
  (f : I -> K1 -> K2) `{Hf : !Inj2 R eq eq f} (m m' : M1 A) i j :
  ~ R i j ->
  (kmap (f i) m :> M2 A) ##ₘ kmap (f j) m'.
Proof.
  intros Hrij.
  rewrite map_disjoint_alt_neg.
  intros k a b (? & _ & Hfij)%lookup_kmap_Some_2
    (? & _ & <-)%lookup_kmap_Some_2.
  now apply Hf in Hfij.
Qed.

Lemma set_map_inj2_disjoint `{FinSet A SA, SemiSet B SB}
  {I} `{R : relation I}
  (f : I -> A -> B) `{Hf : !Inj2 R eq eq f} (X Y : SA) i j :
  ~ R i j ->
  (set_map (f i) X :> SB) ## set_map (f j) Y.
Proof.
  set_solver.
Qed.


#[export] Instance from_option_dec {A} (P : Prop) (Q : A -> Prop) (ma : option A) :
  Decision P -> (forall a, Decision (Q a)) -> Decision (from_option Q P ma) :=
  fun HP HQ =>
  match ma with
  | Some a => (HQ a)
  | None => HP
  end.

Lemma filter_snd_imap_pair_compose {A B} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (f : nat -> B) (l : list A) :
  filter (P ∘ snd) (imap (pair ∘ f) l) =
  (prod_map f id) <$> filter (P ∘ snd) (imap pair l).
Proof.
  revert B f;
  induction l; intros B f; [reflexivity|].
  cbn.
  case_decide as HPa.
  - cbn.
    f_equal.
    rewrite Combinators.compose_assoc, 2 IHl.
    rewrite <- list_fmap_compose.
    reflexivity.
  - rewrite Combinators.compose_assoc, 2 IHl.
    rewrite <- list_fmap_compose.
    reflexivity.
Qed.

Lemma from_option_fmap {A B C} (f : A -> B) (g : B -> C) (d : C) (ma : option A) :
  from_option g d (f <$> ma) = from_option (g ∘ f) d ma.
Proof.
  now destruct ma.
Qed.


Lemma filter_snd_imap_pair {A} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  filter (P ∘ snd) (imap pair l) =
  imap (λ idx v, ((filter (λ i, from_option P False (l !! i)) (seq 0 (length l))) !!! idx, v))
    (filter P l).
Proof.
  induction l; [reflexivity|].
  cbn.
  eenough (Hen : _).
  - case_decide as HPa; [|exact Hen].
    cbn.
    f_equal.
    apply Hen.
  - rewrite (filter_snd_imap_pair_compose P S).
    rewrite IHl.
    rewrite fmap_imap.
    apply imap_ext.
    intros i x Hi.
    cbn.
    f_equal.
    rewrite <- fmap_S_seq.
    symmetry.
    rewrite (list_filter_fmap S).
    unfold compose; cbn.
    apply list_lookup_total_fmap.
    apply lookup_lt_Some in Hi as Hilt.
    eapply Nat.lt_le_trans; [apply Hilt|].
    apply eq_reflexivity.
    clear.
    induction l; [reflexivity|].
    cbn.
    eenough (Heq : _).
    + case_decide as HPa; [|exact Heq].
      cbn.
      rewrite Heq.
      reflexivity.
    + rewrite <- fmap_S_seq, (list_filter_fmap S).
      rewrite length_fmap.
      apply IHl.
Qed.


Lemma length_filter_snd_imap_pair {A} (P : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  length (filter (P ∘ snd) (imap pair l)) =
  length (filter P l).
Proof.
  now rewrite filter_snd_imap_pair, length_imap.
Qed.


Lemma lookup_vec_to_list {A n} (v : vec A n) i :
  vec_to_list v !! i =
  guard (i < n) ≫= fun H => Some (v !!! nat_to_fin H).
Proof.
  apply option_eq; intros a.
  rewrite <- vlookup_lookup'.
  rewrite bind_Some.
  cbn.
  split; [|naive_solver].
  intros (Hlt & <-).
  exists Hlt.
  split; [case_guard; [f_equal; apply proof_irrel|done]|done].
Qed.

Lemma lookup_vec_to_list_fin {A n} (v : vec A n) (i : fin n) :
  vec_to_list v !! (i:>nat) =
  Some (v !!! i).
Proof.
  now apply vlookup_lookup.
Qed.


Lemma set_map_difference `{FinSet A SA, Set_ B SB}
  (f : A -> B) `{Hf : !Inj eq eq f} (X Y : SA) :
  set_map f (X ∖ Y) ≡@{SB} set_map f X ∖ set_map f Y.
Proof.
  set_solver.
Qed.

Lemma set_map_difference_L `{FinSet A SA, Set_ B SB, !LeibnizEquiv SB}
  (f : A -> B) `{Hf : !Inj eq eq f} (X Y : SA) :
  set_map f (X ∖ Y) =@{SB} set_map f X ∖ set_map f Y.
Proof.
  unfold_leibniz.
  now apply set_map_difference.
Qed.

Lemma set_map_dom_map_img `{FinMapDom K M SK, !Elements K SK, !FinSet K SK,
  SemiSet A SA, Inhabited A} (m : M A) :
  set_map (m !!!.) (dom m :> SK) ≡@{SA} map_img m.
Proof.
  intros i.
  split.
  - intros (j & -> & [mj Hmj]%elem_of_dom)%elem_of_map.
    rewrite lookup_total_alt, Hmj.
    eapply elem_of_map_img_2; eauto.
  - intros (j & Hij)%elem_of_map_img.
    apply elem_of_map.
    exists j.
    rewrite lookup_total_alt, Hij.
    split; [done|].
    now apply elem_of_dom_2 in Hij.
Qed.

Lemma set_map_dom_map_img_L `{FinMapDom K M SK, !Elements K SK, !FinSet K SK,
  SemiSet A SA, Inhabited A, !LeibnizEquiv SA} (m : M A) :
  set_map (m !!!.) (dom m :> SK) =@{SA} map_img m.
Proof.
  unfold_leibniz.
  apply set_map_dom_map_img.
Qed.



Lemma difference_empty_l `{Set_ A SA} (X : SA) :
  ∅ ∖ X ≡ ∅.
Proof.
  set_solver.
Qed.
Lemma difference_empty_l_L `{Set_ A SA, !LeibnizEquiv SA} (X : SA) :
  ∅ ∖ X = ∅.
Proof.
  apply leibniz_equiv_iff, difference_empty_l.
Qed.


Lemma fn_lookup_singleton_r `{EqDecision A} (a b : A) :
  {[a := b]} b = b.
Proof.
  now cbv; case_match.
Qed.


Lemma set_map_difference_subseteq `{FinSet A SA, Set_ B SB}
  (f : A -> B) (X Y : SA)  :
  set_map f X ∖ set_map f Y ⊆@{SB} set_map f (X ∖ Y).
Proof.
  set_solver.
Qed.

Lemma set_map_difference_strong `{FinSet A SA, Set_ B SB}
  (f : A -> B) (X Y : SA)
  (Hf : set_Forall2 (λ x y, f x = f y -> x = y) (X ∪ Y)) :
  set_map f (X ∖ Y) ≡@{SB} set_map f X ∖ set_map f Y.
Proof.
  intros x; split; [|apply set_map_difference_subseteq].
  rewrite elem_of_difference, 3 elem_of_map.
  intros (i & -> & [HiX HiY]%elem_of_difference).
  split; [eauto|].
  intros (j & Hfij & Hj).
  enough (i = j) by congruence.
  revert Hfij.
  apply Hf.
  - now apply elem_of_union_l.
  - now apply elem_of_union_r.
Qed.

Lemma set_map_difference_strong_L `{FinSet A SA, Set_ B SB, !LeibnizEquiv SB}
  (f : A -> B) (X Y : SA)
  (Hf : set_Forall2 (λ x y, f x = f y -> x = y) (X ∪ Y)) :
  set_map f (X ∖ Y) =@{SB} set_map f X ∖ set_map f Y.
Proof.
  apply leibniz_equiv_iff.
  now apply set_map_difference_strong.
Qed.

Lemma set_map_fn_singleton_difference `{FinSet A SA, !RelDecision (∈@{SA})}
  (a b : A) (X Y : SA) :
  set_map {[a := b]} (X ∖ Y) ≡@{SA}
  set_map {[a := b]} X ∖ set_map {[a := b]} Y ∪
  if decide (a ∈ X ∖ Y \/ b ∈ X ∖ Y) then {[b]} else ∅.
Proof.
  rewrite set_map_fn_singleton.
  case_decide as HaXY.
  - rewrite decide_True by now left.
    apply elem_of_difference in HaXY as [HaX HaY].
    rewrite 2 set_map_fn_singleton.
    rewrite decide_True, decide_False by done.
    set_solver - HaX HaY.
  - rewrite (decide_ext _ (b ∈ X ∖ Y)) by naive_solver.
    rewrite 2 set_map_fn_singleton.
    apply not_elem_of_difference in HaXY as [HaX | HaY].
    + rewrite decide_False by done.
      case_decide as HaY; [|case_decide; set_solver].
      case_decide as HbXY; [|set_solver].
      rewrite 2 (union_empty_r _).
      rewrite difference_disjoint by set_solver.
      rewrite (difference_disjoint X {[a]}) by set_solver.
      apply elem_of_difference in HbXY as [HbX HbY].
      rewrite <- difference_difference_l.
      rewrite difference_union, (union_comm _).
      rewrite (subseteq_union _ _).1 by set_solver.
      set_solver.
    + rewrite (decide_True _ _ HaY).
      rewrite (union_empty_r _).
      rewrite difference_disjoint by set_solver.
      destruct_decide (decide (b ∈ X ∖ Y)) as HbXY;
      [|case_decide; set_solver].
      apply elem_of_difference in HbXY as [HbX HbY].
      rewrite <- difference_difference_l.
      rewrite difference_union.
      case_decide; set_solver.
Qed.


Lemma set_map_fn_singleton_difference_L `{FinSet A SA,
  !LeibnizEquiv SA, !RelDecision (∈@{SA})}
  (a b : A) (X Y : SA) :
  set_map {[a := b]} (X ∖ Y) =@{SA}
  set_map {[a := b]} X ∖ set_map {[a := b]} Y ∪
  if decide (a ∈ X ∖ Y \/ b ∈ X ∖ Y) then {[b]} else ∅.
Proof.
  unfold_leibniz.
  apply set_map_fn_singleton_difference.
Qed.

Lemma difference_singleton_l_case `{FinSet A SA, !RelDecision (∈@{SA})}
  (a : A) (X : SA) :
  {[a]} ∖ X ≡ if decide (a ∈ X) then ∅ else {[a]}.
Proof.
  case_decide; set_solver.
Qed.

Lemma difference_singleton_l_case_L `{FinSet A SA,
  !LeibnizEquiv SA, !RelDecision (∈@{SA})}
  (a : A) (X : SA) :
  {[a]} ∖ X = if decide (a ∈ X) then ∅ else {[a]}.
Proof.
  apply leibniz_equiv_iff, difference_singleton_l_case.
Qed.

Lemma set_map_difference_respectful_l `{FinSet A SA, Set_ B SB}
  (f : A -> B) (X X' Y : SA) : X ∖ Y ≡ X' ∖ Y ->
  set_map f X ∖ set_map f Y ≡@{SB} set_map f X' ∖ set_map f Y.
Proof.
  set_solver.
Qed.

Lemma set_map_difference_respectful_l_L `{FinSet A SA, Set_ B SB, !LeibnizEquiv SB}
  (f : A -> B) (X X' Y : SA) : X ∖ Y ≡ X' ∖ Y ->
  set_map f X ∖ set_map f Y =@{SB} set_map f X' ∖ set_map f Y.
Proof.
  intros Heq%(set_map_difference_respectful_l (SB:=SB) f).
  now unfold_leibniz.
Qed.

#[export] Instance prod_map_proper `{RA : relation A, RB : relation B, RC : relation C,
  RD : relation D} (f : A -> C) (g : B -> D) :
  Proper (RA ==> RC) f -> Proper (RB ==> RD) g ->
  Proper (prod_relation RA RB ==> prod_relation RC RD) (prod_map f g).
Proof.
  firstorder.
Qed.

#[export] Instance prod_map_proper_equiv `{Equiv A, Equiv B, Equiv C, Equiv D}
  (f : A -> C) (g : B -> D) :
  Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
  Proper (equiv ==> equiv) (prod_map f g).
Proof.
  apply prod_map_proper.
Qed.