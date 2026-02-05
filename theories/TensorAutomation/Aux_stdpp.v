(* Extra bits for stdpp *)
From stdpp Require Import decidable.
Require Import Aux.

From stdpp Require Import prelude.


From stdpp Require Import strings fin_maps pmap gmap hlist.
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
