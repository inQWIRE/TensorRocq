Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp Aux_pos.
Require Export HyperGraph.
Require Import TESyntax.
Require Export TensorGraph SizedGraph.



(* FIXME: Move *)
Fixpoint vbind {A B} {nf : A -> nat} (f : forall a, vec B (nf a)) {n} :
  forall (v : vec A n), vec B (sum_list_with nf v) :=
  match n with
  | O => vec_0_inv _ [#]
  | S n => vec_S_inv _ (fun a v => f a +++ vbind f v)
  end.

Lemma vec_to_list_bind {A B} {nf : A -> nat}
  (f : forall a, vec B (nf a)) {n} (v : vec A n) :
  vec_to_list (vbind f v) = (vec_to_list v) ≫= (λ a, vec_to_list (f a)).
Proof.
  induction v; [done|].
  cbn.
  now rewrite vec_to_list_app, IHv.
Qed.

Lemma is_encode_dec (A : Type) `{Countable A} (p : positive) :
  {a : A & encode a = p} + {forall a : A, encode a <> p}.
Proof.
  destruct (decode p :> option A) as [a|] eqn:Hdec.
  - destruct_decide (decide (encode a = p)) as Ha.
    + now left; exact (existT _ Ha).
    + right.
      abstract (
      intros a' Ha';
      rewrite <- Ha', decode_encode in Hdec;
      congruence).
  - right.
    abstract (intros a <-; now rewrite decode_encode in Hdec).
Defined.


Lemma is_encode_dec' (A : Type) `{Countable A} (p : positive) :
  {exists! a : A, encode a = p} + {forall a : A, encode a <> p}.
Proof.
  destruct (is_encode_dec A p) as [Henc|Hnenc]; [|now right].
  left.
  destruct Henc as [a Ha].
  exists a.
  split; [done|].
  subst; now intros ? ?%encode_inj.
Qed.


Lemma is_encode_dec_encode `{Countable A} (a : A) :
  is_encode_dec A (encode a) = inleft (existT a eq_refl).
Proof.
  destruct (is_encode_dec A (encode a)) as [Ha|Ha];
  [|now exfalso; eapply Ha; eauto].
  f_equal.
  destruct Ha as [a' Haa'].
  apply encode_inj in Haa' as Heq.
  subst a'.
  f_equal.
  apply proof_irrel.
Qed.

Definition encode_map `{Countable A, Countable B}
  (f : A -> B) (p : positive) : positive :=
  match is_encode_dec A p with
  | inleft (existT a _) => encode (f a)
  | inright _ => p
  end.

Lemma encode_map_encode `{Countable A, Countable B}
  (f : A -> B) (a : A) :
  encode_map f (encode a) = encode (f a).
Proof.
  unfold encode_map.
  now rewrite is_encode_dec_encode.
Qed.

Lemma encode_map_not_encode `{Countable A, Countable B}
  (f : A -> B) k : (forall a : A, k <> encode a) ->
  encode_map f k = k.
Proof.
  intros Hk.
  unfold encode_map.
  destruct (is_encode_dec _ k) as [[? []%eq_sym%Hk]|].
  done.
Qed.

#[export] Instance encode_map_inj `{Countable A}
  (f : A -> A) `{Hf : !Inj eq eq f} :
  Inj eq eq (encode_map f).
Proof.
  intros k l.
  unfold encode_map.
  destruct (is_encode_dec _ k) as [[a <-]|Hk],
      (is_encode_dec _ l) as [[a' <-]|Hl].
  - intros ?%encode_inj%Hf.
    congruence.
  - intros []%Hl.
  - intros []%eq_sym%Hk.
  - done.
Qed.




Definition map_bind `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m : M1 A) : M2 B :=
  map_fold (λ k a, union (f k a)) ∅ m.

Lemma map_bind_empty `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) :
  map_bind f ∅ = ∅.
Proof.
  apply map_fold_empty.
Qed.

Lemma map_bind_insert_first_key `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (k : K1) (a : A) (m : M1 A) :
  m !! k = None -> map_first_key (<[k := a]> m) k ->
  map_bind f (<[k := a]> m) = f k a ∪ map_bind f m.
Proof.
  intros Hmk Hfst.
  unfold map_bind.
  rewrite map_fold_insert_first_key by done.
  done.
Qed.

Lemma map_bind_alt `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m : M1 A) :
  map_bind f m = list_to_map (map_to_list m ≫= map_to_list ∘ uncurry f).
Proof.
  induction m using map_first_key_ind.
  - rewrite map_bind_empty, map_to_list_empty.
    done.
  - rewrite map_bind_insert_first_key by done.
    rewrite map_to_list_insert_first_key by done.
    cbn.
    rewrite list_to_map_app.
    rewrite list_to_map_to_list.
    congruence.
Qed.

Lemma map_bind_singleton `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (k : K1) (a : A) :
  map_bind f {[k := a]} = f k a.
Proof.
  rewrite map_bind_alt.
  rewrite map_to_list_singleton.
  cbn.
  rewrite app_nil_r.
  apply list_to_map_to_list.
Qed.

Lemma lookup_map_bind_gen `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m : M1 A) (k : K2) :
  map_bind f m !! k = foldr union None ((.!! k) <$> (uncurry f <$> map_to_list m)).
Proof.
  induction m using map_first_key_ind.
  - rewrite map_bind_empty, map_to_list_empty.
    cbn.
    apply lookup_empty.
  - rewrite map_bind_insert_first_key by done.
    rewrite map_to_list_insert_first_key by done.
    cbn.
    rewrite lookup_union, IHm.
    done.
Qed.


Lemma lookup_map_bind_Some_1 `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m : M1 A) (k2 : K2) (b : B) :
  map_bind f m !! k2 = Some b ->
  exists k1 a, m !! k1 = Some a /\ f k1 a !! k2 = Some b.
Proof.
  induction m using map_first_key_ind.
  - rewrite map_bind_empty, lookup_empty.
    done.
  - rewrite map_bind_insert_first_key by done.
    rewrite lookup_union.
    rewrite union_Some.
    intros [Hfi | [Hfi Hex%IHm]].
    + exists i, x.
      now rewrite lookup_insert.
    + destruct Hex as (k1 & a & Hmk1 & Hfk1).
      exists k1, a.
      now rewrite lookup_insert_ne by congruence.
Qed.


Lemma map_bind_NoDup_helper_aux `{FinMap K1 M1}
  {K2 A B} (f : K1 * A -> list (K2 * B)) (m : M1 A) :
  (forall ka, NoDup (f ka).*1) ->
  (forall ka ka', ka.1 <> ka'.1 -> (f ka).*1 ## (f ka').*1) ->
  NoDup (map_to_list m ≫= f).*1.
Proof.
  intros Hfdup Hf.
  rewrite list_bind_fmap.
  apply NoDup_bind, NoDup_map_to_list.
  - intros [k1 a] [k1' a'] k2.
    rewrite 2 elem_of_map_to_list.
    intros Hmk1 Hmk1'.
    cbn.
    rewrite 2 elem_of_list_fmap, 2 exists_pair.
    cbn.
    intros (_ & b & <- & Hb)
       (_ & b' & <- & Hb').
    enough (k1 = k1') by congruence.
    apply dec_stable.
    intros Hne%(Hf (k1, a) (k1', a')).
    specialize (Hne k2).
    apply Hne; [now apply (elem_of_list_fmap_1 fst) in Hb|
    now apply (elem_of_list_fmap_1 fst) in Hb'].
  - intros ? _.
    apply Hfdup.
Qed.


Lemma map_bind_NoDup_helper `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) m :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  NoDup (map_to_list m ≫= map_to_list ∘ uncurry f).*1.
Proof.
  intros Hf.
  apply map_bind_NoDup_helper_aux.
  - intros; apply NoDup_fst_map_to_list.
  - intros [k a] [k' a'] Hk.
    cbn.
    specialize (Hf k k' a a' Hk).
    intros x.
    specialize (Hf x).
    rewrite 2 elem_of_list_fmap.
    rewrite 2 exists_pair; cbn.
    setoid_rewrite elem_of_map_to_list.
    intros (? & ? & -> & Heq1)
      (? & ? & -> & Heq2); now rewrite Heq1, Heq2 in Hf.
Qed.

Lemma map_bind_insert `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (k : K1) (a : A) (m : M1 A) :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  m !! k = None ->
  map_bind f (<[k := a]> m) = f k a ∪ map_bind f m.
Proof.
  intros Hf Hmk.
  rewrite map_bind_alt.
  erewrite list_to_map_proper. 2:{
    now apply map_bind_NoDup_helper.
  }
  2:{
    rewrite map_to_list_insert by done.
    cbn.
    done.
  }
  rewrite list_to_map_app, list_to_map_to_list.
  now rewrite <- map_bind_alt.
Qed.




Lemma lookup_map_bind_Some `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m : M1 A) :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  forall k2 b,
  map_bind f m !! k2 = Some b <->
  exists k1 a, m !! k1 = Some a /\ f k1 a !! k2 = Some b.
Proof.
  intros Hf k2 b.
  split; [apply lookup_map_bind_Some_1|].
  intros Hex'.
  pose proof (Hex' : map_Exists _ m) as Hex.
  clear Hex'.
  revert m Hex.
  refine (map_Exists_ind _ (λ _, _) _ _).
  - intros k1 a Hfk1.
    now rewrite map_bind_singleton.
  - intros m k1 a Hmk1 Hex Hm_k2.
    rewrite map_bind_insert by done.
    rewrite lookup_union_r; [done|].
    destruct Hex as (k1' & a' & Hmk1' & Hfk1').
    specialize (Hf k1 k1' a a').
    tspecialize Hf by congruence.
    rewrite map_disjoint_alt in Hf.
    specialize (Hf k2) as []; congruence.
Qed.


Lemma map_bind_disj_union `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m m' : M1 A) :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  m ##ₘ m' ->
  map_bind f (m ∪ m') = map_bind f m ∪ map_bind f m'.
Proof.
  intros Hf Hm.
  induction m using map_ind; [now rewrite map_bind_empty, 2 map_empty_union|].
  rewrite <- insert_union_l.
  simplify_map_eq.
  rewrite map_bind_insert; [|done|]. 2:{
    now rewrite lookup_union_None.
  }
  rewrite map_bind_insert by done.
  rewrite IHm by done.
  now rewrite map_union_assoc.
Qed.


Lemma map_bind_insert_dom_eq `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (k : K1) (a : A) (m : M1 A) :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  (forall k a a' k2, is_Some (f k a !! k2) <-> is_Some (f k a' !! k2)) ->
  map_bind f (<[k := a]> m) = f k a ∪ map_bind f m.
Proof.
  intros Hf Hfdom.
  destruct (m !! k) as [a'|] eqn:Hmk.
  - rewrite <- insert_delete_insert.
    rewrite map_bind_insert by now try rewrite lookup_delete.
    rewrite <- (insert_delete m k a' Hmk) at 2.
    rewrite map_bind_insert by now try rewrite lookup_delete.
    rewrite map_union_assoc.
    f_equal.
    apply map_eq; intros k2.
    apply option_eq; intros b.
    rewrite lookup_union, union_Some.
    split; [auto|].
    intros [? | [HNone HSome]]; [done|].
    apply eq_None_not_Some in HNone.
    apply mk_is_Some in HSome.
    erewrite Hfdom in HNone.
    now apply HNone in HSome.
  - now rewrite map_bind_insert by done.
Qed.

Lemma map_bind_union_dom_eq  `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (m m' : M1 A) :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  (forall k a a' k2, is_Some (f k a !! k2) <-> is_Some (f k a' !! k2)) ->
  map_bind f (m ∪ m') = map_bind f m ∪ map_bind f m'.
Proof.
  intros Hf Hfdom.
  induction m using map_ind; [now rewrite map_bind_empty, 2 map_empty_union|].
  rewrite <- insert_union_l.
  rewrite 2 map_bind_insert_dom_eq by done.
  rewrite IHm.
  now rewrite map_union_assoc.
Qed.


Lemma map_bind_ext `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f g : K1 -> A -> M2 B) m :
  (forall k a, m !! k = Some a -> f k a = g k a) ->
  map_bind f m = map_bind g m.
Proof.
  intros Hfg.
  rewrite 2 map_bind_alt.
  f_equal.
  apply list_bind_ext_strong.
  intros [k a] Hka%elem_of_map_to_list.
  cbn.
  f_equal.
  now apply Hfg.
Qed.


Lemma map_bind_fmap `{FinMap K1 M1, FinMap K2 M2}
  {A B C} (f : K1 -> A -> M2 B) (g : B -> C) m :
  g <$> map_bind f m = map_bind (λ k a, g <$> f k a) m.
Proof.
  rewrite 2 map_bind_alt.
  rewrite <- list_to_map_fmap.
  rewrite list_bind_fmap.
  f_equal.
  apply list_bind_ext_strong.
  intros [k a] _.
  cbn.
  now rewrite map_to_list_fmap.
Qed.

Lemma map_fmap_bind `{FinMap K1 M1, FinMap K2 M2}
  {A B C} (g : A -> B) (f : K1 -> B -> M2 C) m :
  map_bind f (g <$> m) = map_bind (λ k a, f k (g a)) m.
Proof.
  rewrite 2 map_bind_alt.
  rewrite map_to_list_fmap.
  rewrite list_fmap_bind.
  f_equal.
  apply list_bind_ext_strong.
  intros [k a] _.
  done.
Qed.


Lemma map_bind_kmap `{FinMap K1 M1, FinMap K2 M2, FinMap K3 M3}
  {A B} (f : K1 -> A -> M2 B) (g : K2 -> K3) `{Hg : !Inj eq eq g} m :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  kmap g $ map_bind f m = map_bind (λ k a, kmap g $ f k a) m.
Proof.
  intros Hf.
  apply map_eq.
  intros k3.
  apply option_eq; intros b.
  rewrite lookup_map_bind_Some by
    now intros; apply (map_disjoint_kmap _ _ _).2; auto.
  setoid_rewrite (lookup_kmap_Some _).
  setoid_rewrite lookup_map_bind_Some; [|done].
  naive_solver.
Qed.

Lemma map_kmap_bind `{FinMap K1 M1, FinMap K2 M2, FinMap K3 M3}
  {A B} (g : K1 -> K2) `{Hg : !Inj eq eq g} (f : K2 -> A -> M3 B) m :
  (forall k k' a a', k <> k' -> f k a ##ₘ f k' a') ->
  map_bind f (kmap g m) = map_bind (λ k a, f (g k) a) m.
Proof.
  intros Hf.
  apply map_eq.
  intros k3.
  apply option_eq; intros b.
  rewrite lookup_map_bind_Some by done.
  rewrite lookup_map_bind_Some by now intros; apply Hf; apply not_inj.
  setoid_rewrite (lookup_kmap_Some g).
  naive_solver.
Qed.

Lemma filter_map_bind' `{FinMap K1 M1, FinMap K2 M2}
  {A B} (f : K1 -> A -> M2 B) (P : K2 -> Prop)
  `{HP : forall k, Decision (P k)} m :
  filter (λ ka, P ka.1) (map_bind f m) = map_bind (λ k a, filter (λ ka, P ka.1) (f k a)) m.
Proof.
  induction m using map_first_key_ind;
  [now rewrite 2 map_bind_empty, map_filter_empty|].
  rewrite 2 map_bind_insert_first_key by done.
  rewrite map_filter_union'.
  f_equal.
  apply IHm.
Qed.



(* TODO: Use this to unify the below *)

Definition list_enlarge_Pmap {A B} (f : positive -> A -> list B) (m : Pmap A) :
  Pmap B :=
  map_bind (λ k a,
    list_to_map (imap (λ i v, (encode (k, i), v)) (f k a))
  ) m.

Lemma list_enlarge_Pmap_disjointness {A B} (f : positive -> A -> list B) :
  forall k k' a a',
  k <> k' ->
  (list_to_map (imap (λ i v, (encode (k, i), v)) (f k a)) :> Pmap B) ##ₘ
   list_to_map (imap (λ i v, (encode (k', i), v)) (f k' a')).
Proof.
  intros k k' a a' Hk.
  rewrite map_disjoint_dom, 2 dom_list_to_map.
  rewrite 2 fmap_imap.
  unfold compose.
  cbn.
  rewrite 2 imap_seq_0.
  intros x.
  rewrite 2 elem_of_list_to_set.
  now intros (i & -> & _)%elem_of_list_fmap (j & [= -> ->]%encode_inj & _)%elem_of_list_fmap.
Qed.

Lemma list_enlarge_Pmap_dom_eq {A B} (f : positive -> A -> list B) :
  (forall k a a', length (f k a) = length (f k a')) ->
  forall k a a' k2,
  is_Some ((list_to_map (imap (λ i v, (encode (k, i), v)) (f k a)) :> Pmap B) !! k2)
  ↔ is_Some ((list_to_map (imap (λ i v, (encode (k, i), v)) (f k a')) :> Pmap B) !! k2).
Proof.
  intros Hf.
  intros k a a' k2.
  rewrite <- 2 elem_of_dom.
  rewrite 2 dom_list_to_map.
  rewrite 2 fmap_imap.
  unfold compose.
  cbn.
  rewrite 2 imap_seq_0.
  now erewrite Hf.
Qed.

Lemma lookup_list_enlarge_Pmap_Some {A B} (f : positive -> A -> list B)
  (m : Pmap A) k b :
  list_enlarge_Pmap f m !! k = Some b <->
  exists (i : positive) (j : nat) a, k = encode (i, j) /\
  m !! i = Some a /\ f i a !! j = Some b.
Proof.
  unfold list_enlarge_Pmap.
  rewrite lookup_map_bind_Some by apply list_enlarge_Pmap_disjointness.
  setoid_rewrite <- elem_of_list_to_map. 2:{
    rewrite fmap_imap.
    unfold compose; cbn.
    rewrite imap_seq_0.
    apply (NoDup_fmap _), NoDup_seq.
  }
  setoid_rewrite elem_of_lookup_imap.
  naive_solver.
Qed.

Lemma lookup_list_enlarge_Pmap_not_encode {A B} (f : positive -> A -> list B)
  (m : Pmap A) k : (forall (ij : positive * nat), encode ij <> k) ->
  list_enlarge_Pmap f m !! k = None.
Proof.
  intros Hk.
  rewrite eq_None_not_Some.
  unfold is_Some.
  intros (b & Hb%lookup_list_enlarge_Pmap_Some).
  naive_solver.
Qed.


Lemma lookup_list_enlarge_Pmap_encode {A B} (f : positive -> A -> list B)
  (m : Pmap A) (i : positive) (j : nat) :
  list_enlarge_Pmap f m !! (encode (i, j)) =
  m !! i ≫= λ a, f i a !! j.
Proof.
  apply option_eq; intros b.
  rewrite bind_Some.
  rewrite lookup_list_enlarge_Pmap_Some.
  setoid_rewrite (inj_iff encode).
  naive_solver.
Qed.


Lemma list_enlarge_Pmap_empty {A B} (f : positive -> A -> list B) :
  list_enlarge_Pmap f ∅ = ∅.
Proof.
  apply map_bind_empty.
Qed.

Lemma list_enlarge_Pmap_insert {A B} (f : positive -> A -> list B)
  k a m : m !! k = None ->
  list_enlarge_Pmap f (<[k := a]> m) =
  list_to_map (imap (λ i v, (encode (k, i), v)) (f k a))
  ∪ list_enlarge_Pmap f m.
Proof.
  intros Hmk.
  unfold list_enlarge_Pmap.
  rewrite map_bind_insert; [done| |done].
  apply list_enlarge_Pmap_disjointness.
Qed.


Lemma list_enlarge_Pmap_disj_union {A B} (f : positive -> A -> list B)
  m m' : m ##ₘ m' ->
  list_enlarge_Pmap f (m ∪ m') =
  list_enlarge_Pmap f m ∪ list_enlarge_Pmap f m'.
Proof.
  apply map_bind_disj_union.
  apply list_enlarge_Pmap_disjointness.
Qed.

Lemma list_enlarge_Pmap_disjoint {A B} (f : positive -> A -> list B)
  m m' : m ##ₘ m' ->
  list_enlarge_Pmap f m ##ₘ list_enlarge_Pmap f m'.
Proof.
  intros Hdisj.
  apply map_disjoint_alt.
  intros k.
  destruct (is_encode_dec (positive * nat) k) as [[[i j] <-]|Hk].
  - rewrite 2 lookup_list_enlarge_Pmap_encode.
    rewrite map_disjoint_alt in Hdisj.
    specialize (Hdisj i) as [-> | ->]; auto.
  - left.
    now rewrite lookup_list_enlarge_Pmap_not_encode by done.
Qed.



Definition enlarge_Pmap {A B} (nf : positive -> nat)
  (f : positive -> A -> B) (m : Pmap A) :
  Pmap B :=
  map_bind (λ k a, fun_to_map (λ _, f k a)
  (list_to_set ((λ i, (encode (k, i))) <$> seq 0 (nf k)) :> Pset)) m.

Lemma enlarge_Pmap_disjointness {A B} (nf : positive -> nat)
  (f : positive -> A -> B) : forall k k' a a',
  k <> k' ->
  (fun_to_map (λ _, f k a)
  (list_to_set ((λ i, (encode (k, i))) <$> seq 0 (nf k)) :> Pset) :> Pmap B) ##ₘ
  fun_to_map (λ _, f k' a')
  (list_to_set ((λ i, (encode (k', i))) <$> seq 0 (nf k')) :> Pset).
Proof.
  intros k k' a a' Hk.
  rewrite map_disjoint_dom, 2 dom_fun_to_map.
  intros x.
  rewrite 2 elem_of_list_to_set.
  now intros (i & -> & _)%elem_of_list_fmap (j & [= -> ->]%encode_inj & _)%elem_of_list_fmap.
Qed.

Lemma enlarge_Pmap_dom_eq {A B} (nf : positive -> nat) (f : positive -> A -> B) :
  forall k a a' k2,
  is_Some ((fun_to_map (λ _, f k a) (list_to_set
    ((λ i, encode (k, i)) <$> seq 0 (nf k)) :> Pset) :> Pmap B) !! k2)
  ↔ is_Some ((fun_to_map (λ _, f k a') (list_to_set
    ((λ i, encode (k, i)) <$> seq 0 (nf k)) :> Pset) :> Pmap B) !! k2).
Proof.
  intros k a a' k2.
  rewrite <- 2 elem_of_dom.
  now rewrite 2 dom_fun_to_map.
Qed.

Lemma lookup_enlarge_Pmap_Some {A B} nf (f : positive -> A -> B)
  (m : Pmap A) k b :
  enlarge_Pmap nf f m !! k = Some b <->
  exists (i : positive) (j : nat) a, k = encode (i, j) /\
  m !! i = Some a /\ j < nf i /\ b = f i a.
Proof.
  unfold enlarge_Pmap.
  rewrite lookup_map_bind_Some by apply enlarge_Pmap_disjointness.
  setoid_rewrite lookup_fun_to_map_Some.
  set_unfold.
  setoid_rewrite elem_of_seq.
  naive_solver lia.
Qed.

Lemma lookup_enlarge_Pmap_not_encode {A B} nf (f : positive -> A -> B)
  (m : Pmap A) k : (forall (ij : positive * nat), encode ij <> k) ->
  enlarge_Pmap nf f m !! k = None.
Proof.
  intros Hk.
  rewrite eq_None_not_Some.
  unfold is_Some.
  intros (b & Hb%lookup_enlarge_Pmap_Some).
  naive_solver.
Qed.

Lemma lookup_enlarge_Pmap_encode_ge {A B} nf (f : positive -> A -> B)
  (m : Pmap A) (i : positive) (j : nat) : nf i <= j ->
  enlarge_Pmap nf f m !! (encode (i, j)) = None.
Proof.
  intros Hnf.
  rewrite eq_None_not_Some.
  unfold is_Some.
  intros (b & Hb%lookup_enlarge_Pmap_Some).
  setoid_rewrite (inj_iff encode) in Hb.
  naive_solver lia.
Qed.

Lemma lookup_enlarge_Pmap_encode_lt {A B} nf (f : positive -> A -> B)
  (m : Pmap A) (i : positive) (j : nat) : j < nf i ->
  enlarge_Pmap nf f m !! (encode (i, j)) =
  f i <$> m !! i.
Proof.
  intros Hj.
  apply option_eq; intros b.
  rewrite fmap_Some.
  rewrite lookup_enlarge_Pmap_Some.
  setoid_rewrite (inj_iff encode).
  naive_solver.
Qed.

Lemma lookup_enlarge_Pmap_encode {A B} nf (f : positive -> A -> B)
  (m : Pmap A) (i : positive) (j : nat) :
  enlarge_Pmap nf f m !! (encode (i, j)) =
  (guard (j < nf i) ;; f i <$> m !! i).
Proof.
  case_guard.
  - now apply lookup_enlarge_Pmap_encode_lt.
  - now apply lookup_enlarge_Pmap_encode_ge; lia.
Qed.

Lemma enlarge_Pmap_empty {A B} nf (f : positive -> A -> B) :
  enlarge_Pmap nf f ∅ = ∅.
Proof.
  apply map_bind_empty.
Qed.

Lemma enlarge_Pmap_insert {A B} nf (f : positive -> A -> B)
  k a m :
  enlarge_Pmap nf f (<[k := a]> m) =
  fun_to_map (λ _, f k a)
  (list_to_set ((λ i, (encode (k, i))) <$> seq 0 (nf k)) :> Pset)
  ∪ enlarge_Pmap nf f m.
Proof.
  unfold enlarge_Pmap.
  rewrite map_bind_insert_dom_eq; [done|..].
  - apply enlarge_Pmap_disjointness.
  - apply enlarge_Pmap_dom_eq.
Qed.


Lemma enlarge_Pmap_union {A B} nf (f : positive -> A -> B)
  m m' :
  enlarge_Pmap nf f (m ∪ m') =
  enlarge_Pmap nf f m ∪ enlarge_Pmap nf f m'.
Proof.
  apply map_bind_union_dom_eq.
  - apply enlarge_Pmap_disjointness.
  - apply enlarge_Pmap_dom_eq.
Qed.

Lemma enlarge_Pmap_disjoint {A B} nf (f : positive -> A -> B)
  m m' : m ##ₘ m' ->
  enlarge_Pmap nf f m ##ₘ enlarge_Pmap nf f m'.
Proof.
  intros Hdisj.
  apply map_disjoint_alt.
  intros k.
  destruct (is_encode_dec (positive * nat) k) as [[[i j] <-]|Hk].
  - rewrite 2 lookup_enlarge_Pmap_encode.
    rewrite map_disjoint_alt in Hdisj.
    specialize (Hdisj i) as [-> | ->]; cbn; rewrite option_bind_None_r; auto.
  - left.
    now rewrite lookup_enlarge_Pmap_not_encode by done.
Qed.


Definition venlarge_Pmap {A B} {nf : positive -> nat}
  (f : forall p, A -> vec B (nf p)) (m : Pmap A) :
  Pmap B :=
  map_bind (λ k a,
    list_to_map (imap (λ i v, (encode (k, i), v)) (f k a))
  ) m.

Lemma venlarge_Pmap_disjointness {A B} {nf : positive -> nat}
  (f : forall p, A -> vec B (nf p)) : forall k k' a a',
  k <> k' ->
  (list_to_map (imap (λ i v, (encode (k, i), v)) (f k a)) :> Pmap B) ##ₘ
   list_to_map (imap (λ i v, (encode (k', i), v)) (f k' a')).
Proof.
  intros k k' a a' Hk.
  rewrite map_disjoint_dom, 2 dom_list_to_map.
  rewrite 2 fmap_imap.
  unfold compose.
  cbn.
  rewrite 2 imap_seq_0.
  intros x.
  rewrite 2 elem_of_list_to_set.
  now intros (i & -> & _)%elem_of_list_fmap (j & [= -> ->]%encode_inj & _)%elem_of_list_fmap.
Qed.

Lemma venlarge_Pmap_dom_eq {A B} {nf : positive -> nat}
  (f : forall p, A -> vec B (nf p)) :
  forall k a a' k2,
  is_Some ((list_to_map (imap (λ i v, (encode (k, i), v)) (f k a)) :> Pmap B) !! k2)
  ↔ is_Some ((list_to_map (imap (λ i v, (encode (k, i), v)) (f k a')) :> Pmap B) !! k2).
Proof.
  intros k a a' k2.
  rewrite <- 2 elem_of_dom.
  rewrite 2 dom_list_to_map.
  rewrite 2 fmap_imap.
  unfold compose.
  cbn.
  now rewrite 2 imap_seq_0, 2 length_vec_to_list.
Qed.

Lemma lookup_venlarge_Pmap_Some {A B} {nf} (f : forall p, A -> vec B (nf p))
  (m : Pmap A) k b :
  venlarge_Pmap f m !! k = Some b <->
  exists (i : positive) (j : nat) a, k = encode (i, j) /\
  m !! i = Some a /\ j < nf i /\ (f i a : list B) !! j = Some b.
Proof.
  unfold venlarge_Pmap.
  rewrite lookup_map_bind_Some by apply venlarge_Pmap_disjointness.
  setoid_rewrite <- elem_of_list_to_map. 2:{
    rewrite fmap_imap.
    unfold compose; cbn.
    rewrite imap_seq_0.
    apply (NoDup_fmap _), NoDup_seq.
  }
  setoid_rewrite elem_of_lookup_imap.
  split; [|naive_solver].
  intros (? & ? & ? & (? & ? & ? & Hlook)).
  apply lookup_lt_Some in Hlook as Hlt.
  rewrite length_vec_to_list in Hlt.
  naive_solver.
Qed.

Lemma lookup_venlarge_Pmap_not_encode {A B} {nf} (f : forall p, A -> vec B (nf p))
  (m : Pmap A) k : (forall (ij : positive * nat), encode ij <> k) ->
  venlarge_Pmap f m !! k = None.
Proof.
  intros Hk.
  rewrite eq_None_not_Some.
  unfold is_Some.
  intros (b & Hb%lookup_venlarge_Pmap_Some).
  naive_solver.
Qed.

Lemma lookup_venlarge_Pmap_encode_ge {A B} {nf} (f : forall p, A -> vec B (nf p))
  (m : Pmap A) (i : positive) (j : nat) : nf i <= j ->
  venlarge_Pmap f m !! (encode (i, j)) = None.
Proof.
  intros Hnf.
  rewrite eq_None_not_Some.
  unfold is_Some.
  intros (b & Hb%lookup_venlarge_Pmap_Some).
  setoid_rewrite (inj_iff encode) in Hb.
  naive_solver lia.
Qed.

Lemma lookup_venlarge_Pmap_encode {A B} {nf} (f : forall p, A -> vec B (nf p))
  (m : Pmap A) (i : positive) (j : nat) :
  venlarge_Pmap f m !! (encode (i, j)) =
  m !! i ≫= λ a, (f i a :> list _) !! j.
Proof.
  apply option_eq; intros b.
  rewrite bind_Some.
  rewrite lookup_venlarge_Pmap_Some.
  setoid_rewrite (inj_iff encode).
  split; [naive_solver|].
  intros (a & Hia & Hj).
  apply lookup_lt_Some in Hj as Hlt.
  rewrite length_vec_to_list in Hlt.
  naive_solver.
Qed.


Lemma lookup_venlarge_Pmap_encode_fin {A B} {nf} (f : forall p, A -> vec B (nf p))
  (m : Pmap A) (i : positive) (j : fin (nf i)) :
  venlarge_Pmap f m !! (encode (i, j :> nat)) =
  m !! i ≫= λ a, Some (f i a !!! j).
Proof.
  rewrite lookup_venlarge_Pmap_encode.
  apply option_bind_ext, reflexivity.
  intros x.
  apply lookup_vec_to_list_fin.
Qed.

Lemma venlarge_Pmap_empty {A B} {nf} (f : forall p, A -> vec B (nf p)) :
  venlarge_Pmap f ∅ = ∅.
Proof.
  apply map_bind_empty.
Qed.

Lemma venlarge_Pmap_insert {A B} {nf} (f : forall p, A -> vec B (nf p))
  k a m :
  venlarge_Pmap f (<[k := a]> m) =
  list_to_map (imap (λ i v, (encode (k, i), v)) (f k a))
  ∪ venlarge_Pmap f m.
Proof.
  unfold venlarge_Pmap.
  rewrite map_bind_insert_dom_eq; [done|..].
  - apply venlarge_Pmap_disjointness.
  - apply venlarge_Pmap_dom_eq.
Qed.


Lemma venlarge_Pmap_union {A B} {nf} (f : forall p, A -> vec B (nf p))
  m m' :
  venlarge_Pmap f (m ∪ m') =
  venlarge_Pmap f m ∪ venlarge_Pmap f m'.
Proof.
  apply map_bind_union_dom_eq.
  - apply venlarge_Pmap_disjointness.
  - apply venlarge_Pmap_dom_eq.
Qed.

Lemma venlarge_Pmap_disjoint {A B} {nf} (f : forall p, A -> vec B (nf p))
  m m' : m ##ₘ m' ->
  venlarge_Pmap f m ##ₘ venlarge_Pmap f m'.
Proof.
  intros Hdisj.
  apply map_disjoint_alt.
  intros k.
  destruct (is_encode_dec (positive * nat) k) as [[[i j] <-]|Hk].
  - rewrite 2 lookup_venlarge_Pmap_encode.
    rewrite map_disjoint_alt in Hdisj.
    specialize (Hdisj i) as [-> | ->]; auto.
  - left.
    now rewrite lookup_venlarge_Pmap_not_encode by done.
Qed.







Definition map_sized_graph {N M} {T n m} (f : N -> M) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T n m :=
  mk_scohg scohg (f <$> scohg.(sized_map)).

(* FIXME: Move *)
Definition enlarge_hypergraph {T} (f : positive -> list positive)
  (hg : HyperGraph T) : HyperGraph T :=
  mk_hg ((λ tio, (tio.1.1, tio.1.2 ≫= f, tio.2 ≫= f)) <$> hg.(hyperedges))
    (set_bind (list_to_set ∘ f) hg.(hypervertices)).

Definition enlarge_graph {T n m} (f : positive -> list positive)
  (cohg : CospanHyperGraph T n m) : CospanHyperGraph T _ _ :=
  list_to_vec ((cohg.(inputs) :> list _) ≫= f) ->
    enlarge_hypergraph f cohg
    <- list_to_vec ((cohg.(outputs) :> list _) ≫= f).


Definition venlarge_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) : CospanHyperGraph T _ _ :=
  vbind f cohg.(inputs) ->
    enlarge_hypergraph (λ p, vec_to_list (f p)) cohg
    <- vbind f cohg.(outputs).


Definition bind_sized_graph {N} {T n m} (scohg : SizedCospanHyperGraph (list N) T n m) :
  SizedCospanHyperGraph N T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : N), encode (k, i)) (scohg.(sized_map) !!! k))
    scohg)
    (venlarge_Pmap (λ k _, list_to_vec (default [] (scohg.(sized_map) !! k)))
      scohg.(sized_map)).


Definition map_list_sized_graph {N M} {T n m} (f : N -> list M)
  (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T _ _ :=
  mk_scohg (enlarge_graph (λ k, imap (λ i (v : M), encode (k, i)) ((f <$> scohg.(sized_map)) !!! k)) scohg)
    (venlarge_Pmap (λ k _, list_to_vec (default [] (f <$> scohg.(sized_map) !! k)))
      (scohg.(sized_map))).

Definition map_vec_sized_graph {N M} {T n m} {nf : N -> nat}
  (f : forall k, vec M (nf k)) (scohg : SizedCospanHyperGraph N T n m) :
  SizedCospanHyperGraph M T _ _ :=
  mk_scohg (venlarge_graph
      (nf := λ p, default 0 (nf <$> (scohg.(sized_map) !! p)))
      (λ p, (fun_to_vec (λ i, encode (p, i:>nat)))) scohg)
    (list_enlarge_Pmap (λ k a, f a) scohg.(sized_map)).






(* Only valid if vertices scohg ⊆ dom scohg.(sized_map) *)
Definition unit_sized_graph_to_graph {T n m}
  (scohg : SizedCospanHyperGraph unit T n m) : CospanHyperGraph T n m := scohg.

Definition nat_sized_graph_to_unit_graph {T n m}
  (scohg : SizedCospanHyperGraph nat T n m) :
  SizedCospanHyperGraph unit T _ _ :=
  map_vec_sized_graph (nf := id)
    (fun k => fun_to_vec (λ _, ())) scohg.

(* Definition sized_graph_to_nat_sized_graph {N T n m} (f : N -> nat)
  (scohg : SizedCospanHyperGraph N T n m) : SizedCospanHyperGraph nat T _ _ :=
  map_
  {T n m} *)

Definition sized_graph_to_graph {N T n m} (f : N -> nat)
  (scohg : SizedCospanHyperGraph N T n m) : CospanHyperGraph T _ _ :=
  map_vec_sized_graph (nf := f)
    (fun k => fun_to_vec (λ _, ())) scohg.


(* Definition graph_to_bundled_graph {T n m} (cohg : CospanHyperGraph T n m) :
  {n & {m & CospanHyperGraph T n m}} :=
  existT n (existT m cohg). *)

(* Definition graph_to_untyped_graph {T n m} (cohg : CospanHyperGraph T n m) :
  HyperGraph T * list positive * list positive :=
  (hedges cohg, vec_to_list $ inputs cohg, vec_to_list $ outputs cohg). *)

(* Coercion graph_to_bundled_graph : CospanHyperGraph >-> sigT. *)











(* Definition sized_graph_to_bundled_sized_graph
  {N T n m} (cohg : SizedCospanHyperGraph N T n m) :
  {n & {m & SizedCospanHyperGraph N T n m}} :=
  existT n (existT m cohg).

(* Coercion sized_graph_to_bundled_sized_graph : SizedCospanHyperGraph >-> sigT. *)

Lemma bundled_sized_graph_eq_iff {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') :
  sized_graph_to_bundled_sized_graph cohg =ₛ
  sized_graph_to_bundled_sized_graph cohg' <-> exists Hn Hm, cohg = eq_rect_r (λ k, SizedCospanHyperGraph N T n k)
    (eq_rect_r (λ k, SizedCospanHyperGraph N T k m') cohg' Hn) Hm.
Proof.
  split.
  - intros Heq.
    unfold sized_graph_to_bundled_sized_graph in Heq.
    inversion_sigma Heq.
    subst n'.
    cbn in Heq2.
    inversion_sigma Heq2.
    subst m'.
    cbn in *.
    subst.
    exists eq_refl, eq_refl.
    done.
  - intros (<- & <- & ->).
    done.
Qed. *)


Lemma enlarge_hypergraph_relabel_hg {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  enlarge_hypergraph f (relabel_hg g hg) = enlarge_hypergraph (f ∘ g) hg.
Proof.
  apply hg_ext; cbn.
  - rewrite <- map_fmap_compose.
    apply map_fmap_ext.
    intros k [[t i] o] _.
    cbn.
    rewrite 2 list_fmap_bind.
    done.
  - set_solver.
Qed.

Lemma relabel_hg_enlarge_hypergraph {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  relabel_hg g (enlarge_hypergraph f hg) = enlarge_hypergraph (fmap g ∘ f) hg.
Proof.
  apply hg_ext; cbn.
  - rewrite <- map_fmap_compose.
    apply map_fmap_ext.
    intros k [[t i] o] _.
    cbn.
    rewrite 2 list_bind_fmap.
    done.
  - set_solver.
Qed.


(* FIXME: Move *)
Lemma vec_to_list_fun_to_vec {A} {n} (f : nat -> A) :
  vec_to_list (fun_to_vec (λ i, f (fin_to_nat i)) :> vec A n) =
  f <$> seq 0 n.
Proof.
  apply (list_eq_same_length _ _ _ eq_refl);
  [now rewrite length_fmap, length_seq, length_vec_to_list|].
  intros i x y Hi.
  rewrite length_fmap, length_seq in Hi.
  rewrite lookup_vec_to_list.
  case_guard as Hi'; [|done].
  cbn.
  rewrite lookup_fun_to_vec.
  rewrite fin_to_nat_to_fin.
  rewrite list_lookup_fmap, lookup_seq_lt by lia.
  cbn.
  congruence.
Qed.

Lemma vmap_fun_to_vec {A B} {n} (f : fin n -> A) (g : A -> B) :
  vmap g (fun_to_vec f) = fun_to_vec (g ∘ f).
Proof.
  apply vec_eq.
  intros p.
  rewrite vlookup_map.
  now rewrite 2 lookup_fun_to_vec.
Qed.

Lemma enlarge_hypergraph_ext {T} f g (hg : HyperGraph T) :
  (forall i, f i = g i) ->
  enlarge_hypergraph f hg = enlarge_hypergraph g hg.
Proof.
  intros Hfg.
  apply hg_ext.
  - cbn.
    apply map_fmap_ext.
    intros _ tio _.
    f_equal; [f_equal|]; apply list_bind_ext, reflexivity; intros; apply Hfg.
  - cbn.
    set_unfold.
    setoid_rewrite Hfg.
    done.
Qed.

Lemma enlarge_hypergraph_id {T} (hg : HyperGraph T) :
  enlarge_hypergraph (λ k, [k]) hg = hg.
Proof.
  apply hg_ext.
  - cbn.
    etransitivity; [|apply map_fmap_id].
    apply map_fmap_ext.
    intros _ [[t i] o] _.
    cbn.
    now f_equal; [f_equal|]; rewrite list_bind_singleton_r, list_fmap_id.
  - cbn.
    set_solver.
Qed.


Inductive sigT2_relation {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) : relation {ab : A * B & P ab.1 ab.2} :=
  | mk_sigT2_relation {a b} (x y : P a b) : R a b x y ->
    sigT2_relation R (existT (a, b) x) (existT (a, b) y).

Lemma sigT2_relation_alt {A B}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) x y :
  sigT2_relation R x y <-> exists Hab, R _ _ (projT2 x) (eq_rect_r _ (projT2 y) Hab).
Proof.
  split.
  - intros HR.
    induction HR.
    cbn.
    now exists eq_refl.
  - destruct x as [[a b] x], y as [[a' b'] y].
    intros (Hab & HR).
    cbn in Hab.
    revert y HR.
    revert Hab.
    generalize (a', b').
    intros p <-.
    cbn.
    now constructor.
Qed.

Lemma mk_sigT2_relation_alt {A B}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b))
  {a b a' b'} (x : P a b) (y : P a' b') :
  (exists Ha Hb, R _ _ x
    (eq_rect_r (x:=(a',b')) (λ ab, P ab.1 ab.2) y
    (eq_trans (f_equal (a,.) Hb) (f_equal (.,b') Ha) : (a, b) = (a', b')))) ->
  sigT2_relation R (existT (a, b) x) (existT (a', b') y).
Proof.
  intros (-> & -> & Hrel).
  now constructor.
Qed.


#[export] Instance sigT2_relation_refl {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Reflexive (R a b)} :
  Reflexive (sigT2_relation R).
Proof.
  intros [[a b] x].
  constructor.
  reflexivity.
Qed.

#[export] Instance sigT2_relation_symm {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Symmetric (R a b)} :
  Symmetric (sigT2_relation R).
Proof.
  intros x y Hxy.
  induction Hxy.
  constructor.
  now symmetry.
Qed.

#[export] Instance sigT2_relation_trans {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Transitive (R a b)} :
  Transitive (sigT2_relation R).
Proof.
  intros x y z Hxy Hyz.
  rewrite sigT2_relation_alt in *.
  destruct Hxy as (Hab & Hxy), Hyz as (Hbc & Hyz).
  exists (eq_trans Hab Hbc).
  destruct x, y, z; cbn in *.
  subst.
  cbn in *.
  now etransitivity; eauto.
Qed.

#[export] Instance sigT2_relation_equivalence {A B} {P : A -> B -> Type}
  (R : forall a b, relation (P a b)) `{HR : forall a b, Equivalence (R a b)} :
  Equivalence (sigT2_relation R).
Proof.
  split; apply _.
Qed.

#[export] Instance sigT2_relation_subrelation {A B} {P : A -> B -> Type}
  (R R' : forall a b, relation (P a b)) `{HR : forall a b, subrelation (R a b) (R' a b)} :
  subrelation (sigT2_relation R) (sigT2_relation R').
Proof.
  intros x y Hxy.
  induction Hxy.
  constructor.
  now apply subrel.
Qed.


















Definition graph_to_pair_bundled {T n m}
  (scohg : CospanHyperGraph T n m) : {nm : nat * nat & CospanHyperGraph T nm.1 nm.2} :=
  existT (n, m) scohg.


Notation "g =ₛ g'" := (graph_to_pair_bundled g%cohg = graph_to_pair_bundled g'%cohg)
  (at level 70) : cohg_scope.

Notation "sg '[≡ₕ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_eq _ n m _)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ᵥ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_vert_eq _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ᵢ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @struct_isomorphic _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Notation "sg '[≡ₛ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @cohg_syntactic_eq _ _ n m)
    (graph_to_pair_bundled sg%cohg)
    (graph_to_pair_bundled sg'%cohg)) (at level 70) : cohg_scope.

Lemma mk_cohg_bundled_eq {T n m n' m'}
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  inputs cohg =@{list _} inputs cohg' ->
  outputs cohg =@{list _} outputs cohg' ->
  hedges cohg = hedges cohg' ->
  cohg =ₛ cohg'.
Proof.
  intros Hins Houts Hhedges.
  apply vec_to_list_inj1 in Hins as Hn.
  apply vec_to_list_inj1 in Houts as Hm.
  subst.
  apply vec_to_list_inj2 in Hins.
  apply vec_to_list_inj2 in Houts.
  auto using cohg_ext with f_equal.
Qed.





Lemma bundled_cohg_eq_iff `{Equiv T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  scohg [≡ₕ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hedges scohg ≡ hedges scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    split_and!; apply Hequiv || f_equal; apply Hequiv.
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    split; [|done].
    now apply mk_cohg_eq.
Qed.

Lemma mk_bundled_cohg_eq `{Equiv T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hedges scohg ≡ hedges scohg' ->
  scohg [≡ₕ]ₛ scohg'.
Proof.
  intros; apply bundled_cohg_eq_iff; easy.
Qed.

Lemma bundled_cohg_vert_eq_iff {T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  scohg [≡ᵥ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    apply cohg_vert_eq_alt_vertices in Hequiv.
    split_and!; first [apply Hequiv|f_equal; apply Hequiv].
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    now apply cohg_vert_eq_alt_vertices.
Qed.

Lemma mk_bundled_cohg_vert_eq {T} {n m n' m'}
  (scohg : CospanHyperGraph T n m)
  (scohg' : CospanHyperGraph T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hyperedges scohg = hyperedges scohg' ->
  vertices scohg = vertices scohg' ->
  scohg [≡ᵥ]ₛ scohg'.
Proof.
  intros; apply bundled_cohg_vert_eq_iff; easy.
Qed.


Lemma graph_to_pair_bundled_apply {T T'}
  (f : forall n m, CospanHyperGraph T n m -> CospanHyperGraph T' n m)
  {n m}
  (scohg : CospanHyperGraph T n m) :
  f n m scohg =ₛ
  (λ scohg', f _ _ (projT2 scohg'))
  (graph_to_pair_bundled scohg).
Proof.
  done.
Qed.






Lemma venlarge_graph_relabel_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  (cohg : CospanHyperGraph T n m) :
  venlarge_graph f (relabel_graph g cohg) =ₛ
  venlarge_graph (λ k, f (g k)) cohg.
Proof.
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite vec_to_list_map.
    now rewrite list_fmap_bind.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite vec_to_list_map.
    now rewrite list_fmap_bind.
  - cbn.
    apply enlarge_hypergraph_relabel_hg.
Qed.


Definition sized_graph_to_pair_bundled {N T n m}
  (scohg : SizedCospanHyperGraph N T n m) : {nm : nat * nat & SizedCospanHyperGraph N T nm.1 nm.2} :=
  existT (n, m) scohg.


Notation "g =ₛ g'" := (sized_graph_to_pair_bundled g = sized_graph_to_pair_bundled g')
  (at level 70) : scohg_scope.

Notation "sg '[≡ₕ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_eq _ _ n m _)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ᵥ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_vert_eq _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ᵢ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @struct_sized_isomorphic _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Notation "sg '[≡ₛ]ₛ'  sg'" :=
  (sigT2_relation (fun n m => @scohg_syntactic_eq _ _ _ n m)
    (sized_graph_to_pair_bundled sg)
    (sized_graph_to_pair_bundled sg')) (at level 70) : scohg_scope.

Lemma bundled_sized_rel_alt {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m')
  (R : forall n m, relation (SizedCospanHyperGraph N T n m)) :
  sigT2_relation R (sized_graph_to_pair_bundled scohg)
    (sized_graph_to_pair_bundled scohg') <->
  exists Hn Hm, R n m scohg (mk_scohg (mk_cohg scohg'
    (Vector.cast scohg'.(inputs) Hn)
    (Vector.cast scohg'.(outputs) Hm)) (scohg'.(sized_map))).
Proof.
  split.
  - intros (Heq & Hcast)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    exists eq_refl, eq_refl.
    rewrite 2 cast_id.
    now destruct scohg' as [[]].
  - intros (-> & -> & HR).
    apply mk_sigT2_relation_alt.
    exists eq_refl, eq_refl.
    cbn.
    rewrite 2 cast_id in HR.
    now destruct scohg' as [[]].
Qed.

Lemma mk_scohg_bundled_eq {N T n m n' m'} (cohg : SizedCospanHyperGraph N T n m)
  (cohg' : SizedCospanHyperGraph N T n' m') :
  vec_to_list (inputs cohg) = vec_to_list (inputs cohg') ->
  vec_to_list (outputs cohg) = vec_to_list (outputs cohg') ->
  hedges cohg = hedges cohg' ->
  sized_map cohg = sized_map cohg' ->
  cohg =ₛ cohg'.
Proof.
  intros Hi Ho Hh Hmap.
  apply vec_to_list_inj1 in Hi as Hn.
  subst n'.
  apply vec_to_list_inj1 in Ho as Hm.
  subst m'.
  f_equal.
  apply vec_to_list_inj2 in Hi, Ho.
  auto using scohg_ext, cohg_ext.
Qed.


Lemma bundled_scohg_eq_iff {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  scohg [≡ₕ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  sized_map scohg = sized_map scohg' /\
  hedges scohg ≡ hedges scohg'.
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    split_and!; apply Hequiv || f_equal; apply Hequiv.
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    split; [|done].
    now apply mk_cohg_eq.
Qed.

Lemma mk_bundled_scohg_eq {N} `{Equiv T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  sized_map scohg = sized_map scohg' ->
  hedges scohg ≡ hedges scohg' ->
  scohg [≡ₕ]ₛ scohg'.
Proof.
  intros; apply bundled_scohg_eq_iff; easy.
Qed.

Lemma scohg_vert_eq_iff {N} {T} {n m}
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' <->
  inputs scohg = inputs scohg' /\
  outputs scohg = outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg' /\
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg').
Proof.
  split.
  - intros Heq.
    pose proof Heq as Heq'.
    unfold scohg_vert_eq in Heq'.
    rewrite cohg_vert_eq_alt_vertices in Heq'.
    split_and!; [apply Heq'.1..|].
    rewrite <- Heq'.1.2.2.2.
    apply map_eq; intros k.
    rewrite 2 map_lookup_filter.
    cbn.
    case_guard; [|cbn; now rewrite 2 option_bind_None_r].
    cbn.
    now rewrite <- Heq'.2 by done.
  - intros (Hins & Houts & Hh & Hverts & Hm).
    split; [now apply cohg_vert_eq_alt_vertices|].
    intros v Hv.
    rewrite <- Hverts in Hm.
    apply (f_equal (.!!v)) in Hm.
    rewrite 2 map_lookup_filter in Hm.
    revert Hm.
    cbn.
    case_guard; [|done].
    cbn.
    destruct (_ !! _), (_ !! _); cbn; congruence.
Qed.

Lemma bundled_scohg_vert_eq_iff {N} {T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  scohg [≡ᵥ]ₛ scohg' <->
  inputs scohg =@{list _} inputs scohg' /\
  outputs scohg =@{list _} outputs scohg' /\
  hyperedges scohg = hyperedges scohg' /\
  vertices scohg = vertices scohg' /\
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg').
Proof.
  split.
  - intros (Heq & Hequiv)%sigT2_relation_alt.
    cbn in Heq.
    assert (n' = n) as -> by congruence.
    assert (m' = m) as -> by congruence.
    replace Heq with (@eq_refl _ (n, m)) in * by apply proof_irrel.
    cbn in *.
    apply scohg_vert_eq_iff in Hequiv.
    split_and!; first [apply Hequiv|f_equal; apply Hequiv].
  - intros (Hins & Houts & Hmap & Hequiv).
    apply vec_to_list_inj1 in Hins as Hn.
    apply vec_to_list_inj1 in Houts as Hm.
    subst n' m'.
    apply vec_to_list_inj2 in Hins.
    apply vec_to_list_inj2 in Houts.
    apply mk_sigT2_relation.
    now apply scohg_vert_eq_iff.
Qed.

Lemma mk_bundled_scohg_vert_eq {N} {T} {n m n' m'}
  (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  inputs scohg =@{list _} inputs scohg' ->
  outputs scohg =@{list _} outputs scohg' ->
  hyperedges scohg = hyperedges scohg' ->
  vertices scohg = vertices scohg' ->
  filter (λ ka, ka.1 ∈ vertices scohg) (sized_map scohg) =
  filter (λ ka, ka.1 ∈ vertices scohg') (sized_map scohg') ->
  scohg [≡ᵥ]ₛ scohg'.
Proof.
  intros; apply bundled_scohg_vert_eq_iff; easy.
Qed.


Lemma map_vec_sized_graph_relabel_sized_graph {N M T n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (g : positive -> positive) `{Hg : !Inj eq eq g}
  (scohg : SizedCospanHyperGraph N T n m) :
  map_vec_sized_graph f (relabel_sized_graph g scohg) =ₛ
  relabel_sized_graph
    (encode_map (prod_map g (@id nat)))
    (map_vec_sized_graph f scohg).
Proof.
  apply mk_scohg_bundled_eq.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_map, vec_to_list_bind.
    rewrite list_bind_fmap, list_fmap_bind.
    apply list_bind_ext; [|done].
    intros k.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_map, vec_to_list_bind.
    rewrite list_bind_fmap, list_fmap_bind.
    apply list_bind_ext; [|done].
    intros k.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    rewrite enlarge_hypergraph_relabel_hg.
    rewrite relabel_hg_enlarge_hypergraph.
    apply enlarge_hypergraph_ext.
    intros i.
    cbn.
    cbn.
    rewrite (lookup_kmap _).
    rewrite <- vec_to_list_map.
    rewrite vmap_fun_to_vec.
    f_equal.
    apply vec_eq; intros p.
    rewrite 2 lookup_fun_to_vec.
    cbn.
    now rewrite encode_map_encode.
  - cbn.
    unfold list_enlarge_Pmap.
    rewrite (map_kmap_bind _) by apply list_enlarge_Pmap_disjointness.
    rewrite (map_bind_kmap _ _) by apply list_enlarge_Pmap_disjointness.
    apply map_bind_ext.
    intros k a _.
    rewrite (kmap_list_to_map _).
    f_equal.
    rewrite fmap_imap.
    unfold compose.
    apply imap_ext.
    intros i x _.
    cbn.
    now rewrite encode_map_encode.
Qed.

Lemma enlarge_hypergraph_reindex_hg {T} (f : positive -> list positive) g
  (hg : HyperGraph T) :
  enlarge_hypergraph f (reindex_hg g hg) = reindex_hg g (enlarge_hypergraph f hg).
Proof.
  apply hg_ext; cbn.
  - now rewrite kmap_fmap'.
  - done.
Qed.

Lemma map_vec_sized_graph_reindex_sized_graph {N M T n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (g : positive -> positive) `{Hg : !Inj eq eq g}
  (scohg : SizedCospanHyperGraph N T n m) :
  map_vec_sized_graph f (reindex_sized_graph g scohg) =ₛ
  reindex_sized_graph g
    (map_vec_sized_graph f scohg).
Proof.
  apply mk_scohg_bundled_eq; [done..| |done].
  cbn.
  apply enlarge_hypergraph_reindex_hg.
Qed.



#[export] Instance enlarge_hypergraph_proper `{Equiv T} f :
  Proper ((≡@{HyperGraph T}) ==> equiv) (enlarge_hypergraph f).
Proof.
  intros hg hg'.
  intros [He Hv].
  split.
  - cbn.
    apply map_fmap_proper, He.
    intros tio tio' Htio.
    split; [split|]; cbn; [|f_equal..]; apply Htio.
  - cbn.
    now f_equal.
Qed.

Lemma map_vec_sized_graph_scohg_eq {N M} `{Equiv T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₕ scohg' ->
  map_vec_sized_graph f scohg [≡ₕ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros Heq.
  apply mk_bundled_scohg_eq.
  - cbn.
    rewrite Heq.1.1, Heq.2.
    done.
  - cbn.
    rewrite Heq.1.2.1, Heq.2.
    done.
  - cbn.
    rewrite Heq.2.
    done.
  - cbn.
    rewrite Heq.2.
    apply enlarge_hypergraph_proper, Heq.1.2.2.
Qed.

Lemma set_bind_union `{FinSet A SA, SemiSet B SB} (f : A -> SB) (X Y : SA) :
  set_bind f (X ∪ Y) ≡ set_bind f X ∪ set_bind f Y.
Proof.
  set_solver.
Qed.

Lemma set_bind_union_L `{FinSet A SA, SemiSet B SB, !LeibnizEquiv SB} (f : A -> SB) (X Y : SA) :
  set_bind f (X ∪ Y) = set_bind f X ∪ set_bind f Y.
Proof.
  set_solver.
Qed.

Lemma vertices_hg_enlarge_hypergraph {T}
  (f : positive -> list positive) (hg : HyperGraph T) :
  vertices_hg (enlarge_hypergraph f hg) =
  set_bind (list_to_set ∘ f) (vertices_hg hg).
Proof.
  rewrite 2 vertices_hg_decomp.
  rewrite set_bind_union_L.
  f_equal.
  cbn.
  apply set_eq; intros p.
  set_unfold.
  split.
  - intros (ktio & Hp & Hktio).
    rewrite map_to_list_fmap in Hktio.
    apply elem_of_list_fmap in Hktio as ([k tio] & -> & Hktio).
    cbn in *.
    rewrite <- elem_of_app, <- bind_app in Hp.
    apply elem_of_list_bind in Hp as (x & Hp & Hx).
    set_solver.
  - intros (x & ([k tio] & Hx & Hktio) & Hp).
    rewrite <- elem_of_app in Hx.
    exists (k, (tio.1.1, (tio.1.2 ≫= f), (tio.2 ≫= f))).
    rewrite map_to_list_fmap.
    split; [set_solver + Hx Hp|].
    refine (elem_of_list_fmap_1 (prod_map id
    (λ tio, (tio.1.1, (tio.1.2 ≫= f), (tio.2 ≫= f)))) _ (k, ((tio.1.1, tio.1.2), tio.2)) _).
    now destruct tio as [ [] ].
Qed.


Lemma vertices_venlarge_graph {T n m nf}
  (f : forall p, vec positive (nf p)) (cohg : CospanHyperGraph T n m) :
  vertices (venlarge_graph f cohg) =
  set_bind (list_to_set ∘ f) (vertices cohg).
Proof.
  unfold vertices.
  cbn.
  rewrite set_bind_union_L.
  rewrite vertices_hg_enlarge_hypergraph.
  rewrite 2 vec_to_list_bind.
  f_equal.
  rewrite 2 list_to_set_app_L, set_bind_union_L; f_equal;
  set_solver +.
Qed.

Lemma map_vec_sized_graph_scohg_vert_eq {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵥ scohg' ->
  map_vec_sized_graph f scohg [≡ᵥ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros Heq'.
  pose proof Heq' as Heq%scohg_vert_eq_alt.
  assert (Hverts : vertices (map_vec_sized_graph f scohg) =
    vertices (map_vec_sized_graph f scohg')). 1:{
    cbn.
    rewrite 2 vertices_venlarge_graph.
    apply scohg_vert_eq_iff in Heq'.
    apply leibniz_equiv_iff, set_bind_ext, eq_reflexivity, Heq'.2.2.2.1.
    intros p Hp _.
    cbn.
    rewrite <- Heq.2.2.2.2 by now apply elem_of_union_l.
    done.
  }
  apply mk_bundled_scohg_vert_eq.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite <- Heq.1.
    apply list_bind_ext_strong.
    intros k Hk.
    rewrite <- Heq.2.2.2.2 by set_solver +Hk.
    done.
  - cbn.
    rewrite 2 vec_to_list_bind.
    rewrite <- Heq.2.1.
    apply list_bind_ext_strong.
    intros k Hk.
    rewrite <- Heq.2.2.2.2 by set_solver +Hk.
    done.
  - cbn.
    rewrite Heq.2.2.1.
    apply map_fmap_ext.
    intros i tio Hi.
    f_equal; [f_equal|].
    + apply list_bind_ext_strong.
      intros v Hv.
      rewrite <- Heq.2.2.2.2 by now apply elem_of_union_r, elem_of_vertices; set_solver +Hv Hi.
      done.
    + apply list_bind_ext_strong.
      intros v Hv.
      rewrite <- Heq.2.2.2.2 by now apply elem_of_union_r, elem_of_vertices; set_solver +Hv Hi.
      done.
  - apply Hverts.
  - rewrite <- Hverts.
    apply map_filter_strong_ext.
    intros i s.
    cbn [fst].
    apply and_iff_from_l; [done|].
    intros Hi _.
    cbn.
    cbn in Hi.
    rewrite vertices_venlarge_graph in Hi.
    apply elem_of_set_bind in Hi as (p & Hp & Hi).
    cbn in Hi.
    rewrite (vec_to_list_fun_to_vec (λ i, encode (p, i))) in Hi.
    set_unfold in Hi.
    cbn in Hi.
    destruct Hi as (j & -> & Hj).
    rewrite 2 lookup_list_enlarge_Pmap_encode.
    rewrite <- Heq'.2 by done.
    done.
Qed.

Lemma sized_graph_to_pair_bundled_apply {N N' T T'}
  (f : forall n m, SizedCospanHyperGraph N T n m -> SizedCospanHyperGraph N' T' n m)
  {n m}
  (scohg : SizedCospanHyperGraph N T n m) :
  f n m scohg =ₛ
  (λ scohg', f _ _ (projT2 scohg'))
  (sized_graph_to_pair_bundled scohg).
Proof.
  done.
Qed.

Lemma map_vec_sized_graph_sized_isomorphic {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  sized_isomorphic scohg scohg' ->
  sigT2_relation (@sized_isomorphic _ _)
    (sized_graph_to_pair_bundled (map_vec_sized_graph f scohg))
    (sized_graph_to_pair_bundled (map_vec_sized_graph f scohg')).
Proof.
  intros (fe & fv & Hfe & Hfv & ->)%sized_isomorphic_exists.
  rewrite (map_vec_sized_graph_relabel_sized_graph _ _).
  rewrite (sized_graph_to_pair_bundled_apply
    (fun _ _ => relabel_sized_graph _)).
  rewrite (map_vec_sized_graph_reindex_sized_graph _ _).
  cbn.
  constructor.
  constructor; apply _.
Qed.



Lemma map_vec_sized_graph_struct_sized_isomorphic {N M T} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ᵢ scohg' ->
  map_vec_sized_graph f scohg [≡ᵢ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  unfold struct_sized_isomorphic at 1.
  intros Heq%(map_vec_sized_graph_sized_isomorphic f).
  etransitivity; [|etransitivity; [apply (subrel Heq)|]].
  - refine (subrel (map_vec_sized_graph_scohg_vert_eq f _ _ _)).
    now rewrite norm_sized_verts_vert_eq.
  - refine (subrel (map_vec_sized_graph_scohg_vert_eq f _ _ _)).
    now rewrite norm_sized_verts_vert_eq.
Qed.



Lemma map_vec_sized_graph_scohg_syntactic_eq {N M}
  `{Equiv T, Equivalence T equiv} {n m}
  {nf : N -> nat} (f : forall k, vec M (nf k))
  (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₛ scohg' ->
  map_vec_sized_graph f scohg [≡ₛ]ₛ
    map_vec_sized_graph f scohg'.
Proof.
  intros (scohg'' & fv & fe & Hfv & Hfe & Heq & ->)%scohg_syntactic_eq_exists.
  rewrite <- (map_vec_sized_graph_sized_isomorphic f scohg'' _
    (sized_iso_relabel_reindex _ _ _)).
  rewrite <- (map_vec_sized_graph_scohg_vert_eq f _ scohg
    (norm_sized_verts_vert_eq _)).
  rewrite (map_vec_sized_graph_scohg_eq f _ _ Heq).
  rewrite map_vec_sized_graph_scohg_vert_eq by apply norm_sized_verts_vert_eq.
  done.
Qed.


#[export] Instance unit_sized_graph_to_graph_cohg_eq `{Equiv T} {n m} :
  Proper (scohg_eq ==> @cohg_eq T n m _) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  apply Heq.1.
Qed.

#[export] Instance unit_sized_graph_to_graph_cohg_vert_eq {T n m} :
  Proper (scohg_vert_eq ==> @cohg_vert_eq T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  apply Heq.1.
Qed.

#[export] Instance unit_sized_graph_to_graph_sized_isomorphic {T n m} :
  Proper (sized_isomorphic ==> @isomorphic T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  now constructor.
Qed.

#[export] Instance unit_sized_graph_to_graph_struct_sized_isomorphic {T n m} :
  Proper (struct_sized_isomorphic ==> @struct_isomorphic T n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq%unit_sized_graph_to_graph_sized_isomorphic.
  apply Heq.
Qed.

#[export] Instance unit_sized_graph_to_graph_cohg_syntactic_eq `{Equiv T} {n m} :
  Proper (scohg_syntactic_eq ==> @cohg_syntactic_eq T _ n m) unit_sized_graph_to_graph.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  constructor; [done..|].
  unfold scohg_eq in *.
  destruct_and!.
  assumption.
Qed.


#[export] Instance sized_cospan_cohg_syntactic_eq {N} `{Equiv T} {n m} :
  Proper (scohg_syntactic_eq (N:=N) ==> @cohg_syntactic_eq T _ n m) sized_cospan.
Proof.
  intros cohg cohg' Heq.
  induction Heq.
  constructor; [done..|].
  unfold scohg_eq in *.
  destruct_and!.
  assumption.
Qed.


Lemma sigT2_relation_f_equiv {A B} {P Q : A -> B -> Type}
  (R : forall a b, relation (P a b))
  (R' : forall a b, relation (Q a b)) (f : forall a b, P a b -> Q a b)
  `{Hf : forall a b, Proper (R a b ==> R' a b) (f a b)} :
  Proper (sigT2_relation R ==> sigT2_relation R') (λ x, existT (_, _) (f _ _ (projT2 x))).
Proof.
  intros x y Heq.
  induction Heq.
  cbn.
  constructor.
  now f_equiv.
Qed.


Lemma sized_graph_to_graph_cohg_syntactic_eq {N} `{Equiv T, Equivalence T equiv} {n m}
  (f : N -> nat) (scohg scohg' : SizedCospanHyperGraph N T n m) :
  scohg ≡ₛ scohg' ->
  (sized_graph_to_graph f scohg [≡ₛ]ₛ sized_graph_to_graph f scohg')%cohg.
Proof.
  unfold sized_graph_to_graph.
  intros Heq%(map_vec_sized_graph_scohg_syntactic_eq (nf:=f) (λ k, fun_to_vec (λ _, ()))).
  refine (sigT2_relation_f_equiv _ _ (fun _ _ => sized_cospan)
    (Hf:=fun _ _ => sized_cospan_cohg_syntactic_eq) _ _ Heq).
Qed.


Lemma sum_list_with_fmap {A B} (f : B -> nat) (g : A -> B) (l : list A) :
  sum_list_with f (g <$> l) = sum_list_with (f ∘ g) l.
Proof.
  induction l; cbn; congruence.
Qed.

Lemma sum_list_with_eq_of_fmap {A} {f g : A -> nat} {l l' : list A} :
  f <$> l = g <$> l' -> sum_list_with f l = sum_list_with g l'.
Proof.
  intros Heq%(f_equal sum_list).
  now rewrite 2 sum_list_with_fmap in Heq.
Qed.

Notation "'cast_graph' Hn Hm cohg" :=
  (eq_rect _ (λ k, CospanHyperGraph _ k _)
    (eq_rect _ (CospanHyperGraph _ _) cohg%cohg _ Hm) _ Hn)
  (at level 10, Hn at level 9, Hm at level 9, cohg at level 9) : cohg_scope.

Notation "'cast_sized_graph' Hn Hm cohg" :=
  (eq_rect _ (λ k, SizedCospanHyperGraph _ _ k _)
    (eq_rect _ (SizedCospanHyperGraph _ _ _) cohg%scohg _ Hm) _ Hn)
  (at level 10, Hn at level 9, Hm at level 9, cohg at level 9) : scohg_scope.

Lemma hedges_cast_graph {T n m n' m'} (Hn : n = n') (Hm : m = m')
  (cohg : CospanHyperGraph T n m) :
  hedges (cast_graph Hn Hm cohg) = hedges cohg.
Proof.
  now subst.
Qed.

Lemma inputs_cast_graph {T n m n' m'} (Hn : n = n') (Hm : m = m')
  (cohg : CospanHyperGraph T n m) :
  inputs (cast_graph Hn Hm cohg) = Vector.cast (inputs cohg) Hn.
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma outputs_cast_graph {T n m n' m'} (Hn : n = n') (Hm : m = m')
  (cohg : CospanHyperGraph T n m) :
  outputs (cast_graph Hn Hm cohg) = Vector.cast (outputs cohg) Hm.
Proof.
  subst.
  now rewrite cast_id.
Qed.

Lemma subst_by_vec_ext_to_list {n m}
  (v : vec _ n) (w : vec _ m) :
  v =@{list _} w ->
  subst_by_vec v = subst_by_vec w.
Proof.
  intros Heq.
  apply vec_to_list_inj1 in Heq as Hnm.
  subst m.
  apply vec_to_list_inj2 in Heq.
  now subst.
Qed.

Lemma propogate_subst_ext_to_list {n m}
  (v : vec _ n) (w : vec _ m) :
  v =@{list _} w ->
  propogate_subst v =@{list _} propogate_subst w.
Proof.
  intros Heq.
  apply vec_to_list_inj1 in Heq as Hnm.
  subst m.
  apply vec_to_list_inj2 in Heq.
  now subst.
Qed.


(* Lemma vzip_vbind_cast_l {A B} {nf : A -> nat} (f : forall a, vec B (nf a))
  {n} (v w : vec A n) H K :
  nf <$> (v :> list A) = nf <$> (w :> list A) ->
  vzip (Vector.cast (vbind f v) H) (vbind f w) =
  K. *)

Lemma zip_with_bind {A B C D E} (f : A -> list C) (g : B -> list D) (h : C -> D -> E)
  (l : list A) (l' : list B) :
  Forall2 (λ a b, length (f a) = length (g b)) l l' ->
  zip_with h (l ≫= f) (l' ≫= g) =
  zip l l' ≫= λ ab, zip_with h (f ab.1) (g ab.2).
Proof.
  intros Hl.
  induction Hl; [done|].
  cbn.
  rewrite zip_with_app by done.
  congruence.
Qed.
(*
Lemma venlarge_graph_compose_graphs_aux {T n m o} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o)
  (Hoi : nf <$> (outputs cohg :> list _) = nf <$> (inputs cohg' :> list _)) :
  (venlarge_graph f (compose_graphs_aux cohg cohg') =ₛ
  compose_graphs_aux (
    cast_graph eq_refl (sum_list_with_eq_of_fmap Hoi)
    (venlarge_graph f cohg)) (venlarge_graph f cohg'))%cohg.
Proof.
  unfold compose_graphs_aux.
  rewrite venlarge_graph_relabel_graph.
  apply mk_cohg_bundled_eq.
  - cbn -[eq_rect].
    rewrite vec_to_list_bind, vec_to_list_map.
    rewrite outputs_cast_graph, inputs_cast_graph.
    rewrite cast_id.
    cbn.
    symmetry.
    assert (f = (λ p, fun_to_vec (λ i, encode (p, fin_to_nat i)))) by admit.
    subst f.

    erewrite subst_by_vec_ext_to_list. 2:{
      apply propogate_subst_ext_to_list.
      rewrite vec_to_list_zip_with.
      rewrite vec_to_list_cast.
      rewrite 2 vec_to_list_bind.
      rewrite zip_with_bind. 2:{
        apply list_eq_Forall2 in Hoi.
        rewrite Forall2_fmap in Hoi.
        apply (Forall2_impl _ _ _ _ Hoi).
        now intros; rewrite 2 length_vec_to_list.
      }
      etransitivity. 1:{
        apply list_bind_ext_strong.
        intros ab Hab.
        apply elem_of_list_lookup in Hab as (i & Hi).
        rewrite (surjective_pairing ab) in Hi.
        apply lookup_zip_Some in Hi as [Hia Hib].
        apply (f_equal (.!! i)) in Hoi.
        rewrite 2 list_lookup_fmap, Hia, Hib in Hoi.
        cbn in Hoi.
        pose proof Hoi as [= Hnf].
        rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
        rewrite zip_fmap_l, zip_fmap_r.
        cbn.
        rewrite <- Hnf.
        rewrite zip_with_diag.
        rewrite <- 2 list_fmap_compose.
        unfold compose; cbn.
        reflexivity.
      }
      etransitivity; [symmetry; apply vec_to_list_to_vec|].
      reflexivity.
    }
    rewrite vec_to_list_bind.
    rewrite list_bind_fmap.
    apply list_bind_ext, reflexivity.
    intros p.
    rewrite 2 (vec_to_list_fun_to_vec (λ i, encode (_, i))).
    rewrite <- list_fmap_compose.
    unfold compose.
    rewrite
    rewrite (vec_to_list_fun_to_vec (λ i, encode (_, i))).
    subst f.
    cbn.
    rewrite <- list_fmap_compose.
    unfold compose.


Lemma venlarge_graph_compose_graphs_aux {T n m o} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T m o)
  (Hoi : nf <$> (outputs cohg :> list _) = nf <$> (inputs cohg' :> list _)) :
  (venlarge_graph f (compose_graphs_aux cohg cohg') =ₛ
  compose_graphs_aux (
    cast_graph eq_refl (sum_list_with_eq_of_fmap Hoi)
    (venlarge_graph f cohg)) (venlarge_graph f cohg'))%cohg.
Proof.
  unfold compose_graphs_aux.
  rewrite venlarge_graph_relabel_graph.
  apply mk_cohg_bundled_eq.
  - cbn -[eq_rect].
    rewrite vec_to_list_bind, vec_to_list_map.
    rewrite outputs_cast_graph, inputs_cast_graph.
    rewrite cast_id.
    cbn.
    symmetry.
    erewrite subst_by_vec_ext_to_list. 2:{
      apply propogate_subst_ext_to_list.
      rewrite vec_to_list_zip_with.
      rewrite vec_to_list_cast.
      rewrite 2 vec_to_list_bind.
      rewrite zip_with_bind. 2:{
        apply list_eq_Forall2 in Hoi.
        rewrite Forall2_fmap in Hoi.
        apply (Forall2_impl _ _ _ _ Hoi).
        now intros; rewrite 2 length_vec_to_list.
      }
      etransitivity; [symmetry; apply vec_to_list_to_vec|].
      reflexivity.
    }
    rewrite vec_to_list_bind.
    rewrite list_bind_fmap.
    apply list_bind_ext, reflexivity.
    intros p.
    assert (f = (λ p, fun_to_vec (λ i, encode (p, fin_to_nat i)))) by admit.
    subst f.
    cbn.
    rewrite (vec_to_list_fun_to_vec (λ i, encode (p, i))).
    rewrite <- list_fmap_compose.
    unfold compose. *)

Lemma exists_by_forall {A} (P : A -> Prop) :
  A -> (forall a, P a) -> exists a, P a.
Proof.
  unshelve eauto; done.
Qed.

Lemma sized_graph_to_graph_compose_graphs {N T n m o}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T m o) :
  (scohg.(sized_map) !!.) <$> (outputs scohg :> list _) =
  (scohg'.(sized_map) !!.) <$> (inputs scohg' :> list _) ->
  exists H,
  (sized_graph_to_graph f (compose_sized_graphs scohg scohg') [≡ᵢ]ₛ
  compose_graphs (cast_graph eq_refl H (sized_graph_to_graph f scohg))
    (sized_graph_to_graph f scohg'))%cohg.
Proof.
  intros Heq.
  apply exists_by_forall.
  1:{
    apply sum_list_with_eq_of_fmap.
    apply (f_equal (fmap (fmap f))) in Heq.
    apply (f_equal (fmap (default 0))) in Heq.
    rewrite <- 4 list_fmap_compose in Heq.
    apply Heq.
  }
  intros H.
Admitted.

Lemma enlarge_hypergraph_union {T} f (hg hg' : HyperGraph T) :
  enlarge_hypergraph f (hg ∪ hg') =
  enlarge_hypergraph f hg ∪ enlarge_hypergraph f hg'.
Proof.
  apply hg_ext.
  - apply map_fmap_union.
  - cbn.
    apply set_bind_union_L.
Qed.

Lemma venlarge_graph_stack_graphs_aux {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (* hyperedges cohg ##ₘ hyperedges cohg' -> *)
  (venlarge_graph f (stack_graphs_aux cohg cohg') =ₛ
  stack_graphs_aux (venlarge_graph f cohg) (venlarge_graph f cohg'))%cohg.
Proof.
  (* intros Hdisj. *)
  apply mk_cohg_bundled_eq.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    rewrite vec_to_list_bind, 2 vec_to_list_app,
      bind_app, 2 vec_to_list_bind.
    done.
  - cbn.
    apply enlarge_hypergraph_union.
Qed.

Lemma graph_to_pair_bundled_apply2 {T T' T''}
  {fn : nat -> nat -> nat} {fm : nat -> nat -> nat}
  (f : forall n m n' m',
    CospanHyperGraph T n m -> CospanHyperGraph T' n' m' ->
    CospanHyperGraph T'' (fn n n') (fm m m'))
  {n m n' m'} (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T' n' m') :
  (f n m n' m' cohg cohg' =ₛ
  (λ x y, f _ _ _ _ (projT2 x) (projT2 y)) (graph_to_pair_bundled cohg)
    (graph_to_pair_bundled cohg'))%cohg.
Proof.
  done.
Qed.



Lemma venlarge_graph_reindex_graph {T n m} {nf : positive -> nat}
  (f : forall p, vec positive (nf p)) (g : positive -> positive)
  (cohg : CospanHyperGraph T n m) :
  venlarge_graph f (reindex_graph g cohg) =
  reindex_graph g (venlarge_graph f cohg).
Proof.
  apply cohg_ext; [|done..].
  cbn.
  apply enlarge_hypergraph_reindex_hg.
Qed.

Lemma venlarge_graph_stack_graphs {T n m n' m'} {nf : positive -> nat}
  (f : forall p, vec positive (nf p))
  (cohg : CospanHyperGraph T n m) (cohg' : CospanHyperGraph T n' m') :
  (venlarge_graph f (stack_graphs cohg cohg') [≡ᵢ]ₛ
  stack_graphs (venlarge_graph f cohg) (venlarge_graph f cohg'))%cohg.
Proof.
  unfold stack_graphs.
  rewrite venlarge_graph_stack_graphs_aux.
  rewrite graph_to_pair_bundled_apply2.
  rewrite 2 venlarge_graph_relabel_graph, 2 venlarge_graph_reindex_graph.
  cbn.
Admitted.


Lemma sum_list_with_ext {A} (f g : A -> nat) l : 
  (forall a, a ∈ l -> f a = g a) -> 
  sum_list_with f l = sum_list_with g l.
Proof.
  rewrite <- Forall_forall.
  intros Hl.
  induction Hl; cbn; congruence.
Qed.

Lemma sized_graph_to_graph_stack_graphs {N T n m n' m'}
  (f : N -> nat) (scohg : SizedCospanHyperGraph N T n m)
  (scohg' : SizedCospanHyperGraph N T n' m') :
  (sized_graph_to_graph f (stack_sized_graphs scohg scohg') [≡ᵢ]ₛ
  stack_graphs (sized_graph_to_graph f scohg)
    (sized_graph_to_graph f scohg'))%cohg.
Proof.
  apply sigT2_relation_alt.
  apply exists_by_forall.
  1:{
    cbn.
    rewrite 2 vec_to_list_app, 
      4 vec_to_list_map, 2 sum_list_with_app, 4 sum_list_with_fmap.
    do 2 f_equal; apply sum_list_with_ext; intros a _;
    cbn -[bcons];
    rewrite lookup_union;
    rewrite (lookup_kmap _); rewrite (lookup_kmap_None _ _ _).2 by lia;
    rewrite 1?(left_id_L None _), 1?(right_id_L None _);
    done.
  }
  intros H.
Admitted.




