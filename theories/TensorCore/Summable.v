Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Set Warnings "-stdlib-vector".
Require Import SetoidList SetoidPermutation. 
Require Export Algebra.
Require Import Ring.
From stdpp Require Import vector fin.
From stdpp Require Export base list.
Require Import Aux_stdpp.


(* A typeclass indicating a type can be summed over, hence
  used in tensor expressions. Note that this is in fact just 
  expressing that there are some distinguished elements of the 
  type. It is expected that the types used are finite and that 
  these lists of elements are complete, but this is not enforced 
  as it is not needed for proofs. So, if desirable, infinite types 
  can be used, though only finitely many values will be used. 
  
  The motivation for this definition is that it means multiple
  instances automatically commute with each other, which is not
  enforcable if the summation function is abstract. (In that case,
  a separate compatability typeclass would be required, which would
  make summations over lists of registers highly impractical and
  balloon proof requirements.) *)
Class Summable (A : Type) := sum_over {
  sum_elements : list A
}.

#[global] Arguments sum_over {_} _ : assert.



(* The sum of a function over a summable domain [A]. 
  We require the codomain to be a SemiRing so that 
  typeclass search can find the definitions of 0 
  and addition.  *)
Definition sum_of `{SR : SemiRing R rO rI radd rmul req} `{SA : Summable A} 
  (f : A -> R) : R :=
  Rlist_sum (f <$> sum_elements).

Global Arguments sum_of {_ _ _ _ _ _ _ _ _} (_)%_function_scope : assert.

(* As [sum_of] has many arguments, we have a notation which exposes
  only the last three. *)
Notation sum_of_with := (@sum_of _ _ _ _ _ _ _) (only parsing).

(* Lemma to unfold [sum_of]. Should not be to reason about 
  tensor expressions directly, only to reason about their 
  definition, such as in relation to other libraries. *)
Lemma sum_of_defn `{SemiRing R rO rI radd rmul req} `{Summable A} (f : A -> R) : 
  sum_of f = Rlist_sum (List.map f sum_elements).
Proof. reflexivity. Qed.

(* We want to prevent [sum_of] ever being evaluated, as this 
  would be catastrophic in many concrete cases (for example,
  [Vector.t bool 10] has [sum_elements] with length [2^10]). *)
Global Opaque sum_of.

(** Tactics to manipulate expressions involving [sum_of] *)

(* Replaces [sum_of] with its definition in all hypotheses and goals *)
Ltac unfold_sum_of :=
  rewrite_strat (bottomup sum_of_defn).

(* Generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_elem l :=
  match goal with 
  |- context [@sum_elements ?A ?SA] => 
    generalize (@sum_elements A SA);
    intros l
  end.

(* Replaces [sum_of] with its definition in all hypotheses and goals
  and generalizes [sum_elements], introducing the generalized list
  with identifier [l] *)
Ltac gen_sum_of l :=
  try unfold_sum_of;
  gen_sum_elem l.

(* Tries to solve a goal about [sum_of] by repeatedly unfolding 
  [sum_of], generalizing [sum_elements], and inducting on the 
  resulting goals. Applies [basetac] to the base case and 
  [indtac IHl] to the inductive case *)
Ltac solve_sum_of basetac indtac :=
  let l := fresh "l" in 
  let IHl := fresh "IHl" in 
  gen_sum_of l;
  induction l as [|? l IHl]; 
  [basetac | indtac IHl].

(* Tries to solve a goal about [sum_of] by repeatedly unfolding 
  [sum_of], generalizing [sum_elements], and inducting on the 
  resulting goals. Solves goals with [simpl; ring], or 
  [simpl; ring [IHl]] in the inductive case *)
Ltac solve_sum_of_ring :=
  solve_sum_of ltac:(simpl; ring) ltac:(fun IHl => simpl; ring [IHl]).


(* We have a specific notation for a sum over a single register, so 
  that sums over many registers can look better. *)
Notation " '∑' x ':' T ',' f " :=
  (@sum_of_with T _ (fun x => f)) 
  (at level 60, 
  x name, T at level 200, f at level 69,
  right associativity).

Notation " '∑' x ',' f " :=
  (∑ x : _, f) 
  (at level 60, 
  x name, f at level 69,
  right associativity, 
  only parsing).

Section SumTheory.

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


Lemma sum_of_ext_gen `{Summable A} (f g : A -> R) 
  (eqR : relation R) : Reflexive eqR ->
  Morphisms.Proper (eqR ==> eqR ==> eqR) radd ->
  (forall x, eqR (f x) (g x)) ->
  eqR (∑ x, f x) (∑ x, g x).
Proof.
  intros Heq Hadd Hfg.
  gen_sum_of l.
  induction l; [reflexivity|].
  simpl.
  apply Hadd.
  - apply Hfg.
  - apply IHl.
Qed.

Lemma sum_of_ext `{Summable A} (f g : A -> R) :
  (forall x, f x == g x) ->
  ∑ x, f x == ∑ x, g x.
Proof.
  apply sum_of_ext_gen; apply _.
Qed.

Lemma sum_of_ext_eq `{Summable A} (f g : A -> R) : 
  (forall x, f x = g x) ->
  ∑ x, f x = ∑ x, g x.
Proof.
  apply sum_of_ext_gen; apply _.
Qed.


Lemma sum_of_0 `{Summable A} : 
  ∑ _ : A, 0 == 0.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_add `{Summable A} (f g : A -> R) : 
  ∑ x, f x + g x == (∑ x, f x) + (∑ x, g x).
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_distr_l `{Summable A} (f : A -> R) r: 
  (∑ x, f x) * r == ∑ x, f x * r.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_distr_r `{Summable A} (f : A -> R) (r : R) : 
  r * (∑ x, f x) == ∑ x, r * f x.
Proof.
  solve_sum_of_ring.
Qed.

Lemma sum_of_comm `{Summable A, Summable B} (f : A -> B -> R) : 
  ∑ x, ∑ y, f x y == ∑ y, ∑ x, f x y.
Proof.
  erewrite sum_of_ext by 
    now intros; apply eq_reflexivity, sum_of_defn.
  rewrite (sum_of_defn (A:=B)).
  gen_sum_elem lB.
  induction lB.
  - apply sum_of_0.
  - simpl.
    rewrite sum_of_add.
    rewrite IHlB.
    reflexivity.
Qed.

Lemma sum_of_mul_sum_of `{Summable A, Summable B} (f : A -> R) (g : B -> R) : 
  (∑ x, f x) * (∑ y, g y) == ∑ x, ∑ y, f x * g y.
Proof.
  rewrite sum_of_distr_l.
  apply sum_of_ext; intros x.
  now rewrite sum_of_distr_r.
Qed.

Lemma sum_of_ext' `{Summable A} (f g : A -> R) :
  (forall a, a ∈ sum_elements -> f a == g a) ->
  sum_of f == sum_of g.
Proof.
  intros Hfg.
  unfold_sum_of.
  apply Rlist_sum_ext.
  rewrite Forall2_fmap_l, Forall2_fmap_r.
  apply Forall_Forall2_diag.
  now apply Forall_forall.
Qed.

Lemma sum_of_relabel `{Summable A, Summable B} (f : A -> B) (g : B -> R) :
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ b : B, g b == ∑ a : A, g (f a).
Proof.
  unfold_sum_of.
  intros Hperm.
  apply Rlist_sum_perm.
  rewrite <- Hperm, list_map_fmap, <- list_fmap_compose.
  reflexivity.
Qed.

Lemma sum_of_relabel'_l2r `{Summable A, Summable B}
  (f : A -> B) (g : A -> R) (h : B -> R) :
  (forall a, a ∈ sum_elements -> g a == h (f a)) ->
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ a : A, g a == ∑ b : B, h b.
Proof.
  intros Hfh Hf.
  rewrite (sum_of_relabel f h) by assumption.
  now apply sum_of_ext'.
Qed.


Lemma sum_of_relabel'_r2l `{Summable A, Summable B}
  (f : B -> A) (g : A -> R) (h : B -> R) :
  (forall b, b ∈ sum_elements -> g (f b) == h b) ->
  f <$> sum_elements ≡ₚ sum_elements ->
  ∑ a : A, g a == ∑ b : B, h b.
Proof.
  intros Hfh Hf.
  rewrite (sum_of_relabel f g) by assumption.
  now apply sum_of_ext'.
Qed.

End SumTheory.


Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req} 
  {A} {SA : Summable A} : (@sum_of_with A SA) 
  with signature Morphisms.pointwise_relation A req ==> req as
  sum_of_mor.
Proof.
  apply sum_of_ext.
Qed.

Add Parametric Morphism `{SR : SemiRing R rO rI radd rmul req} 
  {A} {SA : Summable A} : (@sum_of_with A SA) 
  with signature Morphisms.pointwise_relation A eq ==> (@eq R) as
  sum_of_mor_eq.
Proof.
  apply sum_of_ext_eq.
Qed.

#[export] Instance Summable_bool : Summable bool := 
  sum_over [false; true].

(* TODO: Replace with stdpp's Finite's enum, if we want to use stdpp *)
Fixpoint fin_elements (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => Fin.F1 :: (Fin.FS <$> fin_elements n')
  end.

Lemma fin_elements_NoDup n : NoDup (fin_elements n).
Proof.
  induction n.
  - constructor.
  - cbn. 
    constructor.
    + rewrite elem_of_list_fmap.
      firstorder discriminate.
    + now apply (NoDup_fmap _).
Qed.

Lemma fin_elements_in n (i : Fin.t n) : In i (fin_elements n).
Proof.
  induction i.
  - now left.
  - cbn.
    right.
    now apply in_map.
Qed.

Lemma length_fin_elements n : length (fin_elements n) = n.
Proof.
  induction n; cbn; f_equal; now simpl_list.
Qed.

#[export] Instance Summable_fin n : Summable (Fin.t n) :=
  sum_over (fin_elements n).

(* TODO: Is there an existing function for this? *)
Fixpoint vec_elements `(l : list A) (n : nat) : list (Vector.t A n) :=
  match n with
  | 0 => [@Vector.nil A]
  | S n' => flat_map (fun a => map (@Vector.cons A a n') (vec_elements l n')) l
  end.

Lemma ForallPairs_cons `(R : relation A) a (l : list A) : 
  ForallPairs R (a :: l) <-> R a a /\ Forall (R a) l /\ 
    Forall (fun x => R x a) l /\ ForallPairs R l.
Proof.
  rewrite 2 Forall_forall.
  unfold ForallPairs.
  setoid_rewrite elem_of_list_In.
  cbn.
  firstorder subst; auto.
Qed.

Lemma ForallPairs_not_eq_ForallOrdPairs_NoDup `(R : relation A) (l : list A) : 
  NoDup l ->
  ForallPairs (fun x y => x <> y -> R x y) l ->
  ForallOrdPairs R l.
Proof.
  intros Hl.
  induction Hl as [|a l Ha Hl IHHl]; [constructor|].
  rewrite ForallPairs_cons.
  intros [_ [Hal [Hla Hl'%IHHl]]].
  constructor; [|easy].
  rewrite Forall_forall in Hal |- *.
  intros x Hx; apply Hal in Hx as Hx'; [easy|now intros ->].
Qed.

Lemma ForallPairs_map `(f : A -> B) (P : B -> B -> Prop) (l : list A) : 
  ForallPairs P (map f l) <-> ForallPairs (fun x y => P (f x) (f y)) l.
Proof.
  unfold ForallPairs.
  setoid_rewrite in_map_iff.
  firstorder subst; eauto.
Qed.

Lemma vec_elements_nonempty `(l : list A) n : 
  l <> [] -> vec_elements l n <> [].
Proof.
  intros Hl.
  induction n; [easy|].
  cbn.
  destruct l; [easy|].
  cbn.
  destruct (vec_elements _ _); [easy|].
  cbn.
  easy.
Qed.

(* Lemma map_inj `(f : A -> B) l l' : 
  (forall a b, f a = f b -> a = b) -> 
  map  *)

Lemma vec_elements_NoDup `(l : list A) (n : nat) : 
  NoDup l -> NoDup (vec_elements l n).
Proof.
  revert n.
  assert (Haux : l <> [] -> forall x y n, map (@Vector.cons A x n) (vec_elements l n) =
   map (@Vector.cons A y n) (vec_elements l n) <-> x = y). 1:{
    intros Hl x y n.
    split; [|now intros ->].
    apply (vec_elements_nonempty _ n) in Hl.
    destruct (vec_elements l n); [easy|].
    cbn.
    now intros [= ? _].
  }
  intros n Hl.
  induction n.
  - cbn. 
    constructor; [|constructor].
    easy.
  - cbn.
    rewrite flat_map_concat_map.
    apply NoDup_ListNoDup, NoDup_concat.
    + apply Forall_map, Forall_forall.
      intros x Hx.
      apply NoDup_map_NoDup_ForallPairs; [|now apply NoDup_ListNoDup].
      now intros ? ? ? ? []%Vector.cons_inj.
    + apply ForallPairs_not_eq_ForallOrdPairs_NoDup. 
      1:{ 
        apply NoDup_ListNoDup, NoDup_map_NoDup_ForallPairs; 
          [|now apply NoDup_ListNoDup].
        hnf.
        intros a b Ha Hb.
        apply Haux.
        now intros ->.
      }
      apply ForallPairs_map.
      intros a b Ha Hb.
      rewrite Haux by now intros ->.
      intros Hab.
      setoid_rewrite in_map_iff.
      intros a_vs (vs & <- & _).
      firstorder congruence.
Qed.

Lemma vec_elements_in `(l : list A) n v : 
  In v (vec_elements l n) <-> Vector.Forall (fun x => In x l) v.
Proof.
  induction v.
  - cbn; firstorder constructor.
  - cbn.
    rewrite in_flat_map, Vector.Forall_cons_iff, <- IHv.
    setoid_rewrite in_map_iff.
    split.
    + intros (h' & Hh & (? & [-> ->]%Vector.cons_inj & Hv)).
      easy.
    + intros [].
      eauto.
Qed.

Lemma vec_elements_in' `(l : list A) n : 
  (forall a, In a l) -> forall v, In v (vec_elements l n).
Proof.
  intros Hl v.
  rewrite vec_elements_in.
  induction v; constructor; auto.
Qed.

Lemma length_vec_elements `(l : list A) n : 
  length (vec_elements l n) = Nat.pow (length l) n.
Proof.
  induction n; [reflexivity|].
  cbn.
  rewrite length_flat_map.
  erewrite map_ext. 2:{
    intros a.
    rewrite length_map, IHn.
    reflexivity.
  }
  clear IHn.
  generalize (length l) at 1 3 as k.
  intros k.
  induction l; [reflexivity|].
  cbn.
  f_equal; apply IHl.
Qed.

#[export]
Instance Summable_vec `{Summable A} n : Summable (Vector.t A n) :=
  sum_over (vec_elements sum_elements n).

Section fin_fun.

(* Import Fin. *)

Local Notation "'!S' f" := (fun i => f (Fin.FS i)) (only parsing, at level 10).

Local Definition fin_S_inv {n} (P : Fin.t (S n) -> Type)
  (H0 : P Fin.F1) (HS : forall i, P (Fin.FS i)) (i : Fin.t (S n)) : P i.
Proof.
  revert P H0 HS.
  refine match i with Fin.F1 => fun _ H0 _ => H0 
  | Fin.FS i => fun _ _ HS => HS i end.
Defined.

Fixpoint fin_fun_elements_aux {n} : forall (f : Fin.t n -> Type) 
  (Sf : forall i, list (f i)), list (forall i, f i) := 
  match n with 
  | 0 => fun f Sf => [Fin.case0 f]
  | S n' =>
    fun f Sf =>
    let l := 
      fin_fun_elements_aux (!S f) (!S Sf) in
    flat_map (fun x => map (fin_S_inv f x) l) (Sf (Fin.F1))
  end.


Lemma fin_fun_elements_aux_ina_gen {n} (f : Fin.t n -> Type) Sf 
  (Rf : forall i, relation (f i)) g : 
  InA (forall_relation Rf) g (fin_fun_elements_aux f Sf) <->
  forall i, (InA (Rf i) (g i) (Sf i)).
Proof.
  rewrite InA_altdef.
  induction n.
  - cbn.
    rewrite Exists_cons, Exists_nil.
    split; intros _; [|left]; exact (Fin.case0 _).
  - cbn.
    rewrite Exists_flat_map.
    split.
    + intros (x & Hx & HgS)%Exists_exists.
      (* pose proof HgS as Hx'. *)
      rewrite Exists_exists in HgS.
      destruct HgS as (g' & (gS' & -> & HgS')%elem_of_list_fmap & Hgg').
      specialize (Hgg' Fin.F1) as Hxeq.
      cbn in Hxeq.
      apply fin_S_inv. 
      * rewrite InA_altdef, Exists_exists. 
        eauto. 
      * apply IHn.
        rewrite Exists_exists.
        exists gS'.
        split; [easy|].
        intros i; apply Hgg'.
    + intros Hg.
      rewrite Exists_exists.
      pose proof (Hg Fin.F1) as 
        (g1' & Hg1' & Hg1g1')%InA_altdef%Exists_exists.
      exists g1'.
      split; [auto|].
      rewrite Exists_exists.
      specialize (IHn (!S f) (!S Sf) (!S Rf) (!S g)).
      apply proj2 in IHn.
      specialize (IHn (!S Hg)).
      rewrite Exists_exists in IHn.
      destruct IHn as (gS' & HgS' & HgSgS').
      eexists.
      split; [apply elem_of_list_fmap_1; eassumption|].
      hnf.
      now apply fin_S_inv.
Qed.

Lemma fin_fun_elements_aux_ina_eq {n} (f : Fin.t n -> Type) Sf g : 
  InA (fun f g => forall x, f x = g x) g (fin_fun_elements_aux f Sf) <->
  forall i, (In (g i) (Sf i)).
Proof.
  setoid_rewrite (fin_fun_elements_aux_ina_gen f Sf (fun _ => eq)).
  apply forall_iff.
  intros i.
  split; [|apply In_InA, _].
  now intros (_ & Hgi & <-)%InA_altdef%Exists_exists; apply elem_of_list_In.
Qed.

End fin_fun.


#[export] 
Instance Summable_prod `{Summable A, Summable B} : Summable (A * B) :=
  sum_over (list_prod sum_elements sum_elements).

#[export] 
Instance Summable_sum `{Summable A, Summable B} : Summable (A + B) :=
  sum_over ((inl <$> sum_elements) ++ (inr <$> sum_elements)).

Fixpoint sum_of_fin `{SR : SemiRing R rO rI radd rmul req} {n : nat} 
  (f : Fin.t n -> R) : R :=
  match n, f with
  | O, _ => rO
  | S k, _ => radd (f Fin.F1) (sum_of_fin (fun fin => f (Fin.FS fin)))
  end.

Fixpoint sum_of_vec `{SR : SemiRing R rO rI radd rmul req} {n : nat} 
  `{Summable A} : (Vector.t A n -> R) -> R :=
    match n with
    | O => fun f => f (Vector.nil)
    | S n' => fun f => ∑ b : A, 
      sum_of_vec (fun bs => f (Vector.cons b bs))
    end.

(* FIXME: Move to aux *)
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



Section SummableInstanceUnfold.

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


Lemma sum_of_bool_defn (f : bool -> R) : 
  sum_of f == f false + f true.
Proof.
  unfold_sum_of.
  cbn; ring.
Qed.


Lemma sum_of_fin_0 (f : Fin.t 0 -> R) : 
  sum_of f = 0.
Proof.
  reflexivity.
Qed.

Lemma sum_of_fin_1 (f : Fin.t 1 -> R) : 
  sum_of f == f Fin.F1.
Proof.
  unfold_sum_of; cbn; ring.
Qed.

Lemma sum_of_fin_succ {n} (f : Fin.t (S n) -> R) : 
  sum_of f = f Fin.F1 + sum_of (fun x => f (Fin.FS x)).
Proof.
  unfold_sum_of.
  cbn.
  now rewrite map_map.
Qed.

Lemma sum_of_fin_defn {n} (f : Fin.t n -> R) : 
  sum_of f == sum_of_fin f.
Proof.
  induction n.
  - now rewrite sum_of_fin_0.
  - now rewrite sum_of_fin_succ, IHn.
Qed.

Lemma sum_of_fin_add {n m} (f : Fin.t (n + m) -> R) : 
  sum_of f == sum_of (fun x => f (Fin.L m x)) + sum_of (fun x => f (Fin.R n x)).
Proof.
  induction n.
  - rewrite sum_of_fin_0.
    cbn in *.
    now rewrite radd_0_l.
  - cbn.
    rewrite 2 sum_of_fin_succ.
    rewrite IHn.
    rewrite radd_assoc.
    reflexivity.
Qed.

Lemma sum_of_fin_mul {n m} (f : Fin.t (n * m) -> R) :
  sum_of f == ∑ x : Fin.t n, ∑ y : Fin.t m, f (Fin.depair x y).
Proof.
  induction n.
  - now rewrite 2 sum_of_fin_0.
  - cbn.
    rewrite sum_of_fin_succ, sum_of_fin_add.
    rewrite IHn.
    reflexivity.
Qed.

Section Vector.

Context `{SA : Summable A}.

Lemma sum_of_vec_0 (f : Vector.t A 0 -> R) : 
  sum_of f == f (Vector.nil).
Proof.
  unfold_sum_of.
  cbn.
  ring.
Qed.

Lemma sum_of_vec_1 (f : Vector.t A 1 -> R) : 
  sum_of f == ∑ a, f (Vector.cons a (Vector.nil)).
Proof.
  unfold_sum_of; cbn;
  solve_sum_of_ring.
Qed.

Lemma sum_of_vec_succ {n} (f : Vector.t A (S n) -> R) : 
  sum_of f == ∑ a, sum_of (fun v => f (Vector.cons a v)).
Proof.
  rewrite sum_of_defn.
  cbn.
  rewrite flat_map_concat_map.
  rewrite concat_map, map_map.
  rewrite Rlist_sum_concat.
  rewrite map_map.
  rewrite sum_of_defn.
  erewrite map_ext by now intros; rewrite map_map; reflexivity.
  symmetry.
  erewrite map_ext by now intros; rewrite sum_of_defn; reflexivity.
  reflexivity.
Qed.

Lemma sum_of_vec_defn {n} (f : Vector.t A n -> R) : 
  sum_of f == sum_of_vec f.
Proof.
  induction n.
  - now rewrite sum_of_vec_0.
  - now rewrite sum_of_vec_succ; setoid_rewrite IHn.
Qed.

Lemma sum_of_vec_add {n m} (f : Vector.t A (n + m) -> R) : 
  sum_of f == ∑ v, ∑ w, f (Vector.append v w).
Proof.
  induction n.
  - rewrite sum_of_vec_0.
    reflexivity.
  - cbn.
    rewrite 2 sum_of_vec_succ.
    setoid_rewrite IHn.
    reflexivity.
Qed.

End Vector.

Lemma sum_of_prod_defn `{Summable A, Summable B} (f : A * B -> R) : 
  sum_of f == ∑ a, ∑ b, f (a, b).
Proof.
  unfold_sum_of.
  cbn.
  gen_sum_elem lA.
  gen_sum_elem lB.
  induction lA; [reflexivity|].
  cbn.
  rewrite map_app, Rlist_sum_app, map_map.
  f_equiv.
  apply IHlA.
Qed.


Lemma sum_of_sum_defn `{Summable A, Summable B} (f : A + B -> R) : 
  sum_of f == (∑ a, f (inl a)) + (∑ b, f (inr b)).
Proof.
  unfold_sum_of.
  cbn.
  rewrite map_app, Rlist_sum_app, 2 map_map.
  reflexivity.
Qed.


End SummableInstanceUnfold.
