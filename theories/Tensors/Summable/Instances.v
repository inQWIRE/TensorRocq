Require Import Setoid.
Require Import Relation_Definitions.
Require Import Classes.Morphisms.
Set Warnings "-stdlib-vector".
Require Import SetoidList SetoidPermutation.
Require Import Ring.
From stdpp Require Import vector fin.
From stdpp Require Export base list.
From TensorRocq Require Import Aux_stdpp Aux.
From TensorRocq Require Export Algebra.Instances.
From TensorRocq Require Export Summable.Definitions.



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


Lemma fin_elements_eq_fun_to_vec n :
  fin_elements n = fun_to_vec id.
Proof.
  induction n; [done|].
  cbn.
  rewrite IHn.
  rewrite <- vec_to_list_map, vmap_fun_to_vec.
  done.
Qed.

Lemma vec_to_list_fun_to_vec_gen
  {A n} (f : fin n -> A) :
  vec_to_list (fun_to_vec f) = f <$> fin_elements _.
Proof.
  rewrite fin_elements_eq_fun_to_vec.
  rewrite <- vec_to_list_map, vmap_fun_to_vec.
  done.
Qed.


Lemma NoDup_fun_to_vec {A n} (f : fin n -> A) (Hf : Inj eq eq f) :
  NoDup (fun_to_vec f).
Proof.
  rewrite vec_to_list_fun_to_vec_gen.
  apply (NoDup_fmap _), fin_elements_NoDup.
Qed.

(* TODO: Is there an existing function for this? *)
Fixpoint vec_elements `(l : list A) (n : nat) : list (Vector.t A n) :=
  match n with
  | 0 => [@Vector.nil A]
  | S n' => flat_map (fun a => map (@Vector.cons A a n') (vec_elements l n')) l
  end.

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


Fixpoint sum_of_vec `{SummableOver R A} {n : nat}
   : (Vector.t A n -> R) -> R :=
    match n with
    | O => fun f => f (Vector.nil)
    | S n' => fun f => ∑ b : A,
      sum_of_vec (fun bs => f (Vector.cons b bs))
    end.

Definition Summable_vec `{Summable A} n : Summable (Vector.t A n) :=
  sum_over (vec_elements sum_elements n).

#[export] Instance SummableOver_vec `{SummableOver R A} {n : nat}
  : SummableOver R (vec A n) := sum_by sum_of_vec (fun v => Forall SummedElement v).





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


Definition Summable_prod `{Summable A, Summable B} : Summable (A * B) :=
  sum_over (list_prod sum_elements sum_elements).

Definition Summable_sum `{Summable A, Summable B} : Summable (A + B) :=
  sum_over ((inl <$> sum_elements) ++ (inr <$> sum_elements)).

#[export] Instance SummableOver_prod
  `{SummableOver R A, SummableOver R B} : SummableOver R (A * B) :=
  sum_by (fun f => ∑ a, ∑ b, f (a, b)) (fun ab => SummedElement ab.1 /\ SummedElement ab.2).

#[export] Instance SummableOver_sum `{SR : SemiRing R rO rI radd rmul req}
  `{SummableOver R A, SummableOver R B} : SummableOver R (A + B) :=
  sum_by (fun f => radd (∑ a, f (inl a)) (∑ b, f (inr b)))
    (sum_rect (fun _ => _) SummedElement SummedElement).


Section lawful.

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


Lemma sum_of_vec_comm_1 {A} {SRA : SummableOver R A}
  `{!LawfulSummableOver R A} {n} (f : A -> vec A n -> R) :
  ∑ a, ∑ v, f a v ==
  ∑ v, ∑ a, f a v.
Proof.
  rewrite (sum_of_defn_abstract (A:=vec A n)).
  assert (subrelation eq req) by solve_proper.
  setoid_rewrite (sum_of_defn_abstract (A:=vec A n)).
  cbn.
  induction n; [done|].
  cbn.
  rewrite sum_of_comm_abstract.
  apply sum_of_ext.
  intros a Ha.
  rewrite IHn.
  done.
Qed.

Lemma sum_of_vec_comm {A} {SRA : SummableOver R A}
  `{!LawfulSummableOver R A} {n m} (f : vec A n -> vec A m -> R) :
  ∑ v, ∑ w, f v w ==
  ∑ w, ∑ v, f v w.
Proof.
  assert (Hsucc : forall {n} (f : Vector.t A (S n) -> R),  sum_of f == ∑ a, sum_of (fun v => f (Vector.cons a v))) by done.
  induction n; [done|].
  rewrite Hsucc.
  setoid_rewrite IHn.
  rewrite sum_of_vec_comm_1.
  done.
Qed.

#[global] Instance LawfulSummableOver_vec {A} {SRA : SummableOver R A}
  `{!LawfulSummableOver R A} {n : nat} :
  LawfulSummableOver R (vec A n).
Proof.
  split; [setoid_rewrite sum_of_defn_abstract; cbn..|].
  - intros f g Hfg.
    induction n.
    + cbn.
      apply Hfg.
      constructor.
    + cbn.
      apply sum_of_ext; intros a Ha.
      apply IHn.
      intros v Hv.
      apply Hfg.
      now constructor.
  - induction n; [done|].
    cbn.
    setoid_rewrite IHn.
    apply sum_of_0.
  - intros f g.
    induction n; [done|].
    cbn.
    setoid_rewrite IHn.
    rewrite sum_of_add.
    done.
  - intros f r.
    induction n; [done|].
    cbn.
    rewrite sum_of_distr_l.
    setoid_rewrite IHn.
    done.
  - intros f.
    apply sum_of_vec_comm.
Qed.

(* 
#[global] Instance LawfulSummableOver_sum `{SRA : SummableOver R A,
  SRB : SummableOver R B}
  `{!LawfulSummableOver R A, !LawfulSummableOver R B} {n : nat} :
  LawfulSummableOver R (A + B).
Proof.
  split; setoid_rewrite sum_of_defn_abstract; cbn.
  - intros f g Hfg.
    f_equiv; apply sum_of_ext; intros; apply Hfg; done.
  - rewrite 2 sum_of_0; ring.
  - intros f g.
    rewrite 2 sum_of_add.
    ring.
  - intros f r.
    rewrite <- 2 sum_of_distr_l.
    ring.
  - intros f.
    rewrite (sum_of_defn_abstract' (A:=A + B)).
    cbn.
    rewrite 4 sum_of_
    rewrite 2 sum_of_comm.
Qed.

#[global] Instance LawfulSummableOver_prod `{SRA : SummableOver R A,
  SRB : SummableOver R B}
  `{!LawfulSummableOver R A, !LawfulSummableOver R B} {n : nat} :
  LawfulSummableOver R (A * B).
Proof.
  split; setoid_rewrite sum_of_defn_abstract; cbn.
  - intros f g Hfg.
    do 2 (apply sum_of_ext; intros); apply Hfg; done.
  - setoid_rewrite sum_of_0.
    apply sum_of_0.
  - intros f g.
    setoid_rewrite sum_of_add.
    rewrite sum_of_add; done.
  - intros f r.
    rewrite sum_of_distr_l.
    setoid_rewrite sum_of_distr_l.
    done.
Qed. *)

End lawful.





Fixpoint sum_of_fin `{SR : SemiRing R rO rI radd rmul req} {n : nat}
  (f : Fin.t n -> R) : R :=
  match n, f with
  | O, _ => rO
  | S k, _ => radd (f Fin.F1) (sum_of_fin (fun fin => f (Fin.FS fin)))
  end.


Local Existing Instance fold_right_mor.



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

Context `{SRA : SummableOver R A}.

Lemma sum_of_vec_0 (f : Vector.t A 0 -> R) :
  sum_of f == f (Vector.nil).
Proof.
  done.
Qed.

Lemma sum_of_vec_1 (f : Vector.t A 1 -> R) :
  sum_of f == ∑ a, f (Vector.cons a (Vector.nil)).
Proof.
  done.
Qed.

Lemma sum_of_vec_succ {n} (f : Vector.t A (S n) -> R) :
  sum_of f == ∑ a, sum_of (fun v => f (Vector.cons a v)).
Proof.
  done.
Qed.

Lemma sum_of_vec_defn `{!LawfulSummableOver R A}
  {n} (f : Vector.t A n -> R) :
  sum_of f == sum_of_vec f.
Proof.
  induction n.
  - now rewrite sum_of_vec_0.
  - now rewrite sum_of_vec_succ; setoid_rewrite IHn.
Qed.

Lemma sum_of_vec_add `{!LawfulSummableOver R A} {n m} (f : Vector.t A (n + m) -> R) :
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


Lemma sum_of_vec_cast `{!LawfulSummableOver R A} {n m} (f : vec A n -> R) (H : m = n) :
  ∑ v : _, f v == ∑ v : vec A m, f (Vector.cast v H).
Proof.
  subst.
  apply sum_of_ext.
  intros;
  now rewrite cast_id.
Qed.


Lemma sum_of_vec_rev `{!LawfulSummableOver R A} {n} (f : vec A n -> R) :
  ∑ v : _, f v == ∑ v : _, f (Vector.rev v).
Proof.
  induction n.
  - now rewrite 2 sum_of_vec_0, Vector.rev_nil.
  - erewrite (sum_of_vec_cast f (Nat.add_comm n 1)).
    rewrite sum_of_vec_add, (sum_of_vec_add (n:=1)).
    rewrite sum_of_vec_comm.
    rewrite 2 sum_of_vec_1.
    apply sum_of_ext; intros a Ha.
    rewrite IHn.
    apply sum_of_ext; intros v Hv.
    cbn.
    rewrite vec_rev_cons_alt.
    done.
Qed.

End Vector.


Lemma sum_of_prod_defn `{SummableOver R A, SummableOver R B} (f : A * B -> R) :
  sum_of f == ∑ a, ∑ b, f (a, b).
Proof.
  done.
Qed.

Lemma sum_of_prod_defn_alt `{Summable A, Summable B} (f : A * B -> R) :
  sum_of f == sum_of' Summable_prod f.
Proof.
  rewrite sum_of_defn_abstract'.
  cbn.
  symmetry.
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

Lemma sum_of_sum_defn `{SummableOver R A, SummableOver R B} (f : A + B -> R) :
  sum_of f == (∑ a, f (inl a)) + (∑ b, f (inr b)).
Proof.
  done.
Qed.

Lemma sum_of_sum_defn_alt `{Summable A, Summable B} (f : A + B -> R) :
  sum_of f == sum_of' Summable_sum f.
Proof.
  rewrite sum_of_defn_abstract.
  unfold_sum_of.
  cbn.
  rewrite map_app, Rlist_sum_app, 2 map_map.
  reflexivity.
Qed.


End SummableInstanceUnfold.



#[export] Instance SummableOver_Prop A : SummableOver Prop A | 20 :=
  sum_by (@ex A) (λ _, True).


#[export] Instance LawfulSummableOver_Prop A : LawfulSummableOver Prop A.
Proof.
  split; unfold SummedElement; rewrite !sum_of_defn_abstract'; cbn; firstorder.
Qed.

