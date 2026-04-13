From stdpp Require Import list. 
From TensorRocq Require Export Monoid.
From TensorRocq Require Import AbstractTensorQuote.
From TensorRocq Require Import Aux_relset.

(* FIXME: Move *)

Lemma foldr_assoc_to_unit {A} {R : relation A} `{!Equivalence R}
  (e : A) (op : A -> A -> A)
  `{opP : !Proper (R ==> R ==> R) op, ope : !LeftId R e op, opA : !Assoc R op}
  (a : A) (l : list A) :
  R (foldr op a l) (op (foldr op e l) a).
Proof.
  induction l.
  - cbn.
    now rewrite (left_id _ _).
  - cbn.
    rewrite IHl.
    apply opA.
Qed.

Lemma foldr_app_assoc {A} {R : relation A} `{!Equivalence R}
  (e : A) (op : A -> A -> A)
  `{opP : !Proper (R ==> R ==> R) op, ope : !LeftId R e op, opA : !Assoc R op}
  (l l' : list A) :
  R (foldr op e (l ++ l')) (op (foldr op e l) (foldr op e l')).
Proof.
  rewrite foldr_app.
  now apply foldr_assoc_to_unit.
Qed.




(* FIXME: Move, or maybe it exists already? *)
Inductive btree {A : Type} : Type :=
  | bnode : btree -> btree -> btree
  | bleaf : A -> btree
  | bempty : btree.
#[global] Arguments btree (A) : clear implicits.

#[export] Instance btree_empty A : Empty (btree A) := bempty.

Fixpoint btree_fold {A B} (e : B) (ofa : A -> B)
  (op : B -> B -> B) (t : btree A) : B :=
  match t with
  | bnode l r => op (btree_fold e ofa op l) (btree_fold e ofa op r)
  | bleaf a => ofa a
  | bempty => e
  end.

Fixpoint btree_elems {A} (t : btree A) : list A :=
  match t with
  | bnode l r => btree_elems l ++ btree_elems r
  | bleaf a => [ a ]
  | bempty => []
  end.

Coercion btree_elems : btree >-> list.

#[export] Instance btree_equiv A : Equiv (btree A) :=
  fun t t' => btree_elems t = btree_elems t'.



Lemma btree_fold_to_list {A B} (e : B) (ofa : A -> B)
  (op : B -> B -> B) `{R : relation B, HR : !Equivalence R}
  `{eop : !LeftId R e op, ope : !RightId R e op, opa : !Assoc R op,
  opP : !Proper (R ==> R ==> R) op}
  bw : R (btree_fold e ofa op bw) (foldr op e (ofa <$> btree_elems bw)).
Proof.
  induction bw.
  - cbn.
    rewrite fmap_app.
    rewrite (foldr_app_assoc _ _ _).
    now f_equiv.
  - cbn.
    now rewrite (right_id _ _).
  - done.
Qed.

#[export] Instance btree_fold_Proper {A B} (e : B) (ofa : A -> B)
  (op : B -> B -> B) `{R : relation B, HR : !Equivalence R}
  `{eop : !LeftId R e op, ope : !RightId R e op, opa : !Assoc R op,
  opP : !Proper (R ==> R ==> R) op} :
  Proper (equiv ==> R) (btree_fold e ofa op).
Proof.
  intros bw bw' [= Hbw].
  rewrite 2 (btree_fold_to_list _ _ _).
  now rewrite Hbw.
Qed.

#[export] Instance btree_monoid A :
  Monoid (btree A) ∅ bnode equiv.
Proof.
  split.
  - apply _.
  - intros x x' Hx y y' Hy.
    hnf.
    cbn.
    now f_equal.
  - intros x y z.
    hnf.
    cbn.
    apply app_assoc.
  - easy.
  - intros x.
    hnf.
    cbn.
    apply app_nil_r.
Qed.

#[refine] Instance btree_free_monoid A :
  FreeMonoid (btree A) A := {
  mdecomp b := b;
  mdecomp_inv a := bleaf a;
}.
Proof.
  - abstract easy.
  - abstract easy.
  - abstract easy.
  - abstract easy.
Defined.


























Class QuoteMonoidSize {M} (f : M -> nat)
  `{MD : Monoid M mO madd meq, MS : !MonoidSize f}
  (a : M) (n : nat) := {
  quote_msize : f a = n
}.

#[global] Hint Mode QuoteMonoidSize + ! + + + + ! - + : typeclass_instances.



Section BWQuotation.


#[local] Set Typeclasses Unique Instances.

Definition denote_nat_bw (l : list nat) (bw : btree (option nat)) : nat :=
  btree_fold 0 (λ k, from_option (default 0 ∘ (l !!.)) 1 k) Nat.add bw.

#[global] Instance denote_nat_bw_MonoidSize {l : list nat} :
  MonoidSize (denote_nat_bw l).
Proof.
  split.
  - apply btree_fold_Proper; apply _.
  - done.
  - done.
Qed.

#[export] Instance quote_denote_nat_bw_0 (l : list nat) :
  QuoteMonoidSize (denote_nat_bw l) bempty 0.
Proof.
  now constructor.
Qed.

#[export] Instance quote_denote_nat_bw_S (l : list nat) bw n :
  QuoteMonoidSize (denote_nat_bw l) bw n ->
  QuoteMonoidSize (denote_nat_bw l) (bnode (bleaf None) bw) (S n).
Proof.
  intros [Hbw].
  constructor.
  now rewrite <- Hbw.
Qed.

(* Small optimization *)
#[export] Instance quote_denote_nat_bw_1 (l : list nat) :
  QuoteMonoidSize (denote_nat_bw l) (bleaf None) 1.
Proof.
  now constructor.
Qed.


#[export] Instance quote_denote_nat_bw_add (l : list nat) bw bw' n m :
  QuoteMonoidSize (denote_nat_bw l) bw n ->
  QuoteMonoidSize (denote_nat_bw l) bw' m ->
  QuoteMonoidSize (denote_nat_bw l) (bnode bw bw') (n + m).
Proof.
  intros [Hbw] [Hbw'].
  constructor.
  now rewrite <- Hbw, <- Hbw'.
Qed.

(* TODO: Maybe replace with lemma and hint extern? My concern is that the
  hint extern may not do the same reduction/unification as TC generally,
  so this may be (ironically) overapplied in that case *)
#[export] Instance quote_denote_nat_bw_const (l : list nat) n k :
  IsNth n k l ->
  QuoteMonoidSize (denote_nat_bw l) (bleaf (Some k)) n | 10.
Proof.
  intros Hnth%IsNth_iff.
  constructor.
  cbn.
  now rewrite Hnth.
Qed.



End BWQuotation.