From TensorRocq Require Import Tensor.Definitions.
From stdpp Require Import base vector.
From TensorRocq Require Import Aux_stdpp.

Definition Rel A n m := vec A n -> vec A m -> Prop.
#[export] Instance Rel_equiv A n m : Equiv (Rel A n m) :=
  fun R S => ∀ v w, R v w <-> S v w.
#[export] Instance Rel_equivalence A n m : Equivalence (≡@{Rel A n m}) :=
  (_ : Equivalence (pointwise_relation _ (pointwise_relation _ iff))).


Definition id_rel {A} (n : nat) : Rel A n n := eq.
Definition compose_rel {A} {n m o}
  (R : Rel A n m) (S : Rel A m o) : Rel A n o :=
  λ u w, ∃ v, R u v /\ S v w.
Definition stack_rel {A} {n m n' m'}
  (R : Rel A n m) (R' : Rel A n' m') : Rel A (n + n') (m + m') :=
  fun v w => R (vsplitl v) (vsplitl w) /\ R' (vsplitr v) (vsplitr w).
Definition rel_of_tensor {A n m} (t : @Tensor Prop n m A) : Rel A n m := t.
Definition swap_rel {A} (n m : nat) : Rel A (n + m) (m + n) :=
  fun v w =>
  v = vsplitr w +++ vsplitl w.
Definition transpose_rel {A n m} (R : Rel A n m) : Rel A m n :=
  fun v w => R w v.
Definition cup_rel {A} (n : nat) : Rel A 0 (n + n) :=
  fun _ v => vsplitl v = vsplitr v.
Definition cap_rel {A} (n : nat) : Rel A (n + n) 0 :=
  fun v _ => vsplitl v = vsplitr v.
Definition join_rel_stack_1_tl_tr {A} {n m} (R : Rel A (S n) (S m)) : Rel A n m :=
  fun v w => 
  exists a, R (a ::: v) (a ::: w).
Definition swapped_stack_rel {A} {n m n' m'} (R : Rel A n m) (R' : Rel A n' m') : 
  Rel A (n' + n) (m + m') :=
  fun v w => 
  R (vsplitr v) (vsplitl w) /\ R' (vsplitl v) (vsplitr w).
Definition permute_rel {A} {n m n' m'} (fl : fin n -> fin n') 
  (fr : fin m -> fin m') (R : Rel A n m) : Rel A n' m' :=
  fun v w => R (permute_vec fl v) (permute_vec fr w).

#[global] Arguments join_rel_stack_1_tl_tr {_ _ _} _   _ _ / : assert.
#[global] Arguments swapped_stack_rel {_ _ _ _ _} _ _   _ _ / : assert.
#[global] Arguments stack_rel {_ _ _ _ _} _ _   _ _ / : assert.
#[global] Arguments permute_rel {_ _ _ _ _} _ _ _  _ _ / : assert.


#[export] Instance swapped_stack_rel_mor {A n m n' m'} : 
  Proper (equiv ==> equiv ==> equiv) (@swapped_stack_rel A n m n' m').
Proof.
  intros R R' HR B B' HB v w.
  cbn.
  f_equiv; auto.
Qed.
#[export] Instance stack_rel_mor {A n m n' m'} : 
  Proper (equiv ==> equiv ==> equiv) (@stack_rel A n m n' m').
Proof.
  intros R R' HR B B' HB v w.
  cbn.
  f_equiv; auto.
Qed.

Definition DimensionlessRel A := forall n m, Rel A n m.
#[export] Instance DimensionlessRel_equiv A : Equiv (DimensionlessRel A) :=
  fun A B => ∀ n m, A n m ≡ B n m.
#[export] Instance DimensionlessRel_equivalence A : Equivalence (≡@{DimensionlessRel A}).
Proof.
  split.
  - intros M n m; done.
  - intros M N n m; now symmetry.
  - intros B C D Hbc Hcd n m.
    etransitivity; eauto.
Qed.