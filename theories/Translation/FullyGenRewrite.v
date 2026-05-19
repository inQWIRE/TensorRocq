(* From TensorRocq Require Import Algebra.
From TensorRocq Require Import Aux_stdpp. *)
From stdpp Require Import base option.


Notation Mor A := (A -> A -> Type).

Class MonoidalCategory (D : Mor nat)
  (eqD : forall n m, Equiv (D n m)) 
  (idD : forall n, D n n)
  (compD : forall {n m o}, D n m -> D m o -> D n o)
  (stackD : forall {n1 m1 n2 m2}, D n1 m1 -> D n2 m2 -> D (n1 + n2) (m1 + m2)) := {
  equivD {n m} :: Equivalence (≡@{D n m});
  compDProp {n m o} :: Proper (equiv ==> equiv ==> equiv) (@compD n m o);
  stackDProp {n1 m1 n2 m2} :: Proper (equiv ==> equiv ==> equiv) (@stackD n1 m1 n2 m2);
}.

#[global] Hint Mode MonoidalCategory + - - - - : typeclass_instances.

Inductive Drewrite `{MCD : !MonoidalCategory D eqD idD compD stackD} 
  {n m} (Targ : D n m) {i j} (LHS : D i j) : Type :=
  | drewrite_intro {k} (C1 : D n (k + i)) (C2 : D (k + j) m) : 
    Targ ≡ compD _ _ _ (compD _ _ _ C1 (stackD _ _ _ _ (idD k) LHS)) C2 ->
    Drewrite Targ LHS.


Class TestableEquiv (A : Type) {eqA : Equiv A} := {
  eqTest : A -> A -> bool;
  eqTestCorrect (a b : A) : eqTest a b -> a ≡ b;
}.

Definition rewriteFunc (D : Mor nat) 
  `{MCD : !MonoidalCategory D eqD idD compD stackD} :=
  forall n m (Targ : D n m) i j (LHS : D i j), option (Drewrite Targ LHS).

Definition rewriteFunc_of_testable_unverified 
  `{MCD : !MonoidalCategory D eqD idD compD stackD}
  {EQTD : forall n m, TestableEquiv (D n m)}
  (may_rewrite : forall n m (Targ : D n m) i j (LHS : D i j), 
    option {k & prod (D n (k + i)) (D (k + j) m)}) : 
    rewriteFunc D :=
  fun n m Targ i j LHS => 
  '(existT k (C1, C2)) ← may_rewrite n m Targ i j LHS;
  Heq' ← guard (eqTest Targ (compD _ _ _ (compD _ _ _ C1 (stackD _ _ _ _ (idD k) LHS)) C2));
  Some (drewrite_intro Targ LHS C1 C2 (eqTestCorrect _ _ Heq')).