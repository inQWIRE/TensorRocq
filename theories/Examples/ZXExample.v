Require Export FreeAProp.
Require Import QArith Qcanon.


#[export] Instance Qc_inhabited : Inhabited Qc := populate 0%Qc.

Declare Custom Entry print_qc.

Notation "q" := (q) (only printing, q constr, in custom print_qc at level 0).

Notation "q " := (Qcmake q%Q _) (only printing, q constr, in custom print_qc at level 0).

Notation " q" := (Q2Qc q%Q) (only printing, q constr, in custom print_qc at level 0).


Local Open Scope aprop_scope.

Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 2) n m * AProp (fin 2) n m)%type}})
  (at level 70).

Notation Z n m q := (Agen (0%fin :> fin 2, q%Qc) n m) (only parsing).
Notation X n m q := (Agen (1%fin :> fin 2, q%Qc) n m) (only parsing).

Notation "'Z' n m q" := (Agen (0%fin, q) n m) (only printing, 
  q custom print_qc, at level 10).
Notation "'X' n m q" := (Agen (1%fin, q) n m) (only printing, 
  q custom print_qc, at level 10).

Inductive ZXEq : forall {n m}, relation (AProp (fin 2 * Qc) n m) :=
  | ZXEq_fuseZ n m o q q' : 
    ZXEq (Z n m q ;' Z m o q') (Z n o (q + q'))
  | ZXEq_fuseX n m o q q' : 
    ZXEq (X n m q ;' X m o q') (X n o (q + q')).

Definition ZX : Signature bool := {|
  gens := fin 2 * Qc;
  rules n m := ZXEq
|}.

Notation "x == y" :=
  (x ≡ᵣ@{ZX} y)
  (at level 70).

Lemma fuseZ n m o q q' : Z n m q ;' Z m o q' == Z n o (q + q').
Proof. apply rules_hold; constructor. Qed.



Example test_fuse : Z 1 2 0 * X 2 1 0 ;' Z 2 1 1 * id == 
  Z 1 1 1 * X 2 1 0.
Proof.
  srw_lhs (fuseZ 1 2 1 0 1).
  smcat.
Qed.

