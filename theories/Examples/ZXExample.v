Require Export FreeAProp.
Require Import Qcanon.




Local Open Scope aprop_scope.

Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 2) n m * AProp (fin 2) n m)%type}})
  (at level 70).

Notation Z n m q := (Agen ((0%fin :> fin 2, q%Qc)) n m).
Notation X n m q := (Agen ((1%fin :> fin 2, q%Qc)) n m).

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
  (at level 70, y custom aprop).

Lemma fuseZ n m o q q' : Z n m q ;' Z m o q' == Z n o (q + q').
Proof. apply rules_hold; constructor. Qed.


