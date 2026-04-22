From TensorRocq Require Export AbstractReasoning.

From TensorRocq Require Import MProp.Automation.

Require Import QArith Qcanon.


#[export] Instance Qc_inhabited : Inhabited Qc := populate 0%Qc.

Declare Custom Entry print_qc.

Notation "q" := (q%Qc%Q) (only printing, q constr at level 9, in custom print_qc at level 0).

Notation "q " := (Qcmake q%Q _) (only printing, q constr at level 9, in custom print_qc at level 0).

Notation " q" := (Q2Qc q%Q) (only printing, q constr  at level 9, in custom print_qc at level 0).


Local Open Scope aprop_scope.

Definition ZX n m := AProp (fin 3 * Qc) n m.

Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 3) n m * AProp (fin 3) n m)%type}})
  (at level 70).

Notation Z n m q := (Agen (0%fin :> fin 3, q%Qc) n m) (only parsing).
Notation X n m q := (Agen (1%fin :> fin 3, q%Qc) n m) (only parsing).
Notation H n     := (Agen (2%fin :> fin 3, 0)    n n) (only parsing).

Notation "'Z' n m q" := (Agen (0%fin, q) n m) (only printing,
  n at level 9, m at level 9,
  q custom print_qc, at level 10).
Notation "'X' n m q" := (Agen (1%fin, q) n m) (only printing,
  n at level 9, m at level 9,
  q custom print_qc, at level 10).
Notation "'H' n"     := (Agen (2%fin, _) n n) (only printing,
  n at level 9, at level 10).

Inductive ZXEq : forall {n m}, relation (ZX n m) :=
  | ZXEq_Z_add_2 n m q :
    ZXEq (Z n m q) (Z n m (2 + q))
  | ZXEq_X_add_2 n m q :
    ZXEq (X n m q) (X n m (2 + q))
  | ZXEq_Z_0_id :
    ZXEq (Z 1 1 0) (id)
  | ZXEq_X_0_id :
    ZXEq (X 1 1 0) (id)
  | ZXEq_fuseZ n m o q q' :
    ZXEq (Z n m q ;' Z m o q') (Z n o (q + q'))
  | ZXEq_fuseX n m o q q' :
    ZXEq (X n m q ;' X m o q') (X n o (q + q'))
  | ZXEq_Z_colorswap n m q :
    ZXEq (Z n m q) (H n ;' X n m q ;' H m)
  | ZXEq_H_idempotent n :
    ZXEq (H n ;' H n) ([[ id n ]])
  | ZXEq_Z_add_r n m m' q q' q'' :
    ZXEq (Z n (m + m') (q + q' + q''))
         (Z n 2 q ;' Z 1 m q' * Z 1 m' q'')
  | ZXEq_Z_add_l n n' m q q' q'' :
    ZXEq (Z (n + n') m (q + q' + q''))
         (Z n 1 q * Z n' 1 q' ;' Z 2 m q'')
  | ZXEq_X_add_r n m m' q q' q'' :
    ZXEq (X n (m + m') (q + q' + q''))
         (X n 2 q ;' X 1 m q' * X 1 m' q'')
  | ZXEq_X_add_l n n' m q q' q'' :
    ZXEq (X (n + n') m (q + q' + q''))
         (X n 1 q * X n' 1 q' ;' X 2 m q'').


Definition ZX_sig : Signature bool := {|
  gens := fin 3 * Qc;
  gens_equiv := eq;
  rules n m := ZXEq
|}.

Notation "x == y" :=
  (x ≡ᵣ@{ZX_sig} y)
  (at level 70).

Lemma X_add_2 n m q : X n m q == X n m (2 + q).
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_2 n m q : Z n m q == Z n m (2 + q).
Proof. apply rules_hold; constructor. Qed.

Lemma X_id : X 1 1 0 == id.
Proof. apply rules_hold; constructor. Qed.

Lemma Z_id : Z 1 1 0 == id.
Proof. apply rules_hold; constructor. Qed.

Lemma fuseZ n m o q q' : Z n m q ;' Z m o q' == Z n o (q + q').
Proof. apply rules_hold; constructor. Qed.

Lemma colorswap n m q : Z n m q == H n ;' X n m q ;' H m.
Proof. apply rules_hold; constructor. Qed.

Lemma fuseX n m o q q' : X n m q ;' X m o q' == X n o (q + q').
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_r n m m' q q' q'' :
  Z n (m + m') (q + q' + q'') == Z n 2 q ;' Z 1 m q' * Z 1 m' q''.
Proof. apply rules_hold; constructor. Qed.

Lemma Z_add_l n n' m q q' q'' :
  Z (n + n') m (q + q' + q'') == Z n 1 q * Z n' 1 q' ;' Z 2 m q''.
Proof. apply rules_hold; constructor. Qed.

Lemma X_add_r n m m' q q' q'' :
  X n (m + m') (q + q' + q'') == X n 2 q ;' X 1 m q' * X 1 m' q''.
Proof. apply rules_hold; constructor. Qed.

Lemma X_add_l n n' m q q' q'' :
  X (n + n') m (q + q' + q'') == X n 1 q * X n' 1 q' ;' X 2 m q''.
Proof. apply rules_hold; constructor. Qed.

Example test_fuse : Z 1 2 0 * X 2 1 0 ;' Z 2 1 1 * id ==
  Z 1 1 1 * X 2 1 0.
Proof.
  srw_lhs (fuseZ 1 2 1 0 1).
  smcat.
Qed.

Definition cnot : ZX 2 2 := [[ Z 1 2 0 * id ; id * X 2 1 0 ]].

Definition zmeas (b : bool) := Z 1 0 (if b then 1%Qc else 0).
Definition zcorr (b : bool) := Z 1 1 (if b then 1%Qc else 0).
Definition xmeas (b : bool) := X 1 0 (if b then 1%Qc else 0).
Definition xcorr (b : bool) := X 1 1 (if b then 1%Qc else 0).

Lemma teleportation : forall b,
  id * X 0 1 0 ;' cnot ;' zmeas b * zcorr b == id.
Proof.
  intros [].
  - srw (Z_add_r 1 1 1 0 0 0).
    srw (fuseZ 1 1 0 0 1).
    srw <- (Z_add_r 1 0 1 0 1 0).
    srw (X_add_l 1 1 1 0 0 0).
    srw (fuseX 0 1 1 0 0).
    srw <- (X_add_l 1 0 1 0 0 0).
    srw X_id.
    srw (fuseZ 1 1 1 1 1).
    srw <- (Z_add_2 1 1 0).
    now srw Z_id.
  - srw (Z_add_r 1 1 1 0 0 0).
    srw (fuseZ 1 1 0 0 0).
    srw <- (Z_add_r 1 0 1 0 0 0).
    srw (X_add_l 1 1 1 0 0 0).
    srw (fuseX 0 1 1 0 0).
    srw <- (X_add_l 1 0 1 0 0 0).
    srw X_id.
    now repeat srw Z_id.
Qed.

Lemma test n m o α :
   X n m α * Aid m ;' Aid m * Z m o 2 ==
  Aid n * Z m o 2 ;' X n m α * Aid o.
Proof.
  psmcat.
Qed.
(*
#[global] Arguments free_monoid_meq_dec_subproof {_ _ _ _ _ _ _ _ _ _} : assert.
#[global] Arguments free_monoid_meq_dec_subproof0 {_ _ _ _ _ _ _ _ _ _ _} : assert. *)


Ltac zx_prw_lhs lem match_number :=
  wild_prw_lhs constr:(SignatureTensorLike ZX_sig)
    constr:(APROPlike_AProp (TensT:=SignatureTensorLike ZX_sig))
    open_constr:(SigTensAProp_eq_AProp_semantic_eq)
    open_constr:(AProp_semantic_eq_SigTensAProp_eq (Sig:=ZX_sig))
    lem match_number.


Ltac zx_prw_lhs' lem match_number :=
  wild_prw_lhs' constr:(SignatureTensorLike ZX_sig)
    constr:(APROPlike_AProp (TensT:=SignatureTensorLike ZX_sig))
    open_constr:(SigTensAProp_eq_AProp_semantic_eq)
    open_constr:(AProp_semantic_eq_SigTensAProp_eq (Sig:=ZX_sig))
    lem match_number.

Lemma test' n m o α β :
  Z n m α * Aid m ;' Aswap m m ;' Aid m * Z m o β ==
  Z n o (α + β) * Aid m ;' Aswap o m.
Proof.
  zx_prw_lhs' (fuseZ n m o α β) O.
    
    quote_MP_step.
    quote_MP_step.
    quote_MP_step.
    do 2 (tspecialize Hrew; [quote_MP|]).
unshelve    quote_MP.
    tspecialize Hrew.
    quote_MP.
  }
  psmcat.
Qed.
