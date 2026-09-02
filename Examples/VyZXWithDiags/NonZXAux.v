From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocq Require Import BW.

From stdpp Require Import tactics.

Open Scope nat_scope.


Module GeneratorNotations.

(* Notation "'const' a" := (inl (Some (inr a))) (a at level 9, only printing, at level 1).

Notation "'Z' a" := (inl (Some (inl (false, a)))) (a at level 9, only printing, at level 1).
Notation "'Z'" := (inl (Some (inl (false, IZR 0)))) (only printing, at level 1).

Notation "'X' a" := (inl (Some (inl (true, a)))) (a at level 9, only printing, at level 1).
Notation "'X'" := (inl (Some (inl (true, IZR 0)))) (only printing, at level 1).

Notation "'H'" := ((inl None :> ZXDVERT)) (only printing, at level 1).

Notation "'[' zx ']'" := ((inr (existT _ zx%ZX) :> ZXDVERT)) (only printing, at level 0).
Notation "'[' zx ']'" := ((inr (bundleDiagram zx%ZX) :> ZXDVERT)) (only printing, at level 0). *)

(* Export GeneratorNotations. *)

Notation "n ≃ m" := (cast n%nat m%nat _ _ (n_wire _)) (only printing, at level 70).

End GeneratorNotations.

Import GeneratorNotations.





Import prf_notations.



(* FIXME: Move *)
Lemma div_sub_r a b c : (a - b * c) / c = a / c - b.
Proof.
  destruct_decide (decide (a <= b * c)) as Habc.
  - replace (a - _) with 0 by lia.
    rewrite Nat.Div0.div_0_l.
    symmetry.
    enough (a / c <= b) by lia.
    apply Nat.Div0.div_le_upper_bound.
    lia.
  - replace (a / c) with (((a - b * c) + b * c) / c) by (f_equal; lia).
    destruct_decide (decide (c = 0)); [subst; now rewrite 2 Nat.div_0_r; lia|].
    rewrite Nat.div_add by done.
    lia.
Qed.

(* FIXME: Move, and use! *)
Lemma show_div_eq c a b : b * c <= a < b * S c ->
  a / b = c.
Proof.
  intros Heq; apply Kronecker.div_eq_iff; lia.
Qed.


Lemma tensor_perms_swap_idn k : tensor_perms 2 k swap_2_perm idn = big_swap_perm k k.
Proof.
  eq_by_WF_perm_eq (k + k).
  rewrite big_swap_perm_defn.
  intros i Hi.
  rewrite tensor_perms_defn by lia.
  bdestruct_one.
  - rewrite Nat.mod_small, Nat.div_small by lia.
    cbn; lia.
  - replace (i / k) with 1.
    + cbn.
      rewrite mod_n_to_2n by lia.
      lia.
    + symmetry.
      apply Kronecker.div_eq_iff; lia.
Qed.





(* FIXME: Move??? *)
Lemma Cpow_inv c n :
  ((/ c) ^ n = / c ^ n)%C.
Proof.
  induction n; [lca|].
  cbn.
  rewrite Cinv_mult_distr.
  rewrite IHn.
  done.
Qed.
Lemma Cpow_1_r c : (c ^ 1 = c)%C.
Proof.
  lca.
Qed.



From TensorRocq Require Import BW BWSized.
