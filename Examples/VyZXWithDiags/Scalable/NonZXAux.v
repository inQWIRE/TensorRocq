From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.

From TensorRocqEx Require Import VyZXExample_withdiags.


Import ZXsymm ZXauto ZXfrob.


Import ZXmsymm.
  Import SizedProQuote.
  Import SizedRewriting SizedProLike.
  Import SizedPropsGraphs PropsGraphs.

Import BW.

Import ComposeRules.

Open Scope nat_scope.

Ltac visualize_flag ::= fail.


Module GeneratorNotations.

(* Notation "'const' a" := (inl (Some (inr a))) (a at level 9, only printing, at level 1).

Notation "'Z' a" := (inl (Some (inl (false, a)))) (a at level 9, only printing, at level 1).
Notation "'Z'" := (inl (Some (inl (false, IZR 0)))) (only printing, at level 1).

Notation "'X' a" := (inl (Some (inl (true, a)))) (a at level 9, only printing, at level 1).
Notation "'X'" := (inl (Some (inl (true, IZR 0)))) (only printing, at level 1).

Notation "'H'" := ((inl None :> ZXDVERT)) (only printing, at level 1).

Notation "'[' zx ']'" := ((inr (existT _ zx%ZX) :> ZXDVERT)) (only printing, at level 0).
Notation "'[' zx ']'" := ((inr (bundleDiagram zx%ZX) :> ZXDVERT)) (only printing, at level 0). *)

Export GeneratorNotations.

Notation "n ≃ m" := (cast n%nat m%nat _ _ (n_wire _)) (only printing, at level 70).

End GeneratorNotations.

Import GeneratorNotations.

(* FIXME: Move *)
Hint Opaque zx_mid_comm zx_mul_S_r zx_mul_comm : typeclass_instances.




Module prf_notations.

(* FIXME: Move *)
Notation mul_1_r := (Nat.mul_1_r _).
Notation mul_1_r' := (eq_sym (Nat.mul_1_r _)).
Notation mul_1_l := (Nat.mul_1_l _).
Notation mul_1_l' := (eq_sym (Nat.mul_1_l _)).

(* FIXME: Move  *)
Notation mul_add_distr_l := (Nat.mul_add_distr_l _ _ _).
Notation mul_add_distr_l' := (eq_sym (Nat.mul_add_distr_l _ _ _)).
Notation mul_add_distr_r := (Nat.mul_add_distr_r _ _ _).
Notation mul_add_distr_r' := (eq_sym (Nat.mul_add_distr_r _ _ _)).

(* FIXME: Move *)
Notation mul_0_r := (Nat.mul_0_r _).
Notation mul_0_r' := (eq_sym (Nat.mul_0_r _)).
Notation mul_0_l := (Nat.mul_0_l _).
Notation mul_0_l' := (eq_sym (Nat.mul_0_l _)).
Notation add_0_r := (Nat.add_0_r _).
Notation add_0_r' := (eq_sym (Nat.add_0_r _)).
Notation add_0_l := (Nat.add_0_l _).
Notation add_0_l' := (eq_sym (Nat.add_0_l _)).

Notation add_assoc := (Nat.add_assoc _ _ _).
Notation add_assoc' := (eq_sym (Nat.add_assoc _ _ _)).
Notation mul_assoc := (Nat.mul_assoc _ _ _).
Notation mul_assoc' := (eq_sym (Nat.mul_assoc _ _ _)).

Notation add_comm := (Nat.add_comm _ _).
Notation add_comm' := (eq_sym (Nat.add_comm _ _)).

Notation mul_comm := (Nat.mul_comm _ _).
Notation mul_comm' := (eq_sym (Nat.mul_comm _ _)).

Notation twice_double := (eq_sym (Nat.double_twice _) : 2 * _ = _ + _).
Notation twice_double_r := (eq_sym (Nat.double_twice _) : _ * 2 = _ + _).

Notation double_twice := ((Nat.double_twice _) : _ + _ = 2 * _).
Notation double_twice_r := ((Nat.double_twice _) : _ + _ = _ * 2).


End prf_notations.

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




Lemma btree_size_const_1 {A} {n : btree A} :
  btree_size (λ _, 1) n = bsize n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma bsize_eq_path {A n n'} (p : @bpath A n n') : bsize n = bsize n'.
Proof.
  rewrite <- 2 btree_size_const_1.
  apply btree_size_eq_path.
  done.
Qed.