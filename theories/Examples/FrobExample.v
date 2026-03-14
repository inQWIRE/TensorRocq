Require Export FreeAProp.


Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 4) n m * AProp (fin 4) n m)%type}})
  (at level 70).

Notation m := (Agen (0%fin :> fin 4) 2 1) (only parsing).
Notation u := (Agen (1%fin :> fin 4) 0 1) (only parsing).
Notation n := (Agen (2%fin :> fin 4) 1 2) (only parsing).
Notation v := (Agen (3%fin :> fin 4) 1 0) (only parsing).


Definition Frob : Signature bool := {|
  gens := fin 4;
  gens_equiv := eq;
  (* gen_arity := ([# (2,1); (0,1); (1,2); (1,0)] !!!.); *)
  rules := rules_of_rule_list [

(* (m, u) forms a monoid *)
(* rule assoc : *) m * Aid 1 ;' m === Aid 1 * m ;' m ;
(* rule unitL : *) u * Aid 1 ;' m === Aid 1 ;
(* rule unitR : *) Aid 1 * u ;' m === Aid 1 ;

(* (n, v) forms a comonoid *)
(* rule coassoc : *) n ;' n * Aid 1 === n ;' Aid 1 * n ;
(* rule counitL : *) n ;' v * Aid 1 === Aid 1 ;
(* rule counitR : *) n ;' Aid 1 * v === Aid 1 ;

(* there are many equivalent formulations of the Frobenius condition. Here's one: *)
(* rule frob : *) n * Aid 1 ;' Aid 1 * m === Aid 1 * n ;' m * Aid 1

     ];
|}.


Notation "'m'" := (@Agen _ 0%fin 2 1) (only printing).
Notation "'u'" := (@Agen _ 1%fin 0 1) (only printing).
Notation "'n'" := (@Agen _ 2%fin 1 2) (only printing).
Notation "'v'" := (@Agen _ 3%fin 1 0) (only printing).

Notation "x == y" :=
  (x ≡ᵣ@{Frob} y)
  (at level 70).

(* (m, u) forms a monoid *)
Lemma assoc : m * Aid 1 ;' m == Aid 1 * m ;' m.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma unitL : u * Aid 1 ;' m == Aid 1.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma unitR : Aid 1 * u ;' m == Aid 1.
Proof. apply rules_hold. repeat constructor. Qed.

(* (n, v) forms a comonoid *)
Lemma coassoc : n ;' n * Aid 1 == n ;' Aid 1 * n.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma counitL : n ;' v * Aid 1 == Aid 1.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma counitR : n ;' Aid 1 * v == Aid 1.
Proof. apply rules_hold. repeat constructor. Qed.

(* there are many equivalent formulations of the Frobenius condition. Here's one: *)
Lemma frob : n * Aid 1 ;' Aid 1 * m == Aid 1 * n ;' m * Aid 1.
Proof. apply rules_hold. repeat constructor. Qed.

(* The rule above is equivalent to the slightly more familiar pair of rules:
  frobL : n * id ; id * m = m ; n
  frobR : id * n ; m * id = m ; n
If m and n were both commutative, one of these would imply the other, and either
would imply "frob". However, for non-commutative Frobenius algebras, we need them
both. *)

Lemma frobL : n * Aid 1 ;' Aid 1 * m == m ;' n.
Proof.
  transitivity (u * n * Aid 1 ;' m * m)%aprop;
  [srw unitL; smcat|].
  srw <- frob.
  srw assoc.
  srw frob.
  srw unitL.
  smcat.
Qed.

Lemma frobR : Aid 1 * n ;' m * Aid 1 == m ;' n.
Proof.
  srw <- frob.
  srw frobL.
  smcat.
Qed.

Definition cup : AProp _ _ _ := u ;' n.
Definition cap : AProp _ _ _ := m ;' v.

Lemma cap_assoc : m * Aid 1 ;' cap == Aid 1 * m ;' cap.
Proof.
  unfold cap.
  srw assoc.
  smcat.
Qed.


Lemma cup_assoc : cup ;' n * Aid 1 == cup ;' Aid 1 * n.
Proof.
  unfold cup.
  srw coassoc.
  smcat.
Qed.

Lemma yankL : cup * Aid 1 ;' Aid 1 * cap == Aid 1.
Proof.
  unfold cup, cap.
  srw frobL.
  srw unitL.
  srw counitR.
  smcat.
Qed.

Lemma yankR : Aid 1 * cup ;' cap * Aid 1 == Aid 1.
Proof.
  unfold cup, cap.
  srw frobR.
  srw unitR.
  srw counitL.
  smcat.
Qed.

Lemma m_cupL : cup * Aid 1 ;' Aid 1 * m == n.
Proof.
  unfold cup.
  srw frob.
  srw unitL.
  smcat.
Qed.

Lemma m_cupR : Aid 1 * cup ;' m * Aid 1 == n.
Proof.
  unfold cup.
  srw <- frob.
  srw unitR.
  smcat.
Qed.

Lemma n_capL : Aid 1 * n ;' cap * Aid 1 == m.
Proof.
  unfold cap.
  srw <- frob.
  srw counitL.
  smcat.
Qed.

Lemma n_capR : n * id ;' id * cap == m.
Proof.
  unfold cap.
  srw frob.
  srw counitR.
  smcat.
Qed.

Definition m2 : AProp _ _ _ := id * Aswap 1 1 * id ;' m * m.
Definition u2 : AProp _ _ _ := u * u.

Definition n2 : AProp _ _ _ := n * n ;' id * Aswap 1 1 * id.
Definition v2 : AProp _ _ _ := v * v.

Lemma assoc2 : m2 * Aid 2 ;' m2 ==
  Aid 2 * m2 ;' m2.
Proof.
  unfold m2.
  srw assoc.
  srw assoc.
  smcat.
Qed.

Lemma unitL2 : u2 * Aid 2 ;' m2 == Aid 2.
Proof.
  srw unitL.
  srw unitL.
  smcat.
Qed.

Lemma unitR2 : Aid 2 * u2 ;' m2 == Aid 2.
Proof.
  srw unitR.
  srw unitR.
  smcat.
Qed.

Lemma coassoc2 : n2 ;' n2 * Aid 2 ==
  n2 ;' Aid 2 * n2.
Proof.
  unfold n2.
  srw coassoc.
  srw coassoc.
  smcat.
Qed.

Lemma counitL2 : n2 ;' v2 * Aid 2 == Aid 2.
Proof.
  srw counitL.
  srw counitL.
  smcat.
Qed.

Lemma counitR2 : n2 ;' Aid 2 * v2 == Aid 2.
Proof.
  srw counitR.
  srw counitR.
  smcat.
Qed.

Lemma frob2 : n2 * Aid 2 ;' Aid 2 * m2 == Aid 2 * n2 ;' m2 * Aid 2.
Proof.
  srw frob.
  srw frob.
  smcat.
Qed.
