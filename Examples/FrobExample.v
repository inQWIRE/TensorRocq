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
  rules := rules_of_rule_list [

(* (m, u) forms a monoid *)
(* rule assoc : *) m * id ;' m === id * m ;' m ;
(* rule unitL : *) u * id ;' m === id ;
(* rule unitR : *) id * u ;' m === id ;

(* (n, v) forms a comonoid *)
(* rule coassoc : *) n ;' n * id === n ;' id * n ;
(* rule counitL : *) n ;' v * id === id ;
(* rule counitR : *) n ;' id * v === id ;

(* there are many equivalent formulations of the Frobenius condition. Here's one: *)
(* rule frob : *) n * id ;' id * m === id * n ;' m * id

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
Lemma assoc : m * id ;' m == id * m ;' m.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma unitL : u * id ;' m == id.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma unitR : id * u ;' m == id.
Proof. apply rules_hold. repeat constructor. Qed.

(* (n, v) forms a comonoid *)
Lemma coassoc : n ;' n * id == n ;' id * n.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma counitL : n ;' v * id == id.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma counitR : n ;' id * v == id.
Proof. apply rules_hold. repeat constructor. Qed.

Lemma frob : n * id ;' id * m == id * n ;' m * id.
Proof. apply rules_hold. repeat constructor. Qed.

(* The rule above is equivalent to the slightly more familiar pair of rules:
  frobL : n * id ; id * m = m ; n
  frobR : id * n ; m * id = m ; n
If m and n were both commutative, one of these would imply the other, and either
would imply "frob". However, for non-commutative Frobenius algebras, we need them
both. *)

Lemma frobL : n * id ;' id * m == m ;' n.
Proof.
  transitivity (u * n * id ;' m * m)%aprop; 
  [srw unitL; smcat|].
  (* u * n * [[ id ]];' m * m == m;' n *)
  srw <- frob.
  (* u * [[ id 2 ]];' Aswap 2 1;' [[ id ]] * (n * [[ id ]];' [[ id ]] * m);' (Aswap 2 1;' m * [[ id ]];' sw) == m;' n *)
  srw assoc.
  (* u * [[ id 2 ]];' n * [[ id 2 ]];' [[ id ]] * ([[ id ]] * m;' m) ==
m;' n *)
  srw frob.
  (* m * u;' sw;' ([[ id ]] * n;' m * [[ id ]]) == m;' n *)
  srw unitL.
  (* m;' (n;' sw);' sw == m;' n *)
  smcat.
Qed.

Lemma frobR : Aid 1 * n ;' m * Aid 1 == m ;' n.
Proof.
  srw <- frob.
  (* n * [[ id ]];' [[ id ]] * m == m;' n *)
  srw frobL.
  (* m;' n == m;' n *)
  smcat.
Qed.

Definition cup : AProp _ _ _ := u ;' n.
Definition cap : AProp _ _ _ := m ;' v.

Lemma cap_assoc : m * Aid 1 ;' cap == Aid 1 * m ;' cap.
Proof.
  unfold cap.
  (* m * [[ id ]];' (m;' v) == [[ id ]] * m;' (m;' v) *)
  srw assoc.
  (* [[ id ]] * m;' m;' v == [[ id ]] * m;' (m;' v) *)
  smcat.
Qed.


Lemma cup_assoc : cup ;' n * Aid 1 == cup ;' Aid 1 * n.
Proof.
  unfold cup. 
  (* u;' n;' n * [[ id ]] == u;' n;' [[ id ]] * n *)
  srw coassoc. 
  (* u;' (n;' [[ id ]] * n) == u;' n;' [[ id ]] * n *)
  smcat.
Qed.

Lemma yankL : cup * Aid 1 ;' Aid 1 * cap == Aid 1.
Proof.
  unfold cup, cap.
  (* (u;' n) * [[ id ]];' [[ id ]] * (m;' v) == [[ id ]] *)
  srw frobL.
  (* u * [[ id ]];' (m;' n);' (sw;' v * [[ id ]]) == [[ id ]] *)
  srw unitL.
  (* n;' (sw;' v * [[ id ]]) == [[ id ]] *)
  srw counitR.
  (* [[ id ]] == [[ id ]] *)
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
