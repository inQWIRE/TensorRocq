From TensorRocq Require Export FreeAProp.

Local Open Scope aprop_scope.

Notation "x === y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) :
    {n & {m & (AProp (fin 6) n m * AProp (fin 6) n m)%type}})
  (at level 70).

Notation m := (Agen (0%fin :> fin 6) 2 1) (only parsing).
Notation u := (Agen (1%fin :> fin 6) 0 1) (only parsing).
Notation n := (Agen (2%fin :> fin 6) 1 2) (only parsing).
Notation v := (Agen (3%fin :> fin 6) 1 0) (only parsing).
Notation s := (Agen (4%fin :> fin 6) 1 1) (only parsing).
Notation sp := (Agen (5%fin :> fin 6) 1 1) (only parsing).

Definition Hopf : Signature bool := {|
  gens := fin 6;
  gens_equiv := eq;
  rules := rules_of_rule_list [

(* (m, u) forms a monoid *)
(* rule assoc : *) m * Aid 1 ;' m === Aid 1 * m ;' m ;
(* rule unitL : *) u * Aid 1 ;' m === Aid 1 ;
(* rule unitR : *) Aid 1 * u ;' m === Aid 1 ;

(* (n, v) forms a comonoid *)
(* rule coassoc : *) n ;' n * Aid 1 === n ;' Aid 1 * n ;
(* rule counitL : *) n ;' v * Aid 1 === Aid 1 ;
(* rule counitR : *) n ;' Aid 1 * v === Aid 1 ;

(* # the bialgebra laws *)
(* rule bialg : *) m ;' n === n * n ;' Aid 1 * sw [1;0] * Aid 1 ;' m * m ;
(* rule ucp : *) u ;' n === u * u ;
(* rule vcp : *) m ;' v === v * v ;
(* rule uv : *) u ;' v === Aid 0 ;

(* # the antipode laws *)
(* rule antiL : *) n ;' s * Aid 1 ;' m === v ;' u ;
(* rule antiR : *) n ;' Aid 1 * s ;' m === v ;' u
     ];
|}.


Notation "'m'" := (@Agen _ 0%fin 2 1) (only printing).
Notation "'u'" := (@Agen _ 1%fin 0 1) (only printing).
Notation "'n'" := (@Agen _ 2%fin 1 2) (only printing).
Notation "'v'" := (@Agen _ 3%fin 1 0) (only printing).
Notation "'s'" := (@Agen _ 4%fin 1 1) (only printing).
Notation "'sp'" := (@Agen _ 5%fin 1 1) (only printing).


Notation "x == y" :=
  (x ≡ᵣ@{Hopf} y)
  (at level 70, y custom aprop).

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


(* # the bialgebra laws *)
Lemma bialg : m ;' n == n * n ;' Aid 1 * sw [1;0] * Aid 1 ;' m * m.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma ucp : u ;' n == u * u.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma vcp : m ;' v == v * v.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma uv : u ;' v == Aid 0.
Proof. apply rules_hold. repeat constructor. Qed.

(* # the antipode laws *)
Lemma antiL : n ;' s * Aid 1 ;' m == v ;' u.
Proof. apply rules_hold. repeat constructor. Qed.
Lemma antiR : n ;' Aid 1 * s ;' m == v ;' u.
Proof. apply rules_hold. repeat constructor. Qed.

Definition m2 : AProp _ _ _ := [[id * Aswap 1 1 * id ;' m * m]].
Definition u2 : AProp _ _ _ := u * u.
Definition n2 : AProp _ _ _ := [[n * n ;' id * Aswap 1 1 * id]].
Definition v2 : AProp _ _ _ := v * v.
Definition s2 : AProp _ _ _ := s * s.


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

Lemma bialg2 : m2 ;' n2 ==
  n2 * n2 ;' id * id * sw[2; 3; 0; 1] * id * id ;' m2 * m2.
Proof.
  srw bialg.
  srw bialg.
  smcat.
Qed.

Lemma ucp2 : u2 ;' n2 == u2 * u2.
Proof.
  srw ucp.
  srw ucp.
  smcat.
Qed.

Lemma vcp2 : m2 ;' v2 == v2 * v2.
Proof.
  srw vcp.
  srw vcp.
  smcat.
Qed.

Lemma uv2 : u2 ;' v2 == Aid 0.
Proof.
  srw uv.
  srw uv.
  smcat.
Qed.

Lemma antiL2 : [[n2 ;' s2 * id * id ;' m2]] ==
  v2 ;' u2.
Proof.
  srw antiL.
  srw antiL.
  smcat.
Qed.

Lemma antiR2 : [[n2 ;' id * id * s2 ;' m2]] == v2 * u2.
Proof.
  srw antiR.
  srw antiR.
  smcat.
Qed.

Definition m3 := sw[0;3;1;4;2;5] ;' m * m * m.
Definition u3 := u * u * u.

Lemma assoc3 : m3 * Aid 3 ;' m3 == Aid 3 * m3 ;' m3.
Proof.
  srw assoc.
  srw assoc.
  srw assoc.
  smcat.
Qed.

Lemma unitL3 : u3 * Aid 3 ;' m3 == Aid 3.
Proof.
  srw unitL2.
  srw unitL.
  smcat.
Qed.

Lemma unitR3 : Aid 3 * u3 ;' m3 == Aid 3.
Proof.
  srw unitR2.
  srw unitR.
  smcat.
Qed.


(* #########################
# The antipode is unique
######################### *)

Lemma sp_is_s : forall
  (antiLp : n ;' sp * id ;' m == v ;' u)
  (antiRp : n ;' id * sp ;' m = v ;' u),
  sp == s.
Proof.
  intros antiLp antiRp.
  transitivity (sp * u ;' m); [srw unitR; smcat|].
  transitivity (n ;' id * v ;' sp * u ;' m); [srw counitR; smcat|].
  srw <- antiR.
  srw <- coassoc.
  srw <- assoc.
  srw antiLp.
  srw counitL.
  srw unitL.
  smcat.
Qed.


(* #######################################
# The antipode is an anti-homomorphism
####################################### *)

Definition a1 := m ;' s.
Definition a2 := sw[1;0] ;' s * s ;' m.

(* # show a1 is a left inverse of "m" w.r.t. convolution *)
Lemma anti_mh_lem1 : n2 ;' a1 * m ;' m ==
  u * v * v.
Proof.
  srw <- bialg.
  srw antiL.
  srw vcp.
  smcat.
Qed.


(* # show a2 is a right inverse of "m" w.r.t. convolution *)
Lemma anti_hm_lem2 : n2 ;' m * a2 ;' m == u * v * v.
Proof.
  srw assoc.
  srw_lhs <- assoc at 1.
  srw antiR.
  srw unitL.
  srw antiR.
  smcat.
Qed.

(* # ...hence a1 = a2 *)
Lemma s_anti_hm : m ;' s == s * s ;' sw[1;0] ;' m.
Proof.
  transitivity (u * a1 ;' sw[1;0] ;' m); [srw unitR; smcat|].
  transitivity (u * n2 ;' id * a1 * v * v ;' sw[1;0] ;' m); [srw counitR2; smcat|].
  srw <- anti_hm_lem2.
  srw <- coassoc2.
  srw <- assoc.
  srw anti_mh_lem1.
  srw unitL.
  srw counitL2.
  smcat.
Qed.

(* # This implies that the antipode squared is a homomorphism: *)
Definition ss := s ;' s.

Lemma s2_hm : m ;' ss == ss * ss ;' m.
Proof.
  srw s_anti_hm.
  srw s_anti_hm.
  smcat.
Qed.
