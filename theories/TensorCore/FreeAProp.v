Require Export AProp FreeSemiRing.

(* FIXME: Move *)
#[export] Instance nat_SemiRing : SemiRing nat 0 1 Nat.add Nat.mul eq.
Proof.
  do 2 constructor; repeat (hnf; intros); lia.
Qed.



Record Signature {A : Type} `{SA : Summable A, EqA : EqDecision A} := {
  gens : nat;
  gen_arity : vec (nat * nat) gens;
  rules : list ({n & {m & (AProp (fin gens) n m * AProp (fin gens) n m)%type}});
}.

#[global] Arguments Signature _ {_ _}.


Inductive SigTens `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) : Type :=
  | SigTensApp (f : fin Sig.(gens)) 
    (v : vec A (Sig.(gen_arity) !!! f).1) 
    (w : vec A (Sig.(gen_arity) !!! f).2) : SigTens Sig.

#[export] Instance Sig_fin_equiv `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) : Equiv (fin Sig.(gens)) := eq.

Definition SignatureTensorLike_base `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) : TensorLike (FreeSemiRing nat (SigTens Sig))
    (SR:=FSR_SR _) A 
    (fin Sig.(gens)) := {|
  interpretTensor f := 
    tensor_to_dimensionless (fun v w => FSR_mono _ (SigTensApp Sig f v w));
|}.

Inductive APropEqRel `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) {n m} (lhs rhs : AProp (fin Sig.(gens)) n m) :
  relation (FreeSemiRing nat (SigTens Sig)) :=
  | APropEqRelAt (v : vec A n) (w : vec A m) : 
    APropEqRel Sig lhs rhs 
      (AProp_semantics (TensT:=SignatureTensorLike_base Sig) lhs v w)
      (AProp_semantics (TensT:=SignatureTensorLike_base Sig) rhs v w).

Inductive SigTensRel `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) : relation (FreeSemiRing nat (SigTens Sig)) := 
  | SigTensRelIn {n m} (lhs rhs : AProp (fin Sig.(gens)) n m) :
    existT n (existT m (lhs, rhs)) ∈ Sig.(rules) ->
    forall x y,
    APropEqRel Sig lhs rhs x y -> SigTensRel Sig x y.


#[export] Instance SignatureTensorLike `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) : TensorLike (FreeSemiRing nat (SigTens Sig))
    (SR:=FSR_SR_eqg nat (SigTensRel Sig)) A 
    (fin Sig.(gens)) := {|
  interpretTensor f := 
    tensor_to_dimensionless (fun v w => FSR_mono _ (SigTensApp Sig f v w));
|}.

Definition SigTensAProp_eq `{SA : Summable A, EqA : EqDecision A} 
  (Sig : Signature A) {n m} : relation (AProp (fin Sig.(gens)) n m) :=
  fun d d' =>
  AProp_semantics (TensT:=SignatureTensorLike Sig) d ≡
  AProp_semantics (TensT:=SignatureTensorLike Sig) d'.

(* FIXME: Move *)
Declare Scope aprop_scope.
Delimit Scope aprop_scope with aprop.
Bind Scope aprop_scope with AProp.

Notation "x * y" := (Astack x%aprop y%aprop) : aprop_scope.

Notation "x ;' y" := (Acompose x%aprop y%aprop) 
  (at level 50, left associativity) : aprop_scope.


Notation "d  '≡ᵣ@{' Sig '}'  d'" := (SigTensAProp_eq Sig d%aprop d'%aprop)
  (at level 70).

Notation "d '≡ᵣ' d'" := (d%aprop ≡ᵣ@{_} d'%aprop)
  (at level 70).




Section BoolExample.

Notation "x == y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) : {n & {m & (AProp (fin 7) n m * AProp (fin 7) n m)%type}})
  (at level 70).

Definition BOOL : Signature bool := {|
  gens := 7;
  gen_arity := [# (0, 1) (* T *);
    (0, 1) (* F *);
    (2, 1) (* & *);
    (2, 1) (* || *);
    (1, 0) (* T̄ *);
    (1, 0) (* F̄ *);
    (1, 0) (* disc *)
    ];
  rules := [ (Aswap 1 1 ;' Agen 2%fin 2 1)%aprop == Agen 2%fin 2 1];
|}.

(* TODO: Notation for signature based on let- bindings, e.g.
  declaring T would give something like: 

  let T := (Agen 0%fin 0 1) in let gens := S gens in let gen_arity := gen_arity +++ [(0, 1)] in 
  
  and then the lets would terminate in the bottom where we'd specify rules
  *)

End BoolExample.

