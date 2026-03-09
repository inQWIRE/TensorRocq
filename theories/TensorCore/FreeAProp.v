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
    SummedElement v -> SummedElement w ->
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
  @equiv _ (@Tensor_equiv _ _ _ _ _ _ (FSR_SR_eqg nat (SigTensRel Sig)) _ _ _ _)
  (AProp_semantics (TensT:=SignatureTensorLike_base Sig) d)
  (AProp_semantics (TensT:=SignatureTensorLike_base Sig) d').

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

Lemma rules_hold `{SA : Summable A, EqA : EqDecision A}
  (Sig : Signature A) {n m} (lhs rhs : AProp (fin Sig.(gens)) n m) :
  existT n (existT m (lhs, rhs)) ∈ Sig.(rules) ->
  lhs ≡ᵣ rhs.
Proof.
  intros Hrule.
  unfold SigTensAProp_eq.
  intros v w Hv Hw.
  apply FSR_eqg_R_subrelation.
  econstructor; [eauto|].
  now constructor.
Qed.




Section BoolExample.

Notation "x == y" :=
  (existT _ (existT _ (x%aprop, y%aprop)) : {n & {m & (AProp (fin 7) n m * AProp (fin 7) n m)%type}})
  (at level 70).


Let T := Agen (0%fin : fin 7) 0 1.
Let F := Agen (1%fin : fin 7) 0 1.
Let AND := Agen (2%fin : fin 7) 2 1.
Let OR := Agen (3%fin : fin 7) 2 1.
Let coT := Agen (4%fin : fin 7) 1 0.
Let coF := Agen (5%fin : fin 7) 1 0.
Let disc := Agen (6%fin : fin 7) 1 0.

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
  rules :=  [ 
      T * Aid 1 ;' AND == Aid 1 ;
      F * Aid 1 ;' AND == disc ;' T ;
      Aswap 1 1 ;' AND == AND ;
      AND * Aid 1 ;' AND == Aid 1 * AND ;' AND ;
      AND ;' coT == coT * coT ;


      F * Aid 1 ;' OR == Aid 1 ;
      T * Aid 1 ;' OR == disc ;' T ;
      Aswap 1 1 ;' OR == OR ;
      OR * Aid 1 ;' OR == Aid 1 * OR ;' OR ;
      OR ;' coF == coF * coF ;

      T ;' coT == Aid 0;
      F ;' coF == Aid 0;

      T ;' coF == F ;' coT

     ];
|}.

Lemma test : (T * T ;' AND) ≡ᵣ@{BOOL} T.
Proof.
Admitted.

(* TODO: Notation for signature based on let- bindings, e.g.
  declaring T would give something like:

  let T := (Agen 0%fin 0 1) in let gens := S gens in let gen_arity := gen_arity +++ [(0, 1)] in

  and then the lets would terminate in the bottom where we'd specify rules
  *)

End BoolExample.

