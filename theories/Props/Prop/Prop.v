From TensorRocq Require Export Tensor CospanHyperGraph GraphRewriting.

#[universes(template)]
Inductive PRO  {Struct : nat -> nat -> Type} {Ty : Type} : nat -> nat -> Type :=
  (* Composition of processes *)
  | compose {n m o} (ap1 : PRO n m) (ap2 : PRO m o) : PRO n o
  (* Parallel products of processes *)
  | stack {n1 m1 n2 m2} (ap1 : PRO n1 m1) (ap2 : PRO n2 m2) :
    PRO (n1 + n2) (m1 + m2)
  (* Structural generators which can restrict sizes they operate over *)
  | Pstruct (n m : nat) (s : Struct n m) : PRO n m
  (* Nonstructural generators which must be defined for all sizes *)
  | Pgen (t : Ty) n m : PRO n m.

#[global] Arguments PRO : clear implicits.

Print StrictTensorLike.
Print strictInterpretTensor.

(* Arguments StrictTensorLike : clear implicits. *)

Fixpoint PRO_semantics `{SR : SemiRing R rO rI radd rmul req}
  `{SA : Summable A, EqA : EqDecision A} 
  `{Equiv T, Equivalence T equiv}
   {Struct : nat -> nat -> Type}
    `{TensT : !TensorLike R A T}
  {n m}
    (* `{TensS : !StrictTensorLike R n m A Struct} *)
  (ap : PRO Struct T n m) : Tensor (R:=R) n m A :=
  match ap with
  | compose ap1 ap2 =>
      compose_tensor (PRO_semantics ap1) (PRO_semantics ap2)
  | stack ap1 ap2 =>
      stack_tensor (PRO_semantics ap1) (PRO_semantics ap2)
  | Pgen t n m    => interpretTensor t n m
  (* | Pstruct n m s => strictInterpretTensor (StrictTensorLike:=TensS) n m s *)
  end.

Inductive Permutation : nat -> nat -> Type :=
  | Swap n m : Permutation (n + m) (m + n)
  | Pid  n   : Permutation n n.

Section TensorLikePermutations.

Context `{SR : SemiRing R rO rI radd rmul req}.
Context  `{SA : Summable A, EqA : EqDecision A}.
(* Context (n m : nat). *)

Definition permToTensor (n m : nat) (p : Permutation n m) : Tensor (R:=R) n m A :=
  match p with
  | Swap a b => swap_tensor
  | Pid  n   => delta_tensor
  end. 

Instance PermEquiv {n m} : Equiv (Permutation n m) := {
  equiv := eq
}.

Lemma permToTensorProper {n m} :
  Proper (equiv ==> equiv) (permToTensor n m).
Proof. intros p0 p1 eq; by rewrite eq. Qed.

Instance TensorLikePerm {n m : nat} : StrictTensorLike (n:=n) (m:=m) R A Permutation :=
  {
    sInterpretTensor := permToTensor;
    sInterpretTensorProper := permToTensorProper
  }.
  


Inductive Autonomy : nat -> nat -> Type :=
  | Cap n : Autonomy 0 (n + n)
  | Cup n : Autonomy (n + n) 0.

Inductive SCartesian : nat -> nat -> Type :=
  | Delta n m : SCartesian n m.

Definition Autonomous (n m : nat) := (Permutation n m + Autonomy n m)%type.

Definition Cartesian (n m : nat) := (Autonomous n m + SCartesian n m)%type.

Definition PROP := PRO Permutation.
Definition APROP := PRO Autonomous.
Definition CPROP := PRO Cartesian.

End TensorLikePermutations.
