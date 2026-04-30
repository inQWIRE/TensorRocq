From TensorRocq Require Export Tensor Algebra Monoid.
From TensorRocq Require Import BW.

Notation btree_size f := (btree_fold O f Nat.add).

Class InterpStruct {A} (MStruct : btree A -> btree A -> Type)
  (Struct : nat -> nat -> Type) := 
  interpStruct (f : A -> nat) {n m} (ms : MStruct n m) : 
    Struct (btree_size f n) (btree_size f m).

#[export] Instance interpStructMorUnion {A}
  (MStruct MStruct' : btree A -> btree A -> Type)
  (Struct Struct' : nat -> nat -> Type)
  (interp : InterpStruct MStruct Struct)
  (interp' : InterpStruct MStruct' Struct') :
  InterpStruct (MorUnion MStruct MStruct') (MorUnion Struct Struct') := {
  interpStruct f n m ms := sum_map (interpStruct f) (interpStruct f) ms
}.

#[universes(template)]
Inductive MPRO {A} {MStruct : btree A -> btree A -> Type} {Ty : Type} : 
  btree A -> btree A -> Type :=
  (* Composition of processes *)
  | Mcompose {n m o} (ap1 : MPRO n m) (ap2 : MPRO m o) : MPRO n o
  (* Parallel products of processes *)
  | Mstack {n1 m1 n2 m2} (ap1 : MPRO n1 m1) (ap2 : MPRO n2 m2) :
    MPRO (n1 + n2) (m1 + m2)
  (* Structural generators which can restrict sizes they operate over *)
  | Mstruct (n m : btree A) (s : MStruct n m) : MPRO n m
  (* Nonstructural generators which must be defined for all sizes *)
  | Mgen (t : Ty) n m : MPRO n m.

#[global] Arguments MPRO {_} (_) (_) (_ _) : assert.


From TensorRocq Require Import Props.Prop.Prop.

Fixpoint MPRO_to_PRO {A} (f : A -> nat)
  `{interp : InterpStruct A MStruct Struct}
  (* {MStruct : btree A -> btree A -> Type} 
  {Struct : nat -> nat -> Type}  *)
  (* (interpStruct : forall (n m : btree A), MStruct n m -> 
    Struct (btree_size f n) (btree_size f m)) *)
  {T} {n m : btree A}
  (mp : MPRO MStruct T n m) : PRO Struct T (btree_size f n) (btree_size f m) :=
  match mp with
  | Mcompose mp1 mp2 => Pcompose (MPRO_to_PRO f mp1)
    (MPRO_to_PRO f mp2)
  | Mstack mp1 mp2 => Pstack (MPRO_to_PRO f mp1)
    (MPRO_to_PRO f mp2)
  | Mstruct n m s => Pstruct _ _ (interpStruct f s)
  | Mgen t n m => Pgen t _ _
  end.



Inductive MMonoidal {A} : btree A -> btree A -> Type :=
  | MId {n} : MMonoidal n n
  | MAssociator {n m o} : MMonoidal (n + m + o) (n + (m + o))
  | MInvAssociator {n m o} : MMonoidal (n + (m + o)) (n + m + o)
  | MLUnit {n} : MMonoidal (0 + n) n
  | MInvLUnit {n} : MMonoidal n (0 + n)
  | MRUnit {n} : MMonoidal (n + 0) n
  | MInvRUnit {n} : MMonoidal n (n + 0).


Inductive MSymmetry {A} : btree A -> btree A -> Type :=
  | MSwap n m : MSymmetry (n + m) (m + n).

Inductive MAutonomy {A} : btree A -> btree A -> Type :=
  | MCup n : MAutonomy 0 (n + n)
  | MCap n : MAutonomy (n + n) 0.

Inductive MSCartesian {A} : btree A -> btree A -> Type :=
  | MDelta n m : MSCartesian n m.


Definition MSymmetric {A} : btree A -> btree A -> Type := MorUnion MMonoidal MSymmetry.

Definition MAutonomous {A} : btree A -> btree A -> Type := MorUnion MSymmetric MAutonomy.

Definition MCartesian {A} : btree A -> btree A -> Type  := MorUnion MAutonomous MSCartesian.


Section TensorLikePermutations.


Definition interpMMonoidal {A} (f : A -> nat) {n m} 
  (p : MMonoidal n m) : Monoidal (btree_size f n) (btree_size f m) :=
  match p with
  | MId => Id
  | MAssociator => Associator
  | MInvAssociator => InvAssociator
  | MLUnit => LUnit
  | MInvLUnit => InvLUnit
  | MRUnit => RUnit
  | MInvRUnit => InvRUnit
  end.

#[export] Instance interpStructMonoidal {A} : @InterpStruct A MMonoidal Monoidal :=
  interpMMonoidal.

Definition interpMSymmetry {A} (f : A -> nat) {n m} 
  (p : MSymmetry n m) : Symmetry (btree_size f n) (btree_size f m) :=
  match p with
  | MSwap a b => Swap _ _
  end.

#[export] Instance interpStructSymmetry {A} : @InterpStruct A MSymmetry Symmetry :=
  interpMSymmetry.

Definition interpMAutonomy {A} (f : A -> nat) {n m} 
  (p : MAutonomy n m) : Autonomy (btree_size f n) (btree_size f m) :=
  match p with
  | MCup a => Cup _
  | MCap a => Cap _
  end.

#[export] Instance interpStructAutonomy {A} : @InterpStruct A MAutonomy Autonomy :=
  interpMAutonomy.

Definition interpMSCartesian {A} (f : A -> nat) {n m} 
  (p : MSCartesian n m) : SCartesian (btree_size f n) (btree_size f m) :=
  match p with
  | MDelta a b => Delta _ _
  end.

#[export] Instance interpStructSCartesian {A} : @InterpStruct A MSCartesian SCartesian :=
  interpMSCartesian.


End TensorLikePermutations.

Definition mmonoidal_inl {A} {n m} (p : @MMonoidal A n m) : MSymmetric n m := inl p.
Definition msymmetry_inr {A} {n m} (p : @MSymmetry A n m) : MSymmetric n m := inr p.
Definition msymmetric_inl {A} {n m} (p : @MSymmetric A n m) : MAutonomous n m := inl p.
Definition mautonomy_inr {A} {n m} (p : @MAutonomy A n m) : MAutonomous n m := inr p.
Definition mautonomous_inl {A} {n m} (p : @MAutonomous A n m) : MCartesian n m := inl p.
Definition mscartesian_inr {A} {n m} (p : @MSCartesian A n m) : MCartesian n m := inr p.


Coercion mmonoidal_inl : MMonoidal >-> MSymmetric.
Coercion msymmetry_inr : MSymmetry >-> MSymmetric.
Coercion msymmetric_inl : MSymmetric >-> MAutonomous.
Coercion mautonomy_inr : MAutonomy >-> MAutonomous.
Coercion mautonomous_inl : MAutonomous >-> MCartesian.
Coercion mscartesian_inr : MSCartesian >-> MCartesian.


Notation MPROP := (MPRO MSymmetric).
Notation MAPROP := (MPRO MAutonomous).
Notation MCPROP := (MPRO MCartesian).
