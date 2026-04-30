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
  | Mgen n m (t : Ty) : MPRO n m.

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
  | Mgen n m t => Pgen _ _ t
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

(* FIXME: Move *) 


Global Instance btree_ret: MRet btree := λ A x, bleaf x.
Global Instance btree_fmap : FMap btree := λ A B f,
  fix go (b : btree A) := match b with 
  | l + r => go l + go r
  | ! a => ! (f a)
  | 0 => 0
  end%btree.
Global Instance btree_omap : OMap btree := λ A B f,
  fix go (b : btree A) := match b with 
  | l + r => go l + go r
  | ! a => match (f a) with Some b => ! b | None => bempty end
  | 0 => 0
  end%btree.
Global Instance btree_bind : MBind btree := λ A B f,
  fix go (b : btree A) := match b with 
  | l + r => go l + go r
  | ! a => (f a)
  | 0 => 0
  end%btree.
Global Instance btree_join: MJoin btree := λ A,
  fix go (bs : btree (btree A)) : btree A :=
  match bs with
  | l + r => go l + go r
  | ! a => a
  | 0 => 0
  end%btree.



Declare Scope mpro_scope.
Delimit Scope mpro_scope with mpro.
Bind Scope mpro_scope with PRO.

Notation "g ∘ f" := (Mcompose f%mpro g%mpro) : mpro_scope.
Notation "f ;; g" := (Mcompose f%mpro g%mpro) : mpro_scope.
Notation "f * g" := (Mstack f%mpro g%mpro) : mpro_scope.

Notation "'[str' s ']'" := (Mstruct _ _ s) : mpro_scope.
Notation "'[gen' t n m ']'" := (Mgen n%nat m%nat t) 
  (t at level 9, n at level 9, m at level 9) : mpro_scope.

Local Open Scope mpro_scope.



Fixpoint dbind_MPRO {A B} {Struct : btree A -> btree A -> Type}
  {Struct' : btree B -> btree B -> Type}
  {T T' : Type} 
  (fb : A -> btree B)
  (fs : forall n m, Struct n m -> MPRO Struct' T' (n ≫= fb) (m ≫= fb))
  (ft : forall n m, T -> MPRO Struct' T' (n ≫= fb) (m ≫= fb)) 
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' (n ≫= fb) (m ≫= fb) :=
  match p with
  | l ;; r => dbind_MPRO fb fs ft l ;; dbind_MPRO fb fs ft r
  | l * r => dbind_MPRO fb fs ft l * dbind_MPRO fb fs ft r
  | [str s ] => fs _ _ s
  | [gen t n m] => ft n m t
  end%mpro.

Fixpoint dbind_MPRO' {A B} {Struct : btree A -> btree A -> Type}
  {Struct' : btree B -> btree B -> Type}
  {T T' : Type} 
  (fb : A -> B)
  (fs : forall n m, Struct n m -> MPRO Struct' T' (fb <$> n) (fb <$> m))
  (ft : forall n m, T -> MPRO Struct' T' (fb <$> n) (fb <$> m)) 
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' (fb <$> n) (fb <$> m) :=
  match p with
  | l ;; r => dbind_MPRO' fb fs ft l ;; dbind_MPRO' fb fs ft r
  | l * r => dbind_MPRO' fb fs ft l * dbind_MPRO' fb fs ft r
  | [str s ] => fs _ _ s
  | [gen t n m] => ft n m t
  end%mpro.


Fixpoint bind_MPRO {A} {Struct : btree A -> btree A -> Type}
  {Struct' : btree A -> btree A -> Type}
  {T T' : Type} 
  (fs : forall n m, Struct n m -> MPRO Struct' T' n m)
  (ft : forall n m, T -> MPRO Struct' T' n m) 
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' n m :=
  match p with
  | l ;; r => bind_MPRO fs ft l ;; bind_MPRO fs ft r
  | l * r => bind_MPRO fs ft l * bind_MPRO fs ft r
  | [str s ] => fs _ _ s
  | [gen t n m] => ft n m t
  end%mpro.




Fixpoint dmap_MPRO {A B} {Struct : btree A -> btree A -> Type}
  {Struct' : btree B -> btree B -> Type}
  {T T' : Type} 
  (fb : A -> btree B)
  (fs : forall n m, Struct n m -> Struct' (n ≫= fb) (m ≫= fb))
  (ft : forall n m, T -> T')
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' (n ≫= fb) (m ≫= fb) :=
  match p with
  | l ;; r => dmap_MPRO fb fs ft l ;; dmap_MPRO fb fs ft r
  | l * r => dmap_MPRO fb fs ft l * dmap_MPRO fb fs ft r
  | [str s ] => [str fs _ _ s]
  | [gen t n m] => [gen (ft n m t) _ _]
  end%mpro.

Fixpoint dmap_MPRO' {A B} {Struct : btree A -> btree A -> Type}
  {Struct' : btree B -> btree B -> Type}
  {T T' : Type} 
  (fb : A -> B)
  (fs : forall n m, Struct n m -> Struct' (fb <$> n) (fb <$> m))
  (ft : forall n m, T -> T')
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' (fb <$> n) (fb <$> m) :=
  match p with
  | l ;; r => dmap_MPRO' fb fs ft l ;; dmap_MPRO' fb fs ft r
  | l * r => dmap_MPRO' fb fs ft l * dmap_MPRO' fb fs ft r
  | [str s ] => [str fs _ _ s]
  | [gen t n m] => [gen (ft n m t) _ _]
  end%mpro.

Fixpoint map_MPRO {A} {Struct : btree A -> btree A -> Type}
  {Struct' : btree A -> btree A -> Type}
  {T T' : Type} 
  (fs : forall n m, Struct n m -> Struct' n m)
  (ft : T -> T')
  {n m} (p : MPRO Struct T n m) : MPRO Struct' T' n m :=
  match p with
  | l ;; r => map_MPRO fs ft l ;; map_MPRO fs ft r
  | l * r => map_MPRO fs ft l * map_MPRO fs ft r
  | [str s ] => [str fs _ _ s]
  | [gen t n m] => [gen (ft t) n m]
  end%mpro.



Lemma map_MPRO_to_bind_MPRO {A} {Struct Struct' : btree A -> btree A -> Type}
  {T T' : Type} 
  (fs : forall n m, Struct n m -> Struct' n m)
  (ft : T -> T') 
  {n m} (p : MPRO Struct T n m) : 
  map_MPRO fs ft p = 
  bind_MPRO (λ n m s, [str (fs n m s)]) (λ n m t, [gen (ft t) n m]) p.
Proof.
  induction p; cbn; congruence.
Qed.



Notation SMPRO Struct := (MPRO Struct Empty_set).

Definition Mstruct' {A Struct T n m} (s : SMPRO Struct n m) : @MPRO A Struct T n m :=
  map_MPRO (λ n m, id) (Empty_set_rect _) s.



