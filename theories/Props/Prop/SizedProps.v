From TensorRocq Require Export Tensor Algebra Monoid.
From TensorRocq Require Import BW.


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
  (* Identity process *)
  | Mid n : MPRO n n
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


From TensorRocq Require Import Props.

Fixpoint MPRO_to_PRO {A} (f : A -> nat)
  `{interp : InterpStruct A MStruct Struct}
  (* {MStruct : btree A -> btree A -> Type}
  {Struct : nat -> nat -> Type}  *)
  (* (interpStruct : forall (n m : btree A), MStruct n m ->
    Struct (btree_size f n) (btree_size f m)) *)
  {T} {n m : btree A}
  (mp : MPRO MStruct T n m) : PRO Struct T (btree_size f n) (btree_size f m) :=
  match mp with
  | Mid n => Pid (btree_size f n)
  | Mcompose mp1 mp2 => Pcompose (MPRO_to_PRO f mp1)
    (MPRO_to_PRO f mp2)
  | Mstack mp1 mp2 => Pstack (MPRO_to_PRO f mp1)
    (MPRO_to_PRO f mp2)
  | Mstruct n m s => Pstruct _ _ (interpStruct f s)
  | Mgen n m t => Pgen _ _ t
  end.



Inductive MMonoidal {A} : btree A -> btree A -> Type :=
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
  | MSwap a b => Swap (btree_size f a) (btree_size f b)
  end.

#[export] Instance interpStructSymmetry {A} : @InterpStruct A MSymmetry Symmetry :=
  interpMSymmetry.

Definition interpMAutonomy {A} (f : A -> nat) {n m}
  (p : MAutonomy n m) : Autonomy (btree_size f n) (btree_size f m) :=
  match p with
  | MCup a => Cup (btree_size f a)
  | MCap a => Cap (btree_size f a)
  end.

#[export] Instance interpStructAutonomy {A} : @InterpStruct A MAutonomy Autonomy :=
  interpMAutonomy.

Definition interpMSCartesian {A} (f : A -> nat) {n m}
  (p : MSCartesian n m) : SCartesian (btree_size f n) (btree_size f m) :=
  match p with
  | MDelta a b => Delta (btree_size f a) (btree_size f b)
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
  | Mid _ => Mid _
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
  | Mid _ => Mid _
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
  | Mid _ => Mid _
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
  | Mid _ => Mid _
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
  | Mid _ => Mid _
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
  | Mid _ => Mid _
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




Import vector.


Fixpoint btree_velems {A} (b : btree A) : vec A (bsize b) :=
  match b with
  | 0 => [#]
  | !a => [# a]
  | l + r => btree_velems l +++ btree_velems r
  end%btree.

(* Coercion btree_velems : btree >-> Vector.t. *)

Fixpoint fin_btree_size_cases {A} (f : A -> nat) (b : btree A) :
  fin (btree_size f b) -> {i : fin (bsize b) & fin (f (btree_velems b !!! i))} :=
  match b (* as b return
  fin (btree_size f b) -> {i : fin (bsize b) & fin (f (btree_velems b !!! i))} *) with
  | 0 => fin_0_inv _
  | !a => fun i => existT 0%fin i
  | l + r => fun i : fin (btree_size f l + btree_size f r) =>
    sum_rect (λ _, _)
    ((λ '(existT i' j), existT (P:=λ i, fin (f (_ !!! i))) (Fin.L (bsize r) i')
      (Fin.cast j (f_equal f (eq_sym (lookup_vapp_L (btree_velems l) (btree_velems r) i'))))) ∘ fin_btree_size_cases f l)
    ((λ '(existT i' j), existT (P:=λ i, fin (f (_ !!! i))) (Fin.R (bsize l) i')
      (Fin.cast j (f_equal f (eq_sym (lookup_vapp_R (btree_velems l) (btree_velems r) i'))))) ∘ fin_btree_size_cases f r) (fin_sum_case i)
  end%btree.

Fixpoint fin_btree_size_cases_inv {A} (f : A -> nat) (b : btree A) :
  forall (i : fin (bsize b)) (j : fin (f (btree_velems b !!! i))), fin (btree_size f b) :=
  match b with
  | 0 => fin_0_inv _
  | !a => fin_S_inv _ id (fin_0_inv _)
  | l + r => fin_add_inv _
    (λ i j, Fin.L (btree_size f r)
      (fin_btree_size_cases_inv f l i (Fin.cast j (f_equal f (lookup_vapp_L (btree_velems l) (btree_velems r) i)))))
    (λ i j, Fin.R (btree_size f l)
      (fin_btree_size_cases_inv f r i (Fin.cast j (f_equal f (lookup_vapp_R (btree_velems l) (btree_velems r) i)))))
  end%btree.

Lemma fin_add_inv_L {n m} (P : fin (n + m) -> Type)
  (HPl : forall i, P (Fin.L m i)) (HPr : forall i, P (Fin.R n i))
  (i : fin n) :
  fin_add_inv P HPl HPr (Fin.L m i) = HPl i.
Proof.
  revert P HPl HPr i;
  induction n; [easy|];
  intros P HPl HPr i.
  inv_all_vec_fin; [done|].
  cbn.
  now rewrite IHn.
Qed.

Lemma fin_add_inv_R {n m} (P : fin (n + m) -> Type)
  (HPl : forall i, P (Fin.L m i)) (HPr : forall i, P (Fin.R n i))
  (i : fin m) :
  fin_add_inv P HPl HPr (Fin.R n i) = HPr i.
Proof.
  revert P HPl HPr i;
  induction n; [easy|];
  intros P HPl HPr i.
  cbn.
  now rewrite IHn.
Qed.

Lemma fin_btree_size_cases_linv {A} (f : A -> nat) (b : btree A) (i : fin (btree_size f b)) :
  i = let '(existT i' j') := fin_btree_size_cases f b i in fin_btree_size_cases_inv f b i' j'.
Proof.
  induction b.
  - cbn in *.
    induction i using fin_add_inv.
    + rewrite fin_sum_case_L.
      cbn.
      rewrite IHb1 at 1.
      destruct (fin_btree_size_cases f b1 i) as [i' j'].
      rewrite fin_add_inv_L.
      f_equal.
      f_equal.
      apply fin_to_nat_inj.
      now rewrite 2 fin_to_nat_cast.
    + rewrite fin_sum_case_R.
      cbn.
      rewrite IHb2 at 1.
      destruct (fin_btree_size_cases f b2 i) as [i' j'].
      rewrite fin_add_inv_R.
      f_equal.
      f_equal.
      apply fin_to_nat_inj.
      now rewrite 2 fin_to_nat_cast.
  - done.
  - easy.
Qed.

Lemma fin_btree_size_cases_rinv {A} (f : A -> nat) (b : btree A) (i : fin (bsize b)) j :
  fin_btree_size_cases f b (fin_btree_size_cases_inv f b i j) = existT i j.
Proof.
  induction b.
  - cbn in *.
    induction i using fin_add_inv.
    + rewrite fin_add_inv_L, fin_sum_case_L.
      cbn.
      rewrite IHb1.
      f_equal.
      f_equal.
      apply fin_to_nat_inj.
      now rewrite 2 fin_to_nat_cast.
    + rewrite fin_add_inv_R, fin_sum_case_R.
      cbn.
      rewrite IHb2.
      f_equal.
      f_equal.
      apply fin_to_nat_inj.
      now rewrite 2 fin_to_nat_cast.
  - cbn.
    inv_all_vec_fin.
    done.
  - easy.
Qed.

Lemma length_btree_elems {A} (b : btree A) : length b = bsize b.
Proof.
  induction b; [|done..].
  cbn.
  now rewrite length_app; congruence.
Qed.

Import Aux_stdpp.

Lemma list_to_vec_app {A} (l l' : list A) :
  list_to_vec (l ++ l') = Vector.cast (list_to_vec l +++ list_to_vec l') (eq_sym (length_app _ _)).
Proof.
  induction l.
  - rewrite cast_id.
    done.
  - cbn.
    f_equal.
    rewrite IHl.
    f_equal.
    apply proof_irrel.
Qed.

Lemma cast_cast {A} {n m o} (v : vec A n) (Hnm : n = m) (Hmo : m = o) :
  Vector.cast (Vector.cast v Hnm) Hmo = Vector.cast v (eq_trans Hnm Hmo).
Proof.
  subst; now rewrite ?cast_id.
Qed.

Lemma btree_elems_eq_btree_velems {A} (b : btree A) :
  b =@{list A} btree_velems b.
Proof.
  induction b; [|done..].
  cbn.
  now rewrite vec_to_list_app; congruence.
Qed.

Lemma btree_velems_eq_btree_elems {A} (b : btree A) :
  btree_velems b = Vector.cast (list_to_vec b) (length_btree_elems b).
Proof.
  apply vec_to_list_inj2.
  rewrite vec_to_list_cast.
  rewrite btree_elems_eq_btree_velems.
  now rewrite vec_to_list_to_vec.
Qed.

Lemma MMonoidal_eq {A} {n m : btree A} (p : MMonoidal n m) :
  bsize n = bsize m.
Proof.
  induction p; cbn; lia.
Qed.

Lemma vlookup_cast {A n m} (v : vec A n) (H : n = m) i :
  (Vector.cast v H) !!! i = v !!! (Fin.cast i (eq_sym H)).
Proof.
  subst.
  rewrite cast_id.
  cbn.
  now rewrite fcast_id.
Qed.

Lemma cast_fun_to_vec {A n m} (f : _ -> A) (H : n = m) :
  Vector.cast (fun_to_vec f) H = fun_to_vec (λ i, f (Fin.cast i (eq_sym H))).
Proof.
  apply vec_eq.
  intros i.
  rewrite vlookup_cast.
  now rewrite 2 lookup_fun_to_vec.
Qed.

Lemma fin_to_nat_cast {n m} (i : fin n) (H : n = m) :
  Fin.cast i H =@{nat} i.
Proof.
  subst.
  now rewrite fcast_id.
Qed.

Lemma lookup_btree_velems_MMonoidal_eq {A} {n m : btree A} (g : MMonoidal n m) i :
  btree_velems m !!! Fin.cast i (MMonoidal_eq g) =
  btree_velems n !!! i.
Proof.
  rewrite <- (eq_sym_involutive (MMonoidal_eq g)), <- vlookup_cast.
  f_equal.
  apply vec_to_list_inj2.
  rewrite vec_to_list_cast.
  clear i.
  induction g; cbn; rewrite ?vec_to_list_app; cbn;
  now rewrite ?(assoc app), ?app_nil_r.
Qed.

Definition MSymmetric_perm {A} {n m : btree A} (g : MSymmetric n m) :
  fin (bsize n) -> fin (bsize m) :=
  match g with
  | inl m => fun i => Fin.cast i (MMonoidal_eq m)
  | inr s =>
    match s with
    | MSwap n m => fun i => sum_rect (λ _, fin (bsize m + bsize n))
      (Fin.R (bsize m)) (Fin.L (bsize n)) (@fin_sum_case (bsize n) (bsize m) i)
    end
  end.

Lemma lookup_btree_velems_MSymmetric_perm {A} {n m : btree A} (g : MSymmetric n m) i :
  btree_velems m !!! MSymmetric_perm g i =
  btree_velems n !!! i.
Proof.
  induction g as [p|p].
  - cbn.
    apply lookup_btree_velems_MMonoidal_eq.
  - induction p.
    cbn in *.
    rewrite 2 lookup_vapp.
    destruct (fin_sum_case i); cbn;
    [rewrite fin_sum_case_R|rewrite fin_sum_case_L]; done.
Qed.


Fixpoint MSymmetric_SMPRO_perm {A} {n m : btree A} (g : SMPRO MSymmetric n m) :
  fin (bsize n) -> fin (bsize m) :=
  match g with
  | Mid _ => id
  | Mstruct _ _ s => MSymmetric_perm s
  | Mgen _ _ m => match m with end
  | Mcompose l r => MSymmetric_SMPRO_perm r ∘ MSymmetric_SMPRO_perm l
  | Mstack l r =>
    fun i => sum_rect (λ _, fin (bsize _ + bsize _))
      (Fin.L (bsize _) ∘ MSymmetric_SMPRO_perm l)
      (Fin.R (bsize _) ∘ MSymmetric_SMPRO_perm r) (@fin_sum_case (bsize _) (bsize _) i)
  end.

Lemma lookup_btree_velems_MSymmetric_SMPRO_perm {A} {n m : btree A} (g : SMPRO MSymmetric n m) i :
  btree_velems m !!! MSymmetric_SMPRO_perm g i =
  btree_velems n !!! i.
Proof.
  revert i;
  induction g; intros i.
  - done.
  - cbn.
    rewrite IHg2, IHg1.
    done.
  - cbn in *.
    rewrite 2 lookup_vapp.
    destruct (fin_sum_case i); cbn;
    [rewrite fin_sum_case_L|rewrite fin_sum_case_R]; cbn; auto.
  - apply lookup_btree_velems_MSymmetric_perm.
  - easy.
Qed.

Definition SymmetricG_perm_by_MSymmetric_perm
  {A} (f : A -> nat) {n m : btree A} (g : MSymmetric n m) :
  fin (btree_size f n) -> fin (btree_size f m) :=
    fun ij =>
    let '(existT i j) := fin_btree_size_cases f n ij in
    fin_btree_size_cases_inv f m
      (MSymmetric_perm g i) (Fin.cast j (f_equal f
        (eq_sym (lookup_btree_velems_MSymmetric_perm g i)))).


Definition SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm
  {A} (f : A -> nat) {n m : btree A} (g : SMPRO MSymmetric n m) :
  fin (btree_size f n) -> fin (btree_size f m) :=
    fun ij =>
    let '(existT i j) := fin_btree_size_cases f n ij in
    fin_btree_size_cases_inv f m
      (MSymmetric_SMPRO_perm g i) (Fin.cast j (f_equal f
        (eq_sym (lookup_btree_velems_MSymmetric_SMPRO_perm g i)))).

Lemma fcast_assoc {n m o} (i : fin (n + m + o)) (H : n + m + o = n + (m + o)) :
  Fin.cast i H =
  sum_rect (λ _, fin _) (λ i, sum_rect (λ _, fin _) (Fin.L _) (Fin.R _ ∘ Fin.L _) (fin_sum_case i))
    (Fin.R _ ∘ Fin.R _) (fin_sum_case i).
Proof.
  apply fin_to_nat_inj.
  rewrite fin_to_nat_cast.
  induction i as [i|i] using fin_add_inv;
  [rewrite fin_sum_case_L; induction i as [i|i] using fin_add_inv|]; cbn.
  - rewrite fin_sum_case_L.
    cbn.
    now rewrite 3 fin_to_nat_L.
  - rewrite fin_sum_case_R.
    cbn.
    rewrite fin_to_nat_L, 2 fin_to_nat_R, fin_to_nat_L.
    done.
  - rewrite fin_sum_case_R.
    cbn.
    rewrite 3 fin_to_nat_R; lia.
Qed.

Lemma fcast_iassoc {n m o} (i : fin (n + (m + o))) (H : n + (m + o) = n + m + o) :
  Fin.cast i H =
  sum_rect (λ _, fin _) (Fin.L _ ∘ Fin.L _)
    (λ i, sum_rect (λ _, fin _) (Fin.L _ ∘ Fin.R _) (Fin.R _) (fin_sum_case i)) (fin_sum_case i).
Proof.
  apply fin_to_nat_inj.
  rewrite fin_to_nat_cast.
  induction i as [i|i] using fin_add_inv;
  [|rewrite fin_sum_case_R; induction i as [i|i] using fin_add_inv]; cbn.
  - rewrite fin_sum_case_L.
    cbn.
    now rewrite 3 fin_to_nat_L.
  - rewrite fin_sum_case_L.
    cbn.
    rewrite fin_to_nat_L, 2 fin_to_nat_R, fin_to_nat_L.
    done.
  - rewrite fin_sum_case_R.
    cbn.
    rewrite 3 fin_to_nat_R; lia.
Qed.


Lemma SymmetricG_perm_by_MSymmetric_perm_correct
  {A} (f : A -> nat) {n m : btree A} (g : MSymmetric n m) :
  fun_to_vec (SymmetricG_perm_by_MSymmetric_perm f g) =
  fun_to_vec (SymmetricG_perm (interpStruct f g)).
Proof.
  induction g as [p|p]; apply vec_eq; intros i; rewrite 2 lookup_fun_to_vec.
  - cbn.
    unfold SymmetricG_perm_by_MSymmetric_perm.
    cbn.
    symmetry.
    etransitivity. 1:{
      apply (f_equal (fun i => Fin.cast i _)).
      apply (fin_btree_size_cases_linv f n i).
    }
    destruct (fin_btree_size_cases f n i) as [i' j'].
    clear i.
    apply fin_to_nat_inj.
    rewrite fin_to_nat_cast.
    induction p; cbn in *;
    repeat (remember (f_equal f _) as prf eqn:Hprf;
      clear Hprf; revert prf).
    + rewrite fcast_assoc.
      repeat_on_hyps ltac:(fun H =>
      match type of H with
      | fin (_ + _) => induction H using fin_add_inv
      end);
      repeat (rewrite ?fin_add_inv_L, ?fin_add_inv_R, ?fin_sum_case_L, ?fin_sum_case_R; cbn).
      * intros.
        rewrite fcast_cast.
        rewrite 3 fin_to_nat_L.
        do 2 f_equal.
        apply fin_to_nat_inj.
        now rewrite 3 fin_to_nat_cast.
      * intros.
        rewrite fcast_cast.
        rewrite fin_to_nat_R, 2 fin_to_nat_L, fin_to_nat_R.
        do 3 f_equal.
        apply fin_to_nat_inj.
        now rewrite ? fin_to_nat_cast.
      * intros.
        rewrite fcast_cast.
        rewrite 3 fin_to_nat_R.
        rewrite Nat.add_assoc.
        do 3 f_equal.
        apply fin_to_nat_inj.
        now rewrite ? fin_to_nat_cast.
    + rewrite fcast_iassoc.
      repeat_on_hyps ltac:(fun H =>
      match type of H with
      | fin (_ + _) => induction H using fin_add_inv
      end);
      repeat (rewrite ?fin_add_inv_L, ?fin_add_inv_R, ?fin_sum_case_L, ?fin_sum_case_R; cbn).
      * intros.
        rewrite fcast_cast.
        rewrite 3 fin_to_nat_L.
        do 2 f_equal.
        apply fin_to_nat_inj.
        now rewrite 3 fin_to_nat_cast.
      * intros.
        rewrite fcast_cast.
        rewrite fin_to_nat_R, 2 fin_to_nat_L, fin_to_nat_R.
        do 3 f_equal.
        apply fin_to_nat_inj.
        now rewrite ? fin_to_nat_cast.
      * intros.
        rewrite fcast_cast.
        rewrite 3 fin_to_nat_R.
        rewrite Nat.add_assoc.
        do 3 f_equal.
        apply fin_to_nat_inj.
        now rewrite ? fin_to_nat_cast.
    + rewrite fcast_id.
      intros.
      now rewrite 2 fcast_id.
    + rewrite fcast_id.
      intros.
      now rewrite 2 fcast_id.
    + induction i' using fin_add_inv; [|easy].
      revert j'.
      cbn.
      replace (Fin.cast (Fin.L 0 i') _) with i' by 
        now apply fin_to_nat_inj; rewrite fin_to_nat_cast, fin_to_nat_L.
      rewrite fin_add_inv_L.
      intros.
      rewrite fin_to_nat_L.
      do 2 f_equal.
      apply fin_to_nat_inj.
      now rewrite ?fin_to_nat_cast.
    + replace (Fin.cast i' _) with (Fin.L 0 i') by 
        now apply fin_to_nat_inj; rewrite fin_to_nat_cast, fin_to_nat_L.
      rewrite fin_add_inv_L.
      intros.
      rewrite fin_to_nat_L.
      do 2 f_equal.
      apply fin_to_nat_inj.
      now rewrite ?fin_to_nat_cast.
  - induction p as [n m].
    cbn in *.
    induction i using fin_add_inv.
    + rewrite fin_sum_case_L.
      cbn.
      unfold SymmetricG_perm_by_MSymmetric_perm.
      cbn.
      rewrite fin_sum_case_L.
      cbn.
      destruct (fin_btree_size_cases f n i) as [i' j'] eqn:Hi'.
      rewrite fcast_cast.
      remember (eq_trans _ _) as prf eqn:Hprf; clear Hprf; revert prf.
      rewrite fin_sum_case_L.
      cbn.
      intros prf.
      rewrite fin_add_inv_R.
      f_equal.
      symmetry.
      rewrite (fin_btree_size_cases_linv f n i) at 1.
      rewrite Hi'.
      f_equal.
      now rewrite fcast_cast, fcast_id.
    + rewrite fin_sum_case_R.
      cbn.
      unfold SymmetricG_perm_by_MSymmetric_perm.
      cbn.
      rewrite fin_sum_case_R.
      cbn.
      destruct (fin_btree_size_cases f m i) as [i' j'] eqn:Hi'.
      rewrite fcast_cast.
      remember (eq_trans _ _) as prf eqn:Hprf; clear Hprf; revert prf.
      rewrite fin_sum_case_R.
      cbn.
      intros prf.
      rewrite fin_add_inv_L.
      f_equal.
      symmetry.
      rewrite (fin_btree_size_cases_linv f m i) at 1.
      rewrite Hi'.
      f_equal.
      now rewrite fcast_cast, fcast_id.
Qed.



Lemma SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm_correct
  {A} (f : A -> nat) {n m : btree A} (g : SMPRO MSymmetric n m) :
  fun_to_vec (SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm f g) =
  fun_to_vec (SymmetricG_SPRO_perm (MPRO_to_PRO f g)).
Proof.
  apply vec_eq; intros i; rewrite 2 lookup_fun_to_vec.
  revert i.
  induction g; intros i.
  - cbn.
    unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm.
    cbn.
    rewrite (fin_btree_size_cases_linv f n i) at 2.
    case_match.
    f_equal.
    apply fcast_id.
  - cbn.
    rewrite <- IHg2, <- IHg1.
    unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm.
    case_match.
    cbn.
    rewrite fin_btree_size_cases_rinv.
    f_equal.
    rewrite fcast_cast.
    f_equal.
    apply proof_irrel.
  - unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm.
    cbn in *.
    induction i as [i|i] using fin_add_inv.
    + rewrite fin_sum_case_L.
      cbn.
      destruct (fin_btree_size_cases f _ i) as [i' j'] eqn:Hi'.
      cbn.
      rewrite fcast_cast.
      remember (eq_trans _ _) as prf eqn:Hprf; clear Hprf; revert prf.
      rewrite fin_sum_case_L.
      cbn.
      rewrite fin_add_inv_L.
      intros prf.
      f_equal.
      rewrite <- IHg1.
      unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm.
      rewrite Hi'.
      f_equal.
      rewrite fcast_cast.
      f_equal; apply proof_irrel.
    + rewrite fin_sum_case_R.
      cbn.
      destruct (fin_btree_size_cases f _ i) as [i' j'] eqn:Hi'.
      cbn.
      rewrite fcast_cast.
      remember (eq_trans _ _) as prf eqn:Hprf; clear Hprf; revert prf.
      rewrite fin_sum_case_R.
      cbn.
      rewrite fin_add_inv_R.
      intros prf.
      f_equal.
      rewrite <- IHg2.
      unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm.
      rewrite Hi'.
      f_equal.
      rewrite fcast_cast.
      f_equal; apply proof_irrel.
  - rewrite 2 fin_perm_eta.
    cbn.
    rewrite <- SymmetricG_perm_by_MSymmetric_perm_correct.
    rewrite <- 2 fin_perm_eta.
    unfold SymmetricG_SPRO_perm_by_MSymmetric_SMPRO_perm, SymmetricG_perm_by_MSymmetric_perm.
    case_match.
    f_equal.
    f_equal.
    apply proof_irrel.
  - easy.
Qed.


