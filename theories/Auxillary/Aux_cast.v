From TensorRocq Require Import Aux Aux_stdpp.
From stdpp Require Import vector base.

Module prf_notations.

Export Aux.prf_notations.

Declare Scope eq_scope.
Delimit Scope eq_scope with eq.
Bind Scope eq_scope with eq.

Export EqNotations.

Notation "'<-' H" := (eq_sym H%eq) (at level 60) : eq_scope.
Notation "f '@' H" := (f_equal f H%eq) (at level 50) : eq_scope.
Notation "f '@2' H , G" := (f_equal2 f H%eq G%eq) (at level 50) : eq_scope.
Notation "f ^~ y '@' H" := (f_equal (fun x => f x y) H%eq) (at level 50, y at level 49) : eq_scope.
Notation "H <-> G" := (eq_trans H%eq G%eq) (at level 95) : eq_scope.
Notation "'refl'" := (@eq_refl _ _) (at level 0) : eq_scope.

Lemma add_cancel_l {n n' m m'} (Hn : n = n') (Hnm : n + m = n' + m') : m = m'.
Proof.
  lia.
Qed.

Lemma add_cancel_r {n n' m m'} (Hm : m = m') (Hnm : n + m = n' + m') : n = n'.
Proof.
  lia.
Qed.

Lemma mul_cancel_lg {n n' m m'} (Hn : n = n') (Hnz : n <> 0 \/ n' <> 0) 
  (Hnm : n * m = n' * m') : m = m'.
Proof.
  nia.
Qed.

Lemma mul_cancel_rg {n n' m m'} (Hm : m = m') (Hnz : m <> 0 \/ m' <> 0) 
  (Hnm : n * m = n' * m') : n = n'.
Proof.
  nia.
Qed.

Lemma mul_cancel_l {n n' m m'} (Hn : n = n') (Hnz : n <> 0) 
  (Hnm : n * m = n' * m') : m = m'.
Proof.
  nia.
Qed.

Lemma mul_cancel_r {n n' m m'} (Hm : m = m') (Hnz : m <> 0) 
  (Hnm : n * m = n' * m') : n = n'.
Proof.
  nia.
Qed.

End prf_notations.

Import prf_notations.


(* TODO: Does this help ever? 
Ltac solve_eq :=
  first [
    reflexivity |
    assumption |
    symmetry; assumption |
    f_equal; solve_eq |
    lia
  ].

#[local] Hint Extern 0 (TCEq _ _) =>
  abstract (apply TCEq_eq; solve [solve_eq]) : typeclass_instances.

Notation "'!_'" := (proj1 (TCEq_eq _ _) _) (at level 1) : eq_scope.
(* Notation "'!_'" := (proj1 (TCEq_eq _ _) _) (at level 1, only printing). *)

Notation "'cast!' d" := (cast !_ !_ d) (at level 10). *)


Fixpoint nat_eq_dec_eval (n m : nat) : Decision (n = m) :=
  match n, m with
  | 0, 0 => left eq_refl
  | 0, S m => right (Nat.neq_0_succ m)
  | S n, 0 => right (Nat.neq_succ_0 n)
  | S n, S m =>
    match nat_eq_dec_eval n m with
    | left Hnm => left (match Hnm with | eq_refl => eq_refl end)
    | right Hnm =>
      right (not_eq_S _ _ Hnm)
    end
  end.

Definition cast {D : nat -> nat -> Type} {n m n' m'} (Hn : n = n') (Hm : m = m')
  (d : D n m) : D n' m' :=
  match nat_eq_dec_eval n n' with
  | left Hn =>
    match nat_eq_dec_eval m m' with
    | left Hm =>
      match Hn with
      | eq_refl => match Hm with
        | eq_refl => d
        end
      end
    | right Hnm => False_rect _ (Hnm Hm)
    end
  | right Hnn => False_rect _ (Hnn Hn)
  end.

Lemma cast_id {D : nat -> nat -> Type} {n m} (Hn : n = n) (Hm : m = m) (d : D n m) :
  cast Hn Hm d = d.
Proof.
  unfold cast.
  destruct (nat_eq_dec_eval _ _); [|done].
  destruct (nat_eq_dec_eval _ _); [|done].
  rewrite (proof_irrel _ eq_refl).
  rewrite (proof_irrel _ eq_refl).
  done.
Qed.

Section cast.

Context {D E F : nat -> nat -> Type}.



Lemma cast_irrel {n m n' m'} (Hn Hn' : n = n') (Hm Hm' : m = m') (d : D n m) :
  cast Hn Hm d = cast Hn' Hm' d.
Proof.
  f_equal; apply proof_irrel.
Qed.

Lemma cast_l {R : forall n m, relation (D n m)} 
  {n m n' m'} d d' (Hn : n = n') (Hm : m = m') : 
  R n' m' (cast Hn Hm d) d' <-> R n m d (cast (eq_sym Hn) (eq_sym Hm) d').
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma cast_r {R : forall n m, relation (D n m)} 
  {n m n' m'} d d' Hn Hm : 
  R n m d (cast Hn Hm d') <-> R n' m' (cast (eq_sym Hn) (eq_sym Hm) d) d'.
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma cast_eq_l
  {n m n' m'} (d d' : D _ _) (Hn : n = n') (Hm : m = m') : 
  (cast Hn Hm d) = d' <-> d = (cast (eq_sym Hn) (eq_sym Hm) d').
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma cast_eq_r
  {n m n' m'} (d d' : D _ _) (Hn : n = n') (Hm : m = m') : 
  d = (cast Hn Hm d') <-> (cast (eq_sym Hn) (eq_sym Hm) d) = d'.
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.


Lemma apply_cast_gen  {fn fm : nat -> nat} 
  (f : forall n m, D n m -> E (fn n) (fm m))
  {n m n' m'} d (Hn : n = n') (Hm : m = m') : 
  f n' m' (cast Hn Hm d) = cast (f_equal fn Hn) (f_equal fm Hm) (f n m d).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma apply_cast_functor
  (f : forall n m, D n m -> E n m)
  {n m n' m'} d (Hn : n = n') (Hm : m = m') : 
  f n' m' (cast Hn Hm d) = cast Hn Hm (f n m d).
Proof.
  now subst; rewrite 2 cast_id.
Qed.

Lemma cast_cast {n m n' m' n'' m''} (d : D n m)
  (Hn : n = n') (Hm : m = m') (Hn' : n' = n'') (Hm' : m' = m'') : 
  cast Hn' Hm' (cast Hn Hm d) = cast (Hn <-> Hn') (Hm <-> Hm') d.
Proof.
  now subst; rewrite !cast_id.
Qed.



End cast.

Ltac subst_cast_prf :=
    let not_refl c :=
      lazymatch type of c with
      | ?l = ?r => assert_fails (timeout 1 (unify l r))
      end in 
    match goal with
    |- context [cast ?hn ?hm _] =>
      (not_refl hn; destruct hn) +
      (not_refl hm; destruct hm)
    end.

Ltac subst_casts := repeat subst_cast_prf.

Ltac solve_cast :=
  subst;
  subst_casts; rewrite ?cast_id; done.


Section gcast_facts.

Context {D E F : nat -> nat -> Type}.

Context (stack : ∀ n m o p, D n m -> E o p -> F (n + o) (m + p))
  (compose : ∀ n m o, D n m -> E m o -> F n o)
  (add : ∀ n m, D n m -> E n m -> F n m)
  (kron : ∀ n m o p, D n m -> E o p -> F (n * o) (m * p)).

Context {n m o p n' m' o' p' : nat}.

Implicit Types (Hn : n = n') (Hm : m = m') (Ho : o = o') (Hp : p = p').


Lemma gstack_cast_l 
  dl dr (Hn : n = n') (Hm : m = m') : 
  stack n' m' o p (cast Hn Hm dl) dr = 
    cast (Nat.add^~o @ Hn) (Nat.add^~p @ Hm) (stack n m o p dl dr).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.


Lemma gstack_cast_r dl dr Ho Hp : 
  stack n m o' p' dl (cast Ho Hp dr) = 
    cast (Nat.add n @ Ho) (Nat.add m @ Hp) (stack n m o p dl dr).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma gstack_cast dl dr Hn Hm Ho Hp : 
  stack n' m' o' p' (cast Hn Hm dl) (cast Ho Hp dr) = 
    cast (Nat.add @2 Hn, Ho) (Nat.add @2 Hm, Hp) (stack n m o p dl dr).
Proof.
  subst.
  now rewrite 3 cast_id.
Qed.

Lemma cast_gstack_back_l Hn Hm dl dr Hno Hmp : 
  cast Hno Hmp (stack n m o p dl dr) = 
  stack n' m' o' p' (cast Hn Hm dl) 
    (cast (add_cancel_l Hn Hno) (add_cancel_l Hm Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gstack_back_r Ho Hp dl dr Hno Hmp : 
  cast Hno Hmp (stack n m o p dl dr) = 
  stack n' m' o' p' (cast (add_cancel_r Ho Hno) (add_cancel_r Hp Hmp) dl) 
    (cast Ho Hp dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gstack_id_l dl dr Hno Hmp :
  cast Hno Hmp (stack n m o p dl dr) =
  stack n m o' p' dl (cast (add_cancel_l refl Hno) (add_cancel_l refl Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gstack_id_r dl dr Hno Hmp :
  cast Hno Hmp (stack n m o p dl dr) =
  stack n' m' o p (cast (add_cancel_r refl Hno) (add_cancel_r refl Hmp) dl) dr.
Proof.
  solve_cast.
Qed.


Lemma gcompose_cast_l dl dr Hn Hm : 
  compose n' m' o (cast Hn Hm dl) dr = 
  cast Hn refl (compose n m o dl (cast (<- Hm) refl dr)).
Proof.
  subst.
  now rewrite !cast_id.
Qed.

Lemma gcompose_cast_r dl dr Hm Ho : 
  compose n m' o' dl (cast Hm Ho dr) = 
  cast refl Ho (compose n m o (cast refl (<- Hm) dl) dr).
Proof.
  subst.
  now rewrite !cast_id.
Qed.

Lemma gcompose_cast_eq_mid dl dr Hn Hm Hm' Ho : 
  compose n' m' o' (cast Hn Hm dl) (cast Hm' Ho dr) = 
  cast Hn Ho (compose n m o dl dr).
Proof.
  solve_cast.
Qed.


Lemma gcompose_cast_l_eq_mid dl dr Hn (Hm' : m = m) : 
  compose n' m o (cast Hn Hm' dl) dr = 
  cast Hn refl (compose n m o dl dr).
Proof.
  subst.
  now rewrite !cast_id.
Qed.

Lemma gcompose_cast_r_eq_mid dl dr (Hm' : m = m) Ho : 
  compose n m o' dl (cast Hm' Ho dr) = 
  cast refl Ho (compose n m o dl dr).
Proof.
  subst.
  now rewrite !cast_id.
Qed.

Lemma cast_gcompose_distr_at k (Hk : m = k)
  (dl : D n m) (dr : E m o) Hn Ho : 
  cast Hn Ho (compose n m o dl dr) = 
  compose n' k o' (cast Hn Hk dl) (cast Hk Ho dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gcompose_distr dl dr Hn Ho :
  cast Hn Ho (compose n m o dl dr) = 
  compose n' m o' (cast Hn refl dl) (cast refl Ho dr).
Proof.
  solve_cast.
Qed.


Lemma gadd_cast_l dl dr Hn Hm : 
  add n' m' (cast Hn Hm dl) dr = 
  cast Hn Hm (add n m dl (cast (<- Hn) (<- Hm) dr)).
Proof.
  solve_cast.
Qed.

Lemma gadd_cast_r dl dr Hn Hm : 
  add n' m' dl (cast Hn Hm dr) = 
  cast Hn Hm (add n m (cast (<- Hn) (<- Hm) dl) dr).
Proof.
  solve_cast.
Qed.

Lemma gadd_cast dl dr Hn Hm Hn' Hm' : 
  add n' m' (cast Hn Hm dl) (cast Hn' Hm' dr) = 
  cast Hn Hm (add n m dl dr).
Proof.
  solve_cast.
Qed.



Lemma gkron_cast_l 
  dl dr (Hn : n = n') (Hm : m = m') : 
  kron n' m' o p (cast Hn Hm dl) dr = 
    cast (Nat.mul^~o @ Hn) (Nat.mul^~p @ Hm) (kron n m o p dl dr).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.


Lemma gkron_cast_r dl dr Ho Hp : 
  kron n m o' p' dl (cast Ho Hp dr) = 
    cast (Nat.mul n @ Ho) (Nat.mul m @ Hp) (kron n m o p dl dr).
Proof.
  subst.
  now rewrite 2 cast_id.
Qed.

Lemma gkron_cast dl dr Hn Hm Ho Hp : 
  kron n' m' o' p' (cast Hn Hm dl) (cast Ho Hp dr) = 
    cast (Nat.mul @2 Hn, Ho) (Nat.mul @2 Hm, Hp) (kron n m o p dl dr).
Proof.
  subst.
  now rewrite 3 cast_id.
Qed.

Lemma cast_gkron_back_l_gen Hn Hm Hnz Hnz' dl dr Hno Hmp : 
  cast Hno Hmp (kron n m o p dl dr) = 
  kron n' m' o' p' (cast Hn Hm dl) 
    (cast (mul_cancel_lg Hn Hnz Hno) (mul_cancel_lg Hm Hnz' Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_back_l Hn Hm Hnz Hnz' dl dr Hno Hmp : 
  cast Hno Hmp (kron n m o p dl dr) = 
  kron n' m' o' p' (cast Hn Hm dl) 
    (cast (mul_cancel_l Hn Hnz Hno) (mul_cancel_l Hm Hnz' Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_back_r_gen Ho Hp Hnz Hnz' dl dr Hno Hmp : 
  cast Hno Hmp (kron n m o p dl dr) = 
  kron n' m' o' p' (cast (mul_cancel_rg Ho Hnz Hno) (mul_cancel_rg Hp Hnz' Hmp) dl) 
    (cast Ho Hp dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_back_r Ho Hp Hnz Hnz' dl dr Hno Hmp : 
  cast Hno Hmp (kron n m o p dl dr) = 
  kron n' m' o' p' (cast (mul_cancel_r Ho Hnz Hno) (mul_cancel_r Hp Hnz' Hmp) dl) 
    (cast Ho Hp dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_id_l_gen Hnz Hnz' dl dr Hno Hmp :
  cast Hno Hmp (kron n m o p dl dr) =
  kron n m o' p' dl (cast (mul_cancel_lg refl Hnz Hno) (mul_cancel_lg refl Hnz' Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_id_l Hnz Hnz' dl dr Hno Hmp :
  cast Hno Hmp (kron n m o p dl dr) =
  kron n m o' p' dl (cast (mul_cancel_l refl Hnz Hno) (mul_cancel_l refl Hnz' Hmp) dr).
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_id_r_gen Hnz Hnz' dl dr Hno Hmp :
  cast Hno Hmp (kron n m o p dl dr) =
  kron n' m' o p (cast (mul_cancel_r refl Hnz Hno) (mul_cancel_r refl Hnz' Hmp) dl) dr.
Proof.
  solve_cast.
Qed.

Lemma cast_gkron_id_r Hnz Hnz' dl dr Hno Hmp :
  cast Hno Hmp (kron n m o p dl dr) =
  kron n' m' o p (cast (mul_cancel_r refl Hnz Hno) (mul_cancel_r refl Hnz' Hmp) dl) dr.
Proof.
  solve_cast.
Qed.

End gcast_facts.




Module CastNotation.

Notation "'cast' '$' '$' d" := (cast _ _ d) (only printing, at level 10, d at level 9) : cast_scope.

End CastNotation.
