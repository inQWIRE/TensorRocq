Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Auxillary.Aux_stdpp.
From TensorRocq Require Export Summable.

(* FIXME: Move *)
Definition vec_rel {A n} (R : relation A) : relation (vec A n) :=
  fun v w => Vector.fold_right and (vzip_with R v w) True.

Lemma vec_rel_alt {A n} (R : relation A) (v w : vec A n) :
  vec_rel R v w <-> Forall2 R v w.
Proof.
  unfold vec_rel.
  induction n.
  - inv_all_vec_fin.
    done.
  - inv_vec v; inv_vec w; intros hw w hv v.
    cbn.
    rewrite Forall2_cons.
    rewrite IHn.
    done.
Qed.


Lemma vec_rel_lookup {A n} (R : relation A) (v w : vec A n) :
  vec_rel R v w <-> (forall i, R (v !!! i) (w !!! i)).
Proof.
  rewrite vec_rel_alt.
  rewrite Forall2_vlookup.
  done.
Qed.

#[export] Instance vec_rel_refl {A n} (R : relation A) (HR : Reflexive R) :
  Reflexive (vec_rel (n:=n) R).
Proof.
  intros v.
  rewrite vec_rel_alt.
  done.
Qed.

#[export] Instance vec_rel_symm {A n} (R : relation A) (HR : Symmetric R) :
  Symmetric (vec_rel (n:=n) R).
Proof.
  intros v w.
  rewrite 2 vec_rel_alt.
  done.
Qed.

#[export] Instance vec_rel_trans {A n} (R : relation A) (HR : Transitive R) :
  Transitive (vec_rel (n:=n) R).
Proof.
  intros v w u.
  rewrite 3 vec_rel_alt.
  now intros ->.
Qed.

#[export] Instance vec_rel_equiv {A n} (R : relation A) (HR : Equivalence R) :
  Equivalence (vec_rel (n:=n) R).
Proof.
  split; apply _.
Qed.

#[export] Instance vmap_mor {A B RA RB n} (f : A -> B) (Hf : Proper (RA ==> RB) f) :
  Proper (vec_rel RA ==> vec_rel RB) (vmap (n:=n) f).
Proof.
  intros v w Heq.
  rewrite vec_rel_lookup in Heq.
  rewrite vec_rel_lookup.
  intros i.
  rewrite 2 vlookup_map.
  now f_equiv.
Qed.

#[export] Instance vzip_with_mor {A B C RA RB RC n} (f : A -> B -> C)
  (Hf : Proper (RA ==> RB ==> RC) f) :
  Proper (vec_rel RA ==> vec_rel RB ==> vec_rel RC) (vzip_with (n:=n) f).
Proof.
  intros v v' Hv w w' Hw.
  rewrite @vec_rel_lookup in Hv, Hw |- *.
  intros i.
  rewrite 2 vlookup_zip_with.
  now f_equiv.
Qed.

#[export] Instance vcons_mor {A RA} {n} :
  Proper (RA ==> vec_rel RA ==> vec_rel RA) (fun a v => @vcons A a n v).
Proof.
  intros h h' Hh v v' Hv.
  rewrite @vec_rel_alt in Hv |- *.
  cbn.
  now rewrite Forall2_cons.
Qed.

#[export] Instance vapp_mor {A RA} {n m} :
  Proper (vec_rel RA ==> vec_rel RA ==> vec_rel RA) (@vapp A n m).
Proof.
  intros v v' Hv w w' Hw.
  rewrite @vec_rel_alt in Hv, Hw |- *.
  cbn.
  rewrite 2 vec_to_list_app.
  now apply Forall2_app.
Qed.

#[export] Instance vlookup_mor {A} {RA : relation A} {n} :
  Proper (eq ==> vec_rel (n:=n) RA ==> RA) lookup_total.
Proof.
  intros i ? <- v v' Hv.
  rewrite vec_rel_lookup in Hv.
  done.
Qed.

#[export] Instance vsplitl_mor {A} {RA : relation A} {n m} :
  Proper (vec_rel RA ==> vec_rel RA) (@vsplitl A n m).
Proof.
  intros v v' Hv.
  rewrite @vec_rel_lookup in Hv |- *.
  intros i.
  rewrite 2 lookup_vsplitl.
  done.
Qed.

#[export] Instance vsplitr_mor {A} {RA : relation A} {n m} :
  Proper (vec_rel RA ==> vec_rel RA) (@vsplitr A n m).
Proof.
  intros v v' Hv.
  rewrite @vec_rel_lookup in Hv |- *.
  intros i.
  rewrite 2 lookup_vsplitr.
  done.
Qed.




(* A matrix with dimensions [n] and [m] with values in [R] *)
Definition Matrix (R : Type) (n m : nat) :=
  vec (vec R m) n.




(* The default equivalence relation on tensors with arguments in a
  [Summable] type [A] and values in a [SemiRing], [R]. Two tensors
  are equivalent if they agree (up to the semiring equality [req]
  of [R]) on all arguments whose elements are [SummedElement]s, i.e.
  appear in the list of summed elements of [A].
  This is registered as the [Equiv] ([(≡)]) instance for tensors. *)
Definition matrix_rel {R} (RR : relation R)
  {n m} : relation (Matrix R n m) :=
  vec_rel (vec_rel RR).

#[global] Instance Matrix_equiv `{Equiv R}
  {n m} : Equiv (Matrix R n m) := matrix_rel equiv.

Section VectorOps.

Definition vec_dot `{SR : SemiRing R rO rI radd rmul req}
  {n} (v w : vec R n) : R :=
  Rlist_sum (vzip_with rmul v w).



End VectorOps.

Section MatrixOps.

  Context {R : Type}.

  Let Matrix := (Matrix R).

  Definition fun_to_mx {n m} (f : fin n -> fin m -> R) : Matrix n m :=
    fun_to_vec (λ i, fun_to_vec (λ j, f i j)).

  Definition mx_to_fun {n m} (A : Matrix n m) (i : fin n) (j : fin m) : R :=
    A !!! i !!! j.
  
  #[local] Coercion mx_to_fun : Matrix >-> Funclass.

  Definition const_matrix {n m} (r : R) : Matrix n m :=
    fun_to_mx (λ _ _, r).

  Definition id_matrix `{SR : SemiRing R rO rI radd rmul req}
    (n : nat) : Matrix n n :=
    fun_to_mx (λ i j, if decide (i = j) then rI else rO).

  Definition J_matrix `{SR : SemiRing R rO rI radd rmul req}
    (n m : nat) : Matrix n m :=
    const_matrix rI.

  Definition zero_matrix `{SR : SemiRing R rO rI radd rmul req}
    (n m : nat) : Matrix n m :=
    const_matrix rO.

  Definition mx_row {n m} (A : Matrix n m) (i : fin n) : vec R m :=
    A !!! i.

  Definition mx_col {n m} (A : Matrix n m) (i : fin m) : vec R n :=
    vmap (.!!! i) A.

  Definition compose_matrix `{SR : SemiRing R rO rI radd rmul req}
    {n m o} (t : Matrix n m) (t' : Matrix m o) :
    Matrix n o :=
    fun_to_mx (λ i j, vec_dot (mx_row t i) (mx_col t' j)).

  Definition kron_matrix `{SR : SemiRing R rO rI radd rmul req}
    {n m n' m'} (t : Matrix n m) (t' : Matrix n' m') :
    Matrix (n * n') (m * m') :=
    fun_to_mx (λ i j, rmul (t (fin_split i).1 (fin_split j).1) (t' (fin_split i).2 (fin_split j).2)).

  Definition map_matrix {R'} (f : R -> R') {n m} (A : Matrix n m) : Definitions.Matrix R' n m :=
    vmap (vmap f) A.

  Definition mx_hblock {n m m'} (A : Matrix n m) (B : Matrix n m') : Matrix n (m + m') :=
    vzip_with (+++) A B.

  Definition mx_vblock {n n' m} (A : Matrix n m) (B : Matrix n' m) : Matrix (n + n') m :=
    A +++ B.

  (* Definition cup_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n} :
    Matrix 0 (n + n) := fun v w =>
    delta_tensor (vsplitl w) (vsplitr w).

  Definition cap_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n} :
    Matrix (n + n) 0 := fun v w =>
    delta_tensor (vsplitl v) (vsplitr v).

  Definition swap_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m} :
    Matrix (n + m) (m + n) := fun v w =>
    delta_tensor v (vsplitr w +++ vsplitl w).

  Definition delta_spider_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m} : Matrix n m :=
    fun v w => ∑ a : A, if decide (Forall (eq a) (v +++ w)) then rI else rO.

  Definition delta_spider_tensor' `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
      (vi : vec positive n) (wi : vec positive m) : Matrix n m :=
    fun v w =>
      if decide (equal_on_indices (vzip (vi +++ wi) (v +++ w))) then rI else rO.

  Definition copy_tensor {A} `{SR : SemiRing R rO rI radd rmul req}
    (k : nat) {n m} (f : Matrix n m) :
      Matrix (n * k) (m * k) :=
    fun v w =>
      Rlist_prod (Vector.map2 f (vunjoin' v) (vunjoin' w)).

  Definition delta_spider_tensor_bundled `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} k n m : Matrix (n * k) (m * k) :=
    copy_tensor k delta_spider_tensor.

  Definition tensor_11_to_fun {A} (t : Matrix 1 1) : A -> A -> R :=
    fun a b => t [# a] [# b].

  Definition stack_n_tensor_1 `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req} {n} (t : Matrix 1 1) : Matrix n n :=
    fun v w =>
    Vector.fold_right rmul (vzip_with (tensor_11_to_fun t) v w) rI.

  Fixpoint n_stack_tensor `{SA : Summable A,
    SR : SemiRing R rO rI radd rmul req}
    k {n m} (t : Matrix n m) : Matrix (k * n) (k * m) :=
    match k with
    | 0 => const_tensor rI
    | S k => stack_tensor t (n_stack_tensor k t)
    end.

  Definition tensor_to_dimensionless `{SR : SemiRing R rO rI radd rmul req}
    {A n m} (t : Matrix n m) : @DimensionlessTensor R A :=
    fun n' m' v' w' =>
    default rO (vec_cast_opt v' n ≫= λ v, vec_cast_opt w' m ≫= λ w, Some (t v w)).

  Definition fn_delta_tensor_l `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
    (f : vec A n -> vec A m) : Matrix n m :=
    fun v w => delta_tensor (f v) w.

  Definition fn_delta_tensor_r `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} {n m}
    (f : vec A m -> vec A n) : Matrix n m :=
    fun v w => delta_tensor v (f w).

  Definition assoc_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} n m o : Tensor (n + m + o) (n + (m + o)) A :=
    fn_delta_tensor_l (fun v => vsplitl (vsplitl v) +++ (vsplitr (vsplitl v) +++ vsplitr v)).

  Definition invassoc_tensor `{SA : Summable A, EqA : EqDecision A,
    SR : SemiRing R rO rI radd rmul req} n m o : Tensor (n + (m + o)) (n + m + o) A :=
    fn_delta_tensor_l (fun v => (vsplitl v +++ vsplitl (vsplitr v)) +++ vsplitr (vsplitr v)). *)

  Definition perm_matrix `{SR : SemiRing R rO rI radd rmul req}
    {n m} (f : fin n -> fin m) : Matrix n m :=
    fun_to_mx (λ i j, if decide (f i = j) then rI else rO).

  Definition prepermute_matrix_l {n m o} (f : fin n -> fin m) (t : Matrix m o) : Matrix n o :=
    permute_vec f t.

  Definition prepermute_matrix_r {n m o} (f : fin m -> fin o) (t : Matrix n o) : Matrix n m :=
    vmap (permute_vec f) t.

  Definition prepermute_matrix {n m n' m'}
    (fl : fin n -> fin n') (fr : fin m -> fin m')
    (t : Matrix n' m') : Matrix n m :=
    permute_vec fl (vmap (permute_vec fr) t).

  Definition mx_to_vec_rowmajor {n m} (A : Matrix n m) : vec R (n * m) :=
    vjoin A.

  Definition mx_to_vec_colmajor {n m} (A : Matrix n m) : vec R (m * n) :=
    vjoin' A.

  Definition mx_of_vec_rowmajor {n m} (v : vec R (n * m)) : Matrix n m :=
    vunjoin v.

  Definition mx_of_vec_colmajor {n m} (v : vec R (m * n)) : Matrix n m :=
    vunjoin' v.

  Definition mx_transpose {n m} (A : Matrix n m) : Matrix m n :=
    fun_to_mx (λ i j, A j i).

  Definition cast_matrix {n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix n m) : Matrix n' m' :=
    match Nat.eq_dec n n' with
    | left Hn' =>
      match Nat.eq_dec m m' with
      | left Hm' => match Hn', Hm' with
        | eq_refl, eq_refl => A
        end
      | right HFm => False_rect _ (HFm Hm)
      end
    | right HFn => False_rect _ (HFn Hn)
    end.

  #[global] Arguments cast_matrix {!_ !_ !_ !_} !_ !_ _ / : assert.
(*
  #[global] Arguments const_tensor {_} {_ _} _ _ _ / : assert.
  #[global] Arguments delta_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments compose_tensor {_ _} {_ _ _ _ _ _} {_ _ _} (_ _) _ _ / : assert.
  #[global] Arguments stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
  #[global] Arguments swapped_stack_tensor {_ _} {_ _ _ _ _ _} {_ _ _ _} (_ _) _ _ / : assert.
  #[global] Arguments join_stack_1_tr_bl {_ _} {_ _ _ _ _ _} {_ _ _} (_) _ _ / : assert.
  #[global] Arguments join_stack_tr_bl {_ _} {_ _ _ _ _ _} {_ !_ _} (_) / _ _ : assert.
  #[global] Arguments join_stack_1_tl_tr {_ _} {_ _ _ _ _ _} {_ _} (_) _ _ / : assert.
  #[global] Arguments join_stack_tl_tr {_ _} {_ _ _ _ _ _} {!_ _ _} (_) / _ _ : assert.

  #[global] Arguments cup_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments cap_tensor {_ _ _} {_ _ _ _ _ _} {_} _ _ / : assert.
  #[global] Arguments swap_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ / : assert.

  #[global] Arguments delta_spider_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ / : assert.
  #[global] Arguments delta_spider_tensor' {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ _ / : assert.

  #[global] Arguments copy_tensor {_} {_ _ _ _ _ _} _ {_ _} _ _ _ / : assert.
  #[global] Arguments delta_spider_tensor_bundled {_ _ _} {_ _ _ _ _ _} _ {_ _} _ _ / : assert.

  #[global] Arguments stack_n_tensor_1 {_ _} {_ _ _ _ _ _} {_} _ _ _ / : assert.
  #[global] Arguments n_stack_tensor {_ _} {_ _ _ _ _ _} !_ {_ _} / _ _ _ : assert.
  #[global] Arguments tensor_to_dimensionless {_ _ _ _ _ _} {_} {_ _} _ _ _ _ _ / : assert.
  #[global] Arguments tensor_11_to_fun {_} _ _ _ / : assert.

  #[global] Arguments fn_delta_tensor_l {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.
  #[global] Arguments fn_delta_tensor_r {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments assoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments invassoc_tensor {_ _ _} {_ _ _ _ _ _} _ _ _ _ _ / : assert.
  #[global] Arguments perm_tensor {_ _ _} {_ _ _ _ _ _} {_ _} _ _ _ / : assert.

  #[global] Arguments permute_tensor_l {_ _ _ _} _ _ _ _ / : assert.
  #[global] Arguments permute_tensor_r {_ _ _ _} _ _ _ _ / : assert.
  #[global] Arguments permute_tensor {_ _ _ _ _} _ _ _ _ _ / : assert.

  #[global] Arguments tensor_wrap_l_under {_ _ _ _} _ _ _ / : assert.
  #[global] Arguments tensor_wrap_r_under {_ _ _ _} _ _ _ / : assert.

  #[global] Arguments strong_permute_tensor {_ _ _ _ _} _ _ _ _ / : assert. *)

End MatrixOps.

Declare Scope Matrix_scope.
Delimit Scope Matrix_scope with MX.
Bind Scope Matrix_scope with Matrix.

Notation "'I'" := id_matrix (at level 1) : Matrix_scope.
Notation "'J'" := J_matrix (at level 1) : Matrix_scope.
Notation "'Zero'" := zero_matrix (at level 1) : Matrix_scope.

#[global] Coercion mx_to_fun : Matrix >-> Funclass.
