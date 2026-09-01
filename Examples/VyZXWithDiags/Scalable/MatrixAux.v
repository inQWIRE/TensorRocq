From TensorRocqEx Require NonZXAux.

From TensorRocq Require Export Matrix.
Import vector Aux_stdpp.
Import NonZXAux.prf_notations.


Lemma vtl_mx_vblock {n n' m} (A : Matrix bool (S (S n)) (S m)) (B : Matrix bool (S n') (S m)) :
  vtl (mx_vblock A B) = mx_vblock (vtl A) B.
Proof.
  inv_vec A; done.
Qed.




#[export] Instance bool_leibniz : LeibnizEquiv bool.
Proof.
  intros ? ?; easy.
Qed.
#[export] Instance vec_equiv {A} `{Equiv A} {n} : Equiv (vec A n) := vec_rel equiv.
#[export] Instance vec_leibniz `{LeibnizEquiv A} {n} : LeibnizEquiv (vec A n).
Proof.
  intros v w Hvw.
  apply vec_eq.
  unfold equiv, vec_equiv in Hvw.
  rewrite vec_rel_lookup in Hvw.
  intros i.
  apply leibniz_equiv, Hvw.
Qed.


Lemma cast_matrix_alt {n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix bool n m) :
  cast_matrix Hn Hm A = Vector.cast (vmap (λ v, Vector.cast v Hm) A) Hn.
Proof.
  subst.
  rewrite cast_matrix_id, Aux_stdpp_base.cast_id.
  rewrite vmap_id' by now intros; rewrite Aux_stdpp_base.cast_id.
  done.
Qed.


Lemma mx_vblock_nil_r {n m} (A : Matrix bool n m) :
  mx_vblock A [#] = cast_matrix add_0_r' eq_refl A.
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_vblock.
  induction i using fin_add_inv; [|inv_all_vec_fin].
  rewrite fin_sum_case_L.
  cbn.
  rewrite mlookup_cast.
  rewrite fcast_id.
  f_equal.
  apply fin_to_nat_inj.
  now rewrite fin_to_nat_cast, fin_to_nat_L.
Qed.

Lemma mx_hblock_cons {R n m m'} vA A vB B :
  @mx_hblock R (S n) m m' (vA ::: A) (vB ::: B) =
  (vA +++ vB) ::: mx_hblock A B.
Proof.
  done.
Qed.

Lemma mx_hblock_nil_l {n m'} (A : Matrix bool n 0) (B : Matrix bool n m') :
  mx_hblock A B = B.
Proof.
  apply vec_eq.
  intros i.
  unfold mx_hblock.
  rewrite vlookup_zip_with.
  cbn.
  unfold Matrix in *.
  induction (A !!! i) using vec_0_inv.
  done.
Qed.

Lemma mx_hblock_nil_r {n m} (A : Matrix bool n m) (B : Matrix bool n 0) :
  mx_hblock A B = cast_matrix eq_refl add_0_r' A.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_hblock, mlookup_cast.
  induction j using fin_add_inv; [|inv_all_vec_fin].
  rewrite fin_sum_case_L.
  cbn.
  f_equal; apply fin_to_nat_inj; now rewrite fin_to_nat_cast, ?fin_to_nat_L.
Qed.


(* FIXME: Move *)
Lemma mx_transpose_involutive {R n m} : Cancel eq (@mx_transpose R n m) mx_transpose.
Proof.
  intros A.
  apply mx_eq.
  intros i j.
  now rewrite 2 mlookup_transpose.
Qed.
Lemma mx_transpose_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_transpose (mx_vblock A B) = mx_hblock (mx_transpose A) (mx_transpose B).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_hblock, mlookup_transpose, mlookup_vblock.
  destruct (fin_sum_case j); cbn; now rewrite mlookup_transpose.
Qed.
Lemma mx_transpose_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_transpose (mx_hblock A B) = mx_vblock (mx_transpose A) (mx_transpose B).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_vblock, mlookup_transpose, mlookup_hblock.
  destruct (fin_sum_case i); cbn; now rewrite mlookup_transpose.
Qed.
Definition mx_splitl {R n m m'} (A : Matrix R n (m + m')) :=
  vmap vsplitl A.
Definition mx_splitr {R n m m'} (A : Matrix R n (m + m')) :=
  vmap vsplitr A.
Lemma mx_hblock_split {R n m m'} (A : Matrix R n (m + m')) :
  mx_hblock (mx_splitl A) (mx_splitr A) = A.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_zip_with, 2 vlookup_map.
  apply app_vsplit.
Qed.
Lemma mx_splitl_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_splitl (mx_hblock A B) = A.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_map, vlookup_zip_with.
  apply vsplitl_app.
Qed.
Lemma mx_splitr_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') :
  mx_splitr (mx_hblock A B) = B.
Proof.
  apply vec_eq; intros i.
  unfold mx_hblock, mx_splitl, mx_splitr.
  rewrite vlookup_map, vlookup_zip_with.
  apply vsplitr_app.
Qed.
Definition mx_splitu {R n n' m} (A : Matrix R (n + n') m) :=
  vsplitl A.
Definition mx_splitd {R n n' m} (A : Matrix R (n + n') m) :=
  vsplitr A.
Lemma mx_vblock_split {R n n' m} (A : Matrix R (n + n') m) :
  mx_vblock (mx_splitu A) (mx_splitd A) = A.
Proof.
  apply app_vsplit.
Qed.
Lemma mx_splitu_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_splitu (mx_vblock A B) = A.
Proof.
  apply vsplitl_app.
Qed.
Lemma mx_splitd_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) :
  mx_splitd (mx_vblock A B) = B.
Proof.
  apply vsplitr_app.
Qed.


Lemma matrix_nonempty_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HProw : forall m (A : Matrix R 1 m), P _ _ A)
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n as [|[|n]]; [now auto..|].
  induction A as [vA A] using vec_S_inv.
  change (vA ::: A) with (mx_vblock [#vA] A).
  apply (HPvblock 1 (S n) _ [#vA] A); [lia..|apply IHn|apply IHn]; lia.
Qed.

Lemma matrix_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HProw : forall m (A : Matrix R 1 m), P _ _ A)
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  induction n; [auto|].
  induction A as [vA A] using vec_S_inv.
  change (vA ::: A) with (mx_vblock [#vA] A).
  change (S n) with (1 + n).
  apply HPvblock; [auto|].
  auto.
Qed.




Lemma matrix_nonempty_hblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HPcol : forall n (A : Matrix R n 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct n; [now auto|].
  induction m as [m IHm] using lt_wf_ind.
  destruct m as [|[|m]]; [now auto..|].
  rewrite <- (@mx_hblock_split _ _ 1 (S m) A).
  change (S (S m)) with (1 + S m).
  apply HPhblock; [lia..|apply IHm|apply IHm]; lia.
Qed.

Lemma matrix_hblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HPcol : forall n (A : Matrix R n 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  induction m; [auto|].
  rewrite <- (@mx_hblock_split _ _ 1 m A).
  change (S m) with (1 + m).
  apply HPhblock; [auto|].
  auto.
Qed.


Lemma matrix_nonempty_hblock_vblock_ind {R} (P : forall n m, Matrix R n m -> Prop)
  (HPnil_l : forall m (A : Matrix R 0 m), P _ _ A)
  (HPnil_r : forall n (A : Matrix R n 0), P _ _ A)
  (HP_1_1 : forall (A : Matrix R 1 1), P _ _ A)
  (HPhblock : forall n m m' (A : Matrix R n m) (B : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_hblock A B))
  (HPvblock : forall n n' m (A : Matrix R n m) (B : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A -> P _ _ B -> P _ _ (mx_vblock A B)) :
  forall n m A, P n m A.
Proof.
  intros n m A.
  destruct n; [now auto|].
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m; [auto|].
    change (S (S m)) with (1 + S m) in *.
    rewrite <- (mx_hblock_split A).
    apply HPhblock; [lia..|auto|auto].
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A).
    apply HPvblock; [lia..|apply IHn|apply IHn]; lia.
Qed.


(* FIXME: Move *)
Definition mx_zip_with {R R' R''} (f : R -> R' -> R'')
  {n m} (A : Matrix R n m) (B : Matrix R' n m) : Matrix R'' n m :=
  vzip_with (vzip_with f) A B.

Lemma mlookup_zip_with {R R' R''} (f : R -> R' -> R'')
  {n m} (A : Matrix R n m) (B : Matrix R' n m) i j :
  mx_zip_with f A B i j = f (A i j) (B i j).
Proof.
  unfold mx_zip_with, mx_to_fun, Matrix.
  now rewrite 2 vlookup_zip_with.
Qed.

#[export] Instance mx_zip_with_mor {R R' R''}
  `{Equiv R, Equiv R', Equiv R''} (f : R -> R' -> R'')
  {Hf : Proper (equiv ==> equiv ==> equiv) f}
  {n m} : Proper (equiv ==> equiv ==> equiv) (mx_zip_with f (n:=n) (m:=m)).
Proof.
  intros A A' HA B B' HB.
  apply mx_equiv.
  intros i j.
  rewrite 2 mlookup_zip_with.
  f_equiv; now apply mx_equiv.
Qed.


Definition mx_plus {R} `{SR : SemiRing R rO rI radd rmul req}
  {n m} (A B : Matrix R n m) := mx_zip_with radd A B.

Definition mx_vec_prod {R} `{SR : SemiRing R rO rI radd rmul req}
  {n m} (A : Matrix R n m) (v : vec R m) : vec R n :=
  vmap (vec_dot v) A.

Section mx_plus.


Local Open Scope Matrix_scope.


Context {R} `{SR : SemiRing R rO rI radd rmul req}.



Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.


Lemma mlookup_plus {n m} (A B : Matrix R n m) i j :
  mx_plus A B i j = A i j + B i j.
Proof.
  apply mlookup_zip_with.
Qed.

#[export] Instance mx_plus_mor
  {n m} : Proper (equiv ==> equiv ==> equiv) (mx_plus (n:=n) (m:=m)).
Proof.
  apply mx_zip_with_mor, _.
Qed.

(* TODO: Refactor these to be mx_zip_with lemmas *)
Lemma mx_plus_hblock {n m m'} (A A' : Matrix R n m) (B B' : Matrix R n m') :
  mx_plus (mx_hblock A B) (mx_hblock A' B') =
  mx_hblock (mx_plus A A') (mx_plus B B').
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_hblock.
  induction j as [j|j] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn; now rewrite mlookup_plus.
  - rewrite fin_sum_case_R; cbn; now rewrite mlookup_plus.
Qed.
Lemma mx_plus_vblock {n n' m} (A A' : Matrix R n m) (B B' : Matrix R n' m) :
  mx_plus (mx_vblock A B) (mx_vblock A' B') =
  mx_vblock (mx_plus A A') (mx_plus B B').
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_vblock.
  induction i as [i|i] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn; now rewrite mlookup_plus.
  - rewrite fin_sum_case_R; cbn; now rewrite mlookup_plus.
Qed.

Lemma mx_row_hblock {n m m'}
  (A : Matrix R n m) (B : Matrix R n m') i :
  mx_row (mx_hblock A B) i = mx_row A i +++ mx_row B i.
Proof.
  unfold mx_row, mx_hblock, Matrix.
  rewrite vlookup_zip_with.
  done.
Qed.

Lemma mx_col_vblock {n n' m}
  (A : Matrix R n m) (B : Matrix R n' m) i :
  mx_col (mx_vblock A B) i = mx_col A i +++ mx_col B i.
Proof.
  unfold mx_col, mx_vblock, Matrix.
  rewrite Vector.map_append.
  done.
Qed.

Lemma compose_matrix_hblock_vblock {n m m' o}
  (A : Matrix R n m) (B : Matrix R m o)
  (C : Matrix R n m') (D : Matrix R m' o) :
  compose_matrix (mx_hblock A C) (mx_vblock B D) ≡
  mx_plus (compose_matrix A B) (compose_matrix C D).
Proof.
  apply mx_equiv.
  intros i j.
  rewrite mlookup_plus, 3 mlookup_compose.
  rewrite mx_row_hblock, mx_col_vblock.
  rewrite vec_dot_app.
  done.
Qed.

Lemma mx_row_vblock {n n' m}
  (A : Matrix R n m) (B : Matrix R n' m) i :
  mx_row (mx_vblock A B) i =
  sum_rect (λ _, _) (mx_row A) (mx_row B) (fin_sum_case i).
Proof.
  unfold mx_row, mx_vblock, Matrix.
  rewrite lookup_vapp.
  done.
Qed.

Lemma mx_col_hblock {n m m'}
  (A : Matrix R n m) (B : Matrix R n m') i :
  mx_col (mx_hblock A B) i =
  sum_rect (λ _, _) (mx_col A) (mx_col B) (fin_sum_case i).
Proof.
  unfold mx_col, mx_hblock, Matrix.
  apply vec_eq; intros j.
  rewrite vlookup_map, vlookup_zip_with.
  rewrite lookup_vapp.
  destruct (fin_sum_case i); cbn; now rewrite vlookup_map.
Qed.

Lemma compose_matrix_vblock_l {n n' m o}
  (A : Matrix R n m) (B : Matrix R n' m)
  (C : Matrix R m o) :
  compose_matrix (mx_vblock A B) C =
  mx_vblock (compose_matrix A C) (compose_matrix B C).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_compose, mlookup_vblock.
  rewrite mx_row_vblock.
  induction i as [i|i] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn -[vec_dot].
    now rewrite mlookup_compose.
  - rewrite fin_sum_case_R; cbn -[vec_dot].
    now rewrite mlookup_compose.
Qed.


Lemma compose_matrix_hblock_r {n m o o'}
  (A : Matrix R n m) (B : Matrix R m o)
  (C : Matrix R m o') :
  compose_matrix A (mx_hblock B C) =
  mx_hblock (compose_matrix A B) (compose_matrix A C).
Proof.
  apply mx_eq; intros i j.
  rewrite mlookup_compose, mlookup_hblock.
  rewrite mx_col_hblock.
  induction j as [j|j] using fin_add_inv.
  - rewrite fin_sum_case_L; cbn -[vec_dot].
    now rewrite mlookup_compose.
  - rewrite fin_sum_case_R; cbn -[vec_dot].
    now rewrite mlookup_compose.
Qed.

Lemma compose_matrix_0_mid {n o} (A : Matrix R n 0) (B : Matrix R 0 o) :
  compose_matrix A B = const_matrix 0.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_compose', mlookup_const.
  rewrite sum_of_fin_0.
  done.
Qed.



End mx_plus.



Lemma matrix_double_nonempty_hblock_vblock_ind {R}
  (P : forall n m, Matrix R n m -> Matrix R n m -> Prop)
  (HPnil_l : forall m (A B : Matrix R 0 m), P _ _ A B)
  (HPnil_r : forall n (A B : Matrix R n 0), P _ _ A B)
  (HP_1_1 : forall (A B : Matrix R 1 1), P _ _ A B)
  (HPhblock : forall n m m' (A A' : Matrix R n m) (B B' : Matrix R n m'),
    n <> 0 -> m <> 0 -> m' <> 0 ->
    P _ _ A A' -> P _ _ B B' -> P _ _ (mx_hblock A B) (mx_hblock A' B'))
  (HPvblock : forall n n' m (A A' : Matrix R n m) (B B' : Matrix R n' m),
    n <> 0 -> n' <> 0 -> m <> 0 ->
    P _ _ A A' -> P _ _ B B' -> P _ _ (mx_vblock A B) (mx_vblock A' B')) :
  forall n m A B, P n m A B.
Proof.
  intros n m A B.
  destruct n; [now auto|].
  destruct m; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m; [auto|].
    change (S (S m)) with (1 + S m) in *.
    rewrite <- (mx_hblock_split A), <- (mx_hblock_split B).
    apply HPhblock; [lia..|auto|auto].
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A), <- (mx_vblock_split B).
    apply HPvblock; [lia..|apply IHn|apply IHn]; lia.
Qed.


Lemma matrix_composable_double_nonempty_hblock_vblock_ind {R}
  (P : forall n m o, Matrix R n m -> Matrix R m o -> Prop)
  (HPnil_l : forall m o (A : Matrix R 0 m) (B : Matrix R m o), P _ _ _ A B)
  (HPnil_c : forall n o (A : Matrix R n 0) (B : Matrix R 0 o), P _ _ _ A B)
  (HPnil_r : forall n m (A : Matrix R n m) (B : Matrix R m 0), P _ _ _ A B)
  (HP_1_1 : forall (A B : Matrix R 1 1), P _ _ _ A B)
  (HP_l : forall n n' m o (A : Matrix R n m) (A' : Matrix R n' m) (B : Matrix R m o),
    n <> 0 -> n' <> 0 -> m <> 0 -> o <> 0 ->
    P _ _ _ A B -> P _ _ _ A' B ->
    P _ _ _ (mx_vblock A A') B)
  (HP_r : forall n m o o' (A : Matrix R n m) (B : Matrix R m o) (B' : Matrix R m o'),
    n <> 0 -> m <> 0 -> o <> 0 -> o' <> 0 ->
    P _ _ _ A B -> P _ _ _ A B' ->
    P _ _ _ A (mx_hblock B B'))
  (HP_c : forall n m m' o (A : Matrix R n m) (A' : Matrix R n m')
    (B : Matrix R m o) (B' : Matrix R m' o),
    n <> 0 -> m <> 0 -> m' <> 0 -> o <> 0 ->
    P _ _ _ A B -> P _ _ _ A' B' ->
    P _ _ _ (mx_hblock A A') (mx_vblock B B')) :
  forall n m o A B, P n m o A B.
Proof.
  intros n m o A B.
  destruct n; [now auto|].
  destruct m; [now auto|].
  destruct o; [now auto|].
  induction n as [n IHn] using lt_wf_ind.
  destruct n.
  - clear IHn.
    induction m as [m IHm] using lt_wf_ind.
    destruct m.
    + clear IHm.
      induction o; [auto|].
      change (S (S o)) with (1 + S o) in *.
      rewrite <- mx_hblock_split.
      auto.
    + change (S (S m)) with (1 + S m) in *.
      rewrite <- (mx_vblock_split B), <- (mx_hblock_split A).
      apply HP_c; [lia..| |auto].
      apply IHm.
      lia.
  - change (S (S n)) with (1 + S n) in *.
    rewrite <- (mx_vblock_split A).
    apply HP_l; [lia..| |auto].
    apply IHn.
    lia.
Qed.

Lemma const_matrix_alt {R} {n m} (r : R) :
  @const_matrix R n m r = Vector.const (Vector.const r _) _.
Proof.
  apply mx_eq.
  intros i j.
  rewrite mlookup_const.
  unfold mx_to_fun, Matrix.
  rewrite 2 vlookup_const.
  done.
Qed.


Section mx_vec_prod.


Local Open Scope Matrix_scope.


Context {R} `{SR : SemiRing R rO rI radd rmul req}.



Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.

Lemma mx_vec_prod_0 {n} (A : Matrix R n 0) (v : vec R 0) :
  (mx_vec_prod A v) = (fun_to_vec (λ _, 0)).
Proof.
  apply vec_eq.
  intros i.
  unfold mx_vec_prod.
  rewrite vlookup_map, lookup_fun_to_vec.
  rewrite vec_dot_to_sum_of, sum_of_fin_0.
  done.
Qed.

Lemma mx_vec_prod_hblock_app {n m o} (A : Matrix R n m) (B : Matrix R n o)
  v w :
  vec_rel equiv (mx_vec_prod (mx_hblock A B) (v +++ w))
  (vzip_with radd (mx_vec_prod A v) (mx_vec_prod B w)).
Proof.
  apply vec_rel_lookup.
  intros i.
  unfold mx_vec_prod, mx_hblock.
  rewrite vlookup_zip_with, 3 vlookup_map, vlookup_zip_with.
  rewrite vec_dot_app.
  done.
Qed.

Lemma mx_vec_prod_vblock {n m o} (A : Matrix R n o) (B : Matrix R m o)
  v :
  mx_vec_prod (mx_vblock A B) v =
  (mx_vec_prod A v) +++ (mx_vec_prod B v).
Proof.
  apply Vector.map_append.
Qed.

End mx_vec_prod.
