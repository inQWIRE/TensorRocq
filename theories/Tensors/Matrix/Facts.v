Require Import Setoid Relation_Definitions Classes.Morphisms Btauto.

Set Warnings "-stdlib-vector".
From stdpp Require vector.
Import vector.

From TensorRocq Require Import Aux Aux_stdpp Matrix.Definitions.
From TensorRocq Require Export Algebra Summable.


Lemma permute_vec_vzip_with {A B C n m} (f : fin n -> fin m) (g : A -> B -> C)
  (v : vec A m) w :
  permute_vec f (vzip_with g v w) = vzip_with g (permute_vec f v) (permute_vec f w).
Proof.
  apply vec_eq.
  intros i.
  rewrite lookup_permute_vec, 2 vlookup_zip_with, 2 lookup_permute_vec.
  done.
Qed.

Lemma permute_vec_vmap {A B n m} (f : fin n -> fin m) (g : A -> B)
  (v : vec A m) :
  permute_vec f (vmap g v) = vmap g (permute_vec f v).
Proof.
  apply vec_eq.
  intros i.
  rewrite lookup_permute_vec, 2 vlookup_map, lookup_permute_vec.
  done.
Qed.

Section VectorFacts.

Context `{SR : SemiRing R rO rI radd rmul req}.

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

#[export] Instance vec_dot_mor
  {n} : Proper (vec_rel req ==> vec_rel req ==> req) (vec_dot (n:=n)).
Proof.
  intros v v' Hv w w' Hw.
  unfold vec_dot.
  f_equiv.
  apply SetoidPermutation.eqlistA_PermutationA, SetoidList.eqlistA_altdef.
  apply vec_rel_alt.
  pose proof SR as [].
  eapply vzip_with_mor; [apply SR|done..].
Qed.

Lemma vec_dot_cons' {n} (v w : vec R (S n)) :
  vec_dot v w = vhd v * vhd w + vec_dot (vtl v) (vtl w).
Proof.
  inv_all_vec_fin;
  done.
Qed.

Lemma vec_dot_cons {n} vh wh (v w : vec R n) :
  vec_dot (vh ::: v) (wh ::: w) = vh * wh + vec_dot v w.
Proof.
  done.
Qed.

Lemma vec_dot_app {n m} (v w : vec R n) (v' w' : vec R m) :
  vec_dot (v +++ v') (w +++ w') ==
  vec_dot v w + vec_dot v' w'.
Proof.
  unfold vec_dot.
  rewrite vzip_with_app, vec_to_list_app, Rlist_sum_app.
  done.
Qed.


Lemma vec_dot_permute_vec {n m} (f : fin n -> fin m) {Hf : Inj eq eq f}
  (v w : vec R m) : n = m -> vec_dot (permute_vec f v) (permute_vec f w) ==
  vec_dot v w.
Proof.
  intros <-.
  unfold vec_dot.
  rewrite <- permute_vec_vzip_with.
  f_equiv.
  apply (SetoidPermutation.Permutation_PermutationA _).
  now rewrite permute_vec_perm.
Qed.

Lemma vec_dot_to_sum_of {n} (v w : vec R n) :
  vec_dot v w = ∑ i : fin n, v !!! i * w !!! i.
Proof.
  rewrite sum_of_defn.
  cbn.
  rewrite fin_elements_eq_fun_to_vec.
  rewrite <- vec_to_list_map, vmap_fun_to_vec.
  unfold vec_dot.
  f_equal; f_equal.
  apply vec_eq.
  intros i.
  rewrite vlookup_zip_with, lookup_fun_to_vec.
  done.
Qed.


End VectorFacts.








Lemma mx_eq {R n m} (A B : Matrix R n m) : A = B <-> forall i j, A i j = B i j.
Proof.
  unfold Matrix.
  split; [now intros <-|].
  intros Heq.
  apply vec_eq.
  intros i.
  apply vec_eq.
  apply Heq.
Qed.

Lemma mx_equiv `{Equiv R}
  {n m} (A B : Matrix R n m) : A ≡ B <-> forall i j, A i j ≡ B i j.
Proof.
  unfold equiv, Matrix_equiv, matrix_rel.
  rewrite vec_rel_lookup.
  setoid_rewrite vec_rel_lookup.
  done.
Qed.


Lemma mlookup_fun_to_mx {R n m} (f : fin n -> fin m -> R) i j :
  fun_to_mx f i j = f i j.
Proof.
  unfold fun_to_mx, mx_to_fun.
  cbn.
  setoid_rewrite lookup_fun_to_vec.
  apply lookup_fun_to_vec.
Qed.

Lemma mlookup_const {R n m} (r : R) i j :
  @const_matrix R n m r i j = r.
Proof.
  apply mlookup_fun_to_mx.
Qed.

#[export] Instance const_matrix_mor `{Equiv R} {n m} :
  Proper (equiv ==> equiv) (@const_matrix R n m).
Proof.
  intros r r' Hr.
  apply mx_equiv.
  intros i j.
  now rewrite 2 mlookup_const.
Qed.

Lemma lookup_mx_row {R n m} (A : Matrix R n m) i j :
  mx_row A i !!! j = A i j.
Proof.
  done.
Qed.

Lemma lookup_mx_col {R n m} (A : Matrix R n m) j i :
  mx_col A j !!! i = A i j.
Proof.
  unfold mx_col.
  rewrite vlookup_map.
  done.
Qed.

#[export] Instance mx_row_mor `{Equiv R} {n m} :
  Proper (equiv ==> eq ==> vec_rel equiv) (@mx_row R n m).
Proof.
  intros A B HAB i _ <-.
  rewrite vec_rel_lookup.
  intros j.
  now rewrite 2 lookup_mx_row; apply mx_equiv.
Qed.

#[export] Instance mx_col_mor `{Equiv R} {n m} :
  Proper (equiv ==> eq ==> vec_rel equiv) (@mx_col R n m).
Proof.
  intros A B HAB i _ <-.
  rewrite vec_rel_lookup.
  intros j.
  now rewrite 2 lookup_mx_col; apply mx_equiv.
Qed.

Lemma mlookup_map {R R'} (f : R -> R') {n m} (A : Matrix R n m) i j :
  map_matrix f A i j = f (A i j).
Proof.
  unfold mx_to_fun, map_matrix.
  unfold Matrix.
  now rewrite 2 vlookup_map.
Qed.

#[export] Instance map_matrix_mor `{Equiv R, Equiv R'} (f : R -> R')
  {Hf : Proper (equiv ==> equiv) f}
  {n m} : Proper (equiv ==> equiv) (map_matrix f (n:=n) (m:=m)).
Proof.
  intros A B.
  rewrite 2 mx_equiv.
  intros HAB.
  intros i j.
  rewrite 2 mlookup_map.
  f_equiv.
  done.
Qed.

Lemma mlookup_hblock {R n m m'} (A : Matrix R n m) (B : Matrix R n m') i j :
  mx_hblock A B i j =
  sum_rect (λ _, R) (A i) (B i) (fin_sum_case j).
Proof.
  unfold mx_to_fun, mx_hblock, Matrix.
  rewrite vlookup_zip_with, lookup_vapp.
  done.
Qed.

Lemma mlookup_vblock {R n n' m} (A : Matrix R n m) (B : Matrix R n' m) i j :
  mx_vblock A B i j =
  sum_rect (λ _, R) (λ i, A i j) (λ i, B i j) (fin_sum_case i).
Proof.
  unfold mx_to_fun, mx_vblock, Matrix.
  rewrite lookup_vapp.
  now destruct (fin_sum_case i).
Qed.

#[export] Instance mx_hblock_mor `{Equiv R} {n m m'} :
  Proper (equiv ==> equiv ==> equiv) (@mx_hblock R n m m').
Proof.
  intros A A' HA B B' HB.
  unfold mx_hblock.
  eapply vzip_with_mor; [|eauto..].
  apply _.
Qed.

#[export] Instance mx_vblock_mor `{Equiv R} {n n' m} :
  Proper (equiv ==> equiv ==> equiv) (@mx_vblock R n n' m).
Proof.
  intros A A' HA B B' HB.
  unfold mx_vblock.
  apply vapp_mor; done.
Qed.


Lemma mlookup_prepermute_matrix_l {R n m o} (f : fin n -> fin m) (A : Matrix R m o) i j :
  prepermute_matrix_l f A i j = A (f i) j.
Proof.
  unfold mx_to_fun, prepermute_matrix_l, Matrix.
  rewrite lookup_permute_vec.
  done.
Qed.

Lemma mlookup_prepermute_matrix_r {R n m o} (f : fin m -> fin o) (A : Matrix R n o) i j :
  prepermute_matrix_r f A i j = A i (f j).
Proof.
  unfold mx_to_fun, prepermute_matrix_r, Matrix.
  rewrite vlookup_map, lookup_permute_vec.
  done.
Qed.

Lemma mlookup_prepermute_matrix {R} {n m n' m'}
    (fl : fin n -> fin n') (fr : fin m -> fin m')
    (A : Matrix R n' m') i j :
  prepermute_matrix fl fr A i j = 
  A (fl i) (fr j).
Proof.
  unfold mx_to_fun, prepermute_matrix, Matrix.
  rewrite lookup_permute_vec, vlookup_map, lookup_permute_vec.
  done.
Qed.

#[export] Instance prepermute_matrix_l_mor `{Equiv R} {n m o} : 
  Proper (pointwise_relation (fin n) eq ==> equiv ==> equiv) 
  (@prepermute_matrix_l R n m o).
Proof.
  intros f g Hfg A B HAB.
  rewrite @mx_equiv in HAB |- *.
  intros i j.
  rewrite 2 mlookup_prepermute_matrix_l, <- Hfg.
  done.
Qed.

#[export] Instance prepermute_matrix_r_mor `{Equiv R} {n m o} : 
  Proper (pointwise_relation _ eq ==> equiv ==> equiv) 
  (@prepermute_matrix_r R n m o).
Proof.
  intros f g Hfg A B HAB.
  rewrite @mx_equiv in HAB |- *.
  intros i j.
  rewrite 2 mlookup_prepermute_matrix_r, <- Hfg.
  done.
Qed.

#[export] Instance prepermute_matrix_mor `{Equiv R} {n m n' m'} : 
  Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> equiv ==> equiv) 
  (@prepermute_matrix R n m n' m').
Proof.
  intros fl fl' Hfl fr fr' Hfr A B HAB.
  rewrite @mx_equiv in HAB |- *.
  intros i j.
  rewrite 2 mlookup_prepermute_matrix, <- Hfl, <- Hfr.
  done.
Qed.

Lemma lookup_mx_to_vec_rowmajor {R n m} (A : Matrix R n m) i : 
  mx_to_vec_rowmajor A !!! i = A (fin_split i).1 (fin_split i).2.
Proof.
  unfold mx_to_vec_rowmajor.
  rewrite lookup_vjoin.
  done.
Qed.

Lemma lookup_mx_to_vec_rowmajor_prod {R n m} (A : Matrix R n m) i j :
  mx_to_vec_rowmajor A !!! (fin_prod i j) = A i j.
Proof.
  rewrite lookup_mx_to_vec_rowmajor, fin_split_prod.
  done.
Qed.

Lemma lookup_mx_to_vec_colmajor {R n m} (A : Matrix R n m) i : 
  mx_to_vec_colmajor A !!! i = A (fin_split i).2 (fin_split i).1.
Proof.
  unfold mx_to_vec_colmajor.
  rewrite lookup_vjoin'.
  done.
Qed.

Lemma lookup_mx_to_vec_colmajor_prod {R n m} (A : Matrix R n m) i j :
  mx_to_vec_colmajor A !!! (fin_prod i j) = A j i.
Proof.
  rewrite lookup_mx_to_vec_colmajor, fin_split_prod.
  done.
Qed.

#[export] Instance mx_to_vec_rowmajor_mor `{Equiv R} {n m} : 
  Proper (equiv ==> vec_rel equiv) (@mx_to_vec_rowmajor R n m).
Proof.
  intros A B HAB.
  apply vec_rel_lookup.
  intros i.
  induction i as [i j] using fin_mul_ind.
  rewrite 2 lookup_mx_to_vec_rowmajor_prod.
  now apply mx_equiv.
Qed.

#[export] Instance mx_to_vec_colmajor_mor `{Equiv R} {n m} : 
  Proper (equiv ==> vec_rel equiv) (@mx_to_vec_colmajor R n m).
Proof.
  intros A B HAB.
  apply vec_rel_lookup.
  intros i.
  induction i as [i j] using fin_mul_ind.
  rewrite 2 lookup_mx_to_vec_colmajor_prod.
  now apply mx_equiv.
Qed.

(* TODO: mx_of_vec_[...] lemmas *)





Lemma mlookup_transpose {R n m} (A : Matrix R n m) i j : 
  mx_transpose A i j = A j i.
Proof.
  unfold mx_transpose.
  now rewrite mlookup_fun_to_mx.
Qed.

#[export] Instance mx_transpose_mor `{Equiv R} {n m} : 
  Proper (equiv ==> equiv) (@mx_transpose R n m).
Proof.
  intros A B.
  rewrite 2 mx_equiv.
  intros HAB i j.
  rewrite 2 mlookup_transpose.
  done.
Qed.

Lemma cast_matrix_id {R n m} (Hn : n = n) (Hm : m = m) (A : Matrix R n m) : 
  cast_matrix Hn Hm A = A.
Proof.
  unfold cast_matrix.
  case_match; [|done].
  case_match; [|done].
  rewrite 2 (proof_irrel _ eq_refl).
  done.
Qed.


Lemma mlookup_cast {R n m n' m'} (Hn : n = n') (Hm : m = m') (A : Matrix R n m) i j : 
  cast_matrix Hn Hm A i j = A (Fin.cast i (eq_sym Hn)) (Fin.cast j (eq_sym Hm)).
Proof.
  subst.
  rewrite cast_matrix_id.
  rewrite 2 fcast_id.
  done.
Qed.

#[export] Instance cast_matrix_mor `{Equiv R} {n m n' m'} (Hn : n = n') (Hm : m = m') : 
  Proper (equiv ==> equiv) (@cast_matrix R n m n' m' Hn Hm).
Proof.
  intros A B.
  rewrite 2 mx_equiv.
  intros HAB i j.
  rewrite 2 mlookup_cast.
  done.
Qed.






Section MatrixFacts.

Local Open Scope Matrix_scope.


Context `{SR : SemiRing R rO rI radd rmul req}.



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



Lemma mlookup_id_case n i j :
  I n i j = if decide (i = j) then 1 else 0.
Proof.
  apply mlookup_fun_to_mx.
Qed.

Lemma mlookup_id n i :
  I n i i = 1.
Proof.
  now rewrite mlookup_id_case, decide_True.
Qed.

Lemma mlookup_id_ne n i j : i <> j ->
  I n i j = 0.
Proof.
  intros;
  now rewrite mlookup_id_case, decide_False.
Qed.

Lemma mlookup_J n m i j :
  J n m i j = 1.
Proof.
  apply mlookup_fun_to_mx.
Qed.

Lemma mlookup_zero n m i j :
  Zero n m i j = 0.
Proof.
  apply mlookup_fun_to_mx.
Qed.

Lemma mlookup_compose {n m o} (A : Matrix R n m) (B : Matrix R m o) i j :
  compose_matrix A B i j = vec_dot (mx_row A i) (mx_col B j).
Proof.
  unfold compose_matrix.
  rewrite mlookup_fun_to_mx.
  done.
Qed.

Lemma mlookup_compose' {n m o} (A : Matrix R n m) (B : Matrix R m o) i j :
  compose_matrix A B i j = ∑ k, A i k * B k j.
Proof.
  rewrite mlookup_compose, vec_dot_to_sum_of.
  setoid_rewrite lookup_mx_row.
  setoid_rewrite lookup_mx_col.
  done.
Qed.

Lemma mlookup_kron {n m o p} (A : Matrix R n m) (B : Matrix R o p) i j :
  kron_matrix A B i j = A (fin_split i).1 (fin_split j).1 * B (fin_split i).2 (fin_split j).2.
Proof.
  unfold kron_matrix.
  now rewrite mlookup_fun_to_mx.
Qed.

Lemma mlookup_kron_prod {n m o p} (A : Matrix R n m) (B : Matrix R o p) il ir jl jr:
  kron_matrix A B (fin_prod il ir) (fin_prod jl jr) =
    A il jl * B ir jr.
Proof.
  rewrite mlookup_kron, 2 fin_split_prod.
  done.
Qed.


Lemma mlookup_perm_matrix_case {n m} (f : fin n -> fin m) i j :
  perm_matrix f i j = if decide (f i = j) then 1 else 0.
Proof.
  apply mlookup_fun_to_mx.
Qed.

Lemma mlookup_perm_matrix {n m} (f : fin n -> fin m) i :
  perm_matrix f i (f i) = 1.
Proof.
  now rewrite mlookup_perm_matrix_case, decide_True.
Qed.

Lemma mlookup_perm_matrix_ne {n m} (f : fin n -> fin m) i j : f i <> j ->
  perm_matrix f i j = 0.
Proof.
  intros; 
  now rewrite mlookup_perm_matrix_case, decide_False.
Qed.

#[export] Instance perm_matrix_mor {n m} : 
  Proper (pointwise_relation (fin n) (@eq (fin m)) ==> eq) (perm_matrix (R:=R)).
Proof.
  intros f f' Hf.
  apply mx_eq.
  intros i j.
  rewrite 2 mlookup_perm_matrix_case.
  rewrite <- Hf.
  done.
Qed.


End MatrixFacts.




#[export] Instance fun_to_mx_mor_eq {R n m} :
  Proper (pointwise_relation (fin n) (pointwise_relation (fin m) (@eq R)) ==> eq) fun_to_mx.
Proof.
  intros f g Hfg.
  apply mx_eq.
  intros i j.
  rewrite 2 mlookup_fun_to_mx.
  apply Hfg.
Qed.

#[export] Instance fun_to_mx_mor `{Equiv R} {n m} :
  Proper (pointwise_relation (fin n) (pointwise_relation (fin m) (≡@{R})) ==> equiv) fun_to_mx.
Proof.
  intros f g Hfg.
  apply mx_equiv.
  intros i j.
  rewrite 2 mlookup_fun_to_mx.
  apply Hfg.
Qed.
