From TensorRocq Require Import Aux Aux_stdpp Matrix.Definitions Matrix.Facts Tensor.
From stdpp Require Import vector.




Local Notation Rel R n m := (@Tensor Prop n m R).

Definition mx2rel `{SR : SemiRing R rO rI radd rmul req} {n m} (A : Matrix R n m) : Rel R n m :=
  fun v w => mx_vec_prod A w ≡ v.

Definition id_rel {R n} : Rel R n n :=
  fun v w => v = w.

Definition swap_rel {R n m} : Rel R (n + m) (m + n) :=
  fun v w => v = vsplitr w +++ vsplitl w.

Definition cup_rel {R n} : Rel R 0 (n + n) :=
  fun v w => vsplitl w = vsplitr w.

Definition cap_rel {R n} : Rel R (n + n) 0 :=
  fun v w => vsplitl v = vsplitr v.

#[global] Arguments mx2rel {_ _ _ _ _ _ _} {_ _} _ _ _ / : assert.
#[global] Arguments id_rel {_ _} _ _ / : assert.
#[global] Arguments swap_rel {_ _ _} _ _ / : assert.
#[global] Arguments cup_rel {_ _} _ _ / : assert.
#[global] Arguments cap_rel {_ _} _ _ / : assert.


Module M2R.

Section mx2rel.


Context `{SR : SemiRing R rO rI radd rmul req}
  `{LeibR : !LeibnizEquiv R}.

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

Local Notation mx2rel := (mx2rel (SR:=SR)).

#[global] Instance mor {n m} : Proper ((≡@{Matrix R n m}) ==> equiv) mx2rel.
Proof.
  intros A B <-%leibniz_equiv.
  done.
Qed.

Lemma id {n} : mx2rel (id_matrix n) ≡ id_rel.
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite mx_vec_prod_id.
  rewrite leibniz_equiv_iff.
  done.
Qed.

Lemma swap {n m} : mx2rel (swap_matrix n m) ≡ swap_rel.
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite mx_vec_prod_swap.
  rewrite leibniz_equiv_iff.
  done.
Qed.

Lemma compose `{EqDecision R} {n m o} (A : Matrix R n m) (B : Matrix R m o) :
  mx2rel (compose_matrix A B) ≡ compose_tensor (mx2rel A) (mx2rel B).
Proof.
  intros v w Hv Hw.
  cbn.
  rewrite mx_vec_prod_compose.
  symmetry.
  rewrite (sum_of_unique' _ (mx_vec_prod B w)) by
    now intros; rewrite 2 leibniz_equiv_iff; tauto.
  rewrite and_is_True_r by done.
  done.
Qed.

#[export] Instance vapp_inj_equiv `{Equiv A}
  {n m} : Inj2 equiv equiv equiv (@vapp A n m).
Proof.
  intros v v' w w' Hvw.
  apply (f_equiv vsplitl) in Hvw as Hv.
  apply (f_equiv vsplitr) in Hvw as Hw.
  rewrite 2 vsplitl_app in Hv.
  rewrite 2 vsplitr_app in Hw.
  done.
Qed.


Lemma stack {n m o p} (A : Matrix R n m) (B : Matrix R o p) :
  mx2rel (stack_matrix A B) ≡ stack_tensor (mx2rel A) (mx2rel B).
Proof.
  intros v w Hv Hw.
  induction v as [vl vr] using vec_add_inv.
  induction w as [wl wr] using vec_add_inv.
  cbn.
  rewrite mx_vec_prod_stack_app.
  rewrite (inj2_iff vapp).
  rewrite 2 vsplitl_app, 2 vsplitr_app.
  done.
Qed.

#[global] Instance inj {n m} : Inj (=@{Matrix R n m}) equiv (mx2rel).
Proof.
  intros A B HAB.
  apply mx_eq; intros i j.
  specialize (HAB (mx_col A j) (e j) _ _).
  cbn in HAB.
  rewrite 2 mx_vec_prod_e in HAB.
  specialize (HAB.1 (reflexivity _)) as HB.
  rewrite vec_equiv in HB.
  specialize (HB i).
  rewrite 2 lookup_mx_col, leibniz_equiv_iff in HB.
  done.
Qed.

End mx2rel.

End M2R.


