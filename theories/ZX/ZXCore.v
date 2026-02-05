Require Import TensorCore.Summable.
Require Import Bool.
Require Import Btauto.
Require Import TensorCore.Tensor.
Require Import QuantumLib.Complex.
Set Warnings "-stdlib-vector".
Require Import Vector.
Import VectorNotations.

#[global] 
Program Instance C_SemiRing : SemiRing C C0 C1 Cplus Cmult eq.
Next Obligation.
  split; intros; lca.
Qed.
Next Obligation.
  split; apply _.
Qed.
Next Obligation.
  change (@RelationClasses.Equivalence C eq).
  apply _.
Qed.

Notation vec := Vector.t.
Notation bvec := (vec bool).


Lemma if_mult_dist_r (b : bool) (y z : C) :
  (if b then y else C0) * z = 
  if b then y * z else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_dist_l (b : bool) (y z : C) :
  z * (if b then y else C0) = 
  if b then z * y else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_and (b c : bool) (x y : C) :
  (if b then x else C0) * (if c then y else C0) =
  if (b && c) then x * y else C0.
Proof.
  destruct b; destruct c; lca.
Qed.

(* Section ZX. *)

Ltac split_sums :=
    repeat progress (
        try setoid_rewrite sum_of_vec_succ;
        try setoid_rewrite sum_of_vec_0;
        try setoid_rewrite sum_of_vec_add).

Fixpoint allb {n: nat} (b : bool) (bs : bvec n) : bool :=
    match bs with
    | [] => true
    | b' :: bs' => (Bool.eqb b b') && allb b bs'
    end.

Definition allb_pair {n m : nat} (b : bool) (bscs : bvec n * bvec m) : bool :=
  match bscs with
  | (bs, cs) => allb b bs && allb b cs
  end.

Lemma allb_single (b c: bool) : allb b [c] = Bool.eqb b c.
Proof.
    simpl.
    rewrite andb_comm.
    reflexivity.
Qed.

Lemma allb_append {n m: nat} (b : bool) (bs1 : bvec n) (bs2 : bvec m) :
    allb b (bs1 ++ bs2) = allb b bs1 && allb b bs2.
Proof.
    induction bs1.
    - reflexivity.
    - simpl. rewrite IHbs1. rewrite andb_assoc. reflexivity.
Qed.

Definition zsp {n m : nat} (phase: R) : Tensor (R:=C) n m bool :=
  fun bs cs =>
    (if allb false bs && allb false cs then C1 else C0) +
    (if allb true bs && allb true cs then Cexp phase else C0).

Definition parity  {n : nat} (bs : Vector.t bool n) : bool :=
  Vector.fold_left (xorb) false bs.  

Lemma parity_false {n : nat} (bs : Vector.t bool n) :
  parity (false :: bs) = parity bs.
Proof. reflexivity. Qed.


Lemma parity_true {n : nat} (bs : Vector.t bool n) :
  parity (true :: bs) = negb (parity bs).
Proof. 
  unfold parity. 
  simpl.
  induction bs.
  - easy.
  - destruct h; simpl; rewrite IHbs.
    + rewrite negb_involutive; reflexivity.
    + reflexivity.
Qed.

Definition xsp {n m : nat} 
  (phase : R) (bs : Vector.t bool n) (cs : vec bool m) : C :=
  (1/√2)^(n + m) * (1 + Cexp (if parity (bs ++ cs) 
                       then (PI + phase) 
                       else phase)).

Definition h (bl : bool) (br : bool) : C :=
  1/sqrt(2) * (if bl && br then -1 else 1).

Fixpoint h_stack {n : nat} 
  : Vector.t bool n -> Vector.t bool n -> C :=
  match n with 
  | 0 => fun bll blr => 1
  | S k => fun bll blr => h (Vector.hd bll) (Vector.hd blr) * h_stack (Vector.tl bll) (Vector.tl blr)
  end.

Check Tensor.

Definition bihadamard {n m : nat} (ts : Tensor n m bool) : Tensor n m bool :=
  fun bs cs => 
    ∑ ds, ∑ es, h_stack bs ds * ts ds es * h_stack es cs.

Definition xsp_by_h {n m : nat} (phase : R) : Tensor n m bool :=
  bihadamard (zsp phase).



Lemma zsp_all_left {n m : nat} (bs : vec bool n) (cs : vec bool m) :
  forall phase,
    zsp phase bs cs = zsp phase (bs ++ cs) [].
Proof.
  intros.
  unfold zsp.
  simpl.
  rewrite 2 andb_true_r.
  rewrite 2 allb_append.
  reflexivity. 
Qed.

Lemma h_stack_comm {n : nat} (bs : vec bool n) (cs : vec bool n) :
  h_stack bs cs = h_stack cs bs.
Proof.
  induction bs.
  - simpl.
    C_field.
  - simpl.
    rewrite IHbs.
    unfold h.
    rewrite andb_comm.
    reflexivity.
Qed.

Lemma h_stack_mul {n m : nat} 
  (bs cs : vec bool n) (ds es : vec bool m) :
  h_stack bs cs * h_stack ds es = h_stack (bs ++ ds) (cs ++ es).
Proof.
  intros.
  induction bs.
  - simpl.
    rewrite (nil_spec cs).
    C_field.
  - simpl.
    rewrite <- Cmult_assoc.
    rewrite IHbs.
    rewrite (VectorSpec.eta cs).
    reflexivity.
Qed.

Lemma xsp_by_h_all_left {n m : nat} (bs : vec bool n) (cs : vec bool m) : 
  forall phase,
    xsp_by_h phase bs cs = xsp_by_h phase (bs ++ cs) [].
Proof.
  intros.
  unfold xsp_by_h, bihadamard.
  simpl.
  unfold bihadamard.
  symmetry.
  rewrite sum_of_comm.
  rewrite sum_of_vec_0.
  rewrite sum_of_vec_add.
  apply sum_of_ext; intros; apply sum_of_ext; intros.
  rewrite <- zsp_all_left.
  rewrite <- h_stack_mul.
  rewrite (h_stack_comm cs).
  C_field.
Qed.

Lemma xsp_by_h_ind_l {n : nat} (bs : Vector.t bool (S n)) :
  forall phase,
  xsp_by_h phase bs [] = 1/√2 * xsp_by_h (if hd bs then (PI + phase) else phase) (tl bs) [].
Proof.
  intros.
  unfold xsp_by_h, bihadamard.
  rewrite sum_of_vec_succ.
  rewrite sum_of_bool_defn.
  rewrite <- sum_of_add.
  rewrite sum_of_distr_r.
  apply sum_of_ext; intros.
  rewrite 3 sum_of_vec_0.
  simpl.
  destruct (hd bs).
  - C_field_simplify.
    unfold h, zsp.
    simpl.
    rewrite 2 andb_true_r.
    C_field_simplify.
    destruct (allb true x).
    + rewrite <- Cexp_PI.
      rewrite Cexp_add.
      lca.
    + lca.
    + nonzero.
    + nonzero.
  - C_field_simplify.
    unfold h, zsp. 
    simpl.
    rewrite 2 andb_true_r.
    C_field_simplify.
    reflexivity.
    all: nonzero.
Qed.

Lemma xsp_all_right {n m : nat} : forall (phase : R) (bs : vec bool n) (cs : vec bool m),
  xsp phase bs cs = xsp phase [] (bs ++ cs).
Proof. reflexivity. Qed. 

Lemma xsp_colorswap {n m : nat} : forall (phase : R) (bs : vec bool n) (cs : vec bool m),
  xsp phase bs cs = xsp_by_h phase bs cs.
Proof.
  intros.
  rewrite xsp_all_right.
  rewrite xsp_by_h_all_left.
  generalize dependent phase.
  induction (bs ++ cs); intros.
  - unfold xsp, xsp_by_h, bihadamard, zsp.
    simpl.
    rewrite 2 sum_of_vec_0.
    lca.
  - rewrite xsp_by_h_ind_l.
    rewrite <- IHt. 
    simpl.
    destruct h0.
    + unfold xsp.
      simpl.
      rewrite parity_true.
      rewrite negb_if.
      destruct (parity t).
      * C_field_simplify; [|nonzero].
        replace (Cexp (PI + (PI + phase))) with (Cexp phase).
        reflexivity.
        rewrite 2 Cexp_add.
        rewrite Cexp_PI.
        lca.
      * C_field.
    + unfold xsp.
      simpl.
      rewrite parity_false.
      C_field.
Qed.

Lemma flip_spider {n m} phase v w : 
  @zsp n m phase v w = zsp phase w v.
Proof.
  unfold zsp.
  rewrite andb_comm.
  f_equal.
  now rewrite andb_comm.
Qed.

Lemma sum_spider_1_l {n m : nat} (p: R) 
  (bs : bvec n) (cs : bvec m) :
    ∑ b , zsp p (b :: bs) cs = zsp p bs cs.
Proof.
  unfold zsp; rewrite sum_of_bool_defn; simpl; ring.
Qed.

Lemma sum_spider_1_r {n m : nat} (p : R)
  (bs : bvec n) (cs : bvec m) :
    ∑ c, zsp p bs (c :: cs) = zsp p bs cs.
Proof.
  unfold zsp; rewrite sum_of_bool_defn; simpl; repeat rewrite andb_false_r; ring. 
Qed.

Lemma sum_spider_l {n m o : nat} (p: R) (bs : bvec n) (cs : bvec o) :
    ∑ ds : bvec m, zsp p (ds ++ bs) cs = zsp p bs cs.
Proof.
  induction m.
  - now split_sums.
  - split_sums.
    rewrite sum_of_comm.
    cbn.
    setoid_rewrite sum_spider_1_l.
    apply IHm.
Qed.

Lemma sum_spider_r {n m o : nat} (p : R) (bs : bvec n) (cs : bvec o) :
    ∑ ds : bvec m, zsp p bs (ds ++ cs) = zsp p bs cs.
Proof.
  setoid_rewrite flip_spider.
  apply sum_spider_l.
Qed.


Lemma zsp_allb {n m o p: nat} (phase: R) (bs : bvec n) (ds : bvec m) (cs : bvec o) (es : bvec p) :
    (allb false bs) = (allb false cs) -> 
    (allb true bs) = (allb true cs) -> 
    (allb false ds) = (allb false es) -> 
    (allb true ds) = (allb true es) -> zsp phase bs ds = zsp phase cs es.
    intros Hbf Hbt Hdf Hdt.
    unfold zsp.
    rewrite Hbf, Hbt, Hdf, Hdt. 
    reflexivity.
Qed.

Ltac squash_spiders :=
  repeat progress (
    intros;
    try apply sum_of_ext;
    try apply (f_equal2 Cmult));
  apply zsp_allb;
  simpl;
  repeat rewrite allb_append;
  repeat rewrite allb_single;
  simpl;
  btauto.

Ltac replace_spiders t :=
  match goal with
    | [ |- ?lhs = _ ] => replace lhs with t by squash_spiders
  end.

Lemma spider_loop_1 {n o : nat} (p : R) (bs : bvec n) (cs : bvec o) :
  ∑ b, zsp p (b :: bs) (b :: cs) = zsp p bs cs.
Proof.
  intros.
  rewrite sum_of_bool_defn.
  unfold zsp; simpl.
  ring.
Qed.

Theorem spider_loop {n m o : nat} (p: R) (bs : bvec n) (ds : bvec o) :
    ∑ cs : bvec m, zsp p (cs ++ bs) (cs ++ ds) = zsp p bs ds.
Proof.
  induction m.
  - split_sums; reflexivity.
  - split_sums. 
    cbn. 
    rewrite sum_of_comm.
    setoid_rewrite spider_loop_1.
    apply IHm.
Qed.

Lemma spider_fusion1 {n m o p: nat} (p1 p2: R) 
  (bs1 : bvec n) (bs2 : bvec m) 
  (bs3 : bvec o) (bs4 : bvec p) :
    ∑ c , zsp p1 bs1 (c :: bs2) * zsp p2 (c :: bs3) bs4 =
    zsp (p1 + p2) (bs1 ++ bs3) (bs2 ++ bs4).
Proof.
  unfold zsp.
  rewrite sum_of_bool_defn.
  cbn.
  rewrite 2 andb_false_r.
  rewrite 4 allb_append.
  Csimpl.
  rewrite if_mult_and, if_mult_dist_l, if_mult_dist_r, <- andb_if.
  Csimpl.
  rewrite Cexp_add.
  f_equal.
  - case (allb false bs1);
    case (allb false bs2);
    case (allb false bs3);
    case (allb false bs4);
    reflexivity.
  - case (allb true bs1);
    case (allb true bs2);
    case (allb true bs3);
    case (allb true bs4);
    reflexivity.
Qed.

Theorem spider_fusion {n m o p k: nat} (p1 p2: R) 
  (bs1 : bvec n) (bs2 : bvec m)
  (bs3 : bvec o) (bs4 : bvec p) :
    ∑ cs : bvec (k+1) , zsp p1 bs1 (cs ++ bs2) * zsp p2 (cs ++ bs3) bs4 =
    zsp (p1 + p2) (bs1 ++ bs3) (bs2 ++ bs4).
Proof.
  split_sums.
  replace_spiders (∑ bs0 : bvec k, ∑ b, zsp p1 bs1  (b :: bs0 ++ bs2) * zsp p2 (b :: bs0 ++ bs3) bs4).
  setoid_rewrite spider_fusion1.
  replace_spiders (∑ bs0 : bvec k, zsp (p1 + p2) (bs0 ++ bs1 ++ bs3) (bs0 ++ bs2 ++ bs4)).
  setoid_rewrite spider_loop.
  reflexivity.
Qed.

(* End ZX. *)