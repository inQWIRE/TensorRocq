Require Import TensorCore.FieldSum.
Require Import Bool.
Require Import Btauto.
Require Import TensorCore.Tensor.
Require Import QuantumLib.Complex.
Require Import Vector.
Import VectorNotations.


Section ZX.

Ltac split_sums :=
    repeat progress (
        try setoid_rewrite fsum_vec_succ;
        try setoid_rewrite fsum_vec_zero;
        try setoid_rewrite fsum_vec_append).

Fixpoint allb {n: nat} (b : bool) (bs : Vector.t bool n) : bool :=
    match bs with
    | [] => true
    | b' :: bs' => (Bool.eqb b b') && allb b bs'
    end.

Definition allb_pair {n m : nat} (b : bool) (bscs : Vector.t bool n * Vector.t bool m) : bool :=
  match bscs with
  | (bs, cs) => allb b bs && allb b cs
  end.

Lemma allb_single (b c: bool) : allb b [c] = Bool.eqb b c.
Proof.
    simpl.
    rewrite andb_comm.
    reflexivity.
Qed.

Lemma allb_append {n m: nat} (b : bool) (bs1 : Vector.t bool n) (bs2 : Vector.t bool m) :
    allb b (bs1 ++ bs2) = allb b bs1 && allb b bs2.
Proof.
    induction bs1.
    - reflexivity.
    - simpl. rewrite IHbs1. rewrite andb_assoc. reflexivity.
Qed.

Definition zsp {n m : nat} (phase: R) : Tensor n m bool :=
  fun bs cs =>
    (if allb false bs && allb false cs then C1 else C0) +
    (if allb true bs && allb true cs then Cexp phase else C0).

Lemma sum_spider_1_l {n m : nat} (p: R) 
  (bs : Vector.t bool n) (cs : Vector.t bool m) :
    ∑ b , zsp p (b :: bs) cs = zsp p bs cs.
Proof.
  unfold zsp; rewrite fsum_bool_def; simpl; ring.
Qed.

Lemma sum_spider_1_r {n m : nat} (p : R)
  (bs : Vector.t bool n) (cs : Vector.t bool m) :
    ∑ c, zsp p bs (c :: cs) = zsp p bs cs.
Proof.
  unfold zsp; rewrite fsum_bool_def; simpl; repeat rewrite andb_false_r; ring. 
Qed.

Lemma sum_spider_l {n m o : nat} (p: R) (bs : Vector.t bool n) (cs : Vector.t bool o) :
    ∑ ds : m , zsp p (ds ++ bs) cs = zsp p bs cs.
Proof.
    induction m.
    - rewrite fsum_vec_zero; reflexivity.
    - rewrite fsum_vec_succ.
      rewrite fsum_vec_comm1.
      setoid_rewrite sum_spider_1_l.
      apply IHm.      
Qed.

Lemma sum_spider_r {n m o : nat} (p : R) (bs : Vector.t bool n) (cs : Vector.t bool o) :
    ∑ ds : m , zsp p bs (ds ++ cs) = zsp p bs cs.
Proof.
    induction m.
    - rewrite fsum_vec_zero; auto.
    - rewrite fsum_vec_succ.
      rewrite fsum_vec_comm1.
      setoid_rewrite sum_spider_1_r.
      apply IHm. 
Qed.


Lemma zsp_allb {n m o p: nat} (phase: R) (bs : Vector.t bool n) (ds : Vector.t bool m) (cs : Vector.t bool o) (es : Vector.t bool p) :
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
    try apply fsum_ext;
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

Lemma spider_loop_1 {n m o : nat} (p : R) (bs : Vector.t bool n) (cs : Vector.t bool o) (b : bool) :
  ∑ b, zsp p (b :: bs) (b :: cs) = zsp p bs cs.
Proof.
  intros.
  rewrite fsum_bool_def.
  unfold zsp; simpl.
  ring.
Qed.

Theorem spider_loop {n m o : nat} (p: R) (bs : Vector.t bool n) (ds : Vector.t bool o) :
    ∑ cs : m , zsp p (cs ++ bs) (cs ++ ds) = zsp p bs ds.
Proof.
    induction m.
    - rewrite fsum_vec_zero.
      reflexivity.
    - rewrite fsum_vec_succ.
      simpl.
      rewrite fsum_vec_comm1.
      setoid_rewrite spider_loop_1.
      + apply IHm.
      + exact n.
      + exact true.
Qed.

Lemma spider_fusion1 {n m o p: nat} (p1 p2: R) 
  (bs1 : Vector.t bool n) (bs2 : Vector.t bool m) 
  (bs3 : Vector.t bool o) (bs4 : Vector.t bool p) :
    ∑ c , zsp p1 bs1 (c :: bs2) * zsp p2 (c :: bs3) bs4 =
    zsp (p1 + p2) (bs1 ++ bs3) (bs2 ++ bs4).
Proof.
    unfold zsp.
    rewrite fsum_bool_def.
    repeat rewrite allb_append.
    simpl.
    case (allb true bs1);
    case (allb false bs1);
    case (allb true bs2);
    case (allb false bs2);
    case (allb true bs3);
    case (allb false bs3);
    case (allb true bs4);
    case (allb false bs4);
    simpl;
    autorewrite with Cexp_db;
    ring.
Qed.

Theorem spider_fusion {n m o p k: nat} (p1 p2: R) 
  (bs1 : Vector.t bool n) (bs2 : Vector.t bool m)
  (bs3 : Vector.t bool o) (bs4 : Vector.t bool p) :
    ∑ cs : k+1 , zsp p1 bs1 (cs ++ bs2) * zsp p2 (cs ++ bs3) bs4 =
    zsp (p1 + p2) (bs1 ++ bs3) (bs2 ++ bs4).
Proof.
    split_sums.
    replace_spiders (∑ bs0 : k, ∑ b, zsp p1 bs1  (b :: bs0 ++ bs2) * zsp p2 (b :: bs0 ++ bs3) bs4).
    setoid_rewrite spider_fusion1.
    replace_spiders (∑ bs0 : k, zsp (p1 + p2) (bs0 ++ bs1 ++ bs3) (bs0 ++ bs2 ++ bs4)).
    setoid_rewrite spider_loop.
    reflexivity.
Qed.

End ZX.