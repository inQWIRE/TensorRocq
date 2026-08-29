From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)





From TensorRocqEx Require Export ZXrwsymm ZXrwauto ZXrwfrob.




From TensorRocq Require Import BW BWSized SizedProps PropsGraphs SizedPropsGraphs SizedProLike SizedRewriting SizedProQuote.

Open Scope nat_scope.
(*
Definition ZX_tensor_is_Some (asgn : Pmap nat) (n m : btree positive) (t : ZXCVERT) : bool :=
  match t with
  | None => (* H-box stack *) bool_decide (n =@{list positive} m) (* Conservative, but sufficient *)
  | Some (inr _) => (* Constant; need there to be no args *) (bool_decide (n ++ m = []) |||
    default false (l ← join_list ((asgn !!.) <$> (n ++ m)); Some $ forallb (Nat.eqb 0) l))%lazy
  | Some (inl _) => true
  end.

#[export] Instance ZX_sized_ofTensor_testable : SizedOfTensorSomeTestable ZXCVERT ZX :=
  ZX_tensor_is_Some.

#[export, program] Instance ZX_lawful_sized_ofTensor_testable : LawfulSizedOfTensorSomeTestable ZXCVERT ZX.
Next Obligation.
  intros concr n m t fN Hsome HfN.
  destruct t as [[[isX phase] | c]|]; [destruct isX; done|..]; cbn in Hsome.
  - destruct (bool_decide (_ = [])) eqn:Hsome'.
    + apply bool_decide_eq_true in Hsome'.
      assert (Hnm : n =@{list _} [] /\ m =@{list _} []) by now apply app_nil in Hsome'.
      rewrite (btree_size_ext (n:=n) (m:=0)) by apply Hnm.
      rewrite (btree_size_ext (n:=m) (m:=0)) by apply Hnm.
      done.
    + enough (btree_size fN (n + m) = 0) as Hnm by
      (cbn in Hnm; apply Nat.eq_add_0 in Hnm as [-> ->]; done).
      rewrite <- sum_list_with_btree_elems.
      destruct (_ ≫= _) as [b|] eqn:Hb; [|done].
      apply id in Hsome as [= ->].
      apply bind_Some in Hb as (zeros & Hnm & Hzeros).
      apply join_list_Some in Hnm.
      apply (inj Some) in Hzeros.
      apply Is_true_true, forallb_True in Hzeros.
      remember (length zeros) as k eqn:Hk.
      apply (f_equal length) in Hnm as Hk'.
      rewrite 2 length_fmap in Hk'.
      assert (zeros = replicate k 0) as ?; [|rewrite <- Hk' in Hk; subst zeros].
      1:{
        subst k.
        rewrite <- fmap_const.
        symmetry.
        rewrite Forall_forall in Hzeros.
        apply list_fmap_id'.
        intros a Ha%Hzeros; now destruct a.
      }
      apply list_eq_Forall2 in Hnm.
      rewrite Forall2_fmap in Hnm.
      subst k.
      rewrite <- fmap_const in Hnm.
      rewrite Forall2_fmap_r in Hnm.
      cbn.
      revert Hnm.
      clear Hsome' Hk' Hzeros.
      induction (n ++ m) as [|p nm IHnm]; [done|].
      intros [Hp Hnm]%Forall2_cons.
      cbn in Hp.
      cbn.
      apply Nat.eq_add_0.
      split; [|auto].
      apply HfN in Hp.
      done.
  - apply bool_decide_eq_true in Hsome.
    rewrite (btree_size_ext Hsome).
    cbn.
    case_decide; done.
Qed. *)

Notation SizedProLike' MS S T D :=
    (SizedProLike (N:=positive) MS S T D).


#[export] Instance ZX_SymmetricG_SizedProLike : SizedProLike' MSymmetric SymmetricG ZXDVERT ZX := {}.

#[export] Instance ZX_Autonomous_SizedProLike : SizedProLike' MAutonomous Autonomous ZXDVERT ZX := {}.

#[export] Instance ZX_Frobenius_SizedProLike : SizedProLike' MFrobenius Frobenius ZXDVERT ZX := {}.


(* FIXME: Move *)
Lemma btree_size_eq_path {N} {f : N -> nat} {a b : btree N} (p : bpath a b) :
  btree_size f a = btree_size f b.
Proof.
  rewrite <- 2 sum_list_with_btree_elems.
  f_equal.
  now apply btree_elems_bpath in p.
Qed.