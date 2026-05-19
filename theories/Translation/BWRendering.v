From stdpp Require Import base.
From TensorRocq Require Import Aux_stdpp.
From TensorRocq Require Import BW.

Local Open Scope btree_scope.

Inductive StructuralRenderElement {A} :=
  | RenderSwap (a b : btree A)
  | RenderCup (a : btree A)
  | RenderCap (a : btree A)
  | RenderDelta (a b : btree A).

#[global] Arguments StructuralRenderElement : clear implicits.

Definition SRE_dom {A} (e : StructuralRenderElement A) : btree A :=
  match e with
  | RenderSwap a b => a + b
  | RenderCup a => 0
  | RenderCap a => a + a
  | RenderDelta a _ => a
  end.

Definition SRE_cod {A} (e : StructuralRenderElement A) : btree A :=
  match e with
  | RenderSwap a b => b + a
  | RenderCup a => a + a
  | RenderCap a => 0
  | RenderDelta _ b => b
  end.


Definition StructuralRenderLayer (A : Type) : Type :=
  btree A * StructuralRenderElement A * btree A.

Inductive StructuralRender {A : Type} :=
  | SRid (a : btree A)
  | SRmors (m : StructuralRenderLayer A) (ms : list (StructuralRenderLayer A)).

#[global] Arguments StructuralRender : clear implicits.

Definition SRL_dom {A} (e : StructuralRenderLayer A) : btree A :=
  e.1.1 + SRE_dom e.1.2 + e.2.

Definition SRL_cod {A} (e : StructuralRenderLayer A) : btree A :=
  e.1.1 + SRE_cod e.1.2 + e.2.


Definition SR_dom {A} (e : StructuralRender A) : btree A :=
  match e with
  | SRid a => a
  | SRmors m _ => SRL_dom m
  end.

Definition SR_cod {A} (e : StructuralRender A) : btree A :=
  match e with
  | SRid a => a
  | SRmors m ms => SRL_cod (last ms m)
  end.


Definition SRL_whisker_l {A} (b : btree A) (l : StructuralRenderLayer A) : 
  StructuralRenderLayer A :=
  (b + l.1.1, l.1.2, l.2)%btree.

Definition SRL_whisker_r {A} (b : btree A) (l : StructuralRenderLayer A) : 
  StructuralRenderLayer A :=
  (l.1.1, l.1.2, l.2 + b)%btree.

Definition SR_whisker_l {A} (b : btree A) (r : StructuralRender A) : StructuralRender A :=
  match r with
  | SRid a => SRid (b + a)
  | SRmors m ms => SRmors (SRL_whisker_l b m) (SRL_whisker_l b <$> ms)
  end.

Definition SR_whisker_r {A} (b : btree A) (r : StructuralRender A) : StructuralRender A :=
  match r with
  | SRid a => SRid (a + b)
  | SRmors m ms => SRmors (SRL_whisker_r b m) (SRL_whisker_r b <$> ms)
  end.

Definition SR_compose {A} (l r : StructuralRender A) : StructuralRender A :=
  match l, r with
  | SRid a, SRid _ => SRid a
  | SRid _, r => r
  | l, SRid _ => l
  | SRmors lm lms, SRmors rm rms => SRmors lm (lms ++ rm :: rms)
  end.

Definition SR_stack {A} (t b : StructuralRender A) : StructuralRender A :=
  SR_compose (SR_whisker_r (SR_dom b) t) (SR_whisker_l (SR_cod t) b).


Fixpoint gbpath_to_SR {A} {M : Mor (btree A)} 
  (fM : forall n m, M n m -> StructuralRender A)
  {a b} (p : a ~>[M] b) : StructuralRender A :=
  match p with
  | @brefl _ _ a => SRid a
  | bgen g => fM _ _ g
  | bprop t b => SR_stack (gbpath_to_SR fM t) (gbpath_to_SR fM b)
  | btrans l r => SR_compose (gbpath_to_SR fM l) (gbpath_to_SR fM r)
  end.


Definition bmon_to_SR {A} {a b : btree A} (m : bmonoidal a b) : StructuralRender A :=
  SRid a.

Definition bsym_to_SR {A} {a b : btree A} (m : bsymmetric a b) : StructuralRender A :=
  match m with
  | bmonoidal_bsymmetric m => bmon_to_SR m
  | @bsymm _ a b => SRmors (0, RenderSwap a b, 0) []
  end.


Definition baut_to_SR {A} {a b : btree A} (m : bautonomous a b) : StructuralRender A :=
  match m with
  | bsymmetric_bautonomous m => bsym_to_SR m
  | @bcup _ a => SRmors (0, RenderCup a, 0) []
  | @bcap _ a => SRmors (0, RenderCap a, 0) []
  end.

Definition bpath_to_SR {A} {a b : btree A} (p : a ~> b) : StructuralRender A :=
  SRid a.

Lemma bpath_to_SR_eq {A} {a b : btree A} (p : a ~> b) : 
  bpath_to_SR p = gbpath_to_SR (λ _ _, bmon_to_SR) p.
Proof.
  induction p.
  - easy.
  - easy.
  - cbn.
    rewrite <- IHp1, <- IHp2.
    easy.
  - cbn.
    rewrite <- IHp1, <- IHp2.
    easy.
Qed.

Definition sbpath_to_SRE {A} {a b : btree A} (p : a ~>ₛ b) : StructuralRender A :=
  gbpath_to_SR (λ _ _, bsym_to_SR) p.

Definition abpath_to_SRE {A} {a b : btree A} (p : a ~>ₐ b) : StructuralRender A :=
  gbpath_to_SR (λ _ _, baut_to_SR) p.


(* Import stdpp.sorting.

Definition SRL_composable {A} (l r : StructuralRenderLayer A) : Prop :=
  SRL_cod l =@{list A} SRL_dom r.

Definition SR_composable {A} (r : StructuralRender A) : Prop :=
  match r with
  | SRid c => True
  | SRmors m ms => Sorted SRL_composable (m :: ms)
  end.
 *)

