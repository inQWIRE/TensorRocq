Require Import TensorGraph.
Require Import Tensor.
From stdpp Require Import gmap. 
From stdpp Require Import list.
Require Import TensorExprDBSyntax.
Require Import ZXCore.
From QuantumLib Require Import Complex.


Notation "'ZXG'" := (TensorGraph (R:=C) (A:=bool) (T:=(bool*R)) (TensT:=ZXCALC)) (at level 0).

Check ZXG.

Definition rotation (n : nat) (zxg : ZXG) : option R :=
  snd <$> (get_vertex n zxg).

Definition vertex_type (n : nat) (zxg : ZXG) : option bool :=
  fst <$> (get_vertex n zxg).

Definition hopf (n m : nat) (zxg : ZXG) : ZXG :=
  remove_edge n m (remove_edge n m zxg).

Definition option_eqb_bool (a : option bool) (b : option bool) : bool :=
  match a with
  | Some x => match b with
              | Some y => eqb x y
              | None => false
              end
  | None => false
  end.

Definition fuse (n m : nat) (zxg : ZXG) : ZXG :=
  let preds' := (fun l => (l, n)) <$> predecessors m zxg in
  let succs' := (fun r => (n, r)) <$> successors m zxg in
  let preds'' := (fun l => (l, n)) <$> predecessors n zxg in
  let succs'' := (fun r => (n, r)) <$> successors n zxg in 
  let rot_n : option R := rotation n zxg in
  let rot_m : option R := rotation m zxg in
  if option_eqb_bool (vertex_type n zxg) (vertex_type m zxg) then 
    match rot_n with
    | Some r1 => match rot_m with
                | Some r2 => add_vertex n (true, (r1 + r2)%R) (add_edges (preds' ++ preds'' ++ succs' ++ succs'') (remove_vertex n (remove_vertex m zxg)))
                | None => zxg
                end
    | None => zxg
    end
    else
      zxg.

