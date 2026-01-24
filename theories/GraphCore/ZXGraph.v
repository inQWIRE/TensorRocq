Require Import ZXCore.
From QuantumLib Require Import Complex.
Require Import TensorGraphSemantics.
Open Scope nat_scope.

Notation "'ZXG'" := (TensorGraph (bool * R)) (at level 0).

(* Check ZXG. *)

Instance ZXCALC : TensorLike C bool (bool * R) := {
  interpretTensor (x : bool * R) := match x with
  | (true, r)  => fun n m => @zsp n m r
  | (false, r) => fun n m => @zsp n m r
  end
}.

Definition example_graph : TensorGraph (bool*R) := 
  ∅G +[ 1 := (true, 0%R) ]
     +[ 3 := (true, 0%R) ]
     +{ (6, 1) ; (5, 1) ; (1,2) ; (1,3) ; (1,2) ; (1,3) ; (1,4) }.


(* TODO: Rework these and put them in TensorGraph *)

Definition relabel_vertex {T} (n m : nat) (tg : TensorGraph T) : TensorGraph T :=
  let '(mk_tg verts edges) := tg in
  let verts' := 
    match lookup n verts with
    | Some t => <[m := t]> (delete n verts)
    | None => verts
    end in
  let relabel_idx i := if i =? n then m else i in
  let edges' := (fun e : (nat * nat) => 
    let (s, d) := e in (relabel_idx s, relabel_idx d)) <$> edges in
  mk_tg verts' edges'.


Definition has_edge (n m : nat) (es : list edge) : Prop :=
  (n, m) ∈ es \/ (m, n) ∈ es.

Definition connected {T} (n m : nat) (tg : TensorGraph T) : Prop :=
  is_key tg.1 n /\ is_key tg.1 m /\ has_edge n m tg.2.

Definition remove_vertex {T} (n : nat) (tg : TensorGraph T) : TensorGraph T :=
  let '(mk_tg verts edges) := tg in
  let verts' := delete n verts in
  let edges' := 
    filter (fun e : (nat * nat) => let (s, d) := e in negb ((s =? n) || (d =? n))) edges in
  mk_tg verts' edges'.

Definition remove_edge {T} (n m : nat) (tg : TensorGraph T) : TensorGraph T:=
  let '(mk_tg verts edges) := tg in
  let edges' := filter (fun e : (nat * nat) => let (s, d) := e in ((s =? n) && (d =? m) || (s =? m) && (d =? n))) edges in
  mk_tg verts edges'.

Definition successors {T} (n : nat) (tg : TensorGraph T) : list nat :=
  map snd (filter (fun e => fst e =? n) (snd tg)).

Definition predecessors {T}(n : nat) (tg : TensorGraph T) : list nat :=
  map fst (filter (fun e => snd e =? n) (snd tg)).

Fixpoint add_edges {T} (es : list (nat * nat)) 
  (tg : TensorGraph T) :=
  match es with
  | [] => tg
  | e :: es' => add_edge e (add_edges es' tg)
  end.


Definition rotation (n : nat) (zxg : ZXG) : option R :=
  snd <$> (zxg.1 !! n).

Definition vertex_type (n : nat) (zxg : ZXG) : option bool :=
  fst <$> (zxg.1 !! n).

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
    | Some r1 => 
      match rot_m with
      | Some r2 => add_vertex n (true, (r1 + r2)%R) 
        (add_edges (preds' ++ preds'' ++ succs' ++ succs'') (remove_vertex n (remove_vertex m zxg)))
      | None => zxg
      end
    | None => zxg
    end
    else
      zxg.
