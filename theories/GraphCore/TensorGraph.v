Require Import Tensor.
From stdpp Require Import gmap. 
From stdpp Require Import list.
Require Import TensorExprDBSyntax.
Require Import ZXCore.
From QuantumLib Require Import Complex.

Definition TensorMap {R : Type} (A : Type) := 
  gmap nat (DimensionlessTensor (R:=R) A).

Definition EdgeSet := list (nat * nat).

Definition TensorGraph {R} {A} := 
  ((TensorMap (R:=R) A) * EdgeSet)%type.

Definition is_key {R} {A} (n : nat) 
  (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  match (lookup n (fst tg)) with
  | Some _ => true
  | None => false
  end.

Definition is_input {R} {A} (nm : nat * nat)
  (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key (fst nm) tg.

Definition is_output {R} {A} (nm : nat * nat)
  (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key (snd nm) tg.

Definition count_inputs
  {R} {A} (tg : TensorGraph (R:=R) (A:=A)) : nat := 
  length (filter (fun x => is_input x tg) (snd tg)).

Definition count_outputs
  {R} {A} (tg : TensorGraph (R:=R) (A:=A)) : nat := 
  length (filter (fun x => is_output x tg) (snd tg)).

Definition graph_semantics {R} {A} 
  (tg : TensorGraph (R:=R) (A:=A)) : tensorlist :=

  let nodes := map_to_list (fst tg) in
  let edges := snd tg in

  let is_internal e := is_key (fst e) tg && is_key (snd e) tg in
  let not_internal e := negb (is_internal e) in

  let internal_edges := filter is_internal edges in
  let external_edges := filter not_internal edges in

  let index_list := imap (fun idx e => (idx, e)) in

  let i_internal_edges := index_list internal_edges in
  let i_external_edges := index_list external_edges in

  let mk_ivar (e : nat * (nat * nat)) :=
    rel (Pos.of_succ_nat (fst e)) in

  let offset := (Pos.of_succ_nat (length internal_edges)) in 

  let mk_ovar (e : nat * (nat * nat)) :=
    loc (Pos.of_succ_nat (fst e) + offset) in

  let mk_node (ndt : nat * DimensionlessTensor (R:=R) A) :=
    let n := fst ndt in
    let is_input e := snd (snd e) =? n in
    let is_output e := fst (snd e) =? n in
    let i_internal_inputs  := filter is_input i_internal_edges in
    let i_internal_outputs := filter is_output i_internal_edges in
    let i_external_inputs  := filter is_input i_external_edges in
    let i_external_outputs := filter is_output i_external_edges in
    (Pos.of_succ_nat n, 
      (mk_ivar <$> i_internal_inputs) ++ (mk_ovar <$> i_external_inputs), (mk_ivar <$> i_internal_outputs) ++ (mk_ovar <$> i_external_outputs)) in

  let body := mk_node <$> nodes in

  mk_tl (const 0%nat <$> internal_edges) body.

Definition add_vertex {R} {A} (n : nat) (t : DimensionlessTensor (R:=R) A) 
  (tg : TensorGraph  (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  (<[n := t]> (fst tg), snd tg).

Definition add_edge {R} {A} (e : nat * nat) 
  (tg : TensorGraph (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  (fst tg, e :: snd tg).

Definition empty_graph {R} {A} : TensorGraph (R:=R) (A:=A) := (∅, []).

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with TensorGraph.
Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope.
Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope.
Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope.
Notation "∅G" := empty_graph : graph_scope.

Open Scope graph_scope.
Open Scope nat.

Definition example_graph : TensorGraph (R:=C) (A:=bool) := 
  ∅G +[ 1 := (fun n m => @zsp n m 0) ]
     +[ 3 := (fun n m => @zsp n m 0) ]
     +{ (1,2) ; (1,3) ; (1,2) ; (1,3) ; (1,4) }.

Compute graph_semantics example_graph.
