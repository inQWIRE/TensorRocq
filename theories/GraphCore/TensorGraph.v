Require Import Tensor.
From stdpp Require Import gmap. 
From stdpp Require Import list.
Require Import TensorExprDBSyntax.
Require Import ZXCore.
From QuantumLib Require Import Complex.

Definition TensorMap {R : Type} (A : Type) (T : Type) (TensT : TensorClass R A T) := 
  gmap nat T.

Definition EdgeSet := list (nat * nat).

Definition TensorGraph {R} {A} {T} {TensT : TensorClass R A T} := 
  (gmap nat T * EdgeSet)%type.

Definition is_key {R} {A} {T} {TensT : TensorClass R A T} (n : nat) 
  (tg : TensorGraph (R:=R) (A:=A) (T:=T)) : bool :=
  match (lookup n (fst tg)) with
  | Some _ => true
  | None => false
  end.

Definition is_input {R} {A} {T} {TensT : TensorClass R A T} (nm : nat * nat)
  (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key (fst nm) tg.

Definition is_output {R} {A} {T} {TensT : TensorClass R A T} (nm : nat * nat)
  (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key (snd nm) tg.

Definition count_inputs
  {R} {A} {T} {TensT : TensorClass R A T} (tg : TensorGraph (R:=R) (A:=A)) : nat := 
  length (filter (fun x => is_input x tg) (snd tg)).

Definition count_outputs
  {R} {A} {T} {TensT : TensorClass R A T} (tg : TensorGraph (R:=R) (A:=A)) : nat := 
  length (filter (fun x => is_output x tg) (snd tg)).

Definition graph_semantics {R} {A} {T} {TensT : TensorClass R A T}
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
    loc (Pos.of_succ_nat (fst e)) in

  let mk_node ndt :=
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

Definition add_vertex {R} {A} {T} {TensT : TensorClass R A T} (n : nat) (t : T) 
  (tg : TensorGraph  (R:=R) (A:=A) (T:=T)) : TensorGraph (R:=R) (A:=A) (T:=T) :=
  (<[n := t]> (fst tg), snd tg).

Definition get_vertex {R} {A} {T} {TensT : TensorClass R A T}
  (n : nat) (tg : TensorGraph (R:=R) (A:=A) (T:=T)) : option T :=
  lookup n (fst tg).

Definition add_edge {R} {A} {T} {TensT : TensorClass R A T} (e : nat * nat) 
  (tg : TensorGraph (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  (fst tg, e :: snd tg).

Definition empty_graph {R} {A} {T} {TensT : TensorClass R A T} : TensorGraph (R:=R) (A:=A) := (∅, []).

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with TensorGraph.
Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope.
Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope.
Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope.
Notation "∅G" := empty_graph : graph_scope.

Fixpoint add_edges {R} {A} {T} {TensT : TensorClass R A T} (es : list (nat * nat)) 
  (tg : TensorGraph (R:=R) (A:=A)) :=
  match es with
  | [] => tg
  | e :: es' => add_edge e (add_edges es' tg)
  end.

Open Scope graph_scope.
Open Scope nat.

Instance ZXCALC : TensorClass C bool (bool * R) := {
  interpretTensor (x : bool * R) := match x with
  | (true, r)  => fun n m => @zsp n m r
  | (false, r) => fun n m => @zsp n m r
  end
}.

Definition example_graph : TensorGraph (R:=C) (A:=bool) (T:=(bool*R)) (TensT:=ZXCALC) := 
  ∅G +[ 1 := (true, 0%R) ]
     +[ 3 := (true, 0%R) ]
     +{ (6, 1) ; (5, 1) ; (1,2) ; (1,3) ; (1,2) ; (1,3) ; (1,4) }.


Definition relabel_vertex {R} {A} {T} {TensT : TensorClass R A T} (n m : nat) (tg : TensorGraph (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  let (verts, edges) := tg in
  let verts' := 
    match lookup n verts with
    | Some t => <[m := t]> (delete n verts)
    | None => verts
    end in
  let relabel_idx i := if i =? n then m else i in
  let edges' := (fun e : (nat * nat) => let (s, d) := e in (relabel_idx s, relabel_idx d)) <$> edges in
  (verts', edges').

Definition is_internal_vertex {R} {A} {T} {TensT : TensorClass R A T} (n : nat) (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key n tg.

Definition has_edge {R} {A} {T} {TensT : TensorClass R A T} (n m : nat) (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  existsb (fun e : (nat * nat) => let (s, d) := e in (s =? n) && (d =? m) || (s =? m) && (d =? n)) (snd tg).

Definition connected {R} {A} {T} {TensT : TensorClass R A T} (n m : nat) (tg : TensorGraph (R:=R) (A:=A)) : bool :=
  is_key n tg && is_key m tg && has_edge n m tg.

Definition remove_vertex {R} {A} {T} {TensT : TensorClass R A T} (n : nat) (tg : TensorGraph (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  let (verts, edges) := tg in
  let verts' := delete n verts in
  let edges' := filter (fun e : (nat * nat) => let (s, d) := e in negb ((s =? n) || (d =? n))) edges in
  (verts', edges').

Definition remove_edge {R} {A} {T} {TensT : TensorClass R A T} (n m : nat) (tg : TensorGraph (R:=R) (A:=A)) : TensorGraph (R:=R) (A:=A) :=
  let (verts, edges) := tg in
  let edges' := filter (fun e : (nat * nat) => let (s, d) := e in ((s =? n) && (d =? m) || (s =? m) && (d =? n))) edges in
  (verts, edges').

Definition successors {R} {A} {T} {TensT : TensorClass R A T} (n : nat) (tg : TensorGraph (R:=R) (A:=A)) : list nat :=
  map snd (filter (fun e => fst e =? n) (snd tg)).

Definition predecessors {R} {A} {T} {TensT : TensorClass R A T} (n : nat) (tg : TensorGraph (R:=R) (A:=A)) : list nat :=
  map fst (filter (fun e => snd e =? n) (snd tg)).
