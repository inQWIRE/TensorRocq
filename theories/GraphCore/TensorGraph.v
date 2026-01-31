Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp.

(* Basic definitions and structural operations on TensorGraphs *)

Fixpoint test {n : nat} (l : vec nat n) : vec nat n :=
  match n, l with
  | 0, _ => Vector.nil
  | S k, _ => l
  end.


Notation edge := (prod nat nat).

(* A labelled edge *)
Notation labedge := (prod nat edge).

Declare Scope cohg_scope.

Definition HyperGraph (T : Type) := Pmap (T * list positive * list positive).

(* A graph with nodes labeled by elements of [T] *)
Record CospanHyperGraph {T : Type} {n m : nat} := mk_cohg {
  hedges : HyperGraph T;
  inputs : vec positive n;
  outputs : vec positive m;
}.
#[global] Arguments CospanHyperGraph T : clear implicits.
#[global] Arguments mk_cohg {_} {_ _} (_ _ _) : assert.

Check hedges.

Notation " ins -> hedges <- outs " := (mk_cohg hedges ins outs) : cohg_scope.

Open Scope cohg_scope.

Definition CospanHyperGraph2triple {T} {n m : nat} (tg : CospanHyperGraph T n m) :=
  (tg.(hedges), (tg.(inputs), tg.(outputs))).

#[global] Coercion CospanHyperGraph2triple : CospanHyperGraph >-> prod.

Definition CospanHyperGraph2HyperGraph {T} {n m} (tg : CospanHyperGraph T n m) := tg.(hedges).
#[global] Coercion CospanHyperGraph2HyperGraph : CospanHyperGraph >-> HyperGraph.

Section CospanHyperGraph.

  Context {T : Type}.
  Context {n m : nat}.

  Let CoHyGraph := (CospanHyperGraph T n m).

  Implicit Types chg : CoHyGraph.

  Definition add_vertex_r (n : positive) (v : positive) (tg : CoHyGraph) : CoHyGraph :=
  tg.(inputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) => 
        match tipop with
        | (t, ip, op) => (t, ip, v::op)
        end)
      n
      tg.(hedges))
  <- tg.(outputs).

  Definition add_vertex_l {T : Type} {o p} (n : positive) (v : positive) (tg : CospanHyperGraph T o p) : CospanHyperGraph T o p :=
  tg.(inputs) ->
    (alter
      (fun tipop : (T * list positive * list positive) => 
        match tipop with
        | (t, ip, op) => (t, v::ip, op)
        end)
      n 
      tg.1)
  <- tg.(outputs).

  Definition add_edge {T : Type} {o p} (n : positive) (t : T) (tg : CospanHyperGraph T o p) :
  CospanHyperGraph T o p :=
    tg.2.1 -> (<[ n := (t, [], []) ]> tg.1) <- tg.2.2.

  (* Instance insert_hg {T: Type} : Insert positive T (HyperGraph T) := {
    insert := add_edge 
  }. *)

  #[global] Instance empty_cohg {T : Type} : Empty (CospanHyperGraph T 0 0) := {
    empty := Vector.nil -> ∅ <- Vector.nil
  }.

  Definition add_input {n m} (p : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T (S n) m :=
  Vector.cons p tg.2.1 -> tg.1 <- tg.2.2.

  Definition add_output {n m} (p : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T n (S m) :=
  tg.2.1 -> tg.1 <- Vector.cons p tg.2.2.

  Local Open Scope positive.
  Local Open Scope vector_scope.

  Definition example_cohg : CospanHyperGraph positive 0 0 := 
    ([#] -> {[ 1 := (1, [], []); 2:= (2, [], []) ]} <- [#]).

  Compute example_cohg.

(* is_key explicitly only depends on the nodes *)
Definition is_key (tm : gmap nat T) (n : nat) : Prop :=
  is_Some (tm !! n).

Definition is_input (tm : gmap nat T) (nm : edge) : Prop :=
  is_key tm (fst nm).

Definition is_output (tm : gmap nat T) (nm : edge) : Prop :=
  is_key tm (snd nm).

Definition is_internal tm (e : edge) :=
  is_key tm (fst e) /\ is_key tm (snd e).

Definition not_internal tm (e : edge) :=
  ~ is_internal tm e.


(* Definition internal_edges tg :=
  filter (is_internal tg.1) tg.2. *)

(* Definition external_edges tg :=
  tg.2.1 +++ tg.2.2. *)

(* Definition i_internal_edges tg :=
  enumerate (internal_edges tg). *)

(* Definition i_external_edges tg :=
  enumerate (external_edges tg). *)

Definition is_node_input (k : nat) (e : edge) : Prop :=
  e.2 = k.

#[export] Instance is_node_input_dec k e : Decision (is_node_input k e) := 
  decide_rel _ (e.2) k.

Definition is_node_output (k : nat) (e : edge) : Prop :=
  e.1 = k.

#[export] Instance is_node_output_dec k e : Decision (is_node_output k e) := 
  decide_rel _ (e.1) k.

Definition node_input_edges (k : nat) (les : list labedge) : list labedge :=
  filter (is_node_input k ∘ snd) les.

Definition node_output_edges (k : nat) (les : list labedge) : list labedge :=
  filter (is_node_output k ∘ snd) les.



Definition in_arity (es : list edge) (k : nat) :=
  length (filter (is_node_input k) es).

Definition out_arity (es : list edge) (k : nat) :=
  length (filter (is_node_output k) es).

(* Definition add_edge (n : positive) (t : T)
  (tg : TensorGraph) : TensorGraph :=
  tg.(inputs) -> (<[n := (t, [], [])]> tg.1) <- tg.(outputs). *)

(* Definition add_vertex_r (n : positive) (v : postiive) (tg : TensorGraph) := 
  mk_cohg () *)

(* Definition add_edge (e : edge)
  (tg : TensorGraph) : TensorGraph :=
  mk_cohg tg.1 (e :: tg.2). *)

(* Definition empty_graph : TensorGraph := mk_cohg ∅ []. *)

(* Definition graph_insize (tg : TensorGraph) : nat := size (inputs tg). *)
(* Definition graph_outsize (tg : TensorGraph) : nat := size (outputs tg). *)


(* Definition sorted_inputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (inputs tg). *)

(* Definition sorted_outputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (outputs tg). *)




End CospanHyperGraph.

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with CospanHyperGraph.
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_graph : graph_scope. *)

(* Open Scope graph_scope.
Open Scope nat. *)

