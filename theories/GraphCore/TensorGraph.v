Require Export Tensor.
From stdpp Require Export list sorting fin_maps.
From stdpp Require Export pmap gmap.
Require Export Aux_stdpp.

(* Basic definitions and structural operations on TensorGraphs *)


Notation edge := (prod nat nat).

(* A labelled edge *)
Notation labedge := (prod nat edge).

(* A graph with nodes labeled by elements of [T] *)
Record TensorHyperGraph {T : Type} := mk_tg {
  nodes : Pmap (T * list positive * list positive);
  inputs : list positive;
  outputs : list positive;
}.
#[global] Arguments TensorHyperGraph T : clear implicits.
(* #[global] Arguments mk_tg {_} (_ _) : assert. *)

Definition TensorGraph2triple {T} (tg : TensorHyperGraph T) :=
  (tg.(nodes), (tg.(inputs), tg.(outputs))).

#[global] Coercion TensorGraph2triple : TensorHyperGraph >-> prod.


Section TensorGraph.

Context {T : Type}.

Let TensorGraph := (TensorHyperGraph T).

Implicit Types tg : TensorGraph.

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


(* Definition inputs (tg : TensorGraph) : gset nat :=
  filter (fun k => ~ is_key tg.1 k) $
    list_to_set tg.2.*1.

Definition outputs (tg : TensorGraph) : gset nat :=
  filter (fun k => ~ is_key tg.1 k) $
    list_to_set tg.2.*2. *)

(* Definition internal_edges tg :=
  filter (is_internal tg.1) tg.2.

Definition external_edges tg :=
  filter (not_internal tg.1) tg.2.

Definition i_internal_edges tg :=
  enumerate (internal_edges tg).

Definition i_external_edges tg :=
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

(* Definition add_vertex (n : nat) (t : T)
  (tg : TensorGraph) : TensorGraph :=
  mk_tg (<[n := t]> tg.1) tg.2. *)

(* Definition add_edge (e : edge)
  (tg : TensorGraph) : TensorGraph :=
  mk_tg tg.1 (e :: tg.2). *)

(* Definition empty_graph : TensorGraph := mk_tg ∅ []. *)

(* Definition graph_insize (tg : TensorGraph) : nat := size (inputs tg). *)
(* Definition graph_outsize (tg : TensorGraph) : nat := size (outputs tg). *)


(* Definition sorted_inputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (inputs tg). *)

(* Definition sorted_outputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (outputs tg). *)




End TensorGraph.

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Bind Scope graph_scope with TensorHyperGraph.
(* Notation "g +[ n := t ]" := (add_vertex n t g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e }" := (add_edge e g) (at level 50, left associativity) : graph_scope. *)
(* Notation "g +{ e0 ; .. ; en }" := (add_edge en .. (add_edge e0 g) ..) (at level 50, left associativity) : graph_scope. *)
(* Notation "∅G" := empty_graph : graph_scope. *)

Open Scope graph_scope.
Open Scope nat.

