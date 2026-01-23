From QuantumLib Require Import Complex.
Require Import Tensor.
From stdpp Require Import list sorting fin_maps.
From stdpp Require Import pmap gmap.
Require Import Aux_stdpp.
Require Import TensorExprDBSyntax TensorExprDBSemantics.
Require Import ZXCore.
Require ZifyBool.


Definition bcons (b : bool) (p : positive) : positive :=
  match b with 
  | true => xI p
  | false => xO p
  end.

#[global] 
Program Instance Op_bcons : ZifyClasses.BinOp 
  (T1:=bool) bcons := {
  TBOp b p := (2 * p + Z.b2z b)%Z;
}.
Next Obligation.
  cbn.
  intros [] ?; cbn; lia.
Qed.

Add Zify BinOp Op_bcons.

#[export] Instance bcons_inj2 : Inj2 (=) (=) (=) bcons.
Proof.
  hnf.
  lia.
Qed.

(* Combine input and output maps to get the local variable map *)
Definition gmaps_to_Pmap {A} 
  (minput : gmap nat A) (moutput : gmap nat A) : Pmap A :=
  (kmap (bcons false ∘ Pos.of_succ_nat) minput ∪ 
      kmap (bcons true ∘ Pos.of_succ_nat) moutput).



Notation TensorMap R A := 
  (gmap nat (@DimensionlessTensor R A)).

Section TensorGraph.

Context {R : Type} {A : Type}.


Definition EdgeSet := list (nat * nat).

Definition TensorGraph := 
  (TensorMap R A * EdgeSet)%type.

Definition is_key (tg : TensorGraph) (n : nat) : Prop :=
  is_Some (tg.1 !! n).

Definition is_input (tg : TensorGraph) (nm : nat * nat) : Prop :=
  is_key tg (fst nm).

Definition is_output (tg : TensorGraph) (nm : nat * nat) : Prop :=
  is_key tg (snd nm).

Definition count_inputs (tg : TensorGraph) : nat := 
  length (filter (is_input tg) (snd tg)).

Definition count_outputs (tg : TensorGraph) : nat := 
  length (filter (is_output tg) (snd tg)).

Definition inputs (tg : TensorGraph) : gset nat :=
  filter (fun k => ~ is_key tg k) $ 
    list_to_set tg.2.*1.

Definition outputs (tg : TensorGraph) : gset nat :=
  filter (fun k => ~ is_key tg k) $ 
    list_to_set tg.2.*2.


Definition is_internal tg (e : nat * nat) := 
  is_key tg (fst e) /\ is_key tg (snd e).

Definition not_internal tg (e : nat * nat) :=
  ~ is_internal tg e.


Definition internal_edges tg := 
  filter (is_internal tg) tg.2.

Definition external_edges tg :=
  filter (not_internal tg) tg.2.

Definition i_internal_edges tg := 
  enumerate (internal_edges tg).

Definition i_external_edges tg :=
  enumerate (external_edges tg).

Definition mk_internal_var (e : nat * (nat * nat)) :=
  rel (Pos.of_succ_nat (fst e)).

Definition mk_external_var (is_output : bool) (e : nat * (nat * nat)) :=
  loc (bcons is_output (Pos.of_succ_nat (if is_output then e.2.2 else e.2.1))).

Definition mk_node (tg : TensorGraph)
  (n : nat) : Idx * list var * list var :=
    let is_input e := snd (snd e) = n in
    let is_output e := fst (snd e) = n in
    let i_internal_inputs  := filter is_input (i_internal_edges tg) in
    let i_internal_outputs := filter is_output (i_internal_edges tg) in
    let i_external_inputs  := filter is_input (i_external_edges tg) in
    let i_external_outputs := filter is_output (i_external_edges tg) in
    (Pos.of_succ_nat n, 
      (mk_internal_var <$> i_internal_inputs) ++ 
        (mk_external_var false <$> i_external_inputs), 
      (mk_internal_var <$> i_internal_outputs) ++ 
        (mk_external_var true <$> i_external_outputs)).




Definition add_vertex (n : nat) (t : DimensionlessTensor (R:=R) A) 
  (tg : TensorGraph) : TensorGraph:=
  (<[n := t]> (fst tg), snd tg).

Definition add_edge (e : nat * nat) 
  (tg : TensorGraph) : TensorGraph :=
  (fst tg, e :: snd tg).

Definition empty_graph : TensorGraph := (∅, []).




Definition graph_tensorlist_semantics (tg : TensorGraph) : tensorlist :=
  mk_tl (const 0%nat <$> internal_edges tg) 
    (mk_node tg <$> (map_to_list (fst tg)).*1).

Definition graph_V : nat -> Type := fun _ => A.
Definition graph_Vsum `{Summable A} : forall k, Summable (graph_V k) 
  := fun _ => _.



(* Combine input and output maps to get the local variable map *)
Definition graph_ml (minput : gmap nat A) (moutput : gmap nat A) : 
  Pmap (Vval graph_V) :=
  @mk_Vval graph_V 0 <$> gmaps_to_Pmap minput moutput. 

Fixpoint graph_tensor_to_V_n_args_aux {n} : forall (t : vec A n -> R),
  V_n_args graph_V (replicate n 0) R :=
  match n with
  | O => fun t => t [#]
  | S n' => fun t => 
    fun a => graph_tensor_to_V_n_args_aux (t ∘ vcons a)
  end.

Definition graph_tensor_to_V_n_args {n m} (t : vec A n -> vec A m -> R) :=
  graph_tensor_to_V_n_args_aux (uncurry t ∘ Vector.splitat n).

Definition graph_mabs (tg : TensorGraph) : Pmap (@Vfunc R graph_V) :=
  kmap (Pos.of_succ_nat) $ map_imap (fun n (dt : DimensionlessTensor A) => 
    let node := mk_node tg n in 
    let inarity := length node.1.2 in 
    let outarity := length node.2 in 
    Some $ mk_Vfunc graph_V (replicate (inarity + outarity) 0)
      (graph_tensor_to_V_n_args (dt inarity outarity))
    ) tg.1.

Definition graph_map_semantics `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} 
  (tg : TensorGraph) 
  (minput : gmap nat A) (moutput : gmap nat A) : R :=
  tl_total_semantics (SR:=SR) graph_V (Vsum:=graph_Vsum)
    (graph_mabs tg)
    ∅
    (graph_ml minput moutput)
    (graph_tensorlist_semantics tg).

Definition graph_insize (tg : TensorGraph) : nat := size (inputs tg).
Definition graph_outsize (tg : TensorGraph) : nat := size (outputs tg).


Definition sorted_inputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (inputs tg).

Definition sorted_outputs (tg : TensorGraph) : list nat :=
  merge_sort le $ elements (outputs tg).


Definition graph_list_semantics `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} 
  (tg : TensorGraph) (ins : list A) (outs : list A) : R :=
  graph_map_semantics tg 
    (list_to_map $ zip (sorted_inputs tg) ins)
    (list_to_map $ zip (sorted_outputs tg) outs).

Definition graph_vector_semantics `{SR : SemiRing R rO rI radd rmul req} `{!Summable A} 
  (tg : TensorGraph) (ins : vec A (graph_insize tg)) (outs : vec A (graph_outsize tg)) : R :=
  graph_list_semantics tg (vec_to_list ins) (vec_to_list outs).

End TensorGraph.

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


Definition example_graph' : TensorGraph (R:=C) (A:=bool) := 
  ∅G +[ 1 := (fun n m => @zsp n m 0) ]
     +[ 3 := (fun n m => @zsp n m 0) ]
     +{ (1,2) ; (1,3) ; (3,4) }.

Compute graph_tensorlist_semantics example_graph.

Compute elements $ inputs example_graph.

Compute elements $ outputs example_graph.

Compute graph_tensorlist_semantics example_graph'.

Compute elements $ inputs example_graph'.

Compute elements $ outputs example_graph'.


(* 
From VyZX Require Import CoreData.

Open Scope ZX_scope.

Open Scope nat_scope.

Example example_graph'_map_semantics : forall b b',
  graph_map_semantics example_graph' 
    ∅ {[2:=b; 4:=b']} = 
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_map_semantics].
  unfold kron.
  cbn -[graph_map_semantics].
  intros [] []; cbn -[graph_map_semantics]; (etransitivity; 
    [unfold example_graph'; 
      remember @zsp as zsp' eqn:Hzsp; 
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp]; 
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.

Example example_graph'_list_semantics : forall b b',
  graph_list_semantics example_graph' 
    [] [b; b'] = 
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_list_semantics].
  unfold kron.
  cbn -[graph_list_semantics].
  intros [] []; cbn -[graph_list_semantics]; (etransitivity; 
    [unfold example_graph'; 
      remember @zsp as zsp' eqn:Hzsp; 
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp]; 
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.

Example example_graph'_vector_semantics : forall b b',
  graph_vector_semantics example_graph' 
    [# ] [# b; b'] = 
  ⟦ Z 0 2 0 ⟷ (— ↕ Z 1 1 0) ⟧
    (Bits.funbool_to_nat 2 ([b;b'] !!!.)) O.
Proof.
  cbn -[graph_vector_semantics].
  unfold kron.
  cbn -[graph_vector_semantics].
  intros [] []; cbn -[graph_vector_semantics]; (etransitivity; 
    [unfold example_graph'; 
      remember @zsp as zsp' eqn:Hzsp; 
      vm_compute|Csimpl; reflexivity]);
  subst zsp'; cbn -[Cexp]; 
  change R0 with 0%R; rewrite ?Cexp_0; lca.
Qed.
 *)
