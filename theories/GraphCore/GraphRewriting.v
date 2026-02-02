Require Import TensorGraph.
Require Import HyperGraph.
Require Import TESyntax.
Require Import Aux_pos.
From stdpp Require Export pmap gmap.


(* An implementation of double pushout (DPO) rewriting *)

Section DPO.


  Context {T : Type}.
    

  (* Definition new_vertex_between {n m} (l r : positive) (tg : CospanHyperGraph T n m) : CospanHyperGraph T n m. *)

  (* Definition disjoint_union (hg : Pmap (T * list positive * list positive))

  Definition add_vertex (tg : CospanHyperGraph T) (e : positive * positive) : CospanHyperGraph T.
  apply mk_cohg.
  - destruct e.

    admit.
  - exact tg.2.1.
  - exact tg.2.2. *)


  Definition positive_subst (p p' : positive) (o : positive) : positive :=
    if decide (p = o) then p' else o.

  Notation "[ p |-> p' ]" := (positive_subst p p').

  Print relabel_delt.

  Fixpoint propogate_subst {n} (ps : vec (positive * positive) n) : vec (positive * positive) n :=
  match n, ps with
  | 0, _ => [#]
  | (S k), _ => 
    let (p, p') := Vector.hd ps in
    let ps' := Vector.tl ps in
      (p, p') ::: propogate_subst (vmap (relabel_delt ([p |-> p'])) ps')
  end.

  Fixpoint vzipwith {n} {B C D} (f : B -> C -> D) (bs : vec B n) (cs : vec C n) : vec D n :=
  match n, bs, cs with
  | 0, _, _ => [#]
  | (S k), bs, cs => (f (Vector.hd bs) (Vector.hd cs)) ::: vzipwith f (Vector.tl bs) (Vector.tl cs)
  end.

  Notation vzip := (vzipwith pair).

  Check relabel_graph.

  Fixpoint subst_by_vec {n} (ps : vec (positive * positive) n) (p : positive) : positive :=
    match ps with
    | [#] => p
    | (a, b) ::: ps' => subst_by_vec ps' ([a |-> b] p)
    end.

  Reserved Notation "tgl ; tgr" (at level 50).
  Definition compose_safe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := 
        propogate_subst (vzip (vmap (bcons false) tgl.(outputs)) (vmap (bcons true) tgr.(inputs))) in 
     relabel_graph (subst_by_vec connected_substs) ((vmap (bcons false) tgl.(inputs)) -> tgl.(hedges) ⊎ tgr.(hedges) <- (vmap (bcons true) tgr.(outputs))).

  Definition compose {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
    let connected_substs := propogate_subst (vzip (tgl.(outputs)) (tgr.(inputs))) in
    relabel_graph (subst_by_vec connected_substs) 
      (tgl.(inputs) -> tgl.(hedges) ∪ tgr.(hedges) <- tgr.(outputs)).

End DPO.
