Require Import TensorGraph.
Require Import HyperGraph.
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

Search ((_ -> _) -> vec _ _ -> _).

  Reserved Notation "tgl ; tgr" (at level 50).
  Definition compose_safe {n m o} (tgl : CospanHyperGraph T n m) (tgr : CospanHyperGraph T m o) : CospanHyperGraph T n o :=
     (vmap xI tgl.(inputs)) -> tgl.(hedges) ⊎ tgr.(hedges) <- (vmap xO tgr.(outputs)).

  Definition compose {n m} (tgl tgr : CospanHyperGraph T n m) : CospanHyperGraph T n m :=
    tgl.(inputs) -> tgl.(hedges) ∪ tgr.(hedges) <- tgr.(outputs).

  

End DPO.
