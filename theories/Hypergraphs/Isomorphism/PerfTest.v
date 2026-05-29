From TensorRocq Require Import CospanHyperGraph.

#[local] Instance pos_equiv : Equiv positive := eq.

Definition PathGraph {T} {n : nat}
  (v : vec T n) : CospanHyperGraph T 1 1 :=
  mk_cohg (mk_hg (list_to_map 
    (imap (λ i t, (Pos.of_succ_nat i, 
      (t, [Pos.of_succ_nat i], [Pos.of_succ_nat (S i)]))) v)) ∅) 
    [# xH] [# Pos.of_succ_nat (S n) ].

Definition PathGraph' {T} {n : nat}
  (v : vec T n) : CospanHyperGraph T 1 1 :=
  mk_cohg (mk_hg (list_to_map 
    (imap (λ i t, (Pos.of_succ_nat i, 
      (t, [Pos.of_succ_nat (S n - i)], [Pos.of_succ_nat (S n - (S i))]))) v)) ∅) 
    [# Pos.of_succ_nat (S n) ] [# xH].

Definition BinTreeGraphLayer {T} (n : nat) (t : T) : 
  CospanHyperGraph T (2 * n) n :=
  mk_cohg (mk_hg 
    (list_to_map
      ((λ i, (Pos.of_succ_nat i, (t, 
        xO ∘ Pos.of_succ_nat <$> [2 * i; S (2*i)], 
          [xI (Pos.of_succ_nat i)]))) <$> seq 0 n)
    )
    ∅)
    (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (2 * n)))
    (vmap (xI ∘ Pos.of_succ_nat) (vseq 0 n)).

Fixpoint BinTreeGraph {T} {n : nat} (v : vec T n) : 
  CospanHyperGraph T (2 ^ n) 1 :=
  match v with
  | [#] => id_graph 1
  | t ::: v => compose_graphs (BinTreeGraphLayer _ t) (BinTreeGraph v)
  end.


Definition graph_iso_partial_test `{Equiv T, RelDecision T T equiv}
  {n m} (cohg cohg' : CospanHyperGraph T n m) : bool :=
  weak_graph_iso_partial_test cohg cohg'.
  
Ltac test_BinTreeGraph_BinTreeGraph n :=
  idtac n;
  time (
  let _ := eval vm_compute in 
  (let v := vmap Pos.of_succ_nat (vseq 0 n)  in
  (graph_iso_partial_test (BinTreeGraph v) (BinTreeGraph v))) in idtac).

Ltac test_BinTreeGraph_BinTreeGraph_sameval n :=
  idtac n;
  time (
  let _ := eval vm_compute in 
  (let v := vmap (λ _, xH) (vseq 0 n)  in
  (graph_iso_partial_test (BinTreeGraph v) (BinTreeGraph v))) in idtac).


Ltac test_PathGraph_PathGraph' n :=
  idtac n;
  time (
  let _ := eval vm_compute in 
  (let v := vmap Pos.of_succ_nat (vseq 0 n)  in
  (graph_iso_partial_test (PathGraph v) (PathGraph' v))) in idtac).


Ltac test_PathGraph_PathGraph'_sameval n :=
  idtac n;
  time (
  let _ := eval vm_compute in 
  (let v := vmap (λ _, xH) (vseq 0 n)  in
  (graph_iso_partial_test (PathGraph v) (PathGraph' v))) in idtac).

Ltac test_PathGraph_PathGraph_sameval n :=
  idtac n;
  time (
  let _ := eval vm_compute in 
  (let v := vmap (λ _, xH) (vseq 0 n)  in
  (graph_iso_partial_test (PathGraph v) (PathGraph v))) in idtac).

From TensorRocq Require Import TestingAlt.


Ltac test_PathGraph_PathGraph_sameval' n :=
  idtac n;
  time (
  let x := eval vm_compute in 
  (let v := vmap (λ _, xH) (vseq 0 n)  in
  (test_graph_isos_by_vertex_map (PathGraph v) (PathGraph v))) in idtac x).


Ltac test_PathGraph_PathGraph_sameval'' n :=
  idtac n;
  time (
  let x := eval vm_compute in 
  (let v := vmap (λ _, xH) (vseq 0 n)  in
  (prod_map (map_to_list ∘ IsoAux.Piso_map) (map_to_list ∘ IsoAux.Piso_map) <$>
     (graph_isos_by_vertex_map (PathGraph v) (PathGraph v)))) in idtac x).


(* Eval vm_compute in (size (vertices (BinTreeGraph (vmap (λ _, xH) (vseq 0 4))))). *)
(*
Goal True.

(* test_PathGraph_PathGraph_sameval' 2. *)


Eval vm_compute in 
  map_to_list (
    (PathGraph (vseq 0 2)) :> Pmap _).
Eval vm_compute in 
  map_to_list (prod_map elements elements <$> 
    vertex_map (PathGraph (vseq 0 2))).

Eval vm_compute in 
  (let n := 2 in 
  let v := vmap (λ _, xH) (vseq 0 n)  in
  ((* prod_map (map_to_list ∘ IsoAux.Piso_map) (map_to_list ∘ IsoAux.Piso_map) <$> *)
     (graph_isos_by_vertex_map (PathGraph v) (PathGraph v)))).

test_PathGraph_PathGraph_sameval'' 2.

Eval vm_compute in 
  map_to_list (
    (PathGraph (vseq 0 2)) :> Pmap _).
Eval vm_compute in 
  map_to_list (prod_map elements elements <$> 
    vertex_map (PathGraph (vseq 0 2))).

test_PathGraph_PathGraph_sameval'' 1.


test_BinTreeGraph_BinTreeGraph 1.
test_BinTreeGraph_BinTreeGraph 2.
test_BinTreeGraph_BinTreeGraph 3.
test_BinTreeGraph_BinTreeGraph 4.
test_BinTreeGraph_BinTreeGraph 5.
test_BinTreeGraph_BinTreeGraph 6.
test_BinTreeGraph_BinTreeGraph 7.
test_BinTreeGraph_BinTreeGraph 8.

test_BinTreeGraph_BinTreeGraph_sameval 1.
test_BinTreeGraph_BinTreeGraph_sameval 2.
test_BinTreeGraph_BinTreeGraph_sameval 3.
test_BinTreeGraph_BinTreeGraph_sameval 4.
test_BinTreeGraph_BinTreeGraph_sameval 5.
test_BinTreeGraph_BinTreeGraph_sameval 6.
test_BinTreeGraph_BinTreeGraph_sameval 7.
test_BinTreeGraph_BinTreeGraph_sameval 8.

test_PathGraph_PathGraph_sameval 1.
test_PathGraph_PathGraph_sameval 2.
test_PathGraph_PathGraph_sameval 3.
test_PathGraph_PathGraph_sameval 4.
test_PathGraph_PathGraph_sameval 5.
test_PathGraph_PathGraph_sameval 6.
test_PathGraph_PathGraph_sameval 7.
test_PathGraph_PathGraph_sameval 8.
test_PathGraph_PathGraph_sameval 9.
test_PathGraph_PathGraph_sameval 10.
test_PathGraph_PathGraph_sameval 11.
test_PathGraph_PathGraph_sameval 12.
test_PathGraph_PathGraph_sameval 13.

test_PathGraph_PathGraph'_sameval 1.
test_PathGraph_PathGraph'_sameval 2.
test_PathGraph_PathGraph'_sameval 3.
test_PathGraph_PathGraph'_sameval 4.
test_PathGraph_PathGraph'_sameval 5.
test_PathGraph_PathGraph'_sameval 6.
test_PathGraph_PathGraph'_sameval 7.
test_PathGraph_PathGraph'_sameval 8.
test_PathGraph_PathGraph'_sameval 9.
test_PathGraph_PathGraph'_sameval 10.
test_PathGraph_PathGraph'_sameval 11.
test_PathGraph_PathGraph'_sameval 12.
test_PathGraph_PathGraph'_sameval 13.

test_PathGraph_PathGraph' 10.
test_PathGraph_PathGraph' 20.
test_PathGraph_PathGraph' 30.
test_PathGraph_PathGraph' 40.
test_PathGraph_PathGraph' 50.
test_PathGraph_PathGraph' 60.
test_PathGraph_PathGraph' 70.
test_PathGraph_PathGraph' 80.
test_PathGraph_PathGraph' 90.
test_PathGraph_PathGraph' 100.
test_PathGraph_PathGraph' 110.
test_PathGraph_PathGraph' 120.
test_PathGraph_PathGraph' 130.
test_PathGraph_PathGraph' 140.
test_PathGraph_PathGraph' 150.
test_PathGraph_PathGraph' 160.
test_PathGraph_PathGraph' 170.
test_PathGraph_PathGraph' 180.
test_PathGraph_PathGraph' 190.
test_PathGraph_PathGraph' 200.
test_PathGraph_PathGraph' 300.
test_PathGraph_PathGraph' 400.
test_PathGraph_PathGraph' 500.
test_PathGraph_PathGraph' 600.
test_PathGraph_PathGraph' 700.
test_PathGraph_PathGraph' 800.




 *)
