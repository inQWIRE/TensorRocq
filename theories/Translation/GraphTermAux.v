Require Export Setoid. 
From stdpp Require Export base list.
From TensorRocq Require Import Aux_relset Aux_pos.


(* FIXME: Move *)
Tactic Notation "vm_eval" uconstr(pat) :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in *;
  vm_compute in Hx;
  subst x.

Tactic Notation "vm_eval" uconstr(pat) "in" 
  ne_hyp_list_sep(H, ",") :=
  let x := fresh "x" in
  let Hx := fresh "Hx" in
  remember pat as x eqn:Hx in H;
  vm_compute in Hx;
  subst x.


(* FIXME: Move *)
Definition rel_preimage_dec {A B} (f : A -> B) (R : relation B) :
  RelDecision R -> RelDecision (rel_preimage f R) := fun HR x y => HR (f x) (f y).

#[export] Hint Extern 0 (RelDecision (rel_preimage ?f ?R)) => 
  notypeclasses refine (rel_preimage_dec f R _) : typeclass_instances.

Definition rel_preimage_dec' {A B} (f : A -> B) (R : relation B) x y :
  Decision (R (f x) (f y)) -> Decision (rel_preimage f R x y) := λ H, H.

#[export] Hint Extern 0 (Decision (rel_preimage ?f ?R ?x ?y)) => 
  notypeclasses refine (rel_preimage_dec' f R x y _) : typeclass_instances.




(* Heuristic for ordering input lists (hence edges): which have 
  more lower inputs? *)

Definition pos_lists_earlier (ins1 ins2 : list positive) : Z :=
  foldr (λ '(i1, i2), Z.add (Z.sgn (Z.pos_sub i1 i2))) 0%Z (cprod ins1 ins2).





From TensorRocq Require Import HyperGraph.


Definition get_extractable_edges {T} (inputs : Pset)
  (edges : Pmap (HyperEdge T)) :=
  filter (λ ktio, Forall (.∈ inputs) ktio.2.1.2) edges.

Fixpoint get_simultaneously_extractable_edges_aux {T} (inputs : list positive) 
  (n : nat) (es : list (positive * HyperEdge T)) : 
  list (positive * HyperEdge T) * (list positive * list (positive * HyperEdge T)) :=
  match n with 
  | 0 => ([], (inputs, es))
  | S n' =>
    match es with 
    | [] => ([], (inputs, []))
    | ktio :: es => 
      if decide (Forall (.∈ inputs) ktio.2.1.2) then 
        prod_map (ktio ::.) id $ get_simultaneously_extractable_edges_aux 
          (filter (.∉ ktio.2.1.2) inputs) n es
      else
        prod_map id (prod_map id (ktio ::.)) $ get_simultaneously_extractable_edges_aux inputs n es
    end
  end.

Definition get_simultaneously_extractable_edges {T} (inputs : list positive) 
  (es : Pmap (HyperEdge T)) : list (positive * HyperEdge T) * (list positive * Pmap (HyperEdge T)) :=
  prod_map id (prod_map id list_to_map) $ 
    let es' := map_to_list es in 
    get_simultaneously_extractable_edges_aux inputs (length es') es'.



Definition sort_extracted_edges {T} (es : list (positive * HyperEdge T)) :
  list (positive * HyperEdge T) :=
  merge_sort (rel_preimage (λ ktio, ktio.2.1.2) 
    (λ ins1 ins2, (pos_lists_earlier ins1 ins2) < 0)%Z) es.



