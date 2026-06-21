From TensorRocq Require Import GraphRewriting CospanHyperGraph.Facts
  Isomorphism.IsoAux.


Definition frob_enlarge_graph {T n m}
  (cohg : CospanHyperGraph T n m)
    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *)
    CospanHyperGraph T (j + i + n) m :=
  mk_cohg
    (mk_hg
      (map_imap (λ e tio,
        if decide (is_Some (me.(Psurj_invmap) !! e)) then None
          else
            Some $ relabel_abs (λ v,
              if decide (is_Some (mv.(Psurj_invmap) !! v)) then
                (encode (e, v))~1~1
              else
                v~0~1)
              tio) (hyperedges cohg))
      (set_omap (λ v, if decide (is_Some (mv.(Psurj_invmap) !! v))
        then None else Some v~0~1) (vertices cohg)))
    (vmap xO (subouts +++ subins) +++ vmap (xI ∘ xO) (inputs cohg)) (* TODO: What should we do on the boundary here??? *)
    (vmap (xI ∘ xO) (outputs cohg)).



(* The nontrivial fibers of g : frob_enlarge_graph cohg -> cohg
  all (TODO: Check) arise from the boundary K; specifically,
  a valid match should satisfy that the only vertices in the image
  of mv are vertices in K *)
(*
Definition frob_fiber {T n m}
  {i j} (subins : vec positive i) (subouts : vec positive j)
  (enlarged_cohg : CospanHyperGraph T (j + i + n) m)
  (k : positive) : Pset :=
  set_omap (λ v,
    match v with
    | v'~1 => if decide (v' = v)) (vertices enlarged_cohg).

    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *) :
      list Pset :=

Definition frob_fibers {T n m}
  (cohg : CospanHyperGraph T n m)
    (* G, or the graph we want to rewrite into *)
  {i j} (subins : vec positive i) (subouts : vec positive j)
    (* K, the interface of the subgraph matching *)
  (mv : Psurj) (me : Psurj) :
    (* The vertex and edge components of the match, recorded here
      with explicit preimage functions for ease of computation *) :
      list Pset :=

*)


