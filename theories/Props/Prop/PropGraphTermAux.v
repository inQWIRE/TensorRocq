Require Export Setoid. 
From stdpp Require Export base list.
From TensorRocq Require Import Aux_relset Aux_pos.

From TensorRocq Require Import HyperGraph.




Fixpoint inversions (p : list nat) : nat :=
  match p with
  | [] => 0
  | x :: p => sum_list_with (fun n => if n <? x then 1 else 0) p + inversions p
  end.

(* Time Compute inversions (reverse (seq 0 8)) =? 8 * (8 - 1) / 2. *)


Fixpoint inversionsP (p : list positive) : N :=
  match p with
  | [] => 0
  | x :: p =>
    foldr (fun n acc => if Pos.ltb n x then N.succ acc else acc) N0
      p + inversionsP p
  end%N.

(* Time Compute (inversions (reverse (seq 0 800)) =? 800 * (800 - 1) / 2)%nat.
Time Compute (inversionsP (reverse (Pos.of_succ_nat <$> seq 0 800)) =? 800 * (800 - 1) / 2)%N. *)


Fixpoint inversionsP_between (p q : list positive) : N :=
  match p with
  | [] => 0
  | x :: p =>
    foldr (fun n acc => if Pos.ltb n x then N.succ acc else acc) N0
      q + inversionsP_between p q
  end%N.
(*
Compute inversionsP (pseq 1 10 ++ reverse (pseq 11 10)).
Compute inversionsP_between (pseq 1 10) (reverse (pseq 1 10)).
Compute inversionsP (reverse (pseq 1 10)).
Compute inversionsP_between (pseq 1 10) (pseq 1 10). *)



Fixpoint argmin_list_with_aux {A} (f : A -> nat) (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | a :: l =>
    let n := f a in
    if decide (n = 0) then
    Some (0, a)
    else
    union_with (fun '(n, a) '(m, b) =>
    Some (if n <=? m then (n, a) else (m, b))) (Some (n, a))
    (argmin_list_with_aux f l)
  end.

Definition argmin_list_with {A} (f : A -> nat) (l : list A) : option A :=
  snd <$> (argmin_list_with_aux f l).


Fixpoint argmin_list_with_auxN {A} (f : A -> N) (l : list A) : option (N * A) :=
  match l with
  | [] => None
  | a :: l =>
    let n := f a in
    if decide (n = N0) then
    Some (N0, a)
    else
    union_with (fun '(n, a) '(m, b) =>
    Some (if (n <=? m)%N then (n, a) else (m, b))) (Some (n, a))
    (argmin_list_with_auxN f l)
  end.

Definition argmin_list_withN {A} (f : A -> N) (l : list A) : option A :=
  snd <$> (argmin_list_with_auxN f l).


Definition Pmap_splitb_aux {A}
  (go : Pmap_ne A -> Pmap A * Pmap A)
  (p : Pmap A) : Pmap A * Pmap A :=
  match p with
  | PNodes p => go p
  | PEmpty => (PEmpty, PEmpty)
  end.

Definition Pmap_ne_splitb {A} (f : A -> bool) : Pmap_ne A -> Pmap A * Pmap A :=
  fix go p {struct p} :=
  pmap.Pmap_ne_case p $ λ pl ma pr,
    let '(plt, plf) := Pmap_splitb_aux go pl in
    let '(prt, prf) := Pmap_splitb_aux go pr in
    let '(mat, maf) := match ma with | None => (None, None)
      | Some a => if f a then (Some a, None) else (None, Some a)
      end in
    (pmap.PNode plt mat prt, pmap.PNode plf maf prf).

Definition Pmap_splitb {A} (f : A -> bool) (p : Pmap A) : Pmap A * Pmap A :=
  Pmap_splitb_aux (Pmap_ne_splitb f) p.


Fixpoint argmins_list_with_auxN {A} (f : A -> N)
  (l : list A) : option (N * list A) :=
  match l with
  | [] => None
  | a :: l =>
    let na := f a in
    match argmins_list_with_auxN f l with
    | None => Some (na, [a])
    | Some (n, l') =>
      match N.compare na n with
      | Lt => Some (na, [a])
      | Gt => Some (n, l')
      | Eq => Some (n, a :: l')
      end
    end
  end.

Definition argmins_list_withN {A} (f : A -> N)
  (l : list A) : list A :=
  from_option snd [] (argmins_list_with_auxN f l).




Definition Pmap_argminsN_aux {A}
  (go : Pmap_ne A -> option (N * Pmap A) * Pmap A)
  (p : Pmap A) : option (N * Pmap A) * Pmap A :=
  match p with
  | PNodes p => go p
  | PEmpty => (None, PEmpty)
  end.

Definition Pmap_ne_argminsN {A} (f : A -> N) : Pmap_ne A ->
  option (N * Pmap A) * Pmap A :=
  fix go p {struct p} :=
  pmap.Pmap_ne_case (B:=option (N * Pmap A) * Pmap A) p $ λ pl ma pr,
    let '(mpl, pl') := Pmap_argminsN_aux go pl :> option (N * Pmap A) * Pmap A in
    let '(mpr, pr') := Pmap_argminsN_aux go pr :> option (N * Pmap A) * Pmap A in
    let ma' : option (N * A) := (λ a, (f a, a)) <$> ma in
    let min_N : option N := union_with (M:= option N) (λ a b, Some (N.min a b)) (fst <$> mpl)
      (union_with (M:= option N) (λ a b, Some (N.min a b)) (fst <$> ma') (fst <$> mpr)) in
    let (min_pl, rest_pl) := match mpl with
      | None => (PEmpty, pl')
      | Some (n, pln) =>
        if decide (min_N = Some n) then
          (pln, pl') else (PEmpty, pln ∪ pl')
      end in
    let (min_pr, rest_pr) := match mpr with
      | None => (PEmpty, pr')
      | Some (n, prn) =>
        if decide (min_N = Some n) then
          (prn, pr') else (PEmpty, prn ∪ pr')
      end in
    let (min_ma, rest_ma) := match ma' return option A * option A with
      | None => (None, None)
      | Some (n, a) => if decide (min_N = Some n) then
        (Some a, None) else (None, Some a)
      end in
    ((., pmap.PNode min_pl min_ma min_pr) <$> min_N,
      pmap.PNode rest_pl rest_ma rest_pr).

Definition Pmap_argminsN {A} (f : A -> N) (p : Pmap A) : Pmap A * Pmap A :=
  prod_map (from_option snd PEmpty) id $ Pmap_argminsN_aux (Pmap_ne_argminsN f) p.


Fixpoint vec_index `{EqDecision A} (a : A) {n} (v : vec A n) : option (fin n) :=
  match v with
  | [#] => None
  | a' ::: v =>
    if decide (a = a') then Some 0%fin else
      FS <$> vec_index a v
  end.






Definition get_extractable_edges {T} (inputs : Pset)
  (edges : Pmap (HyperEdge T)) :=
  Pmap_splitb (λ tio, forallb (λ k, bool_decide (k ∈ inputs)) tio.1.2) edges.



Definition optimize_edges {T} (inputs : list positive)
  (es : list (HyperEdge T)) : list (HyperEdge T) :=
  let idxmap : Pmap positive :=
    list_to_map (imap (λ i p, (p, Pos.of_succ_nat i)) inputs) in
  let es' := (λ e : HyperEdge T, (omap (idxmap !!.) e.1.2, e)) <$> es in
  (merge_sort (fun e e' =>
    Is_true ((fun e e' => match N.compare (inversionsP_between e e')
    (inversionsP_between e' e) with
    | Lt => true
    | Gt => false
    | Eq => Nat.leb (length e) (length e')
    end) e.1 e'.1)) es').*2.

  (* let idxmap : Pmap positive :=
    list_to_map (imap (λ i p, (p, Pos.of_succ_nat i)) inputs) in
  let es' : list ((list positive) * (T * list positive * list positive)) :=
    (λ e : HyperEdge T, ((idxmap !!!.) <$> e.1.2, e)) <$> es in
  default es ((λ l, l.*2) <$> argmin_list_withN (fun esp' =>
    inversionsP (flat_map fst esp'))
    (permutations es')). *)


Notation IdxOrHyperEdge T := (sum positive (HyperEdge T)).


Definition IOH_ins {T} (i_e : IdxOrHyperEdge T) : list positive :=
  match i_e with
  | inl i => [i]
  | inr e => e.1.2
  end.

Definition IOH_outs {T} (i_e : IdxOrHyperEdge T) : list positive :=
  match i_e with
  | inl i => [i]
  | inr e => e.2
  end.

Notation IOH_insize := (length ∘ IOH_ins).
Notation IOH_outsize := (length ∘ IOH_outs).


Definition IOH_aprop_ins (inputs : list positive)
  {T} (ioh : IdxOrHyperEdge T) :=
  match ioh with
  | inl i => [i]
  | inr tio => filter (.∈ inputs) tio.1.2
  end.

Definition IOH_aprop_outs (inputs : list positive)
  {T} (ioh : IdxOrHyperEdge T) :=
  match ioh with
  | inl i => [i]
  | inr tio => tio.2 ++ filter (.∉ inputs) tio.1.2
  end.

Definition IOH_aprop_ins' {A} (inputs : Pmap A)
  {T} (ioh : IdxOrHyperEdge T) :=
  match ioh with
  | inl i => [i]
  | inr tio => filter (λ i, is_Some (inputs !! i)) tio.1.2
  end.

Definition IOH_aprop_outs' {A} (inputs : Pmap A)
  {T} (ioh : IdxOrHyperEdge T) :=
  match ioh with
  | inl i => [i]
  | inr tio => tio.2 ++ filter (λ i, ~ is_Some (inputs !! i)) tio.1.2
  end.


Definition new_optimize_edges {T} (inputs : list positive)
  (es : list (IdxOrHyperEdge T)) : list (IdxOrHyperEdge T) :=
  let idxmap : Pmap positive :=
    list_to_map (imap (λ i p, (p, Pos.of_succ_nat i)) inputs) in
  let es' := (λ e : IdxOrHyperEdge T,
    (omap (idxmap !!.) $ IOH_ins e, e)) <$> es in
  (merge_sort (fun e e' =>
    Is_true ((fun e e' => match N.compare (inversionsP_between e e')
    (inversionsP_between e' e) with
    | Lt => true
    | Gt => false
    | Eq => Nat.leb (length e) (length e')
    end) e.1 e'.1)) es').*2.




Definition graph_to_APROP_badness_idxs (inputs : Pmap positive)
  (e_ins : list positive) : N :=
  lengthN (filter (λ i, inputs !! i = None) e_ins).



(* Compute prod_map map_to_list map_to_list $
  Pmap_argminsN id {[1%positive := 1%N; 2%positive := 1%N; 3%positive := 2%N]}. *)

Definition get_most_extractable_edges {T} (input_idxs : Pmap positive)
  (hg : Pmap (HyperEdge T)) :=
  Pmap_argminsN (λ '(t, i, o), graph_to_APROP_badness_idxs input_idxs i) hg.




Definition withPCounts (l : list positive) : list (positive * nat) :=
  reverse (foldl (fun '(ls, counts) p =>
    let cp := default 0 (counts !! p) in
    ((p, cp) :: ls, <[p := S cp]> counts)) ([], ∅ :> Pmap nat) l).1.


Definition sw_between (l l' : list positive) : list nat :=
  let idxmap : Pmap nat :=
    list_to_map (imap (λ i p, (p, i)) (encode <$> withPCounts l)) in
  (λ p, default 0 (idxmap !! (encode p))) <$> (withPCounts l').

(* Eval vm_compute in Psw (sw_between [1;3;1] [3;1;1])%positive : PROP bool _ _. *)

Fixpoint move_to_front `{EqDecision A} (a : A) (l : list A) : nat * list A :=
  match l with
  | [] => (1, [])
  | b :: l =>
    let '(n, l') := move_to_front a l in
    if decide (a = b) then (S n, l') else (n, b :: l')
  end.

Fixpoint moved_to_front_aux `{EqDecision A} (fuel : nat) (l : list A) : list A :=
  match fuel with
  | 0 => l
  | S fuel =>
    match l with
    | [] => []
    | a :: l' =>
      let (na, lrest) := move_to_front a l' in
      replicate na a ++ moved_to_front_aux fuel lrest
    end
  end.

Definition moved_to_front `{EqDecision A} (l : list A) : list A :=
  moved_to_front_aux (S (length l)) l.

Fixpoint plist_to_unique_counts_aux (fuel : nat) (l : list positive) :
  list (positive * positive) :=
  match l with
  | [] => []
  | p :: l =>
    match fuel with
    | 0 => []
    | S fuel =>
      let '(count, lrest) :=
        foldr (λ p' '(acc, lrest),
          if decide (p = p') then (Pos.succ acc, lrest) else (acc, p' :: lrest))
          (xH, []) l in
      (p, count) :: plist_to_unique_counts_aux fuel lrest
    end
  end.

Definition plist_to_unique_counts l :=
  plist_to_unique_counts_aux (S (length l)) l.