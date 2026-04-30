From TensorRocq Require Import BW.
From Ltac2 Require Import Ltac2.
From TensorRocq Require Import Ltac2.ConstrExtra.

(* A set of Ltac2 functions for automatically quoting nat terms 
  into binary trees of [option nat]s which index into a list of constants *)

(* A customizable tactic for comparing equality of terms for the purpose of
  quoting them into syntactic formats *)
Ltac2 mutable quote_constr_eq : constr -> constr -> bool :=
  fun c d => unify_eq c d.


(* Given a list and an element, give a new list and an index such that the 
  element is at that index, up to equality by [aeq] *)
Ltac2 get_nth (aeq : 'a -> 'a -> bool) (l : 'a list) (a : 'a) : 'a list * int :=
  let rec go i l' :=
    match l' with
    | [] => (List.append l [a], i)
    | a' :: l' =>
      if aeq a a' then (l, i)
      else go (Int.add i 1) l'
    end
  in go 0 l.

Ltac2 test_get_nth (aeq : 'a -> 'a -> bool) (l : 'a list) (a : 'a) : bool :=
  let (l', i) := get_nth aeq l a in 
  aeq a (List.nth l' i).

(* Ltac2 Eval test_get_nth Int.equal [0;2;3] 2.
Ltac2 Eval test_get_nth Int.equal [0;2;3] 4. *)

(* Given a list of constrs and an element, give a new list of constrs and 
  an index such that the element is at that index, up to [quote_constr_eq] *)
Ltac2 constr_get_nth (l : constr list) (c : constr) : constr list * int :=
  get_nth quote_constr_eq l c.






Require Import Ltac2.Ltac2.

Ltac2 Type rec ('a) btree := [
  | Bnode ('a btree, 'a btree)
  | Bleaf ('a)
  | Bempty
].

(* Ltac2 Type rec ('b, 'a) lbtree := [
  | LBnode ('b, ('b, 'a) lbtree, ('b, 'a) lbtree)
  | LBleaf ('a)
  | LBempty
]. *)

Ltac2 rec btree_fold (of_empty : 'b) (of_leaf : 'a -> 'b) (node : 'b -> 'b -> 'b)
  (b : 'a btree) : 'b :=
  let rec go b :=
    match b with
    | Bempty => of_empty
    | Bleaf a => of_leaf a
    | Bnode l r => node (go l) (go r)
    end
  in go b.


Ltac2 btree_map (f : 'a -> 'b) (b : 'a btree) : 'b btree :=
  btree_fold Bempty (fun a => Bleaf (f a)) (fun l r => Bnode l r) b.
  

Ltac2 rec btree_eq (eqa : 'a -> 'a -> bool) (b : 'a btree) c : bool :=
  match b with
  | Bnode l r =>
    match c with
    | Bnode l' r' => if btree_eq eqa l l' then btree_eq eqa r r' else false
    | _ => false
    end
  | Bleaf a =>
    match c with
    | Bleaf a' => eqa a a'
    | _ => false
    end
  | Bempty =>
    match c with
    | Bempty => true
    | _ => false
    end
  end.

Ltac2 rec is_empty (b : 'a btree) : bool :=
  match b with
  | Bnode l r => if is_empty l then is_empty r else false
  | Bleaf _ => false
  | Bempty => true
  end.

(* 'join' two btrees by requiring that they be equal EXCEPT that
  [Bnode Bempty ?t == ?t] (ONLY on the left of a Bnode). This captures
  definitional equality of their nat semantics. *)
Ltac2 rec btree_join (eqa : 'a -> 'a -> bool)
  (b : 'a btree) (c : 'a btree) : 'a btree option := 
  let rec go b c :=
    if btree_eq eqa b c then Some b else
    match b with
    | Bnode l r => 
      if is_empty l then 
        Option.map (fun b' => Bnode l b') (go r c)
      else
        match c with
        | Bnode l' r' => 
          if is_empty l' then 
            Option.map (fun b' => Bnode l' b') (go b r')
          else
            Option.bind (go l l') (fun newl =>
              Option.map (fun newr => Bnode newl newr) (go r r'))
        | _ => None
        end
    | Bleaf a => 
      match c with
      | Bnode l' r' => 
        if is_empty l' then 
          Option.map (fun b' => Bnode l' b') (go (Bleaf a) r')
        else
          None
      | Bleaf a' => if eqa a a' then Some (Bleaf a) else None
      | _ => None
      end
    | Bempty => if is_empty c then Some c else None
    end in 
  go b c.


Module CC.

Export ConstrExtra.CC.


Ltac2 mk_btree_typed (ty : constr) (b : constr btree) : constr :=
  let rec go b :=
    match b with
    | Bnode l r => let cl := go l with cr := go r in 
      '(bnode $cl $cr)
    | Bleaf c => '(@bleaf $ty $c)
    | Bempty => '(@bempty $ty)
    end
  in go b.


Ltac2 mk_btree (b : constr btree) : constr :=
  let rec go b :=
    match b with
    | Bnode l r => let cl := go l with cr := go r in 
      '(bnode $cl $cr)
    | Bleaf c => '(bleaf $c)
    | Bempty => '(bempty)
    end
  in go b.


Ltac2 to_btree_typed (ty : constr) (cA : 'a -> constr) (b : 'a btree) : constr :=
  mk_btree_typed ty (btree_map cA b).

Ltac2 to_btree (cA : 'a -> constr) (b : 'a btree) : constr :=
  mk_btree (btree_map cA b).

Ltac2 of_btree (pA : constr -> 'a) (b : constr) : 'a btree :=
  let rec go p :=
  match! p with 
  | bempty => Bempty
  | bleaf ?a => Bleaf (pA a)
  | bnode ?l ?r => Bnode (go l) (go r)
  | _ =>
    let p' := Std.eval_red p in 
    if Constr.equal p' p then 
      let p' := Std.eval_hnf p in 
      if Constr.equal p' p then 
        Control.throw_invalid_argument 
          "of_option: argument is not reducible to an [option] constant"
      else go p'
    else go p'
  end in 
  go b.


Ltac2 of_btree_with_state (st : 'state) 
  (pA : 'state -> constr -> 'state * 'a) (b : constr) : 'state * 'a btree :=
  let rec go st p :=
  match! p with 
  | bempty => (st, Bempty)
  | bleaf ?a => let (st', a') := pA st a in (st', Bleaf a')
  | bnode ?l ?r => 
    let (st, l') := go st l in 
    let (st, r') := go st r in 
    (st, Bnode l' r')
  | _ =>
    let p' := Std.eval_red p in 
    if Constr.equal p' p then 
      let p' := Std.eval_hnf p in 
      if Constr.equal p' p then 
        Control.throw_invalid_argument 
          "of_option: argument is not reducible to an [option] constant"
      else go st p'
    else go st p'
  end in 
  go st b.

End CC.


Ltac2 denote_nat_btree (ns : constr list) (c : int option btree) : constr :=
  btree_fold 'O (Option.map_default (fun i => List.nth ns i) '(S O))
    (fun l r => '(Nat.add $l $r)) c.

Ltac2 rec parse_nat_btree (ns : constr list) (c : constr) : constr list * int option btree :=
  let maygo c :=
    lazy_match! c with
    | O => Some (ns, Bempty)
    | S O => Some (ns, Bleaf None)
    | S ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      Some (ns, Bnode (Bleaf None) nt)
    | ?n + ?m => 
      let (ns, nt) := parse_nat_btree ns n in 
      let (ns, mt) := parse_nat_btree ns m in 
      Some (ns, Bnode nt mt)
    | _ => None
    end in 
  match maygo c with
  | Some out => out
  | None => 
    match maygo (Std.eval_hnf c) with
    | Some out => out
    | None => 
      let (ns, i) := constr_get_nth ns c in 
      (ns, Bleaf (Some i))
    end
  end.

Ltac2 test_parse_nat_btree_assert ns c :=
  let (ns, b) := parse_nat_btree ns c in 
  let c' := denote_nat_btree ns b in 
  let cns := CC.to_list (fun a => a) ns in 
  Std.assert (Std.AssertType None '($cns = $cns -> $c = $c') None).


Ltac2 test_denote_nat_bw_parse_nat_btree_assert ns c :=
  let (ns, b) := parse_nat_btree ns c in 
  let c' := denote_nat_btree ns b in 
  let cns := CC.to_list (fun a => a) ns in 
  let b' := CC.to_btree (CC.to_option CC.to_nat) b in 
  Std.assert (Std.AssertType None '($cns = $cns -> $c = $c' ->
    $c = denote_nat_bw $cns $b') None).

(* Goal forall n m o : nat, True.
intros.

test_denote_nat_bw_parse_nat_btree_assert [] '(n + S m + 1).
reflexivity.


test_parse_nat_btree_assert [] '(n + S m + 1).
reflexivity.
test_parse_nat_btree_assert [] '(n + S m + 1 + (fun n m => n + m) n m).

reflexivity.
denote_nat_bw *)



