Require Import TensorCore.Summable.
Require Import Bool.
Require Import Btauto.
Require Import TensorCore.Tensor.
Require Import QuantumLib.Complex.
Set Warnings "-stdlib-vector".
Require Import Vector.
Import VectorNotations.
Require Import ZXCore LtacTensorExprDBParseTemp.
Require Import Ltac2.Notations Ltac2.Init.
Require Ltac2.Constr.

(* FIXME: Move, or maybe it exists already? *)
Inductive btree {A : Type} : Type :=
  | bnode : btree -> btree -> btree
  | bleaf : A -> btree.
#[global] Arguments btree (A) : clear implicits.

Fixpoint btree_fold {A B} (ofa : A -> B)
  (op : B -> B -> B) (t : btree A) : B :=
  match t with 
  | bnode l r => op (btree_fold ofa op l) (btree_fold ofa op r)
  | bleaf a => ofa a
  end.

Fixpoint btree_elems {A} (t : btree A) : list A :=
  match t with 
  | bnode l r => btree_elems l ++ btree_elems r
  | bleaf a => [a]
  end.

Coercion btree_elems : btree >-> list.

Fixpoint ntree_sum (t : btree nat) : nat :=
  match t with 
  | bnode l r => ntree_sum l + ntree_sum r
  | bleaf n => match n with | O => 1 | S n' => n' end
  end.

Definition borvec (n : nat) : Type :=
  match n with 
  | 0 => bool
  | S n' => bvec n'
  end.

(* TODO: Replace [list nat] with [btree nat] so we don't _need_ right-association *)
Notation bv_args := (TensorExprDBSemantics.V_n_args borvec).

Fixpoint bv_args_app {args args' A} : (bv_args args (bv_args args' A)) ->
  bv_args (args ++ args') A :=
  match args with 
  | List.nil => fun f => f
  | List.cons n args => fun f v => bv_args_app (f v)
  end.

Definition borvec_to_vec (n : nat) : borvec n ->  
  bvec (match n with | O => 1 | S n' => n' end) :=
  match n with 
  | O => fun b => [b]
  | S n' => fun v => v
  end.

Fixpoint zsp_gen_aux {A} (args : btree nat) : 
  (bvec (ntree_sum args) -> A) ->
  bv_args (btree_elems args) A :=
  match args with 
  | bnode l r => fun f => 
    bv_args_app (zsp_gen_aux l (fun vl => zsp_gen_aux r (fun vr => f (vl ++ vr))))
  | bleaf n => fun f v => f (borvec_to_vec n v)
  end.

Definition zsp_gen (phase : R) (ins outs : btree nat) : 
  bv_args ins (bv_args outs C) := 
  zsp_gen_aux ins (fun inv => zsp_gen_aux outs (fun outv => zsp phase inv outv)).

Ltac2 Type rec 'a btree := [
    BNode ('a btree, 'a btree)
  | BLeaf ('a) 
].

Ltac2 bnode (l : 'a btree) (r : 'a btree) : 'a btree := BNode l r.
Ltac2 bleaf (a : 'a) : 'a btree := BLeaf a.

Ltac2 rec btree_fold (ofa : 'a -> 'b) (op : 'b -> 'b -> 'b) (b : 'a btree) : 'b :=
  match b with 
  | BNode l r => op (btree_fold ofa op l) (btree_fold ofa op r)
  | BLeaf a => ofa a
  end.

Ltac2 constr_of_btree (ofa : 'a -> constr) (b : 'a btree) : constr :=
  btree_fold (fun a => let ca := ofa a in '(bleaf $ca)) 
    (fun l r => '(bnode $l $r)) b.

Ltac2 btree_of_constr (toa : constr -> 'a) (c : constr) : 'a btree :=
  let rec go c := 
  match! c with 
  | bleaf ?a => BLeaf (toa a)
  | bnode ?l ?r => BNode (go l) (go r)
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_vm None c in 
      if Constr.equal c' c then 
      Control.throw_invalid_argument 
        "btree_of_constr: argument is not reducible to a [btree] constant"
      else go c'
    else go c'
  end in 
  go c.

Ltac2 btree_map (f : 'a -> 'b) (b : 'a btree) : 'b btree :=
  btree_fold (fun a => BLeaf (f a)) bnode b.

Ltac2 rec btree_elems (b : 'a btree) : 'a list :=
  match b with 
  | BNode l r => List.append (btree_elems l) (btree_elems r)
  | BLeaf a => [a]
  end.

Ltac2 vec_expr_to_btree (tA : constr) (size : constr) (v : constr) : 
  (constr * constr) btree :=
  let rec go size v :=
  match! v with 
  | @Vector.nil ?_tA => BLeaf ('(@Vector.nil $tA), '(S O))
  | @Vector.cons ?_tA ?a ?n ?v => 
    BNode (BLeaf (a, '(O)))
    (go n v)
  | @Vector.append _ ?nl ?nr ?l ?r => 
    BNode (go nl l) (go nr r)
  | _ => BLeaf (v, '(S $size))
  end in 
  go size v.

Require Import PrintingExtra.
Import Pp Printf.

Ltac2 parse_zsp (c : constr) : 
  (constr * (constr * constr) list * (constr * constr) list) option :=
  match! c with 
  | @zsp ?n ?m ?phase ?vl ?vr => 
    (* printf "zsp called"; *)
    let ltree := vec_expr_to_btree 'bool n vl in 
    let rtree := vec_expr_to_btree 'bool m vr in 
    (* printf "trees parsed"; *)
    (* Message.print (btree_fold (of_pair of_constr of_constr)
      (fun l r => str "(" ++ l ++ str ")" ++ spc() ++ str "(" ++ r ++ str ")") ltree);
    Message.print (btree_fold (of_pair of_constr of_constr)
      (fun l r => str "(" ++ l ++ str ")" ++ spc() ++ str "(" ++ r ++ str ")") rtree); *)
    let to_list := btree_fold (fun (v, size) => [(v, Std.eval_red '(borvec $size))]) List.append in 
    let largs := constr_of_btree snd ltree in 
    let rargs := constr_of_btree snd rtree in 
    (* printf "constrs made"; *)
    Some ('(zsp_gen $phase $largs $rargs), to_list ltree, to_list rtree)
  | _ => None
  end.

Ltac2 Set parse_abstract as parse_abstract_old := fun c ty => 
  match! c with 
  | @zsp _ _ _ _ _ => 
    match parse_zsp c with 
    | Some out => Some out
    | None => parse_abstract_old c ty
    end
  | _ => parse_abstract_old c ty
  end.

Ltac2 Set red_te_semantics_post as red_old := fun () =>
  cbv [zsp_gen zsp_gen_aux borvec bv_args_app borvec_to_vec btree_elems
    app];
  red_old ().

Set Default Proof Mode "Classic".

(* 
  NOTE: At present, this tactic works by shelving the key statements (i.e.
  that the rewrites are correct). These are usually [admit]ted; in future
  they will be automatically solved.
  
  The tactic [te_rewrite] performs a single rewrite in the goal, up to 
  (only) tensor expression equivalence (so, no commuting of arguments
  to spiders). Also, it cannot instantiate holes that have types other
  than [bool] and [Vector.t bool _], so these must be given explicitly
  (such as phase and size). Furthermore, it cannot 'split' one quantified
  argument into the appending of several arguments, so the lemma passed in
  has to match the 'shape' of the arguments in the goal exactly. We have 
  notations below to handle the most common instances of this more easily, 
  namely [!_] and [!++].

  As an example, suppose we are rewriting with the lemma
  [self_loop_l : forall p u v, ∑ bs : n, zsp p (bs ++ bs ++ u) v == zsp p u v]
  in the goal 
  [∑ bs : n, ∑ w0 : k, zsp p0 (bs ++ bs ++ w0 ++ w1) x == rhs]
  (where [rhs] is some other expression),
  we will have the variable [u] of [self_loop_l] taking the form [w0 ++ w1], 
  once we pass under binders (which is done automatically). So, to perform 
  the rewrite, we need to explicitly replace [self_loop_l]'s variable [u] with
  two appended variables, which is very straightforward: 
    [fun p ul ur v => self_loop p (ul ++ ur) v]. 
  We also have to specify the phase, we which can do directly as [self_loop_l p]. 
  The [v] can stay universally quantified. All in all, we have
    [fun ul ur v => self_loop p0 (ul ++ ur) v],
  or using our notations, [self_loop p0 !++ !_]. 
  (In practice, we would also need to specify the sizes of all arguments;
  this is omitted here for clarity). *)
Tactic Notation "te_rewrite" open_constr(h) :=
  let tac := ltac2:(h |- let cH := Option.get (Ltac2.Ltac1.to_constr h) in 
  te_rewrite 'C cH) in 
  tac h.


Notation "lem '!++'" := (
  ltac2:(let res := 
    ConstrExtra.Unsafe.map_lambda 
      (fun lem => '(fun l r => $lem (l ++ r))) (Constr.pretype lem) in 
    exact $res))
  (at level 10, left associativity, only parsing).


Notation "lem '!_'" := (
  ltac2:(let res := 
    ConstrExtra.Unsafe.map_lambda (fun lem => '(fun x => $lem x)) (Constr.pretype lem) in 
    exact $res))
  (at level 10, left associativity, only parsing).






Theorem spider_fusion {n m o p k: nat} (p1 p2: R) 
  (bs1 : bvec n) (bs2 : bvec m)
  (bs3 : bvec o) (bs4 : bvec p) :
    ∑ cs : bvec (k+1) , zsp p1 bs1 (cs ++ bs2) * zsp p2 (cs ++ bs3) bs4 =
    zsp (p1 + p2) (bs1 ++ bs3) (bs2 ++ bs4).
Proof.
  split_sums.
  replace_spiders (∑ bs0 : bvec k, ∑ b, zsp p1 bs1 (b :: bs0 ++ bs2) 
    * zsp p2 (b :: bs0 ++ bs3) bs4).
  (* setoid_rewrite (fun v l r l' r' => @spider_fusion1 n (k + m) (k + o) p p1 p2 
    v (l ++ r) (l' ++ r')). *)
  te_rewrite (@spider_fusion1 n (k + m) (k + o) p p1 p2
    !_ !++ !++).

  replace_spiders (∑ bs0 : bvec k, zsp (p1 + p2) (bs0 ++ bs1 ++ bs3) (bs0 ++ bs2 ++ bs4)).
  te_rewrite (@spider_loop (n + o) k (m + p) (p1+p2)
    !++ !++).
  reflexivity.
  Unshelve. all: admit.
Admitted.

