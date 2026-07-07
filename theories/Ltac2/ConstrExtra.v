Require Import Ltac2.Init.
From Ltac2 Require Export Constr.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Std.
From TensorRocq Require PrintingExtra.
Require Ltac2.Notations.




(* FIXME: Move *)
Ltac2 pair_equal (eqa : 'a -> 'a -> bool) (eqb : 'b -> 'b -> bool) :
  'a * 'b -> 'a * 'b -> bool :=
  fun (a, b) (a', b') => if eqa a a' then eqb b b' else false.
Ltac2 char_list_of_string (s : string) : char list :=
  List.map (String.get s) (List.seq 0 1 (String.length s)).
Ltac2 int_of_string (s : string) : int :=
  List.fold_right (fun c acc => Int.add (Int.sub (Char.to_int c) 48)
    (Int.mul 10 acc))
    (List.rev (char_list_of_string s)) 0.
Module IfAnd.
Import Ltac2.Notations.
Ltac2 Notation "!if" conds(list1(thunk(tactic(0)), "and")) "then"
  t(thunk(tactic(5))) "else" f(thunk(tactic(5))) : 5 :=
  let rec get_val vs :=
    match vs with
    | [] => false
    | [v] => v()
    | v :: vs =>
      if v() then true else get_val vs
    end in
  if get_val conds then t() else f().
End IfAnd.



Import Unsafe.

Local Ltac2 map_invert (f : constr -> constr) (iv : case_invert) : case_invert :=
  match iv with
  | NoInvert => NoInvert
  | CaseInvert indices => CaseInvert (Array.map f indices)
  end.

(** [map_with_binders_alt g f n c] maps [f n] on the immediate subterms of [c];
   it carries an extra data [n] (typically a lift index) which is processed by [g]
   (which typically add 1 to [n]) at each binder traversal;
   it is not recursive and the order with which subterms are processed is not specified. *)
Ltac2 map_with_binders_alt
  (lift : 'a -> binder -> binder * 'a)
  (f : 'a -> constr -> constr) (n : 'a) (c : constr) : constr :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => c
  | Cast c k t =>
      let c := f n c
      with t := f n t in
      make (Cast c k t)
  | Prod b c =>
      let (b, n) := lift n b in
      let c := f n c in
      make (Prod b c)
  | Lambda b c =>
      let (b, n) := lift n b in
      let c := f n c in
      make (Lambda b c)
  | LetIn b t c =>
      let t := f n t in
      let (b, n) := lift n b in
      let c := f n c in
      make (LetIn b t c)
  | App c l =>
      let c := f n c
      with l := Array.map (f n) l in
      make (App c l)
  | Evar e l =>
      let l := Array.map (f n) l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x,x') => (f n x, x') end
      with iv := map_invert (f n) iv
      with y := f n y
      with bl := Array.map (f n) bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f n c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let (n,tl_l) := Ltac2.List.fold_right (fun b (n, l) =>
        let (b', n') := lift n b in
        (n', List.cons b' l)) (Array.to_list tl) (n, []) in
      let tl := Array.of_list tl_l in
      (* let n_bl := Array.fold_left lift n tl in *)
      (* let bl := Array.map (f n_bl) bl in *)
      make (Fix structs which tl (Array.map (f n) bl))
  | CoFix which tl bl =>
      let (n,tl_l) := Ltac2.List.fold_right (fun b (n, l) =>
        let (b', n') := lift n b in
        (n', List.cons b' l)) (Array.to_list tl) (n, []) in
      let tl := Array.of_list tl_l in
      make (CoFix which tl (Array.map (f n) bl))
  | Array u t def ty =>
      let ty := f n ty
      with t := Array.map (f n) t
      with def := f n def in
      make (Array u t def ty)
  end.

(* Given a term, change the names of binders in that term to be fresh *)
Ltac2 rec make_binders_distinct_aux (used : Fresh.Free.t) (c : constr) : constr :=
  map_with_binders_alt (fun used b =>
    match Binder.name b with
    | None => (b, used)
    | Some name =>
      let newname := Fresh.fresh used name in
      let newused := Fresh.Free.union used (Fresh.Free.of_ids [newname]) in
      (Binder.unsafe_make (Some newname)
        (Binder.relevance b) (Binder.type b),
       newused)
    end) (fun used c =>
    make_binders_distinct_aux used c
    ) used c.


Ltac2 make_binders_distinct (c : constr) : constr :=
  make_binders_distinct_aux
    (Fresh.Free.of_ids []) c.

(* Given a term, change the names of binders in that term to be anonymous *)
Ltac2 rec make_binders_anon (c : constr) : constr :=
  map_with_binders_alt (fun () b =>
      (Binder.unsafe_make None (Binder.relevance b) (Binder.type b), ())
    ) (fun () c =>
    make_binders_anon c
    ) () c.

Ltac2 mk_evar (type : constr) : constr :=
  (* TODO: investigate using Constr.pretype to avoid TC search *)
  open_constr:(_ :> $type).

Ltac2 unify_eq (c : constr) (d : constr) : bool :=
  if Constr.equal c d then true else
  if Int.equal (Control.numgoals()) 1 then
    match Control.case (fun () => Std.unify c d) with
    | Val _ => true
    | Err _ => false
    end
  else false.







Module Unsafe.

Export Constr.Unsafe.

Import PrintingExtra.Pp.


Ltac2 rec decompose_lambda (f : constr) : binder * constr :=
  match kind f with
  | Lambda b c => (b, c)
  | Cast c _ _ => decompose_lambda c
  | _ =>
    match kind (Std.eval_red f) with
    | Lambda b c => (b, c)
    | _ => Control.throw (Invalid_argument (Some (str "decompose_lambda:" ++
      spc() ++ str "constr" ++ spc() ++ Message.of_constr f ++ spc() ++
      str "cannot be reduced to a bare lambda (by red)")))
    end
  end.

Ltac2 rec decompose_prod (f : constr) : binder * constr :=
  match kind f with
  | Prod b c => (b, c)
  | Cast c _ _ => decompose_prod c
  | _ =>
    match kind (Std.eval_red f) with
    | Lambda b c => (b, c)
    | _ => Control.throw (Invalid_argument (Some (str "decompose_prod:" ++
      spc() ++ str "constr" ++ spc() ++ Message.of_constr f ++ spc() ++
      str "cannot be reduced to a bare prod (by red)")))
    end
  end.

Ltac2 is_Rel_data (c : constr) : int option :=
  match kind c with
  | Rel i => Some i
  | _ => None
  end.

Ltac2 is_Var_data (c : constr) : ident option :=
  match kind c with
  | Var i => Some i
  | _ => None
  end.

Ltac2 mk_Rel (i : int) : constr :=
  make (Rel i).

(* Applies a funciton [f : constr -> constr] to [lem], where
  [c] is [fun x y .. => lem x y ..] (i.e., strips off any lambda
  binders and applies f to the inner function) *)
Ltac2 rec map_lambda (f : constr -> constr) (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Lambda b body =>
    let name := Option.default (Fresh.fresh (Fresh.Free.of_goal ()) ident:(x))
      (Binder.name b) in
    Constr.in_context name (Binder.type b) (fun () =>
    let c' := Constr.Unsafe.substnl [Control.hyp name] 0 body in
    let res := map_lambda f c' in
    Control.refine (fun _ => res))
  | _ => f c
  end.



(* Given a term with one bound variable (unsafe, with a _REL_ subterm),
  return the result of substituting that variable with the given term *)
Ltac2 subst_one_var (f : constr) (x : constr) : constr :=
  substnl [x] 0 f.

Ltac2 beta_apply (f : constr) (x : constr) : constr :=
  let (_, fbody) := decompose_lambda f in
  subst_one_var fbody x.


Ltac2 Notation "default" x(thunk(tactic(0))) mx(thunk(tactic(0))) :=
  match mx() with
  | Some v => v
  | None => x()
  end.


Ltac2 Notation "getor" mx(thunk(tactic(0))) x(thunk(tactic(0))) :=
  match mx() with
  | Some v => v
  | None => x()
  end.

Local Ltac2 binder_fold (go : 'st -> constr -> 'st * constr)
  (st : 'st) (b : binder) : 'st * binder :=
  let (st, t) := go st (Binder.type b) in
  (st, Binder.unsafe_make (Binder.name b) (Binder.relevance b) t).


Ltac2 array_fold_right_to_array (go : 'st -> 'a -> 'st * 'b)
  (st : 'st) (l : 'a array) : 'st * 'b array :=
    let (st, lst) := List.fold_right (fun arg (st, l) =>
      let (st, arg) := go st arg in
      (st, arg :: l)) (Array.to_list l) (st, []) in
  (st, Array.of_list lst).

Local Ltac2 invert_fold (go : 'st -> constr -> 'st * constr)
  (st : 'st) (iv : case_invert) : 'st * case_invert :=
  match iv with
  | NoInvert => (st, NoInvert)
  | CaseInvert indices =>
    let (st, indices) := array_fold_right_to_array go st indices in
    (st, CaseInvert indices)
  end.




Ltac2 rec_fold_with_binders (lift : 'a -> binder -> 'a)
  (f : 'a -> constr -> ('a * constr) option) (st : 'a) (c : constr) : 'a * constr :=
  let rec go st c :=
    getor (f st c) (
    match kind c with
    | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
    | Constructor _ _ | Uint63 _ | Float _ | String _ => (st, c)
    | Cast c k t =>
        let (st, t) := go st t in
        let (st, c) := go st c in
        (st, make (Cast c k t))
    | Prod b c =>
        let (st, b) := binder_fold go st b in
        let (st, c) := go (lift st b) c in
        (st, make (Prod b c))
    | Lambda b c =>
        let (st, b) := binder_fold go st b in
        let (st, c) := go (lift st b) c in
        (st, make (Lambda b c))
    | LetIn b t c =>
        let (st, b) := binder_fold go st b in
        let (st, t) := go st t in
        let (st, c) := go (lift st b) c in
        (st, make (LetIn b t c))
    | App c l =>
        let (st, l) := array_fold_right_to_array go st l in
        let (st, c) := go st c in
        (st, make (App c l))
    | Evar e l =>
        let (st, l) := array_fold_right_to_array go st l in
        (st, make (Evar e l))
    | Case info x iv y bl =>
        let (st, x) := match x with (x,x') =>
          let (st, x) := go st x in
          (st, (x, x')) end in
        let (st, iv) := invert_fold go st iv in
        let (st, y) := go st y in
        let (st, bl) := array_fold_right_to_array go st bl in
        (st, make (Case info x iv y bl))
    | Proj p r c =>
        let (st, c) := go st c in
        (st, make (Proj p r c))
    | Fix structs which tl bl =>
        let (st, tl) := array_fold_right_to_array (binder_fold go) st tl in
        let st_bl := Array.fold_left lift st tl in
        let (st, bl) := array_fold_right_to_array go st_bl bl in
        (st, make (Fix structs which tl bl))
    | CoFix which tl bl =>
        let (st, tl) := array_fold_right_to_array (binder_fold go) st tl in
        let st_bl := Array.fold_left lift st tl in
        let (st, bl) := array_fold_right_to_array go st_bl bl in
        (st, make (CoFix which tl bl))
    | Array u t def ty =>
        let (st, ty) := go st ty in
        let (st, t) := array_fold_right_to_array go st t in
        let (st, def) := go st def in
        (st, make (Array u t def ty))
    end) in
  go st c.


End Unsafe.


Require PArith.

(* 'Constr Conversions' *)
Module CC.

Import Ltac2.Notations PArith.


Import Message.

Ltac2 mk_of (fn_name : string) (type : string) (of : constr -> 'a) : constr -> 'a :=
  fun c =>
  Notations.orelse
    (fun _ => of c)
    (fun e =>
      let c' := Std.eval_hnf c in
      (* Message.print (Message.concat (Message.of_string "mk_of reduced: ")
        (Message.of_constr c')); *)
      if Constr.equal c c' then
        Control.zero e
      else
        Notations.orelse (fun _ => of c')
        (fun e' =>
          Control.throw_invalid_argument
          (String.concat "" [fn_name; ": argument is not parseable as a [";
            type; "] constant: "; to_string (of_constr c);
            " (reduced to "; to_string (of_constr c');
            "; parser failed first with error ";
            to_string (of_exn e);
            ", then with error ";
            to_string (of_exn e')]))
      ).

Ltac2 of_nat (n : constr) : int :=
  mk_of "of_nat" "nat" (fun n =>
  let rec go p :=
  lazy_match! p with
  | O => 0
  | S ?n => Int.add 1 (go n)
  (* | ?n + ?m => Int.add (go n) (go m) *)
  | _ => let p' := Std.eval_hnf p in
    if Constr.equal p p' then Control.throw_invalid_argument "not nat constant"
    else go p'
  end in
  go n) n.


Ltac2 rec to_nat (i : int) : constr :=
  if Int.le i 0 then
    'O
  else
    let n' := to_nat (Int.sub i 1) in
    '(S $n').

Ltac2 of_unit (_ : constr) : unit :=
  ().

Ltac2 to_unit () : constr := 'tt.

(* Ltac2 of_list (f : constr -> 'a) : constr -> 'a list :=
  let rec go l :=
  match! l with
  | nil => []
  | cons ?x ?l => f x :: go l
  | _ =>
    let l' := Std.eval_red l in
    if Constr.equal l' l then
      Control.throw_invalid_argument
        "of_list: argument is not reducible to a [nat] constant"
    else go l'
  end in
  go. *)


Ltac2 rec to_pos (i : int) : constr :=
  match Int.compare i 1 with
  | 1 => let res := to_pos (Int.asr i 1) in
    match Int.land i 1 with
    | 1 => '(xI $res)
    | _ => '(xO $res)
    end
  | 0 => 'xH
  | _ =>
    Control.throw_invalid_argument "to_pos: nonpositive argument"
  end.

Ltac2 of_pos (p : constr) : int :=
  let rec go p :=
  match! p with
  | xH => 1
  | xI ?p => Int.add 1 (Int.lsl (go p) 1)
  | xO ?p => Int.lsl (go p) 1
  | _ =>
    let p' := Std.eval_red p in
    if Constr.equal p' p then
      let p' := Std.eval_vm None p in
      if Constr.equal p' p then
        Control.throw_invalid_argument
          "of_pos: argument is not reducible to a [positive] constant"
      else go p'
    else go p'
  end in
  go p.

Ltac2 mk_pair_typed
  (ts : constr * constr) : constr * constr -> constr :=
  fun (a, b) =>
  let (tA, tB) := ts in
  '(@pair $tA $tB $a $b).

Ltac2 to_pair_typed (ts : constr * constr)
  (cA : 'a -> constr) (cB : 'b -> constr) : 'a * 'b -> constr :=
  fun (a, b) => mk_pair_typed ts (cA a, cB b).

Ltac2 of_pair (pA : constr -> 'a) (pB : constr -> 'b) (c : constr) : 'a * 'b :=
  let rec go p :=
  match! p with
  | (?a, ?b) => (pA a, pB b)
  | _ =>
    let p' := Std.eval_red p in
    if Constr.equal p' p then
      let p' := Std.eval_hnf p in
      if Constr.equal p' p then
        Control.throw_invalid_argument
          "of_pair: argument is not reducible to a [pair] constant"
      else go p'
    else go p'
  end in
  go c.

Ltac2 mk_list_typed (type : constr) (l : constr list) : constr :=
  let rec go l :=
  match l with
  | [] => '(@nil $type)
  | x :: l' =>
    let res := go l' in
    '(@cons $type $x $res)
  end in
  go l.

Ltac2 mk_list (l : constr list) : constr :=
  let rec go l :=
  match l with
  | [] => 'nil
  | x :: l' =>
    let res := go l' in
    '(cons $x $res)
  end in
  go l.

Ltac2 to_list (cA : 'a -> constr) (l : 'a list) : constr :=
  mk_list (List.map cA l).

Ltac2 of_list (pA : constr -> 'a) (c : constr) : 'a list :=
  let rec go p :=
  match! p with
  | nil => []
  | cons ?a ?l => pA a :: go l
  | app ?l ?r => List.append (go l) (go r)
  | _ =>
    let p' := Std.eval_red p in
    if Constr.equal p' p then
      let p' := Std.eval_hnf p in
      if Constr.equal p' p then
        Control.throw_invalid_argument
          "of_list: argument is not reducible to a [list] constant"
      else go p'
    else go p'
  end in
  go c.

Ltac2 mk_option_typed (ty : constr) (mc : constr option) : constr :=
  match mc with
  | Some c => '(@Some $ty $c)
  | None => '(@None $ty)
  end.

Ltac2 mk_option (mc : constr option) : constr :=
  match mc with
  | Some c => '(Some $c)
  | None => '(None)
  end.

Ltac2 to_option_typed (ty : constr) (cA : 'a -> constr) (ma : 'a option) : constr :=
  mk_option_typed ty (Option.map cA ma).

Ltac2 to_option (cA : 'a -> constr) (ma : 'a option) : constr :=
  mk_option (Option.map cA ma).

Ltac2 of_option (pA : constr -> 'a) (c : constr) : 'a option :=
  let rec go p :=
  match! p with
  | None => None
  | Some ?a => Some (pA a)
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
  go c.




End CC.


(* TODO: *)
(*

Ltac2 constr_of_constr_map (of_k : 'k -> constr) (of_v : 'v -> constr)
  (tk : constr) (tv : constr) (tm : constr) (m : ('k, 'v) FMap.t) : constr :=
  let mappings :=
    constr_of_constr_list_typed '(prod $tk $tv)
      (List.map (fun (k, v) =>
        let ck := of_k k with cv := of_v v in
        '(@pair $tk $tv $ck $cv)) (FMap.bindings m)) in
  let res := '(@list_to_map $tk $tv $tm _ _ $mappings) in
  Std.resolve_tc res;
  res.
*)
