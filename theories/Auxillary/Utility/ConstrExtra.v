Require Import Ltac2.Init.
From Ltac2 Require Export Constr.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Std.
Require PrintingExtra.


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

End Unsafe.