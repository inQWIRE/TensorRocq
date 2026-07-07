Require Import Ltac2.Init.
From TensorRocq Require Import ConstrExtra.

Import Unsafe.

Ltac2 option_matches (eq : 'a -> 'a -> bool) (pat : 'a option) (term : 'a option) :=
  match pat with
  | None => true
  | Some p => match term with
    | None => false
    | Some t => eq p t
    end
  end.

Ltac2 binder_matches_aux (name : ident option -> bool) (type : constr -> bool)
  (rel : Binder.relevance -> bool) (b : binder) : bool :=
  if name (Binder.name b) then
    if type (Binder.type b) then
      rel (Binder.relevance b)
    else false
  else false.

Ltac2 binder_matches (name : ident option) (type : constr option) (b : binder) : bool :=
  binder_matches_aux (option_matches Ident.equal name)
    (fun c => option_matches unify_eq type (Some c))
    (fun _ => true) b.


Ltac2 subst_letin (name : ident option) (type : constr option)
  (c : constr) : constr :=
  snd (rec_fold_with_binders (fun _ _ => ())
    (fun n c =>
      match kind c with
      | LetIn b val body =>
        if binder_matches name type b then
          Some (n, substnl [val] 0 body)
        else None
      | _ => None
      end) () c).

(* FIXME: move to printingExtra *)
(* Ltac2 of_binder (b : binder) : message :=
  let varname := str (Option.map_default Ident.to_string "_" (Binder.name b)) in
  str "(" ++ varname ++ brk 1 2 ++ str ": " ++ of_constr (Binder.type b) ++ str ")". *)

Ltac2 subst_one_letin (name : ident option) (type : constr option)
  (c : constr) : constr :=
  snd (rec_fold_with_binders (fun i _ => i)
    (fun done c =>
      if done then None else
        match kind c with
        | LetIn b val body =>
          (* printf "(at %i) LetIn (%s) (%s) (%s)" n (to_string (of_binder b)) (to_string (of_constr val)) (to_string (of_constr body)); *)
          if binder_matches name type b then
            Some (true, substnl [val] 0 body)
          else None
        | _ => None
        end) (false) c).

Ltac2 intro_letin (newname : ident option) (name : ident option) (valpat : constr option) (type : constr option) : unit :=
  let (done, newgoal) := rec_fold_with_binders (fun i _ => i)
    (fun done c =>
      if done then None else
        match kind c with
        | LetIn b val body =>
          if binder_matches name type b then
            if is_closed val then
              if option_matches unify_eq valpat (Some val) then
                let newname := Option.default (Option.default 
                  (Option.default @x (Binder.name b)) name) newname in

                Std.set false (fun _ => (Some newname, val)) {Std.on_hyps := Some []; Std.on_concl:=Std.NoOccurrences};
                Some (true, substnl [make (Var newname)] 0 body)
              else None
            else None
          else None
        | _ => None
        end) (false) (Control.goal()) in
  if done then
    Std.change None (fun _ => newgoal) {Std.on_hyps := Some []; Std.on_concl:=Std.AllOccurrences}
  else
    Control.zero (Invalid_argument (Some (Message.of_string "No let expression of the given name and type (without bound variables) found!"))).

Ltac2 intro_letin0 (namevaltype : ident option * constr option * constr option)
  (newname : ident option) : unit :=
  let (name, valpat, type) := namevaltype in 
  intro_letin newname name valpat type.

Ltac2 intro_letin1 (pat : (ident option * unit option * constr option * constr option) option)
  (name : ident option) : unit :=
  let (letname, valpat, type) := match pat with
    | None => (None, None, None)
    | Some (mname, _, mval, mtype) => 
      (mname, mval, mtype)
    end in
  intro_letin0 (letname, valpat, type) name.


Ltac2 open_pretype (p : preterm) : constr :=
  Pretype.pretype 
    Pretype.Flags.open_constr_flags_no_tc 
    Pretype.expected_without_type_constraint
    p.

Ltac2 open_pretype_as (type : constr option) (p : preterm) : constr :=
  Pretype.pretype 
    Pretype.Flags.open_constr_flags_no_tc 
    (Option.map_default Pretype.expected_oftype Pretype.expected_without_type_constraint type) 
    p.


Ltac2 intro_letin1' (pat : (ident option * unit option * preterm option * constr option) option)
  (name : ident option) : unit :=
  let (letname, valpat, type) := match pat with
    | None => (None, None, None)
    | Some (mname, _, mval, mtype) => 
      (mname, Option.map (open_pretype_as mtype) mval, mtype)
    end in
  intro_letin0 (letname, valpat, type) name.

(* TODO: Add 'in H' *)
(* TODO: Rewrite with pattern:() for the value *)
Ltac2 Notation "intro_let" pat(opt(seq(opt(ident), opt("_"), opt(seq(":=", preterm)), opt(seq(":", open_constr)))))
  name(opt(seq("as", ident))) :=
  intro_letin1' pat name.

Ltac2 intro_letin1'_ltac1 (pat : (Ltac1.t option * Ltac1.t option * Ltac1.t option) option)
  (name : Ltac1.t option) :=
  let (letname, valpat, type) := match pat with
    | None => (None, None, None)
    | Some (mname, mval, mtype) => 
      (Option.bind mname Ltac1.to_ident, 
        Option.bind mval Ltac1.to_preterm, Option.bind mtype Ltac1.to_constr)
    end in
  intro_letin1' (Some (letname, None, valpat, type)) (Option.bind name Ltac1.to_ident).
  

Tactic Notation "intro_let" ident(x) ":=" uconstr(val) ":" open_constr(type) "as" ident(name) :=
  let go := ltac2:(x val type name |- 
    intro_letin1'_ltac1 (Some (Some x, Some val, Some type)) (Some name)) in
  go x val type name.

Tactic Notation "intro_let" ident(x) ":=" uconstr(val) "as" ident(name) :=
  let go := ltac2:(x val name |- 
    intro_letin1'_ltac1 (Some (Some x, Some val, None)) (Some name)) in
  go x val name.

Tactic Notation "intro_let" "_" ":=" uconstr(val) "as" ident(name) :=
  let go := ltac2:(val name |- 
    intro_letin1'_ltac1 (Some (None, Some val, None)) (Some name)) in
  go val name.

Tactic Notation "intro_let" "as" ident(name) :=
  let go := ltac2:(name |- 
    intro_letin1'_ltac1 (Some (None, None, None)) (Some name)) in
  go name.

Tactic Notation "intro_let" ident(x) ":=" uconstr(val) ":" open_constr(type) :=
  let go := ltac2:(x val type |- 
    intro_letin1'_ltac1 (Some (Some x, Some val, Some type)) None) in
  go x val type.

Tactic Notation "intro_let" ident(x) ":=" uconstr(val) :=
  let go := ltac2:(x val |- 
    intro_letin1'_ltac1 (Some (Some x, Some val, None)) None) in
  go x val.

Tactic Notation "intro_let" "_" ":=" uconstr(val) :=
  let go := ltac2:(val |- 
    intro_letin1'_ltac1 (Some (None, Some val, None)) None) in
  go val.


Tactic Notation "intro_let" ident(x) ":" open_constr(type) "as" ident(name) :=
  let go := ltac2:(x type name |- 
    intro_letin1'_ltac1 (Some (Some x, None, Some type)) (Some name)) in
  go x type name.

Tactic Notation "intro_let" ident(x) ":" open_constr(type) :=
  let go := ltac2:(x type |- 
    intro_letin1'_ltac1 (Some (Some x, None, Some type)) None) in
  go x type.

Tactic Notation "intro_let" ident(x) :=
  let go := ltac2:(x |- 
    intro_letin1'_ltac1 (Some (Some x, None, None)) None) in
  go x.

Tactic Notation "intro_let" :=
  let go := ltac2:(intro_letin1'_ltac1 (Some (None, None, None)) (None)) in
  go.

Ltac2 intro_letin2 (pat : (ident option * unit option * preterm option * preterm option) option)
  (name : ident option) : unit :=
  let (letname, valpat, type) := match pat with
    | None => (None, None, None)
    | Some (mname, _, mval, mtype) => 
      let mtype' := Option.map open_pretype mtype in 
      (mname, Option.map (open_pretype_as mtype') mval, mtype')
    end in
  intro_letin0 (letname, valpat, type) name.

Ltac2 Notation "intro_lets" patnames(list1(seq(
    opt(seq(opt(ident), opt("_"), opt(seq(":=", preterm)), opt(seq(":", preterm)))),
    opt(seq("as", ident))), ",")) :=
  List.iter (fun (pat, name) => intro_letin2 pat name) patnames.g

