From TensorRocq Require Export BWQuote ProQuote SizedProps SizedProLike.


Import ConstrExtra.

Module CC.

Export BWQuote.CC ProQuote.CC ConstrExtra.CC.

Import Ltac2.Ltac2.


Ltac2 of_MPRO_gen
  (of_n : constr -> 'n) (of_s : constr -> 's)
  (of_t : constr -> 't) : constr -> ('n, 's, 't) PRO :=
  mk_of "of_MPRO" "MPRO" (
    let rec go p :=
    lazy_match! p with
    | Mid ?n => let cn := of_n n in (Pid cn)
    | Mcompose ?l ?r =>
      let cl := go l with cr := go r in
      (Pcompose cl cr)
    | Mstack ?l ?r =>
      let cl := go l with cr := go r in
      Pstack cl cr
    | Mstruct ?n ?m ?s =>
      let cn := of_n n with cm := of_n m with cs := of_s s in
      Pstruct cn cm cs
    | Mgen ?n ?m ?t =>
      let cn := of_n n with cm := of_n m with ct := of_t t in
      Pgen cn cm ct
    end in go
  ).

Ltac2 of_MPRO
  (of_n : constr -> 'n) (of_s : constr -> 's)
  (of_t : constr -> 't) : constr -> ('n btree, 's, 't) PRO :=
  of_MPRO_gen (of_btree of_n) of_s of_t.

Ltac2 of_MMonoidal_gen (of_n : constr -> 'n) (c : constr) : 'n Monoidal :=
  mk_of "of_MMonoidal_gen" "MMonoidal"
  (
  let rec go c :=
    lazy_match! c with
    | @MAssociator _ ?n ?m ?o =>
      let n' := of_n n in
      let m' := of_n m in
      let o' := of_n o in
      Associator n' m' o'
    | @MInvAssociator _ ?n ?m ?o =>
      let n' := of_n n in
      let m' := of_n m in
      let o' := of_n o in
      InvAssociator n' m' o'
    | @MLUnit _ ?n =>
      let n' := of_n n in
      LUnit n'
    | @MInvLUnit _ ?n =>
      let n' := of_n n in
      InvLUnit n'
    | @MRUnit _ ?n =>
      let n' := of_n n in
      RUnit n'
    | @MInvRUnit _ ?n =>
      let n' := of_n n in
      InvRUnit n'
    end in  go) c.

Ltac2 of_MSymmetry_gen (of_n : constr -> 'n) (c : constr) : 'n Symmetry :=
  mk_of "of_MSymmetry_gen" "MSymmetry" (let rec go c :=
    lazy_match! c with
    | @MSwap _ ?n ?m =>
      let n' := of_n n in
      let m' := of_n m in
      Swap n' m'
    end in
    go) c.

Ltac2 of_MAutonomy_gen (of_n : constr -> 'n) (c : constr) : 'n Autonomy :=
  mk_of "of_MAutonomy_gen" "MAutonomy" (let rec go c :=
    lazy_match! c with
    | @MCup _ ?n =>
      let n' := of_n n in
      Cup n'
    | @MCap _ ?n =>
      let n' := of_n n in
      Cap n'
    end in go) c.

Ltac2 of_MFrobenial_gen (of_k : constr -> 'k) (of_i : constr -> 'i) (c : constr) : ('k, 'i) Frobenial :=
  mk_of "of_MFrobenial_gen" "MFrobenial" (let rec go c :=
    lazy_match! c with
    | @MDelta _ ?k ?n ?m =>
      let k' := of_k k in  (* NB : this is wrong too! *)
      let n' := of_i n in
      let m' := of_i m in
      Delta k' n' m'
    end in go) c.



Ltac2 of_MSymmetric_gen (of_n : constr -> 'n) (c : constr) : 'n SymmetricG :=
  mk_of "of_MSymmetric_gen" "MSymmetric" (let rec go c :=
    lazy_match! c with
    | mmonoidal_inl ?m =>
      inl (of_MMonoidal_gen of_n m)
    | inl ?m =>
      inl (of_MMonoidal_gen of_n m)
    | msymmetry_inr ?m =>
      inr (of_MSymmetry_gen of_n m)
    | inr ?m =>
      inr (of_MSymmetry_gen of_n m)
    end in go) c.


Ltac2 of_MAutonomous_gen (of_n : constr -> 'n) (c : constr) : 'n Autonomous :=
  mk_of "of_MAutonomous_gen" "MAutonomous" (let rec go c :=
    lazy_match! c with
    | msymmetric_inl ?m =>
      inl (of_MSymmetric_gen of_n m)
    | inl ?m =>
      inl (of_MSymmetric_gen of_n m)
    | mautonomy_inr ?m =>
      inr (of_MAutonomy_gen of_n m)
    | inr ?m =>
      inr (of_MAutonomy_gen of_n m)
    end in go) c.

Ltac2 of_MFrobenius_gen (of_n : constr -> 'n) (of_k : constr -> 'k)
  (of_i : constr -> 'i) (c : constr) : ('n, 'k, 'i) Frobenius :=
  mk_of "of_MFrobenius_gen" "MFrobenius" (let rec go c :=
    lazy_match! c with
    | mautonomous_inl ?m =>
      inl (of_MAutonomous_gen of_n m)
    | inl ?m =>
      inl (of_MAutonomous_gen of_n m)
    | mfrobenial_inr ?m =>
      inr (of_MFrobenial_gen of_k of_i m)
    | inr ?m =>
      inr (of_MFrobenial_gen of_k of_i m)
    end in go) c.

Ltac2 to_MMonoidal_gen (to_n : 'n -> constr) (m : 'n Monoidal) : constr :=
  match m with
  | Associator n m o =>
    let n' := to_n n in
    let m' := to_n m in
    let o' := to_n o in
    '(@MAssociator _ $n' $m' $o')
  | InvAssociator n m o =>
    let n' := to_n n in
    let m' := to_n m in
    let o' := to_n o in
    '(@MInvAssociator _ $n' $m' $o')
  | LUnit n =>
    let n' := to_n n in
    '(@MLUnit _ $n')
  | InvLUnit n =>
    let n' := to_n n in
    '(@MInvLUnit _ $n')
  | RUnit n =>
    let n' := to_n n in
    '(@MRUnit _ $n')
  | InvRUnit n =>
    let n' := to_n n in
    '(@MInvRUnit _ $n')
  end.

Ltac2 to_MSymmetry_gen (to_n : 'n -> constr) (m : 'n Symmetry) : constr :=
  match m with
  | Swap n m =>
    let n' := to_n n in
    let m' := to_n m in
    '(@MSwap _ $n' $m')
  end.

Ltac2 to_MAutonomy_gen (to_n : 'n -> constr) (m : 'n Autonomy) : constr :=
  match m with
  | Cup n =>
    let n' := to_n n in
    '(@MCup _ $n')
  | Cap n =>
    let n' := to_n n in
    '(@MCap _ $n')
  end.

Ltac2 to_MFrobenial_gen (to_k : 'k -> constr) (to_i : 'i -> constr) (m : ('k, 'i) Frobenial) : constr :=
  match m with
  | Delta k n m =>
    let k' := to_k k in
    let n' := to_i n in
    let m' := to_i m in
    '(MDelta $k' $n' $m')
  | _ => Control.throw_invalid_argument "to_MFrobenial_gen: Cannot convert Delta0 or Delta1 to MDelta!"
  end.

Ltac2 to_MSymmetric_gen (to_n : 'n -> constr) (m : 'n SymmetricG) : constr :=
  sum_elim (fun m =>
    let cm := to_MMonoidal_gen to_n m in
    '(mmonoidal_inl $cm))
    (fun m =>
    let cm := to_MSymmetry_gen to_n m in
    '(msymmetry_inr $cm)) m.

Ltac2 to_MAutonomous_gen (to_n : 'n -> constr) (m : 'n Autonomous) : constr :=
  sum_elim (fun m =>
    let cm := to_MSymmetric_gen to_n m in
    '(msymmetric_inl $cm))
    (fun m =>
    let cm := to_MAutonomy_gen to_n m in
    '(mautonomy_inr $cm)) m.

Ltac2 to_MFrobenius_gen (to_n : 'n -> constr) (to_k : 'k -> constr)
  (to_i : 'i -> constr) (m : ('n, 'k, 'i) Frobenius) : constr :=
  sum_elim (fun m =>
    let cm := to_MAutonomous_gen to_n m in
    '(mautonomous_inl $cm))
    (fun m =>
    let cm := to_MFrobenial_gen to_k to_i m in
    '(mfrobenial_inr $cm)) m.


Ltac2 to_MPRO_gen (to_n : 'n -> constr) (to_s : 's -> constr) (to_t : 't -> constr) :
  ('n, 's, 't) PRO -> constr :=
  let rec go p :=
    match p with
    | Pid n =>
      let cn := to_n n in
      '(Mid $cn)
    | Pcompose l r =>
      let cl := go l with cr := go r in
      '(Mcompose $cl $cr)
    | Pstack l r =>
      let cl := go l with cr := go r in
      '(Mstack $cl $cr)
    | Pstruct n m s =>
      let cn := to_n n with cm := to_n m with cs := to_s s in
      '(Mstruct $cn $cm $cs)
    | Pgen n m t =>
      let cn := to_n n with cm := to_n m with ct := to_t t in
      '(Mgen $cn $cm $ct)
    end
  in go.

Ltac2 to_MPRO (to_n : 'n -> constr) (to_s : 's -> constr) (to_t : 't -> constr) :
  ('n btree, 's, 't) PRO -> constr :=
  to_MPRO_gen (to_btree to_n) to_s to_t.






Ltac2 of_MMonoidal (of_n : constr -> 'n) (c : constr) := of_MMonoidal_gen (of_btree of_n) c.
Ltac2 of_MSymmetry (of_n : constr -> 'n) (c : constr) := of_MSymmetry_gen (of_btree of_n) c.
Ltac2 of_MAutonomy (of_n : constr -> 'n) (c : constr) := of_MAutonomy_gen (of_btree of_n) c.
Ltac2 of_MFrobenial (of_n : constr -> 'n) (c : constr) := of_MFrobenial_gen of_n (of_btree of_unit) c.

Ltac2 of_MSymmetric (of_n : constr -> 'n) (c : constr) := of_MSymmetric_gen (of_btree of_n) c.
Ltac2 of_MAutonomous (of_n : constr -> 'n) (c : constr) := of_MAutonomous_gen (of_btree of_n) c.
Ltac2 of_MFrobenius (of_n : constr -> 'n) (c : constr) := of_MFrobenius_gen (of_btree of_n) of_n (of_btree of_unit) c.



Ltac2 of_MMonoidal_MPRO (of_n : constr -> 'n) (of_t : constr -> 't)
  (c : constr) : ('n btree, 'n btree Monoidal, 't) PRO :=
  of_MPRO_gen (of_btree of_n) (of_MMonoidal of_n) of_t c.
Ltac2 of_MSymmetric_MPRO (of_n : constr -> 'n) (of_t : constr -> 't)
  (c : constr) : ('n btree, 'n btree SymmetricG, 't) PRO :=
  of_MPRO_gen (of_btree of_n) (of_MSymmetric of_n) of_t c.
Ltac2 of_MAutonomous_MPRO (of_n : constr -> 'n) (of_t : constr -> 't)
  (c : constr) : ('n btree, 'n btree Autonomous, 't) PRO :=
  of_MPRO_gen (of_btree of_n) (of_MAutonomous of_n) of_t c.
Ltac2 of_MFrobenius_MPRO (of_n : constr -> 'n) (of_t : constr -> 't)
  (c : constr) : ('n btree, ('n btree, 'n, unit btree) Frobenius, 't) PRO :=
  of_MPRO_gen (of_btree of_n) (of_MFrobenius of_n) of_t c.



Ltac2 to_MMonoidal (to_n : 'n -> constr) (m : 'n btree Monoidal) :=
  to_MMonoidal_gen (to_btree to_n) m.
Ltac2 to_MSymmetry (to_n : 'n -> constr) (m : 'n btree Symmetry) :=
  to_MSymmetry_gen (to_btree to_n) m.
Ltac2 to_MAutonomy (to_n : 'n -> constr) (m : 'n btree Autonomy) :=
  to_MAutonomy_gen (to_btree to_n) m.
Ltac2 to_MFrobenial (to_n : 'n -> constr) (m : ('n, unit btree) Frobenial) :=
  to_MFrobenial_gen to_n (to_btree to_unit) m.

Ltac2 to_MSymmetric (to_n : 'n -> constr) (m : 'n btree SymmetricG) :=
  to_MSymmetric_gen (to_btree to_n) m.
Ltac2 to_MAutonomous (to_n : 'n -> constr) (m : 'n btree Autonomous) :=
  to_MAutonomous_gen (to_btree to_n) m.
Ltac2 to_MFrobenius (to_n : 'n -> constr) (m : ('n btree, 'n, unit btree) Frobenius) :=
  to_MFrobenius_gen (to_btree to_n) to_n (to_btree to_unit) m.



Ltac2 to_MMonoidal_MPRO (to_n : 'n -> constr) (to_t : 't -> constr) (m : ('n btree, 'n btree Monoidal, 't) PRO) : constr :=
  to_MPRO_gen (to_btree to_n) (to_MMonoidal to_n) to_t m.
Ltac2 to_MSymmetric_MPRO (to_n : 'n -> constr) (to_t : 't -> constr) (m : ('n btree, 'n btree SymmetricG, 't) PRO) : constr :=
  to_MPRO_gen (to_btree to_n) (to_MSymmetric to_n) to_t m.
Ltac2 to_MAutonomous_MPRO (to_n : 'n -> constr) (to_t : 't -> constr) (m : ('n btree, 'n btree Autonomous, 't) PRO) : constr :=
  to_MPRO_gen (to_btree to_n) (to_MAutonomous to_n) to_t m.
Ltac2 to_MFrobenius_MPRO (to_n : 'n -> constr) (to_t : 't -> constr) (m : ('n btree, ('n btree, 'n, unit btree) Frobenius, 't) PRO) : constr :=
  to_MPRO_gen (to_btree to_n) (to_MFrobenius to_n) to_t m.


(* FIXME: Move, rewrite with mk_of? *)
Ltac2 of_nat_sum_expr (c : constr) : constr btree :=
  let (ns, b) := parse_nat_btree [] c in
  btree_map (Option.map_default (List.nth ns) '(1:>nat)) b.



Ltac2 to_var_name (c : constr) : ident option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var i => Some i
  | _ => None
  end.

Ltac2 hyp_value (i : ident) : constr :=
  match List.find_opt (fun (j, _, _) => Ident.equal i j) (Control.hyps ()) with
  | Some (_, b, _) =>
    match b with
    | None => Control.throw_invalid_argument (String.app "(hyp_value) hypothesis has no value! " (Ident.to_string i))
    | Some v => v
    end
  | None => Control.throw_invalid_argument (String.app "(hyp_value) no such hypothesis! " (Ident.to_string i))
  end.

Ltac2 close_evar_ended_list (cls : constr) : unit :=
  let fail () := Control.throw_invalid_argument
          (String.app "(close_evar_ended_list) list is not evar-ended! "
            (Message.to_string (Message.of_constr cls))) in
  let rec go c :=
    lazy_match! c with
    | _ :: ?c' =>
      go c'
    | [] => ()
    | ?c =>
      match to_var_name c with
      | Some idn =>
        go (hyp_value idn)
      | None =>
        orelse (fun () => Std.unify c '(@nil _))
          (fun _ => fail())
      end
    end in
  go cls.

(* FIXME: Move *)

Module ConstrDecomp.

Import Constr Unsafe.


Ltac2 rec to_app2_of (f : constr) (c : constr) : (constr * constr) option :=
  match kind c with
  | Unsafe.Cast c _ _ => to_app2_of f c
  | App cf cargs =>
    let numargs := (Array.length cargs) in
    if Int.lt numargs 2 then
      None
    else
    let (cf', cargs') := if Int.gt numargs 2 then
      let cf' := make (App cf (Array.sub cargs 0 (Int.sub numargs 2))) in
      let cargs' := Array.sub cargs (Int.sub numargs 2) 2 in
      (cf', cargs')
      else (cf, cargs) in
    if unify_eq f cf' then
      Some (Array.get cargs' 0, Array.get cargs' 1)
    else None
  | _ => None
  end.

End ConstrDecomp.

Ltac2 of_btree_expr (add : constr) (e : constr) (of_n : constr -> 'n) (c : constr) : 'n btree :=
  let rec go c :=
    if Constr.equal c e then Bempty else
    match ConstrDecomp.to_app2_of add c with
    | Some (l, r) =>
      Bnode (go l) (go r)
    | None =>
      Bleaf (of_n c)
    end in
  go c.

Ltac2 to_btree_expr (add : constr) (e : constr) (to_n : 'n -> constr) (b : 'n btree) : constr :=
  let rec go b :=
    match b with
    | Bnode l r =>
      let cl := go l in
      let cr := go r in
      '($add $cl $cr)
    | Bleaf n => to_n n
    | Bempty => e
    end in
  go b.


Ltac2 is_nat_const (c : constr) :=
  let rec go c :=
    lazy_match! c with
    | Init.Nat.of_num_uint _ => true
    | S ?c => go c
    | 0 => true
    | ?f ?l ?r =>
      if lazy_match! f with
         | Nat.add => true
         | Nat.sub => true
         | Nat.mul => true
         | Nat.div => true
         | Nat.modulo => true
         | Nat.min => true
         | Nat.max => true
         | Nat.pow => true
         | _ => false
         end then (if go l then go r else false)
      else false
    | _ =>
      let c' := Std.eval_hnf c in
      if Constr.equal c c' then false
      else go c
    end in
  go c.






Ltac2 get_concr_asgn_list (cs : constr list) : constr :=
  let ics := Ltac2.List.enumerate cs in
  let const_ics : (int * constr) list := List.filter (fun (_, c) => is_nat_const c) ics in
  CC.to_list (CC.to_pair_typed ('positive, 'nat)
    (fun i => CC.to_pos (Int.add 1 i)) (fun c => c)) const_ics.


Ltac2 specialize_with_concr_asgn_list (hrw : constr) (ln : constr) : unit :=
  let lns := of_evar_ended_list (fun i => i) ln in
  let concr_asgn := get_concr_asgn_list lns in
  let concr_asgn_map := '(fin_maps.list_to_map (M:=pmap.Pmap nat) $concr_asgn) in
  Std.resolve_tc concr_asgn_map;
  specialize ($hrw $concr_asgn_map).


End CC.


Ltac close_evar_ended_list c :=
  let close := ltac2:(c |- CC.close_evar_ended_list (Option.get (Ltac1.to_constr c))) in
  close c.

Tactic Notation "close_evar_ended_list" constr(c) :=
  let close := ltac2:(c |- CC.close_evar_ended_list (Option.get (Ltac1.to_constr c))) in
  close c.

Tactic Notation "specialize_with_concr_asgn_list" constr(hrw) constr(c) :=
  let close := ltac2:(hrw c |- CC.specialize_with_concr_asgn_list
    (Option.get (Ltac1.to_constr hrw)) (Option.get (Ltac1.to_constr c))) in
  close hrw c.



(* FIXME: Move, to Aux? *)
Ltac enable_timing :=
  fail.

Tactic Notation "time?" string(s) tactic3(tac) :=
  tryif enable_timing then
    idtac "Running" s"...";
    time "time?_internal" tac
  else tac.

Tactic Notation "time?" tactic3(tac) :=
  tryif enable_timing then
    time "time?_internal" tac
  else tac.






Import Ltac2.Ltac2.

(* NB : We need to make absolutely sure the first element of
  the constr list is 1 *)


Ltac2 parse_nat_btree_to_pos (ns : constr list)
  (c : constr) : constr list * int btree :=
  let (ns, b) := parse_nat_btree ns c in
  let (ns, n_one) := constr_get_nth ns '(1:>nat) in
  (ns, btree_map (Ltac2.Option.map_default (Int.add 1) (Int.add 1 n_one)) b).


Local Ltac2 pair : 'a -> 'b -> 'a * 'b := fun a b => (a, b).

Local Ltac2 id : 'a -> 'a := fun a => a.

Ltac2 posify_MPRO_sizes (fs : constr list -> 's -> constr list * 's')
  (ns : constr list)
  (p : (constr, 's, 't) PRO) : constr list * (int btree, 's', 't) PRO :=
  map_PRO_with parse_nat_btree_to_pos fs pair ns p.

Ltac2 constr_get_pth (cs : constr list) (c : constr) : constr list * int :=
  let (cs, n) := constr_get_nth cs c in
  (cs, Int.add 1 n).

Ltac2 map_btree_with (f : 'st -> 'a -> 'st * 'b)
  (st : 'st) (b : 'a btree) : 'st * 'b btree :=
  let rec go st b :=
    match b with
    | Bnode l r =>
      let (st, l') := go st l in
      let (st, r') := go st r in
      (st, Bnode l' r')
    | Bleaf a =>
      let (st, a') := f st a in
      (st, Bleaf a')
    | Bempty =>
      (st, Bempty)
    end
  in go st b.

Import Props AbstractTensorQuote.



(* FIXME: Move *)
Ltac2 bleaf (a : 'a) : 'a btree := Bleaf a.
Ltac2 bnode (a : 'a btree) b : 'a btree := Bnode a b.



(* FIXME: Move *)
Ltac2 Notation l(thunk(self)) "||" r(thunk(self)) : 2 :=
  orelse l (fun _ => r()).

Import Printf.

Ltac2 print_goal (s : string) : unit :=
  let g := Control.goal() in
  printf "Goal (%s):" s;
  Message.print (Message.of_constr g).



Ltac2 mk_MPRO_PRO_chain_gen (cfN : constr)
  (to_s : 's -> int btree * int btree * constr) (to_t : 't -> constr)
  (mp : (int btree, 's, 't) PRO) : int btree * int btree * (unit -> unit) :=
  let bad_goal (s : string) :=
    (* lazy_match! goal with
    | [|- ?g] => Message.print (Message.of_string (String.concat "" ["bad goal ("; s; ")! "
      ; Message.to_string (Message.of_constr g)]));
      Control.shelve()
    end in *)
    lazy_match! goal with
    | [|- ?g] => Control.throw_invalid_argument (String.concat "" ["bad goal ("; s; ")! "
      ; Message.to_string (Message.of_constr g)])
    end in
  let to_btree := CC.to_btree_typed constr:(positive) CC.to_pos in
  let rec go mp :=
    match mp with
    | Pstruct _ _ s =>
      let (ins, outs, cs) := to_s s in
      let cins := to_btree ins in
      let couts := to_btree outs in
      (ins, outs, fun () =>
        refine '(MPC_struct $cfN $cins $couts $cs) || bad_goal "struct")
    | Pgen ins outs t =>
      let ct := to_t t in
      let cins := to_btree ins in
      let couts := to_btree outs in
      (ins, outs, fun () =>
      refine '(MPC_gen $cfN $cins $couts $ct) || bad_goal "gen")
    | Pid i =>
      let ci := to_btree i in
      (i, i, fun () =>
      refine '(MPC_id $cfN $ci) || bad_goal "id")
    | Pstack t b =>
      let (tn, tm, t_tac) := go t in
      let (bn, bm, b_tac) := go b in
      let ctn := to_btree tn in
      let ctm := to_btree tm in
      let cbn := to_btree bn in
      let cbm := to_btree bm in
      (Bnode tn bn, Bnode tm bm, fun () =>
      (lazy_match! goal with
      | [|- MPRO_PRO_chain _ _ (@Pstack _ _ ?cn1 ?cm1 ?cn2 ?cm2 ?pt ?pb) ] =>
        refine '(MPC_stack $cfN $ctn $ctm $cbn $cbm _ _
        (n:=$cn1) (m:=$cm1) (n':=$cn2) (m':=$cm2) $pt $pb  _ _)
           > [Control.shelve()..|t_tac()|b_tac()]
      | [|- _] => 
        refine '(MPC_stack $cfN $ctn $ctm $cbn $cbm _ _
          _ _  _ _)
      end
        )|| bad_goal "stack")
    | Pcompose l r =>
      let (ln, lm, l_tac) := go l in
      let (rm, ro, r_tac) := go r in
      let cln := to_btree ln in
      let clm := to_btree lm in
      let crm := to_btree rm in
      let cro := to_btree ro in

      if btree_eq Int.equal lm rm then
        (ln, ro, fun () =>
          (refine '(MPC_compose $cfN $cln $clm $cro _ _
            _ _   _ _) 
           > [(* print_goal "compose";  *)Control.shelve()..|l_tac()|r_tac()]

            )|| bad_goal "compose")
      else
        (* TODO: Is this route better? *)
        (* let chp := constr:(ltac:(compute_done) : is_Some (BW.may_bpath $clm $crm)) in *)
        let cp := match! Std.eval_vm None constr:(BW.may_bpath $clm $crm) with
          | Some ?cp => cp
          | None => Control.throw_invalid_argument "mk_MPRO_PRO_chain_gen: unresolvable path!!"
          end in
        (ln, ro, fun () =>
          (refine '(MPC_compose_reassoc $cfN $cln $clm $crm $cro ($cp) _ _
            _ _   _ _)
           > [Control.shelve()..|l_tac()|r_tac()]

            )|| bad_goal "compose_reassoc")
    end
  in go mp.



(* FIXME: Move *)

Ltac2 denote_pos_btree (ns : constr list) (c : int btree) : constr :=
  btree_fold constr:(O) ((fun i => List.nth ns (Int.sub i 1)))
    (fun l r => constr:(Nat.add $l $r)) c.

Ltac2 mk_MPRO_PRO_chain_Monoidal_go cfN (m : (int btree, int btree Monoidal, constr) PRO) : unit :=
  let (_, _, tac) := mk_MPRO_PRO_chain_gen cfN (fun s =>
    let (ins, outs) := dim_Monoidal Bempty bnode id s in
    let cs := CC.to_MMonoidal CC.to_pos s in
    (ins, outs, cs)) id m in
  tac().


Ltac2 mk_MPRO_PRO_quote_Monoidal () :=
  lazy_match! goal with
  | [|- MPRO_PRO_quote (Struct:=_) (T:=?_cT) (@interp_discrete_hg_inhab _ ?inhab ?cts) _ ?cp] =>
    let p := once (CC.of_PRO id (CC.of_Monoidal_gen id) id cp) in
    let ts := CC.of_evar_ended_list id cts in
    let map_btree := parse_nat_btree_to_pos in
    let (ts', mp) := map_PRO_with map_btree
        (map_Monoidal_with map_btree) pair ts p in
    let _cts := once (CC.extend_evar_ended_list ts' cts) in
    apply MPRO_PRO_quote_of_chain >
    [Control.throw_invalid_argument "mk_MPRO_PRO_quote_Monoidal: Extra goals! Are all typeclasses declared?"..|
    mk_MPRO_PRO_chain_Monoidal_go constr:(@interp_discrete_hg_inhab _ $inhab $cts) mp]
  end.


Ltac2 mk_MPRO_PRO_denote_Monoidal () :=
  lazy_match! goal with
  | [|- MPRO_PRO_denote (Struct:=_) (T:=?_cT) (interp_discrete_hg_inhab ?cts)
    (a:=?ca) (b:=?cb) ?cmp (n:=?ecn) (m:=?ecm) ?ecp] =>
    let mp := once (CC.of_MMonoidal_MPRO CC.of_pos id cmp) in
    let (n, m) := dim_PRO bnode mp in
    let ts := CC.of_evar_ended_list id cts in
    let btden := denote_pos_btree ts in
    let cn := btden n in
    let cm := btden m in
    let p := map_PRO btden (map_Monoidal btden) id mp in
    let cp := CC.to_PRO id (CC.to_Monoidal_gen id) id p in
    Std.unify cn ecn;
    Std.unify cm ecm;
    Std.unify ecp cp;
    apply (MPRO_PRO_denote_of_refl _ $ca $cb $cmp $cn $cm $cp);
    reflexivity
  end.


Ltac2 mk_MPRO_PRO_chain_SymmetricG_go cfN (m : (int btree, int btree SymmetricG, constr) PRO) : unit :=
  let (_, _, tac) := mk_MPRO_PRO_chain_gen cfN (fun s =>
    let (ins, outs) := dim_SymmetricG Bempty bnode id s in
    let cs := CC.to_MSymmetric CC.to_pos s in
    (ins, outs, cs)) id m in
  tac().


Ltac2 mk_MPRO_PRO_quote_SymmetricG () :=
  lazy_match! goal with
  | [|- MPRO_PRO_quote (Struct:=_) (T:=?_cT) (@interp_discrete_hg_inhab _ ?inhab ?cts) _ ?cp] =>
    let p := once (CC.of_PRO id (CC.of_SymmetricG_gen id) id cp) in
    let ts := CC.of_evar_ended_list id cts in
    let map_btree := parse_nat_btree_to_pos in
    let (ts', mp) := map_PRO_with map_btree
        (map_SymmetricG_with map_btree) pair ts p in
    let _cts := once (CC.extend_evar_ended_list ts' cts) in
    apply MPRO_PRO_quote_of_chain >
    [Control.throw_invalid_argument "mk_MPRO_PRO_quote_SymmetricG: Extra goals! Are all typeclasses declared?"..|
    mk_MPRO_PRO_chain_SymmetricG_go constr:(@interp_discrete_hg_inhab _ $inhab $cts) mp]
  end.


Ltac2 mk_MPRO_PRO_denote_SymmetricG () :=
  lazy_match! goal with
  | [|- MPRO_PRO_denote (Struct:=_) (T:=?_cT) (interp_discrete_hg_inhab ?cts)
    (a:=?ca) (b:=?cb) ?cmp (n:=?ecn) (m:=?ecm) ?ecp] =>
    let mp := once (CC.of_MSymmetric_MPRO CC.of_pos id cmp) in
    let (n, m) := dim_PRO bnode mp in
    let ts := CC.of_evar_ended_list id cts in
    let btden := denote_pos_btree ts in
    let cn := btden n in
    let cm := btden m in
    let p := map_PRO btden (map_SymmetricG btden) id mp in
    let cp := CC.to_PRO id (CC.to_SymmetricG_gen id) id p in
    Std.unify cn ecn;
    Std.unify cm ecm;
    Std.unify ecp cp;
    apply (MPRO_PRO_denote_of_refl _ $ca $cb $cmp $cn $cm $cp);
    reflexivity
  end.


Ltac2 mk_MPRO_PRO_chain_Autonomous_go cfN (m : (int btree, int btree Autonomous, constr) PRO) : unit :=
  let (_, _, tac) := mk_MPRO_PRO_chain_gen cfN (fun s =>
    let (ins, outs) := dim_Autonomous Bempty bnode id s in
    let cs := CC.to_MAutonomous CC.to_pos s in
    (ins, outs, cs)) id m in
  tac().


Ltac2 mk_MPRO_PRO_quote_Autonomous () :=
  lazy_match! goal with
  | [|- MPRO_PRO_quote (Struct:=_) (T:=?_cT) (@interp_discrete_hg_inhab _ ?inhab ?cts) _ ?cp] =>
    let p := once (CC.of_PRO id (CC.of_Autonomous_gen id) id cp) in
    let ts := CC.of_evar_ended_list id cts in
    let map_btree := parse_nat_btree_to_pos in
    let (ts', mp) := map_PRO_with map_btree
        (map_Autonomous_with map_btree) pair ts p in
    let _cts := once (CC.extend_evar_ended_list ts' cts) in
    apply MPRO_PRO_quote_of_chain >
    [Control.throw_invalid_argument "mk_MPRO_PRO_quote_Autonomous: Extra goals! Are all typeclasses declared?"..|
    mk_MPRO_PRO_chain_Autonomous_go constr:(@interp_discrete_hg_inhab _ $inhab $cts) mp]
  end.


Ltac2 mk_MPRO_PRO_denote_Autonomous () :=
  lazy_match! goal with
  | [|- MPRO_PRO_denote (Struct:=_) (T:=?_cT) (interp_discrete_hg_inhab ?cts)
    (a:=?ca) (b:=?cb) ?cmp (n:=?ecn) (m:=?ecm) ?ecp] =>
    let mp := once (CC.of_MAutonomous_MPRO CC.of_pos id cmp) in
    let (n, m) := dim_PRO bnode mp in
    let ts := CC.of_evar_ended_list id cts in
    let btden := denote_pos_btree ts in
    let cn := btden n in
    let cm := btden m in
    let p := map_PRO btden (map_Autonomous btden) id mp in
    let cp := CC.to_PRO id (CC.to_Autonomous_gen id) id p in
    Std.unify cn ecn;
    Std.unify cm ecm;
    Std.unify ecp cp;
    apply (MPRO_PRO_denote_of_refl _ $ca $cb $cmp $cn $cm $cp);
    reflexivity
  end.


Module testing.

Import ProQuote.testing.

Open Scope pro_scope.

Definition monoidal_test_diags : list {nm & PRO Monoidal positive nm.1 nm.2} :=
  Eval cbn [monoidal_test_diags app] in
  ProQuote.testing.monoidal_test_diags ++
  [
    !(Passoc 1 1 1 ;; Passoc 1 1 1);
    !(Passoc 1 2 1 ;; Passoc (2 + 0) 1 1)
  ].

Definition symmetricg_test_diags : list {nm & PRO SymmetricG positive nm.1 nm.2} :=
  Eval cbn [symmetricg_test_diags app] in
  ProQuote.testing.symmetricg_test_diags ++
  [
    !(Passoc 1 1 1 ;; Passoc 1 1 1);
    !(Passoc 1 2 1 ;; Passoc (2 + 0) 1 1);
    !(Passoc 1 1 1 ;; Passoc 1 1 1 ;; Pswap 1 1 * Pid 1);
    !(Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0)
  ].

Definition autonomous_test_diags : list {nm & PRO Autonomous positive nm.1 nm.2} :=
  Eval cbn [autonomous_test_diags app] in
  ProQuote.testing.autonomous_test_diags ++
  [
    !(Passoc 1 1 1 ;; Passoc 1 1 1);
    !(Passoc 1 2 1 ;; Passoc (2 + 0) 1 1);
    !(Passoc 1 1 1 ;; Passoc 1 1 1 ;; Pswap 1 1 * Pid 1);
    !(Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0);
    !(Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0 ;; Pcap 2);
    !(Pcup 2 ;; Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0 ;; Pcap 2)
  ].

Ltac2 monoidal_roundtrip_test l (cm : constr) :=
  ltac1:(l cm |-

  let lv := eval unfold l in l in
  eassert (Hq : MPRO_PRO_quote (interp_discrete_hg_inhab lv) _
    (cm :> PRO Monoidal positive _ _))
      by ltac2:(mk_MPRO_PRO_quote_Monoidal());
  cbn [gbpath_to_MPRO] in Hq;
  lazymatch goal with
  | H : MPRO_PRO_quote ?f ?m _ |- _ => eassert (Hq' : MPRO_PRO_denote f m 
    (_ :> PRO Monoidal positive _ _)) by ltac2:(mk_MPRO_PRO_denote_Monoidal())
  ; clear Hq Hq'
  end

  ) (Ltac1.of_ident l) (Ltac1.of_constr cm).

Ltac2 symmetricg_roundtrip_test l (cm : constr) :=
  ltac1:(l cm |-

  let lv := eval unfold l in l in
  eassert (Hq : MPRO_PRO_quote (interp_discrete_hg_inhab lv) _
    (cm :> PRO SymmetricG positive _ _))
      by ltac2:(mk_MPRO_PRO_quote_SymmetricG());
  cbn [gbpath_to_MPRO] in Hq;
  lazymatch goal with
  | H : MPRO_PRO_quote ?f ?m _ |- _ => eassert (Hq' : MPRO_PRO_denote f m _) by ltac2:(mk_MPRO_PRO_denote_SymmetricG())
  ; clear Hq Hq'
  end

  ) (Ltac1.of_ident l) (Ltac1.of_constr cm).

Ltac2 autonomous_roundtrip_test l (cm : constr) :=
  ltac1:(l cm |-

  let lv := eval unfold l in l in
  eassert (Hq : MPRO_PRO_quote (interp_discrete_hg_inhab lv) _
    (cm :> PRO Autonomous positive _ _))
      by ltac2:(mk_MPRO_PRO_quote_Autonomous());
  cbn [gbpath_to_MPRO] in Hq;
  lazymatch goal with
  | H : MPRO_PRO_quote ?f ?m _ |- _ => eassert (Hq' : MPRO_PRO_denote f m _) by ltac2:(mk_MPRO_PRO_denote_Autonomous())
  ; clear Hq Hq'
  end

  ) (Ltac1.of_ident l) (Ltac1.of_constr cm).

Goal forall (n : nat), True.
intros n.
Proof Mode "Classic".
evar (l : list nat).

Import PropsGraphs SizedPropsGraphs.
Import PrintingExtra.
(* unshelve *)


ltac2:(
let cmon := CC.of_list (of_bundled id) 'monoidal_test_diags in
List.iter (monoidal_roundtrip_test @l) cmon).

ltac2:(
let cmon := CC.of_list (of_bundled id) 'symmetricg_test_diags in
List.iter (symmetricg_roundtrip_test @l) cmon).

ltac2:(monoidal_roundtrip_test @l constr:((Passoc 1 1 n ;; Passoc 1 1 n :> PRO Monoidal positive _ _))).



ltac2:(
let cmon := CC.of_list (of_bundled id) 'autonomous_test_diags in
List.iteri (fun i c => 
  (* FIXME: Bad hack!! Instead, refactor to make the quote maker take the parsed constr
  as well so it can give all arguments (and at that point maybe make it generate a constr
  proof rather than tactic one?)*)
  if Bool.and (Int.le 9 i) (Int.le i 10) then () (* skip tests involving Psw... *)
  else 
  (autonomous_roundtrip_test @l c)) cmon).



let lv := eval unfold l in l in
eassert (Hq : MPRO_PRO_quote (interp_discrete_hg_inhab lv) _
  (Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0 :> PRO Autonomous positive _ _))
    by ltac2:(mk_MPRO_PRO_quote_Autonomous());
cbn [gbpath_to_MPRO] in Hq;
lazymatch goal with
| H : MPRO_PRO_quote ?f ?m _ |- _ => eassert (Hq' : MPRO_PRO_denote f m _) by ltac2:(mk_MPRO_PRO_denote_Autonomous())
end; clear Hq Hq'.


let lv := eval unfold l in l in
eassert (Hq : MPRO_PRO_quote (interp_discrete_hg_inhab lv) _
  (Passoc 2 1 1 ;; Passoc 2 1 1 ;; Pswap 2 2 * Pid 0 ;; Pcap 2 :> PRO Autonomous positive _ _))
    by ltac2:(mk_MPRO_PRO_quote_Autonomous());
cbn [gbpath_to_MPRO] in Hq;
lazymatch goal with
| H : MPRO_PRO_quote ?f ?m _ |- _ => eassert (Hq' : MPRO_PRO_denote f m _) by ltac2:(mk_MPRO_PRO_denote_Autonomous())
end; clear Hq Hq'.

close_evar_ended_list l.
done.
Qed.


End testing.




#[global] Hint Extern 0
  (MPRO_PRO_quote (Struct:=?Struct) _ _ _) =>
  tryif unify Struct Monoidal then
    ltac2:(mk_MPRO_PRO_quote_Monoidal())
  else tryif unify Struct SymmetricG then
    ltac2:(mk_MPRO_PRO_quote_SymmetricG())
  else tryif unify Struct Autonomous then
    ltac2:(mk_MPRO_PRO_quote_Autonomous())
  else tryif unify Struct Frobenius then
    ltac2:(Message.print (Message.of_string "ERROR: Sized rewriting with Frobenius is not available yet!");
    Control.throw_invalid_argument "ERROR: Sized rewriting with Frobenius is not available yet!")
    (* ltac2:(mk_MPRO_PRO_quote_Frobenius()) *)
  else fail : typeclass_instances.

#[global] Hint Extern 0
  (MPRO_PRO_denote (Struct:=?Struct) _ _ _) =>
  tryif unify Struct Monoidal then
    ltac2:(mk_MPRO_PRO_denote_Monoidal())
  else tryif unify Struct SymmetricG then
    ltac2:(mk_MPRO_PRO_denote_SymmetricG())
  else tryif unify Struct Autonomous then
    ltac2:(mk_MPRO_PRO_denote_Autonomous())
  else tryif unify Struct Frobenius then
    ltac2:(Message.print (Message.of_string "ERROR: Sized rewriting with Frobenius is not available yet!");
    Control.throw_invalid_argument "ERROR: Sized rewriting with Frobenius is not available yet!")
    (* ltac2:(mk_MPRO_PRO_quote_Frobenius()) *)
  else fail : typeclass_instances.


(*
Ltac2 mk_MPRO_PRO_quote_Monoidal () :=
  match! goal with
  | [|- MPRO_PRO_quote (Struct:=Monoidal) (T:=?cT) (interp_discrete_hg_inhab ?cts) _ ?cp] =>
    let p := CC.of_PRO id (CC.of_Monoidal id) id cp in
    let ts := CC.of_evar_ended_list id cts in
    let (ts, pi) := posify_MPRO_sizes (map_Monoidal_with parse_nat_btree_to_pos) ts p in
    let cmi := CC.to_MPRO CC.to_pos (CC.to_MMonoidal CC.to_pos) id pi in
    let cts := CC.extend_evar_ended_list ts cts in
    refine '(mk_MPRO_PRO_quote (MStruct:=@MMonoidal positive) (Struct:=Monoidal)
      (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi)
  end. *)


(* Set Default Proof Mode "Classic".
Import PropsGraphs.
Goal (forall (n m o p : nat), True).
intros.
Import BW.
epose (?[l] : list nat).
eassert (MPRO_PRO_denote (Struct:=SymmetricG)
      (interp_discrete_hg_inhab (m :: 1 :: n :: p :: ?l))
      (((((((((([gen 1%positive (! 3%positive)
                (! 4%positive + ! 1%positive + ! 3%positive)];;
                Mid (! 4%positive) *
                [gen 2%positive (! 1%positive) (! 1%positive)] *
                [gen 3%positive (! 3%positive) (! 1%positive)]);;
               Mid (! 4%positive + ! 1%positive) *
               [gen 1%positive (! 1%positive) (! 3%positive)]);;
              (([str inl MInvRUnit] * [str inl MInvRUnit];;
                [str inl MAssociator]);;
               Mid (! 4%positive) * [str inl MLUnit]) *
              [str inl MInvRUnit]);; [str inl MAssociator]);;
            Mid (! 4%positive) *
            ([str inl MAssociator];;
             Mid (! 1%positive) * [str inl MLUnit]));;
           Mid (! 4%positive) *
           (([str inl MInvAssociator];;
             [str inr (MSwap (! 1%positive) (! 3%positive))] *
             Mid 0);; [str inl MAssociator]));;
          Mid (! 4%positive) *
          (Mid (! 3%positive) * [str inl MInvLUnit];;
           [str inl MInvAssociator]));; [str inl MInvAssociator]);;
        ((Mid (! 4%positive) * [str inl MInvLUnit];;
          [str inl MInvAssociator]);;
         [str inl MRUnit] * [str inl MRUnit]) *
        [str inl MRUnit]);;
       [gen 4%positive
       (! 4%positive + ! 3%positive + ! 1%positive)
       (! 4%positive)])%mpro _).

ltac2:(mk_MPRO_PRO_denote_SymmetricG()).
Set Typeclasses Debug.
apply _.
Proof Mode "Ltac2".



Ltac2 Eval
lazy_match! goal with
| [|- MPRO_PRO_quote (Struct:=SymmetricG) (T:=?cT) (interp_discrete_hg_inhab ?cts) ?cmp _] =>
  let mp := CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp in
  let ts := CC.of_evar_ended_list id cts in
  let denote_btree := denote_pos_btree ts in

  let p := ProQuote.map_PRO denote_btree (map_SymmetricG denote_btree) id mp in

  let cp := CC.to_PRO id (CC.to_SymmetricG id) id p in
  cp
  (*
  let p := CC.of_PRO id (CC.of_SymmetricG id) id cp in
  let (ts, pi) := posify_MPRO_sizes (map_SymmetricG_with parse_nat_btree_to_pos) ts p in
  let cmi := CC.to_MPRO CC.to_pos (CC.to_MSymmetric CC.to_pos) id pi in
  let cts := CC.extend_evar_ended_list ts cts in
  refine '(mk_MPRO_PRO_quote (MStruct:=@MSymmetric positive) (Struct:=SymmetricG)
    (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi) *)
end.

Ltac2 Eval

Ltac2 Eval
  let cmp := constr:((((
               [str inr (MSwap (! 1%positive) (! 3%positive))])))%mpro :> MPROP positive _ _) in
  CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp.

Ltac2 Eval
  let cmp := constr:((((((([gen 1%positive (! 3%positive)
	              (! 4%positive + ! 1%positive + ! 3%positive)];;
                  Mid (! 4%positive) *
                  [gen 2%positive (! 1%positive) (! 1%positive)] *
                  [gen 3%positive (! 3%positive) (! 1%positive)]);;
                 Mid (! 4%positive + ! 1%positive) *
                 [gen 1%positive (! 1%positive) (! 3%positive)]);;
                (([str inl MInvRUnit] * [str inl MInvRUnit];;
                  [str inl MAssociator]);;
                 Mid (! 4%positive) * [str inl MLUnit]) *
                [str inl MInvRUnit]);; [str inl MAssociator]);;
              Mid (! 4%positive) *
              ([str inl MAssociator];; Mid (! 1%positive) * [str inl MLUnit]));;
             Mid (! 4%positive) *
             (([str inl MInvAssociator];;
               [str inr (MSwap (! 1%positive) (! 3%positive))] * Mid 0);;
              [str inl MAssociator]))%mpro :> MPROP positive _ _) in
  CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp.

Ltac2 Eval
  let cmp := constr:(((((
            Mid (! 4%positive) *
            (Mid (! 3%positive) * [str inl MInvLUnit];;
             [str inl MInvAssociator]));; [str inl MInvAssociator]);;
          ((Mid (! 4%positive) * [str inl MInvLUnit];;
            [str inl MInvAssociator]);; [str inl MRUnit] * [str inl MRUnit]) *
          [str inl MRUnit]);;
         [gen 4%positive (! 4%positive + ! 3%positive + ! 1%positive)
         (! 4%positive)])%mpro :> MPROP positive _ _) in
  CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp.

Ltac2 Eval
  let cmp := constr:((((((((((([gen 1%positive (! 3%positive)
	              (! 4%positive + ! 1%positive + ! 3%positive)];;
                  Mid (! 4%positive) *
                  [gen 2%positive (! 1%positive) (! 1%positive)] *
                  [gen 3%positive (! 3%positive) (! 1%positive)]);;
                 Mid (! 4%positive + ! 1%positive) *
                 [gen 1%positive (! 1%positive) (! 3%positive)]);;
                (([str inl MInvRUnit] * [str inl MInvRUnit];;
                  [str inl MAssociator]);;
                 Mid (! 4%positive) * [str inl MLUnit]) *
                [str inl MInvRUnit]);; [str inl MAssociator]);;
              Mid (! 4%positive) *
              ([str inl MAssociator];; Mid (! 1%positive) * [str inl MLUnit]));;
             Mid (! 4%positive) *
             (([str inl MInvAssociator];;
               [str inr (MSwap (! 1%positive) (! 3%positive))] * Mid 0);;
              [str inl MAssociator]));;
            Mid (! 4%positive) *
            (Mid (! 3%positive) * [str inl MInvLUnit];;
             [str inl MInvAssociator]));; [str inl MInvAssociator]);;
          ((Mid (! 4%positive) * [str inl MInvLUnit];;
            [str inl MInvAssociator]);; [str inl MRUnit] * [str inl MRUnit]) *
          [str inl MRUnit]);;
         [gen 4%positive (! 4%positive + ! 3%positive + ! 1%positive)
         (! 4%positive)])%mpro :> MPROP positive _ _) in
  CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp.

lazy_match! goal with
| [|- MPRO_PRO_quote (Struct:=SymmetricG) (T:=?cT) (interp_discrete_hg_inhab ?cts) ?cmp _] =>
  let mp := CC.of_MPRO CC.of_pos (CC.of_MSymmetric CC.of_pos) id cmp in
  mp
  (* let p := CC.of_PRO id (CC.of_SymmetricG id) id cp in
  let ts := CC.of_evar_ended_list id cts in
  let (ts, pi) := posify_MPRO_sizes (map_SymmetricG_with parse_nat_btree_to_pos) ts p in
  let cmi := CC.to_MPRO CC.to_pos (CC.to_MSymmetric CC.to_pos) id pi in
  let cts := CC.extend_evar_ended_list ts cts in
  refine '(mk_MPRO_PRO_quote (MStruct:=@MSymmetric positive) (Struct:=SymmetricG)
    (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi) *)
end.
4: typeclasses eauto.
all: shelve_unifiable.



(*
Goal True.
eassert (MPRO_PRO_quote (Struct:=Frobenius) (T:=bool)
  (interp_discrete_hg_inhab _) _ (Pgen 1 1 true)).
  apply _.
  mk_MPRO_PRO_quote_Monoidal().


    let pi := map_PRO id id (fun x => CC.to_pos (Int.add x 1)) pi in
    let (_, _, cpi) := CC.to_PRO_safe struct_T '(positive) id id id pi in
    let cts := CC.extend_evar_ended_list ts' cts in
    Std.unify cqp cpi;
    refine '(mk_MPRO_PRO_quote (MStruct:=@MMonoidal positive)
      (T:=positive) (T':=$t_T) (interp_discrete_hg_inhab $cts) $cpi $cp _);
    reflexivity *) *)
