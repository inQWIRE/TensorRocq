From TensorRocq Require Export BWQuote ProQuote SizedProps SizedProLike.


Import ConstrExtra. 

Module CC.

Export BWQuote.CC ProQuote.CC ConstrExtra.CC.

Import Ltac2.Ltac2.


Ltac2 of_MPRO
  (of_n : constr -> 'n) (of_s : constr -> 's)
  (of_t : constr -> 't) : constr -> ('n btree, 's, 't) PRO :=
  mk_of "of_MPRO" "MPRO" (
    let rec go p :=
    lazy_match! p with
    | Mid ?n => let cn := of_btree of_n n in (Pid cn)
    | Mcompose ?l ?r =>
      let cl := go l with cr := go r in
      (Pcompose cl cr)
    | Mstack ?l ?r =>
      let cl := go l with cr := go r in
      Pstack cl cr
    | Mstruct ?n ?m ?s =>
      let cn := of_btree of_n n with cm := of_btree of_n m with cs := of_s s in
      Pstruct cn cm cs
    | Mgen ?n ?m ?t =>
      let cn := of_btree of_n n with cm := of_btree of_n m with ct := of_t t in
      Pgen cn cm ct
    end in go
  ).

Ltac2 of_MMonoidal (of_n : constr -> 'n) (c : constr) : 'n btree Monoidal :=
  mk_of "of_MMonoidal" "MMonoidal"
  (
  let rec go c :=
    lazy_match! c with
    | @MAssociator _ ?n ?m ?o => 
      let n' := of_btree of_n n in 
      let m' := of_btree of_n m in 
      let o' := of_btree of_n o in 
      Associator n' m' o'
    | @MInvAssociator _ ?n ?m ?o => 
      let n' := of_btree of_n n in 
      let m' := of_btree of_n m in 
      let o' := of_btree of_n o in 
      InvAssociator n' m' o'
    | @MLUnit _ ?n => 
      let n' := of_btree of_n n in 
      LUnit n'
    | @MInvLUnit _ ?n => 
      let n' := of_btree of_n n in 
      InvLUnit n'
    | @MRUnit _ ?n => 
      let n' := of_btree of_n n in 
      RUnit n'
    | @MInvRUnit _ ?n => 
      let n' := of_btree of_n n in 
      InvRUnit n'
    end in  go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Monoidal: argument is not reducible to a [Monoidal] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Monoidal: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_MSymmetry (of_n : constr -> 'n) (c : constr) : 'n btree Symmetry :=
  mk_of "of_MSymmetry" "MSymmetry" (let rec go c :=
    lazy_match! c with
    | @MSwap ?n ?m => 
      let n' := of_btree of_n n in 
      let m' := of_btree of_n m in
      Swap n' m'
    end in 
    go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Symmetry: argument is not reducible to a [Symmetry] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Symmetry: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_MAutonomy (of_n : constr -> 'n) (c : constr) : 'n btree Autonomy :=
  mk_of "of_MAutonomy" "MAutonomy" (let rec go c :=
    lazy_match! c with
    | @MCup ?n => 
      let n' := of_btree of_n n in 
      Cup n'
    | @MCap ?n => 
      let n' := of_btree of_n n in 
      Cap n'
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Autonomy: argument is not reducible to a [Autonomy] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Autonomy: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_MFrobenial (of_n : constr -> 'n) (c : constr) : 'n btree Frobenial :=
  mk_of "of_MFrobenial" "MFrobenial" (let rec go c :=
    lazy_match! c with
    | @MDelta ?k ?n ?m => 
      let k' := of_btree of_n k in 
      let n' := of_nat n in
      let m' := of_nat m in
      (* let n' := of_n n in 
      let m' := of_n m in  *)
      Delta k' n' m'
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Frobenial: argument is not reducible to a [Frobenial] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Frobenial: error with argument " (to_string (of_constr c)))
  end. *)



Ltac2 of_MSymmetric (of_n : constr -> 'n) (c : constr) : 'n btree SymmetricG :=
  mk_of "of_MSymmetric" "MSymmetric" (let rec go c :=
    lazy_match! c with
    | mmonoidal_inl ?m => 
      inl (of_MMonoidal of_n m)
    | inl ?m => 
      inl (of_MMonoidal of_n m)
    | msymmetry_inr ?m => 
      inr (of_MSymmetry of_n m)
    | inr ?m => 
      inr (of_MSymmetry of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_SymmetricG: argument is not reducible to a [SymmetricG] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  (* | _ => 
    Control.throw_invalid_argument 
      (String.app "of_SymmetricG: error with argument " (to_string (of_constr c))) *)
  end. *)


Ltac2 of_MAutonomous (of_n : constr -> 'n) (c : constr) : 'n btree Autonomous :=
  mk_of "of_MAutonomous" "MAutonomous" (let rec go c :=
    lazy_match! c with
    | msymmetric_inl ?m => 
      inl (of_MSymmetric of_n m)
    | inl ?m => 
      inl (of_MSymmetric of_n m)
    | mautonomy_inr ?m => 
      inr (of_MAutonomy of_n m)
    | inr ?m => 
      inr (of_MAutonomy of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Autonomous: argument is not reducible to a [Autonomous] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Autonomous: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 of_MFrobenius (of_n : constr -> 'n) (c : constr) : 'n btree Frobenius :=
  mk_of "of_MFrobenius" "MFrobenius" (let rec go c :=
    lazy_match! c with
    | mautonomous_inl ?m => 
      inl (of_MAutonomous of_n m)
    | inl ?m => 
      inl (of_MAutonomous of_n m)
    | mfrobenial_inr ?m => 
      inr (of_MFrobenial of_n m)
    | inr ?m => 
      inr (of_MFrobenial of_n m)
    end in go) c.
  (* match! c with
  | ?m => go m
  | _ => 
    (* let c' := Std.eval_red c in 
    if Constr.equal c' c then  *)
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app "of_Frobenius: argument is not reducible to a [Frobenius] constant: " (to_string (of_constr c)))
      else go c'
    (* else go c' *)
  | _ => 
    Control.throw_invalid_argument 
      (String.app "of_Frobenius: error with argument " (to_string (of_constr c)))
  end. *)

Ltac2 to_MMonoidal (to_n : 'n -> constr) (m : 'n btree Monoidal) : constr :=
  match m with
  | Associator n m o => 
    let n' := to_btree to_n n in 
    let m' := to_btree to_n m in 
    let o' := to_btree to_n o in 
    '(MAssociator $n' $m' $o')
  | InvAssociator n m o => 
    let n' := to_btree to_n n in 
    let m' := to_btree to_n m in 
    let o' := to_btree to_n o in 
    '(MInvAssociator $n' $m' $o')
  | LUnit n => 
    let n' := to_btree to_n n in 
    '(MLUnit $n')
  | InvLUnit n => 
    let n' := to_btree to_n n in 
    '(MInvLUnit $n')
  | RUnit n => 
    let n' := to_btree to_n n in 
    '(MRUnit $n')
  | InvRUnit n => 
    let n' := to_btree to_n n in 
    '(MInvRUnit $n')
  end.

Ltac2 to_MSymmetry (to_n : 'n -> constr) (m : 'n btree Symmetry) : constr :=
  match m with
  | Swap n m => 
    let n' := to_btree to_n n in 
    let m' := to_btree to_n m in 
    '(MSwap $n' $m')
  end.

Ltac2 to_MAutonomy (to_n : 'n -> constr) (m : 'n btree Autonomy) : constr :=
  match m with
  | Cup n => 
    let n' := to_btree to_n n in 
    '(MCup $n')
  | Cap n => 
    let n' := to_btree to_n n in 
    '(MCap $n')
  end.

Ltac2 to_MFrobenial (to_n : 'n -> constr) (m : 'n btree Frobenial) : constr :=
  match m with
  | Delta k n m => 
    let k' := to_btree to_n k in 
    let n' := to_nat n in 
    let m' := to_nat m in 
    '(MDelta $k' $n' $m')
  end.

Ltac2 to_MSymmetric (to_n : 'n -> constr) (m : 'n btree SymmetricG) : constr :=
  sum_elim (to_MMonoidal to_n) (to_MSymmetry to_n) m.

Ltac2 to_MAutonomous (to_n : 'n -> constr) (m : 'n btree Autonomous) : constr :=
  sum_elim (to_MSymmetric to_n) (to_MAutonomy to_n) m.

Ltac2 to_MFrobenius (to_n : 'n -> constr) (m : 'n btree Frobenius) : constr :=
  sum_elim (to_MAutonomous to_n) (to_MFrobenial to_n) m.


Ltac2 to_MPRO (to_n : 'n -> constr) (to_s : 's -> constr) (to_t : 't -> constr) :
  ('n btree, 's, 't) PRO -> constr :=
  let rec go p :=
    match p with
    | Pid n =>
      let cn := to_btree to_n n in
      '(Mid $cn)
    | Pcompose l r =>
      let cl := go l with cr := go r in
      '(Mcompose $cl $cr)
    | Pstack l r =>
      let cl := go l with cr := go r in
      '(Mstack $cl $cr)
    | Pstruct n m s =>
      let cn := to_btree to_n n with cm := to_btree to_n m with cs := to_s s in
      '(Mstruct $cn $cm $cs)
    | Pgen n m t =>
      let cn := to_btree to_n n with cm := to_btree to_n m with ct := to_t t in
      '(Mgen $cn $cm $ct)
    end
  in go.


(* FIXME: Move, rewrite with mk_of? *)
Ltac2 of_nat_sum_expr (c : constr) : constr btree :=
  let (ns, b) := parse_nat_btree [] c in 
  btree_map (Option.map_default (List.nth ns) '(1:>nat)) b.

End CC.


Ltac2 map_Monoidal_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Monoidal) : 'st * 'm Monoidal :=
  match m with
  | Associator n m o =>
    let (st, n') := f st n in
    let (st, m') := f st m in
    let (st, o') := f st o in 
    (st, Associator n' m' o')
  | InvAssociator n m o =>
    let (st, n') := f st n in
    let (st, m') := f st m in
    let (st, o') := f st o in 
    (st, InvAssociator n' m' o')
  | LUnit n =>
    let (st, n') := f st n in
    (st, LUnit n')
  | InvLUnit n =>
    let (st, n') := f st n in
    (st, InvLUnit n')
  | RUnit n =>
    let (st, n') := f st n in
    (st, RUnit n')
  | InvRUnit n =>
    let (st, n') := f st n in
    (st, InvRUnit n')
  end.

Ltac2 map_Symmetry_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Symmetry) : 'st * 'm Symmetry :=
  match m with
  | Swap n m => 
    let (st, n') := f st n in
    let (st, m') := f st m in
    (st, Swap n' m')
  end.

Ltac2 map_Autonomy_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Autonomy) : 'st * 'm Autonomy :=
  match m with
  | Cup n => 
    let (st, n') := f st n in
    (st, Cup n')
  | Cap n => 
    let (st, n') := f st n in
    (st, Cap n')
  end.

Ltac2 map_Frobenial_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Frobenial) : 'st * 'm Frobenial :=
  match m with
  | Delta k n m =>
    let (st, k') := f st k in
    (st, Delta k' n m)
  end.

Ltac2 map_sum_with (f : 'st -> 'n -> 'st * 'n') (g : 'st -> 'm -> 'st * 'm') 
  (st : 'st) :
  ('n, 'm) Sum -> 'st * ('n', 'm') Sum := 
  sum_elim (fun n => let (st, n') := f st n in (st, inl n'))
    (fun n => let (st, n') := g st n in (st, inr n')).

Ltac2 map_SymmetricG_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n SymmetricG) : 'st * 'm SymmetricG :=
  map_sum_with (map_Monoidal_with f) (map_Symmetry_with f) st m.

Ltac2 map_Autonomous_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Autonomous) : 'st * 'm Autonomous :=
  map_sum_with (map_SymmetricG_with f) (map_Autonomy_with f) st m.

Ltac2 map_Frobenius_with (f : 'st -> 'n -> 'st * 'm) 
  (st : 'st) (m : 'n Frobenius) : 'st * 'm Frobenius :=
  map_sum_with (map_Autonomous_with f) (map_Frobenial_with f) st m.


Ltac2 map_Monoidal (f : 'n -> 'm) 
  (m : 'n Monoidal) : 'm Monoidal :=
  match m with
  | Associator n m o =>
    let n' := f n in
    let m' := f m in
    let o' := f o in 
    Associator n' m' o'
  | InvAssociator n m o =>
    let n' := f n in
    let m' := f m in
    let o' := f o in 
    InvAssociator n' m' o'
  | LUnit n =>
    let n' := f n in
    LUnit n'
  | InvLUnit n =>
    let n' := f n in
    InvLUnit n'
  | RUnit n =>
    let n' := f n in
    RUnit n'
  | InvRUnit n =>
    let n' := f n in
    InvRUnit n'
  end.

Ltac2 map_Symmetry (f : 'n -> 'm) 
  (m : 'n Symmetry) : 'm Symmetry :=
  match m with
  | Swap n m => 
    let n' := f n in
    let m' := f m in
    Swap n' m'
  end.

Ltac2 map_Autonomy (f : 'n -> 'm) 
  (m : 'n Autonomy) : 'm Autonomy :=
  match m with
  | Cup n => 
    let n' := f n in
    Cup n'
  | Cap n => 
    let n' := f n in
    Cap n'
  end.

Ltac2 map_Frobenial (f : 'n -> 'm) 
  (m : 'n Frobenial) : 'm Frobenial :=
  match m with
  | Delta k n m =>
    let k' := f k in
    Delta k' n m
  end.

Ltac2 map_SymmetricG (f : 'n -> 'm) 
  (m : 'n SymmetricG) : 'm SymmetricG :=
  sum_map (map_Monoidal f) (map_Symmetry f) m.

Ltac2 map_Autonomous (f : 'n -> 'm) 
  (m : 'n Autonomous) : 'm Autonomous :=
  sum_map (map_SymmetricG f) (map_Autonomy f) m.

Ltac2 map_Frobenius (f : 'n -> 'm) 
  (m : 'n Frobenius) : 'm Frobenius :=
  sum_map (map_Autonomous f) (map_Frobenial f) m.


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

Import Props AbstractTensorQuote.

Ltac2 mk_MPRO_of_PRO_Monoidal () := 
  match! goal with
  | [|- MPRO_of_PRO (Struct:=Monoidal) (T:=?cT) (interp_discrete_hg_inhab ?cts) _ ?cp] =>
    let p := CC.of_PRO id (CC.of_Monoidal id) id cp in 
    let ts := CC.of_evar_ended_list id cts in 
    let (ts, pi) := posify_MPRO_sizes (map_Monoidal_with parse_nat_btree_to_pos) ts p in
    let cmi := CC.to_MPRO CC.to_pos (CC.to_MMonoidal CC.to_pos) id pi in 
    let cts := CC.extend_evar_ended_list ts cts in 
    refine '(mk_MPRO_of_PRO (MStruct:=@MMonoidal positive) (Struct:=Monoidal)
      (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi)
  end.


Ltac2 mk_MPRO_of_PRO_SymmetricG () := 
  match! goal with
  | [|- MPRO_of_PRO (Struct:=SymmetricG) (T:=?cT) (interp_discrete_hg_inhab ?cts) _ ?cp] =>
    let p := CC.of_PRO id (CC.of_SymmetricG id) id cp in 
    let ts := CC.of_evar_ended_list id cts in 
    let (ts, pi) := posify_MPRO_sizes (map_SymmetricG_with parse_nat_btree_to_pos) ts p in
    let cmi := CC.to_MPRO CC.to_pos (CC.to_MSymmetric CC.to_pos) id pi in 
    let cts := CC.extend_evar_ended_list ts cts in 
    refine '(mk_MPRO_of_PRO (MStruct:=@MSymmetric positive) (Struct:=SymmetricG)
      (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi)
  end.

Ltac2 mk_MPRO_of_PRO_Autonomous () := 
  match! goal with
  | [|- MPRO_of_PRO (Struct:=Autonomous) (T:=?cT) (interp_discrete_hg_inhab ?cts) _ ?cp] =>
    let p := CC.of_PRO id (CC.of_Autonomous id) id cp in 
    let ts := CC.of_evar_ended_list id cts in 
    let (ts, pi) := posify_MPRO_sizes (map_Autonomous_with parse_nat_btree_to_pos) ts p in
    let cmi := CC.to_MPRO CC.to_pos (CC.to_MAutonomous CC.to_pos) id pi in 
    let cts := CC.extend_evar_ended_list ts cts in 
    refine '(mk_MPRO_of_PRO (MStruct:=@MAutonomous positive) (Struct:=Autonomous)
      (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi)
  end.

Ltac2 mk_MPRO_of_PRO_Frobenius () := 
  match! goal with
  | [|- MPRO_of_PRO (Struct:=Frobenius) (T:=?cT) (interp_discrete_hg_inhab ?cts) _ ?cp] =>
    let p := CC.of_PRO id (CC.of_Frobenius id) id cp in 
    let ts := CC.of_evar_ended_list id cts in 
    let (ts, pi) := posify_MPRO_sizes (map_Frobenius_with parse_nat_btree_to_pos) ts p in
    let cmi := CC.to_MPRO CC.to_pos (CC.to_MFrobenius CC.to_pos) id pi in 
    let cts := CC.extend_evar_ended_list ts cts in 
    refine '(mk_MPRO_of_PRO (MStruct:=@MFrobenius positive) (Struct:=Frobenius)
      (T:=$cT) (interp_discrete_hg_inhab $cts) $cmi)
  end.

#[global] Hint Extern 0 
  (MPRO_of_PRO (Struct:=Monoidal) _ _ _) => 
  ltac2:(mk_MPRO_of_PRO_Monoidal()) : typeclass_instances.

#[global] Hint Extern 0 
  (MPRO_of_PRO (Struct:=SymmetricG) _ _ _) => 
  ltac2:(mk_MPRO_of_PRO_SymmetricG()) : typeclass_instances.

#[global] Hint Extern 0 
  (MPRO_of_PRO (Struct:=Autonomous) _ _ _) => 
  ltac2:(mk_MPRO_of_PRO_Autonomous()) : typeclass_instances.

#[global] Hint Extern 0 
  (MPRO_of_PRO (Struct:=Frobenius) _ _ _) => 
  ltac2:(mk_MPRO_of_PRO_Frobenius()) : typeclass_instances.
(* 
Goal True.
eassert (MPRO_of_PRO (Struct:=Frobenius) (T:=bool)
  (interp_discrete_hg_inhab _) _ (Pgen 1 1 true)).
  apply _.
  mk_MPRO_of_PRO_Monoidal().
  

    let pi := map_PRO id id (fun x => CC.to_pos (Int.add x 1)) pi in 
    let (_, _, cpi) := CC.to_PRO_safe struct_T '(positive) id id id pi in
    let cts := CC.extend_evar_ended_list ts' cts in 
    Std.unify cqp cpi;
    refine '(mk_MPRO_of_PRO (MStruct:=@MMonoidal positive) 
      (T:=positive) (T':=$t_T) (interp_discrete_hg_inhab $cts) $cpi $cp _);
    reflexivity *)



