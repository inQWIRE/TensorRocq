From TensorRocq Require Import BW BWQuote.
From Ltac2 Require Import Ltac2.
From TensorRocq Require Import Ltac2.ConstrExtra.
From TensorRocq Require Import Props.Prop.Prop.
From TensorRocq Require Import SizedProp.

From TensorRocq Require Import BWQuote.


Ltac2 denote_opt_int_btree (b : int option btree) : constr :=
  CC.to_btree (CC.to_option CC.to_nat) b.

Ltac2 quote_Monoidal (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | @Id ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MId _ $cnt))
    | @Associator ?n ?m ?o => 
      let (ns, nt) := parse_nat_btree ns n in 
      let (ns, mt) := parse_nat_btree ns m in 
      let (ns, ot) := parse_nat_btree ns o in 
      let cnt := denote_opt_int_btree nt with
        cmt := denote_opt_int_btree mt with
        cot := denote_opt_int_btree ot in
      (ns, '(@MAssociator _ $cnt $cmt $cot))
    | @InvAssociator ?n ?m ?o => 
      let (ns, nt) := parse_nat_btree ns n in 
      let (ns, mt) := parse_nat_btree ns m in 
      let (ns, ot) := parse_nat_btree ns o in 
      let cnt := denote_opt_int_btree nt with
        cmt := denote_opt_int_btree mt with
        cot := denote_opt_int_btree ot in
      (ns, '(@MInvAssociator _ $cnt $cmt $cot))
    | @LUnit ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MLUnit _ $cnt))
    | @InvLUnit ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MInvLUnit _ $cnt))
    | @RUnit ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MLUnit _ $cnt))
    | @InvRUnit ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MInvLUnit _ $cnt))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          "quote_Monoidal: argument is not reducible to a [Monoidal] constant"
      else go ns c'
    else go ns c'
  end.


Ltac2 quote_Symmetry (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | @Swap ?n ?m => 
      let (ns, nt) := parse_nat_btree ns n in 
      let (ns, mt) := parse_nat_btree ns m in
      let cnt := denote_opt_int_btree nt with
        cmt := denote_opt_int_btree mt in
      (ns, '(@MSwap _ $cnt $cmt))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          "quote_Symmetry: argument is not reducible to a [Symmetry] constant"
      else go ns c'
    else go ns c'
  end.


Ltac2 quote_Autonomy (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | @Cup ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MCup _ $cnt))
    | @Cap ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MCap _ $cnt))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          "quote_Autonomy: argument is not reducible to a [Autonomy] constant"
      else go ns c'
    else go ns c'
  end.


Ltac2 quote_SCartesian (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | @Delta ?n ?m => 
      let (ns, nt) := parse_nat_btree ns n in 
      let (ns, mt) := parse_nat_btree ns m in
      let cnt := denote_opt_int_btree nt with
        cmt := denote_opt_int_btree mt in
      (ns, '(@MDelta _ $cnt $cmt))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          "quote_SCartesian: argument is not reducible to a [SCartesian] constant"
      else go ns c'
    else go ns c'
  end.



Ltac2 quote_Symmetric (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | monoidal_inl ?m => 
      let (ns, m') := quote_Monoidal ns m in 
      (ns, '(mmonoidal_inl $m'))
    | inl ?m => 
      let (ns, m') := quote_Monoidal ns m in 
      (ns, '(mmonoidal_inl $m'))
    | symmetry_inr ?m => 
      let (ns, m') := quote_Symmetry ns m in 
      (ns, '(msymmetry_inr $m'))
    | inr ?m => 
      let (ns, m') := quote_Symmetry ns m in 
      (ns, '(msymmetry_inr $m'))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          "quote_Symmetric: argument is not reducible to a [Symmetric] constant"
      else go ns c'
    else go ns c'
  end.


Ltac2 quote_Autonomous (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | symmetric_inl ?m => 
      let (ns, m') := quote_Symmetric ns m in 
      (ns, '(msymmetric_inl $m'))
    | inl ?m => 
      let (ns, m') := quote_Symmetric ns m in 
      (ns, '(msymmetric_inl $m'))
    | autonomy_inr ?m => 
      let (ns, m') := quote_Autonomy ns m in 
      (ns, '(mautonomy_inr $m'))
    | inr ?m => 
      let (ns, m') := quote_Autonomy ns m in 
      (ns, '(mautonomy_inr $m'))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app 
            "quote_Autonomous: argument is not reducible to a [Autonomous] constant"
            (Message.to_string (Message.of_constr c)))
      else go ns c'
    else go ns c'
  end.


Ltac2 quote_Cartesian (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | autonomous_inl ?m => 
      let (ns, m') := quote_Autonomous ns m in 
      (ns, '(mautonomous_inl $m'))
    | inl ?m => 
      let (ns, m') := quote_Autonomous ns m in 
      (ns, '(mautonomous_inl $m'))
    | scartesian_inr ?m => 
      let (ns, m') := quote_SCartesian ns m in 
      (ns, '(mscartesian_inr $m'))
    | inr ?m => 
      let (ns, m') := quote_SCartesian ns m in 
      (ns, '(mscartesian_inr $m'))
    end in 
  match! c with
  | ?m => go ns m
  | _ => 
    let c' := Std.eval_red c in 
    if Constr.equal c' c then 
      let c' := Std.eval_hnf c in 
      if Constr.equal c' c then 
        Control.throw_invalid_argument 
          (String.app 
            "quote_Cartesian: argument is not reducible to a [Cartesian] constant"
            (Message.to_string (Message.of_constr c)))
      else go ns c'
    else go ns c'
  end.
