From TensorRocq Require Import BW BWQuote.
From Ltac2 Require Import Ltac2.
From TensorRocq Require Import Ltac2.ConstrExtra.
From TensorRocq Require Import Props.
From TensorRocq Require Import SizedProps.

From TensorRocq Require Import BWQuote.


Ltac2 denote_opt_int_btree (b : int option btree) : constr :=
  CC.to_btree (CC.to_option CC.to_nat) b.

Ltac2 quote_Monoidal (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    (* | @Id ?n => 
      let (ns, nt) := parse_nat_btree ns n in 
      let cnt := denote_opt_int_btree nt in
      (ns, '(@MId _ $cnt)) *)
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


Ltac2 quote_Frobenial (ns : constr list) (c : constr) : constr list * constr :=
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
          "quote_Frobenial: argument is not reducible to a [Frobenial] constant"
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


Ltac2 quote_Frobenius (ns : constr list) (c : constr) : constr list * constr :=
  let rec go ns c :=
    match! c with
    | autonomous_inl ?m => 
      let (ns, m') := quote_Autonomous ns m in 
      (ns, '(mautonomous_inl $m'))
    | inl ?m => 
      let (ns, m') := quote_Autonomous ns m in 
      (ns, '(mautonomous_inl $m'))
    | Frobenial_inr ?m => 
      let (ns, m') := quote_Frobenial ns m in 
      (ns, '(mFrobenial_inr $m'))
    | inr ?m => 
      let (ns, m') := quote_Frobenial ns m in 
      (ns, '(mFrobenial_inr $m'))
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
            "quote_Frobenius: argument is not reducible to a [Frobenius] constant"
            (Message.to_string (Message.of_constr c)))
      else go ns c'
    else go ns c'
  end.



(* FIXME: Move *)
Fixpoint gbpath_to_MPRO {A T} {M : Mor (btree A)} {a b} (p : gbpath M a b) : 
  MPRO M T a b :=
  match p with
  | brefl => Mid _
  | bgen m => Mstruct _ _ m
  | bprop l r => gbpath_to_MPRO l * gbpath_to_MPRO r
  | btrans l r => gbpath_to_MPRO l ;; gbpath_to_MPRO r
  end%mpro.

Class StructuralMMorphism {A} (M : Mor (btree A)) (a b : btree A) :=
  structuralMMor : forall {T}, MPRO M T a b.

Definition bmonoidal_MMonoidal {A} {a b : btree A} (p : bmonoidal a b) : MMonoidal a b :=
  match p with
  | bassoc => MAssociator
  | bassoci => MInvAssociator
  | blunit => MLUnit
  | bluniti => MInvLUnit
  | brunit => MRUnit
  | bruniti => MInvRUnit
  end.


Definition bsymmetric_MSymmetric {A} {a b : btree A} (p : bsymmetric a b) : MSymmetric a b :=
  match p with
  | bmonoidal_bsymmetric p => bmonoidal_MMonoidal p
  | bsymm => MSwap _ _
  end.


Definition bautonomous_MAutonomous {A} {a b : btree A} (p : bautonomous a b) : MAutonomous a b :=
  match p with
  | bsymmetric_bautonomous p => bsymmetric_MSymmetric p
  | bcup => MCup _
  | bcap => MCap _
  end.


Definition structuralMMorphism_monoidal `{EqDecision A} {a b : btree A} :
  is_Some (may_bpath a b) -> StructuralMMorphism MMonoidal a b :=
  fun Hab T => gbpath_to_MPRO (gbpath_map (@bmonoidal_MMonoidal A) (is_Some_proj Hab)).

Definition structuralMMorphism_symmetric `{EqDecision A} {a b : btree A} :
  is_Some (may_sbpath a b) -> StructuralMMorphism MSymmetric a b :=
  fun Hab T => gbpath_to_MPRO (gbpath_map (@bsymmetric_MSymmetric A) (is_Some_proj Hab)).

Definition structuralMMorphism_autonomous `{EqDecision A} {a b : btree A} :
  is_Some (may_abpath a b) -> StructuralMMorphism MAutonomous a b :=
  fun Hab T => gbpath_to_MPRO (gbpath_map (@bautonomous_MAutonomous A) (is_Some_proj Hab)).

Class StructuralMorphism (M : Mor nat) (a b : nat) :=
  structuralMor : forall {T}, PRO M T a b.

Definition structuralMMorphism_structuralMorphism {A} 
  (f : A -> nat) {M : Mor (btree A)} {M' : Mor nat}
    {EqM : forall a b, Equiv (M a b)}
    {EqM' : forall a b, Equiv (M' a b)}
    {HM : InterpStruct M M'} (a b : btree A) :
  StructuralMMorphism M a b ->
  StructuralMorphism M' (btree_size f a) (btree_size f b) :=
  fun p T => MPRO_to_PRO f (p T).


#[export] Hint Extern 0 (StructuralMorphism Monoidal _ _) => 
  ltac2:(
    lazy_match! goal with
  | [ |- StructuralMorphism Monoidal ?a ?b ] => 
    let ns : constr list := [] in 
    let (ns, ta) := parse_nat_btree ns a in 
    let (ns, tb) := parse_nat_btree ns b in 
    let cta := CC.to_btree (CC.to_option CC.to_nat) ta in 
    let ctb := CC.to_btree (CC.to_option CC.to_nat) tb in 
    let cns := CC.mk_list ns in 
    refine '(structuralMMorphism_structuralMorphism
      (λ k : option nat, from_option (default 0 ∘ (fun i =>
        @lookup nat nat (list nat) list_lookup i $cns)) 1 k) (HM:=interpStructMonoidal)
      $cta $ctb _);
    refine '(@structuralMMorphism_monoidal _ (@option_eq_dec _ Nat.eq_dec) _ _ _);
    ltac1:(compute_done)
  end
  ) : typeclass_instances.

Import Props.

(* FIXME: Move *)
Definition interpStructSymmetric {A} : @InterpStruct A MSymmetric _ SymmetricG _:= _.
Definition interpStructAutonomous {A} : @InterpStruct A MAutonomous _ Autonomous _ := _.

#[export] Hint Extern 0 (StructuralMorphism SymmetricG _ _) => 
  ltac2:(
    lazy_match! goal with
  | [ |- StructuralMorphism SymmetricG ?a ?b ] => 
    let ns : constr list := [] in 
    let (ns, ta) := parse_nat_btree ns a in 
    let (ns, tb) := parse_nat_btree ns b in 
    let cta := CC.to_btree (CC.to_option CC.to_nat) ta in 
    let ctb := CC.to_btree (CC.to_option CC.to_nat) tb in 
    let cns := CC.mk_list ns in 
    refine '(structuralMMorphism_structuralMorphism
      (λ k : option nat, from_option (default 0 ∘ (fun i =>
        @lookup nat nat (list nat) list_lookup i $cns)) 1 k) (HM:=interpStructSymmetric)
      $cta $ctb _);
    refine '(@structuralMMorphism_symmetric _ (@option_eq_dec _ Nat.eq_dec) _ _ _);
    ltac1:(compute_done)
  end
  ) : typeclass_instances.


#[export] Hint Extern 0 (StructuralMorphism Autonomous _ _) => 
  ltac2:(
    lazy_match! goal with
  | [ |- StructuralMorphism Autonomous ?a ?b ] => 
    let ns : constr list := [] in 
    let (ns, ta) := parse_nat_btree ns a in 
    let (ns, tb) := parse_nat_btree ns b in 
    let cta := CC.to_btree (CC.to_option CC.to_nat) ta in 
    let ctb := CC.to_btree (CC.to_option CC.to_nat) tb in 
    let cns := CC.mk_list ns in 
    refine '(structuralMMorphism_structuralMorphism
      (λ k : option nat, from_option (default 0 ∘ (fun i =>
        @lookup nat nat (list nat) list_lookup i $cns)) 1 k) (HM:=interpStructAutonomous)
      $cta $ctb _);
    refine '(@structuralMMorphism_autonomous _ (@option_eq_dec _ Nat.eq_dec) _ _ _);
    ltac1:(compute_done)
  end
  ) : typeclass_instances.

Definition Pcompose_join_Monoidal (* {Struct : Mor nat} *) {T}
  {a b b' c : nat} (f : PRO Monoidal T a b) (g : PRO Monoidal T b' c)
  (Hb : StructuralMorphism Monoidal b b') : PRO Monoidal T a c :=
  f ;; Hb T ;; g.
(* 
Notation " f  ;;ₘ g " := (Pcompose_join_Monoidal f%pro g%pro _) (at level 100) : pro_scope.
 *)

Definition Pcompose_join {Struct : Mor nat} {T}
  {a b b' c : nat} (f : PRO Struct T a b) (g : PRO Struct T b' c)
  (Hb : StructuralMorphism Struct b b') : PRO Struct T a c :=
  f ;; Hb T ;; g.

Notation " f  ;;'@{ M } g " := (Pcompose_join (Struct:=M) f%pro g%pro _) (at level 100, only parsing) : pro_scope.
Notation " f  ;;' g " := (Pcompose_join f%pro g%pro _) (at level 100) : pro_scope.


(* #[global] Arguments substruct_refl /. *)

Definition Pcompose_join_sub (Struct : Mor nat) {Struct' : Mor nat} 
  {SubS : SubStruct Struct Struct'} {T}
  {a b b' c : nat} (f : PRO Struct' T a b) (g : PRO Struct' T b' c)
  (Hb : StructuralMorphism Struct b b') : PRO Struct' T a c :=
  f ;; map_PRO (fun _ _ => includeStruct) id (Hb T) ;; g.

Definition Pcompose_joinM {Struct : Mor nat} 
  {SubS : SubStruct Monoidal Struct} {T}
  {a b b' c : nat} (f : PRO Struct T a b) (g : PRO Struct T b' c)
  (Hb : StructuralMorphism Monoidal b b') : PRO Struct T a c :=
  f ;; map_PRO (fun _ _ => includeStruct) id (Hb T) ;; g.

Notation " f  ;;ₘ@{ M } g " := (Pcompose_joinM (Struct:=M) f%pro g%pro _) (at level 100, only parsing) : pro_scope.

Notation " f  ;;ₘ g " := (Pcompose_joinM f%pro g%pro _) (at level 100) : pro_scope.


(* Open Scope pro_scope.

Goal forall n m o : nat, True.
intros n m o.
Check Pgen (n + m) (n + m + o) true ;;ₘ@{Monoidal} Pgen (n + (m + o)) 0 false.
Check Pgen (n + m) (n + m + o) true ;;ₘ@{SymmetricG} Pgen (n + (m + o)) 0 false.
Check Pgen (n + m) (n + m + o) true ;;'@{SymmetricG} Pgen (n + (o + m)) 0 false. *)


(* Goal forall n m o, StructuralMorphism Autonomous (n + 0 + 1 + m + o + 1) (n + (o + 0 + m)).
Proof.
  apply _. *)

(* Goal forall n m o, StructuralMorphism Monoidal (n + 0 + m + o) (n + (m + 0 + o)).
Proof.
  Time apply _. *)




