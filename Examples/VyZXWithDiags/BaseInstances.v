From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
Import Props stdpp.vector.




(* First, we must define the data assocated to generators. In our case,
  we use [option (bool * R + C)] with [None] being the hadamard box,
  [Some (inl (false, α))] being a Z spider with phase [α],
  [Some (inl (true, α))] being a X spider with phase [α], and
  [Some (inr c)] being a constant gadget with value [c]. *)
Definition ZXCVERT := option (bool * R + C).

(* We must show the type of generators is nonempty *)
#[export] Instance ZXCVERT_inhab : Inhabited ZXCVERT := populate None.

(* We define the natural equivalence relation on [ZXCVERT], with phases
  taken mod [2*PI], and show it is in fact an equivalence relation. *)
#[export] Instance ZXCVERT_equiv : Equiv ZXCVERT :=
  option_Forall2 (sum_relation (prod_relation eq (Rmodeq (2*PI))) eq).

#[export] Instance ZXCVERT_equiv_equivalence : Equivalence (≡@{ZXCVERT}).
Proof. apply _. Qed.

(* We give an interpretation of our generators as dimensionless tensors (to [C]),
  using the definitions in [ZXCore.v] *)
Definition ZXCCALC_tensor (x : ZXCVERT) : DimensionlessTensor bool :=
  match x with
  | None => fun n m => (tensor_to_dimensionless (@h_stack n)) n m
  | Some (inl (false, r))  => fun n m => @zsp n m r
  | Some (inl (true, r)) => fun n m => @xsp n m r
  | Some (inr c) => fun n m v w => c
  end.

#[global] Arguments ZXCCALC_tensor !_ /.

(* We show this tensor interpretation respects our equivalence relation;
  this is basically just applying instances from [ZXCore.v]. *)
#[export] Instance ZXCCALC_tensor_proper :
  Proper ((≡) ==> (≡)) ZXCCALC_tensor.
Proof.
  intros x x' Heq.
  induction Heq as [x y Heq|]; [|done..].
  induction Heq as [ [ [] x] [c y] [ [= <-] Heq]|? ? <-]; [..|done];
  cbn;
  intros n m;
  now rewrite Heq.
Qed.

(* Then, we give the [TensorLike] instance defining the tensor associated
  to a [ZXCVERT]. *)
#[export] Instance ZXCCALC : TensorLike C bool ZXCVERT := {
  interpretTensor := ZXCCALC_tensor;
}.


(* We declare the equivalence relation assocaited to ZX-diagrams *)
#[local] Instance ZX_equiv {n m} : Equiv (ZX n m) := proportional_by_1.

#[program] Instance ZX_tensorlike : StrictTensorLike C bool ZX := {
  strictInterpretTensor n m zx := ZX_tensor_semantics zx;
}.
Next Obligation.
  intros n m zx zx' Hzx.
  apply matrix_of_tensor_inj.
  rewrite 2 ZX_tensor_semantics_correct.
  now rewrite Hzx.
Qed.

Definition ZXCVERT_to_ZX
  n m (c : ZXCVERT) : option (ZX n m) :=
  match c with
  | None => match decide (n = m) with
    | left Heq => Some (cast _ _ Heq eq_refl (n_stack1 m Box))
    | right _ => None
    end
  | Some (inl (true, r)) => Some (X n m r)
  | Some (inl (false, r)) => Some (Z n m r)
  | Some (inr c) => match n, m with
    | 0, 0 => Some (zx_of_const c)
    | _, _ => None
    end
  end.

#[export] Instance ZX_tensorable : TensorableDiagram ZXCVERT ZX :=
  ZXCVERT_to_ZX.

#[export] Instance ZX_compositional : Compositional ZX := {
  Did n := n_wire n;
  Dcompose _ _ _ zx zx' := zx ⟷ zx';
  Dstack _ _ _ _ zx zx' := zx ↕ zx';
}.

Definition Monoidal_to_ZX {n m} (p : Monoidal n m) : ZX n m :=
  cast n m (Monoidal_eq p) eq_refl (n_wire _).

Definition Symmetry_to_ZX {n m} (p : Symmetry n m) : ZX n m :=
  match p with
  | Swap n m => zx_comm n m
  end.


Definition SymmetricG_to_ZX {n m} (p : SymmetricG n m) : ZX n m :=
  match p with
  | inl p => Monoidal_to_ZX p
  | inr p => Symmetry_to_ZX p
  end.

Definition Autonomy_to_ZX {n m} (p : Autonomy n m) : ZX n m :=
  match p with
  | Cap 0 => ⦰
  | Cap 1 => ⊃
  | Cap n => n_cup n
  | Cup 0 => ⦰
  | Cup 1 => ⊂
  | Cup n => n_cap n
  end.

Definition Autonomous_to_ZX {n m} (p : Autonomous n m) : ZX n m :=
  match p with
  | inl p => SymmetricG_to_ZX p
  | inr p => Autonomy_to_ZX p
  end.

#[export] Instance ZX_Monoidal_structable : StructableDiagram Monoidal ZX :=
  fun _ _ => Monoidal_to_ZX.

#[export] Instance ZX_Symmetry_structable : StructableDiagram Symmetry ZX :=
  fun _ _ => Symmetry_to_ZX.

#[export] Instance ZX_Autonomy_structable : StructableDiagram Autonomy ZX :=
  fun _ _ => Autonomy_to_ZX.

#[export] Instance ZX_SymmetricG_structable : StructableDiagram SymmetricG ZX :=
  fun _ _ => SymmetricG_to_ZX.

#[export] Instance ZX_Autonomous_structable : StructableDiagram Autonomous ZX :=
  fun _ _ => Autonomous_to_ZX.

Local Instance ZX_abstract_symmetricG : AbstractProLike SymmetricG ZX := {}.

(*
Lemma zx_mul_comm_S_l n m : zx_mul_comm (S n) m ∝= K.

Lemma zx_mul_comm_transpose n m : ((zx_mul_comm n m) ⊤)%ZX ∝= zx_mul_comm m n.
Proof. *)



Lemma Monoidal_to_ZX_zxperm
  {n m} (p : Monoidal n m) : ZXperm (Monoidal_to_ZX p).
Proof.
  unfold Monoidal_to_ZX.
  auto_zxperm.
Qed.

Lemma Symmetry_to_ZX_zxperm
  {n m} (p : Symmetry n m) : ZXperm (Symmetry_to_ZX p).
Proof.
  induction p; cbn;
  auto_zxperm.
Qed.

#[export] Hint Resolve Monoidal_to_ZX_zxperm Symmetry_to_ZX_zxperm : zxperm_db.

Lemma zx_symmetricG_SPRO_to_diagram_zxperm
  {n m} (p : SPRO SymmetricG n m) : ZXperm (SPRO_to_diagram p).
Proof.
  induction p; cbn; [auto_zxperm..| |done].
  induction s; cbn; auto_zxperm.
Qed.

#[export] Hint Resolve zx_symmetricG_SPRO_to_diagram_zxperm : zxperm_db.



Definition Frobenial_to_ZX {n m} (p : Frobenial n m) : ZX n m :=
  match p with
  | Delta0 => Z 0 0 0
  | Delta1 n m => Z n m 0
  | Delta k n m => ZX_copy k (Z n m 0)
  end.

Definition Frobenius_to_ZX {n m} (p : Frobenius n m) : ZX n m :=
  match p with
  | inl p => Autonomous_to_ZX p
  | inr p => Frobenial_to_ZX p
  end.

#[export] Instance ZX_Frobenial_structable : StructableDiagram Frobenial ZX :=
  fun _ _ => Frobenial_to_ZX.

#[export] Instance ZX_Frobenius_structable : StructableDiagram Frobenius ZX :=
  fun _ _ => Frobenius_to_ZX.



#[export, program] Instance ZX_Monoidal_lawstructable :
  LawfulStructableDiagram C bool Monoidal ZX.
Next Obligation.
  intros n m sm.
  cbn.
  unfold ofStruct, ZX_Monoidal_structable; cbn.
  unfold Monoidal_to_ZX.
  etransitivity; [|symmetry; apply (Monoidal_semantics sm)].
  destruct (Monoidal_eq sm).
  cbn.
  rewrite perm_tensor_id' by now intros; apply fcast_id.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct.
  now rewrite n_wire_semantics, matrix_of_tensor_delta.
Qed.

#[export, program] Instance ZX_Symmetry_lawstructable :
  LawfulStructableDiagram C bool Symmetry ZX.
Next Obligation.
  intros n m ss.
  cbn.
  induction ss as [n m].
  cbn.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct.
  rewrite <- tensor_of_matrix_kron_comm.
  rewrite matrix_of_tensor_of_matrix.
  now rewrite zx_comm_semantics.
Qed.

#[export, program] Instance ZX_Autonomy_lawstructable :
  LawfulStructableDiagram C bool Autonomy ZX.
Next Obligation.
  intros n m sa.
  induction sa as [[|[|n]]|[|[|n]]]; cbn -[n_cup n_cap].
  - intros v w.
    inv_all_vec_fin.
    done.
  - done.
  - unfold n_cap.
    apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    rewrite semantics_transpose_comm.
    apply tensor_of_matrix_inj'.
    rewrite tensor_of_matrix_transpose.
    intros v w Hv Hw.
    etransitivity; [apply (tensor_of_matrix_n_cup_semantics (S (S n)) w v); done|].
    rewrite tensor_of_matrix_of_tensor.
    done.
  - intros v w.
    inv_all_vec_fin.
    done.
  - done.
  - apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    apply tensor_of_matrix_inj'.
    etransitivity; [apply (tensor_of_matrix_n_cup_semantics (S (S n)))|].
    rewrite tensor_of_matrix_of_tensor.
    done.
Qed.

#[export, program] Instance ZX_Frobenial_lawstructable :
  LawfulStructableDiagram C bool Frobenial ZX.
Next Obligation.
  intros n m s.
  induction s as [|n m|k n m];
  [now cbn; try rewrite <- ZX_tensor_semantics_Z_delta_spider..|].
  cbn -[ZX_copy].
  rewrite ZX_tensor_semantics_ZX_copy.
  unfold delta_spider_tensor_bundled.
  apply copy_tensor_mor.
  apply ZX_tensor_semantics_Z_delta_spider.
Qed.

#[export, program] Instance ZX_SymmetricG_lawstructable :
  LawfulStructableDiagram C bool SymmetricG ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
Qed.

#[export, program] Instance ZX_Autonomous_lawstructable :
  LawfulStructableDiagram C bool Autonomous ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
Qed.

#[export, program] Instance ZX_Frobenius_lawstructable :
  LawfulStructableDiagram C bool Frobenius ZX.
Next Obligation.
  intros n m ss.
  destruct ss as [ss|ss]; apply (ofStruct_correct _ _ ss).
Qed.






Notation ZXDVERT := (WithDiagrams ZXCVERT ZX).

#[export] Instance ZXDCALC : TensorLike C bool ZXDVERT :=
  withDiagrams_tensorLike ZXCVERT ZXCCALC ZX.


#[program] Instance ZX_lawtensorable
  : LawfulTensorableDiagram C bool (TensT := ZXDCALC)
    _ ZX (StructD := _).
Next Obligation.
  intros n m zxc zxc' Heq.
  induction Heq as [zxc zxc' Heq|d d' Heq]. 2:{
    cbn.
    now f_equiv.
  }
  induction Heq as [z_c z_c' Heq|]; [|done].
  induction Heq as [z z' Heq|c c' <-]; [|done].
  destruct z as [is_x r], z' as [is_x' r'].
  destruct Heq as [[= <-] Heq].
  cbn.
  destruct is_x; f_equiv; [apply X_Rmodeq_2PI|apply Z_Rmodeq_2PI]; done.
Qed.
Next Obligation.
  intros n m [[[([], r)|c]|]|bd] d.
  - cbn.
    intros [= <-].
    done.
  - cbn.
    intros [= <-].
    done.
  - cbn.
    case_match; [|done].
    case_match; [|done].
    intros [= <-].
    subst.
    apply matrix_of_tensor_inj.
    rewrite ZX_tensor_semantics_correct.
    rewrite zx_of_const_semantics.
    intros v w Hv Hw.
    cbn in *.
    replace v with 0 by lia.
    replace w with 0 by lia.
    unfold scale.
    cbn.
    apply Cmult_1_r.
  - cbn.
    unfold ZXCCALC_tensor.
    case_decide; [|done].
    subst m.
    rewrite cast_id_eq.
    intros [= <-].
    unfold ZXCCALC_tensor.
    cbn.
    apply matrix_of_tensor_inj.
    rewrite tensor_to_dimensionless_refl.
    rewrite matrix_of_tensor_h_stack.
    rewrite ZX_tensor_semantics_correct.
    rewrite n_stack1_semantics.
    done.
  - cbn.
    intros ->.
    done.
Qed.

#[program] Instance ZX_lawcompositional : LawfulCompositional C bool ZX.
Next Obligation.
  intros n.
  cbn.
  apply matrix_of_tensor_inj.
  rewrite ZX_tensor_semantics_correct, n_wire_semantics, matrix_of_tensor_delta.
  done.
Qed.
Next Obligation.
  done.
Qed.
Next Obligation.
  done.
Qed.
Next Obligation.
  intros n m zx zx' Hzx.
  prep_matrix_equivalence.
  apply tensor_of_matrix_inj'.
  rewrite <- 2 ZX_tensor_semantics_correct.
  rewrite 2 tensor_of_matrix_of_tensor.
  apply Hzx.
Qed.


#[export] Instance ZX_SymmetricG_ProLike : ProLike SymmetricG ZXDVERT ZX := {
  PL_tensD := _
}.

#[export] Instance ZX_Autonomous_ProLike : ProLike Autonomous ZXDVERT ZX := {
  PL_tensD := _
}.

#[export] Instance ZX_Frobenius_ProLike : ProLike Frobenius ZXDVERT ZX := {
  PL_tensD := _
}.

#[export] Instance ZX_SymmetricG_lawpro :
  LawfulProLike C bool SymmetricG ZXDVERT ZX
    (ProD:=ZX_SymmetricG_ProLike)
    (TensT := ZXDCALC):= {}.


#[export] Instance ZX_Autonomous_lawpro :
  LawfulProLike C bool Autonomous ZXDVERT ZX
    (ProD:=ZX_Autonomous_ProLike)
    (TensT := ZXDCALC):= {}.

#[export] Instance ZX_Frobenius_lawpro :
  LawfulProLike C bool Frobenius ZXDVERT ZX
    (ProD:=ZX_Frobenius_ProLike)
    (TensT := ZXDCALC):= {}.





(* FIXME: Move *)
Require Import Ltac2.Notations.
From TensorRocq Require SizedProQuote.
#[export] Hint Extern 0 (DiagramQuote (n_stack ?n _) _) =>
  ltac2:(
    lazy_match! goal with
    | [|- DiagramQuote (n_stack ?n _) _] =>
      if SizedProQuote.CC.is_nat_const n then
        ltac1:(cbn [n_stack])
      else
        Control.zero Init.No_value
    end
  ) : typeclass_instances.

#[export] Hint Extern 0 (DiagramQuote (n_stack1 ?n _) _) =>
  ltac2:(
    lazy_match! goal with
    | [|- DiagramQuote (n_stack1 ?n _) _] =>
      if SizedProQuote.CC.is_nat_const n then
        ltac1:(cbn [n_stack1])
      else
        Control.zero Init.No_value
    end
  ) : typeclass_instances.
