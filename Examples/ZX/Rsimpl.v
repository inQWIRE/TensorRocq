Require Import Setoid Reals Lra Ring.
From QuantumLib Require Import RealAux.
From TensorRocqEx Require Import Rmodeq.

Ltac is_phase_const r :=
  is_var r || is_const r ||
  lazymatch r with
  | 0%R => idtac
  | PI => idtac
  | PI / 2 => idtac
  | if _ then _ else _ => idtac
  end.

Class Rsimpl (rin rout : R) :=
  rsimpl : rin = rout.

#[global] Hint Mode Rsimpl - - : typeclass_instances.

Ltac rsimpl_tac :=
  let r := lazymatch goal with
    |- Rsimpl ?r _ => constr:(r)
    end in
  tryif is_phase_const r then exact eq_refl else
  field_simplify r; exact eq_refl.

#[global] Hint Extern 0 (Rsimpl ?r _) =>
  rsimpl_tac : typeclass_instances.

Class Rsimpl_modeq_2PI (rin rout : R) :=
  rsimpl_modeq_2PI : rin =[mod 2 * PI] rout.

#[global] Hint Mode Rsimpl_modeq_2PI - - : typeclass_instances.

Lemma mk_Rsimpl_modeq_2PI rin rmid rout : 
  rin =[mod 2 * PI] rmid -> Rsimpl rmid rout ->
  Rsimpl_modeq_2PI rin rout.
Proof.
  intros Heq [= <-].
  apply Heq.
Qed.

Import QArith Qround.

Local Open Scope R_scope.

Ltac rsimpl_modeq_2PI_tac :=
  let get_lhs tac :=
    lazymatch goal with
    |- Rsimpl_modeq_2PI ?r _ => constr:(r)
    end in
  let r := get_lhs idtac in
  tryif is_phase_const r then exact (Rmodeq_refl (2 * PI) r) else
  field_simplify r;
  let r' := get_lhs idtac in
  lazymatch r' with
  | context Cr [- PI / IZR ?d] =>
    let n := eval vm_compute in (BinInt.Z.pred (2 * d)) in 
    let r'' := context Cr [IZR n * PI / IZR d] in
      apply (mk_Rsimpl_modeq_2PI r' r'' _);
      [exists (-1 : BinInt.Z); lra|]
  | context Cr [IZR ?n * PI / IZR ?d] =>
    let p := eval vm_compute in (Qfloor (Qdiv (n # xH) (d # xH))) in 
    let pdivmod2 := eval vm_compute in (BinInt.Z.div_eucl p 2) in
    let pdiv := lazymatch pdivmod2 with | (?pdiv, _) => constr:(pdiv) end in
    let pmod := lazymatch pdivmod2 with | (_, ?pmod) => constr:(pmod) end in
    let qres := eval vm_compute in 
      (Qred (Qplus (pmod # xH) (Qminus (Qdiv (n # xH) (d # xH)) (p # xH)))) in
    let n' := lazymatch qres with | ?n' # _ => constr:(n') end in 
    match qres with
    | ?n' # xH => 
      let r'' := context Cr [IZR n' * PI] in
      apply (mk_Rsimpl_modeq_2PI r' r'' _);
      [exists pdiv; lra|]
    | ?n' # ?d' =>
      let r'' := context Cr [IZR n' * PI / IZR (Zpos d')] in
      apply (mk_Rsimpl_modeq_2PI r' r'' _);
      [exists pdiv; lra|]
    end

  | context Cr [IZR ?p * PI] =>
    let pdivmod2 := eval vm_compute in (BinInt.Z.div_eucl p 2) in
    let pdiv := lazymatch pdivmod2 with | (?pdiv, _) => constr:(pdiv) end in
    let pmod := lazymatch pdivmod2 with | (_, ?pmod) => constr:(pmod) end in
    let r'' := context Cr [IZR pmod * PI] in
    apply (mk_Rsimpl_modeq_2PI r' r'' _);
    [exists pdiv; lra|]
  | context Cr [- PI] => 
    let r'':= context Cr [PI] in 
    lazymatch goal with
    |- Rsimpl_modeq_2PI _ ?s =>
      apply (mk_Rsimpl_modeq_2PI r' r'' _);
      [exists (-1 : Z); lra|]
    end
  | _ =>
    lazymatch goal with
    |- Rsimpl_modeq_2PI _ ?s =>
      exact (Rmodeq_refl (2 * PI) r')
    end
  end.
  (* let get_lhs tac :=
    lazymatch goal with
    |- Rsimpl_modeq_2PI ?r _ => constr:(r)
    end in
  let r := get_lhs idtac in
  ring_simplify r;
  let r' := get_lhs idtac in
  lazymatch r' with
  | context Cr [IZR ?p * PI] =>
    let pdivmod2 := eval vm_compute in (Z.div_eucl p 2) in
    let pdiv := lazymatch pdivmod2 with | (?pdiv, _) => constr:(pdiv) end in
    let pmod := lazymatch pdivmod2 with | (_, ?pmod) => constr:(pmod) end in
    let r'' := context Cr [IZR pmod * PI] in
    apply (mk_Rsimpl_modeq_2PI r' r'' _);
    [exists pdiv; lra|]
  | context Cr [- PI] => 
    let r'':= context Cr [PI] in 
    lazymatch goal with
    |- Rsimpl_modeq_2PI _ ?s =>
      apply (mk_Rsimpl_modeq_2PI r' r'' _);
      [exists (-1 : Z); lra|]
    end
  | _ =>
    lazymatch goal with
    |- Rsimpl_modeq_2PI _ ?s =>
      exact (Rmodeq_refl (2 * PI) r')
    end
  end. *)

#[global] Hint Extern 0 (Rsimpl_modeq_2PI ?r _) =>
  rsimpl_modeq_2PI_tac : typeclass_instances.



