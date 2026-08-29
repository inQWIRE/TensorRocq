From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)

Module GeneratorNotations.

Notation "'const' a" := (inl (Some (inr a))) (a at level 9, only printing, at level 1).

Notation "'Z' a" := (inl (Some (inl (false, a)))) (a at level 9, only printing, at level 1).
Notation "'Z'" := (inl (Some (inl (false, IZR 0)))) (only printing, at level 1).

Notation "'X' a" := (inl (Some (inl (true, a)))) (a at level 9, only printing, at level 1).
Notation "'X'" := (inl (Some (inl (true, IZR 0)))) (only printing, at level 1).

Notation "'H'" := ((inl (B:=BundledDiagram ZX) None)) (only printing, at level 1).

Notation "'[' zx ']'" := ((inr (A:=ZXCVERT) (existT _ zx%ZX))) (only printing, at level 0).
Notation "'[' zx ']'" := ((inr (A:=ZXCVERT) (bundleDiagram zx%ZX))) (only printing, at level 0).

(* TODO: The gen one that hides sizes *)

End GeneratorNotations.




(* FIXME: Move *)
Module BWQuote.

Import Ltac2.
Export BWQuote.

(* FIXME: Move *)
Ltac2 timeout_or (i : int) (f : unit -> 'a) (d : unit -> 'a) :=
  orelse (fun () => Control.timeout i f) (fun _ => d ()).

Ltac2 quote_constr_eq_timeout (i : int) c d :=
  timeout_or i (fun _ => quote_constr_eq c d) (fun _ => false).

End BWQuote.




(* Reset this to enable/disable visualization. By default, it is disabled in
  this file and enabled elsewhere. *)
Ltac visualize_flag :=
  idtac.

Ltac visualize_flag ::=
  fail.