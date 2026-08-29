From VyZX Require Export ZXRules ZXpermFacts CoreRules DiagramRules GateRules.

From TensorRocqEx Require Export VyZXTensor.
From TensorRocq Require Import ProLike PropGraphTerm.


From TensorRocqEx Require Import Rmodeq.
From TensorRocqEx Require Export ZXAux.
From TensorRocqEx Require Export BaseInstances.



From TensorRocq Require Import Props.Prop.Rewriting.
Import Definitions PropsGraphs.
From TensorRocq Require SizedProQuote. (* For visualization *)




From TensorRocqEx Require Export ZXrw_base.

From TensorRocqEx Require Export ZXrwsymm ZXrwauto ZXrwfrob.

From TensorRocqEx Require Export ZXsrw_base.

From TensorRocqEx Require Export ZXsrwsymm ZXsrwauto (* FIXME: Add: ZXsrwfrob *).




From TensorRocq Require Import BW BWSized SizedProps PropsGraphs SizedPropsGraphs SizedProLike SizedRewriting SizedProQuote.




Ltac visualize_flag ::=
  idtac.