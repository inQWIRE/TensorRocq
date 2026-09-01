(* We make variables generalizable so that the unbundled
  definition of SemiRing is usable as
  [`{SR : SemiRing R rO rI radd rmul req}].
  Additionally, it is not practical to declare only these
  variables generalizable, as this causes an error when
  all variables are later declared generalizable (such as
  in stdpp). *)
#[global]
Generalizable All Variables.

From TensorRocq Require Import Aux.
Require Ring_theory.
Require Integral_domain.
Require List.
Require SetoidList.
Require SetoidPermutation.
Require Import Ring.
Import Morphisms Setoid.

Class Field (R : Type) (rO : R) (rI : R)
  (radd : R -> R -> R) (rmul : R -> R -> R)
  (rsub : R -> R -> R) (ropp : R -> R)
  (rdiv : R -> R -> R) (rinv : R -> R)
  (req : R -> R -> Prop) := {
  Fth : Field_theory.field_theory rO rI radd rmul rsub ropp rdiv rinv req;
  Feq_ext : ring_eq_ext radd rmul ropp req;
  Finv_ext : Proper (req ==> req) rinv;
  Feq_equiv : Setoid.Setoid_Theory R req;
}.
Global Hint Mode Field ! - - - - - - - - - : typeclass_instances.

Section Field.

Context `{FTH : Field R rO rI radd rmul rsub ropp rdiv rinv req}.


Notation "0" := rO.
Notation "1" := rI.
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "-" := rsub.
Infix "*" := rmul.
Infix "/" := rdiv.
Notation "- x" := (ropp x).
Notation "/ x" := (rinv x).

Let Feq_equiv : Equivalence req := FTH.(Feq_equiv).

Local Existing Instance Feq_equiv.

Let Radd_proper := Feq_ext.(Radd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Feq_ext.(Rmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.

Let Ropp_proper := Feq_ext.(Ropp_ext) : Proper (req ==> req) ropp.
Local Existing Instance Ropp_proper.

Let Rinv_proper := Finv_ext : Proper (req ==> req) rinv.
Local Existing Instance Rinv_proper.

Add Field Ffield : FTH.(Fth).

End Field.

