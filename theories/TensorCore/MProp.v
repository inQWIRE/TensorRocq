Require Import Monoid AProp.

Inductive MProp `{MD : Monoid M mO madd meq} 
  {T : Type} : M -> M -> Type :=
  | Mid n : MProp n n
  | Mswap n m : MProp (madd n m) (madd m n)
  | Mcup n : MProp mO (madd n n)
  | Mcap n : MProp (madd n n) mO
  | Mcompose {n m o} (mp1 : MProp n m) (mp2 : MProp m o) : MProp n o
  | Mstack {n1 m1 n2 m2} 
    (mp1 : MProp n1 m1) (mp2 : MProp n2 m2) : MProp (madd n1 n2) (madd m1 m2)
  | Massoc n m : meq n m -> MProp n m.

#[global] Arguments MProp _ {_ _ _ _} _ _ _ : assert.

(* FIXME: Move *)
Notation cast_aprop' Hn Hm ap :=
  (cast_aprop (eq_sym Hn) (eq_sym Hm) ap) (only parsing).

Fixpoint MProp_to_AProp `{MD : Monoid M mO madd meq, f : M -> nat, 
  MS : !MonoidSize f} {T} {n m : M}
  (mp : MProp M T n m) : AProp T (f n) (f m) :=
  match mp with
  | Mid n => Aid _
  | Mswap n m => cast_aprop' (msize_add n m) (msize_add m n) (Aswap (f n) (f m))
  | Mcup n => cast_aprop' msize_mO (msize_add n n) (Acup (f n))
  | Mcap n => cast_aprop' (msize_add n n) msize_mO (Acap (f n))
  | Mcompose mp1 mp2 => 
      Acompose (MProp_to_AProp mp1) (MProp_to_AProp mp2)
  | Mstack mp1 mp2 => 
      cast_aprop' (msize_add (_ :> M) _) (msize_add (_ :> M) _) (Astack
        (MProp_to_AProp mp1) (MProp_to_AProp mp2))
  | Massoc n m Hnm => cast_aprop eq_refl (msize_proper n m Hnm) (Aid _)
  end.


Class MProp_of_AProp `{MD : Monoid M mO madd meq, f : M -> nat, MS : !MonoidSize f}
  {T} {a b : M} (mp : MProp M T a b) {n m : nat} (ap : AProp T n m) := {
  mprop_of_aprop : exists Hn Hm, cast_aprop Hn Hm (MProp_to_AProp mp) = ap;
}.

#[export] Instance mprop_of_aprop_mprop_to_aprop `{MD : Monoid M mO madd meq, f : M -> nat, MS : !MonoidSize f}
  {T} {a b : M} (mp : MProp M T a b) : 
  MProp_of_AProp mp (MProp_to_AProp mp).
Proof.
  constructor.
  exists eq_refl, eq_refl.
  apply cast_aprop_id.
Qed.


#[export] Instance mprop_of_aprop_cast `{MD : Monoid M mO madd meq, f : M -> nat, MS : !MonoidSize f}
  {T} {a b : M} (mp : MProp M T a b) {n m n' m'} (ap : AProp T n m)
    (Hn : n = n') (Hm : m = m') : 
  MProp_of_AProp mp ap -> MProp_of_AProp mp (cast_aprop Hn Hm ap).
Proof.
  intros [(Ha & Hb & <-)].
  subst.
  rewrite 2 cast_aprop_id.
  apply _.
Qed.



