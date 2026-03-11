Require Export FreeAPropAux.

(* FIXME: Move *)
Inductive sigT_equiv {A} (P : A -> Type) 
  {HP : forall a, Equiv (P a)} : Equiv (sigT P) :=
  | mk_sigT_equiv a (x y : P a) : x ≡ y ->
    existT a x ≡ existT a y.
#[global] Existing Instance sigT_equiv.

#[export] Instance sigT_equiv_dec `{EqDecision A} (P : A -> Type)
  {HP : forall a, Equiv (P a)} {HPdec : forall a, RelDecision (≡@{P a})} :
  RelDecision (≡@{sigT P}).
   refine (fun '(existT a x) '(existT b y) =>
    match decide (a = b) with
    | left Hab => cast_if (decide (x ≡ eq_rect_r P y Hab))
    | right Hab => right _
    end).
  Proof.
    - abstract (now subst).
    - abstract (intros Heq;
      apply n;
      subst;
      inversion Heq;
      repeat_on_hyps ltac:(fun H => inversion_sigma H);
      rewrite ?(proof_irrel _ (eq_refl _)) in *;
      cbn in *;
      subst;
      auto).
    - abstract (intros Heq;
      now inversion Heq).
  Defined.
