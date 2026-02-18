Require Import PeanoNat Lia.
From stdpp Require Import base list.

Class AbstractTensorQuote {Ctx T} `{Equiv T'} (f : Ctx -> T -> T') (ctx : Ctx)
  (t : T) (t' : T') := {
  abs_quote : f ctx t ≡ t'
}.

#[global] Hint Mode AbstractTensorQuote + + + - + - - + : typeclass_instances.

Class AbstractTensorDenote {Ctx T} `{Equiv T'} (f : Ctx -> T -> T') (ctx : Ctx)
  (t : T) (t' : T') := {
  abs_denote : f ctx t ≡ t'
}.

#[global] Hint Mode AbstractTensorDenote + + + - + - + - : typeclass_instances.

#[export] Instance abstens_denote_default {Ctx T} `{Equiv T', Reflexive T' equiv}
  (f : Ctx -> T -> T') (ctx : Ctx) (t : T) :
  AbstractTensorDenote f ctx t (f ctx t) | 100.
Proof.
  constructor.
  reflexivity.
Qed.







Inductive IsNth {A} : forall (a : A) (i : nat) (l : list A), Prop :=
  | IsNth_here a l : IsNth a 0 (a :: l)
  | IsNth_later a i a' l : IsNth a i l -> IsNth a (S i) (a' :: l).

Lemma IsNth_iff_base {A} (a : A) i l :
  IsNth a i l <-> (i < length l /\ forall d, nth i l d = a)%nat.
Proof.
  split.
  - intros Hisn.
    induction Hisn; (split; [cbn; lia|]).
    + reflexivity.
    + intros ?.
      cbn.
      easy.
  - intros [Hil Hnth].
    revert l Hil Hnth;
    induction i; intros l Hil Hnth.
    + destruct l; [easy|].
      generalize (Hnth a).
      cbn.
      intros ->.
      constructor.
    + destruct l; [easy|].
      cbn in Hil.
      apply <- Nat.succ_lt_mono in Hil.
      constructor.
      auto.
Qed.

Lemma IsNth_iff {A} (a : A) i l :
  IsNth a i l <-> l !! i = Some a.
Proof.
  split.
  - intros Hisn.
    induction Hisn; [done|].
    cbn.
    done.
  - revert l;
    induction i; intros l Hil.
    + destruct l; [easy|].
      cbn in Hil.
      revert Hil.
      intros [= ->].
      constructor.
    + destruct l; [easy|].
      cbn in Hil.
      constructor.
      auto.
Qed.



(* On a goal [IsNth a ?i l], where [l] is [a0 :: a1 :: ... :: an :: ?l]
  (i.e. ends in an evar), solves it with the smallest [i] such that
  [a] and [ai] are convertible, or appends [a] to [l] if not (by
  instantiating [?l := a :: ?l']). Assumes that [a] and all the [ai]
  are ground terms (i.e. are not evars), and that [l] ends in an evar as
  described above (if [a] is in [l], the latter condition is not necessary). *)
Ltac get_nth :=
  lazymatch goal with
  | |- @IsNth ?A ?a ?i_evar ?l =>
    tryif is_evar l then
      (* idtac "evar" l; *)
      let l' := fresh "l" in
      evar (l' : list A);
      let l' := eval unfold l' in l' in
      refine (IsNth_here a l');
      shelve
    else
      lazymatch l with
      | ?a0 :: ?lrest =>
        (* idtac "trying" a0; *)
        tryif unify a a0 then
          (* idtac "succeeded"; *)
          refine (IsNth_here a lrest);
          shelve
        else
          (* idtac "failed"; *)
          refine (IsNth_later a _ a0 lrest _);
          shelve_unifiable;
          get_nth
      | _ => fail "get_nth: list" l "is not an evar or a cons"
      end
  | |- ?G => fail "get_nth: goal is not of the form 'IsNth a ?i l' (goal:" G ")"
  end.


(* Splits a goal [Forall2 P l l'] according to the structure of [l].
  In particular, if [l] is concrete and [l'] is an evar, [l'] will be
  filled with evars to match the length of [l] *)
Ltac split_forall2 := match goal with
  | |- Forall2 _ (cons _ _) _ => apply List.Forall2_cons; [|split_forall2]
  | |- Forall2 _ nil _ => apply List.Forall2_nil
  | _ => idtac
  end.

(* To make the [IsNth] condition work, we use the following hint *)
#[global] Hint Extern 0 (IsNth _ _ _) => get_nth : typeclass_instances.

Require Import Aux_pos.

#[export] Instance positive_equiv : Equiv positive := eq.

Definition interp_discrete_hg {T} (l : list T) (p : positive) :
  option T :=
  l !! (pos_to_nat_pred p).

#[global] Instance interp_discrete_hg_proper `{Equiv T, Reflexive T equiv} ctx :
  Proper (equiv ==> equiv) (@interp_discrete_hg T ctx).
Proof.
  intros ? ? [].
  now apply option_Forall2_refl.
Qed.

#[global] Instance abstens_quote_discrete `{Equiv T, Reflexive T equiv}
  (ctx : list T) (n : nat) (t : T) : IsNth t n ctx ->
  AbstractTensorQuote interp_discrete_hg ctx (Pos.of_succ_nat n) (Some t).
Proof.
  intros Hn%IsNth_iff.
  constructor.
  unfold interp_discrete_hg.
  rewrite pos_to_nat_pred_of_nat.
  rewrite Hn.
  now apply option_Forall2_refl.
Qed.