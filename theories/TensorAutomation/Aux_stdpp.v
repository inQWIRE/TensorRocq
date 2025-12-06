(* Extra bits for stdpp *)
From stdpp Require Import decidable.

Lemma exists_dsig {A} {P Q : A -> Prop} `{forall x, Decision (P x)} : 
  (exists x : dsig P, Q (`x)) <-> exists x, P x /\ Q x.
Proof.
  split.
  - intros ((x & p) & q).
    cbn in *.
    apply bool_decide_unpack in p.
    eauto.
  - intros (x & p & q).
    now exists (dexist x p).
Qed.

Lemma exists_and_dsig {A} {P Q R : A -> Prop} 
  `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} : 
  (exists x : dsig (λ a, P a /\ Q a), R (`x)) <-> 
    exists (x : dsig P), Q (`x) /\ R (`x).
Proof.
  rewrite exists_dsig.
  setoid_rewrite <- (and_assoc _).
  now rewrite <- exists_dsig.
Qed.

From stdpp Require Import prelude.


Fixpoint join_list {A} (l : list (option A)) : option (list A) :=
  match l with 
  | [] => Some []
  | None :: _ => None
  | Some x :: ml => 
      l ← join_list ml;
      Some (x :: l)
  end.


Lemma join_list_Some {A} (l : list (option A)) l' : 
  join_list l = Some l' <-> l = Some <$> l'.
Proof.
  revert l'; induction l as [|a l IHl]; intros l'.
  - cbn.
    split; [now intros [= <-]|].
    now destruct l'.
  - cbn.
    destruct a; [|now destruct l'].
    rewrite bind_Some.
    setoid_rewrite IHl.
    destruct l'; [naive_solver|].
    naive_solver.
Qed.

Lemma join_list_is_Some {A} (l : list (option A)) : 
  is_Some (join_list l) <-> None ∉ l.
Proof.
  unfold is_Some.
  setoid_rewrite join_list_Some.
  induction l as [|a l IHl].
  - cbn.
    split; try easy.
    now exists [].
  - rewrite not_elem_of_cons, <- IHl.
    split.
    + intros (l' & Hl').
      destruct l' as [|a' l']; [easy|].
      cbn in Hl'.
      injection Hl'.
      intros -> ->.
      eauto.
    + intros [Ha (l' & Hl')].
      destruct a as [a|]; [|easy].
      exists (a :: l'); cbn; congruence.
Qed.
