From TensorRocq Require Export sigT2_relation Monoid.
From TensorRocq Require Import AProp.
From TensorRocq Require Import SizedGraph.ToUnsized.

(* FIXME: Move *)
#[export] Instance sum_decomp_MonoidSize `{MD : Monoid M mO madd meq,
  FMD : !FreeMonoid M X} (f : X -> nat) :
  MonoidSize (λ m : M, sum_list_with f (mdecomp m)).
Proof.
  split.
  - change (Proper ?R _) with (Proper R (sum_list_with f ∘ mdecomp)).
    apply _.
  - now rewrite mdecomp_mO.
  - intros n m.
    now rewrite mdecomp_madd, sum_list_with_app.
Qed.


Inductive MProp `{MD : Monoid M mO madd meq}
  {T : Type} : M -> M -> Type :=
  | Mid n : MProp n n
  | Mswap n m : MProp (madd n m) (madd m n)
  | Mcup n : MProp mO (madd n n)
  | Mcap n : MProp (madd n n) mO
  | Mcompose {n m o} (mp1 : MProp n m) (mp2 : MProp m o) : MProp n o
  | Mstack {n1 m1 n2 m2}
    (mp1 : MProp n1 m1) (mp2 : MProp n2 m2) : MProp (madd n1 n2) (madd m1 m2)
  | Mcast n m n' m' : meq n n' -> meq m m' -> MProp n m -> MProp n' m'
  | Mgen (t : T) n m : MProp n m.

#[global] Arguments MProp _ {_ _ _ _} _ _ _ : assert.

Definition Massoc `{MD : Monoid M mO madd meq} {T} n m (Hnm : meq n m) : MProp M T n m :=
  Mcast n n n m (MD.(meq_equivalence).(Equivalence_Reflexive) _) Hnm (Mid n).

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
  | Mcast n m n' m' Hn Hm mp =>
    cast_aprop (msize_proper n n' Hn) (msize_proper m m' Hm) (MProp_to_AProp mp)
  | Mgen t n m => Agen t _ _
  end.




Fixpoint MProp_sized_graph_semantics `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} {a b : M} (mp : MProp M T a b) : SizedCospanHyperGraph X T (length (mdecomp a)) (length (mdecomp b)) :=
  match mp with
  | Mid n => id_sized_graph (list_to_vec (mdecomp n))
  | Mswap n m =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n m)) (length_app _ _)))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd m n)) (length_app _ _)))
      (swap_sized_graph (list_to_vec (mdecomp n)) (list_to_vec (mdecomp m)))
    (* cast_aprop' (msize_add n m) (msize_add m n) (Aswap (f n) (f m)) *)
  | Mcup n =>
    cast_sized_graph
      (eq_sym (f_equal length mdecomp_mO))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n n)) (length_app _ _)))
      (cup_sized_graph (list_to_vec (mdecomp n)))
  | Mcap n =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd n n)) (length_app _ _)))
      (eq_sym (f_equal length mdecomp_mO))
      (cap_sized_graph (list_to_vec (mdecomp n)))

  | Mcompose mp1 mp2 =>
    compose_sized_graphs (MProp_sized_graph_semantics mp1)
      (MProp_sized_graph_semantics mp2)
  | Mstack mp1 mp2 =>
    cast_sized_graph
      (eq_sym (eq_trans (f_equal length (mdecomp_madd _ _)) (length_app _ _)))
      (eq_sym (eq_trans (f_equal length (mdecomp_madd _ _)) (length_app _ _)))

      (stack_sized_graphs (MProp_sized_graph_semantics mp1)
        (MProp_sized_graph_semantics mp2))
  | Mcast n m n' m' Hn Hm mp => cast_sized_graph (f_equal length (mdecomp_proper n n' Hn))
    (f_equal length (mdecomp_proper m m' Hm)) (MProp_sized_graph_semantics mp)
  | Mgen t n m =>
    sized_graph_of_tensor t (list_to_vec (mdecomp n)) (list_to_vec (mdecomp m))
  end.





Lemma MProp_sized_graph_semantics_correct_aux `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} (f : X -> nat) {a b : M} (mp : MProp M T a b) :
  well_sized (MProp_sized_graph_semantics mp) /\
  sized_inputs (MProp_sized_graph_semantics mp) = Some <$> mdecomp a /\
  sized_outputs (MProp_sized_graph_semantics mp) = Some <$> mdecomp b /\
  (sized_graph_to_graph f (MProp_sized_graph_semantics mp) [≡ᵢ]ₛ
  AProp_graph_semantics (MProp_to_AProp (MS:=sum_decomp_MonoidSize f) mp))%cohg.
Proof.
  induction mp;
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
  - rewrite sized_graph_to_graph_id_sized_graph'.
    rewrite sized_inputs_id_sized_graph, sized_outputs_id_sized_graph.
    split; [apply well_sized_id_sized_graph|now rewrite vec_to_list_to_vec].
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_swap_sized_graph, sized_outputs_swap_sized_graph.
    split; [apply well_sized_swap_sized_graph|].
    rewrite 2 vec_to_list_to_vec, 2 mdecomp_madd.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_swap_sized_graph).
    now rewrite 2 vec_to_list_to_vec.
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_cup_sized_graph, sized_outputs_cup_sized_graph.
    split; [apply well_sized_cup_sized_graph|].
    rewrite vec_to_list_to_vec, mdecomp_madd, mdecomp_mO.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_cup_sized_graph).
    now rewrite vec_to_list_to_vec.
  - rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_cap_sized_graph, sized_outputs_cap_sized_graph.
    split; [apply well_sized_cap_sized_graph|].
    rewrite vec_to_list_to_vec, mdecomp_madd, mdecomp_mO.
    split_and!; [done..|].
    rewrite (sized_graph_to_graph_cap_sized_graph).
    now rewrite vec_to_list_to_vec.
  - destruct IHmp1 as (Hws1 & Hins1 & Houts1 & Hiso1).
    destruct IHmp2 as (Hws2 & Hins2 & Houts2 & Hiso2).
    rewrite sized_inputs_compose_sized_graphs,
      sized_outputs_compose_sized_graphs by assumption + congruence.
    split; [apply well_sized_compose_sized_graphs; assumption + congruence|].
    split_and!; [assumption..|].
    destruct (sized_graph_to_graph_compose_graphs f
    (MProp_sized_graph_semantics mp1) (MProp_sized_graph_semantics mp2)) as (? & Heq).
    1:{
      unfold sized_inputs, sized_outputs in *.
      congruence.
    }
    rewrite Heq.
    symmetry in Hiso1, Hiso2.
    apply sigT2_relation_alt in Hiso1, Hiso2.
    destruct Hiso1 as (Hisoeq1 & Hiso1).
    destruct Hiso2 as (Hisoeq2 & Hiso2).
    etransitivity. 2:{
      instantiate (1:=graph_to_pair_bundled _).
      constructor.
      symmetry.
      apply compose_graphs_struct_isomorphic;
      eassumption.
    }
    cbn [projT2 graph_to_pair_bundled].
    unfold eq_rect_r.
    rewrite 2 cast_pair_to_cast_graph.
    apply eq_reflexivity.
    apply compose_graphs_bundled_eq; now rewrite ?graph_to_pair_bundled_cast.
  - destruct IHmp1 as (Hws1 & Hins1 & Houts1 & Hiso1).
    destruct IHmp2 as (Hws2 & Hins2 & Houts2 & Hiso2).
    rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    rewrite sized_inputs_stack_sized_graphs, sized_outputs_stack_sized_graphs.
    split; [apply well_sized_stack_sized_graphs; assumption|].
    split_and!; [rewrite mdecomp_madd, fmap_app; f_equal; done..|].
    rewrite sized_graph_to_graph_stack_graphs.
    refine (sigT2_relation_f_equiv_2 _ _ _
      (@stack_graphs T) _ _ Hiso1 _ _ Hiso2).
  -
    rewrite sized_graph_to_graph_cast, AProp_graph_semantics_cast,
      2 graph_to_pair_bundled_cast,
        well_sized_cast, sized_inputs_cast, sized_outputs_cast.
    cbn [MProp_sized_graph_semantics AProp_graph_semantics MProp_to_AProp].
    split; [apply IHmp.1|].
    split; [rewrite IHmp.2.1; f_equal; now apply mdecomp_proper|].
    split; [rewrite IHmp.2.2.1; f_equal; now apply mdecomp_proper|].
    easy.
  - split; [apply well_sized_sized_graph_of_tensor|].
    rewrite sized_inputs_sized_graph_of_tensor,
      sized_outputs_sized_graph_of_tensor.
    split_and!; [now rewrite vec_to_list_to_vec..|].
    rewrite sized_graph_to_graph_sized_graph_of_tensor'.
    now rewrite 2 vec_to_list_to_vec.
Qed.




Lemma MProp_sized_graph_semantics_correct `{MD : Monoid M mO madd meq, FMD : !FreeMonoid M X}
  {T} (f : X -> nat) {a b : M} (mp : MProp M T a b) :
  (sized_graph_to_graph f (MProp_sized_graph_semantics mp) [≡ᵢ]ₛ
  AProp_graph_semantics (MProp_to_AProp (MS:=sum_decomp_MonoidSize f) mp))%cohg.
Proof.
  apply MProp_sized_graph_semantics_correct_aux.
Qed.

Lemma by_sigT2_relation {A B} `{forall ab : A * B, ProofIrrel (ab = ab)}
  {P : A -> B -> Type}
  (R : forall a b, relation (P a b))
  {a b} (x y : P a b) :
  sigT2_relation R (existT (a, b) x) (existT (a, b) y) ->
  R a b x y.
Proof.
  rewrite sigT2_relation_alt.
  cbn.
  intros (Hab & HR).
  now rewrite (proof_irrel Hab eq_refl) in HR.
Qed.


Declare Scope mprop_scope.
Bind Scope mprop_scope with MProp.
Delimit Scope mprop_scope with mprop.


Notation "x * y" := (Mstack x%mprop y%mprop)
  (at level 40, left associativity) : mprop_scope.

Notation "x ;' y" := (Mcompose x%mprop y%mprop)
  (at level 50, left associativity) : mprop_scope.

Notation Massoc' H := (Massoc _ _ H) (only parsing).

Close Scope aprop_scope.
Open Scope mprop_scope.



Section perms.

Context `{MD : Monoid M mO madd meq}.

Notation "0" := mO.
Notation "x '==' y" := (meq x y) (at level 70).
Infix "+" := madd.

(* We use [Let] and [Local Existing Instance] to avoid creating extra
  definitions *)
Let Meq_equivalence : Equivalence meq := meq_equivalence.
Local Existing Instance Meq_equivalence.

Let Meq_refl : Reflexive meq := meq_equivalence.(Equivalence_Reflexive).
Local Existing Instance Meq_refl.

Let Madd_proper : Proper (meq ==> meq ==> meq) madd := madd_proper.
Local Existing Instance Madd_proper.

Open Scope mprop_scope.

Definition cast_mprop {T} {n m n' m' : M}
  (Hn : n == n') (Hm : m == m') (mp : MProp M T n m) : MProp M T n' m' :=
  Mcast _ _ _ _ Hn Hm mp.

Notation cast_mprop' Hn Hm mp :=
  (cast_mprop (meq_equivalence.(Equivalence_Symmetric) _ _ Hn)
    (meq_equivalence.(Equivalence_Symmetric) _ _ Hm) mp) (only parsing).


Definition mtop_to_bottom {T} (ls : list M) :
  MProp M T (Mlist_sum ls) (Mlist_sum (tail ls) + Mlist_sum (option_list (head ls))) :=
  match ls with
  | [] => Massoc' (symmetry (madd_0_l 0))
  | a :: ls =>
    cast_mprop (reflexivity _) ((madd_proper (Mlist_sum ls) (Mlist_sum ls) (reflexivity (Mlist_sum ls))
      a (a + 0) (symmetry (MD.(madd_0_r) a)))) (Mswap a (Mlist_sum ls))
      (* (Massoc (Mlist_sum ls + a) (Mlist_sum ls + (a + 0))
      ) *)
  end.

(*
Definition abottom_to_top {T} (n : nat) : MProp M T n n :=
  match n with
  | 0 => Aid 0
  | S n =>
    cast_aprop (Nat.add_comm n 1) eq_refl (Aswap n 1)
  end.

Definition aprop_aswap {T} (n : nat) : MProp M T n n :=
  match n with
  | 0 => Aid 0
  | 1 => Aid _
  | 2 => Aswap 1 1
  | S n =>
    cast_aprop (Nat.add_comm n 1) eq_refl
      (Acompose (Aswap n 1) (Astack (Aid 1) (atop_to_bottom n)))
  end.





Lemma Apad_prf {a n} (H : a < n) : a + (n - a) = n.
Proof. lia. Qed.

Definition Apad {T a} (ap : MProp M T a a) n : MProp M T n n :=
  match decide (a = n) with
  | left Han => cast_aprop Han Han ap
  | right _ =>
    match Nat.lt_dec a n with
    | left Han => cast_aprop (Apad_prf Han) (Apad_prf Han) (Astack ap (Aid (n - a)))
    | right _ => Aid _
    end
  end.


Definition ocast_aprop {T n m n' m'} (ap : MProp M T n m) : option (MProp M T n' m') :=
  match decide (n = n' /\ m = m') with
  | left Hnm => Some (cast_aprop Hnm.1 Hnm.2 ap)
  | right _ => None
  end.

Definition Apad_nonsquare {T a b} (ap : MProp M T a b) n m :
  option (MProp M T n m) :=
  match decide (a = n /\ b = m) with
  | left Heq => Some (cast_aprop Heq.1 Heq.2 ap)
  | right _ =>
    ocast_aprop (Astack ap (Aid (n - a)))
  end.

Lemma Apad_nonsquare_l_prf1 {a b n} (Han : a = n) : b = n + b - a.
Proof.
  lia.
Qed.

Lemma Apad_nonsquare_l_prf2 {a b n} (Han : a < n) : b + (n - a) = n + b - a.
Proof.
  lia.
Qed.

Definition Apad_nonsquare_l {T a b} (ap : MProp M T a b) n :
  option (MProp M T n (n + b - a)) :=
  match decide (a = n) with
  | left Han => Some $ cast_aprop Han (Apad_nonsquare_l_prf1 Han) ap
  | right _ =>
    match decide (a < n) with
    | left Han => Some $ cast_aprop (Apad_prf Han)
      (Apad_nonsquare_l_prf2 Han) (Astack ap (Aid (n - a)))
    | right _ => None
    end
  end.

Definition aprop_to_top {T} (a n : nat) : MProp M T n n :=
  Apad (abottom_to_top (S a `min` n)) n. *)


(* FIXME: Move *)
Lemma lookup_list_decomps_aux {A} (pre l : list A) k :
  list_decomps_aux pre l !! k =
  (λ a, (pre ++ take k l, a, drop (S k) l)) <$> l !! k.
Proof.
  revert k pre; induction l; intros k pre; [now destruct k|].
  cbn.
  destruct k as [|k]; [cbn; now rewrite app_nil_r, drop_0|].
  cbn.
  rewrite IHl.
  destruct (l !! k); [|done].
  cbn.
  now rewrite <- app_assoc.
Qed.
Lemma lookup_list_decomps {A} (l : list A) k :
  list_decomps l !! k =
  (λ a, (take k l, a, drop (S k) l)) <$> l !! k.
Proof.
  unfold list_decomps.
  rewrite lookup_list_decomps_aux.
  done.
Qed.
Lemma lookup_list_removals {A} (l : list A) k :
  list_removals l !! k =
  (., take k l ++ drop (S k) l) <$> l !! k.
Proof.
  unfold list_removals.
  rewrite list_lookup_fmap, lookup_list_decomps.
  rewrite <- option_fmap_compose.
  done.
Qed.



(* Definition list_to_front {A} (ns : list A) (a : nat) : list ns :=
  match list_removals ns !! a with
  | None => ns
  | Some  *)

(* Lemma false : False.
Proof. admit. Admitted. *)

Definition Mswapa {T} (a b c : M) : MProp M T (a + (b + c)) (b + (a + c)) :=
  (cast_mprop' ((MD.(madd_assoc) a b c))
    ((MD.(madd_assoc) b a c)) (Mstack (Mswap a b) (Mid c))).

Definition mprop_to_top {T n} (i : fin n) : forall (v : vec M n), MProp M T (Mlist_sum v)
  (Mlist_sum (v !!! i ::: vremove i v)) :=
  Fin.t_rect (fun n i => forall v : vec M n,
  MProp M T (Mlist_sum v) (Mlist_sum (v !!! i ::: vremove i v)))
  (λ n, vec_S_inv (λ v, MProp M T (Mlist_sum v)
    (Mlist_sum (v !!! (0%fin :> fin (S n)) ::: vremove 0%fin v)))
     (λ x v, (Mid (x + Mlist_sum v) :>
     MProp M T (Mlist_sum (x ::: v))
    (Mlist_sum ((x ::: v) !!! 0%fin ::: vremove 0 (x ::: v))))))
  (fun n i => match i with
    | 0%fin => fun _ => vec_S_inv _ (λ a : M, vec_S_inv _ (λ b v,
      Mswapa a b (Mlist_sum v)))
    | FS i' => fun IH =>
      vec_S_inv _ (λ a v,
      Mcompose (Mstack (Mid a) (IH v))
        (Mswapa _ _ _))
    end) n i.


Definition mprop_to_top' {T n} (i : fin n) (v : vec M n) : MProp M T (Mlist_sum' v)
  (Mlist_sum' (v !!! i ::: vremove i v)) :=
  cast_mprop' (Mlist_sum'_correct _) (Mlist_sum'_correct _)
  (mprop_to_top i v).



Fixpoint apply_sw {A n} (ns : vec A n) (l : list nat) {struct n} : vec A n :=
  match n with
  | 0 => fun ns => ns
  | S n => fun ns =>
    if decide (n <= 1) then
      match n as n return vec A (S n) -> vec A (S n) with
      | 1 => fun ns => if decide (head l = Some 1) then [# vhd (vtl ns) ; vhd ns] else ns
      | _ => fun ns => ns
      end ns
    else
      match l with
      | [] => ns
      | a :: l =>
        match decide (a < S n) with
        | right _ => ns
        | left Ha => ns !!! (nat_to_fin Ha) :::
          apply_sw (vremove (nat_to_fin Ha) ns)
          ((λ k, if decide (a < k) then Nat.pred k else k) <$> l)
        end
      end
  end ns.


Fixpoint mprop_of_sw {T n} (ns : vec M n) (l : list nat) :
  MProp M T (Mlist_sum ns) (Mlist_sum (apply_sw ns l)).
  refine (
    match n as n return forall ns : vec M n, MProp M T (Mlist_sum ns) (Mlist_sum (apply_sw ns l)) with
    | 0 => fun ns => Mid (Mlist_sum ns)
    | S n => fun ns => _
    end ns).
  cbn.
  case_decide as Hn.
  - refine (match n with
    | 1 => _
    | _ => _
    end ns).
    + intros; apply Mid.
    + case_decide; [|intros; apply Mid].
      refine (vec_S_inv _ _).
      intros a.
      refine (vec_S_inv _ _).
      intros b.
      refine (vec_0_inv _ _).
      cbn.
      apply Mswapa.
    + intros; apply Mid.
  - destruct l as [|a l]; [apply Mid|].
    case_decide as Ha; [|apply Mid].
    refine (Mcompose (mprop_to_top (nat_to_fin Ha) ns) _).
    cbn [vec_to_list Mlist_sum].
    refine (Mstack (Mid _) _).
    apply mprop_of_sw.
Defined.

Lemma Mlist_sum'_cons m (l : list M) : Mlist_sum' (m :: l) == m + Mlist_sum' l.
Proof.
  destruct l; [|done].
  cbn.
  now rewrite madd_0_r.
Qed.

Definition Mstack'_sums {T} {n m} {ns ms : list M} : forall
  (mp : MProp M T n m) (mps : MProp M T (Mlist_sum' ns) (Mlist_sum' ms)),
  MProp M T (Mlist_sum' (n :: ns)) (Mlist_sum' (m :: ms)) :=
  match ns as ns, ms as ms return forall
  (mp : MProp M T n m) (mps : MProp M T (Mlist_sum' ns) (Mlist_sum' ms)),
    MProp M T (Mlist_sum' (n :: ns)) (Mlist_sum' (m :: ms)) with 
  | [], [] => fun mp _ => mp
  | n' :: ns, [] => fun mp mps =>
    cast_mprop (Meq_refl _) (madd_0_r m) (Mstack mp mps)
  | [], m' :: ms => fun mp mps =>
    cast_mprop (madd_0_r n) (Meq_refl _) (Mstack mp mps)
  | _, _ => fun mp mps => Mstack mp mps
  end.

Fixpoint mprop_of_sw' {T n} (ns : vec M n) (l : list nat) :
  MProp M T (Mlist_sum' ns) (Mlist_sum' (apply_sw ns l)).
  refine (
    match n as n return forall ns : vec M n, 
      MProp M T (Mlist_sum' ns) (Mlist_sum' (apply_sw ns l)) with
    | 0 => fun ns => Mid (Mlist_sum' ns)
    | S n => fun ns => _
    end ns).
  cbn.
  case_decide as Hn.
  - refine (match n with
    | 1 => _
    | _ => _
    end ns).
    + intros; apply Mid.
    + case_decide; [|intros; apply Mid].
      refine (vec_S_inv _ _).
      intros a.
      refine (vec_S_inv _ _).
      intros b.
      refine (vec_0_inv _ _).
      cbn.
      apply Mswap.
    + intros; apply Mid.
  - destruct l as [|a l]; [apply Mid|].
    case_decide as Ha; [|apply Mid].
    refine (Mcompose (mprop_to_top' (nat_to_fin Ha) ns) _).
    cbn [vec_to_list Mlist_sum].
    refine (Mstack'_sums (Mid _) _).
    apply mprop_of_sw'.
Defined.


Definition Mocompose `{!RelDecision meq} {T n m m' o}
  (mp1 : MProp M T n m) (mp2 : MProp M T m' o) :
  option (MProp M T n o) :=
  match decide (m == m') with
  | right _ => None
  | left Heq => Some (Mcompose (cast_mprop (reflexivity _) Heq mp1) mp2)
  end.

Definition ocast_mprop_r `{!RelDecision meq} {T n m} m'
  (mp : MProp M T n m) : option (MProp M T n m') :=
  match decide (m == m') with
  | right _ => None
  | left Heq => Some (cast_mprop (reflexivity _) Heq mp)
  end.

Definition ocast_mprop_l `{!RelDecision meq} {T n m} n'
  (mp : MProp M T n m) : option (MProp M T n' m) :=
  match decide (n == n') with
  | right _ => None
  | left Heq => Some (cast_mprop Heq (reflexivity _) mp)
  end.

Definition ocast_mprop `{!RelDecision meq} {T n m} n' m'
  (mp : MProp M T n m) : option (MProp M T n' m') :=
  Hn ← guard (n == n'); Hm ← guard (m == m');
  Some (cast_mprop Hn Hm mp).

End perms.