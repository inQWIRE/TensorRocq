From QuantumLib Require Import Complex.
Require Import Aux_pos.
Require Import Tensor.
From stdpp Require Import list fin_maps.
From stdpp Require Import pmap gmap.
Require Import TensorExprDBSyntax TensorExprDBSemantics.
Require Import ZXCore.
Require ZifyBool.
Require Import TensorGraph.

#[local] Coercion pos_to_nat_pred : positive >-> nat.

(* FIXME: Move *)
Lemma Forall_filter {A} (P Q : A -> Prop) `{HP : forall a, Decision (P a)}
  (l : list A) :
  Forall Q (filter P l) <-> Forall (fun a => P a -> Q a) l.
Proof.
  induction l; [now split; constructor|].
  cbn.
  case_decide as HPa.
  - rewrite 2 Forall_cons, IHl. tauto.
  - rewrite Forall_cons, IHl. tauto.
Qed.

Lemma fmap_const {A B} (l : list A) (b : B) :
  const b <$> l = replicate (length l) b.
Proof.
  induction l; cbn; f_equal; assumption.
Qed.

Lemma lookup_gmaps_to_Pmap {A} (mi mo : gmap nat A) p :
  gmaps_to_Pmap mi mo !! p =
  match p with
  | xH => None
  | p~0 => mi !! (p:>nat)
  | p~1 => mo !! (p:>nat)
  end.
Proof.
  unfold gmaps_to_Pmap.
  rewrite lookup_union.
  destruct p.
  - rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite option_union_left_id.
    replace p~1 with ((bcons true ∘ Pos.of_succ_nat) p) by now cbn; lia.
    rewrite lookup_kmap by apply _.
    reflexivity.
  - replace p~0 with ((bcons false ∘ Pos.of_succ_nat) p) by now cbn; lia.
    rewrite lookup_kmap by apply _.
    rewrite (lookup_kmap_None _ _ _).2 by now cbn; lia.
    rewrite option_union_right_id.
    reflexivity.
  - rewrite 2 (lookup_kmap_None _ _ _).2 by now cbn; lia.
    reflexivity.
Qed.

Lemma length_list_filter_ext {A B} (P : A -> Prop) (Q : B -> Prop)
  `{HP : forall a, Decision (P a)} `{HQ : forall b, Decision (Q b)}
  (l : list A) (l' : list B) :
  Forall2 (λ a b, P a <-> Q b) l l' ->
  length (filter P l) = length (filter Q l').
Proof.
  intros Hall.
  induction Hall; [reflexivity|].
  cbn.
  unshelve (erewrite decide_ext by eassumption); [auto|].
  case_decide; cbn; f_equal; easy.
Qed.

(* FIXME: Move *)
Lemma lengthN_fmap {A B} (f : A -> B) (l : list A) :
  lengthN (f <$> l) = lengthN l.
Proof.
  apply lengthN_eq, length_fmap.
Qed.
Lemma ppermute_fmap {A B} p (f : A -> B) (l : list A) :
  ppermute p (f <$> l) = f <$> ppermute p l.
Proof.
  destruct (ppermute_case p l) as [(Hbdd & Hsome) | (Hndbb & Hnone)].
  - apply (list_eq_same_length _ _ _ eq_refl);
    [now rewrite length_fmap, 2 length_ppermute, length_fmap|].
    intros i x y.
    rewrite length_fmap, length_ppermute.
    intros Hi.
    rewrite lookup_ppermute_alt_bdd by now rewrite ?lengthN_fmap, ?length_fmap.
    rewrite 2 list_lookup_fmap.
    rewrite lookup_ppermute_alt_bdd by easy.
    congruence.
  - now rewrite 2 ppermute_not_bdd by now rewrite ?lengthN_fmap.
Qed.
Lemma default_is_Some_ext_mor_gen {B} {R : relation B} (d d' : B)
  (mb mb' : option B) : R d d' ->
  (forall b, mb = Some b -> mb' = None -> R b d') ->
  (forall b', mb = None -> mb' = Some b' -> R d b') ->
  (forall b b', mb = Some b -> mb' = Some b' -> R b b') ->
  R (default d mb) (default d' mb').
Proof.
  destruct mb, mb'; cbn; eauto.
Qed.
Lemma default_is_Some_ext_mor {B} {R : relation B} (d d' : B)
  (mb mb' : option B) :
  (is_Some mb <-> is_Some mb') ->
  R d d' ->
  (forall b b', mb = Some b -> mb' = Some b' -> R b b') ->
  R (default d mb) (default d' mb').
Proof.
  intros HSome Hd HR.
  rewrite 2 is_Some_alt in HSome.
  destruct mb, mb'; cbn; naive_solver.
Qed.
Lemma not_elem_of_list_fmap {A B} (f : A -> B) (l : list A) (b : B) :
  b ∉ f <$> l <-> forall a, a ∈ l -> f a ≠ b.
Proof.
  rewrite elem_of_list_fmap.
  naive_solver.
Qed.
Lemma Permutation_swap_app_app {A} (l1 l2 l3 l4 : list A) :
  (l1 ++ l2) ++ (l3 ++ l4) ≡ₚ (l1 ++ l3) ++ (l2 ++ l4).
Proof.
  solve_Permutation.
Qed.
Lemma forall_var (P : var -> Prop) :
  (forall v, P v) <-> (forall r, P (rel r)) /\ (forall l, P (loc l)) /\
    (forall g, P (glob g)).
Proof.
  split; [auto|].
  now intros (?&?&?) [].
Qed.
Lemma and_is_True_r {P Q} : Q -> P /\ Q <-> P.
Proof. tauto. Qed.
Lemma and_is_True_l {P Q} : P -> P /\ Q <-> Q.
Proof. tauto. Qed.
Lemma and_or_distr_r {P Q R} : (P \/ Q) /\ R <-> P /\ R \/ Q /\ R.
Proof. tauto. Qed.
Lemma and_or_distr_l {P Q R} : P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof. tauto. Qed.
Lemma iff_True {P} : (P <-> True) <-> P.
Proof. tauto. Qed.
Lemma iff_True_1 {P} : P -> (P <-> True).
Proof. tauto. Qed.
Lemma iff_True_2 {P} : (P <-> True) -> P.
Proof. tauto. Qed.







Definition mk_tg {R A} (tm : TensorMap R A) (es : EdgeSet) : TensorGraph :=
  (tm, es).


Section TensorGraphFacts.

Context {R : Type} {A : Type}.

Context `{SR : SemiRing R rO rI radd rmul req}.

(* Notation "0" := rO.
Notation "1" := rI. *)
Notation "x '==' y" := (req x y) (at level 70).
Infix "+" := radd.
Infix "*" := rmul.

Add Ring R : SR.(RSRth)
  (setoid SR.(Req_equiv) SR.(Req_ext)).

Let Req_equivalence : Equivalence req := Req_equiv.
Local Existing Instance Req_equivalence.

Let Radd_proper := Req_ext.(SRadd_ext) : Proper (req ==> req ==> req) radd.
Local Existing Instance Radd_proper.

Let Rmul_proper := Req_ext.(SRmul_ext) : Proper (req ==> req ==> req) rmul.
Local Existing Instance Rmul_proper.




Let TensorGraph := @TensorGraph R A.

Definition graph_tabs (tg : TensorGraph) : abstypecontext :=
  kmap (Pos.of_succ_nat) $
    map_imap (fun n (dt : DimensionlessTensor _) =>
    let node := mk_node tg n in
    let inarity := length node.1.2 in
    let outarity := length node.2 in
    Some (replicate (inarity + outarity) 0)) tg.1.

Definition graph_tl (tg : TensorGraph) : vartypecontext :=
  (gmaps_to_Pmap (set_to_map (fun k => (k, 0)) (inputs tg))
    (set_to_map (fun k => (k, 0)) (outputs tg))).

Definition graph_type_context (tg : TensorGraph) : typecontext :=
  mk_tc (graph_tabs tg) ∅ (graph_tl tg) [].



Lemma graph_semantics_WT tg :
  well_typed (graph_type_context tg) (graph_tensorlist_semantics tg).
Proof.
  apply tl_well_typed_correct.
  cbn.
  unfold tl_well_typed_aux.
  rewrite 2 Forall_fmap, Forall_forall.
  intros (n & dt) Hn%elem_of_map_to_list.
  cbn.
  unfold graph_tabs.
  rewrite lookup_kmap by apply _.
  rewrite map_lookup_imap, Hn.
  cbn.
  f_equal.
  rewrite !length_app, !length_fmap.
  apply (list_eq_same_length _ _ _ eq_refl).
  - rewrite !length_fmap, !length_app, !length_fmap, length_replicate.
    reflexivity.
  - rewrite !length_fmap, !length_app, !length_fmap.
    intros i x y Hi.
    rewrite list_lookup_fmap.
    destruct (replicate _ _ !! _) as [ri|] eqn:Hri; [|easy].
    apply lookup_replicate in Hri as [-> _].
    cbn.
    intros [= <-].
    intros Hhyp; symmetry; revert Hhyp.
    refine ((Forall_lookup (.= Some 0) _).1 _ i y).
    rewrite Forall_fmap.
    rewrite 3 Forall_app, 4 ! Forall_fmap.
    unfold compose; cbn.
    rewrite 4 Forall_filter.
    unfold i_internal_edges, i_external_edges.
    rewrite app_nil_r.
    split; (split; apply Forall_forall; intros (k, e) Hke%elem_of_enumerate;
      intros [= Hen];

      [rewrite <- fmap_reverse; rewrite list_lookup_fmap;
        rewrite pos_to_nat_pred_of_nat; cbn;
        destruct (reverse _  !! k) as [v|] eqn:Hv; [easy|
        apply lookup_lt_Some in Hke;
        apply lookup_ge_None in Hv;
        rewrite length_reverse in Hv; lia]|]);
    unfold graph_tl; rewrite lookup_gmaps_to_Pmap, lookup_set_to_map by easy;
    [exists e.1|exists e.2]; (split; [|cbn; f_equal; lia]).
    + unfold inputs.
      rewrite elem_of_filter, elem_of_list_to_set.
      apply elem_of_list_lookup_2 in Hke.
      unfold external_edges in Hke.
      apply elem_of_list_filter in Hke.
      pose proof (mk_is_Some _ _ Hn : is_key tg n) as Hkey.
      unfold not_internal, is_internal in Hke.
      split; [subst; tauto|].
      now apply elem_of_list_fmap_1.
    + unfold outputs.
      rewrite elem_of_filter, elem_of_list_to_set.
      apply elem_of_list_lookup_2 in Hke.
      unfold external_edges in Hke.
      apply elem_of_list_filter in Hke.
      pose proof (mk_is_Some _ _ Hn : is_key tg n) as Hkey.
      unfold not_internal, is_internal in Hke.
      split; [subst; tauto|].
      now apply elem_of_list_fmap_1.
Qed.

Context `{Summable A}.

Definition num_internals (tg : TensorGraph) : nat :=
  length (filter (is_internal tg) tg.2).

Definition num_externals (tg : TensorGraph) : nat :=
  length (filter (not_internal tg) tg.2).

Lemma fold_num_internals' tm es es' :
  length (filter (is_internal (mk_tg tm es')) es) =
  num_internals (mk_tg tm es).
Proof. reflexivity. Qed.

Definition abs_length_eq {A} : relation (Idx * list A * list A) :=
  fun '(f, low, up) '(f', low', up') =>
  f = f' /\ length low = length low' /\ length up = length up'.

Lemma mk_node_perm_eq_lengths (tm : TensorMap R A) es es' k :
  es ≡ₚ es' ->
  length (mk_node (mk_tg tm es) k).1.2 =
  length (mk_node (mk_tg tm es') k).1.2 /\
  length (mk_node (mk_tg tm es) k).2 =
  length (mk_node (mk_tg tm es') k).2.
Proof.
  intros Hes.
  cbn.
  change (is_internal (mk_tg tm es')) with (is_internal (mk_tg tm es)).
  change (not_internal (mk_tg tm es')) with (not_internal (mk_tg tm es)).
  rewrite 4 length_app.
  split; f_equal; rewrite 2 length_fmap;
      (rewrite <- (length_fmap snd);
      (change (λ e : Ty * (Ty * Ty), e.2.2 = k) with
        ((λ e : Ty * Ty, e.2 = k) ∘ @snd Ty _) ||
        change (λ e : Ty * (Ty * Ty), e.2.1 = k) with
        ((λ e : Ty * Ty, e.1 = k) ∘ @snd Ty _));
      etransitivity; [symmetry; apply (f_equal length);
        refine (list_filter_fmap snd _)|];
      rewrite fmap_imap; unfold compose at 1; cbn -[compose];
      rewrite imap_to_fmap, list_fmap_id;

      (* rewrite imap_snds by (now rewrite length_fmap, length_seq); *)
      rewrite <- (length_fmap (@snd _ (_*_)));
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)];
      rewrite fmap_imap; unfold compose at 1; cbn -[compose];
      rewrite imap_to_fmap, list_fmap_id);
    rewrite <- Hes;
    reflexivity.
Qed.






(*
Lemma mk_node_perm_eq (tm : TensorMap R A) es es' fint fext k :
  posperm (lengthP (filter (is_internal (mk_tg tm es)) es)) fint ->
  ppermute fint (filter (is_internal (mk_tg tm es)) es) =
  filter (is_internal (mk_tg tm es')) es' ->

  posperm (lengthP (filter (not_internal (mk_tg tm es')) es')) fext ->
  ppermute fext (filter (not_internal (mk_tg tm es)) es) =
  filter (not_internal (mk_tg tm es')) es' ->
  abs_perm
    ((mk_node (mk_tg tm es) k))
    (relabel_abs (var_map fint fext Datatypes.id) (mk_node (mk_tg tm es') k)).
Proof.
  intros Hfint Hfint_pperm Hfext Hfext_pperm.
  cbn.
  split; [reflexivity|].
  rewrite 2 fmap_app.
  split; f_equiv.
  - apply posperm_imap_eq' in Hfint as Hfint'.
    unfold EdgeSet in *.
    setoid_rewrite Hfint'.
    rewrite ppermute_permutation. 2:{
      rewrite lengthN_correct_rev, length_zip, length_fmap,
        length_seq, length_ppermute, Nat.min_id, <- lengthN_correct_rev.
      now apply posperm_inv_posperm.
    }
    setoid_rewrite <- Hfint_pperm.
    rewrite posperm_imap_eq by easy.
    symmetry.
    rewrite ppermute_permutation. 2:{
      now rewrite lengthN_correct_rev, length_zip, length_fmap,
        length_seq, Nat.min_id, <- lengthN_correct_rev.
    }
    rewrite zip_with_ppermute_r by now
      rewrite ?lengthN_correct_rev, length_fmap, length_seq,
        <- ?lengthN_correct_rev.


    apply eq_reflexivity.


    apply list_eq_Forall2.
    rewrite 2 Forall2_fmap_l, Forall2_fmap_r.
    apply Forall2







    symmetry.
    rewrite lengthN_correct_rev, length_fmap, length_seq, <- lengthN_correct_rev.
    symmetry.

    apply (list_eq_same_length _ _ _ eq_refl). 1:{
      rewrite !length_fmap.
      rewrite <- (length_fmap snd).
      change (@filter (Ty * (Ty * Ty)) ?B ?H _) with
        (@filter (Ty * (Ty * Ty)) B H ((λ e, e.2 = k) ∘ snd)).
      etransitivity; [symmetry; apply (f_equal length);
        refine (list_filter_fmap snd _)|].
      rewrite snd_zip by now rewrite length_fmap, length_seq.
      rewrite <- (length_fmap (@snd _ (_*_))).
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)].
      rewrite <- ppermute_fmap.
      rewrite snd_zip by now rewrite length_ppermute, length_fmap, length_seq.
      now rewrite ppermute_permutation by easy.
    }

    intros i x y Hi.
    rewrite ! list_lookup_fmap.


    rewrite <- list_fmap_compose.
    unfold compose; cbn.
    evar (n : nat);
    replace (length _) with n. 2:{

      rewrite length_fmap.
      rewrite <- (length_fmap snd).
      change (@filter (Ty * (Ty * Ty)) ?B ?H _) with
        (@filter (Ty * (Ty * Ty)) B H ((λ e, e.2 = k) ∘ snd)).
      etransitivity; [|apply (f_equal length);
        refine (list_filter_fmap snd _)].
      rewrite snd_zip by now rewrite length_fmap, length_seq, length_ppermute.
      rewrite ppermute_permutation by easy.
      unfold n; reflexivity.
    }
    subst n.
    intros i x y Hi.
    rewrite 2 list_lookup_fmap.

    list_lookup filter

  intros Hes.
  cbn.
  rewrite !length_app, !length_fmap.
  split; f_equal.

  erewrite <- (length_fmap snd).
  epose proof (fun l => list_filter_fmap snd (P:= λ e, e.2 = k)
    l) as Hrw.
  etransitivity; [apply (f_equal length); symmetry; apply Hrw|].

  rewrite <- Hrw.

  1, 3: rewrite <- Hes at 2.
  cbv delta [mk_node] beta.
*)

Lemma graph_mabs_perm_eq (tm : TensorMap R A) es es' :
  es ≡ₚ es' ->
  graph_mabs (mk_tg tm es) = graph_mabs (mk_tg tm es').
Proof.
  intros Hes.
  unfold graph_mabs.
  f_equal.
  cbn [fst mk_tg].
  apply map_imap_ext.
  intros k.
  apply option_fmap_ext.
  intros dt.
  f_equal.
  pose proof (mk_node_perm_eq_lengths tm es es' k Hes) as (-> & ->).
  reflexivity.
Qed.

Definition type {A} (a : A) : Type := A.
Definition domtype {A B} (f : A -> B) : Type := A.
Definition codomtype {A B} (f : A -> B) : Type := B.
#[global] Arguments type /.
#[global] Arguments domtype /.
#[global] Arguments codomtype /.

Ltac2 empty_flags () : Std.red_flags := {
  Std.rStrength := Std.Norm;
  Std.rBeta := Init.false;
  Std.rMatch := Init.false;
  Std.rFix := Init.false;
  Std.rCofix := Init.false;
  Std.rZeta := Init.false;
  Std.rDelta := Init.false;
  Std.rConst := [];
}.

Import Ltac2.Notations.

Notation "'right_uncompose' fg g" :=
  ((* let fpat :=  *)
    ltac2:(
      let fg := Constr.pretype fg in
      let g := Constr.pretype g in  (* TODO: Improve with expected type from fg *)
      let tf := match! Constr.type fg with
        | ?a -> _ => a
        end in
      let res := Constr.in_context ident:(x) tf (fun () =>
        let fg' := Std.eval_hnf fg in
        let fgx := Std.eval_cbv {(empty_flags()) with Std.rBeta := Init.true}
            '($fg' &x) in
        let pat := Std.eval_pattern [('($g &x), Std.AllOccurrences)] fgx in
        match! pat with
        | ?f _ => exact $f
        end) in
      match Constr.Unsafe.kind res with
      | Constr.Unsafe.Lambda _ body =>
        ltac1:(r |- let r' := eval cbn in r in exact r') (Ltac1.of_constr body)
      | _ => Control.throw (Init.Tactic_failure Init.None)
      end
        )) (at level 10, fg at level 0, g at level 0).

(* Goal True.
Check (right_uncompose (λ (x : nat * (nat * nat)), x.2.2) (@snd nat (nat * nat))). *)

Lemma graph_semantics_abstracts_is_Some (tm : TensorMap R A) es mi mo k
  (mr': Vlist graph_V (replicate (num_internals (mk_tg tm es)) 0))
  (Hmr': WF_Vlist graph_V mr') :
  k ∈ dom tm ->
  is_Some
  (join_list
     (get_var graph_V ∅ (graph_ml mi mo) (reverse mr') <$>
      ((mk_internal_var <$>
        filter (λ e : Ty * (Ty * Ty), e.2.2 = k)
          (imap pair
             (filter (is_internal (mk_tg tm es)) es))) ++
       (mk_external_var false <$>
        filter (λ e : Ty * (Ty * Ty), e.2.2 = k)
          (imap pair
             (filter (not_internal (mk_tg tm es)) es)))) ++
      (mk_internal_var <$>
       filter (λ e : Ty * (Ty * Ty), e.2.1 = k)
         (imap pair (filter (is_internal (mk_tg tm es)) es))) ++
      (mk_external_var true <$>
       filter (λ e : Ty * (Ty * Ty), e.2.1 = k)
         (imap pair
            (filter (not_internal (mk_tg tm es)) es))))
   ≫= λ args : list (Vval graph_V),
        graph_mabs (mk_tg tm es) !! Pos.of_succ_nat k
        ≫= λ fval : Vfunc graph_V,
             Vapplys graph_V fval args) <->
  ((forall i, i ∈ (filter (λ e, e.2 = k /\ ~ is_key (mk_tg tm es) e.1) es).*1 ->
    (i:>nat) ∈ dom mi) /\
  (forall o, o ∈ (filter (λ e, e.1 = k /\ ~ is_key (mk_tg tm es) e.2) es).*2 ->
    (o:>nat) ∈ dom mo)) /\ True.
Proof.
  intros Hkdom.
  unfold graph_mabs.
  rewrite lookup_kmap by apply _.
  rewrite map_lookup_imap.
  apply elem_of_dom in Hkdom as [fk Hfk].
  cbn [fst mk_tg].
  rewrite Hfk.
  cbn [mbind option_bind].
  rewrite bind_is_Some.
  rewrite join_list_is_Some.
  apply and_iff_from_l.
  - rewrite not_elem_of_list_fmap.
    rewrite <- Forall_forall.
    rewrite Permutation_swap_app_app.
    rewrite <- fmap_app.
    change (mk_external_var false) with
      (loc ∘ (λ e : Ty * (Ty * Ty), bcons false (Pos.of_succ_nat e.2.1))).
    change (mk_external_var true) with
      (loc ∘ (λ e : Ty * (Ty * Ty), bcons true (Pos.of_succ_nat e.2.2))).
    rewrite 2 list_fmap_compose, <- fmap_app.
    rewrite Forall_app.
    rewrite and_is_True_l. 2:{
      rewrite Forall_fmap, Forall_forall.
      intros x.
      rewrite elem_of_app, 2 elem_of_list_filter.
      rewrite <- and_or_distr_r.
      intros [Hxk (i & e & -> & Hlook)%elem_of_lookup_imap].
      cbn.
      apply not_eq_None_Some.
      apply lookup_lt_is_Some.
      rewrite length_reverse.
      apply Forall2_length in Hmr' as Hlen.
      unfold Vval.
      rewrite <- Hlen, length_replicate.
      unfold num_internals.
      apply lookup_lt_Some in Hlook.
      cbn; lia.
    }
    rewrite Forall_fmap.
    rewrite Forall_app, 2 Forall_fmap.
    unfold compose; cbn.
    unfold graph_ml.
    setoid_rewrite lookup_fmap.
    setoid_rewrite lookup_gmaps_to_Pmap.
    setoid_rewrite pos_to_nat_pred_of_nat.
    f_equiv.
    + change (Forall _ ?l) with
        (Forall (((λ x : Ty,
        @mk_Vval graph_V 0 <$> mi !! x ≠ None)∘ fst) ∘ snd) l) at 1.
      rewrite <- Forall_fmap.
      change (filter (H:=?H) _ ?l) with
        (filter (H:=H) ((λ e, e.2 = k) ∘ snd) l) at 1.
      remember (filter _ _).*2 as l eqn:Hl.
      pose proof (eq_trans Hl (eq_sym (list_filter_fmap snd _))) as Hl'.
      clear Hl.
      subst l.
      rewrite fmap_imap.
      unfold compose at 2.
      cbn.
      rewrite imap_to_fmap, list_fmap_id.
      rewrite <- Forall_fmap.
      rewrite <- Forall_forall.
      setoid_rewrite list_filter_filter.
      erewrite list_filter_iff; [apply Forall_iff|].
      * intros x.
        now rewrite not_eq_None_Some, fmap_is_Some, elem_of_dom.
      * intros (i, j).
        cbn.
        unfold not_internal, is_internal.
        cbn.
        apply and_iff_from_l; [easy|].
        intros -> _.
        enough (is_key (mk_tg tm es) k) by tauto.
        apply elem_of_dom.
        refine (elem_of_dom_2 _ _ _ Hfk).
    + change (Forall _ ?l) with
        (Forall (((λ x : Ty,
        @mk_Vval graph_V 0 <$> mo !! x ≠ None) ∘ snd) ∘ snd) l) at 1.
      rewrite <- Forall_fmap.
      change (filter (H:=?H) _ ?l) with
        (filter (H:=H) ((λ e, e.1 = k) ∘ snd) l) at 1.
      remember (filter _ _).*2 as l eqn:Hl.
      pose proof (eq_trans Hl (eq_sym (list_filter_fmap snd _))) as Hl'.
      clear Hl.
      subst l.
      rewrite fmap_imap.
      unfold compose at 2.
      cbn.
      rewrite imap_to_fmap, list_fmap_id.
      rewrite <- Forall_fmap.
      rewrite <- Forall_forall.
      setoid_rewrite list_filter_filter.
      erewrite list_filter_iff; [apply Forall_iff|].
      * intros x.
        now rewrite not_eq_None_Some, fmap_is_Some, elem_of_dom.
      * intros (i, j).
        cbn.
        unfold not_internal, is_internal.
        cbn.
        apply and_iff_from_l; [easy|].
        intros -> _.
        enough (is_key (mk_tg tm es) k) by tauto.
        apply elem_of_dom.
        refine (elem_of_dom_2 _ _ _ Hfk).
  - intros Hnone_nin [Hmi Hmo].
    apply iff_True_1.
    intros vs Hvs%join_list_Some.
    apply Vapplys_is_Some.
    cbn -[mk_node].
    apply (list_eq_same_length _ _ _ eq_refl).
    1: {
      apply (f_equal length) in Hvs.
      rewrite 2 length_fmap in Hvs.
      rewrite length_fmap, length_replicate.
      unfold Vval in *.
      rewrite <- Hvs.
      cbn.
      rewrite <- length_app.
      reflexivity.
    }
    intros i x y Hi.
    rewrite length_fmap in Hi.
    rewrite lookup_replicate.
    rewrite list_lookup_fmap.
    intros [-> Hi'].
    apply (f_equal (.!! i)) in Hvs.
    rewrite ! list_lookup_fmap in Hvs.
    unfold Vval in *.
    destruct (vs !! i) as [vi|] eqn:Hvi in *; [|easy].
    cbn.
    intros [= <-].
    symmetry.
    cbn in Hvs.
    rewrite fmap_Some in Hvs.
    destruct Hvs as (v & Hv & HSvi).
    change (projT1 vi) with (from_option projT1 0 (Some vi)).
    rewrite HSvi.
    apply elem_of_list_lookup_2 in Hv as Hin.
    rewrite Permutation_swap_app_app, <- fmap_app in Hin.
    rewrite 2 elem_of_app, 3 elem_of_list_fmap in Hin.
    destruct Hin as [((n&?&?) & -> & Hin) |[((?&?&?) & -> & Hin) | ((?&?&?) & -> & Hin)]].
    + cbn.
      rewrite pos_to_nat_pred_of_nat.
      destruct (reverse _ !! _) as [mr'i|] eqn:Hmr'i; [|easy].
      apply elem_of_list_lookup_2 in Hmr'i as Hn.
      pose proof Hmr' as HWF.
      unfold WF_Vlist in HWF.
      rewrite Forall2_lookup in HWF.
      specialize (HWF (length mr' - S n)).
      pose proof Hmr'i as Hmri.
      rewrite reverse_lookup in Hmri by 
        now apply lookup_lt_Some in Hmr'i; rewrite length_reverse in Hmr'i.
      setoid_rewrite Hmri in HWF.
      destruct (replicate _ _ !! _) as [ri|] eqn:Hrep in HWF; [|easy].
      apply lookup_replicate in Hrep as [-> ?].
      inversion HWF; subst.
      cbn.
      easy.
    + cbn.
      unfold graph_ml.
      rewrite lookup_fmap.
      destruct (_ !! _) in |- *; reflexivity.
    + cbn.
      unfold graph_ml.
      rewrite lookup_fmap.
      destruct (_ !! _) in |- *; reflexivity.
Qed.


Lemma num_internals_perm_eq tm es es' : es ≡ₚ es' ->
  num_internals (mk_tg tm es) = num_internals (mk_tg tm es').
Proof.
  intros Hes.
  unfold num_internals.
  cbn.
  rewrite <- Hes at 2.
  reflexivity.
Qed.

(* 
Lemma graph_semantics_perm_eq_aux (tm : TensorMap R A) es es' :
  es ≡ₚ es' ->
  forall mi mo,
  graph_map_semantics (mk_tg tm es) mi mo ==
  graph_map_semantics (mk_tg tm es') mi mo.
Proof.
  intros Hes mi mo.
  cbn.
  rewrite 2 fmap_const.
  rewrite <- (graph_mabs_perm_eq tm es es' Hes).

  change (is_internal (mk_tg tm es')) with (is_internal (mk_tg tm es)).
  rewrite <- Hes at 1.
  set (l := length _).
  subst l.
  rewrite fold_num_internals'.


  apply tl_total_semantics_aux_ext_abs.

  intros mr' Hmr'.

  rewrite Forall2_fmap.
  apply Forall_Forall2_diag.
  rewrite Forall_forall.
  intros k Hk.
  rewrite rev_append_reverse, app_nil_r.
  cbn.

  apply default_is_Some_ext_mor; [|reflexivity|].
  - assert (Hkdom : k ∈ dom tm) by now rewrite dom_alt, elem_of_list_to_set.

    rewrite graph_semantics_abstracts_is_Some by easy.
    rewrite (graph_mabs_perm_eq _ _ _ Hes).
    rewrite graph_semantics_abstracts_is_Some; [..|easy]. 2:{
      rewrite <- (num_internals_perm_eq _ _ _ Hes).
      exact Hmr'.
    }
    f_equiv.
    change (is_key (mk_tg tm es')) with (is_key (mk_tg tm es)).
    f_equiv; apply forall_iff; intros ?.
    f_equiv.
    setoid_rewrite <- Hes.

  f_equal.


  induction Hes; [reflexivity|..].


  setoid_rewrite fold_num_internals'.
  rewrite <- Hes at 3.
  rewrite fold_num_internals'.

  rewrite 2 tl_total_semantics_aux_alt_Vlist.
  setoid_rewrite rev_append_rev.
  setoid_rewrite app_nil_r.


  pose proof Hes as Hes'.

  apply (filter_Permutation (is_internal (mk_tg tm es))) in Hes' as Hesint.

  apply perm_exists_posperm in Hesint as Hf.
  destruct Hf as (f & Hfperm & Hfppermute & Hlook).

  eapply sum_of_relabel'_r2l with (ppermute f).
  2:{
    unfold sum_elements; cbn.
    rewrite ppermute_posperm_permutes_Vlist_elements. 2:{
      now rewrite lengthN_correct_rev, length_replicate, <- lengthN_correct_rev.
    }
    rewrite ppermute_replicate.
    reflexivity.
  }
  intros ml Hml%elem_of_Vlist_elements.

  apply tl_total_semantics_aux_ext_base_mr.
  unshelve (instantiate (1:=_)).
  unfold Vlist.
  exact



  eexists; cbn -[reverse].
  rewrite !fmap_const.
  rewrite reverse_replicate, lengthN_correct_rev, length_replicate.
  replace (N.succ_pos _) with (Pos.of_succ_nat (num_internals (mk_tg tm es)))
    by lia. *)

(* 
Lemma graph_semantics_perm_eq_aux (tm : TensorMap R A) es es' :
  es ≡ₚ es' ->
  forall mi mo,
  graph_tensorlist_semantics (mk_tg tm es) =tl=
  graph_tensorlist_semantics (mk_tg tm es').
Proof.
  intros Hes.
  eexists; cbn -[reverse].
  rewrite !fmap_const.
  remember (num_internals (mk_tg tm es)) as x eqn:Hx.
  pose proof Hx as Hx'.
  cbn in Hx'.
  rewrite <- Hx', Hx.
  unfold is_internal, is_key in Hx' |- *.
  cbn -[reverse num_internals] in Hx' |- *.
  rewrite <- Hes at 1.
  rewrite <- Hx', Hx.
  clear x Hx Hx'.
  rewrite reverse_replicate, lengthN_correct_rev, length_replicate.
  replace (N.succ_pos _) with (Pos.of_succ_nat (num_internals (mk_tg tm es)))
    by lia.
  apply (filter_Permutation (is_internal (mk_tg tm es))) in Hes as Hesint.




*)

End TensorGraphFacts.