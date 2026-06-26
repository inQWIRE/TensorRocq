(* A file containing rewriting theory, especially for rewriting in
  autonomous and frobenius categories *)

From TensorRocq Require Import CospanHyperGraph.Definitions
  Isomorphism.IsoAux Isomorphism.Testing CospanHyperGraph.Matching
  Props.Prop.Props
  Props.Prop.PropsGraphs.
  (* Props.Prop.PropGraphTerm. *)



(* FIXME: Move?!?!?!? *)

Import StackComposeCorrect.

#[export] Instance compose_graphs_alt_cohg_vert_eq {T}
  {n m o} : Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@compose_graphs_alt T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  unfold compose_graphs_alt.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_graphs_alt_struct_isomorphic `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@compose_graphs_alt T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  unfold compose_graphs_alt.
  apply add_top_loops_struct_isomorphic.
  now apply swapped_stack_graphs_struct_isomorphic.
Qed.

Import Facts.

Lemma proper_cohg_syntactic_eq_of_struct_iso_eq_binary `{Equiv T1, Equivalence T1 equiv,
  Equiv T2, Equivalence T2 equiv, Equiv T3, Equivalence T3 equiv} {n1 m1 n2 m2 n3 m3}
  (f : CospanHyperGraph T1 n1 m1 -> CospanHyperGraph T2 n2 m2 ->
    CospanHyperGraph T3 n3 m3) :
  Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic) f ->
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) f ->
  Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq) f.
Proof.
  intros Hfiso Hfcohg.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  induction Hcohg1 as [cohg1 cohg1' fv1 fe1 Hfv1 Hfe1 Hverteq1].
  rewrite <- (subrel'' struct_isomorphic (norm_verts_vert_eq cohg1)).
  rewrite (Hverteq1).
  rewrite (subrel'' struct_isomorphic (norm_verts_vert_eq _)).
  rewrite <- (subrel'' struct_isomorphic (iso_relabel_reindex _ _ _)) by done.
  induction Hcohg2 as [cohg2 cohg2' fv2 fe2 Hfv2 Hfe2 Hverteq2].
  rewrite <- (subrel'' struct_isomorphic (norm_verts_vert_eq cohg2)).
  rewrite (Hverteq2).
  rewrite (subrel'' struct_isomorphic (norm_verts_vert_eq _)).
  rewrite <- (subrel'' struct_isomorphic (iso_relabel_reindex _ _ _)) by done.
  done.
Qed.

#[export] Instance compose_graphs_alt_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@compose_graphs_alt T n m o).
Proof.
  apply proper_cohg_syntactic_eq_of_struct_iso_eq_binary; apply _.
Qed.

#[export] Instance compose_graphs_cohg_vert_eq {T}
  {n m o} : Proper (cohg_vert_eq ==> cohg_vert_eq ==> cohg_vert_eq)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  do 2 rewrite <- compose_graphs_alt_correct.
  now do 2 f_equiv.
Qed.

#[export] Instance compose_graphs_struct_isomorphic `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (struct_isomorphic ==> struct_isomorphic ==> struct_isomorphic)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  do 2 rewrite <- compose_graphs_alt_correct.
  now apply compose_graphs_alt_struct_isomorphic.
Qed.

#[export] Instance compose_graphs_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  rewrite <- 2 compose_graphs_alt_correct.
  now apply compose_graphs_alt_cohg_syntactic_eq.
Qed.

#[export] Instance stack_graphs_cohg_syntactic_eq `{Equiv T, Equivalence T equiv}
  {n m o p} : Proper (cohg_syntactic_eq ==> cohg_syntactic_eq ==> cohg_syntactic_eq)
    (@stack_graphs T n m o p).
Proof.
  apply proper_cohg_syntactic_eq_of_iso_vert_eq_binary; apply _.
Qed.




From TensorRocq Require Import ProQuote.
From TensorRocq Require Import CospanHyperGraph.Hom.

(* FIXME: Move to Definitions *)
Lemma cohg_eq_ind `{Equiv T} {n m} (P : CospanHyperGraph T n m -> CospanHyperGraph T n m -> Prop)
  (HP : forall ins outs verts he he', map_equiv he he' ->
    P (mk_cohg (mk_hg he verts) ins outs) (mk_cohg (mk_hg he' verts) ins outs)) :
  forall cohg cohg', cohg ≡ₕ cohg' -> P cohg cohg'.
Proof.
  intros [[he verts] ins outs] [[he' verts'] ins' outs'] ([= <-] & [= <-] & [Hhe [= <-]]).
  apply HP, Hhe.
Qed.

Lemma cohg_eq_ind' `{Equiv T} {n m} (P : CospanHyperGraph T n m -> CospanHyperGraph T n m -> Prop)
  (HP : forall ins outs hg hg', hg ≡ hg' ->
    P (mk_cohg hg ins outs) (mk_cohg hg' ins outs)) :
  forall cohg cohg', cohg ≡ₕ cohg' -> P cohg cohg'.
Proof.
  intros [hg ins outs] [hg' ins' outs'] ([= <-] & [= <-] & Hhg).
  apply HP, Hhg.
Qed.

#[export] Instance compose_graphs_aux_cohg_eq `{Equiv T} {n m o} :
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (@compose_graphs_aux T n m o).
Proof.
  refine (cohg_eq_ind _ _).
  intros ins1 outs1 verts1 he1 he1' Hhe1.
  refine (cohg_eq_ind _ _).
  intros ins2 outs2 verts2 he2 he2' Hhe2.
  unfold compose_graphs_aux.
  cbn.
  f_equiv.
  split_and!; [done..|].
  cbn.
  split; cbn.
  - now apply fin_maps.union_proper.
  - do 3 f_equal;
    eapply vertices_hg_equiv; split; done.
Qed.


#[export] Instance compose_graphs_cohg_eq `{Equiv T} {n m o} :
  Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (@compose_graphs T n m o).
Proof.
  intros cohg1 cohg1' Hcohg1 cohg2 cohg2' Hcohg2.
  rewrite 2 compose_graphs_to_compose_graphs_aux.
  now apply compose_graphs_aux_cohg_eq; do 2 f_equiv.
Qed.


(* FIXME: Move *)
Lemma PRO_graph_semantics_equiv_cohg_eq `{StructGraphable Struct T,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv}
  {GraphSProper : forall n m, Proper ((≡@{Struct n m}) ==> cohg_eq) graph_of_struct}
  {n m} :
  Proper ((≡@{PRO Struct T n m}) ==> cohg_eq) PRO_graph_semantics.
Proof.
  intros p p' Hp.
  induction Hp.
  - done.
  - cbn.
    now f_equiv.
  - cbn.
    now apply graph_of_tensor_cohg_eq.
  - cbn.
    now apply compose_graphs_cohg_eq.
  - cbn.
    now apply stack_graphs_cohg_eq.
Qed.

Lemma PRO_graph_semantics_equiv_cohg_syntactic_eq `{StructGraphable Struct T,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv}
  {GraphSProper : forall n m, Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) graph_of_struct}
  {n m} :
  Proper ((≡@{PRO Struct T n m}) ==> cohg_syntactic_eq) PRO_graph_semantics.
Proof.
  intros p p' Hp.
  induction Hp.
  - done.
  - cbn.
    now f_equiv.
  - cbn.
    now apply (subrel' cohg_eq), graph_of_tensor_cohg_eq.
  - cbn.
    now apply compose_graphs_cohg_syntactic_eq.
  - cbn.
    now apply stack_graphs_cohg_syntactic_eq.
Qed.

Lemma PRO_graph_semantics_map_full_gen `{StructGraphable Struct T,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv}
  `{StructGraphable Struct' T',
  EqStruct' : forall n m, Equiv (Struct' n m),
  EqT' : Equiv T', EquivT' : Equivalence T' equiv}
  (R : forall n m, relation (CospanHyperGraph T' n m))
  (HR : forall n m, Equivalence (R n m))
  (HRcomp : forall n m o, Proper (R n m ==> R m o ==> R n o) (@compose_graphs T' n m o))
  (HRstack : forall n m o p, Proper (R n m ==> R o p ==> R _ _) (@stack_graphs T' n m o p))
  (fs : forall n m, Struct n m -> Struct' n m)
  (ft : T -> T')
  (Hfs : forall n m s, R n m (graph_apply_hom ft (graph_of_struct s)) (graph_of_struct (fs n m s)))
  {n m} (p : PRO Struct T n m) :
  R n m (PRO_graph_semantics (map_PRO fs ft p))
    (graph_apply_hom ft (PRO_graph_semantics p)).
Proof.
  induction p.
  - done.
  - cbn.
    rewrite graph_apply_hom_compose_graphs.
    f_equiv; done.
  - cbn.
    rewrite graph_apply_hom_stack_graphs.
    f_equiv; done.
  - cbn.
    done.
  - cbn.
    done.
Qed.


Lemma PRO_graph_semantics_map_cohg_syntactic_eq `{StructGraphable Struct T,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv}
  `{StructGraphable Struct' T',
  EqStruct' : forall n m, Equiv (Struct' n m),
  EqT' : Equiv T', EquivT' : Equivalence T' equiv}
  (fs : forall n m, Struct n m -> Struct' n m)
  (ft : T -> T')
  (Hfs : forall n m s, graph_apply_hom ft (graph_of_struct s) ≡ₛ graph_of_struct (fs n m s))
  {n m} (p : PRO Struct T n m) :
  PRO_graph_semantics (map_PRO fs ft p) ≡ₛ
    graph_apply_hom ft (PRO_graph_semantics p).
Proof.
  apply PRO_graph_semantics_map_full_gen.
  - apply _.
  - intros; apply compose_graphs_cohg_syntactic_eq.
  - intros; apply stack_graphs_cohg_syntactic_eq.
  - done.
Qed.

(* FIXME: Move to PropsGraphs *)
Class FreeStructGraphable (Struct : Mor nat)
  `{StructG : forall T, StructGraphable Struct T} :=
  graph_of_struct_free T {n m} (s : Struct n m) :
    graph_of_struct (T:=T) s = graph_apply_hom (Empty_set_rect _) (graph_of_struct s).

Lemma free_struct_graphable_empty `{FreeGraphS : FreeStructGraphable Struct}
  T {n m} (s : Struct n m) : hyperedges (graph_of_struct (T:=T) s) = ∅.
Proof.
  rewrite graph_of_struct_free.
  cbn.
  apply fmap_empty_iff.
  apply map_empty.
  intros i.
  destruct (_ !! i) as [[[]]|]; done.
Qed.

Lemma graph_apply_hom_free_graph_of_struct `{FreeGraphS : FreeStructGraphable Struct}
  {T T'} (f : T -> T') {n m} (s : Struct n m) :
    graph_apply_hom f (graph_of_struct s) = graph_of_struct s.
Proof.
  rewrite (graph_of_struct_free T), (graph_of_struct_free T').
  rewrite graph_apply_hom_compose.
  apply graph_apply_hom_ext; done.
Qed.

#[export] Instance morunion_free_graphable
  `{FreeGraphS : FreeStructGraphable Struct,
    FreeGraphS' : FreeStructGraphable Struct'} : FreeStructGraphable (MorUnion Struct Struct').
Proof.
  intros T n m [s|s]; cbn; apply graph_of_struct_free.
Qed.

#[export] Instance monoidal_free_graphable : FreeStructGraphable Monoidal.
Proof.
  intros T n m []; done.
Qed.

#[export] Instance symmetry_free_graphable : FreeStructGraphable Symmetry.
Proof.
  intros T n m []; done.
Qed.

#[export] Instance autonomy_free_graphable : FreeStructGraphable Autonomy.
Proof.
  intros T n m []; done.
Qed.

#[export] Instance frobenial_free_graphable : FreeStructGraphable Frobenial.
Proof.
  intros T n m []; done.
Qed.


Class SubStructGraphable (Struct Struct' : Mor nat) (T : Type) `{Equiv T}
  `{!SubStruct Struct Struct'}
  `{StructGraphable Struct T, StructGraphable Struct' T} :=
  graph_of_struct_includeStruct : forall {n m} (s : Struct n m),
  graph_of_struct (includeStruct s :> Struct' n m) ≡ₛ
  graph_of_struct s.

#[export] Instance substruct_graphable_refl `{Equiv T, Equivalence T equiv}
  `{StructGraphable Struct T} :
  SubStructGraphable Struct Struct T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_monoidal_symmetricg
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Monoidal SymmetricG T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_monoidal_autonomous
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Monoidal Autonomous T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_monoidal_frobenius
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Monoidal Frobenius T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_symmetry_symmetricg
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Symmetry SymmetricG T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_symmetry_autonomous
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Symmetry Autonomous T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_symmetry_frobenius
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Symmetry Frobenius T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_autonomy_autonomous
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Autonomy Autonomous T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_autonomy_frobenius
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Autonomy Frobenius T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_frobenial_frobenius
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Frobenial Frobenius T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_symmetricg_autonomous
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable SymmetricG Autonomous T.
Proof.
  intros n m s.
  done.
Qed.

#[export] Instance substruct_graphable_autonomous_frobenius
  `{Equiv T, Equivalence T equiv} :
  SubStructGraphable Autonomous Frobenius T.
Proof.
  intros n m s.
  done.
Qed.




Lemma PRO_graph_semantics_denote `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv,
  EqT' : Equiv T', EquivT' : Equivalence T' equiv}
  (ft : T -> T')
  {n m} (p : PRO Struct T n m) :
  PRO_graph_semantics (PRO_denote ft p) =
    graph_apply_hom ft (PRO_graph_semantics p).
Proof.
  unfold PRO_denote.
  apply PRO_graph_semantics_map_full_gen; [cbn; apply _..|].
  intros ? ? s.
  apply graph_apply_hom_free_graph_of_struct.
Qed.

Lemma PRO_quote_correct_graph_semantics `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EqT : Equiv T, EquivT : Equivalence T equiv,
  EqT' : Equiv T', EquivT' : Equivalence T' equiv}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  (ft : T -> T') {Hft : Proper (equiv ==> equiv) ft}
  {n m} (qp : PRO Struct T n m) p : PRO_quote ft qp p ->
  PRO_graph_semantics p ≡ₛ graph_apply_hom ft (PRO_graph_semantics qp).
Proof.
  unfold PRO_quote.
  intros Hp.
  erewrite <- PRO_graph_semantics_equiv_cohg_syntactic_eq by apply Hp.
  now rewrite PRO_graph_semantics_denote.
Qed.

















Local Existing Instance Countable_Equiv.


Record LawfulPRORewritingRelation {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
   := mk_LawfulPRORewritingRelation {
  pro_rewriting_relation n m : relation (PRO Struct T n m);
  pro_rewriting_domain {n m} : PRO Struct T n m -> Prop;
  pro_rewriting_domain_dec {n m} (p : PRO Struct T n m) :: Decision (pro_rewriting_domain p);
  pro_rewriting_domain_id n : pro_rewriting_domain (Pid n);
  pro_rewriting_domain_struct {n m} (s : Struct n m) : pro_rewriting_domain ([str s]);
  pro_rewriting_domain_compose {n m o} (p : PRO Struct T n m) (q : PRO Struct T m o) :
    pro_rewriting_domain p -> pro_rewriting_domain q -> pro_rewriting_domain (p ;; q);
  pro_rewriting_domain_stack {n m n' m'} (p : PRO Struct T n m) (q : PRO Struct T n' m') :
    pro_rewriting_domain p -> pro_rewriting_domain q -> pro_rewriting_domain (p * q);
  (* pro_rewriting_relation_equiv {n m} :: Equivalence (pro_rewriting_relation n m); *)
  pro_rewriting_relation_refl {n m} (p : PRO Struct T n m) :
    pro_rewriting_domain p -> pro_rewriting_relation n m p p;
  pro_rewriting_relation_symm {n m} :: Symmetric (pro_rewriting_relation n m);
  pro_rewriting_relation_trans {n m} :: Transitive (pro_rewriting_relation n m);
  pro_rewriting_relation_graph_syntax_l {n m} (p p' q : PRO Struct T n m) :
    pro_rewriting_domain p' ->
    PRO_graph_semantics p ≡ₛ PRO_graph_semantics p' ->
    pro_rewriting_relation n m p q ->
    pro_rewriting_relation n m p' q;
  pro_rewriting_relation_compose {n m o} ::
    Proper (pro_rewriting_relation n m ==> pro_rewriting_relation m o
    ==> pro_rewriting_relation n o) Pcompose;
  pro_rewriting_relation_stack {n m n' m'} ::
    Proper (pro_rewriting_relation n m ==> pro_rewriting_relation n' m'
    ==> pro_rewriting_relation (n + n') (m + m')) Pstack;
}.

Coercion pro_rewriting_relation : LawfulPRORewritingRelation >-> Funclass.

Global Arguments LawfulPRORewritingRelation (_ _) {_ _ _} : assert.

Global Arguments pro_rewriting_relation {_ _ _ _ _} {_} {_ _} _ _ : assert.


Lemma pro_rewriting_relation_graph_syntax_r `{StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  {n m} (p q q' : PRO Struct T n m) :
    pro_rewriting_domain R q' ->
    R n m p q ->
    PRO_graph_semantics q ≡ₛ PRO_graph_semantics q' ->
    R n m p q'.
Proof.
  intros Hq' Hqp%symmetry Hqq'.
  apply (pro_rewriting_relation_graph_syntax_l R q q' p Hq' Hqq') in Hqp.
  now symmetry.
Qed.

Lemma pro_rewriting_relation_graph_syntax `{StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  {n m} (p q : PRO Struct T n m) :
    pro_rewriting_domain R p ->
    pro_rewriting_domain R q ->
    PRO_graph_semantics p ≡ₛ PRO_graph_semantics q ->
    R n m p q.
Proof.
  intros Hp Hq Hpq.
  apply (pro_rewriting_relation_graph_syntax_l R q p q); [done..|].
  now apply pro_rewriting_relation_refl.
Qed.











From TensorRocq Require Import ProLike.

Program Definition LawfulProLike_LawfulPRORewritingRelation
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{GraphS : StructGraphable Struct T,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  : LawfulPRORewritingRelation Struct T := {|
  pro_rewriting_relation n m :=
    λ p q, exists d1 d2, DiagramDenote d1 p /\ DiagramDenote d2 q /\ d1 ≡ d2;
  pro_rewriting_domain n m p := is_Some (PRO_to_diagram p);
|}.
Next Obligation.
  intros.
  cbn; done.
Qed.
Next Obligation.
  intros.
  cbn; done.
Qed.
Next Obligation.
  cbn.
  intros.
  now apply omap2_is_Some.
Qed.
Next Obligation.
  cbn.
  intros.
  now apply omap2_is_Some.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  intros n m p [d Hd].
  exists d, d.
  split_and!; [constructor; apply eq_reflexivity, Hd..|].
  done.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  unfold Symmetric.
  naive_solver.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  intros n m p q r (dp & dq & Hdp & Hdq & Hdpq)
    (dq' & dr & Hdq' & Hdr & Hdqr).
  exists dp, dr.
  split_and!; [done..|].
  rewrite Hdpq, <- Hdqr.
  eapply denote_unique; eauto.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  intros n m p p' q [dp' Hdp'] Hpp' (dp & dq & Hdp & Hdq & Hdpq).
  exists dp', dq.
  split_and!; [now constructor; apply eq_reflexivity|done|].
  rewrite <- Hdpq.
  destruct Hdp as [Hdp].
  apply option_relation_Forall2 in Hdp.
  destruct (PRO_to_diagram p) as [dp''|] eqn:Hdp''; [|done].
  cbn in Hdp.
  rewrite <- Hdp.
  apply (PRO_to_diagram_correct R A) in Hdp', Hdp''.
  symmetry.
  apply (Dsemantics_correct R A).
  rewrite Hdp', Hdp''.
  rewrite <- 2 (PRO_graph_semantics_correct (LawGraphS:=LawGraphS)).
  now apply graph_semantics_syntactic_eq.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  intros n m o p p' (dp & dp' & Hdp & Hdp' & Hdpp') q q' (dq & dq' & Hdq & Hdq' & Hdqq').
  eexists _, _.
  split; [apply _|].
  split; [apply _|].
  now f_equiv.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ? ? ?.
  intros n m n' m' p p' (dp & dp' & Hdp & Hdp' & Hdpp') q q' (dq & dq' & Hdq & Hdq' & Hdqq').
  eexists _, _.
  split; [apply _|].
  split; [apply _|].
  now f_equiv.
Qed.

Import PropGraphTerm.













Lemma LawfulProLike_PRO_quote_test_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {n m} (dlhs drhs : D n m) :
  forall lhs rhs,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  default_countable_graph_iso_test (PRO_graph_semantics Qlhs)
    (PRO_graph_semantics Qrhs) = true ->
  dlhs ≡ drhs.
Proof.
  intros lhs rhs Hlhs Hrhs Qlhs Qrhs HQlhs HQrhs.
  intros Hlr%default_countable_graph_iso_test_correct.

  apply (PRO_quote_correct_graph_semantics _) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics _) in HQrhs as HQrhs'.
  eapply (DiagramQuote_correct R A); [eauto..|].
  rewrite <- 2 PRO_graph_semantics_correct.
  apply graph_semantics_syntactic_eq.
  rewrite HQlhs', HQrhs'.
  f_equiv.
  apply Hlr.
Qed.



Lemma LawfulProLike_RW_dom_of_Quote
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d : D n m) p :
  DiagramQuote d p ->
  RW.(pro_rewriting_domain) p.
Proof.
  intros [Hdp%(f_equiv is_Some)].
  now apply Hdp.
Qed.

Lemma LawfulProLike_RW_dom_of_Denote
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d : D n m) p :
  DiagramDenote d p ->
  RW.(pro_rewriting_domain) p.
Proof.
  intros [Hdp%(f_equiv is_Some)].
  now apply Hdp.
Qed.



Lemma LawfulProLike_equiv_of_RW_Quote
  {R : Type} `{SR : SemiRing R rO rI radd rmul req} {A : Type}
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  {Struct : Mor nat} {T : Type} {D : Mor nat}
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (d d' : D n m) p p' :
  DiagramQuote d p ->
  DiagramQuote d' p' ->
  RW n m p p' -> d ≡ d'.
Proof.
  intros [Hdp] [Hdp'] (d1 & d1' & [Hd1] & [Hd1'] & Heq).
  rewrite Hd1 in Hdp.
  rewrite Hd1' in Hdp'.
  apply (inj Some) in Hdp, Hdp'.
  rewrite <- Hdp, <- Hdp'; done.
Qed.








Definition PRO_monog_context_domainb `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  {i j n m}
  (ctx : {k & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type) :
  bool :=
  default false (
    let '(existT k (GC1, GC2)) := ctx in
    C1 ← graph_to_term _ _ GC1;
    C2 ← graph_to_term _ _ GC2;
    _ ← guard (R.(pro_rewriting_domain) C1);
    _ ← guard (R.(pro_rewriting_domain) C2);
    Some true).

Lemma PRO_monog_context_domainb_correct `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  {i j n m}
  (ctx : {k & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type) :
  PRO_monog_context_domainb R graph_to_term ctx ->
  forall lhs rhs, R i j lhs rhs ->
  forall (tl tr : PRO Struct T n m),
    R.(pro_rewriting_domain) tl ->
    R.(pro_rewriting_domain) tr ->
    PRO_graph_semantics tl ≡ₛ make_monog_pushout (PRO_graph_semantics lhs) ctx ->
    PRO_graph_semantics tr ≡ₛ make_monog_pushout (PRO_graph_semantics rhs) ctx ->
    R n m tl tr.
Proof.
  unfold PRO_monog_context_domainb.
  destruct ctx as [k [GC1 GC2]].
  destruct (graph_to_term _ _ GC1) as [C1|] eqn:HC1; [|done].
  destruct (graph_to_term _ _ GC2) as [C2|] eqn:HC2; [|done].
  cbn.
  do 2 case_guard; [|done..].
  cbn.
  intros _.
  intros lhs rhs Hlrhs tl tr HRtl HRtr Htl Htr.
  eapply pro_rewriting_relation_graph_syntax_l with ((C1 ;; Pid k * lhs) ;; C2)%pro; [done|..].
  1: {
    cbn.
    rewrite Htl.
    apply compose_graphs_cohg_syntactic_eq, Hgraph_to_term, HC2.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HC1|].
    done.
  }
  eapply pro_rewriting_relation_graph_syntax_r with ((C1 ;; Pid k * rhs) ;; C2)%pro; [done|..].
  2: {
    cbn.
    rewrite Htr.
    apply compose_graphs_cohg_syntactic_eq, Hgraph_to_term, HC2.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HC1|].
    done.
  }
  f_equiv; [|now apply pro_rewriting_relation_refl].
  f_equiv; [now apply pro_rewriting_relation_refl|].
  f_equiv; [|done].
  apply pro_rewriting_relation_refl.
  apply R.(pro_rewriting_domain_id).
Qed.



Definition PRO_monog_rewrite `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number : nat) :
  option (PRO Struct T n m) :=
  let Glhs := PRO_graph_semantics lhs in let Gtgt := PRO_graph_semantics tgt in
  ctx ← select_monog_context Glhs Gtgt match_number;
  if negb (default_graph_iso_test Gtgt (make_monog_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (PRO_monog_context_domainb R graph_to_term ctx) then None else
  let Grhs := PRO_graph_semantics rhs in
  res ← graph_to_term n m (make_monog_pushout Grhs ctx);
  _ ← guard (R.(pro_rewriting_domain) res);
  Some res.


Lemma PRO_monog_rewrite_correct `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number : nat) :
  pro_rewriting_domain R tgt ->
  R i j lhs rhs ->
  forall res, PRO_monog_rewrite R graph_to_term lhs rhs tgt match_number = Some res ->
  R n m tgt res.
Proof.
  intros Htgt Hlrhs res.
  unfold PRO_monog_rewrite.
  set (Glhs := PRO_graph_semantics lhs).
  set (Grhs := PRO_graph_semantics rhs).
  set (Gtgt := PRO_graph_semantics tgt).
  destruct (select_monog_context _ _ _) as [ctx|]; [|done].
  cbn.
  destruct (default_graph_iso_test_correct' Gtgt (make_monog_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (PRO_monog_context_domainb _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (PRO_monog_context_domainb_correct R graph_to_term Hgraph_to_term
    ctx (Is_true_true_2 _ Hdom)) as Hpush.
  destruct (graph_to_term _ _ _) as [res'|] eqn:Hres; [|done].
  cbn.
  case_guard as Hres'; [|done].
  cbn.
  intros [= ->].
  apply (Hpush lhs rhs Hlrhs).
  - done.
  - done.
  - done.
  - now apply Hgraph_to_term in Hres.
Qed.


Definition PRO_monog_quote_context_domainb `{StructGraphable Struct T, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (f : T' -> T)
  {i j n m}
  (ctx : {k & CospanHyperGraph T' n (k + i) * CospanHyperGraph T' (k + j) m}%type) :
  bool :=
  default false (
    let '(existT k (GC1, GC2)) := ctx in
    C1 ← graph_to_term _ _ GC1;
    C2 ← graph_to_term _ _ GC2;
    _ ← @guard (R.(pro_rewriting_domain) (PRO_denote f C1)) (R.(pro_rewriting_domain_dec) _);
    _ ← @guard (R.(pro_rewriting_domain) (PRO_denote f C2)) (R.(pro_rewriting_domain_dec) _);
    Some true).

Lemma PRO_monog_quote_context_domainb_correct `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j n m}
  (ctx : {k & CospanHyperGraph T' n (k + i) * CospanHyperGraph T' (k + j) m}%type) :
  PRO_monog_quote_context_domainb R graph_to_term f ctx ->
  forall lhs rhs, R i j lhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs -> PRO_quote f Qrhs rhs ->

  forall (tl tr : PRO Struct T n m),
    R.(pro_rewriting_domain) tl ->
    R.(pro_rewriting_domain) tr ->
    forall Qtl Qtr,
    PRO_quote f Qtl tl -> PRO_quote f Qtr tr ->
    PRO_graph_semantics Qtl ≡ₛ make_monog_pushout (PRO_graph_semantics Qlhs) ctx ->
    PRO_graph_semantics Qtr ≡ₛ make_monog_pushout (PRO_graph_semantics Qrhs) ctx ->
    R n m tl tr.
Proof.
  unfold PRO_monog_quote_context_domainb.
  destruct ctx as [k [GC1 GC2]].
  destruct (graph_to_term _ _ GC1) as [C1|] eqn:HC1; [|done].
  destruct (graph_to_term _ _ GC2) as [C2|] eqn:HC2; [|done].
  cbn.
  do 2 case_guard; [|done..].
  cbn.
  intros _.
  intros lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs
    tl tr HRtl HRtr Qtl Qtr HQtl HQtr Htl Htr.
  apply (PRO_quote_correct_graph_semantics f) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQtl as HQtl'.
  apply (PRO_quote_correct_graph_semantics f) in HQtr as HQtr'.
  eapply pro_rewriting_relation_graph_syntax_l with
    ((PRO_denote f C1 ;; Pid k * lhs) ;; PRO_denote f C2)%pro; [done|..].
  1: {
    cbn.
    rewrite 2 PRO_graph_semantics_denote.
    rewrite HQlhs'.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- 2 graph_apply_hom_compose_graphs.
    rewrite HQtl'.
    f_equiv.
    rewrite Htl.
    apply compose_graphs_cohg_syntactic_eq, Hgraph_to_term, HC2.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HC1|].
    done.
  }
  eapply pro_rewriting_relation_graph_syntax_r with
    ((PRO_denote f C1 ;; Pid k * rhs) ;; PRO_denote f C2)%pro; [done|..].
  2: {
    cbn.
    rewrite 2 PRO_graph_semantics_denote.
    rewrite HQrhs'.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- 2 graph_apply_hom_compose_graphs.
    rewrite HQtr'.
    rewrite Htr.
    f_equiv.
    apply compose_graphs_cohg_syntactic_eq, Hgraph_to_term, HC2.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HC1|].
    done.
  }
  f_equiv; [|now apply pro_rewriting_relation_refl].
  f_equiv; [now apply pro_rewriting_relation_refl|].
  f_equiv; [|done].
  apply pro_rewriting_relation_refl.
  apply R.(pro_rewriting_domain_id).
Qed.



Definition PRO_monog_quote_rewrite `{FreeStructGraphable Struct, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (f : T' -> T)
  {i j} (Qlhs Qrhs : PRO Struct T' i j) {n m} (Qtgt : PRO Struct T' n m)
  (match_number : nat) :
  option (PRO Struct T' n m) :=
  let Glhs := PRO_graph_semantics Qlhs in let Gtgt := PRO_graph_semantics Qtgt in
  ctx ← select_monog_context Glhs Gtgt match_number;
  if negb (default_graph_iso_test Gtgt (make_monog_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (PRO_monog_quote_context_domainb R graph_to_term f ctx) then None else
  let Grhs := PRO_graph_semantics Qrhs in
  res ← graph_to_term n m (make_monog_pushout Grhs ctx);
  (* _ ← guard (R.(pro_rewriting_domain) (PRO_denote f res)); *)
  Some res.


Lemma PRO_monog_quote_rewrite_correct `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number : nat) :
  pro_rewriting_domain R tgt ->
  R i j lhs rhs ->
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_monog_quote_rewrite R graph_to_term f Qlhs Qrhs Qtgt match_number = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  bool_decide (R.(pro_rewriting_domain) res) ->
  R n m tgt res.
Proof.
  intros Htgt Hlrhs Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt.
  unfold PRO_monog_quote_rewrite.
  set (Glhs := PRO_graph_semantics Qlhs).
  set (Grhs := PRO_graph_semantics Qrhs).
  set (Gtgt := PRO_graph_semantics Qtgt).
  destruct (select_monog_context _ _ _) as [ctx|]; [|done].
  cbn.
  destruct (default_graph_iso_test_correct' Gtgt (make_monog_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (PRO_monog_quote_context_domainb _ _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (PRO_monog_quote_context_domainb_correct R graph_to_term Hgraph_to_term
    f
    ctx (Is_true_true_2 _ Hdom)) as Hpush.
  destruct (graph_to_term _ _ _) as [Qres|] eqn:HQres_eq; [|done].
  cbn.
  intros _ [= <-].
  intros res HQres Hres%bool_decide_spec.
  eapply (Hpush lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs _ _ Htgt Hres Qtgt Qres HQtgt HQres).
  - done.
  - apply Hgraph_to_term in HQres_eq.
    rewrite HQres_eq.
    apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
    done.
Qed.

Lemma LawfulProLike_PRO_monog_quote_rewrite_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMon : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_PROP')

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m)
  (match_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->
(*
  pro_rewriting_domain R tgt ->
  R i j lhs rhs -> *)
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_monog_quote_rewrite RW graph_to_term f Qlhs Qrhs Qtgt match_number = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (PRO_monog_quote_rewrite_correct
    RW graph_to_term (fun n m => graph_to_PROP'_correct) f lhs rhs tgt match_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.



Lemma LawfulProLike_PRO_monog_quote_clean_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMon : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_PROP')

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {n m} (dtgt : D n m) :
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres,
    graph_to_term n m (PRO_graph_semantics Qtgt) = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros tgt Htgt Qtgt HQtgt Qres HQres res Hres dres Hdres.
  apply graph_to_PROP'_correct in HQres.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.
  apply (f_equiv (graph_apply_hom f)) in HQres.
  rewrite <- HQtgt', <- HQres' in HQres.
  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - fold RW.
    apply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + done.
Qed.








Definition PRO_context_domainb `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  {i j n m}
  (ctx : CospanHyperGraph T n ((i + j) + m)) :
  bool :=
  default false (
    Pctx ← graph_to_term _ _ ctx;
    _ ← guard (R.(pro_rewriting_domain) Pctx);
    Some true).

Lemma PRO_context_domainb_correct `{Countable T}
  `{!SubStruct Autonomy Struct}
  `{!StructGraphable Struct T}
  `{!SubStructGraphable Autonomy Struct T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  {i j n m}
  (ctx : CospanHyperGraph T n ((i + j) + m)) :
  PRO_context_domainb R graph_to_term ctx ->
  forall lhs rhs, R i j lhs rhs ->
  forall (tl tr : PRO Struct T n m),
    R.(pro_rewriting_domain) tl ->
    R.(pro_rewriting_domain) tr ->
    PRO_graph_semantics tl ≡ₛ make_pushout (PRO_graph_semantics lhs) ctx ->
    PRO_graph_semantics tr ≡ₛ make_pushout (PRO_graph_semantics rhs) ctx ->
    R n m tl tr.
Proof.
  unfold PRO_context_domainb.
  destruct (graph_to_term _ _ ctx) as [Pctx|] eqn:HPctx; [|done].
  cbn.
  case_guard; [|done].
  cbn.
  intros _.
  intros lhs rhs Hlrhs tl tr HRtl HRtr Htl Htr.
  eapply pro_rewriting_relation_graph_syntax_l with
    (Pctx ;; (lhs * Pid j ;; Pcap j) * Pid m)%pro; [done|..].
  1: {
    cbn.
    rewrite Htl.
    rewrite graph_of_struct_includeStruct.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HPctx|].
    done.
  }
  eapply pro_rewriting_relation_graph_syntax_r with
    (Pctx ;; (rhs * Pid j ;; Pcap j) * Pid m)%pro; [done|..].
  2: {
    cbn.
    rewrite Htr.
    rewrite graph_of_struct_includeStruct.
    apply compose_graphs_cohg_syntactic_eq; [apply Hgraph_to_term, HPctx|].
    done.
  }
  f_equiv; [now apply pro_rewriting_relation_refl|].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_id)].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_struct)].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_id)].
  done.
Qed.

Definition PRO_gen_rewrite `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  (select_context : forall i j (lhs : CospanHyperGraph T i j)
    n m (tgt : CospanHyperGraph T n m), nat -> nat ->
    option (CospanHyperGraph T n ((i + j) + m)))
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number : nat) (quotient_number : nat) :
  option (PRO Struct T n m) :=
  let Glhs := PRO_graph_semantics lhs in let Gtgt := PRO_graph_semantics tgt in
  ctx ← select_context i j Glhs n m Gtgt match_number quotient_number;
  if negb (default_graph_iso_test Gtgt (make_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (PRO_context_domainb R graph_to_term ctx) then None else
  let Grhs := PRO_graph_semantics rhs in
  res ← graph_to_term n m (make_pushout Grhs ctx);
  _ ← guard (R.(pro_rewriting_domain) res);
  Some res.




Definition PRO_bimonog_rewrite `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number quotient_number : nat) :
  option (PRO Struct T n m) :=
  PRO_gen_rewrite R graph_to_term (fun i j lhs n m tgt =>
    select_bimonog_context lhs tgt) lhs rhs tgt match_number quotient_number.


Definition PRO_frobenius_rewrite `{StructGraphable Struct T, Countable T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number quotient_number : nat) :
  option (PRO Struct T n m) :=
  PRO_gen_rewrite R graph_to_term (fun i j lhs n m tgt =>
    select_frobenius_context lhs tgt) lhs rhs tgt match_number quotient_number.


Lemma PRO_gen_rewrite_correct `{Countable T}
  `{!SubStruct Autonomy Struct}
  `{!StructGraphable Struct T}
  `{!SubStructGraphable Autonomy Struct T}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T n m -> option (PRO Struct T n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  (select_context : forall i j (lhs : CospanHyperGraph T i j)
    n m (tgt : CospanHyperGraph T n m), nat -> nat ->
    option (CospanHyperGraph T n ((i + j) + m)))
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number quotient_number : nat) :
  pro_rewriting_domain R tgt ->
  R i j lhs rhs ->
  forall res, PRO_gen_rewrite R graph_to_term select_context
    lhs rhs tgt match_number quotient_number = Some res ->
  R n m tgt res.
Proof.
  intros Htgt Hlrhs res.
  unfold PRO_gen_rewrite.
  set (Glhs := PRO_graph_semantics lhs).
  set (Grhs := PRO_graph_semantics rhs).
  set (Gtgt := PRO_graph_semantics tgt).
  destruct (select_context _ _ _  _ _ _  _ _) as [ctx|]; [|done].
  cbn.
  destruct (default_graph_iso_test_correct' Gtgt (make_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (PRO_context_domainb _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (PRO_context_domainb_correct R graph_to_term Hgraph_to_term
    ctx (Is_true_true_2 _ Hdom)) as Hpush.
  destruct (graph_to_term _ _ _) as [res'|] eqn:Hres; [|done].
  cbn.
  case_guard as Hres'; [|done].
  cbn.
  intros [= ->].
  apply (Hpush lhs rhs Hlrhs).
  - done.
  - done.
  - done.
  - now apply Hgraph_to_term in Hres.
Qed.


Definition PRO_quote_context_domainb `{StructGraphable Struct T, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (f : T' -> T)
  {i j n m}
  (ctx : CospanHyperGraph T' n ((i + j) + m)) :
  bool :=
  default false (
    Pctx ← graph_to_term _ _ ctx;
    _ ← @guard (R.(pro_rewriting_domain) (PRO_denote f Pctx)) (R.(pro_rewriting_domain_dec) _);
    Some true).

Lemma PRO_quote_context_domainb_correct `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{!SubStruct Autonomy Struct, !SubStructGraphable Autonomy Struct T}

  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j n m}
  (ctx : CospanHyperGraph T' n ((i + j) + m)) :
  PRO_quote_context_domainb R graph_to_term f ctx ->
  forall lhs rhs, R i j lhs rhs ->
  forall Qlhs Qrhs,
  PRO_quote f Qlhs lhs -> PRO_quote f Qrhs rhs ->

  forall (tl tr : PRO Struct T n m),
    R.(pro_rewriting_domain) tl ->
    R.(pro_rewriting_domain) tr ->
    forall Qtl Qtr,
    PRO_quote f Qtl tl -> PRO_quote f Qtr tr ->
    PRO_graph_semantics Qtl ≡ₛ make_pushout (PRO_graph_semantics Qlhs) ctx ->
    PRO_graph_semantics Qtr ≡ₛ make_pushout (PRO_graph_semantics Qrhs) ctx ->
    R n m tl tr.
Proof.
  unfold PRO_quote_context_domainb.
  destruct (graph_to_term _ _ ctx) as [Pctx|] eqn:Hctx; [|done].
  cbn.
  case_guard; [|done..].
  cbn.
  intros _.
  intros lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs
    tl tr HRtl HRtr Qtl Qtr HQtl HQtr Htl Htr.
  apply (PRO_quote_correct_graph_semantics f) in HQlhs as HQlhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
  apply (PRO_quote_correct_graph_semantics f) in HQtl as HQtl'.
  apply (PRO_quote_correct_graph_semantics f) in HQtr as HQtr'.
  eapply pro_rewriting_relation_graph_syntax_l with
    (PRO_denote f Pctx ;; (lhs * Pid j ;; Pcap j) * Pid m)%pro; [done|..].
  1: {
    cbn.
    rewrite PRO_graph_semantics_denote.
    rewrite HQlhs'.
    rewrite graph_of_struct_includeStruct.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- (graph_apply_hom_id_graph f (n:=m)).
    cbn.
    rewrite <- (graph_apply_hom_cap_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite HQtl'.
    f_equiv.
    cbn.
    rewrite Htl.
    unfold make_pushout.
    f_equiv.
    apply Hgraph_to_term; done.
  }
  eapply pro_rewriting_relation_graph_syntax_r with
    (PRO_denote f Pctx ;; (rhs * Pid j ;; Pcap j) * Pid m)%pro; [done|..].
  2: {
    cbn.
    rewrite PRO_graph_semantics_denote.
    rewrite HQrhs'.
    rewrite graph_of_struct_includeStruct.
    rewrite <- (graph_apply_hom_id_graph f).
    rewrite <- (graph_apply_hom_id_graph f (n:=m)).
    cbn.
    rewrite <- (graph_apply_hom_cap_graph f).
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite <- graph_apply_hom_stack_graphs.
    rewrite <- graph_apply_hom_compose_graphs.
    rewrite HQtr'.
    f_equiv.
    cbn.
    rewrite Htr.
    unfold make_pushout.
    f_equiv.
    apply Hgraph_to_term; done.
  }
  f_equiv; [now apply pro_rewriting_relation_refl|].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_id)].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_struct)].
  f_equiv; [|apply pro_rewriting_relation_refl, R.(pro_rewriting_domain_id)].
  done.
Qed.


Definition PRO_gen_quote_rewrite `{FreeStructGraphable Struct, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), nat -> nat ->
    option (CospanHyperGraph T' n ((i + j) + m)))
  (f : T' -> T)
  {i j} (Qlhs Qrhs : PRO Struct T' i j) {n m} (Qtgt : PRO Struct T' n m)
  (match_number quotient_number : nat) :
  option (PRO Struct T' n m) :=
  let Glhs := PRO_graph_semantics Qlhs in let Gtgt := PRO_graph_semantics Qtgt in
  ctx ← select_context i j Glhs n m Gtgt match_number quotient_number;
  if negb (default_graph_iso_test Gtgt (make_pushout Glhs ctx)) then None else
  (* '(existT k (GC1, GC2)) ← select_monog_context Glhs Gtgt match_number; *)
  if negb (PRO_quote_context_domainb R graph_to_term f ctx) then None else
  let Grhs := PRO_graph_semantics Qrhs in
  res ← graph_to_term n m (make_pushout Grhs ctx);
  (* _ ← guard (R.(pro_rewriting_domain) res); *)
  Some res.


Lemma PRO_gen_quote_rewrite_correct `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{!SubStruct Autonomy Struct, !SubStructGraphable Autonomy Struct T}

  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  select_context
  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
  (match_number quotient_number : nat) :
  pro_rewriting_domain R tgt ->
  R i j lhs rhs ->
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_rewrite R graph_to_term select_context
    f Qlhs Qrhs Qtgt match_number quotient_number = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  bool_decide (R.(pro_rewriting_domain) res) ->
  R n m tgt res.
Proof.
  intros Htgt Hlrhs Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt.
  unfold PRO_gen_quote_rewrite.
  set (Glhs := PRO_graph_semantics Qlhs).
  set (Grhs := PRO_graph_semantics Qrhs).
  set (Gtgt := PRO_graph_semantics Qtgt).

  destruct (select_context _ _ _  _ _ _  _ _) as [ctx|]; [|done].
  cbn.
  destruct (default_graph_iso_test_correct' Gtgt (make_pushout Glhs ctx))
    as [Hctx|]; [|done].
  cbn.
  destruct (PRO_quote_context_domainb _ _ _ _) as [|] eqn:Hdom; [|done].
  cbn.
  specialize (PRO_quote_context_domainb_correct R graph_to_term Hgraph_to_term
    f ctx (Is_true_true_2 _ Hdom)) as Hpush.
  destruct (graph_to_term _ _ _) as [Qres|] eqn:HQres_eq; [|done].
  cbn.
  intros _ [= <-].
  intros res HQres Hres%bool_decide_spec.
  eapply (Hpush lhs rhs Hlrhs Qlhs Qrhs HQlhs HQrhs _ _ Htgt Hres Qtgt Qres HQtgt HQres).
  - done.
  - apply Hgraph_to_term in HQres_eq.
    rewrite HQres_eq.
    apply (PRO_quote_correct_graph_semantics f) in HQrhs as HQrhs'.
    done.
Qed.

(* FIXME: Move *)
#[export] Instance substruct_symmetricg_of_monoidal_symmetry
  `{!SubStruct Monoidal Struct, !SubStruct Symmetry Struct} :
  SubStruct SymmetricG Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.

#[export] Instance substruct_autonomous_of_symmetricg_autonomy
  `{!SubStruct SymmetricG Struct, !SubStruct Autonomy Struct} :
  SubStruct Autonomous Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.

#[export] Instance substruct_frobenius_of_autonomous_frobenial
  `{!SubStruct Autonomous Struct, !SubStruct Frobenial Struct} :
  SubStruct Frobenius Struct := fun n m s =>
  match s with
  | inl s | inr s => includeStruct s
  end.



Lemma LawfulProLike_PRO_bimonog_quote_rewrite_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_APROP')
  (select_context := fun i j lhs n m tgt =>
    select_bimonog_context lhs tgt)

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m)
  (match_number quotient_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->
(*
  pro_rewriting_domain R tgt ->
  R i j lhs rhs -> *)
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_rewrite RW graph_to_term select_context f
    Qlhs Qrhs Qtgt match_number quotient_number = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (PRO_gen_quote_rewrite_correct
    RW graph_to_term (fun n m => graph_to_APROP'_correct) select_context
    f lhs rhs tgt match_number quotient_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.




Lemma LawfulProLike_PRO_bimonog_quote_clean_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_APROP')

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {n m} (dtgt : D n m) :
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres,
    graph_to_term n m (PRO_graph_semantics Qtgt) = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros tgt Htgt Qtgt HQtgt Qres HQres res Hres dres Hdres.
  apply graph_to_APROP'_correct in HQres.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.
  apply (f_equiv (graph_apply_hom f)) in HQres.
  rewrite <- HQtgt', <- HQres' in HQres.
  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - fold RW.
    apply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + done.
Qed.





Lemma LawfulProLike_PRO_frobenius_quote_rewrite_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    StructFrob : !SubStruct Frobenial Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_FPROP')
  (select_context := fun i j lhs n m tgt =>
    select_frobenius_context lhs tgt)

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {i j} (dlhs drhs : D i j) {n m} (dtgt : D n m)
  (match_number quotient_number : nat) :
  dlhs ≡ drhs ->
  forall lhs rhs tgt,
  DiagramQuote dlhs lhs ->
  DiagramQuote drhs rhs ->
  DiagramQuote dtgt tgt ->
(*
  pro_rewriting_domain R tgt ->
  R i j lhs rhs -> *)
  forall Qlhs Qrhs Qtgt,
  PRO_quote f Qlhs lhs ->
  PRO_quote f Qrhs rhs ->
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_rewrite RW graph_to_term select_context f
    Qlhs Qrhs Qtgt match_number quotient_number = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros Hdlrhs lhs rhs tgt Hlhs Hrhs Htgt.
  specialize (PRO_gen_quote_rewrite_correct
    RW graph_to_term (fun n m => graph_to_FPROP'_correct) select_context
    f lhs rhs tgt match_number quotient_number) as Hrw.
  tspecialize Hrw. 1:{
    destruct Htgt as [Htgt].
    apply (f_equiv is_Some) in Htgt.
    apply Htgt.
    done.
  }
  tspecialize Hrw by
    (exists dlhs, drhs; split_and!;
      [apply DiagramQuote_iff_DiagramDenote..|]; done).
  intros Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres dres Hdres.
  specialize (Hrw Qlhs Qrhs Qtgt HQlhs HQrhs HQtgt Qres HQres_eq res HQres).
  tspecialize Hrw. 1:{
    apply bool_decide_spec.
    destruct Hdres as [Hdres].
    apply (f_equiv is_Some) in Hdres.
    now apply Hdres.
  }
  destruct Hrw as (dtgt' & dres' & Hdtgt' & Hres' & Hdtgt_res').
  assert (Hdtgt_tgt' : dtgt ≡ dtgt') by (
    apply DiagramQuote_iff_DiagramDenote in Htgt;
    eapply (denote_unique _ _ tgt); eauto).
  assert (Hdres_res' : dres ≡ dres') by (
    eapply (denote_unique _ _ res); eauto).
  rewrite Hdtgt_tgt', Hdres_res'.
  done.
Qed.



Lemma LawfulProLike_PRO_frobenius_quote_clean_correct `{Countable T'}
  (R : Type) `{SR : SemiRing R rO rI radd rmul req} (A : Type)
  `{SA : Summable A, EQA : EqDecision A, WFA : !WFSummable A}
  (Struct : Mor nat) (T : Type) (D : Mor nat)
  {ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawPro : LawfulProLike R A Struct T D)
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  `{StructD : StructableDiagram Struct D,
    LawStructD : !LawfulStructableDiagram R A Struct D}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    StructFrob : !SubStruct Frobenial Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_FPROP')

  (f : T' -> T) {Hf : Proper (equiv ==> equiv) f}
  {n m} (dtgt : D n m) :
  forall tgt,
  DiagramQuote dtgt tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres,
    graph_to_term n m (PRO_graph_semantics Qtgt) = Some Qres ->
  forall res, PRO_unquote f Qres res ->
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros tgt Htgt Qtgt HQtgt Qres HQres res Hres dres Hdres.
  apply graph_to_FPROP'_correct in HQres.
  apply (PRO_quote_correct_graph_semantics _) in HQtgt as HQtgt'.
  apply (PRO_quote_correct_graph_semantics _) in Hres as HQres'.
  apply (f_equiv (graph_apply_hom f)) in HQres.
  rewrite <- HQtgt', <- HQres' in HQres.
  eapply (LawfulProLike_equiv_of_RW_Quote (LawPro)).
  - eauto.
  - apply DiagramQuote_iff_DiagramDenote; eauto.
  - fold RW.
    apply (pro_rewriting_relation_graph_syntax RW).
    + eapply LawfulProLike_RW_dom_of_Quote; eauto.
    + eapply LawfulProLike_RW_dom_of_Denote; eauto.
    + done.
Qed.


(*





Record PROPushout {Struct T} := mk_PROPushout {
  pro_pushout_context (i j n m : nat) :> Type;
  pro_mk_pushout {i j n m}
    (ctx : pro_pushout_context i j n m)
    (lhs : PRO Struct T i j) : PRO Struct T n m;
}.

Global Arguments PROPushout _ _ : clear implicits, assert.

Record PROMatchingEngine {Struct T} {P : PROPushout Struct T} := mk_PROMatchingEngine {
  pro_match_selector :> Type;
  pro_match {i j} (subp : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : pro_match_selector) : option (P i j n m);
}.

Global Arguments PROMatchingEngine {_ _} (_) : assert.

Record PRORewritingEngine {Struct T} {P : PROPushout Struct T}
  {M : PROMatchingEngine P} := mk_PRORewritingEngine {
  pro_rewrite {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (match_number : M) : option (PRO Struct T n m);
}.

Global Arguments PRORewritingEngine {_ _} (_ _) : assert.

Class LawfulPRORewritingEngine {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (P : PROPushout Struct T) (M : PROMatchingEngine P)
  (RW : PRORewritingEngine P M) (R : LawfulPRORewritingRelation Struct T) := {
  pro_rewrite_spec {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : M) res : RW.(pro_rewrite) lhs rhs tgt s = Some res ->
      R i j lhs rhs ->
      R n m tgt res
}.



Definition PRORW_of_test_match {Struct T}
  {P : PROPushout Struct T} (M : PROMatchingEngine P)
  ()























Class LawfulPROPushout {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (P : PROPushout Struct T) (R : LawfulPRORewritingRelation Struct T) := {
  pro_mk_pushout_proper i j n m ctx ::
    Proper (R i j ==> R n m) (P.(pro_mk_pushout) ctx)
}.

Class LawfulPROMatchingEngine {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (P : PROPushout Struct T)
  (M : PROMatchingEngine P) (R : LawfulPRORewritingRelation Struct T) := {
  lawful_pro_match_pushout :: LawfulPROPushout P R;
  pro_match_correct {i j} (subp : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : M) ctx : M.(pro_match) subp tgt s = Some ctx ->
      R n m tgt (P.(pro_mk_pushout) ctx subp);
  pro_match_dom {i j} (subp : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : M) ctx : M.(pro_match) subp tgt s = Some ctx ->
      forall subp', R.(pro_rewriting_domain) subp' ->
      R.(pro_rewriting_domain) (P.(pro_mk_pushout) ctx subp');
}.

Class LawfulPRORewritingEngine {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (P : PROPushout Struct T) (M : PROMatchingEngine P)
  (RW : PRORewritingEngine P M) (R : LawfulPRORewritingRelation Struct T) := {
  lawful_pro_rewrite_match :: LawfulPROMatchingEngine P M R;
  pro_rewrite_spec {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : M) res : RW.(pro_rewrite) lhs rhs tgt s = Some res ->
      exists ctx, M.(pro_match) lhs tgt s = Some ctx
        /\ R n m res (P.(pro_mk_pushout) ctx rhs);
}.

Lemma pro_rewrite_correct {Struct T} {StructG : StructGraphable Struct T}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  (P : PROPushout Struct T) (M : PROMatchingEngine P)
  (RW : PRORewritingEngine P M) (R : LawfulPRORewritingRelation Struct T)
  {LawRW : LawfulPRORewritingEngine P M RW R}
  {i j} (lhs rhs : PRO Struct T i j) {n m} (tgt : PRO Struct T n m)
    (s : M) res :
    R i j lhs rhs ->
    RW.(pro_rewrite) lhs rhs tgt s = Some res ->
    R n m tgt res.
Proof.
  intros Hlhs_rhs Hrew.
  apply pro_rewrite_spec in Hrew as Hctx.
  destruct Hctx as (ctx & Hmatch & Hres).
  rewrite Hres.
  rewrite <- Hlhs_rhs.
  now apply pro_match_correct in Hmatch.
Qed.





Definition nth_frobenius_context
  `{Countable T}
  {i j} (lhs : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : nat) :
  option (CospanHyperGraph T n (i + j + m)) :=
  ctx ← all_frobenius_contexts lhs cohg !! match_number;
  if opt_weak_graph_iso_partial_test (make_pushout lhs ctx) cohg
    then Some ctx
  else None.






Lemma DiagramQuote_to_DiagramDenote_correct_rew {Struct T D} `{ProD : ProLike Struct T D}
  `{EqT : Equiv T, EquivT : Equivalence T equiv}
  `{EqStruct : forall n m, Equiv (Struct n m)}
  `{EquivStruct : forall n m, @Equivalence (Struct n m) equiv}
  {TensStruct : StrictTensorLike R A Struct}
  {TensT : TensorLike R A T}
  {TensD : StrictTensorLike R A D}
  (LawProD : LawfulProLike Struct T D)
  {i j} (lhs rhs : PRO Struct T i j) (dlhs drhs : D i j)
  {n m} (tgt res : PRO Struct T n m) (dtgt : D n m) :
  DiagramQuote dlhs lhs -> DiagramDenote drhs rhs ->

  DiagramQuote dtgt tgt ->
  forall res,

  DiagramDenote d' p' ->
  PRO_semantics p ≡ PRO_semantics p' ->
  d ≡ d'.
Proof.
  rewrite <- DiagramQuote_iff_DiagramDenote.
  apply DiagramQuote_correct.
Qed. *)