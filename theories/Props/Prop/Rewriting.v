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
  pro_rewriting_relation_to_domain {n m} (p q : PRO Struct T n m) :
    pro_rewriting_relation n m p q -> pro_rewriting_domain p /\ pro_rewriting_domain q
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
  intros * ? * ? ? ?.
  intros n m p [d Hd].
  exists d, d.
  split_and!; [constructor; apply eq_reflexivity, Hd..|].
  done.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ?.
  unfold Symmetric.
  naive_solver.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ?.
  intros n m p q r (dp & dq & Hdp & Hdq & Hdpq)
    (dq' & dr & Hdq' & Hdr & Hdqr).
  exists dp, dr.
  split_and!; [done..|].
  rewrite Hdpq, <- Hdqr.
  eapply denote_unique; eauto.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ?.
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
  intros * ? * ? ? ?.
  intros n m o p p' (dp & dp' & Hdp & Hdp' & Hdpp') q q' (dq & dq' & Hdq & Hdq' & Hdqq').
  eexists _, _.
  split; [apply _|].
  split; [apply _|].
  now f_equiv.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ?.
  intros n m n' m' p p' (dp & dp' & Hdp & Hdp' & Hdpp') q q' (dq & dq' & Hdq & Hdq' & Hdqq').
  eexists _, _.
  split; [apply _|].
  split; [apply _|].
  now f_equiv.
Qed.
Next Obligation.
  cbn.
  intros * ? * ? ? ?.
  intros n m p q (? & ? & [Hp%(f_equiv is_Some)] & [Hq%(f_equiv is_Some)] & _).
  naive_solver.
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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
  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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
  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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

  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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

  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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
  (f : T' -> T)
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
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
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
  (f : T' -> T)
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

  (f : T' -> T)
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

  (f : T' -> T)
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

  (f : T' -> T)
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

  (f : T' -> T)
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





(* TODO: Multi-rewrite (start with frob; we'll use it for
  box_compose, <- cap_X, <- cup_X) *)

(* The general definitions of rewriting schemes. We assume
  rewrites are indexed by fins (TODO: Extend this to something
  like parametric rewrites; requires extending the notions of
  semantic correctness interpretations)*)


Lemma rtc_transitive_correctness {A} (R R' : relation A) `{!Transitive R'} :
  subrelation R R' ->
  forall x y, R' x x -> rtc R x y -> R' x y.
Proof.
  intros HRR' x y Hx.
  revert y.
  apply rtc_ind_r.
  - done.
  - now intros ? ? ? ?%HRR' ?; etransitivity; eauto.
Qed.

Definition multi_rewriter_step (State RWidx Err : Type)
  := State -> RWidx -> State + Err.

Inductive multi_rewrites_to_step {State RWidx Err}
  (RW : multi_rewriter_step State RWidx Err) : relation (State + Err) :=
  | multi_rewrites_to_steps st idx : multi_rewrites_to_step RW (inl st) (RW st idx).

Lemma multi_rewrites_to_step_inl_inl_spec `(RW : multi_rewriter_step State RWidx Err)
  st st' : multi_rewrites_to_step RW (inl st) (inl st') <->
  exists idx, RW st idx = inl st'.
Proof.
  remember (inl st') as e eqn:He.
  split.
  - inversion 1; subst; eauto.
  - intros [? <-]; constructor.
Qed.

Definition multi_rewrites_to {State RWidx Err}
  (RW : multi_rewriter_step State RWidx Err) : relation (State + Err) :=
  rtc (multi_rewrites_to_step RW).


Lemma multi_rewrites_to_inl_inl_spec_aux `(RW : multi_rewriter_step State RWidx Err)
  e_st st' :
  multi_rewrites_to RW e_st (inl st') <->
  exists st, e_st = inl st /\
  rtc (λ st st', exists idx, RW st idx = inl st') st st'.
Proof.
  split.
  - intros HRW.
    remember (inl st') as r eqn:Hr.
    revert st' Hr.
    induction HRW as [|e_st e_st' e_st'' Hstep HRW IH]; [naive_solver|].
    intros st'' ->.
    induction Hstep.
    specialize (IH _ eq_refl).
    eexists _.
    split; [done|].
    destruct IH as (st' & HRWst & Hrtc).
    econstructor; [|apply Hrtc].
    eauto.
  - intros (st & -> & Hrtc).
    induction Hrtc as [|x y z Hst]; [done|].
    econstructor; [|done].
    destruct Hst as [? <-].
    constructor.
Qed.


Lemma multi_rewrites_to_inl_inl_spec `(RW : multi_rewriter_step State RWidx Err)
  st st' :
  multi_rewrites_to RW (inl st) (inl st') <->
  rtc (λ st st', exists idx, RW st idx = inl st') st st'.
Proof.
  rewrite multi_rewrites_to_inl_inl_spec_aux.
  naive_solver.
Qed.


Lemma multi_rewrites_to_correctness {State RWidx Err}
  (RW : multi_rewriter_step State RWidx Err)
  (R : relation State) {HR : Transitive R}
  (HRW : forall st idx st', RW st idx = inl st' -> R st st')
  st st' :
  R st st ->
  multi_rewrites_to RW (inl st) (inl st') ->
  R st st'.
Proof.
  rewrite multi_rewrites_to_inl_inl_spec.
  apply rtc_transitive_correctness; [done|].
  hnf;
  naive_solver.
Qed.



Notation BundledEqn D := {nm : nat * nat & D nm.1 nm.2 * D nm.1 nm.2}%type.

(* Import stdpp.strings. *)

(* Inductive PRORWERR :=
  | mk_PRORWERR (s : string) : PRORWERR.

#[export] Instance pretty_PRORWERR  *)


Class Matching_failures (Err : Type) := {
  no_match_failure : Err;
  nonisomorphic_match_failure : Err;
  not_in_domain_ctx_failure : Err;
  out_of_fuel_failure : Err
}.


Definition PRO_gen_quoted_multi_context_domainb
  {Struct T'}
  (P : forall n m, PRO Struct T' n m -> Prop)
  {HP : forall n m p, Decision (P n m p)}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  {n ijm}
  (ctx : CospanHyperGraph T' n (ijm)) :
  bool :=
  default false (
    Pctx ← graph_to_term _ _ ctx;
    HPctx ← @guard (P n _ Pctx) (HP n _ _);
    Some true).


Definition PRO_gen_quoted_graph_multi_rewrite_aux
  `{StructGraphable Struct T', Countable T'}
  (P : forall n m, PRO Struct T' n m -> Prop)
  {HP : forall n m p, Decision (P n m p)}
  {MatchSelector QuotientSelector Err : Type} {MFE : Matching_failures Err}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)

  {Idx State}
  (idx_to_graphs : Idx -> BundledEqn (CospanHyperGraph T'))
  (select_rewrite : State -> forall n m, CospanHyperGraph T' n m ->
    State * option ((option State (* To rewrite in parallel on the context *) *
      Idx * MatchSelector * QuotientSelector)) + Err)
  (handle_err : State -> Err -> option State) :
  nat -> State -> forall n m, CospanHyperGraph T' n m ->
  State * CospanHyperGraph T' n m + Err :=
  fix go fuel st n m tgt {struct fuel} :=
  match fuel return _ + Err with
  | 0 => 
    match select_rewrite st n m tgt with
    | inr e => inr e
    | inl (st', None) => inl (st', tgt)
    | inl (st', Some _) => 
      inr out_of_fuel_failure
    end
  | S fuel =>
    let handle (st : State) (err : Err) :=
      match handle_err st err with
      | Some st' => go fuel st' n m tgt
      | None => inr err
      end in
    match select_rewrite st n m tgt with
    | inr e => (* rewrite selection error! *)
      handle st e
    | inl (st', None) => (* no rewrite to perform *)
      inl (st', tgt)
    | inl (st', Some (do_par, idx, match_num, quot_num)) =>
      let '(existT (i, j) (lhs, rhs)) := idx_to_graphs idx in

      match select_context i j lhs n m tgt match_num quot_num with
      | inr e =>
        handle st' e
      | inl ctx =>
        if negb (default_graph_iso_test tgt (make_pushout lhs ctx)) then
          handle st' nonisomorphic_match_failure else
        if negb (PRO_gen_quoted_multi_context_domainb P graph_to_term ctx) then
          handle st' not_in_domain_ctx_failure else
        match do_par with
        | Some par_st =>
          match go fuel par_st n _ ctx with
          | inr e => handle par_st e
          | inl (_st, ctx') =>
            (* TODO: Do I need to check anything here? *)
            go fuel st' n m (make_pushout rhs ctx')
          end
        | None =>
          (* TODO: Do I need to check anything here? *)
          go fuel st' n m (make_pushout rhs ctx)
        end
      end
    end
  end.






(*
    forall n m (tlhs )

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
  Some res. *)

Definition graph_rel_of_PRO_rel
  `{StructGraphable Struct T', Equiv T'}
  (R : forall n m, relation (PRO Struct T' n m))
  n m : relation (CospanHyperGraph T' n m) :=
  fun Gl Gr => exists l r, PRO_graph_semantics l ≡ₛ Gl /\
    PRO_graph_semantics r ≡ₛ Gr /\ R n m l r.

#[export] Instance graph_rel_of_PRO_rel_symm
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (R : forall n m, relation (PRO Struct T' n m))
  {HRsymm : forall n m, Symmetric (R n m)} n m :
  Symmetric (graph_rel_of_PRO_rel R n m).
Proof.
  unfold Symmetric, graph_rel_of_PRO_rel.
  naive_solver.
Qed.


Lemma graph_rel_of_PRO_rel_trans
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (P : forall n m, PRO Struct T' n m -> Prop)
  (R : forall n m, relation (PRO Struct T' n m))
  {HRtrans : forall n m, Transitive (R n m)}
  (HRgraph : forall n m p q, PRO_graph_semantics p ≡ₛ PRO_graph_semantics q ->
    P n m p -> P n m q -> R n m p q)
  (HRP : forall n m p q, R n m p q -> P n m p /\ P n m q) n m :
  Transitive (graph_rel_of_PRO_rel R n m).
Proof.
  unfold Transitive, graph_rel_of_PRO_rel.
  intros l t r (Pl & Pt & HPl & HPt & HPlt)
    (Pt' & Pr & HPt' & HPr & HPt'r).
  exists Pl, Pr.
  split_and!; [done..|].
  rewrite HPlt, <- HPt'r.
  rewrite <- HPt' in HPt.
  apply HRP in HPlt, HPt'r.
  eapply HRgraph; [done|easy..].
Qed.

Lemma graph_rel_of_PRO_rel_refl
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (P : forall n m, PRO Struct T' n m -> Prop)
  (R : forall n m, relation (PRO Struct T' n m))
  (HRrefl : forall n m p, P n m p -> R n m p p) n m g :
  (exists t, PRO_graph_semantics t ≡ₛ g /\ P n m t) ->
  graph_rel_of_PRO_rel R n m g g.
Proof.
  intros (t & Htg & Ht).
  exists t, t.
  split_and!; [done..|].
  now apply HRrefl.
Qed.

Lemma graph_rel_of_PRO_rel_syntactic_eq
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (P : forall n m, PRO Struct T' n m -> Prop)
  (R : forall n m, relation (PRO Struct T' n m))
  (HRgraph : forall n m p q, PRO_graph_semantics p ≡ₛ PRO_graph_semantics q ->
    P n m p -> P n m q -> R n m p q) n m g g' :
  (exists t, PRO_graph_semantics t ≡ₛ g /\ P n m t) ->
  (exists t', PRO_graph_semantics t' ≡ₛ g' /\ P n m t') ->
  g ≡ₛ g' ->
  graph_rel_of_PRO_rel R n m g g'.
Proof.
  intros (t & Htg & Ht) (t' & Ht'g & Ht') Hgg'.
  exists t, t'.
  split_and!; [done..|].
  apply HRgraph; [|done..].
  now rewrite Htg, Ht'g.
Qed.

#[export] Instance graph_rel_of_PRO_rel_comp
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (R : forall n m, relation (PRO Struct T' n m))
  (HRcomp : forall n m o, Proper (R n m ==> R m o ==> R n o) Pcompose)
  n m o :
  Proper (graph_rel_of_PRO_rel R n m ==> graph_rel_of_PRO_rel R m o ==>
  graph_rel_of_PRO_rel R n o) compose_graphs.
Proof.
  intros l l' (Pl & Pl' & HPl & HPl' & HPll')
    r r' (Pr & Pr' & HPr & HPr' & HPrr').
  exists (Pl ;; Pr)%pro, (Pl' ;; Pr')%pro.
  cbn.
  split_and!; [f_equiv; done..|].
  now f_equiv.
Qed.

#[export] Instance graph_rel_of_PRO_rel_stack
  `{StructGraphable Struct T', Equiv T', Equivalence T' equiv}
  (R : forall n m, relation (PRO Struct T' n m))
  (HRstack : forall n m o p, Proper (R n m ==> R o p ==> R _ _) Pstack)
  n m o p :
  Proper (graph_rel_of_PRO_rel R n m ==> graph_rel_of_PRO_rel R o p ==>
  graph_rel_of_PRO_rel R _ _) stack_graphs.
Proof.
  intros l l' (Pl & Pl' & HPl & HPl' & HPll')
    r r' (Pr & Pr' & HPr & HPr' & HPrr').
  exists (Pl * Pr)%pro, (Pl' * Pr')%pro.
  cbn.
  split_and!; [f_equiv; done..|].
  now f_equiv.
Qed.

Lemma PRO_gen_quoted_multi_context_domainb_correct
  `{StructGraphable Struct T', Countable T'}
  (P : forall n m, PRO Struct T' n m -> Prop)
  {HP : forall n m p, Decision (P n m p)}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m g p, graph_to_term n m g = Some p ->
    PRO_graph_semantics p ≡ₛ g)
  {n ijm}
  (ctx : CospanHyperGraph T' n (ijm)) :
  PRO_gen_quoted_multi_context_domainb P graph_to_term ctx ->
  exists Pctx, PRO_graph_semantics Pctx ≡ₛ ctx /\ P n _ Pctx.
Proof.
  unfold PRO_gen_quoted_multi_context_domainb.
  destruct (graph_to_term _ _ ctx) as [Pctx|] eqn:HPctx; [|done].
  cbn.
  case_guard; [|done].
  intros _.
  exists Pctx.
  eauto.
Qed.

Lemma PRO_gen_quoted_multi_context_domainb_correct'
  `{StructGraphable Struct T', Countable T'}
  (P : forall n m, PRO Struct T' n m -> Prop)
  {HP : forall n m p, Decision (P n m p)}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m g p, graph_to_term n m g = Some p ->
    PRO_graph_semantics p ≡ₛ g)
  {n ijm}
  (ctx : CospanHyperGraph T' n (ijm)) :
  BoolSpec (exists Pctx, PRO_graph_semantics Pctx ≡ₛ ctx /\ P n _ Pctx)
    True (PRO_gen_quoted_multi_context_domainb P graph_to_term ctx).
Proof.
  destruct (PRO_gen_quoted_multi_context_domainb _ _ _) eqn:Heq; constructor; [|done].
  apply Is_true_true in Heq.
  revert Heq.
  now apply PRO_gen_quoted_multi_context_domainb_correct.
Qed.

Definition PRO_gen_quoted_graph_multi_rewrite_aux_correct
  `{StructGraphable Struct T', Countable T'}
  `{StructAuto : !SubStruct Autonomy Struct,
  SubStructG : !SubStructGraphable Autonomy Struct T'}
  (P : forall n m, PRO Struct T' n m -> Prop)
  {HP : forall n m p, Decision (P n m p)}
  (HPid : forall n, P n n (Pid n))
  (HPstr : forall n m s, P n m (Pstruct n m s))
  (R : forall n m, relation (PRO Struct T' n m))
  (HRrefl : forall n m p, P n m p -> R n m p p)
  {HRsymm : forall n m, Symmetric (R n m)}
  {HRtrans : forall n m, Transitive (R n m)}
  (HRcomp : forall n m o, Proper (R n m ==> R m o ==> R n o) Pcompose)
  (HRstack : forall n m o p, Proper (R n m ==> R o p ==> R _ _) Pstack)
  (HRgraph : forall n m p q, PRO_graph_semantics p ≡ₛ PRO_graph_semantics q ->
    P n m p -> P n m q -> R n m p q)
  (HRP : forall n m p q, R n m p q -> P n m p /\ P n m q)

  (MatchSelector QuotientSelector Err : Type) `{Matching_failures Err}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m g p, graph_to_term n m g = Some p ->
    PRO_graph_semantics p ≡ₛ g)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)

  {Idx State}
  (idx_to_graphs : Idx -> BundledEqn (CospanHyperGraph T'))
  (select_rewrite : State -> forall n m, CospanHyperGraph T' n m ->
    State * option ((option State (* To rewrite in parallel on the context *) *
      Idx * MatchSelector * QuotientSelector)) + Err)
  (handle_err : State -> Err -> option State)
  (Hidxs_to_graphs : forall idx i j (lhs rhs : CospanHyperGraph T' i j),
    idx_to_graphs idx = existT (i, j) (lhs, rhs) ->
    graph_rel_of_PRO_rel R i j lhs rhs) :
  forall fuel st n m tgt,
    (exists Ptgt, PRO_graph_semantics Ptgt ≡ₛ tgt /\ P _ _ Ptgt) ->
  forall stres res,
  PRO_gen_quoted_graph_multi_rewrite_aux P graph_to_term select_context
    idx_to_graphs select_rewrite handle_err fuel st n m tgt = inl (stres, res) ->
  graph_rel_of_PRO_rel R n m tgt res.
Proof.
  assert (HPcomp : forall n m o p q, P n m p -> P m o q -> P n o (p ;; q)%pro). 1:{
    intros n m o p q Hp Hq.
    apply (HRP n o (p ;; q) (p ;; q))%pro.
    f_equiv; now apply HRrefl.
  }
  assert (HPstack : forall n m n' m' p q, P n m p -> P n' m' q -> P _ _ (p * q)%pro). 1:{
    intros n m n' m' p q Hp Hq.
    apply (HRP _ _ (p * q) (p * q))%pro.
    f_equiv; now apply HRrefl.
  }
  intros fuel.
  induction fuel. 1:{
    intros st n m tgt Htgt stres res.
    cbn.
    case_match; [|done].
    do 2 case_match; [done|].
    intros [= <- <-].
    apply (graph_rel_of_PRO_rel_refl P); eauto.
  }
  intros st n m tgt HPtgt stres res.
  cbn delta [PRO_gen_quoted_graph_multi_rewrite_aux] beta fix match.
  set (handle := λ _ _, _).
  cbv zeta.
  assert (Hhandle : forall st e, handle st e = inl (stres, res) ->
    graph_rel_of_PRO_rel R n m tgt res). 1:{
    intros st' e.
    unfold handle.
    case_match; [|done].
    apply IHfuel; done.
  }
  destruct (select_rewrite st n m tgt) as
    [rwsel|e]; [|now apply Hhandle].
  destruct rwsel as [st' [(((do_par, idx), match_num), quot_num)|]]; cycle 1.
  1:{
    intros [= <- <-].
    apply (graph_rel_of_PRO_rel_refl P); done.
  }
  destruct (idx_to_graphs idx) as [(i, j) (lhs, rhs)] eqn:Hidx.
  destruct (select_context _ _ _ _ _ _ _ _) as [ctx|]; [|apply Hhandle].
  destruct (default_graph_iso_test_correct' tgt (make_pushout lhs ctx)) as [Hiso|]; [|apply Hhandle].
  cbn [negb].
  destruct (PRO_gen_quoted_multi_context_domainb_correct' P _ Hgraph_to_term ctx)
    as [HPctx|]; [|apply Hhandle].
  cbn [negb].

  apply Hidxs_to_graphs in Hidx as (Plhs & Prhs & HPlhs & HPrhs & Hlrhs).
  apply HRP in Hlrhs as Hlrhs'.
  destruct Hlrhs'.
  destruct HPtgt as (Ptgt & HPtgt & HPPtgt).
  destruct HPctx as (Pctx & HPctx & HPPctx).
  cbn [fst snd] in *.

  specialize (graph_rel_of_PRO_rel_trans P R HRgraph HRP) as Hgrtrans.
  specialize (graph_rel_of_PRO_rel_symm R) as Hgrsymm.

  assert (PRO_graph_semantics (Pctx;; (Prhs * Pid j;; Pcap j) * Pid m) ≡ₛ make_pushout rhs ctx
    ∧ P n m (Pctx;; (Prhs * Pid j;; Pcap j) * Pid m)%pro) as [Hctxr HPctxr].  1:{
    split; [|by eauto].
    cbn.
    unfold make_pushout.
    f_equiv; [done|].
    rewrite graph_of_struct_includeStruct.
    cbn.
    f_equiv.
    f_equiv.
    f_equiv.
    done.
  }

  assert (PRO_graph_semantics (Pctx;; (Plhs * Pid j;; Pcap j) * Pid m) ≡ₛ make_pushout lhs ctx
    ∧ P n m (Pctx;; (Plhs * Pid j;; Pcap j) * Pid m)%pro) as [Hctxl HPctxl].  1:{
    split; [|by eauto].
    cbn.
    unfold make_pushout.
    f_equiv; [done|].
    rewrite graph_of_struct_includeStruct.
    cbn.
    f_equiv.
    f_equiv.
    f_equiv.
    done.
  }
  assert (Htgt_push : graph_rel_of_PRO_rel R n m tgt (make_pushout lhs ctx)). 1:{
    apply (graph_rel_of_PRO_rel_syntactic_eq P); [done|by eauto..|].
    done.
  }

  assert (Hpushlr : graph_rel_of_PRO_rel R n m (make_pushout lhs ctx) (make_pushout rhs ctx)). 1:{
    eexists _, _.
    split_and!; [by eauto..|].
    apply HRcomp; [auto|].
    f_equiv; [|auto].
    f_equiv; [|eauto].
    f_equiv; [|auto].
    done.
  }
  rewrite Htgt_push, Hpushlr.

  assert (Hhandle' : forall st e, handle st e = inl (stres, res) ->
    graph_rel_of_PRO_rel R n m (make_pushout rhs ctx) res). 1:{
    intros ? ? Hrw%Hhandle.
    eapply Hgrtrans, Hrw.
    apply Hgrsymm.
    eapply Hgrtrans, Hpushlr.
    done.
  }

  destruct do_par as [par_st|].
  - destruct (PRO_gen_quoted_graph_multi_rewrite_aux _ _ _ _ _ _ _ _ _ _ _)
      as [(_st,ctx')|] eqn:Hctx'; [|apply Hhandle'].
    apply IHfuel in Hctx' as Hctxrel. 2:{ eauto. }
    pose proof Hctxrel as (Pctx_ & Pctx' & HPctx_ & HPctx' & HPPctx').
    apply HRP in HPPctx' as [_ HPPctx'].
    clear Pctx_ HPctx_.

    assert (PRO_graph_semantics (Pctx';; (Prhs * Pid j;; Pcap j) * Pid m) ≡ₛ make_pushout rhs ctx'
      ∧ P n m (Pctx';; (Prhs * Pid j;; Pcap j) * Pid m)%pro) as [Hctx'r HPctx'r].  1:{
      split; [|by eauto].
      cbn.
      unfold make_pushout.
      f_equiv; [done|].
      rewrite graph_of_struct_includeStruct.
      cbn.
      f_equiv.
      f_equiv.
      f_equiv.
      done.
    }

    intros Hpush.

    apply IHfuel in Hpush as Hrel. 2:{ eauto. }
    eapply Hgrtrans, Hrel.
    unfold make_pushout.
    f_equiv; [done|].
    apply (graph_rel_of_PRO_rel_refl P R HRrefl).
    exists ((Prhs * Pid j ;; Pcap j) * Pid m)%pro.
    split; [|by eauto].
    cbn.
    rewrite graph_of_struct_includeStruct.
    cbn.
    do 3 f_equiv.
    done.

  - intros Hpush.

    cbn [fst snd] in *.
    apply IHfuel in Hpush as Hrel. 2:{
      eauto.
    }
    eapply Hgrtrans, Hrel.
    apply (graph_rel_of_PRO_rel_refl P R HRrefl).
    eauto.
Qed.


Record PRO_graph_rewriter
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MatchSelector QuotientSelector Idx State Err : Type} := {
  (* PGR_err :: Matching_failures Err; *)
  PGR_idx_to_graphs : Idx -> BundledEqn (CospanHyperGraph T');
  PGR_select_rewrite : State -> forall n m, CospanHyperGraph T' n m ->
    State * option ((option State (* To rewrite in parallel on the context *) *
      Idx * MatchSelector * QuotientSelector)) + Err;
  PGR_handle_err : State -> Err -> option State;
  PGR_Hidxs_to_graphs : forall idx i j (lhs rhs : CospanHyperGraph T' i j),
    PGR_idx_to_graphs idx = existT (i, j) (lhs, rhs) ->
    graph_rel_of_PRO_rel R i j lhs rhs;
  PGR_fuel {n m} : CospanHyperGraph T' n m -> nat;
  PGR_init {n m} : CospanHyperGraph T' n m -> State;
}.

#[global] Arguments PRO_graph_rewriter { _ _ _ _ _} _ _ _ _ _ _ : assert.


Definition PRO_gen_quote_graph_multi_rewrite_aux
  `{FreeStructGraphable Struct, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  {MatchSelector QuotientSelector Err : Type} `{Matching_failures Err}
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)
  (f : T' -> T)
  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (R n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)
  {n m} (Qtgt : PRO Struct T' n m) : State * PRO Struct T' n m + Err :=
  let tgt := PRO_graph_semantics Qtgt in
  match
    PRO_gen_quoted_graph_multi_rewrite_aux (λ n m p, R.(pro_rewriting_domain) (PRO_denote f p))
      graph_to_term select_context
      RWS.(PGR_idx_to_graphs) RWS.(PGR_select_rewrite) RWS.(PGR_handle_err)
      (RWS.(PGR_fuel) tgt)
      (RWS.(PGR_init) tgt) _ _ tgt with
  | inr e => inr e
  | inl (st, res) =>
    match graph_to_term n m res with
    | None => (* This really shouldn't happen... *)
      inr not_in_domain_ctx_failure
    | Some Qres =>
      inl (st, Qres)
    end
  end.

Definition PRO_gen_quote_graph_multi_rewrite `{FreeStructGraphable Struct, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  {MatchSelector QuotientSelector Err : Type} `{Matching_failures Err}
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)
  (f : T' -> T)
  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (R n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)
  {n m} (Qtgt : PRO Struct T' n m) :
  PRO Struct T' n m + Err :=
  match PRO_gen_quote_graph_multi_rewrite_aux R graph_to_term
    select_context f RWS Qtgt with
  | inl (_, p) => inl p
  | inr e => inr e
  end.

Lemma PRO_gen_quote_graph_multi_rewrite_aux_correct
  `{FreeStructGraphable Struct, Countable T',
  EqT : Equiv T, EquivT : Equivalence T equiv}
  `{StructAuto : !SubStruct Autonomy Struct,
  SubStructG : !SubStructGraphable Autonomy Struct T'}
  `{EqStruct : forall n m, Equiv (Struct n m), EquivStruct : forall n m, @Equivalence (Struct n m) equiv}

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}

  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  {MatchSelector QuotientSelector Err : Type} `{Matching_failures Err}
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)
  (f : T' -> T)
  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (R n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)
  {n m} (Qtgt : PRO Struct T' n m) st Qres :
  pro_rewriting_domain R (PRO_denote f Qtgt) ->
  PRO_gen_quote_graph_multi_rewrite_aux R graph_to_term select_context f RWS Qtgt = inl (st, Qres) ->
  pro_rewriting_domain R (PRO_denote f Qres) -> R' n m Qtgt Qres.
Proof.
  intros Htgt.
  unfold PRO_gen_quote_graph_multi_rewrite_aux.
  destruct (PRO_gen_quoted_graph_multi_rewrite_aux _ _ _ _ _ _ _ _ _ _)
    as [(st', res)|] eqn:Hres; [|done].
  specialize (fun HPid HPstr =>
    PRO_gen_quoted_graph_multi_rewrite_aux_correct (λ n m p,
      pro_rewriting_domain R (PRO_denote f p)) HPid HPstr R') as HQres.
  do 3 tspecialize HQres by (intros; now apply R).
  do 2 tspecialize HQres by apply _.
  do 2 tspecialize HQres by (intros ** ? ? ?  ? ? ?;
    unfold R', rel_preimage; cbn; now f_equiv).
  tspecialize HQres. 1:{
    intros **; apply pro_rewriting_relation_graph_syntax; [done..|].
    rewrite 2 (PRO_graph_semantics_denote f).
    f_equiv; done.
  }
  tspecialize HQres. 1:{
    intros; now apply pro_rewriting_relation_to_domain.
  }
  specialize (HQres MatchSelector QuotientSelector Err _ graph_to_term
    Hgraph_to_term select_context _ _
    RWS.(PGR_idx_to_graphs) RWS.(PGR_select_rewrite)
    RWS.(PGR_handle_err) RWS.(PGR_Hidxs_to_graphs)).
  apply HQres in Hres; [|exists Qtgt; split; done].
  clear HQres.
  case_match eqn:HQres_eq; [|done].
  intros [= <- ->].
  intros HQresdom.
  destruct Hres as (Qtgt' & Qres' & HQtgt' & HQres' & HQtgtres').
  unfold R', rel_preimage in *.
  apply pro_rewriting_relation_to_domain in HQtgtres' as Hdom.
  destruct Hdom.
  pose proof (@cohg_syntactic_eq_equivalence T' _ _).
  etransitivity; [etransitivity; [|apply HQtgtres']|];
  (apply pro_rewriting_relation_graph_syntax; [done..|]);
  rewrite 2 PRO_graph_semantics_denote; f_equiv; [done|].
  rewrite HQres'.
  now apply Hgraph_to_term in HQres_eq.
Qed.






Lemma PRO_gen_quote_graph_multi_rewrite_correct
  `{FreeStructGraphable Struct,
  EqStruct : forall n m, Equiv (Struct n m),
  EquivStruct : forall n m, Equivalence (≡@{Struct n m}),
  EqT : Equiv T, EquivT : Equivalence T equiv, Countable T'}
  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{!SubStruct Autonomy Struct, !SubStructGraphable Autonomy Struct T'}

  (R : LawfulPRORewritingRelation Struct T)
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m))
  {MatchSelector QuotientSelector Err : Type} `{Matching_failures Err}
  (Hgraph_to_term : forall n m cohg p, graph_to_term n m cohg = Some p ->
    PRO_graph_semantics p ≡ₛ cohg)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err)
  (f : T' -> T)

  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (R n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)

  {n m} (tgt : PRO Struct T n m) :
  pro_rewriting_domain R tgt ->
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_graph_multi_rewrite R graph_to_term
    select_context f RWS Qtgt = inl Qres ->
  forall res, PRO_unquote f Qres res ->
  R.(pro_rewriting_domain) res ->
  (* Extraneous, but necessary in the abstract case here: *)
  R.(pro_rewriting_domain) (PRO_denote f Qtgt) ->
  R.(pro_rewriting_domain) (PRO_denote f Qres) ->
  R n m tgt res.
Proof.
  assert (Hf : Proper (equiv ==> equiv) f) by now intros ? ? [= <-].
  intros Htgt Qtgt HQtgt Qres HQres.
  unfold PRO_gen_quote_graph_multi_rewrite in HQres.
  case_match eqn:HQres_eq; [|done].
  case_match; subst.
  revert HQres; intros [= ->].
  intros res HQres Hdom.
  intros HPtgt' HPres'.
  apply (PRO_gen_quote_graph_multi_rewrite_aux_correct R graph_to_term
    Hgraph_to_term select_context f RWS) in HQres_eq; [|done..].
  unfold rel_preimage in HQres_eq.
  etransitivity; [etransitivity; [|apply HQres_eq]|].
  - apply pro_rewriting_relation_graph_syntax; [done..|].
    apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
    symmetry.
    apply quote_pro.
  - apply pro_rewriting_relation_graph_syntax; [done..|].
    apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
    apply find_denote_pro.
Qed.



Inductive PRO_gen_rewrite_match_selector :=
  | PROfrw_match_nat (n : nat)
  | PROfrw_match_maps (me : Piso) (mv : Pmap positive)
  | PROfrw_match_weak_maps (me mv : Pmap positive)
  (* TODO: add "match_extending" (with maps and nat), etc. *)
  .

Inductive PRO_gen_rewrite_quotient_selector :=
  | PROfrw_quotient_nat (n : nat)
  (* TODO: add "match_extending" (with maps and nat), etc. *)
  .

(* FIXME: Move *)
Definition Pmap_to_Piso (m : Pmap positive) : option Piso :=
  match decide (map_inj m) with
  | left Hinj => Some $ mk_Piso''_def m (bool_decide_eq_true_2 _ Hinj)
  | right _ =>None
  end.

Import stdpp.strings.

Inductive ProRWErr :=
  | Err_no_match
  | Err_no_quotient
  | Err_nonisomorphic_match
  | Err_not_in_domain_ctx
  | Err_out_of_fuel
  | Err_not_enough_isolated_vertices
  | Err_other (s : string).

#[export] Instance PropRWErr_dec : EqDecision (ProRWErr).
  intros p q.
  hnf.
  decide equality.
  apply String.eq_dec.
Defined.

#[export] Instance PropRWErr_matching_failures : Matching_failures ProRWErr := {
  no_match_failure := Err_no_match;
  nonisomorphic_match_failure := Err_nonisomorphic_match;
  not_in_domain_ctx_failure := Err_not_in_domain_ctx;
  out_of_fuel_failure := Err_out_of_fuel;
}.





Definition select_frobenius_context_selector `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : PRO_gen_rewrite_match_selector)
  (quotient_number : PRO_gen_rewrite_quotient_selector) :
    CospanHyperGraph T n ((i + j) + m) + ProRWErr :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then inr Err_not_enough_isolated_vertices else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)
  let ome_mv : option (Piso * Pmap positive) :=
    match match_number with
    | PROfrw_match_nat n => fst <$> frobenius_graph_matchings subcohg cohg !! n
    | PROfrw_match_maps me mv => Some (me, mv)
    | PROfrw_match_weak_maps me mv =>
      (., mv) <$> Pmap_to_Piso me
    end in
  match ome_mv with
  | None => inr Err_no_match
  | Some (me, mv) =>

  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv (map_img mv) in

  (* Then we get a candidate quotient *)
  let ores := match quotient_number with
  | PROfrw_quotient_nat n =>
    quotiented_contexts f_g_equiv_classes exploded_interfaced_context !! n
  end in
  match ores with
  | None => inr Err_no_quotient
  | Some res => inl res
  end
  end.


Definition select_bimonog_context_selector `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : PRO_gen_rewrite_match_selector)
  (quotient_number : PRO_gen_rewrite_quotient_selector) :
    CospanHyperGraph T n ((i + j) + m) + ProRWErr :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then inr Err_not_enough_isolated_vertices else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)
  let ome_mv : option (Piso * Pmap positive) :=
    match match_number with
    | PROfrw_match_nat n => fst <$> bimonog_graph_matchings subcohg cohg !! n
    | PROfrw_match_maps me mv => Some (me, mv)
    | PROfrw_match_weak_maps me mv =>
      (., mv) <$> Pmap_to_Piso me
    end in
  match ome_mv with
  | None => inr Err_no_match
  | Some (me, mv) =>

  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv (map_img mv) in

  (* Then we get a candidate quotient *)
  let ores := match quotient_number with
  | PROfrw_quotient_nat n =>
    (filter is_bimonogamousb $ quotiented_contexts f_g_equiv_classes
    exploded_interfaced_context) !! n
  end in
  match ores with
  | None => inr Err_no_quotient
  | Some res => inl res
  end
  end.


Lemma PRO_tensors_proper `{forall n m, Equiv (Struct n m), Equiv T} {n m} :
  Proper (equiv ==> Forall2 equiv) (@PRO_tensors Struct T n m).
Proof.
  intros p q Hp.
  induction Hp; [done..| | |].
  - cbn.
    constructor; [|done].
    done.
  - cbn.
    now f_equiv.
  - cbn.
    now f_equiv.
Qed.

Lemma PRO_to_diagram_equiv_is_Some `{ProLike Struct T D}
  `{forall n m, Equiv (Struct n m), Equiv T}
  {Htens : forall n m, Proper ((≡@{T}) ==> equiv) (ofTensor n m)}
  {n m} (p q : PRO Struct T n m) : p ≡ q ->
  is_Some (PRO_to_diagram p) <-> is_Some (PRO_to_diagram q).
Proof.
  intros Hpq%PRO_tensors_proper.
  rewrite 2 PRO_to_diagram_is_Some.
  induction Hpq as [|[[]] [[]] ? ? Heq]; [done|].
  rewrite 2 Forall_cons.
  f_equiv; [|done].
  destruct Heq as [[= <- <-] Ht].
  apply (f_equiv (RA:=equiv) is_Some).
  f_equiv.
  done.
Qed.

Lemma LawfulProLike_PRO_frobenius_quote_multi_rewrite_correct_aux `{Countable T'}
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    StructFrob : !SubStruct Frobenial Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T'}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_FPROP')
  (MatchSelector := PRO_gen_rewrite_match_selector)
  (QuotientSelector := PRO_gen_rewrite_quotient_selector)
  (Err := ProRWErr)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err := fun i j lhs n m =>
    select_frobenius_context_selector lhs)
  (f : T' -> T)

  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (RW n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)

  {n m} (dtgt : D n m) :
  forall tgt : PRO Struct T n m,
  DiagramQuote dtgt tgt ->
  (* pro_rewriting_domain R tgt -> *)
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_graph_multi_rewrite RW graph_to_term
    select_context f RWS Qtgt = inl Qres ->
  forall res, PRO_unquote f Qres res ->
  (* R.(pro_rewriting_domain) res -> *)
  (* Extraneous, but necessary in the abstract case here: *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qtgt) -> *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qres) -> *)
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros tgt Htgt Qtgt HQtgt Qres HQres_eq res HQres dres Hres.
  pose proof (PRO_gen_quote_graph_multi_rewrite_correct RW graph_to_term
    (fun n m => graph_to_FPROP'_correct) select_context f RWS tgt) as Hequiv.
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Quote; eauto.
  }
  specialize (Hequiv _ _).
  specialize (Hequiv _ HQres_eq).
  specialize (Hequiv _ _).
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Denote; eauto.
  }
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Quote with dtgt; [done|].
    eapply DiagramQuote_proper_semantics; [eauto|.. |eauto];
    pose proof (@quote_pro _ _ _ _ _ _ _ _ _ _ HQtgt) as Hrw;
    [unshelve (eapply PRO_to_diagram_equiv_is_Some; done);
    eapply ofTensor_proper; apply _|].
    rewrite <- 2 PRO_graph_semantics_correct.
    apply graph_semantics_syntactic_eq.
    now apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
  }
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Denote with dres; [done|].
    eapply DiagramDenote_proper_semantics; [eauto|.. |eauto];
    pose proof (@quote_pro _ _ _ _ _ _ _ _ _ _ HQres) as Hrw;
    [unshelve (eapply PRO_to_diagram_equiv_is_Some; done);
    eapply ofTensor_proper; apply _|].
    rewrite <- 2 PRO_graph_semantics_correct.
    apply graph_semantics_syntactic_eq.
    now apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
  }
  destruct Hequiv as (dtgt' & dres' & Hdtgt' & Hdres' & Hequiv).
  etransitivity; [etransitivity; [|apply Hequiv]|].
  - eapply quote_unique; [done|now apply DiagramQuote_iff_DiagramDenote].
  - eapply denote_unique; eauto.
Qed.


Lemma LawfulProLike_PRO_autonomous_quote_multi_rewrite_correct_aux `{Countable T'}
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T'}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_APROP')
  (MatchSelector := PRO_gen_rewrite_match_selector)
  (QuotientSelector := PRO_gen_rewrite_quotient_selector)
  (Err := ProRWErr)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err := fun i j lhs n m =>
    select_bimonog_context_selector lhs)
  (f : T' -> T)

  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (RW n m))
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)

  {n m} (dtgt : D n m) :
  forall tgt : PRO Struct T n m,
  DiagramQuote dtgt tgt ->
  (* pro_rewriting_domain R tgt -> *)
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_graph_multi_rewrite RW graph_to_term
    select_context f RWS Qtgt = inl Qres ->
  forall res, PRO_unquote f Qres res ->
  (* R.(pro_rewriting_domain) res -> *)
  (* Extraneous, but necessary in the abstract case here: *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qtgt) -> *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qres) -> *)
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  intros tgt Htgt Qtgt HQtgt Qres HQres_eq res HQres dres Hres.
  pose proof (PRO_gen_quote_graph_multi_rewrite_correct RW graph_to_term
    (fun n m => graph_to_APROP'_correct) select_context f RWS tgt) as Hequiv.
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Quote; eauto.
  }
  specialize (Hequiv _ _).
  specialize (Hequiv _ HQres_eq).
  specialize (Hequiv _ _).
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Denote; eauto.
  }
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Quote with dtgt; [done|].
    eapply DiagramQuote_proper_semantics; [eauto|.. |eauto];
    pose proof (@quote_pro _ _ _ _ _ _ _ _ _ _ HQtgt) as Hrw;
    [unshelve (eapply PRO_to_diagram_equiv_is_Some; done);
    eapply ofTensor_proper; apply _|].
    rewrite <- 2 PRO_graph_semantics_correct.
    apply graph_semantics_syntactic_eq.
    now apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
  }
  tspecialize Hequiv. 1:{
    eapply LawfulProLike_RW_dom_of_Denote with dres; [done|].
    eapply DiagramDenote_proper_semantics; [eauto|.. |eauto];
    pose proof (@quote_pro _ _ _ _ _ _ _ _ _ _ HQres) as Hrw;
    [unshelve (eapply PRO_to_diagram_equiv_is_Some; done);
    eapply ofTensor_proper; apply _|].
    rewrite <- 2 PRO_graph_semantics_correct.
    apply graph_semantics_syntactic_eq.
    now apply PRO_graph_semantics_equiv_cohg_syntactic_eq.
  }
  destruct Hequiv as (dtgt' & dres' & Hdtgt' & Hdres' & Hequiv).
  etransitivity; [etransitivity; [|apply Hequiv]|].
  - eapply quote_unique; [done|now apply DiagramQuote_iff_DiagramDenote].
  - eapply denote_unique; eauto.
Qed.




Lemma LawfulProLike_PRO_to_diagram_Proper_equiv
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro) n m :
  Proper ((≡@{PRO Struct T n m}) ==> equiv) (PRO_to_diagram).
Proof.
  intros p q Hpq.
  induction Hpq.
  - done.
  - cbn.
    f_equiv.
    eapply ofStruct_proper; [apply _|done].
  - cbn.
    eapply ofTensor_proper; [apply _|done].
  - cbn.
    now f_equiv.
  - cbn.
    now f_equiv.
Qed.

Lemma LawfulProLike_RW_Proper_equiv
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro) n m :
  Proper (equiv ==> equiv ==> iff) (RW n m).
Proof.
  pose proof (LawfulProLike_PRO_to_diagram_Proper_equiv R A Struct T D LawPro) as HP.
  intros l l' Hl r r' Hr.
  split.
  - intros (dl & dr & Hdl & Hdr & Hlr).
    exists dl, dr.
    split_and!; [constructor..|done].
    + etransitivity; [apply HP; done|].
      apply diagram_denote.
    + etransitivity; [apply HP; done|].
      apply diagram_denote.
  - intros (dl & dr & Hdl & Hdr & Hlr).
    exists dl, dr.
    split_and!; [constructor..|done].
    + etransitivity; [apply HP; done|].
      apply diagram_denote.
    + etransitivity; [apply HP; done|].
      apply diagram_denote.
Qed.






Program Definition PGR_lemma `{Countable T'}
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (dlhs drhs : D n m)
  (Hdlrhs : dlhs ≡ drhs)
  (match_num quotient_num : nat)

  (f : T' -> T) lhs rhs
  (Hlhs : DiagramQuote dlhs lhs) (Hrhs : DiagramQuote drhs rhs)
  Qlhs Qrhs
  (HQlhs : PRO_quote f Qlhs lhs) (HQrhs : PRO_quote f Qrhs rhs) :
  PRO_graph_rewriter (fun n m => rel_preimage (PRO_denote f) (RW n m))
  PRO_gen_rewrite_match_selector PRO_gen_rewrite_quotient_selector
   () bool ProRWErr := {|
  PGR_idx_to_graphs := fun _ =>
    existT (n, m) (PRO_graph_semantics Qlhs, PRO_graph_semantics Qrhs);
  PGR_select_rewrite := fun b _ _ _ =>
    if b then inl (true, None) else
    inl (true, Some (None, (), PROfrw_match_nat match_num,
      PROfrw_quotient_nat quotient_num));
  PGR_handle_err _ _ := None;

  PGR_fuel _ _ _ := 1;
  PGR_init _ _ _ := false;
|}.
Next Obligation.
  intros * ? * ? * ? ? ? ? * ? ? * ? ? [] i j l' r' Heq.
  cbn in Heq.
  injection Heq.
  intros <- <-.
  apply existT_inj_r in Heq.
  injection Heq.
  intros <- <-.
  exists Qlhs, Qrhs.
  split_and!; [done..|].
  unfold rel_preimage.
  eapply (LawfulProLike_RW_Proper_equiv R A Struct T D LawPro _ _);
  [done..|].
  exists dlhs, drhs.
  split_and!; [now apply DiagramQuote_iff_DiagramDenote..|done].
Qed.

Definition PGR_seq `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (l : PRO_graph_rewriter R MS QS Idx State Err)
  (r : PRO_graph_rewriter R MS QS Idx' State' Err) :
  PRO_graph_rewriter R MS QS (Idx + Idx') (State + State') Err := {|
  PGR_idx_to_graphs i := match i with
    | inl i => l.(PGR_idx_to_graphs) i
    | inr i => r.(PGR_idx_to_graphs) i
    end;
  PGR_Hidxs_to_graphs i := match i with
    | inl i => l.(PGR_Hidxs_to_graphs) i
    | inr i => r.(PGR_Hidxs_to_graphs) i
    end;
  PGR_select_rewrite := 
    let rw_r rst n m tgt : 
      (State + State') * (option (option (State + State') * (Idx + Idx') * _ * _)) + Err :=
      match r.(PGR_select_rewrite) rst n m tgt with
      | inr e => inr e
      | inl (rst', orw) => inl (inr rst',
        match orw with
        | None => None
        | Some (orst_par, ridx, mn, qn) =>
          Some (fmap (M:=option) inr orst_par,
            inr ridx, mn, qn)
        end)
      end in
    fun st n m tgt =>
    match st with
    | inl lst => 
      match l.(PGR_select_rewrite) lst n m tgt with
      | inr e => inr e
      | inl (lst', Some (olst_par, lidx, mn, qn)) => inl (inl lst',
        Some ((lst_par ← olst_par; Some (inl lst_par)),
          inl lidx, mn, qn))
      | inl (lst', None) =>
        rw_r (r.(PGR_init) tgt) n m tgt
      end
    | inr rst => rw_r rst n m tgt
    end
      ;
  PGR_handle_err st e :=
    match st with
    | inl lst =>
      match l.(PGR_handle_err) lst e with
      | Some lst' => Some (inl lst')
      | None => None
      end
    | inr rst =>
      match r.(PGR_handle_err) rst e with
      | Some rst' => Some (inr rst')
      | None => None
      end
    end;
  PGR_init n m Gtgt := inl (l.(PGR_init) Gtgt);
  PGR_fuel n m Gtgt :=
    l.(PGR_fuel) Gtgt + r.(PGR_fuel) Gtgt
|}.

Import stdpp.pretty.
(*
Definition PGR_repeat_k `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State}
  (k : nat)
  (not_enough_rewrites : nat -> nat -> Err)
  (l : PRO_graph_rewriter R MS QS Idx State ProRWErr) :
  PRO_graph_rewriter R MS QS Idx (nat * State) ProRWErr := {|
  PGR_idx_to_graphs i := l.(PGR_idx_to_graphs) i;
  PGR_Hidxs_to_graphs i := l.(PGR_Hidxs_to_graphs) i;
  PGR_select_rewrite '(n, st) n m tgt :=
    match n with
    | 0 => inl ((0, st), None)
    | S n' =>
      match l.(PGR_select_rewrite) st n m tgt with
      | inr e => inr e
      | inl (st', Some (ost_par, idx, mn, qn)) =>
        inl ((n', st'),
        Some ((st_par ← ost_par; Some (n', st_par)),
          idx, mn, qn))
      | inl (st', None) =>
        inr (Err_other ("cannot perform enough rewrites (performed "
          ++ pretty (k - n) ++ " of " ++ pretty k ++ ")")%string)
      end
    end;
  PGR_handle_err '(n, st) e :=
    (n,.) <$> l.(PGR_handle_err) st e;
  PGR_fuel n m Gtgt := k * l.(PGR_fuel) Gtgt;
  PGR_init n m Gtgt := (k, l.(PGR_init) Gtgt);
|}.
 *)

Definition PGR_repeat_k `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State}
  (k : nat)
  (l : PRO_graph_rewriter R MS QS Idx State ProRWErr) :
  PRO_graph_rewriter R MS QS Idx (nat * State) ProRWErr := {|
  PGR_idx_to_graphs i := l.(PGR_idx_to_graphs) i;
  PGR_Hidxs_to_graphs i := l.(PGR_Hidxs_to_graphs) i;
  PGR_select_rewrite '(nst, st) n m tgt :=
    match nst with
    | 0 => inl ((0, st), None)
    | S nst' =>
      match l.(PGR_select_rewrite) st n m tgt with
      | inr e => inr e
      | inl (st', Some (ost_par, idx, mn, qn)) =>
        inl ((S nst', st'),
        Some ((st_par ← ost_par; Some (nst', st_par)),
          idx, mn, qn))
      | inl (st', None) =>
        match l.(PGR_select_rewrite) (l.(PGR_init) tgt) n m tgt with
        | inr e => inr e
        | inl (st', Some (ost_par, idx, mn, qn)) =>
          inl ((nst', st'),
          Some ((st_par ← ost_par; Some (nst', st_par)),
            idx, mn, qn))
        | _ => 
          inr (Err_other ("cannot perform enough rewrites (performed "
            ++ pretty (k - nst) ++ " of " ++ pretty k ++ ")")%string)
        end
      end
    end;
  PGR_handle_err '(n, st) e :=
    (n,.) <$> l.(PGR_handle_err) st e;
  PGR_fuel n m Gtgt := k * l.(PGR_fuel) Gtgt;
  PGR_init n m Gtgt := (k, l.(PGR_init) Gtgt);
|}.

Definition PGR_repeat_upto_k `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State}
  (k : nat)
  (l : PRO_graph_rewriter R MS QS Idx State ProRWErr) :
  PRO_graph_rewriter R MS QS Idx (nat * State) ProRWErr := {|
  PGR_idx_to_graphs i := l.(PGR_idx_to_graphs) i;
  PGR_Hidxs_to_graphs i := l.(PGR_Hidxs_to_graphs) i;
  PGR_select_rewrite '(nst, st) n m tgt :=
    match nst with
    | 0 => inl ((0, st), None)
    | S nst' =>
      match l.(PGR_select_rewrite) st n m tgt with
      | inr e => inr e
      | inl (st', Some (ost_par, idx, mn, qn)) =>
        inl ((S nst', st'),
        Some ((st_par ← ost_par; Some (nst', st_par)),
          idx, mn, qn))
      | inl (st', None) =>
        match l.(PGR_select_rewrite) (l.(PGR_init) tgt) n m tgt with
        | inr e => inr e
        | inl (st', Some (ost_par, idx, mn, qn)) =>
          inl ((nst', st'),
          Some ((st_par ← ost_par; Some (nst', st_par)),
            idx, mn, qn))
        | inl (st', None) => 
          inl ((0, st'), None)
        end
      end
    end;
  PGR_handle_err '(n, st) e :=
    (n,.) <$> l.(PGR_handle_err) st e;
  PGR_fuel n m Gtgt := k * l.(PGR_fuel) Gtgt;
  PGR_init n m Gtgt := (k, l.(PGR_init) Gtgt);
|}.

Definition PGR_try_catch_gen `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (onerr : State -> Err -> option State)
  (l : PRO_graph_rewriter R MS QS Idx State Err) :
  PRO_graph_rewriter R MS QS Idx State Err := {|
  PGR_idx_to_graphs := l.(PGR_idx_to_graphs);
  PGR_Hidxs_to_graphs := l.(PGR_Hidxs_to_graphs);
  PGR_select_rewrite := l.(PGR_select_rewrite);
  PGR_fuel n m := l.(PGR_fuel);
  PGR_init n m := l.(PGR_init);
  PGR_handle_err st e :=
    match l.(PGR_handle_err) st e with
    | Some st' => Some st'
    | None => onerr st e
    end
|}.

Definition PGR_try_catch `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (catch : Err -> bool)
  (l : PRO_graph_rewriter R MS QS Idx State Err) :
  PRO_graph_rewriter R MS QS Idx State Err :=
  PGR_try_catch_gen (λ s e, if catch e then Some s else None) l.


Definition PGR_repeat `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (max_iters : forall n m, CospanHyperGraph T' n m -> nat)
  (l : PRO_graph_rewriter R MS QS Idx State Err) :
  PRO_graph_rewriter R MS QS Idx (nat * State) Err := {|
  PGR_idx_to_graphs i := l.(PGR_idx_to_graphs) i;
  PGR_Hidxs_to_graphs i := l.(PGR_Hidxs_to_graphs) i;
  PGR_select_rewrite '(nst, st) n m tgt :=
    match nst with
    | 0 => inl ((0, st), None)
    | S nst' =>
      match l.(PGR_select_rewrite) st n m tgt with
      | inr e => inr e
      | inl (st', Some (ost_par, idx, mn, qn)) =>
        inl ((S nst', st'),
        Some ((st_par ← ost_par; Some (nst', st_par)),
          idx, mn, qn))
      | inl (st', None) =>
        match l.(PGR_select_rewrite) (l.(PGR_init) tgt) n m tgt with
        | inr e => inr e
        | inl (st', Some (ost_par, idx, mn, qn)) =>
          inl ((nst', st'),
          Some ((st_par ← ost_par; Some (nst', st_par)),
            idx, mn, qn))
        | inl (st', None) => 
          inl ((0, st'), None)
        end
      end
    end;
  PGR_handle_err '(n, st) e :=
    (n,.) <$> l.(PGR_handle_err) st e;
  PGR_fuel n m Gtgt := max_iters n m Gtgt * l.(PGR_fuel) Gtgt;
  PGR_init n m Gtgt := (max_iters n m Gtgt, l.(PGR_init) Gtgt);
|}.

Definition PGR_repeat_square_graph_size `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (l : PRO_graph_rewriter R MS QS Idx State Err) :
  PRO_graph_rewriter R MS QS Idx (nat * State) Err :=
  PGR_repeat (fun n m Gtgt =>
    let s := size (hyperedges Gtgt) in s * s * l.(PGR_fuel) Gtgt) l.

Definition PGR_with_par `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (rw : PRO_graph_rewriter R MS QS Idx State Err)
  (par : PRO_graph_rewriter R MS QS Idx' State' Err) :
  PRO_graph_rewriter R MS QS (Idx + Idx') (bool * State * State') Err := {|
  PGR_idx_to_graphs i := match i with
    | inl i => rw.(PGR_idx_to_graphs) i
    | inr i => par.(PGR_idx_to_graphs) i
    end;
  PGR_Hidxs_to_graphs i := match i with
    | inl i => rw.(PGR_Hidxs_to_graphs) i
    | inr i => par.(PGR_Hidxs_to_graphs) i
    end;
  PGR_select_rewrite := fun st n m tgt =>
    let '(is_nonpar, lst, rst) := st in
    if is_nonpar :> bool then
      match rw.(PGR_select_rewrite) lst n m tgt with
      | inr e => inr e
      | inl (lst', Some (olst_par, lidx, mn, qn)) => inl ((true, lst', rst),
        Some (
          match olst_par with
          | Some lst_par => (Some (true, lst_par, rst),
            inl lidx, mn, qn)
          | None => (Some (false, lst', rst), inl lidx, mn, qn)
          end))
      | inl (lst', None) => inl ((true, lst', rst), None)
      end
    else
      match par.(PGR_select_rewrite) rst n m tgt with
      | inr e => inr e
      | inl (rst', orw) =>
        inl ((false, lst, rst'),
          match orw with
          | None => None
          | Some (orst_par, ridx, mn, qn) =>
            Some ((rst_par ← orst_par; Some (false, lst, rst_par)),
              inr ridx, mn, qn)
          end)
      end
      ;
  PGR_handle_err '(is_nonpar, lst, rst) e :=
    if is_nonpar then
      match rw.(PGR_handle_err) lst e with
      | Some lst' => Some (true, lst', rst)
      | None => None
      end
    else
    match par.(PGR_handle_err) rst e with
      | Some rst' => Some (true, lst, rst')
      | None => None
      end;
  PGR_init n m Gtgt :=
    (true, rw.(PGR_init) Gtgt, par.(PGR_init) Gtgt);
  PGR_fuel n m Gtgt :=
    rw.(PGR_fuel) Gtgt + par.(PGR_fuel) Gtgt
|}.


Definition PGR_full_par `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (rw : PRO_graph_rewriter R MS QS Idx State Err) :
  PRO_graph_rewriter R MS QS Idx State Err := {|
  PGR_idx_to_graphs i := rw.(PGR_idx_to_graphs) i;
  PGR_Hidxs_to_graphs i := rw.(PGR_Hidxs_to_graphs) i;
  PGR_select_rewrite st n m tgt :=
    match rw.(PGR_select_rewrite) st n m tgt with
      | inr e => inr e
      | inl (st', Some (ost_par, lidx, mn, qn)) => inl (st',
        Some (
          match ost_par with
          | Some st_par => (Some st_par,
            lidx, mn, qn)
          | None => (Some (rw.(PGR_init) tgt), lidx, mn, qn)
          end))
      | inl (st', None) => inl (st', None)
      end;
  PGR_handle_err := rw.(PGR_handle_err);
  PGR_fuel n m Gtgt := rw.(PGR_fuel) Gtgt * rw.(PGR_fuel) Gtgt;
  PGR_init n m := rw.(PGR_init);
|}.


Definition PGR_choice `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (l : PRO_graph_rewriter R MS QS Idx State Err)
  (r : PRO_graph_rewriter R MS QS Idx' State' Err) :
  PRO_graph_rewriter R MS QS (Idx + Idx') (State * State') Err := {|
  PGR_idx_to_graphs i := match i with
    | inl i => l.(PGR_idx_to_graphs) i
    | inr i => r.(PGR_idx_to_graphs) i
    end;
  PGR_Hidxs_to_graphs i := match i with
    | inl i => l.(PGR_Hidxs_to_graphs) i
    | inr i => r.(PGR_Hidxs_to_graphs) i
    end;
  PGR_select_rewrite := fun st n m tgt =>
    let '(lst, rst) := st in
    match l.(PGR_select_rewrite) lst n m tgt with
    | inr e => inr e
    | inl (lst', Some (olst_par, lidx, mn, qn)) => inl ((lst', rst),
      Some ((lst_par ← olst_par; Some (lst_par, rst)),
        inl lidx, mn, qn))
    | inl (lst', None) =>
      match r.(PGR_select_rewrite) rst n m tgt with
      | inr e => inr e
      | inl (rst', orw) => inl ((lst, rst'),
        match orw with
        | None => None
        | Some (orst_par, ridx, mn, qn) =>
          Some ((rst_par ← orst_par; Some (lst, rst_par)),
            inr ridx, mn, qn)
        end)
      end
    end;
  PGR_handle_err '(lst, rst) e :=
    match l.(PGR_handle_err) lst e with
    | Some lst' => Some (lst', rst)
    | None =>
      match r.(PGR_handle_err) rst e with
      | Some rst' => Some (lst, rst')
      | None => None
      end
    end;
  PGR_init n m Gtgt :=
    (l.(PGR_init) Gtgt, r.(PGR_init) Gtgt);
  PGR_fuel n m Gtgt :=
    l.(PGR_fuel) Gtgt + r.(PGR_fuel) Gtgt
|}.


Definition PGR_none `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Err} :
  PRO_graph_rewriter R MS QS Empty_set unit Err := {|
  PGR_idx_to_graphs := Empty_set_rect _;
  PGR_Hidxs_to_graphs := Empty_set_rect _;
  PGR_select_rewrite := fun st n m tgt => inl (st, None);
  PGR_handle_err := fun st e => None;
  PGR_init n m Gtgt := ();
  PGR_fuel n m Gtgt := 0;
|}.

(* TODO: Refactor handle_err to return State + Err so we can support backtraces. *)

(* Inductive expr  := Const : nat -> expr | Op : expr -> expr -> expr
  | Smul : nat -> expr -> expr.

Declare Custom Entry expr.
Notation "'![' e ']'" := e (e custom expr at level 0).
Notation "x" := (Const x) (in custom expr at level 0, x bigint).
Notation "x + y" := (Op x y) (in custom expr at level 10,
  x custom expr, y custom expr).

Notation "x * y" := (Smul x y) (in custom expr at level 0,
  x bigint, y custom expr, right associativity).


Check ![ 5 * 7 ]. *)


#[universes(polymorphic=yes)]
Inductive rw_expr :=
  | rw_seq : rw_expr -> rw_expr -> rw_expr
  | rw_try : rw_expr -> rw_expr
  | rw_repeat_k : nat -> rw_expr -> rw_expr
  | rw_repeat_upto_k : nat -> rw_expr -> rw_expr
  | rw_repeat_star : rw_expr -> rw_expr
  | rw_with_par : rw_expr -> rw_expr -> rw_expr
  | rw_par_star : rw_expr -> rw_expr
  | rw_choice : rw_expr -> rw_expr -> rw_expr
  | rw_base (l2r : bool) {A} (lem : A) : rw_expr
  | rw_none : rw_expr.

Fixpoint flip_rw_expr (e : rw_expr) : rw_expr :=
  match e with
  | rw_seq l r => rw_seq (flip_rw_expr l) (flip_rw_expr r)
  | rw_try e => rw_try (flip_rw_expr e)
  | rw_repeat_k k e => rw_repeat_k k (flip_rw_expr e)
  | rw_repeat_upto_k k e => rw_repeat_upto_k k (flip_rw_expr e)
  | rw_repeat_star e => rw_repeat_star (flip_rw_expr e)
  | rw_with_par rw par => rw_with_par (flip_rw_expr rw) (flip_rw_expr par)
  | rw_par_star rw => rw_par_star (flip_rw_expr rw)
  | rw_choice l r => rw_choice (flip_rw_expr l) (flip_rw_expr r)
  | rw_base l2r lem => rw_base (if l2r then false else true) lem
  | rw_none => rw_none
  end.


Declare Custom Entry rw_expr.

Notation "'![rw' e ']'" := (e)
  (at level 0, e custom rw_expr at level 200, only parsing).


Notation "'(' e ')'" := (e)
  (in custom rw_expr at level 0, e custom rw_expr at level 200).


Notation "l , r" := (rw_seq l r)
  (l custom rw_expr, r custom rw_expr,
  in custom rw_expr at level 60, right associativity).

(* TODO: Better notation possible? Also maybe better name? This
  ignores errors, but doesn't force full success. *)
Notation "'try' e" := (rw_try e)
  (e custom rw_expr, in custom rw_expr at level 20, right associativity).

Notation "n '!' e" := (rw_repeat_k n%nat e)
  (n bigint, e custom rw_expr,
  in custom rw_expr at level 0, right associativity).

Notation "n '?' e" := (rw_repeat_upto_k n%nat e)
  (n bigint, e custom rw_expr,
  in custom rw_expr at level 0, right associativity).

Notation "'?' e" := (rw_repeat_star e)
  (e custom rw_expr,
  in custom rw_expr at level 0, right associativity).

Notation "'!' e" := (rw_seq e (rw_repeat_star e))
  (e custom rw_expr,
  in custom rw_expr at level 0, right associativity).


Notation "rw '>>' par" :=
    (rw_with_par rw par)
  (rw custom rw_expr, par custom rw_expr,
  in custom rw_expr at level 30, right associativity).


Notation "'<' rw '>*'" :=
    (rw_par_star rw)
  (rw custom rw_expr at level 200,
  in custom rw_expr at level 0).


Notation "l || r" := (rw_choice l r)
  (l custom rw_expr, r custom rw_expr,
  in custom rw_expr at level 50, right associativity).



Notation "'{' lem '}'" :=
    (rw_base true (lem))
    (lem constr at level 200,
    in custom rw_expr at level 10).

Notation "'{' lem 'at' n '}'" :=
    (rw_base true (lem, n))
    (lem constr at level 200, n bigint,
    in custom rw_expr at level 10).

Notation "'{' lem 'at' n 'quotient' q '}'" :=
    (rw_base true (lem, n, q))
    (lem constr at level 200, n bigint, q bigint,
    in custom rw_expr at level 10).

Notation "'{' lem 'quotient' q '}'" :=
    (rw_base true (lem, 0, q))
    (lem constr at level 200, q bigint,
    in custom rw_expr at level 10).

Notation "'{' <- lem '}'" :=
    (rw_base false (lem))
    (lem constr at level 200,
    in custom rw_expr at level 10).

Notation "'{' <- lem 'at' n '}'" :=
    (rw_base false (lem, n))
    (lem constr at level 200, n bigint,
    in custom rw_expr at level 10).

Notation "'{' <- lem 'at' n 'quotient' q '}'" :=
    (rw_base (lem, n, q))
    (lem constr at level 200, n bigint, q bigint,
    in custom rw_expr at level 10).

Notation "'{' <- lem 'quotient' q '}'" :=
    (rw_base false (lem, 0, q))
    (lem constr at level 200, q bigint,
    in custom rw_expr at level 10).

Notation "<- e" := (flip_rw_expr e) 
  (e custom rw_expr at level 20, in custom rw_expr at level 10).

(* Check ![rw < {Nat.add_0_r 4} >* >>  <- ? {<- 4}]. *)
(* Check ![rw < {Nat.add_0_r 4 quotient 0} >* >>  ? {4}]. *)



Class RWS_of_expr (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err} (RWS : PRO_graph_rewriter R MS QS Idx State Err) := {}.

Lemma RWS_of_expr_base_change
  {A} (a : A) {B} (b : B)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err} (RWS : PRO_graph_rewriter R MS QS Idx State Err) :
  RWS_of_expr ![rw {a}] RWS ->
  RWS_of_expr ![rw {b}] RWS.
Proof.
  done.
Qed.



Lemma RWS_of_expr_base_lemma_l2r `{Countable T'}
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
  {LawPro : LawfulProLike R A Struct T D}
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (dlhs drhs : D n m)
  (Hdlrhs : dlhs ≡ drhs)
  (match_num quotient_num : nat)

  (f : T' -> T) lhs rhs
  (Hlhs : DiagramQuote dlhs lhs) (Hrhs : DiagramQuote drhs rhs)
  Qlhs Qrhs
  (HQlhs : PRO_quote f Qlhs lhs) (HQrhs : PRO_quote f Qrhs rhs) :
  RWS_of_expr (rw_base true Hdlrhs)
  (PGR_lemma R A Struct T D LawPro dlhs drhs Hdlrhs match_num quotient_num
  f lhs rhs Hlhs Hrhs Qlhs Qrhs HQlhs HQrhs).
Proof.
  done.
Qed.

Lemma RWS_of_expr_base_lemma_r2l `{Countable T'}
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
  {LawPro : LawfulProLike R A Struct T D}
  `{FreeGraphS : FreeStructGraphable Struct,
    LawGraphS : !LawfulStructGraphable Struct T}
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)
  {n m} (dlhs drhs : D n m)
  (Hdlrhs : dlhs ≡ drhs)
  (match_num quotient_num : nat)

  (f : T' -> T) lhs rhs
  (Hlhs : DiagramQuote dlhs lhs) (Hrhs : DiagramQuote drhs rhs)
  Qlhs Qrhs
  (HQlhs : PRO_quote f Qlhs lhs) (HQrhs : PRO_quote f Qrhs rhs) :
  RWS_of_expr (rw_base false Hdlrhs)
  (PGR_lemma R A Struct T D LawPro drhs dlhs (symmetry Hdlrhs) match_num quotient_num
  f rhs lhs Hrhs Hlhs Qrhs Qlhs HQrhs HQlhs).
Proof.
  done.
Qed.






Lemma RWS_of_expr_seq (e e' : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err)
  (RWS' : PRO_graph_rewriter R MS QS Idx' State' Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr e' RWS' ->
  RWS_of_expr (rw_seq e e') (PGR_seq RWS RWS').
Proof.
  done.
Qed.


Lemma RWS_of_expr_with_par (e e' : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err)
  (RWS' : PRO_graph_rewriter R MS QS Idx' State' Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr e' RWS' ->
  RWS_of_expr (rw_with_par e e') (PGR_with_par RWS RWS').
Proof.
  done.
Qed.

Lemma RWS_of_expr_choice (e e' : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Idx' State' Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err)
  (RWS' : PRO_graph_rewriter R MS QS Idx' State' Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr e' RWS' ->
  RWS_of_expr (rw_choice e e') (PGR_choice RWS RWS').
Proof.
  done.
Qed.


Lemma RWS_of_expr_try (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr (rw_try e) (PGR_try_catch_gen (fun _ _ => None) RWS).
Proof.
  done.
Qed.

Lemma RWS_of_expr_repeat_k k (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State}
  (RWS : PRO_graph_rewriter R MS QS Idx State ProRWErr) :
  RWS_of_expr e RWS ->
  RWS_of_expr (rw_repeat_k k e) (PGR_repeat_k k RWS).
Proof.
  done.
Qed.

Lemma RWS_of_expr_repeat_upto_k k (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State}
  (RWS : PRO_graph_rewriter R MS QS Idx State ProRWErr) :
  RWS_of_expr e RWS ->
  RWS_of_expr (rw_repeat_upto_k k e) (PGR_repeat_upto_k k RWS).
Proof.
  done.
Qed.

Lemma RWS_of_expr_repeat_star (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr (rw_repeat_star e) (PGR_repeat_square_graph_size RWS).
Proof.
  done.
Qed.

Lemma RWS_of_expr_par_star (e : rw_expr)
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Idx State Err}
  (RWS : PRO_graph_rewriter R MS QS Idx State Err) :
  RWS_of_expr e RWS ->
  RWS_of_expr (rw_par_star e) (PGR_full_par RWS).
Proof.
  done.
Qed.


Lemma RWS_of_expr_none
  `{StructGraphable Struct T', Countable T'}
  {R : forall n m, relation (PRO Struct T' n m)}
  {MS QS Err} :
  RWS_of_expr (rw_none) (R:=R) (PGR_none (MS:=MS) (QS:=QS) (Err:=Err)).
Proof.
  done.
Qed.

Module quote_RWS.

Import Ltac2.Ltac2.

Ltac2 constr_list_of_pairs (e : constr) : constr list :=
  let rec go e :=
  lazy_match! e with
  | pair ?l ?r => List.append (go l) (go r)
  | _ => [e]
  end
  in go e.

Ltac2 solve_RWS_of_expr_aux_base (e : constr) :
  constr * constr * constr * constr * constr :=
  let es := constr_list_of_pairs e in 
  let es' := if Int.lt (List.length es) 3 then 
    List.append es (List.repeat '(Datatypes.O) (Int.sub 3 (List.length es))) else es in 
  let lem := List.nth es' 0 in 
  let match_num := List.nth es' 1 in 
  let quotient_num := List.nth es' 2 in 
  let lemT := Constr.type lem in 
  lazy_match! lemT with
  | ?_r ?lhs ?rhs => 
    (lhs, rhs, lem, match_num, quotient_num)
  end.


Ltac2 get_ref_flip_rw_expr () : Std.reference := reference:(flip_rw_expr).

(* 
Ltac2 solve_RWS_of_expr () : unit :=
  lazy_match! goal with
  | [|- RWS_of_expr ?e ?_rws] =>
    lazy_match! e with
    | rw_seq ?l ?r =>
      refine '(RWS_of_expr_seq $l $r _ _  _ _)
    | rw_try ?e =>
      refine '(RWS_of_expr_try $e _  _)
    | rw_repeat_k ?k ?e =>
      refine '(RWS_of_expr_repeat_k $k $e _  _)
    | rw_repeat_upto_k ?k ?e =>
      refine '(RWS_of_expr_repeat_upto_k $k $e _  _)
    | rw_repeat_star ?e =>
      refine '(RWS_of_expr_repeat_star $e _  _)
    | rw_with_par ?l ?r =>
      refine '(RWS_of_expr_with_par $l $r _ _  _ _)
    | rw_par_star ?e =>
      refine '(RWS_of_expr_par_star $e _  _)
    | rw_choice ?l ?r => 
      refine '(RWS_of_expr_choice $l $r _ _  _ _)
    | rw_none => 
      refine '(RWS_of_expr_none)
    | rw_base ?e => 
      let (lhs, rhs, lem, match_num, quotient_num) := solve_RWS_of_expr_aux_base e in 
      refine '(RWS_of_expr_base_change $lem _ _);
      apply (RWS_of_expr_base_lemma $lhs $rhs $lem $match_num $quotient_num)
    end
  end. *)


Ltac2 rec solve_RWS_of_expr' () : unit :=
  let step := 
    lazy_match! goal with
    | [|- @RWS_of_expr ?e ?_struct ?_t' ?_hgraph ?_eqt' ?_countt' ?r
      ?_ms ?_qs ?_idx ?_state ?_err ?_rws] =>
      lazy_match! e with
      | rw_seq ?l ?r =>
        refine '(RWS_of_expr_seq $l $r _ _  _ _)
      | rw_try ?e =>
        refine '(RWS_of_expr_try $e _  _)
      | rw_repeat_k ?k ?e =>
        refine '(RWS_of_expr_repeat_k $k $e _  _)
      | rw_repeat_upto_k ?k ?e =>
        refine '(RWS_of_expr_repeat_upto_k $k $e _  _)
      | rw_repeat_star ?e =>
        refine '(RWS_of_expr_repeat_star $e _  _)
      | rw_with_par ?l ?r =>
        refine '(RWS_of_expr_with_par $l $r _ _  _ _)
      | rw_par_star ?e =>
        refine '(RWS_of_expr_par_star $e _  _)
      | rw_choice ?l ?r => 
        refine '(RWS_of_expr_choice $l $r _ _  _ _)
      | rw_none => 
        refine '(RWS_of_expr_none)
      | rw_base ?b ?e => 
        let (lhs, rhs, lem, match_num, quotient_num) := solve_RWS_of_expr_aux_base e in 
        let (struct, lawpro) := lazy_match! r with
          | context [(LawfulProLike_LawfulPRORewritingRelation _ _ ?struct _ _ ?lawpro)] => 
            (struct, lawpro)
          end in 
        (* refine '(RWS_of_expr_base_change $lem _ _ _); *)
        (* match! r with *)
        
        let hfree := Fresh.fresh (Fresh.Free.of_goal()) ident:(Hfree) in 
        ltac1:(Struct Hfree |- epose (ltac:(typeclasses eauto) : FreeStructGraphable Struct) as Hfree) 
        (Ltac1.of_constr struct) (Ltac1.of_ident hfree);
        let go l2r := 
          lazy_match! l2r with
          | true => 
              apply (RWS_of_expr_base_lemma_l2r (FreeGraphS:=&Hfree) (LawPro := $lawpro) 
                $lhs $rhs $lem $match_num $quotient_num)
          | false => 
              apply (RWS_of_expr_base_lemma_r2l (FreeGraphS:=&Hfree) (LawPro := $lawpro) 
                $lhs $rhs $lem $match_num $quotient_num)
          end in
        first [go b | let b' := Std.eval_vm None b in go b']
        (* apply (let lp := $lawpro in 
          RWS_of_expr_base_lemma (LawPro := lp) 
          (rw_base $e) $lhs $rhs $lem $match_num $quotient_num) *)
      end
    end in 
  repeat (
  lazy_match! goal with
  | [|- @RWS_of_expr ?e ?_struct ?_t' ?_hgraph ?_eqt' ?_countt' ?_r
      ?_ms ?_qs ?_idx ?_state ?_err ?rws] => 
      first [step | 
      let e' := Std.eval_cbn {
          Std.rStrength := Std.Norm;
          Std.rBeta := true;
          Std.rMatch := true;
          Std.rFix := true;
          Std.rCofix := false;
          Std.rZeta := false;
          Std.rDelta := false;
          Std.rConst := [get_ref_flip_rw_expr()]
          } e in 
      if Constr.equal e e' then 
        Control.zero No_value
      else
      change (RWS_of_expr $e' $rws);
      step]
  end).

End quote_RWS.

#[export] Hint Extern 0 (RWS_of_expr _ _) =>
  ltac2:(quote_RWS.solve_RWS_of_expr'()) : typeclass_instances.







Lemma LawfulProLike_PRO_frobenius_quote_multi_rewrite_correct `{Countable T'}
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    StructFrob : !SubStruct Frobenial Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T'}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_FPROP')
  (MatchSelector := PRO_gen_rewrite_match_selector)
  (QuotientSelector := PRO_gen_rewrite_quotient_selector)
  (Err := ProRWErr)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err := fun i j lhs n m =>
    select_frobenius_context_selector lhs)
  (f : T' -> T)
  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (RW n m))
  (e : rw_expr)
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)
  (HRWS : RWS_of_expr e RWS)

  {n m} (dtgt : D n m) :
  forall tgt : PRO Struct T n m,
  DiagramQuote dtgt tgt ->
  (* pro_rewriting_domain R tgt -> *)
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_graph_multi_rewrite RW graph_to_term
    select_context f RWS Qtgt = inl Qres ->
  forall res, PRO_unquote f Qres res ->
  (* R.(pro_rewriting_domain) res -> *)
  (* Extraneous, but necessary in the abstract case here: *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qtgt) -> *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qres) -> *)
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  apply LawfulProLike_PRO_frobenius_quote_multi_rewrite_correct_aux;
    typeclasses eauto.
Qed.



Lemma LawfulProLike_PRO_autonomous_quote_multi_rewrite_correct `{Countable T'}
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
  (RW : LawfulPRORewritingRelation Struct T :=
    LawfulProLike_LawfulPRORewritingRelation R A Struct T D LawPro)

  {StructGProp : forall T (EqT : Equiv T) (EquivT : Equivalence (≡@{T})) n m,
    Proper ((≡@{Struct n m}) ==> cohg_syntactic_eq) (graph_of_struct (T:=T))}
  `{StructMono : !SubStruct Monoidal Struct,
    StructSymm : !SubStruct Symmetry Struct,
    StructAuto : !SubStruct Autonomy Struct,
    SubStructG : !SubStructGraphable Autonomy Struct T'}
  `{StructClean : CleanableStruct Struct,
    StructComp : ComposableStruct Struct}
  (graph_to_term : forall n m, CospanHyperGraph T' n m -> option (PRO Struct T' n m)
    := fun n m => graph_to_APROP')
  (MatchSelector := PRO_gen_rewrite_match_selector)
  (QuotientSelector := PRO_gen_rewrite_quotient_selector)
  (Err := ProRWErr)
  (select_context : forall i j (lhs : CospanHyperGraph T' i j)
    n m (tgt : CospanHyperGraph T' n m), MatchSelector -> QuotientSelector ->
    CospanHyperGraph T' n ((i + j) + m) + Err := fun i j lhs n m =>
    select_bimonog_context_selector lhs)
  (f : T' -> T)
  (R' : forall n m, relation (PRO Struct T' n m) := fun n m =>
    rel_preimage (PRO_denote f) (RW n m))
  (e : rw_expr)
  {Idx State}
  (RWS : PRO_graph_rewriter R' MatchSelector QuotientSelector Idx State Err)
  (HRWS : RWS_of_expr e RWS)

  {n m} (dtgt : D n m) :
  forall tgt : PRO Struct T n m,
  DiagramQuote dtgt tgt ->
  (* pro_rewriting_domain R tgt -> *)
  forall Qtgt,
  PRO_quote f Qtgt tgt ->
  forall Qres, PRO_gen_quote_graph_multi_rewrite RW graph_to_term
    select_context f RWS Qtgt = inl Qres ->
  forall res, PRO_unquote f Qres res ->
  (* R.(pro_rewriting_domain) res -> *)
  (* Extraneous, but necessary in the abstract case here: *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qtgt) -> *)
  (* R.(pro_rewriting_domain) (PRO_denote f Qres) -> *)
  forall dres, DiagramDenote dres res ->
  dtgt ≡ dres.
Proof.
  apply LawfulProLike_PRO_autonomous_quote_multi_rewrite_correct_aux;
    typeclasses eauto.
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