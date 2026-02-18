Require Export SPTensorGraphHom AbstractTensorQuote SPIsomorphismTesting.

(* TODO: Quote from CospanSPHyperGraph T to
  CospanSPHyperGraph positive, via CospanSPHyperGraph (option T).
  Prove can test for isomorphism in quoted. *)

(* FIXME: Move *)
Lemma spgraph_of_tensor_cosphg_eq `{Equiv T} (t t' : T) n m : t ≡ t' ->
  cosphg_eq (spgraph_of_tensor t n m) (spgraph_of_tensor t' n m).
Proof.
  intros Ht.
  apply mk_cosphg_eq; [done..|].
  cbn.
  split; [|done].
  rewrite 2 sphyperedges_singleton.
  rewrite <- insert_empty.
  apply insert_proper; [|apply map_empty_equiv_eq; done].
  split;[|done].
  apply Ht.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_spgraphs_aux T n m o)
  with signature cosphg_eq ==> cosphg_eq ==> cosphg_eq
  as compose_spgraphs_aux_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' (Hin1 & Hout1 & He1)
    cosphg2 cosphg2' (Hin2 & Hout2 & He2).
  unfold compose_spgraphs_aux.
  rewrite <- Hin1, <- Hout1, <- Hin2, <- Hout2.
  apply relabel_spgraph_cosphg_eq_Proper.
  apply mk_cosphg_eq; [done..|].
  cbn.
  f_equiv.
  now apply sphypergraph_union_proper.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_spgraphs T n m o)
  with signature cosphg_eq ==> cosphg_eq ==> cosphg_eq
  as compose_spgraphs_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' Heq1
    cosphg2 cosphg2' Heq2.
  rewrite 2 compose_spgraphs_to_compose_spgraphs_aux.
  now f_equiv; apply reindex_spgraph_cosphg_eq_Proper, 
    relabel_spgraph_cosphg_eq_Proper.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_spgraphs_unsafe T n m o)
  with signature cosphg_eq ==> cosphg_eq ==> cosphg_eq
  as compose_spgraphs_unsafe_cosphg_eq.
Proof.
  intros cosphg1 cosphg1' (Hin1 & Hout1 & He1)
    cosphg2 cosphg2' (Hin2 & Hout2 & He2).
  unfold compose_spgraphs_unsafe.
  rewrite <- Hin1, <- Hin2, <- Hout2.
  apply mk_cosphg_eq; [done..|].
  cbn.
  f_equiv.
  now apply sphypergraph_union_proper.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@spreferrenced_vertices T n m)
  with signature cosphg_eq ==> eq as spreferrenced_vertices_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & [Heq Hverts]).
  unfold spreferrenced_vertices.
  rewrite <- Hins, Houts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@spisolated_vertices T n m)
  with signature cosphg_eq ==> eq as spisolated_vertices_cosphg_eq.
Proof.
  intros cosphg cosphg' Heq.
  unfold spisolated_vertices.
  f_equal; [|now rewrite Heq].
  apply Heq.2.2.2.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@set_spverts T n m)
  with signature cosphg_eq ==> eq ==> cosphg_eq as set_spverts_cosphg_eq.
Proof.
  intros cosphg cosphg' (Hins & Houts & [Heq Hverts]) vs.
  apply mk_cosphg_eq; [done..|].
  split; [done|].
  done.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@norm_spverts T n m)
  with signature cosphg_eq ==> cosphg_eq as norm_spverts_cosphg_eq.
Proof.
  intros cosphg cosphg' Heq.
  unfold norm_spverts.
  now apply set_spverts_cosphg_eq, spisolated_vertices_cosphg_eq_Proper.
Qed.








Class CospanSPHyperGraphQuote {Ctx T} `{Equiv T'} (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr : CospanSPHyperGraph T n m) (val : CospanSPHyperGraph T' n m) := {
  cosphg_quote : cosphg_eq (spgraph_apply_hom (f ctx) expr) val;
}.

#[global] Hint Mode CospanSPHyperGraphQuote + + + - + - + + - + : typeclass_instances.


Lemma cosphg_quote_correct_equiv {Ctx} `{Equiv T, Equivalence T equiv,
  Equiv T', Equivalence T' equiv}
  (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr expr' : CospanSPHyperGraph T n m)
    (val val' : CospanSPHyperGraph T' n m)
    {Hval : CospanSPHyperGraphQuote f ctx expr val}
    {Hval' : CospanSPHyperGraphQuote f ctx expr' val'}
    {Hf : Proper (equiv ==> equiv) (f ctx)} :
  expr ≡ expr' -> val ≡ val'.
Proof.
  intros Heq.
  destruct Hval as [Hval].
  destruct Hval' as [Hval'].
  rewrite <- Hval.
  etransitivity; [|apply cosphg_eq_subrelation, Hval'].
  refine (spgraph_apply_hom_proper_Proper _ _ _ _ _).
  done.
Qed.


Section instances.

#[local] Set Typeclasses Unique Instances.

Context {Ctx T} `{Equiv T'} `{Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx).

Local Notation Quote := (@CospanSPHyperGraphQuote Ctx T T' _ f ctx _ _).

#[export] Instance cosphg_quote_spgraph_apply_hom {n m} (expr : CospanSPHyperGraph T n m) :
  Quote expr (spgraph_apply_hom (f ctx) expr).
Proof.
  now constructor.
Qed.

#[export] Instance cosphg_quote_id_spgraph {n} : Quote (id_spgraph n) (id_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_quote_cup_spgraph {n} : Quote (cup_spgraph n) (cup_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_quote_cap_spgraph {n} : Quote (cap_spgraph n) (cap_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_quote_swap_spgraph {n m} : Quote (swap_spgraph n m) (swap_spgraph n m).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_quote_spgraph_of_tensor {n m} t t' :
  AbstractTensorQuote f ctx t t' ->
  Quote (spgraph_of_tensor t n m) (spgraph_of_tensor t' n m).
Proof.
  intros [Ht].
  constructor.
  rewrite spgraph_apply_hom_spgraph_of_tensor.
  now apply spgraph_of_tensor_cosphg_eq.
Qed.

Lemma quote_of_unary_mor {n m n' m'}
  (g : forall T'', CospanSPHyperGraph T'' n m -> CospanSPHyperGraph T'' n' m')
  (Hg : Proper (cosphg_eq ==> cosphg_eq) (g T'))
  (Hghom : forall cosphg, spgraph_apply_hom (f ctx) (g T cosphg) =
      g T' (spgraph_apply_hom (f ctx) cosphg)) :
  forall expr val, Quote expr val -> Quote (g T expr) (g T' val).
Proof.
  intros expr val [Hval].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

Lemma quote_of_binary_mor {n m n' m' n'' m''}
  (g : forall T'', CospanSPHyperGraph T'' n m -> CospanSPHyperGraph T'' n' m' ->
    CospanSPHyperGraph T'' n'' m'')
  (Hg : Proper (cosphg_eq ==> cosphg_eq ==> cosphg_eq) (g T'))
  (Hghom : forall cosphg cosphg', spgraph_apply_hom (f ctx) (g T cosphg cosphg') =
      g T' (spgraph_apply_hom (f ctx) cosphg) (spgraph_apply_hom (f ctx) cosphg')) :
  forall expr expr' val val', Quote expr val -> Quote expr' val' ->
    Quote (g T expr expr') (g T' val val').
Proof.
  intros expr expr' val val' [Hval] [Hval'].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

#[export] Instance cosphg_quote_relabel_spgraph {n m}
  g (expr : CospanSPHyperGraph T n m) val :
  Quote expr val ->
  Quote (relabel_spgraph g expr)
    (relabel_spgraph g val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_relabel_spgraph.
Qed.

#[export] Instance cosphg_quote_reindex_spgraph {n m}
  g (expr : CospanSPHyperGraph T n m) val :
  Quote expr val ->
  Quote (reindex_spgraph g expr)
    (reindex_spgraph g val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_reindex_spgraph.
Qed.

#[export] Instance cosphg_quote_swapped_stack_spgraphs_aux {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (swapped_stack_spgraphs_aux expr expr')
    (swapped_stack_spgraphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_swapped_stack_spgraphs_aux.
Qed.

#[export] Instance cosphg_quote_swapped_stack_spgraphs {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (swapped_stack_spgraphs expr expr')
    (swapped_stack_spgraphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_swapped_stack_spgraphs.
Qed.

#[export] Instance cosphg_quote_stack_spgraphs_aux {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (stack_spgraphs_aux expr expr')
    (stack_spgraphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_stack_spgraphs_aux.
Qed.

#[export] Instance cosphg_quote_stack_spgraphs {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (stack_spgraphs expr expr')
    (stack_spgraphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_stack_spgraphs.
Qed.

#[export] Instance cosphg_quote_spadd_top_loop {n m}
  (expr : CospanSPHyperGraph T (S n) (S m)) val :
  Quote expr val ->
  Quote (spadd_top_loop expr)
    (spadd_top_loop val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_spadd_top_loop.
Qed.

#[export] Instance cosphg_quote_spadd_top_loops {n m o}
  (expr : CospanSPHyperGraph T (n + m) (n + o)) val :
  Quote expr val ->
  Quote (spadd_top_loops expr)
    (spadd_top_loops val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_spadd_top_loops.
Qed.

#[export] Instance cosphg_quote_compose_spgraphs_aux {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_spgraphs_aux expr expr')
    (compose_spgraphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs_aux.
Qed.

#[export] Instance cosphg_quote_compose_spgraphs {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_spgraphs expr expr')
    (compose_spgraphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs.
Qed.

#[export] Instance cosphg_quote_compose_spgraphs_unsafe {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_spgraphs_unsafe expr expr')
    (compose_spgraphs_unsafe val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs_unsafe.
Qed.

#[export] Instance cosphg_quote_norm_spverts {n m}
  (expr : CospanSPHyperGraph T n m) val :
  Quote expr val ->
  Quote (norm_spverts expr)
    (norm_spverts val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_norm_spverts.
Qed.

End instances.




Class CospanSPHyperGraphDenote {Ctx T} `{Equiv T'} (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr : CospanSPHyperGraph T n m) (val : CospanSPHyperGraph T' n m) := {
  cosphg_denote : cosphg_eq (spgraph_apply_hom (f ctx) expr) val;
}.

#[global] Hint Mode CospanSPHyperGraphDenote + + + - + - + + + - : typeclass_instances.

Class AbstractTensorDenote {Ctx T} `{Equiv T'} (f : Ctx -> T -> T') (ctx : Ctx)
  (t : T) (t' : T') := {
  abs_denote : f ctx t ≡ t'
}.

#[global] Hint Mode AbstractTensorDenote + + + - + + + - : typeclass_instances.

#[export] Instance abstens_denote_default {Ctx T} `{Equiv T', Reflexive T' equiv}
  (f : Ctx -> T -> T') (ctx : Ctx) (t : T) :
  AbstractTensorDenote f ctx t (f ctx t) | 100.
Proof.
  constructor.
  reflexivity.
Qed.


Lemma cosphg_denote_correct_equiv {Ctx} `{Equiv T, Equivalence T equiv,
  Equiv T', Equivalence T' equiv}
  (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr expr' : CospanSPHyperGraph T n m)
    (val val' : CospanSPHyperGraph T' n m)
    {Hval : CospanSPHyperGraphDenote f ctx expr val}
    {Hval' : CospanSPHyperGraphDenote f ctx expr' val'}
    {Hf : Proper (equiv ==> equiv) (f ctx)} :
  expr ≡ expr' -> val ≡ val'.
Proof.
  intros Heq.
  destruct Hval as [Hval].
  destruct Hval' as [Hval'].
  rewrite <- Hval.
  etransitivity; [|apply cosphg_eq_subrelation, Hval'].
  refine (spgraph_apply_hom_proper_Proper _ _ _ _ _).
  done.
Qed.

Section instances.

#[local] Set Typeclasses Unique Instances.

Context {Ctx T} `{Equiv T'} `{Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx).

Local Notation Denote := (@CospanSPHyperGraphDenote Ctx T T' _ f ctx _ _).

#[export] Instance cosphg_denote_id_spgraph {n} : Denote (id_spgraph n) (id_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_denote_cup_spgraph {n} : Denote (cup_spgraph n) (cup_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_denote_cap_spgraph {n} : Denote (cap_spgraph n) (cap_spgraph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_denote_swap_spgraph {n m} : Denote (swap_spgraph n m) (swap_spgraph n m).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cosphg_denote_spgraph_of_tensor {n m} t t' :
  AbstractTensorDenote f ctx t t' ->
  Denote (spgraph_of_tensor t n m) (spgraph_of_tensor t' n m).
Proof.
  intros [Ht].
  constructor.
  rewrite spgraph_apply_hom_spgraph_of_tensor.
  now apply spgraph_of_tensor_cosphg_eq.
Qed.

Lemma denote_of_unary_mor {n m n' m'}
  (g : forall T'', CospanSPHyperGraph T'' n m -> CospanSPHyperGraph T'' n' m')
  (Hg : Proper (cosphg_eq ==> cosphg_eq) (g T'))
  (Hghom : forall cosphg, spgraph_apply_hom (f ctx) (g T cosphg) =
      g T' (spgraph_apply_hom (f ctx) cosphg)) :
  forall expr val, Denote expr val -> Denote (g T expr) (g T' val).
Proof.
  intros expr val [Hval].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

Lemma denote_of_binary_mor {n m n' m' n'' m''}
  (g : forall T'', CospanSPHyperGraph T'' n m -> CospanSPHyperGraph T'' n' m' ->
    CospanSPHyperGraph T'' n'' m'')
  (Hg : Proper (cosphg_eq ==> cosphg_eq ==> cosphg_eq) (g T'))
  (Hghom : forall cosphg cosphg', spgraph_apply_hom (f ctx) (g T cosphg cosphg') =
      g T' (spgraph_apply_hom (f ctx) cosphg) (spgraph_apply_hom (f ctx) cosphg')) :
  forall expr expr' val val', Denote expr val -> Denote expr' val' ->
    Denote (g T expr expr') (g T' val val').
Proof.
  intros expr expr' val val' [Hval] [Hval'].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

#[export] Instance cosphg_denote_relabel_spgraph {n m}
  g (expr : CospanSPHyperGraph T n m) val :
  Denote expr val ->
  Denote (relabel_spgraph g expr)
    (relabel_spgraph g val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_relabel_spgraph.
Qed.

#[export] Instance cosphg_denote_reindex_spgraph {n m}
  g (expr : CospanSPHyperGraph T n m) val :
  Denote expr val ->
  Denote (reindex_spgraph g expr)
    (reindex_spgraph g val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_reindex_spgraph.
Qed.

#[export] Instance cosphg_denote_swapped_stack_spgraphs_aux {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (swapped_stack_spgraphs_aux expr expr')
    (swapped_stack_spgraphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_swapped_stack_spgraphs_aux.
Qed.

#[export] Instance cosphg_denote_swapped_stack_spgraphs {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (swapped_stack_spgraphs expr expr')
    (swapped_stack_spgraphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_swapped_stack_spgraphs.
Qed.

#[export] Instance cosphg_denote_stack_spgraphs_aux {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (stack_spgraphs_aux expr expr')
    (stack_spgraphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_stack_spgraphs_aux.
Qed.

#[export] Instance cosphg_denote_stack_spgraphs {n m n' m'}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (stack_spgraphs expr expr')
    (stack_spgraphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_stack_spgraphs.
Qed.

#[export] Instance cosphg_denote_spadd_top_loop {n m}
  (expr : CospanSPHyperGraph T (S n) (S m)) val :
  Denote expr val ->
  Denote (spadd_top_loop expr)
    (spadd_top_loop val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_spadd_top_loop.
Qed.

#[export] Instance cosphg_denote_spadd_top_loops {n m o}
  (expr : CospanSPHyperGraph T (n + m) (n + o)) val :
  Denote expr val ->
  Denote (spadd_top_loops expr)
    (spadd_top_loops val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_spadd_top_loops.
Qed.

#[export] Instance cosphg_denote_compose_spgraphs_aux {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_spgraphs_aux expr expr')
    (compose_spgraphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs_aux.
Qed.

#[export] Instance cosphg_denote_compose_spgraphs {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_spgraphs expr expr')
    (compose_spgraphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs.
Qed.

#[export] Instance cosphg_denote_compose_spgraphs_unsafe {n m o}
  (expr : CospanSPHyperGraph T n m) (expr' : CospanSPHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_spgraphs_unsafe expr expr')
    (compose_spgraphs_unsafe val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_compose_spgraphs_unsafe.
Qed.

#[export] Instance cosphg_denote_norm_spverts {n m}
  (expr : CospanSPHyperGraph T n m) val :
  Denote expr val ->
  Denote (norm_spverts expr)
    (norm_spverts val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply spgraph_apply_hom_norm_spverts.
Qed.

End instances.






#[local] Program Instance opttensor_TensorLike
  `{TensorLike R rO rI radd rmul req A T} : TensorLike R A (option T) := {
  interpretTensor mt := from_option interpretTensor (fun _ _ => const_tensor rO) mt;
}.
Next Obligation.
  intros *.
  intros mt mt' Hmt.
  induction Hmt as [mt mt' Hmt|]; [|done].
  cbn.
  now apply interpretTensorProper.
Qed.

#[export] Instance Some_TensorProper `{Equiv T} :
  Proper (equiv ==> equiv) (@Some T) :=
  Some_proper.

#[export] Instance Some_TensorLikeHom `{TensorLike R rO rI radd rmul req A T} :
  TensorLikeHom R A (@Some T).
Proof.
  split.
  reflexivity.
Qed.



Lemma spgraph_to_option_correct_equiv `{Equiv T, Equivalence T equiv}
  {n m} (expr expr' : CospanSPHyperGraph T n m) val val' :
  CospanSPHyperGraphDenote (fun _ => Some) tt expr val ->
  CospanSPHyperGraphDenote (fun _ => Some) tt expr' val' ->
  val ≡ val' ->
  expr ≡ expr'.
Proof.
  intros [Hval] [Hval'] Heq.
  rewrite <- Hval, <- Hval' in Heq.
  now apply (spgraph_apply_hom_equiv_inv Some).
Qed.



Local Existing Instance positive_equiv.


Lemma spgraph_equiv_of_positive `{Equiv T, Equivalence T equiv}
  (ctx : list T) {n m} (expr expr' : CospanSPHyperGraph positive n m) 
  val val' oval oval' :
  CospanSPHyperGraphDenote (λ _, Some) tt val oval ->
  CospanSPHyperGraphDenote (λ _, Some) tt val' oval' ->
  CospanSPHyperGraphQuote interp_discrete_hg ctx expr oval ->
  CospanSPHyperGraphQuote interp_discrete_hg ctx expr' oval' ->
  expr ≡ expr' ->
  val ≡ val'.
Proof.
  intros Hoval Hoval' Hval Hval'.
  intros Heq.
  apply (cosphg_quote_correct_equiv interp_discrete_hg ctx _ _ oval oval') in Heq.
  revert Heq.
  apply spgraph_to_option_correct_equiv; apply _.
Qed.

Lemma spgraph_test_isomorphism_quote `{Equiv T, Equivalence T equiv}
  (ctx : list T) {n m} (expr expr' : CospanSPHyperGraph positive n m) val val' oval oval' :
  CospanSPHyperGraphDenote (λ _, Some) tt val oval ->
  CospanSPHyperGraphDenote (λ _, Some) tt val' oval' ->
  CospanSPHyperGraphQuote interp_discrete_hg ctx expr oval ->
  CospanSPHyperGraphQuote interp_discrete_hg ctx expr' oval' ->
  spgraph_iso_partial_test expr expr' = true ->
  norm_spverts val ≡ norm_spverts val'.
Proof.
  intros Hoval Hoval' Hval Hval' Heq%spgraph_iso_partial_test_correct.
  revert Heq.
  apply spgraph_equiv_of_positive with ctx (norm_spverts oval) (norm_spverts oval');
    apply _.
Qed.




