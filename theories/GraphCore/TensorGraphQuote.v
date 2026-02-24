Require Export TensorGraphHom.
Require Export AbstractTensorQuote.

(* TODO: Quote from CospanHyperGraph T to
  CospanHyperGraph positive, via CospanHyperGraph (option T).
  Prove can test for isomorphism in quoted. *)

(* FIXME: Move *)
Lemma graph_of_tensor_cohg_eq `{Equiv T} (t t' : T) n m : t ≡ t' ->
  cohg_eq (graph_of_tensor t n m) (graph_of_tensor t' n m).
Proof.
  intros Ht.
  apply mk_cohg_eq; [done..|].
  cbn.
  split; [|done].
  rewrite 2 hyperedges_singleton.
  rewrite <- insert_empty.
  apply insert_proper; [|apply map_empty_equiv_eq; done].
  split; [split;[|done]|done].
  apply Ht.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs_aux T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_aux_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hin1 & Hout1 & He1)
    cohg2 cohg2' (Hin2 & Hout2 & He2).
  unfold compose_graphs_aux.
  rewrite <- Hin1, <- Hout1, <- Hin2, <- Hout2.
  f_equiv.
  apply mk_cohg_eq; [done..|].
  cbn.
  now do 2 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_cohg_eq.
Proof.
  intros cohg1 cohg1' Heq1
    cohg2 cohg2' Heq2.
  rewrite 2 compose_graphs_to_compose_graphs_aux.
  now do 3 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T, Equivalence T equiv}
  {n m o} : (@compose_graphs_unsafe T n m o)
  with signature cohg_eq ==> cohg_eq ==> cohg_eq
  as compose_graphs_unsafe_cohg_eq.
Proof.
  intros cohg1 cohg1' (Hin1 & Hout1 & He1)
    cohg2 cohg2' (Hin2 & Hout2 & He2).
  unfold compose_graphs_unsafe.
  rewrite <- Hin1, <- Hin2, <- Hout2.
  apply mk_cohg_eq; [done..|].
  cbn.
  now do 2 f_equiv.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@referrenced_vertices T n m)
  with signature cohg_eq ==> eq as referrenced_vertices_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & [Heq Hverts]).
  unfold referrenced_vertices.
  rewrite <- Hins, Houts.
  f_equal.
  apply map_to_list_equiv in Heq.
  induction Heq as [|? ? ? ? Hhd]; [done|].
  cbn.
  rewrite 2 (list_to_set_app_L (_++_)).
  f_equal; [|done].
  do 2 f_equal; apply Hhd.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@isolated_vertices T n m)
  with signature cohg_eq ==> eq as isolated_vertices_cohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold isolated_vertices.
  f_equal; [|now rewrite Heq].
  apply Heq.2.2.2.
Qed.

Add Parametric Morphism `{Equiv T} {n m} : (@set_verts T n m)
  with signature cohg_eq ==> eq ==> cohg_eq as set_verts_cohg_eq.
Proof.
  intros cohg cohg' (Hins & Houts & [Heq Hverts]) vs.
  apply mk_cohg_eq; [done..|].
  split; [done|].
  done.
Qed.


Add Parametric Morphism `{Equiv T} {n m} : (@norm_verts T n m)
  with signature cohg_eq ==> cohg_eq as norm_verts_cohg_eq.
Proof.
  intros cohg cohg' Heq.
  unfold norm_verts.
  now apply set_verts_cohg_eq, isolated_vertices_cohg_eq_Proper.
Qed.








Class CospanHyperGraphQuote {Ctx T} `{Equiv T', Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr : CospanHyperGraph T n m) (val : CospanHyperGraph T' n m) := {
  cohg_quote : cohg_eq (graph_apply_hom (f ctx) expr) val;
}.

#[global] Hint Mode CospanHyperGraphQuote + + + - - + - + + - + : typeclass_instances.


Lemma cohg_quote_correct_equiv {Ctx} `{Equiv T, Equivalence T equiv,
  Equiv T', Equivalence T' equiv}
  (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr expr' : CospanHyperGraph T n m)
    (val val' : CospanHyperGraph T' n m)
    {Hval : CospanHyperGraphQuote f ctx expr val}
    {Hval' : CospanHyperGraphQuote f ctx expr' val'}
    {Hf : Proper (equiv ==> equiv) (f ctx)} :
  expr ≡ expr' -> val ≡ val'.
Proof.
  intros Heq.
  destruct Hval as [Hval].
  destruct Hval' as [Hval'].
  rewrite <- Hval.
  etransitivity; [|apply cohg_eq_subrelation, Hval'].
  refine (graph_apply_hom_proper_Proper _ _ _ _ _).
  done.
Qed.


Section instances.

#[local] Set Typeclasses Unique Instances.

Context {Ctx T} `{Equiv T'} `{Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx).

Local Notation Quote := (@CospanHyperGraphQuote Ctx T T' _ _ f ctx _ _).

#[export] Instance cohg_quote_graph_apply_hom {n m} (expr : CospanHyperGraph T n m) :
  Quote expr (graph_apply_hom (f ctx) expr).
Proof.
  now constructor.
Qed.

#[export] Instance cohg_quote_id_graph {n} : Quote (id_graph n) (id_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_quote_cup_graph {n} : Quote (cup_graph n) (cup_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_quote_cap_graph {n} : Quote (cap_graph n) (cap_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_quote_swap_graph {n m} : Quote (swap_graph n m) (swap_graph n m).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_quote_graph_of_tensor {n m} t t' :
  AbstractTensorQuote f ctx t t' ->
  Quote (graph_of_tensor t n m) (graph_of_tensor t' n m).
Proof.
  intros [Ht].
  constructor.
  rewrite graph_apply_hom_graph_of_tensor.
  now apply graph_of_tensor_cohg_eq.
Qed.

Lemma quote_of_unary_mor {n m n' m'}
  (g : forall T'', CospanHyperGraph T'' n m -> CospanHyperGraph T'' n' m')
  (Hg : Proper (cohg_eq ==> cohg_eq) (g T'))
  (Hghom : forall cohg, graph_apply_hom (f ctx) (g T cohg) =
      g T' (graph_apply_hom (f ctx) cohg)) :
  forall expr val, Quote expr val -> Quote (g T expr) (g T' val).
Proof.
  intros expr val [Hval].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

Lemma quote_of_binary_mor {n m n' m' n'' m''}
  (g : forall T'', CospanHyperGraph T'' n m -> CospanHyperGraph T'' n' m' ->
    CospanHyperGraph T'' n'' m'')
  (Hg : Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (g T'))
  (Hghom : forall cohg cohg', graph_apply_hom (f ctx) (g T cohg cohg') =
      g T' (graph_apply_hom (f ctx) cohg) (graph_apply_hom (f ctx) cohg')) :
  forall expr expr' val val', Quote expr val -> Quote expr' val' ->
    Quote (g T expr expr') (g T' val val').
Proof.
  intros expr expr' val val' [Hval] [Hval'].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

#[export] Instance cohg_quote_relabel_graph {n m}
  g (expr : CospanHyperGraph T n m) val :
  Quote expr val ->
  Quote (relabel_graph g expr)
    (relabel_graph g val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_relabel_graph.
Qed.

#[export] Instance cohg_quote_reindex_graph {n m}
  g (expr : CospanHyperGraph T n m) val :
  Quote expr val ->
  Quote (reindex_graph g expr)
    (reindex_graph g val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_reindex_graph.
Qed.

#[export] Instance cohg_quote_swapped_stack_graphs_aux {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (swapped_stack_graphs_aux expr expr')
    (swapped_stack_graphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_swapped_stack_graphs_aux.
Qed.

#[export] Instance cohg_quote_swapped_stack_graphs {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (swapped_stack_graphs expr expr')
    (swapped_stack_graphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_swapped_stack_graphs.
Qed.

#[export] Instance cohg_quote_stack_graphs_aux {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (stack_graphs_aux expr expr')
    (stack_graphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_stack_graphs_aux.
Qed.

#[export] Instance cohg_quote_stack_graphs {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (stack_graphs expr expr')
    (stack_graphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_stack_graphs.
Qed.

#[export] Instance cohg_quote_add_top_loop {n m}
  (expr : CospanHyperGraph T (S n) (S m)) val :
  Quote expr val ->
  Quote (add_top_loop expr)
    (add_top_loop val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_add_top_loop.
Qed.

#[export] Instance cohg_quote_add_top_loops {n m o}
  (expr : CospanHyperGraph T (n + m) (n + o)) val :
  Quote expr val ->
  Quote (add_top_loops expr)
    (add_top_loops val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_add_top_loops.
Qed.

#[export] Instance cohg_quote_compose_graphs_aux {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_graphs_aux expr expr')
    (compose_graphs_aux val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs_aux.
Qed.

#[export] Instance cohg_quote_compose_graphs {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_graphs expr expr')
    (compose_graphs val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs.
Qed.

#[export] Instance cohg_quote_compose_graphs_unsafe {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Quote expr val -> Quote expr' val' ->
  Quote (compose_graphs_unsafe expr expr')
    (compose_graphs_unsafe val val').
Proof.
  apply (quote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs_unsafe.
Qed.

#[export] Instance cohg_quote_norm_verts {n m}
  (expr : CospanHyperGraph T n m) val :
  Quote expr val ->
  Quote (norm_verts expr)
    (norm_verts val).
Proof.
  apply (quote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_norm_verts.
Qed.

End instances.




Class CospanHyperGraphDenote {Ctx T} `{Equiv T', Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr : CospanHyperGraph T n m) (val : CospanHyperGraph T' n m) := {
  cohg_denote : cohg_eq (graph_apply_hom (f ctx) expr) val;
}.

#[global] Hint Mode CospanHyperGraphDenote + + + - - + - + + + - : typeclass_instances.


Lemma cohg_denote_correct_equiv {Ctx} `{Equiv T, Equivalence T equiv,
  Equiv T', Equivalence T' equiv}
  (f : Ctx -> T -> T')
  (ctx : Ctx) {n m} (expr expr' : CospanHyperGraph T n m)
    (val val' : CospanHyperGraph T' n m)
    {Hval : CospanHyperGraphDenote f ctx expr val}
    {Hval' : CospanHyperGraphDenote f ctx expr' val'}
    {Hf : Proper (equiv ==> equiv) (f ctx)} :
  expr ≡ expr' -> val ≡ val'.
Proof.
  intros Heq.
  destruct Hval as [Hval].
  destruct Hval' as [Hval'].
  rewrite <- Hval.
  etransitivity; [|apply cohg_eq_subrelation, Hval'].
  refine (graph_apply_hom_proper_Proper _ _ _ _ _).
  done.
Qed.

Section instances.

#[local] Set Typeclasses Unique Instances.

Context {Ctx T} `{Equiv T'} `{Equivalence T' equiv} (f : Ctx -> T -> T')
  (ctx : Ctx).

Local Notation Denote := (@CospanHyperGraphDenote Ctx T T' _ _ f ctx _ _).

#[export] Instance cohg_denote_id_graph {n} : Denote (id_graph n) (id_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_denote_cup_graph {n} : Denote (cup_graph n) (cup_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_denote_cap_graph {n} : Denote (cap_graph n) (cap_graph n).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_denote_swap_graph {n m} : Denote (swap_graph n m) (swap_graph n m).
Proof.
  constructor.
  done.
Qed.

#[export] Instance cohg_denote_graph_of_tensor {n m} t t' :
  AbstractTensorDenote f ctx t t' ->
  Denote (graph_of_tensor t n m) (graph_of_tensor t' n m).
Proof.
  intros [Ht].
  constructor.
  rewrite graph_apply_hom_graph_of_tensor.
  now apply graph_of_tensor_cohg_eq.
Qed.

Lemma denote_of_unary_mor {n m n' m'}
  (g : forall T'', CospanHyperGraph T'' n m -> CospanHyperGraph T'' n' m')
  (Hg : Proper (cohg_eq ==> cohg_eq) (g T'))
  (Hghom : forall cohg, graph_apply_hom (f ctx) (g T cohg) =
      g T' (graph_apply_hom (f ctx) cohg)) :
  forall expr val, Denote expr val -> Denote (g T expr) (g T' val).
Proof.
  intros expr val [Hval].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

Lemma denote_of_binary_mor {n m n' m' n'' m''}
  (g : forall T'', CospanHyperGraph T'' n m -> CospanHyperGraph T'' n' m' ->
    CospanHyperGraph T'' n'' m'')
  (Hg : Proper (cohg_eq ==> cohg_eq ==> cohg_eq) (g T'))
  (Hghom : forall cohg cohg', graph_apply_hom (f ctx) (g T cohg cohg') =
      g T' (graph_apply_hom (f ctx) cohg) (graph_apply_hom (f ctx) cohg')) :
  forall expr expr' val val', Denote expr val -> Denote expr' val' ->
    Denote (g T expr expr') (g T' val val').
Proof.
  intros expr expr' val val' [Hval] [Hval'].
  constructor.
  rewrite Hghom.
  now apply Hg.
Qed.

#[export] Instance cohg_denote_relabel_graph {n m}
  g (expr : CospanHyperGraph T n m) val :
  Denote expr val ->
  Denote (relabel_graph g expr)
    (relabel_graph g val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_relabel_graph.
Qed.

#[export] Instance cohg_denote_reindex_graph {n m}
  g (expr : CospanHyperGraph T n m) val :
  Denote expr val ->
  Denote (reindex_graph g expr)
    (reindex_graph g val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_reindex_graph.
Qed.

#[export] Instance cohg_denote_swapped_stack_graphs_aux {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (swapped_stack_graphs_aux expr expr')
    (swapped_stack_graphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_swapped_stack_graphs_aux.
Qed.

#[export] Instance cohg_denote_swapped_stack_graphs {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (swapped_stack_graphs expr expr')
    (swapped_stack_graphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_swapped_stack_graphs.
Qed.

#[export] Instance cohg_denote_stack_graphs_aux {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (stack_graphs_aux expr expr')
    (stack_graphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_stack_graphs_aux.
Qed.

#[export] Instance cohg_denote_stack_graphs {n m n' m'}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T n' m')
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (stack_graphs expr expr')
    (stack_graphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_stack_graphs.
Qed.

#[export] Instance cohg_denote_add_top_loop {n m}
  (expr : CospanHyperGraph T (S n) (S m)) val :
  Denote expr val ->
  Denote (add_top_loop expr)
    (add_top_loop val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_add_top_loop.
Qed.

#[export] Instance cohg_denote_add_top_loops {n m o}
  (expr : CospanHyperGraph T (n + m) (n + o)) val :
  Denote expr val ->
  Denote (add_top_loops expr)
    (add_top_loops val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_add_top_loops.
Qed.

#[export] Instance cohg_denote_compose_graphs_aux {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_graphs_aux expr expr')
    (compose_graphs_aux val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs_aux.
Qed.

#[export] Instance cohg_denote_compose_graphs {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_graphs expr expr')
    (compose_graphs val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs.
Qed.

#[export] Instance cohg_denote_compose_graphs_unsafe {n m o}
  (expr : CospanHyperGraph T n m) (expr' : CospanHyperGraph T m o)
  val val' :
  Denote expr val -> Denote expr' val' ->
  Denote (compose_graphs_unsafe expr expr')
    (compose_graphs_unsafe val val').
Proof.
  apply (denote_of_binary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_compose_graphs_unsafe.
Qed.

#[export] Instance cohg_denote_norm_verts {n m}
  (expr : CospanHyperGraph T n m) val :
  Denote expr val ->
  Denote (norm_verts expr)
    (norm_verts val).
Proof.
  apply (denote_of_unary_mor (fun _ => _) _).
  intros; apply graph_apply_hom_norm_verts.
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



Lemma graph_to_option_correct_equiv `{Equiv T, Equivalence T equiv}
  {n m} (expr expr' : CospanHyperGraph T n m) val val' :
  CospanHyperGraphDenote (fun _ => Some) tt expr val ->
  CospanHyperGraphDenote (fun _ => Some) tt expr' val' ->
  val ≡ val' ->
  expr ≡ expr'.
Proof.
  intros [Hval] [Hval'] Heq.
  rewrite <- Hval, <- Hval' in Heq.
  now apply (graph_apply_hom_equiv_inv Some).
Qed.





Local Existing Instance positive_equiv.


Lemma graph_equiv_of_positive `{Equiv T, Equivalence T equiv}
  (ctx : list T) {n m} (expr expr' : CospanHyperGraph positive n m) 
  val val' oval oval' :
  CospanHyperGraphDenote (λ _, Some) tt val oval ->
  CospanHyperGraphDenote (λ _, Some) tt val' oval' ->
  CospanHyperGraphQuote interp_discrete_hg ctx expr oval ->
  CospanHyperGraphQuote interp_discrete_hg ctx expr' oval' ->
  expr ≡ expr' ->
  val ≡ val'.
Proof.
  intros Hoval Hoval' Hval Hval'.
  intros Heq.
  apply (cohg_quote_correct_equiv interp_discrete_hg ctx _ _ oval oval') in Heq.
  revert Heq.
  apply graph_to_option_correct_equiv; apply _.
Qed.

Lemma graph_test_isomorphism_quote `{Equiv T, Equivalence T equiv}
  (ctx : list T) {n m} (expr expr' : CospanHyperGraph positive n m) val val' oval oval' :
  CospanHyperGraphDenote (λ _, Some) tt val oval ->
  CospanHyperGraphDenote (λ _, Some) tt val' oval' ->
  CospanHyperGraphQuote interp_discrete_hg ctx expr oval ->
  CospanHyperGraphQuote interp_discrete_hg ctx expr' oval' ->
  graph_iso_partial_test expr expr' = true ->
  norm_verts val ≡ norm_verts val'.
Proof.
  intros Hoval Hoval' Hval Hval' Heq%graph_iso_partial_test_correct.
  revert Heq.
  apply graph_equiv_of_positive with ctx (norm_verts oval) (norm_verts oval');
    apply _.
Qed.




