From TensorRocq Require Import Isomorphism.IsoAux Isomorphism.Testing CospanHyperGraph.Definitions
  CospanHyperGraph.Ops.
Require Ltac2.Ltac2.

Local Existing Instance Countable_Equiv.


(* FIXME: Move *)
Definition map_inv `{MapFold K V MKV, Empty MVK, Insert V K MVK}
  (m : MKV) : MVK :=
  list_to_map (prod_swap <$> map_to_list m).

Lemma elem_of_list_fmap_cancel_1 {A B} {f : A -> B}
  {g : B -> A} `{!Cancel eq g f} b (l : list A) :
  b ∈ f <$> l -> g b ∈ l.
Proof.
  intros Hb%(elem_of_list_fmap_1 g).
  rewrite <- list_fmap_compose, list_fmap_id' in Hb by now intros; apply cancel.
  done.
Qed.

Lemma elem_of_list_fmap_cancel_2 {A B} {f : A -> B}
  {g : B -> A} `{!Cancel eq f g} b (l : list A) :
  g b ∈ l -> b ∈ f <$> l.
Proof.
  intros Hb%(elem_of_list_fmap_1 f).
  now rewrite cancel in Hb.
Qed.

Lemma lookup_map_inv_Some_1 `{FinMap K MK, FinMap V MV}
  (m : MK V) v k :
  (map_inv m :> MV K) !! v = Some k -> m !! k = Some v.
Proof.
  intros Hkv%elem_of_list_to_map_2%elem_of_list_fmap_cancel_1%elem_of_map_to_list.
  done.
Qed.

Lemma lookup_map_inv_Some_2 `{FinMap K MK, FinMap V MV}
  (m : MK V) v k :
  (forall k', m !! k' = Some v -> k = k') ->
  m !! k = Some v ->
  (map_inv m :> MV K) !! v = Some k.
Proof.
  intros Hminj Hmkv.
  apply elem_of_list_to_map'.
  - intros k' _ Hk'%elem_of_list_fmap_cancel_1%elem_of_map_to_list.
    now apply Hminj.
  - apply elem_of_list_fmap_cancel_2.
    now apply elem_of_map_to_list.
Qed.

Lemma lookup_map_inv_Some `{FinMap K MK, FinMap V MV}
  (m : MK V) (Hm : map_inj m) v k :
  (map_inv m :> MV K) !! v = Some k <-> m !! k = Some v.
Proof.
  split; [apply lookup_map_inv_Some_1|].
  intros Hmk.
  apply lookup_map_inv_Some_2, Hmk.
  intros k'.
  revert Hmk.
  apply Hm.
Qed.

Lemma map_inv_is_inv `{FinMap K MK, FinMap V MV}
  (m : MK V) (Hm : map_inj m) : map_inverses m (map_inv m :> MV K).
Proof.
  intros k v.
  rewrite (lookup_map_inv_Some _ Hm).
  done.
Qed.

Lemma map_inj_insert `{FinMap K M} {A} (m : M A) k v :
  m !! k = None ->
  map_inj (<[k := v]> m) <-> v ∉ (map_to_list m).*2 /\ map_inj m.
Proof.
  intros Hmk.
  split.
  - intros Hins.
    split.
    + apply not_elem_of_list_fmap.
      intros [k' v'] Hkv'%elem_of_map_to_list.
      cbn.
      intros ->.
      specialize (Hins k k' v).
      tspecialize Hins by now rewrite lookup_insert.
      tspecialize Hins by now rewrite lookup_insert_ne by congruence.
      congruence.
    + intros k' k'' v' Hk' Hk''.
      apply (Hins _ _ v'); now rewrite lookup_insert_ne by congruence.
  - intros [Hv Hinj].
    intros k' k'' v'.
    rewrite 2 lookup_insert_case.
    do 2 case_decide; subst.
    + done.
    + intros [= <-] Hv'%elem_of_map_to_list%(elem_of_list_fmap_1 snd).
      done.
    + intros Hv'%elem_of_map_to_list%(elem_of_list_fmap_1 snd) [= <-].
      done.
    + apply Hinj.
Qed.


Lemma map_inj_iff_NoDup `{FinMap K M} {A} (m : M A) :
  map_inj m <-> NoDup (map_to_list m).*2.
Proof.
  split.
  - induction m as [|k v m Hmk IHm] using map_ind.
    + now rewrite map_to_list_empty; constructor.
    + rewrite map_inj_insert by done.
      rewrite map_to_list_insert by done.
      intros [Hv Hdup%IHm].
      now apply NoDup_cons.
  - intros Hm%(map_inj_list_to_map _ (NoDup_fst_map_to_list m)).
    now rewrite list_to_map_to_list in Hm.
Qed.

#[export] Instance map_inj_dec `{FinMap K M} `{EqDecision A} (m : M A) : Decision (map_inj m).
refine (cast_if (decide (NoDup (map_to_list m).*2)));
abstract (now rewrite map_inj_iff_NoDup).
Defined.

Definition mk_Piso''_def (m : Pmap positive) (Hm : bool_decide (map_inj m) = true) : Piso :=
  mk_Piso m (map_inv m) (map_inv_is_inv m ((@bool_decide_eq_true _ _).1 Hm)).

Notation mk_Piso'' m := (mk_Piso''_def (m :> Pmap positive)%positive eq_refl) (only parsing).












Import pretty.

#[export] Instance pretty_unit : Pretty unit := fun '() => "()".

#[export] Instance pretty_list `{Pretty A} : Pretty (list A) :=
  (fun v => "[" ++ String.concat "; " (pretty <$> v) ++ "]")%string.

#[export] Instance pretty_vec `{Pretty A} {n} : Pretty (vec A n) :=
  (fun v => "[#" ++ String.concat "; " (pretty <$> vec_to_list v) ++ "]")%string.

#[export] Instance pretty_Pmap `{Pretty A} : Pretty (Pmap A) :=
  (fun m =>
    let bnds := merge_sort (rel_preimage fst Pos.lt) (map_to_list m) in
    let elems := (λ '(k, v), pretty k ++ " := " ++ pretty v) <$> bnds in
    let up_to_13 := "{[ " ++ String.concat "; " (take 13 elems) ++ " ]}" in
    foldr (λ elem acc, "<[ " ++ elem ++ " ]> " ++ acc) up_to_13 (drop 13 elems))%string.

#[export] Instance pretty_Pset : Pretty Pset :=
  (fun s =>
    let elems := elements s in
    match elems with
    | [] => "∅"
    | _ =>
      let elems := merge_sort Pos.lt elems in
      "{[ " ++ String.concat "; " (pretty <$> elems) ++ " ]}"
    end)%string.

(* Compute pretty ({[1; 3; 2; 4; 3]} :> Pset)%positive. *)

#[export] Instance pretty_bool : Pretty bool :=
  fun b => if b then "true" else "false".


Fixpoint pretty_prods_aux_T (l : Tlist) : Type :=
  match l with
  | Tnil => unit
  | Tcons T Tnil => T
  | Tcons T Ts => pretty_prods_aux_T Ts * T
  end.

Fixpoint pretty_prods_aux_T_pretty (l : Tlist) : Type :=
  match l with
  | Tnil => True
  | Tcons T Tnil => Pretty T
  | Tcons T Ts => pretty_prods_aux_T_pretty Ts * Pretty T
  end.

Fixpoint pretty_prods_aux (l : Tlist) : pretty_prods_aux_T_pretty l ->
  pretty_prods_aux_T l -> string :=
  match l with
  | Tnil => fun _ => @pretty unit _
  | Tcons T Ts => match Ts as Ts return
    (pretty_prods_aux_T_pretty Ts -> pretty_prods_aux_T Ts -> string) ->
    (pretty_prods_aux_T_pretty (Tcons T Ts) -> pretty_prods_aux_T (Tcons T Ts) -> string)
    with
    | Tnil => fun _ (hT : Pretty T) (t : T) => pretty t
    | Tcons _ _ => (fun IH '(hTs, hT) '(ts, t) =>
      IH hTs ts ++ ", " ++ pretty t)
    end (pretty_prods_aux Ts)
  end%string.

Definition pretty_prods (l : Tlist) : pretty_prods_aux_T_pretty l ->
  Pretty (pretty_prods_aux_T l) :=
  (fun Hl t =>
    "(" ++ pretty_prods_aux l Hl t ++ ")")%string.

Existing Class pretty_prods_aux_T_pretty.
#[export] Hint Extern 0 (pretty_prods_aux_T_pretty _) =>
  cbn [pretty_prods_aux_T_pretty];
  repeat lazymatch goal with
    | |- _ * _ => split
    | |- _ => idtac
    end : typeclass_instances.

#[export] Instance pretty_pair `{Pretty A, Pretty B} : Pretty (A * B) | 8 :=
  pretty_prods (Tcons B $ Tcons A Tnil) _.

#[export] Instance pretty_triple `{Pretty A, Pretty B, Pretty C} :
  Pretty (A * B * C) | 7 :=
  pretty_prods (Tcons C $ Tcons B $ Tcons A Tnil) _.

#[export] Instance pretty_quadruple `{Pretty A, Pretty B, Pretty C, Pretty D} :
  Pretty (A * B * C * D) | 6 :=
  pretty_prods (Tcons D $ Tcons C $ Tcons B $ Tcons A Tnil) _.


Module pretty_prods.

Import Ltac2.Ltac2.

Ltac2 tlist_of_prods (c : constr) : constr :=
  let rec go c :=
  lazy_match! c with
  | prod ?a ?b => let r := go a in '(Tcons $b $r)
  | _ => '(Tcons $c Tnil)
  end
  in go c.

Ltac2 pretty_prods (c : constr) :=
  let tl := tlist_of_prods c in
  refine '(pretty_prods $tl _).


Ltac2 solve_pretty_prods () :=
  match! goal with
  | [|- Pretty ?c] => pretty_prods c;
    cbn;
    repeat (match! goal with
    | [|- prod _ _] => split
    end)
  end.

End pretty_prods.

#[export] Hint Extern 0 (Pretty (_ * _)) =>
  ltac2:(pretty_prods.solve_pretty_prods()) : typeclass_instances.

(* Compute pretty (1, 2, 3, 4, 5, 6, 7, 8). *)

#[export] Instance pretty_string : Pretty string :=
  fun s => String Ascii.DoubleQuote (s ++ String Ascii.DoubleQuote EmptyString).

(* FIXME: NB: This is unsafe in general, but much nicer-printing (since Rocq uses ""
  to represent a single (double) quote in strings) *)
Local Instance pretty_string_raw : Pretty string := fun s => s.

#[export] Instance pretty_option `{Pretty A} : Pretty (option A) :=
  fun ma =>
  match ma with
  | None => "None"
  | Some a => "Some (" ++ pretty a ++ ")"
  end%string.

#[export] Instance pretty_hg `{Pretty T} : Pretty (HyperGraph T) :=
  (fun hg =>
   String.concat " " ["mk_hg"; pretty hg.(hyperedges); pretty hg.(hypervertices)]).


#[export] Instance pretty_cohg `{Pretty T} {n m} : Pretty (CospanHyperGraph T n m) :=
  (fun cohg =>
  String.concat " " ["mk_cohg";
    "(" ++ pretty cohg.(hedges) ++ ")";
    pretty cohg.(inputs);
    pretty cohg.(outputs)])%string.

From TensorRocq Require Import tc.


#[export] Instance pretty_blocks : Pretty blocks :=
  fun p => pretty p.*2.

#[export] Instance pretty_Piso : Pretty Piso :=
  (fun m => "mk_Piso'' " ++ pretty m.(Piso_map))%string.

#[export] Instance pretty_Psurj : Pretty Psurj :=
  (fun m => "Psurj_of_Pmap " ++ pretty m.(Psurj_map))%string.

(* Compute pretty (partition_of_func
  (({[1 := 1; 2:= 1; 3 := 4; 5:= 1]} :> Pmap positive) !!!.)
  [1;2;3;5])%positive. *)

#[export] Instance pretty_sigT {A} {P : A -> Type}
  `{Pretty A, forall a, Pretty (P a)} : Pretty (sigT P) :=
  (fun '(existT a p) =>
  String.concat " " [
    "existT";
    pretty a;
    pretty p
  ]
  )%string.


(* Compute pretty (partitions 5 !! 5).

Compute pretty (make_blocks [{[ 1; 2; 4; 5 ]}; {[ 3 ]}])%positive. *)

#[export] Instance pretty_ascii : Pretty Ascii.ascii :=
  (fun a => "'" ++ String a EmptyString ++ "'")%string.

Definition pth_letter (p : positive) : string :=
  String (Ascii.ascii_of_pos (96 + p)) EmptyString.




Definition hg_succ_aux (vmap : Pmap (Pset * Pset)) : prel :=
  map_fold (λ _ '(precs, succs) m,
    prel_union (set_to_map (.,precs) succs) m) ∅ vmap.

Definition hg_succ {T} (hg : Pmap (T * list positive * list positive)) : prel :=
  let vmap := vertex_map hg in
  hg_succ_aux vmap.

Definition hg_succs {T} (hg : Pmap (T * list positive * list positive)) : prel :=
  prel_tc (hg_succ hg).
(* Compute pretty (partitions_of_list [1;3;5])%positive. *)


Definition prel_eq_chain (ps : list positive) : prel :=
  list_to_map (prod_map id singleton <$> (zip ps (drop 1 ps ++ take 1 ps))).

(* Compute pretty $
  let R := (prel_eq_chain (pseq 1 10)) in
  pretty $ prel_tc_aux (size R - 2)%nat R R. *)






(* A matching of cospans of hypergraphs subcohg into cohg is a subgraph
  homomorphism (concretely, a pair of maps fv and fe on the vertices and
  edges preserving incidence, i.e. for every edge (idx, (t, ins, outs)) of subcohg,
    (fe idx, (t, fv <$> ins, fv <$> outs)) is an edge of cohg) such that
  a) fe is injective
  b) fv is injective _except_ possibly on the boundary/interface of subcohg
  c) for every vertex v of the interior of subcohg, every edge e' of
    cohg incident to v is in the image of fe

  Given these three conditions, we can construct _a_ pushout complement
  (in the category of hypergraphs, so not necessarily maintaining
    acyclicity or monogamy) by removing the image of the interior of subcohg
  from cohg and (TODO: HOW????) handling the boundary
    (TODO: Follow up. AN: I feel like there's some way to handle this
    progressively vertex-by-vertex on the boundary. Even though this has
    been presented as a two-step, global process (construct a whole exploded
    graph, then figure out how to quotient) it seems we should simply be
    able to enumerate the positions a given vertex can go in. I'll explore
    this for bimonogamous in this file, then maybe try to extend.)
  *)

(* NB: IN THIS FILE I WILL ASSUME EDGE LABELS ARE [Countable].
  This is so I can use [Pmap]s to index edges by label _and_ degrees. *)

(* How to construct a matching:
  As a zeroeth step, we match all isolated vertices (this match is unique,
    if it exists)
  First, we have to match all the edges.
    1. We construct a map from (label, indegree, outdegree) to the list of
      edge indices in cohg with that label, indegree, and outdegree,
      and do the same for subcohg.
    2. Using these maps, we enumerate all the possible edge matches

  Second, we have to extend these matchings subordinate to the

*)

Fixpoint sublistings_aux {B} (l'revhd l' : list B) : list (B * list B) :=
  match l' with
  | [] => []
  | b :: l' =>
    (b, rev_append l'revhd l') :: sublistings_aux (b :: l'revhd) l'
  end.

Fixpoint sublistings {A B} (l : list A) (l' : list B) : list (list (A * B)) :=
  match l with
  | [] => [[]]
  | a :: l =>
    '(b, l') ← sublistings_aux [] l';
    ((a, b) ::.) <$> sublistings l l'
  end.

Fixpoint ofold_sublistings {A B C} (f : A -> B -> C -> option C)
  (l : list A) (l' : list B) (acc : C) : list C :=
  match l with
  | [] => [acc]
  | a :: l =>
    '(b, l'') ← sublistings_aux [] l';
    match f a b acc with
    | None => []
    | Some acc' =>
      ofold_sublistings f l l'' acc'
    end
  end.

Definition kimerge_aux {K1} `{forall A, PartialAlter K2 A (M2 A)}
  `{forall A, Empty (M2 A)} {A B}
  (f : K1 -> A -> K2 * B) (l : list (K1 * A)) :=
  foldr (fun '(k1, a) (m' : M2 (list B)) =>
    let '(k2, b) := f k1 a in
    partial_alter (fun a_s =>
      Some (from_option (b ::.) [b] a_s)) k2 m')
  (∅ :> M2 (list B)) l.

Definition kimerge `{forall A, MapFold K1 A (M1 A)}
  `{forall A, PartialAlter K2 A (M2 A)}
  `{forall A, Empty (M2 A)} {A B}
  (f : K1 -> A -> K2 * B) (m : M1 A) : M2 (list B) :=
  kimerge_aux f (map_to_list m).


Definition kimerge_gen `{forall A, MapFold K1 A (M1 A)}
  `{forall A, PartialAlter K2 A (M2 A)}
  `{forall A, Empty (M2 A)} {A B}
  (fb : B -> B -> B)
  (f : K1 -> A -> K2 * B) (m : M1 A) : M2 B :=
  map_fold (fun k1 a (m' : M2 B) =>
    let '(k2, b) := f k1 a in
    partial_alter (fun a_s =>
      Some (from_option (fb b) b a_s)) k2 m')
  (∅ :> M2 B) m.





(* Compute sublistings [1;2] [1;2;3].
Time
Compute ofold_sublistings (fun n m res =>
  if decide (Nat.divide n m) then Some ((n, m) :: res) else None)
  (seq 2 4) (seq 1 10) []. *)


Definition Pcounts (l : list positive) : Pmap nat :=
  foldr (λ v m, partial_alter (λ d, Some (from_option S 1 d)) v m) ∅ l.

Definition hg_degree_map {T} (hg : Pmap (T * list positive * list positive)) :
  Pmap nat :=
  map_fold (λ _ '(_, ins, outs) m,
    merge (union_with (λ n m, Some (n + m))) (Pcounts (ins ++ outs)) m) ∅ hg.

Definition cohg_degree_map {T n m} (cohg : CospanHyperGraph T n m) : Pmap nat :=
  merge (union_with (λ n m, Some (n + m)))
    (Pcounts (cohg.(inputs) ++ cohg.(outputs)))
    (hg_degree_map cohg).


Definition hg_iodegree_map {T} (hg : Pmap (T * list positive * list positive)) :
  Pmap (nat * nat) :=
  map_fold (λ _ '(_, ins, outs) m,
    merge (union_with (λ '(n, n') '(m, m'), Some (n + m, n' + m')))
      (merge (λ mayout mayin,
        match mayin, mayout with
        | Some indeg, Some outdeg => Some (indeg, outdeg)
        | Some indeg, None => Some (indeg, 0)
        | None, Some outdeg => Some (0, outdeg)
        | None, None => None
        end) (Pcounts ins) (Pcounts outs)) m) ∅ hg.


Definition cohg_iodegree_map {T n m} (cohg : CospanHyperGraph T n m) : Pmap (nat * nat) :=
  merge (union_with (λ '(n, n') '(m, m'), Some (n + m, n' + m')))
      (merge (λ mayin mayout,
        match mayin, mayout with
        | Some indeg, Some outdeg => Some (indeg, outdeg)
        | Some indeg, None => Some (indeg, 0)
        | None, Some outdeg => Some (0, outdeg)
        | None, None => None
        end) (Pcounts cohg.(inputs)) (Pcounts cohg.(outputs)))
    (hg_iodegree_map cohg).

(* Compute pretty $ cohg_iodegree_map (@graph_of_tensor _ xH 2 2). *)


Definition is_bimonogamousb {T n m} (cohg : CospanHyperGraph T n m) :=
  bool_decide (map_Forall (λ _ v, v = 2) (cohg_degree_map cohg)).

Definition is_monogamousb {T n m} (cohg : CospanHyperGraph T n m) :=
  bool_decide (map_Forall (λ _ v, v = (1, 1)) (cohg_iodegree_map cohg)).






Definition make_label_indexed_edge_map `{Countable T}
  (es : Pmap (T * list positive * list positive)) :
  gPmap (T * N * N) (list (positive * list positive * list positive)) :=
  kimerge (M2:=gPmap _) (fun idx '(t, ins, outs) =>
    ((t, lengthN ins, lengthN outs), (idx, ins, outs))) es.

Definition make_aligned_edge_list {T}
  (es es' : gPmap (T * N * N) (list (positive * list positive * list positive))) :
  list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)) :=
  let m' := merge (M:=Pmap) (fun me me' =>
    (λ e, from_option (e,.) (e, []) me') <$> me) es es' in
  (map_to_list m').*2.


Definition spupdate (noninj_dom : Pset) (k v : positive) (m : Psurj) : option Psurj :=
  if decide (k ∈ noninj_dom) then
    match m.(Psurj_map) !! k with
    | None => Some (<[k := v]> m)
    | Some v' => if decide (v = v') then Some m else None
    end
  else Psurj_inj_insert k v m.

(* Compute pretty $ Psurj_of_Pmap {[1 := 1]}%positive. *)


Definition spupdates (noninj_dom : Pset) (kvs : list (positive * positive))
  (m : Psurj) : option Psurj :=
  foldr (λ '(k, v) maym, maym ≫= spupdate noninj_dom k v) (Some m) kvs.

Definition update_frobenius_edge_match
  (boundary : Pset) (e e' : positive * list positive * list positive)
  (me_mv : Piso * Psurj) : option (Piso * Psurj) :=
  let '(me, mv) := me_mv in
  let '(idx, ins, outs) := e in
  let '(idx', ins', outs') := e' in
  me' ← pupdate idx idx' me;
  mv' ← spupdates boundary (zip (ins ++ outs) (ins' ++ outs')) mv;
  Some (me', mv').

Fixpoint frobenius_edge_matchings_extending_aux_aligned
  (boundary : Pset)
  (es_es' : list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)))
    (* The edges of subcohg and cohg, aligned by label and in/outdegrees *)
  (me_mv : Piso * Psurj) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Psurj) :=
  match es_es' with
  | [] => [me_mv]
  | (es, es') :: es_es' =>
    ofold_sublistings (update_frobenius_edge_match boundary) es es' me_mv ≫=
    frobenius_edge_matchings_extending_aux_aligned boundary es_es'
  end.


Definition frobenius_edge_matchings_extending `{Countable T}
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *)
  (me_mv : Piso * Psurj) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Psurj) :=
  frobenius_edge_matchings_extending_aux_aligned boundary
    (make_aligned_edge_list (make_label_indexed_edge_map es)
      (make_label_indexed_edge_map es')) me_mv.

Definition frobenius_edge_matchings `{Countable T}
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Psurj) :=
  let vmap := vertex_map es' in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Psurj_map) !!.) boundary in

    map_Forall
      (fun v' _ =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Psurj_invmap)
  ) $
    frobenius_edge_matchings_extending boundary es es' (∅, ∅).


Definition graph_boundary {T n m} (cohg : CospanHyperGraph T n m) : Pset :=
  list_to_set (cohg.(inputs) ++ cohg.(outputs)).


Fixpoint frobenius_vertex_matchings_extending (vs : list positive)
  (codom_verts : list positive)
    (* The vertices in the codomain which are _not_ in the image of mv
      (invariant) *)
  (true_boundary : Pset)
  (mv : Pmap positive) : list (Pmap positive * Pset) :=
  match vs with
  | [] => [(mv, true_boundary)]
  | v :: vs =>
    if decide (is_Some (mv !! v)) then
      (* v is already assigned! Nothing to do *)
      frobenius_vertex_matchings_extending vs codom_verts true_boundary mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      v' ← codom_verts;
      frobenius_vertex_matchings_extending vs codom_verts
        ({[v']} ∪ true_boundary) (<[v := v']> mv)
  end.



Definition frobenius_graph_matchings `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list (Piso * Pmap positive * Pset) :=
  let boundary := graph_boundary subcohg in
  '(me, mv) ← frobenius_edge_matchings boundary subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Psurj_invmap) !! v = None) (vertices cohg) in
  (λ '(mv', bnd), (me, mv', (set_map (mv'!!!.) (graph_boundary subcohg))))
    <$> frobenius_vertex_matchings_extending (inputs subcohg ++ outputs subcohg) codom_verts ∅ mv.




Definition update_bimonog_edge_match (e e' : positive * list positive * list positive)
  (me_mv : Piso * Piso) : option (Piso * Piso) :=
  let '(me, mv) := me_mv in
  let '(idx, ins, outs) := e in
  let '(idx', ins', outs') := e' in
  me' ← pupdate idx idx' me;
  mv' ← pupdates (zip (ins ++ outs) (ins' ++ outs')) mv;
  Some (me', mv').

Fixpoint bimonog_edge_matchings_extending_aux_aligned
  (es_es' : list (list (positive * list positive * list positive) *
    list (positive * list positive * list positive)))
    (* The edges of subcohg and cohg, aligned by label and in/outdegrees *)
  (me_mv : Piso * Piso) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Piso) :=
  match es_es' with
  | [] => [me_mv]
  | (es, es') :: es_es' =>
    ofold_sublistings update_bimonog_edge_match es es' me_mv ≫=
    bimonog_edge_matchings_extending_aux_aligned es_es'
  end.


Definition bimonog_edge_matchings_extending `{Countable T}
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *)
  (me_mv : Piso * Piso) (* The partial injections for the interior *)
    (* TODO: FIXME: This probably doesn't work for the Frobenius case:
      for bimonogamous, if a vertex is incident to an edge of es, it
      can't be a point of non-injectivity on the boundary, so we needn't
      worry about forcing all of them to be injectively mapped. I'm not
      _positive_ if that's valid for Frobenius *) : list (Piso * Piso) :=
  bimonog_edge_matchings_extending_aux_aligned
    (make_aligned_edge_list (make_label_indexed_edge_map es)
      (make_label_indexed_edge_map es')) me_mv.

Definition bimonog_edge_matchings `{Countable T}
  (boundary : Pset)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Piso) :=
  let vmap := vertex_map es' in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Piso_map) !!.) boundary in
    (* FIXME: Is there some test I can do here to help with bimonogamy? *)
    map_Forall
      (fun _ v' =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Piso_map)
  ) $
    bimonog_edge_matchings_extending es es' (∅, ∅).



(* NB: This is ONLY for boundary vertices of (bi)monogamous hypergraphs! *)
Fixpoint bimonog_vertex_matchings_extending (vs : list positive)
  (codom_verts : list positive)
    (* The vertices in the codomain which are _not_ in the image of mv
      (invariant) *)
  (true_boundary : Pset)
  (mv : Pmap positive) : list (Pmap positive * Pset) :=
  match vs with
  | [] => [(mv, true_boundary)]
  | v :: vs =>
    if decide (is_Some (mv !! v)) then
      (* v is already assigned! Nothing to do *)
      bimonog_vertex_matchings_extending vs codom_verts true_boundary mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      '(v', codom_verts') ← sublistings_aux [] codom_verts;
      bimonog_vertex_matchings_extending vs codom_verts'
        ({[v']} ∪ true_boundary) (<[v := v']> mv)
  end.

Definition bimonog_graph_matchings `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list (Piso * Pmap positive * Pset) :=
  let boundary := graph_boundary subcohg in
  '(me, mv) ← bimonog_edge_matchings boundary subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Piso_invmap) !! v = None) (vertices cohg) in
  (λ '(mv', bnd), (me, mv', bnd)) <$> bimonog_vertex_matchings_extending (inputs subcohg ++ outputs subcohg) codom_verts ∅ mv.





Definition monog_edge_matchings `{Countable T}
  (boundary : Pset) (cohg_succs : prel)
  (es : Pmap (T * list positive * list positive))
    (* The edges of subcohg*)
  (es' : Pmap (T * list positive * list positive))
    (* The edges of cohg *) : list (Piso * Piso) :=
  let vmap := vertex_map es' in
  let cohg_succ := hg_succ_aux vmap in
  filter (
    fun '(me, mv) =>
    let boundary' : Pset := set_omap (mv.(Piso_map) !!.) boundary in

    map_Forall
      (fun _ v' =>
        Is_true (
          if decide (v' ∈ boundary') then true
          else
          match vmap !! v' with
          | None => true
          | Some (inc_es, inc_es') =>
            let incident_edges := inc_es ∪ inc_es' in
            Pmap_dom_subseteqb (mapset.mapset_car incident_edges)
              me.(Piso_invmap)
          end))
      mv.(Piso_map) /\
      (* Convexity : *)
      let es' : Pset := dom me.(Piso_invmap) in
      es' ## prel_img cohg_succs (prel_img cohg_succ es' ∖ es')
  ) $
    bimonog_edge_matchings_extending es es' (∅, ∅).



(* NB: This is ONLY for boundary vertices of monogamous hypergraphs! *)
Fixpoint monog_vertex_matchings_extending (vs : list positive)
  (codom_verts : list positive)
    (* The vertices in the codomain which are _not_ in the image of mv
      (invariant) *)
  (mv : Piso) : list Piso :=
  match vs with
  | [] => [mv]
  | v :: vs =>
    if decide (is_Some (mv.(Piso_map) !! v)) then
      (* v is already assigned! Nothing to do *)
      monog_vertex_matchings_extending vs codom_verts mv
    else
      (* v can be assigned anywhere not in the image of mv *)
      '(v', codom_verts') ← sublistings_aux [] codom_verts;
      from_option (monog_vertex_matchings_extending vs codom_verts') [] (pupdate v v' mv)
  end.

Definition monog_graph_matchings `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (cohg_succs : prel) : list (Piso * Piso) :=
  let boundary := graph_boundary subcohg in
  '(me, mv) ← monog_edge_matchings boundary cohg_succs subcohg cohg;
  let codom_verts := elements $ filter (λ v, mv.(Piso_invmap) !! v = None) (vertices cohg) in
  (λ mv', (me, mv')) <$>
    monog_vertex_matchings_extending (inputs subcohg ++ outputs subcohg) codom_verts mv.






Definition explode_step (arities : Pmap (list nat))
  (p : positive) : Pmap (list nat) * positive :=
  match arities !! p with
  | None => (arities, xO p)
  | Some l => (alter tl p arities, xI $ encode (p, hd 0 l))
  end.

Definition explode_list (arities : Pmap (list nat))
  (ps : list positive) : Pmap (list nat) * list positive :=
  foldr (λ p '(ar, ps), let '(ar', p') := explode_step ar p in
    (ar', p' :: ps)) (arities, []) ps.


Fixpoint explode_vec (arities : Pmap (list nat))
  {n} (ps : vec positive n) : Pmap (list nat) * vec positive n :=
  match ps with
  | [#] => (arities, [#])
  | p ::: ps =>
    let '(ar, ps) := explode_vec arities ps in
    let '(ar', p') := explode_step ar p in
    (ar', p' ::: ps)
  end.

Definition explode_hypergraph_aux {T} (arities : Pmap (list nat))
  (hg : Pmap (T * list positive * list positive)) :
  Pmap (list nat) * Pmap (T * list positive * list positive) :=
  map_fold (λ k '(t, ins, outs) '(ar, m),
    let '(ar, ins') := explode_list ar ins in
    let '(ar, outs') := explode_list ar outs in
    (ar, <[k := (t, ins', outs')]> m)) (arities, ∅) hg.

Definition explode_hypergraph {T} (arities : Pmap (list nat))
  (hg : HyperGraph T) : Pmap (list nat) * HyperGraph T :=
  let '(ar, hg') := explode_hypergraph_aux arities hg.(hyperedges) in
  (ar, mk_hg hg'
    (set_bind (λ p,
      match arities !! p with
      | None => {[xO p]}
      | Some l =>
        list_to_set ((λ k, xI $ encode (p, k)) <$> l)
      end) hg.(hypervertices))).

Definition explode_cohg {T n m} (arities : Pmap (list nat))
  (cohg : CospanHyperGraph T n m) : Pmap (list nat) * CospanHyperGraph T n m :=
  let '(ar, ins) := explode_vec arities cohg.(inputs) in
  let '(ar, outs) := explode_vec ar cohg.(outputs) in
  let '(ar, hg) := explode_hypergraph ar cohg.(hedges) in
  (ar, mk_cohg hg ins outs).






Definition exploded_context {T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (me : Piso) (mv : Pmap positive) (true_bnd : Pset) :
  Pmap (list positive) * CospanHyperGraph T n m :=

  (* let mv_bnd_map := restrict_map (graph_boundary subcohg) mv.(Piso_map) in
  let mv_boundary_img_cohg : Pset := map_img mv_bnd in *)
  let mv_boundary_img_cohg := true_bnd in

  let context : CospanHyperGraph T n m :=
    (mk_cohg (mk_hg
      (filter (λ k_tio, me.(Piso_invmap) !! k_tio.1 = None) (hyperedges cohg))
      (hypervertices cohg (* ∪ mv_boundary_img_cohg *)))
      cohg.(inputs)
      cohg.(outputs)) in

  let deg := cohg_degree_map context in
  let bnd_deg : Pmap nat := restrict_map mv_boundary_img_cohg deg in
  let bnd_deg_ars : Pmap (list nat) := seq O <$> bnd_deg in
  let '(_, exploded_context) := explode_cohg bnd_deg_ars context in
    (* ^ This is the exploded context; we just need to give a record of
      the g-equivalence classes. These are pretty trivial to generate, though *)

  let g_equiv_classes := map_imap
    (λ p (ar : list _), Some $ (((λ k, xI $ encode (p, k)) <$> ar))) bnd_deg_ars in
  (g_equiv_classes, exploded_context).

Definition exploded_interfaced_context {T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (me : Piso) (mv : Pmap positive) (true_bnd : Pset) :
  Pmap blocks * CospanHyperGraph T n ((i + j) + m) :=
  let '(g_equiv_classes, exploded_context) := exploded_context subcohg cohg me mv true_bnd in

  (* TODO: Fix this: Relabel to ensure disjointness with the added boundary *)
  let g_equiv_classes := fmap xI <$> g_equiv_classes in
  let exploded_context := relabel_graph xI exploded_context in
  (* let mv := xI <$> mv in  *) (* NB: We don't relabel mv because
    it's used to say where in the _original_ graph each element of the
    boundary lands; we're just changing our names for the new context *)

  let exploded_interfaced_context :=
    mk_cohg exploded_context exploded_context.(inputs)
      (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j)) +++ exploded_context.(outputs)) in

  let subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs) in

    (* Equivalence classes of interface vertices for _g_ *)
  let interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)) in

    (* Equivalence classes of interface vertices for _f_ *)
  let f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes in

  (* Now, I'm ASSUMING (TODO: triple-check this [AN: I have found direct evidence
     in the paper]) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

  let g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes in

  (merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks, exploded_interfaced_context).


Definition partitions_joining_wildly_inefficient (p : blocks) : list blocks :=
  let supp := elements (foldr (λ b, union b.2) ∅ p) in
  filter (λ p', length (join_partitions p p') = 1) (partitions_of_list supp).

Fixpoint partitions_joining_aux_inserts (k : positive) (p : blocks) : list blocks :=
  match p with
  | [] => []
  | (bmin, b) :: p =>
    ((Pos.min bmin k, {[k]} ∪ b) :: p) ::
    (((bmin, b) ::.) <$> partitions_joining_aux_inserts k p)
  end.

Definition partitions_joining_mildly_inefficient (p : blocks) : list blocks :=
  let (psingl, pnontrivial) := list_split (λ '(bmin, b), length (elements b) = 1) p in
  match pnontrivial with
  | [] => [make_blocks [list_to_set psingl.*1]]
  | _ =>
  let base_equivs := partitions_joining_wildly_inefficient pnontrivial in
  foldr (λ '(bmin, _) equivs, equivs ≫= partitions_joining_aux_inserts bmin) base_equivs psingl
  end.

Definition make_pushout {T} {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (context : CospanHyperGraph T n ((i + j) + m)) : CospanHyperGraph T n m :=
  compose_graphs context (stack_graphs
    (* (wrapunder_l subcohg) *) (compose_graphs (stack_graphs subcohg (id_graph j)) (cap_graph j))
    (id_graph m)).


(* Fixpoint quotient_maps_aux (f_g_equiv_classes : Pmap blocks) : list (Pmap positive) := *)

Definition quotient_maps (f_g_equiv_classes : Pmap blocks) : list (Pmap positive) :=
  map_fold (λ _ (bl : blocks) (maps : list (Pmap positive)),
    bl' ← partitions_joining_mildly_inefficient bl;
    (partition_quotient bl' ∪.) <$> maps) [∅] f_g_equiv_classes.


Definition quotiented_contexts {T}
  (f_g_equiv_classes : Pmap blocks)
  {n ijm} (exploded_interfaced_context : CospanHyperGraph T n ijm) :
  list (CospanHyperGraph T n ijm) :=
  (λ m, relabel_graph (Pmap_map m) exploded_interfaced_context) <$> quotient_maps f_g_equiv_classes.


Definition all_frobenius_contexts `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list (CospanHyperGraph T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then [] else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← frobenius_graph_matchings subcohg cohg;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

  
Definition select_frobenius_context `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) 
  (match_number quotient_number : nat) : option (CospanHyperGraph T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then None else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← frobenius_graph_matchings subcohg cohg !! match_number;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context !! quotient_number.


Definition frobenius_graph_rewriting_correctness `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : nat * bool :=
  foldr (λ cohg' '(len, corr),
    (S len, if corr :> bool then
      (@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg cohg')
      else false)) (0, true)
    (make_pushout subcohg <$> all_frobenius_contexts subcohg cohg).


Definition frobenius_graph_rewriting_correctness' `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list bool :=
    ((@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg) ∘
    make_pushout subcohg <$> all_frobenius_contexts subcohg cohg).



(* FIXME: Ideally, I'd like to better understand the bimonogamous case
  so we can replace this filter hack with something much better. For now,
  there's a paper to write. *)

Definition all_bimonog_contexts `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list (CospanHyperGraph T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then [] else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← bimonog_graph_matchings subcohg cohg;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  filter is_bimonogamousb $ quotiented_contexts f_g_equiv_classes exploded_interfaced_context.


Definition select_bimonog_context `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) 
  (match_number : nat)
  (quotient_number : nat) : option (CospanHyperGraph T n ((i + j) + m)) :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then None else

  let cohg' := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← bimonog_graph_matchings subcohg cohg' !! match_number;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg' me mv true_bnd in
  (filter is_bimonogamousb $ quotiented_contexts f_g_equiv_classes 
    exploded_interfaced_context) !! quotient_number.


Definition bimonog_graph_rewriting_correctness `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : nat * bool :=
  foldr (λ cohg' '(len, corr),
    (S len, if corr :> bool then
      (@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg cohg')
      else false)) (0, true)
    (make_pushout subcohg <$> all_bimonog_contexts subcohg cohg).


Definition bimonog_graph_rewriting_correctness' `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list bool :=
    ((@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg) ∘
    make_pushout subcohg <$> all_bimonog_contexts subcohg cohg).



Definition monog_graph_decomp {T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (cohg_succs : prel)
  (me mv : Piso) : {k : nat & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type :=
  let L_edges : Pset := dom me.(Piso_invmap) in
  let C2_edges := prel_img cohg_succs L_edges ∖ L_edges in
  let C1_edges := dom (hyperedges cohg) ∖ (C2_edges ∪ L_edges) in
  let C1_hg : HyperGraph T :=
    mk_hg (restrict_map C1_edges (hyperedges cohg)) (isolated_vertices cohg) in
  let C2_hg : HyperGraph T :=
    mk_hg (restrict_map C2_edges (hyperedges cohg)) ∅ in
  let k_set := ((list_to_set cohg.(inputs) ∪ referenced_vertices_hg C1_hg) ∩
    (list_to_set cohg.(outputs) ∪ referenced_vertices_hg C2_hg)) ∖ dom mv.(Piso_invmap) in
  let k_vec := list_to_vec (elements k_set) in
  let i_vec := vmap (mv.(Piso_map)!!!.) subcohg.(inputs) in
  let j_vec := vmap (mv.(Piso_map)!!!.) subcohg.(outputs) in
  existT _ (mk_cohg C1_hg cohg.(inputs) (k_vec +++ i_vec),
    mk_cohg C2_hg (k_vec +++ j_vec) cohg.(outputs)).

Definition make_monog_pushout {T i j}
  (subcohg : CospanHyperGraph T i j)
  {n m} (context : {k & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type) :
    CospanHyperGraph T n m :=
  let '(existT k (C1, C2)) := context in
  compose_graphs (compose_graphs C1 (stack_graphs (id_graph k) subcohg)) C2.

Definition all_monog_contexts `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  : list {k : nat & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then [] else

  let cohg := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)
  let cohg_succs := hg_succs cohg in
  (λ '(me, mv), monog_graph_decomp subcohg cohg cohg_succs me mv)
    <$> monog_graph_matchings subcohg cohg cohg_succs.

Definition verified_monog_graph_decomp `{Countable T} {i j}
  (subcohg : CospanHyperGraph T i j) {n m} (cohg cohg' : CospanHyperGraph T n m)
  cohg_succs me mv :
    option {k & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type :=
  let ctx := monog_graph_decomp subcohg cohg' cohg_succs me mv in
  (* TODO: Replace with something that uses me and mv productively to make this
    almost trivial. Also probably need something with isol verts to do that I guess? *)
  if default_countable_graph_iso_test cohg (make_monog_pushout subcohg ctx) then
    Some ctx
  else None.

Lemma verified_monog_graph_decomp_correct `{Countable T} {i j}
  (subcohg : CospanHyperGraph T i j) {n m} (cohg cohg' : CospanHyperGraph T n m)
  cohg_succs me mv ctx :
  verified_monog_graph_decomp subcohg cohg cohg' cohg_succs me mv = Some ctx ->
  cohg ≡ₛ make_monog_pushout subcohg ctx.
Proof.
  unfold verified_monog_graph_decomp.
  destruct (default_countable_graph_iso_test_correct' cohg
    (make_monog_pushout subcohg
      (monog_graph_decomp subcohg cohg' cohg_succs me mv))); [|done].
  now intros [= <-].
Qed.


Definition verified_select_monog_context `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : nat)
  : option {k : nat & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then None else

  let cohg' := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)
  let cohg_succs := hg_succs cohg in
  '(me, mv) ← monog_graph_matchings subcohg cohg' cohg_succs !! match_number;
  verified_monog_graph_decomp subcohg cohg cohg' cohg_succs me mv.

Lemma verified_select_monog_context_correct `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : nat) ctx :
  verified_select_monog_context subcohg cohg match_number = Some ctx ->
  cohg ≡ₛ make_monog_pushout subcohg ctx.
Proof.
  unfold verified_select_monog_context.
  case_decide; [done|].
  destruct (_ !! _) as [[me mv]|]; [|done].
  cbn.
  apply verified_monog_graph_decomp_correct.
Qed.


Definition select_monog_context `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m)
  (match_number : nat)
  : option {k : nat & CospanHyperGraph T n (k + i) * CospanHyperGraph T (k + j) m}%type :=
  (* First, check we have enough isolated vertices and remove
    those we'll replace *)
  let num_sub_isol := size (isolated_vertices subcohg) in
  let cohg_isol := elements (isolated_vertices cohg) in
  if decide (length cohg_isol < num_sub_isol) then None else

  let cohg' := (set_verts cohg (list_to_set (drop num_sub_isol cohg_isol))) in

  (* Next, we get a candidate matching *)
  let cohg_succs := hg_succs cohg in
  (λ '(me, mv), monog_graph_decomp subcohg cohg' cohg_succs me mv)
  <$> monog_graph_matchings subcohg cohg' cohg_succs !! match_number.




Definition monog_graph_rewriting_correctness `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : nat * bool :=
  foldr (λ cohg' '(len, corr),
    (S len, if corr :> bool then
      (@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg cohg')
      else false)) (0, true)
    (make_monog_pushout subcohg <$> all_monog_contexts subcohg cohg).


Definition monog_graph_rewriting_correctness' `{Countable T}
  {i j} (subcohg : CospanHyperGraph T i j)
  {n m} (cohg : CospanHyperGraph T n m) : list bool :=
    ((@Testing.opt_weak_graph_iso_partial_test T eq _ _ _ cohg) ∘
    make_monog_pushout subcohg <$> all_monog_contexts subcohg cohg).









From stdpp Require Import strings.

Definition test_graph_33_lhs : CospanHyperGraph string 1 1 :=
  (mk_cohg ∅
    [# 1] [# 1]
  )%positive%string.

Definition test_graph_33_rhs : CospanHyperGraph string 1 1 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ]} ∅)
    [# 1] [# 3]
  )%positive%string.

Definition test_graph_34_lhs : CospanHyperGraph string 1 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [1], [4]) ; 4 := ("g", [4], [5]) ]} ∅)
    [# 1] [# 3; 5]
  )%positive%string.

Definition test_graph_34_rhs : CospanHyperGraph string 1 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [1], [4]) ; 4 := ("f", [4], [5]) ;
    5 := ("g", [5], [6]) ; 6 := ("g", [6], [7]) ]} ∅)
    [# 1] [# 3; 7]
  )%positive%string.

(*
Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_lhs test_graph_34_rhs) in
    lazymatch r with
    | (39%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).
Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_lhs test_graph_34_lhs) in
    lazymatch r with
    | (29%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).

Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs test_graph_34_lhs) in
    lazymatch r with
    | (2%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).

Succeed Compute
    ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs test_graph_34_rhs) in
    lazymatch r with
    | (2%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end).
*)

Definition test_graph_34_layer n : CospanHyperGraph string n (n * 2) :=
  (fix go n : CospanHyperGraph string n (n * 2) :=
    match n with
    | 0 => id_graph 0
    | S n => stack_graphs test_graph_34_rhs (go n)
    end) n.

Fixpoint test_graph_34_exploded n : CospanHyperGraph string 1 (2 ^ n) :=
  match n with
  | 0 => id_graph 1
  | S n =>
    cast_graph eq_refl (Nat.mul_comm (2^n) 2) $ compose_graphs (test_graph_34_exploded n)
      (test_graph_34_layer _)
  end.


Definition test_graph_33_layer k : CospanHyperGraph string k k :=
  (fix go k : CospanHyperGraph string k k :=
    match k with
    | 0 => id_graph 0
    | S k => stack_graphs test_graph_33_rhs (go k)
    end) k.

Definition test_graph_33_array n k : CospanHyperGraph string k k :=
  (fix go n : CospanHyperGraph string k k :=
    match n with
    | 0 => id_graph k
    | S n => compose_graphs (test_graph_33_layer k) (go n)
    end) n.

(* Compute pretty (hg_succs test_graph_33_rhs). *)

Definition test_graph_33_rhs_stack2 : CospanHyperGraph string 2 2 :=
  (mk_cohg (mk_hg {[ 1 := ("f", [1], [2]) ; 2 := ("g", [2], [3]) ;
    3 := ("f", [4], [5]) ; 5 := ("g", [5], [6]) ]} ∅)
    [# 1; 4] [# 3; 6]
  )%positive%string.

(* Compute is_monogamousb (test_graph_33_array 3 2). *)

(* Compute monog_graph_rewriting_correctness test_graph_33_rhs_stack2
  (test_graph_33_array 3 2). *)

(* Compute monog_graph_rewriting_correctness (stack_graphs (id_graph 1)
test_graph_33_rhs_stack2) (test_graph_33_array 3 2). *)

(* Succeed Compute ltac:(let r := eval vm_compute in
      (frobenius_graph_rewriting_correctness test_graph_33_rhs_stack2
        (test_graph_33_array 2 2)) in
    lazymatch r with
    | (12%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)

(* Compute monog_graph_rewriting_correctness' test_graph_33_rhs test_graph_33_rhs_stack2. *)

(* Compute pretty $ monog_graph_matchings
  test_graph_33_rhs test_graph_33_rhs_stack2 (hg_succs test_graph_33_rhs_stack2). *)


(* Compute pretty $ uncurry (monog_graph_decomp test_graph_33_rhs test_graph_33_rhs_stack2
  (hg_succs test_graph_33_rhs_stack2)) <$> monog_graph_matchings
  test_graph_33_rhs test_graph_33_rhs_stack2 (hg_succs test_graph_33_rhs_stack2). *)

(* Compute pretty $ monog_graph_matchings test_graph_33_rhs test_graph_33_rhs (hg_succs test_graph_33_rhs). *)

(* Compute monog_graph_rewriting_correctness' test_graph_33_rhs test_graph_33_rhs. (test_graph_33_array 2 2). *)


(*
Definition test_graph_cap_lhs : CospanHyperGraph string 2 0 := cap_graph 1.
Definition test_graph_cap_rhs : CospanHyperGraph string 2 0 :=
  (mk_cohg (mk_hg {[1 := ("f", [1;2], [])]} ∅) [#1;2] [#])%positive.

  Time
Compute pretty $ all_bimonog_contexts test_graph_cap_lhs (test_graph_33_array 2 3) !! 10.

Compute filter is_bimonogamousb $ all_bimonog_contexts test_graph_cap_lhs (test_graph_33_array 2 2). *)



(* Compute is_bimonogamousb (@cup_graph positive 2). *)

(* Time Compute is_bimonogamousb (test_graph_33_array 10 10). *)

(* Compute length $ all_frobenius_contexts test_graph_33_rhs (test_graph_33_array 3 3). *)
(* Compute  test_graph_33_rhs (test_graph_33_array 3 3). *)
(* Compute is_bimonogamousb <$> all_frobenius_contexts test_graph_33_rhs (test_graph_33_array 3 3). *)


(* Compute frobenius_graph_rewriting_correctness test_graph_33_rhs (test_graph_34_exploded 3). *)

(* Definition Plist_idxmap (l : list positive) : Pmap positive :=
  list_to_map (imap (λ i p, (p, Pos.of_succ_nat i)) l).

Definition reduce_graph {T n m} (cohg : CospanHyperGraph T n m) : CospanHyperGraph T n m :=
  let fe := Plist_idxmap (map_to_list (hyperedges cohg)).*1 in
  let fv := Plist_idxmap (elements (vertices cohg)) in
  relabel_graph (fv !!!.) (reindex_graph (fe !!!.) cohg). *)

(* Compute pretty $ (reduce_graph (test_graph_34_exploded 3)). *)

(* Time Compute
  let cohg := ((* reduce_graph *) (test_graph_34_exploded 2)) in
  monog_graph_rewriting_correctness test_graph_33_rhs cohg. *)


Module PaperExample.


(* #[local] Instance pretty_blocks_letter : Pretty blocks :=
  (fun p =>
  "[" ++ String.concat "; "
    ((λ '(_, b), "{[" ++ String.concat "; " (pth_letter <$>
      merge_sort Pos.lt (elements b)) ++ "]}") <$> p) ++ "]")%string. *)

Local Open Scope positive_scope.
Local Open Scope list_scope.


Definition frel := make_blocks [ {[1; 2]}; {[3; 4]} ]%positive.
Definition grel := make_blocks [ {[1; 2; 3; 4]} ]%positive.

Section perms.
Local Notation a := 1%positive.
Local Notation b := 2%positive.
Local Notation c := 3%positive.
Local Notation d := 4%positive.
Local Notation e := 5%positive.




Definition correct_perms : list blocks :=
  (make_blocks <$> [[{[a;b;c;d]}];
[{[a]};{[b;c;d]}];
[{[b]};{[a;c;d]}];
[{[a;c]};{[b;d]}];
[{[c]};{[a;b;d]}];
[{[d]};{[a;b;c]}];
[{[a;d]};{[b;c]}];
[{[a;c]};{[b]};{[d]}];
[{[a;d]};{[b]};{[c]}];
[{[b;c]};{[a]};{[d]}];
[{[b;d]};{[a]};{[c]}]])%positive.

End perms.

(* Compute pretty (filter (λ p, join_partitions p frel = grel) (partitions 4)). *)

(* Compute bool_decide (filter (λ p, join_partitions p frel = grel) (partitions 4) ≡ₚ correct_perms). *)

Module Example1.

Local Definition i : nat := 2.
Local Definition j : nat := 2.

Local Definition subcohg : CospanHyperGraph string i j :=
  mk_cohg ∅ [#1; 1] [#2; 2].

Local Definition cohg : CospanHyperGraph string 0 0 :=
  mk_cohg (mk_hg {[ 1 := ("e", [1], [1])]} ∅) [#] [#].

(* Succeed Compute
    ltac:(let r := eval vm_compute in (frobenius_graph_rewriting_correctness subcohg cohg) in
    lazymatch r with
    | (61%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)

Local Definition all_contexts := all_frobenius_contexts subcohg cohg.

(* Compute length all_contexts. *)

Definition remove_dupsA {A} (R : relation A) `{!RelDecision R} : list A -> list A :=
  fix remove_dupsA (l : list A) :=
  match l with
  | [] => []
  | x :: l => if decide (Exists (R x) l) then remove_dupsA l
    else x :: remove_dupsA l
  end.

Definition remove_dupsb {A} (R : A -> A -> bool) : list A -> list A :=
  fix remove_dupsb (l : list A) :=
  match l with
  | [] => []
  | x :: l => if existsb (R x) l then remove_dupsb l
    else x :: remove_dupsb l
  end.

Definition ascii_newline : Ascii.ascii := Ascii.ascii_of_pos 10.
Definition string_newline : string := Eval lazy in String ascii_newline EmptyString.

(* Compute ("[" ++ String.concat string_newline (pretty <$> all_contexts) ++ "]")%string. *)

(* Compute length (remove_dupsb (@Testing.opt_weak_graph_iso_partial_test _ eq _ _ _) all_contexts).
Time Compute length (@remove_dupsA _ (@Testing.opt_weak_graph_iso_partial_test _ eq _ _ _)
  (λ _ _, _) all_contexts). *)

(* Time Compute frobenius_graph_rewriting_correctness subcohg cohg. *)




Local Definition mv : Pmap positive :=
  {[1 := 1; 2 := 1]}.

Local Definition me : Piso := ∅.

Local Definition true_bnd : Pset := {[1]}.

Local Definition g_equiv_classes_exploded_context :=
  exploded_context subcohg cohg me mv true_bnd.

Local Definition g_equiv_classes := g_equiv_classes_exploded_context.1.
Local Definition exploded_context := g_equiv_classes_exploded_context.2.



Local Definition exploded_interfaced_context :=
    mk_cohg exploded_context exploded_context.(inputs)
      (exploded_context.(outputs) +++ vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j))).

Local Definition subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs).

    (* Equivalence classes of interface vertices for _g_ *)
Local Definition interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)).

    (* Equivalence classes of interface vertices for _f_ *)
Local Definition f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes.

  (* Now, I'm ASSUMING (TODO: triple-check this) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

Local Definition g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes.

(* Compute pretty g_equiv_classes_blocks. *)

Local Definition f_g_equiv_classes :=
  merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks.

(* Compute pretty f_g_equiv_classes. *)

Local Definition block_1 : blocks := f_g_equiv_classes !!! 1.

Local Definition fully_quotiented_contexts :=
  Eval vm_compute in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

(* Compute length fully_quotiented_contexts. *)

Local Instance cohg_empty {T n m} : Empty (CospanHyperGraph T n m) :=
  mk_cohg ∅ (fun_to_vec (λ _, xH)) (fun_to_vec (λ _, xH)).

Local Instance cohg_inhabited {T n m} : Inhabited (CospanHyperGraph T n m) :=
  populate $ mk_cohg ∅ (fun_to_vec (λ _, xH)) (fun_to_vec (λ _, xH)).


(* Compute forallb (graph_iso_partial_test cohg)
  (make_pushout subcohg <$> fully_quotiented_contexts). *)


(* Compute pretty block_1. *)

(* Compute length $ partitions_joining_wildly_inefficient block_1.
Compute length $ partitions_joining_mildly_inefficient block_1. *)






#[export] Instance maybe_Npos : Maybe Npos :=
  fun n =>
  match n with
  | N0 => None
  | Npos p => Some p
  end.

Definition map_partition (f : positive -> positive) (p : blocks) : blocks :=
  (λ '(bmin, bset), let bset' := set_map f bset in
    (default bmin (maybe Npos (Pset_min bset')), bset')) <$> p.

Definition block_1_quotiented : blocks :=
  map (λ '(bmin, _), (bmin, {[bmin]})) block_1.

(* Compute length $ partitions_joining_wildly_inefficient block_1_quotiented. *)

(* TODO: Investigate / think about if this is a valid way to cut down on the
  number of resulting graphs, or if it's unsafe [AN: I think this cuts down
    to something like the number of distinct pushouts, but it's cutting down
    based on the boundary non-injectivity of subcohg—which is not ultimately
    what we care about! Possibly if we modify this idea to use the boundary
    of the RHS of the rewrite, we can make it work...]*)
(* Compute length $
  remove_dups
  $
  remove_dups ∘ merge_sort (rel_preimage fst Pos.lt) ∘ map_partition (partition_quotient block_1 !!!.) <$>
  partitions_joining_wildly_inefficient block_1. *)



(* Compute (bool_decide ((map_partition (partition_quotient block_1 !!!.) block_1) = block_1_quotiented)). *)

End Example1.


Module Example_bell.

Definition graph_X n : CospanHyperGraph positive (N.to_nat n) 0 :=
  mk_cohg
    (mk_hg
      (list_to_map ((λ p, (p, (p, [p], []))) <$> pseq 1 n)) ∅)
      (fun_to_vec (λ p, Pos.of_succ_nat p)) [#].

Definition graph_Z n : CospanHyperGraph positive 0 0 :=
  mk_cohg
    (mk_hg
      (list_to_map ((λ p, (p, (p, [xH], []))) <$> pseq 1 n)) ∅) [#] [#].

(* Succeed Compute
    ltac:(let r := eval vm_compute in (frobenius_graph_rewriting_correctness (graph_X 1) (graph_Z 2)) in
    lazymatch r with
    | (1%nat, true) => idtac
    | ?c => fail "TEST FAILURE: " c
    end). *)


Local Definition i : nat := 1.
Local Definition j : nat := 0.

Local Definition n : nat := 0.
Local Definition m : nat := 0.

Local Definition subcohg : CospanHyperGraph positive i j :=
  graph_X 1.

Local Definition cohg : CospanHyperGraph positive n m :=
  graph_Z 2.

(* Compute frobenius_graph_rewriting_correctness subcohg
  (relabel_graph (Pos.add (xO $ xO (Pos.of_succ_nat (i + j)))) cohg). *)

Local Definition all_contexts := all_frobenius_contexts subcohg cohg.

(* Compute pretty $ all_contexts !! 1. *)

(* Compute opt_weak_graph_iso_partial_test cohg ∘
  make_pushout subcohg <$> all_contexts. *)

Local Open Scope positive_scope.

(* Compute pretty $ frobenius_edge_matchings_extending
  (graph_boundary subcohg) subcohg cohg (∅, ∅).

Compute pretty $ frobenius_graph_matchings subcohg cohg. *)

Local Definition me : Piso :=
  mk_Piso'' {[1 := 1]}.

Local Definition mv : Psurj :=
  Psurj_of_Pmap {[1 := 1]}.


Local Definition true_bnd : Pset := set_map (mv.(Psurj_map) !!!.) (graph_boundary subcohg).



Local Definition g_equiv_classes_exploded_context :=
  exploded_context subcohg cohg me mv true_bnd.

Local Definition g_equiv_classes :=
  map xI <$>
  g_equiv_classes_exploded_context.1.
Local Definition exploded_context :=
  relabel_graph xI
  g_equiv_classes_exploded_context.2.
Local Definition mv' :=
  (* xI <$>  *)
  mv.(Psurj_map).

(* Compute pretty g_equiv_classes.

Compute pretty exploded_context. *)





Local Definition exploded_interfaced_context :=
    mk_cohg exploded_context exploded_context.(inputs)
      (vmap (xO ∘ Pos.of_succ_nat) (vseq 0 (i + j)) +++ exploded_context.(outputs)).

Local Definition subcohg_bnd : list positive := subcohg.(inputs) ++ subcohg.(outputs).

    (* Equivalence classes of interface vertices for _g_ *)
Local Definition interface_equiv_classes : Pmap (list positive) :=
    kimerge_aux pair ((λ i,
      (mv' !!! (subcohg_bnd !!! i), xO (Pos.of_succ_nat i))) <$> seq 0 (i + j)).

    (* Equivalence classes of interface vertices for _f_ *)
Local Definition f_equiv_classes : Pmap blocks :=
    (partition_of_func (λ p,
      let p' := match p with | xO p | xI p => p | xH => xH end in
      subcohg_bnd !!! Nat.pred (Pos.to_nat p'))) <$> interface_equiv_classes.

  (* Now, I'm ASSUMING (TODO: triple-check this) that the f-equivalence class
     of all vertices in exploded_context are always trivial (it sure seems that
     way). So, the g-equivalence classes, themselves further partitioned by f,
     are given by singleton blocks for everything in g_equiv_classes, along
     with the f_equiv_classes *)

Local Definition g_equiv_classes_blocks : Pmap blocks :=
    (λ ps, make_blocks (fmap singleton ps)) <$> g_equiv_classes.

(* Compute pretty g_equiv_classes_blocks. *)

Local Definition f_g_equiv_classes :=
  merge (union_with (λ bl bl', Some (join_partitions bl bl')))
    f_equiv_classes g_equiv_classes_blocks.

(* Compute pretty exploded_interfaced_context.

Compute pretty f_g_equiv_classes. *)

(* Compute pretty $ quotient_maps f_g_equiv_classes.

(* Compute pretty f_g_equiv_classes. *)

Local Definition block_1 : blocks := f_g_equiv_classes !!! 1. *)

Local Definition fully_quotiented_contexts :=
  Eval vm_compute in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

(* Compute frobenius_graph_rewriting_correctness subcohg cohg. *)

(* Compute pretty fully_quotiented_contexts.

Compute pretty (make_pushout subcohg <$> fully_quotiented_contexts).
Compute pretty cohg.

Compute pretty (@opt_weak_graph_iso_partial_test _ eq _ _ _ cohg ∘ make_pushout subcohg <$> fully_quotiented_contexts). *)




(* Compute pretty matching. *)
(*
Compute let '(me, mv, true_bnd) := matching in
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  length $ quotiented_contexts f_g_equiv_classes exploded_interfaced_context.

  (* Next, we get a candidate matching *)

  '(me, mv, true_bnd) ← frobenius_graph_matchings subcohg cohg;
  let '(f_g_equiv_classes, exploded_interfaced_context) :=
    exploded_interfaced_context subcohg cohg me mv true_bnd in
  quotiented_contexts f_g_equiv_classes exploded_interfaced_context.



Local Definition i : nat := 2.
Local Definition j : nat := 2.

Local Definition subcohg : CospanHyperGraph string i j :=
  mk_cohg ∅ [#1; 1] [#2; 2].

Local Definition cohg : CospanHyperGraph string 0 0 :=
  mk_cohg (mk_hg {[ 1 := ("e", [1], [1])]} ∅) [#] [#].


Time Compute frobenius_graph_rewriting_correctness subcohg cohg. *)

End Example_bell.



End PaperExample.
