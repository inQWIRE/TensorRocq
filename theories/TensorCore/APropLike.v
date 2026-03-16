Require Export AProp.

Class APROPlike (R : Type) `{SR : SemiRing R rO rI radd rmul req}
  (A : Type) `{SA : Summable A, EqA : EqDecision A} 
  (D : nat -> nat -> Type) `{EquivD : forall n m, Equiv (D n m),
    EquivalenceD : forall n m, @Equivalence (D n m) equiv} := {
  interpretDiagram {n m} (d : D n m) : @Tensor R n m A;
  interpretDiagram_correct {n m} (d d' : D n m) : 
    interpretDiagram d ≡ interpretDiagram d' ->
    d ≡ d'; 
}.

#[global] Hint Mode APROPlike + - - - - - - - - - + - - : typeclass_instances.

Class DiagramQuote `{APROPlikeD : APROPlike R rO rI radd rmul req A D}
  `{Equiv T, Equivalence T equiv} `{TensT : !TensorLike R A T}
  {n m} (d : D n m) (a : AProp T n m) := {
  diagram_quote : interpretDiagram d ≡ AProp_semantics (TensT:=TensT) a;
}.

#[global] Hint Mode DiagramQuote + - - - - - - - - - - - - -
  - - - - + + + - : typeclass_instances.

Class DiagramDenote `{APROPlikeD : APROPlike R rO rI radd rmul req A D}
  `{Equiv T, Equivalence T equiv} `{TensT : !TensorLike R A T}
  {n m} (d : D n m) (a : AProp T n m) := {
  diagram_denote : interpretDiagram d ≡ AProp_semantics (TensT:=TensT) a;
}.

#[global] Hint Mode DiagramDenote + - - - - - - - - - - - - -
  - - - - + + - + : typeclass_instances.



Lemma APROPlike_convert `{APROPlikeD : APROPlike R rO rI radd rmul req A D}
  `{Equiv T, Equivalence T equiv} `{TensT : !TensorLike R A T}
  {n m} (d d' : D n m) (a a' : AProp T n m) : 
  DiagramQuote d a -> DiagramDenote d' a' ->
  AProp_semantics (TensT:=TensT) a ≡ AProp_semantics a' ->
  d ≡ d'.
Proof.
  intros [<-] [<-].
  apply interpretDiagram_correct.
Qed.




Lemma APROPlike_equiv `{APROPlikeD : APROPlike R rO rI radd rmul req A D}
  `{Equiv T, Equivalence T equiv} `{TensT : !TensorLike R A T}
  {n m} (d d' : D n m) (a a' : AProp T n m) : 
  DiagramQuote d a -> DiagramQuote d' a' ->
  AProp_semantics (TensT:=TensT) a ≡ AProp_semantics a' ->
  d ≡ d'.
Proof.
  intros [<-] [<-].
  apply interpretDiagram_correct.
Qed.




