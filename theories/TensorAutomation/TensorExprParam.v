(* TODO: TensorExpr, but with generic arguments (through some framework?)
  and parameters to functions (maybe params want [DPmap]?). Param types
  indexed by [P : Ty -> Type].
  The big goal is parametric sizes with this, specifically for ZX. 
  TODO: Details of this!!! *)

(* To flesh out:
(i) What is a type of arguments? How do we match? / specify it? 
  What context do they get? Should that be explicitly restricted,
  or otherwise ensure we can know the used variables? Or are we
  cool not?
  - I think our type of arguments should come equipped with a
    function to 'size', telling us what type of function
    we need to apply it to. (i.e., each type maybe has a 
    custom notion of [V_n_args] and [Vapplys], where 'size' 
    there means the list of types of arguments; for ZX it may 
    be just the total length (or even just always [list]!!!))
  - We need an equivalence relation on types of arguments, or
    we just can't do anything
(ii) If I think through the type of arguments for ZX (to begin
  with, [gmultiset var] sounds about right - or just list up
  to permutation tbh. Strictly, [gmap var bool] with product
  given by [xor] should be right — but jury's out on whether
  we want to do that cancellation at the level of argument
  or lemma. Lemma might be better so we don't stop people 
  ever seeing it... but maybe [xor] later on? No, that lives
  at the graph level), think about what notion of size this 
  gives. How do I get size out of this?
  - I think we may need variables to have a notion of size / type. 
    For otherwise how can we possibly talk about the size
    we get when we match some of the arguments? Maybe the 
    abstract tensor itself has a record of the size as a
    parameter? 
    NO OK The argument itself marks the size! So we don't
    just have [gmap var positive], but [gmap var (nat * positive)],
    indicating the size with the nat. Then the overall size is also
    a multiset, in this case [gmultiset nat]. 
    Ah, there may be a small problem if we're not careful — we might
    need size to actually be a partial map from type, and we're back
    to typed variables (is that such a bad thing?). 
(iii) Separate things for parsing vs processing? I'm thinking having

*)

(* TODO: [varmap], a product of three [Pmap]s *)