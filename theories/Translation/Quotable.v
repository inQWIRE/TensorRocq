Require Import stdpp.option stdpp.list.

Class Quotable (A B Ctx : Type) (f : Ctx -> A -> B) := {}.

#[global] Hint Mode Quotable - ! - - : typeclass_instances.



#[export] Instance option_quotable `{Quot : Quotable A B Ctx f} :
  Quotable (option A) (option B) Ctx (λ c, fmap (f c)) := {}.

#[export] Instance prod_quotable `{Quot1 : Quotable A1 B1 Ctx1 f1}
  `{Quot2 : Quotable A2 B2 Ctx2 f2} :
  Quotable (A1 * A2) (B1 * B2) (Ctx1 * Ctx2) (λ c, prod_map (f1 c.1) (f2 c.2))
   := {}.

#[export] Instance sum_quotable `{Quot1 : Quotable A1 B1 Ctx1 f1}
  `{Quot2 : Quotable A2 B2 Ctx2 f2} :
  Quotable (A1 + A2) (B1 + B2) (Ctx1 * Ctx2) (λ c, sum_map (f1 c.1) (f2 c.2))
   := {}.

#[export] Instance list_quotable `{Quot : Quotable A B Ctx f} : 
  Quotable (list A) (list B) Ctx (λ c, fmap (f c)).

