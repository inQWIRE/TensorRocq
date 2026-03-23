Require Export VyZXInterface.

Declare Scope PZX_scope.
Delimit Scope PZX_scope with PZX.
Open Scope PZX_scope.

Inductive PZX (A : Type) : nat -> nat -> Type :=
  | PEmpty : PZX A 0 0
  | PCup  : PZX A 0 2
  | PCap  : PZX A 2 0
  | PSwap : PZX A 2 2
  | PWire : PZX A 1 1
  | PBox  : PZX A 1 1
  | PX_Spider n m (α : A) : PZX A n m
  | PZ_Spider n m (α : A) : PZX A n m
  | PStack {n_0 m_0 n_1 m_1} (zx0 : PZX A n_0 m_0) (zx1 : PZX A n_1 m_1) : 
          PZX A (n_0 + n_1) (m_0 + m_1)
  | PCompose {n m o} (zx0 : PZX A n m) (zx1 : PZX A m o) : PZX A n o.

(* Fixpoint zx2pzx {n m} (zx : ZX n m) : PZX R n m :=
  match zx with 
  | Empty => PEmpty
  | Cup => PCup
  |  *)
