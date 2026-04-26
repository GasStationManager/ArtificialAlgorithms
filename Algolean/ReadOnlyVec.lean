/-
A read-only vector query type and a `ℕ`-cost model.
Vendored from Algolean.

Original author: Shreyas Srinivas (Apache 2.0).
-/

import Algolean.QueryModel

namespace Algolean

/--
Read-only access to a fixed-length vector: read the element at a given index.
-/
inductive ReadOnlyVec (α : Type) : Type → Type 1 where
  | read {n : Nat} (a : Vector α n) (i : Fin n) : ReadOnlyVec α α

namespace ReadOnlyVec

/-- Cost model: every read costs 1. -/
@[simps]
def natCost {α : Type} : Model (ReadOnlyVec α) ℕ where
  evalQuery
    | .read a i => a[i]
  cost _ := 1

end ReadOnlyVec

end Algolean
