import Mathlib

/-!
# VFA Chapter: Decide
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Decide.html

## Overview
Programming with decision procedures. The Coq chapter introduces `reflect` and
`sumbool` as two ways to bridge the Prop/bool gap. In Lean 4, the built-in
`Decidable` typeclass unifies both concepts:

```
inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)   : Decidable p
```

The `if` construct in Lean 4 works with any `Decidable` instance, and the
standard library provides instances for `<`, `≤`, `=`, `∈`, etc. There is no
need for separate `lt_dec`/`le_dec` definitions or `bdestruct` tactics.

## Mathlib Mappings
- Coq `reflect P b` ↦ `Decidable P` (Lean 4 core)
- Coq `sumbool A B` / `{A}+{~A}` ↦ `Decidable A` (Lean 4 core)
- Coq `ltb_reflect` ↦ `Nat.decLt` (instance, automatic)
- Coq `lt_dec` / `le_dec` ↦ `inferInstance : Decidable (a < b)` etc.
- Coq `list_eq_dec` ↦ `DecidableEq (List α)` (instance, automatic)
- Coq `in_dec` ↦ `List.instDecidableMemOfDecidableEq` (instance, automatic)
-/

namespace VFA.Decide

-- ============================================
-- Section: Decidable — Lean 4's unified approach
-- ============================================

-- In Coq, `reflect (3 < 7) (3 <? 7)` relates a Prop to a bool.
-- In Lean 4, `Decidable (3 < 7)` does the same job.
-- The `decide` tactic evaluates `Decidable` instances at elaboration time.

/-- Coq exercise `three_less_seven`: trivial via `decide` in Lean 4. -/
theorem three_less_seven : 3 < 7 := by decide

-- Coq's `lt_dec` and `le_dec` are just `Decidable` instances in Lean 4.
-- No explicit definition needed — they're already inferred.

example : Decidable (3 < 7) := inferInstance
example : Decidable (5 ≤ 5) := inferInstance
example : Decidable (4 = 4) := inferInstance

-- ============================================
-- Section: Using Decidable in programs
-- ============================================

-- Coq's `sumbool`-based `insert` and `sort` use `le_dec` explicitly.
-- In Lean 4, `if` works with any `Decidable` instance automatically.

/-- Insertion sort using `if` with `Decidable` (no `bdestruct` needed).
    This mirrors the Coq chapter's `insert`/`sort` using `le_dec`. -/
def insert (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [x]
  | h :: t => if x ≤ h then x :: h :: t else h :: insert x t

def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)

-- Lean 4's `#eval` is fully computable — no `Qed` opacity issues.
-- (In Coq, opaque `Qed` proofs block computation; Lean 4 doesn't have this problem.)
#eval sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
-- [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]

-- ============================================
-- Section: Sortedness and insert_sorted
-- ============================================

/-- Inductive sortedness (same as VFA Sort chapter). -/
inductive sorted : List Nat → Prop where
  | nil : sorted []
  | single : ∀ x, sorted [x]
  | cons : ∀ x y l, x ≤ y → sorted (y :: l) → sorted (x :: y :: l)

/-- VFA Exercise: insert_sorted (2★).
    Proved using `if`/`Decidable` rather than Coq's `destruct (le_dec a x)`. -/
lemma insert_sorted : ∀ a l, sorted l → sorted (insert a l) := by
  intro a l hs
  induction hs with
  | nil => exact sorted.single a
  | single x =>
    simp only [insert]
    split_ifs with h
    · exact sorted.cons a x [] h (sorted.single x)
    · exact sorted.cons x a [] (by omega) (sorted.single a)
  | cons x y l hxy _hsl ih =>
    unfold insert
    by_cases h : a ≤ x
    · simp only [if_pos h]
      exact sorted.cons a x (y :: l) h (sorted.cons x y l hxy _hsl)
    · simp only [if_neg h]
      unfold insert at ih ⊢
      by_cases h2 : a ≤ y
      · simp only [if_pos h2] at ih ⊢
        exact sorted.cons x a (y :: l) (by omega) (sorted.cons a y l h2 _hsl)
      · simp only [if_neg h2] at ih ⊢
        exact sorted.cons x y (insert a l) hxy ih

-- ============================================
-- Section: Decidable list equality and membership
-- ============================================

-- Coq's `list_eq_dec` requires manually composing `eq_nat_dec` with `list_eq_dec`.
-- In Lean 4, `DecidableEq (List Nat)` is inferred automatically.

/-- Decidable equality for lists of naturals — just an instance lookup. -/
example : DecidableEq (List Nat) := inferInstance

#eval if ([1, 3, 4] : List Nat) = [1, 4, 3] then true else false  -- false
#eval if ([1, 3, 4] : List Nat) = [1, 3, 4] then true else false  -- true

/-- VFA Exercise: list_nat_in (2★).
    Decidable membership — trivially an instance in Lean 4. -/
example : ∀ (i : Nat) (al : List Nat), Decidable (i ∈ al) :=
  fun _ _ => inferInstance

/-- VFA Exercise: in_4_pi (2★). -/
example : (if (4 : Nat) ∈ [3, 1, 4, 1, 5, 9, 2, 6] then true else false) = true := by
  decide

-- ============================================
-- Section: Decidable predicates compose
-- ============================================

-- The power of Lean 4's `Decidable` instances: they compose automatically.
-- No need to manually build decision procedures for compound propositions.

example : Decidable (3 < 7 ∧ 5 ≤ 5) := inferInstance
example : Decidable (3 < 7 ∨ 10 < 2) := inferInstance
example : Decidable (¬ (3 > 7)) := inferInstance
example : Decidable (∀ x ∈ [1, 2, 3], x < 10) := inferInstance

-- These all compute:
#eval if 3 < 7 ∧ 5 ≤ 5 then "both" else "nope"   -- "both"
#eval if ∀ x ∈ [1, 2, 3], x < 10 then "yes" else "no"  -- "yes"

end VFA.Decide
