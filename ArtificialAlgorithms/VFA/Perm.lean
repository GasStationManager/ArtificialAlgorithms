import Mathlib

/-!
# VFA Chapter: Perm
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html

## Overview
Introduces techniques for reasoning about comparisons and permutations of lists,
serving as foundations for verifying sorting and searching algorithms.

## Mathlib Mappings
- VFA `Permutation` ↦ `List.Perm`
- VFA `reflect` / `bdestruct` ↦ Lean's `Decidable` typeclass + `split_ifs` / `omega`
- VFA `Forall` ↦ `∀ x ∈ l, P x`
- VFA `lia` ↦ `omega`
-/

namespace VFA.Perm

-- ============================================
-- Section: Linear Arithmetic (omega in Lean)
-- ============================================

-- VFA: In Coq, `lia` handles linear integer arithmetic.
-- In Lean 4, `omega` serves the same purpose for Nat and Int.

/-- Nat subtraction truncates at zero: `0 - 3 = 0`, so `¬ (0 > 0)`. -/
theorem truncated_subtraction : ¬ (∀ k : Nat, k > k - 3) := by
  intro h; exact absurd (h 0) (by omega)

theorem lia_example1 : ∀ i j k : Nat, i < j → ¬ (k - 3 ≤ j) → k > i := by
  intros; omega

/-- `omega` handles opaque function applications as uninterpreted terms. -/
theorem lia_example3 : ∀ (f : Nat → Nat → Nat) a b x y,
    f x y > a * b → f x y + 3 ≥ a * b := by
  intros; omega

-- ============================================
-- Section: Swapping
-- ============================================

/-- Swap the first two elements if they are out of order. -/
def maybeSwap (al : List Nat) : List Nat :=
  match al with
  | a :: b :: ar => if a > b then b :: a :: ar else a :: b :: ar
  | _ => al

#eval maybeSwap [1, 2, 3]  -- [1, 2, 3]
#eval maybeSwap [3, 2, 1]  -- [2, 3, 1]

example : maybeSwap [1, 2, 3] = [1, 2, 3] := by native_decide
example : maybeSwap [3, 2, 1] = [2, 3, 1] := by native_decide

-- VFA: Theorem maybe_swap_idempotent
-- In Coq this required `bdestruct`. In Lean, `split_ifs` + `omega` handles it.
theorem maybeSwap_idempotent : ∀ al, maybeSwap (maybeSwap al) = maybeSwap al := by
  intro al
  match al with
  | [] => rfl
  | [_] => rfl
  | a :: b :: ar =>
    simp only [maybeSwap]
    by_cases h1 : a > b
    · have h2 : ¬(b > a) := by omega
      simp [h1, h2]
    · simp [h1]

-- ============================================
-- Section: Permutations
-- ============================================

-- VFA `Permutation` ↦ `List.Perm`
-- Constructors: .nil, .cons, .swap, .trans

/-- VFA: Example butterfly.
    Demonstrates rearranging elements using permutation lemmas. -/
theorem butterfly : ∀ b u t e r f l y : Nat,
    List.Perm ([b, u, t, t, e, r] ++ [f, l, y]) ([f, l, u, t, t, e, r] ++ [b, y]) := by
  intros b u t e r f l y
  rw [List.perm_iff_count]
  intro a
  simp [List.count_cons, List.count_nil]
  ring

/-- VFA Exercise: permut_example (3 stars).
    `5 :: 6 :: a ++ b` is a permutation of `(5 :: b) ++ (6 :: a)`. -/
theorem permut_example : ∀ (a b : List Nat),
    List.Perm (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])) := by
  intros a b
  simp only [List.append_nil]
  -- Goal: List.Perm (5 :: 6 :: a ++ b) (5 :: (b ++ 6 :: a))
  apply List.Perm.cons
  -- Goal: List.Perm (6 :: a ++ b) (b ++ 6 :: a)
  -- 6 :: (a ++ b) is definitionally (6 :: a) ++ b
  exact List.perm_append_comm

/-- VFA Exercise: not_a_permutation (2 stars).
    `[1, 1]` is not a permutation of `[1, 2]` because counts differ. -/
theorem not_a_permutation : ¬ List.Perm ([1, 1] : List Nat) [1, 2] := by
  intro h
  have := h.count_eq 2
  simp [List.count_nil] at this

-- ============================================
-- Section: Correctness of maybe_swap
-- ============================================

/-- `maybe_swap` is a permutation of its input. -/
theorem maybeSwap_perm : ∀ al, List.Perm al (maybeSwap al) := by
  intro al
  match al with
  | [] => exact List.Perm.refl _
  | [_] => exact List.Perm.refl _
  | a :: b :: ar =>
    simp only [maybeSwap]
    split_ifs with h
    · exact List.Perm.swap b a ar
    · exact List.Perm.refl _

/-- The first element is ≤ the second (trivially true for short lists). -/
def firstLeSecond (al : List Nat) : Prop :=
  match al with
  | a :: b :: _ => a ≤ b
  | _ => True

/-- `maybe_swap` produces a permutation where the first two elements are ordered. -/
theorem maybeSwap_correct : ∀ al,
    List.Perm al (maybeSwap al) ∧ firstLeSecond (maybeSwap al) := by
  intro al
  exact ⟨maybeSwap_perm al, by
    match al with
    | [] => trivial
    | [_] => trivial
    | a :: b :: _ =>
      simp only [maybeSwap, firstLeSecond]
      split_ifs with h <;> omega⟩

/-- Bundled version (code_with_proof pattern): returns the swapped list
    together with proofs of correctness. -/
def verifiedMaybeSwap (al : List Nat) :
    {al' : List Nat // List.Perm al al' ∧ firstLeSecond al'} :=
  ⟨maybeSwap al, maybeSwap_correct al⟩

-- ============================================
-- Section: Forall and Permutations
-- ============================================

/-- VFA Exercise: Forall_perm (3 stars).
    A property that holds for all elements of a list is preserved by permutation.
    In Lean, this follows from the fact that permutations preserve membership. -/
theorem forall_perm {A : Type} (f : A → Prop) (al bl : List A)
    (h : List.Perm al bl) (hf : ∀ x ∈ al, f x) : ∀ x ∈ bl, f x := by
  intro x hx
  exact hf x (h.symm.mem_iff.mp hx)

end VFA.Perm
