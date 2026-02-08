import Mathlib

/-!
# VFA Chapter: Sort (Insertion Sort)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html

## Overview
Defines insertion sort and proves it correct: the output is a sorted permutation
of the input. Also explores alternative sortedness specifications and proves their
equivalence.

## Mathlib Mappings
- VFA `sorted` (inductive) ↦ translated faithfully (exercises depend on it)
- VFA `Permutation` ↦ `List.Perm`
- Mathlib equivalent of VFA's `sorted`: `List.Sorted (· ≤ ·)` or `List.Chain' (· ≤ ·)`
-/

namespace VFA.Sort

-- ============================================
-- Section: The Insertion-Sort Program
-- ============================================

/-- Insert `i` into its sorted position in list `l`.
    Precondition: `l` is sorted. -/
def insert (i : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [i]
  | h :: t => if i ≤ h then i :: h :: t else h :: insert i t

/-- Insertion sort: repeatedly insert each element into a sorted accumulator. -/
def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)

#eval sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
-- [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]

example : sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
    = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide

-- ============================================
-- Section: Specification of Correctness
-- ============================================

/-- Inductive definition of sortedness (VFA's version).
    - The empty list is sorted.
    - Any single-element list is sorted.
    - For two adjacent elements, the first must be ≤ the second. -/
inductive sorted : List Nat → Prop where
  | nil : sorted []
  | single : ∀ x, sorted [x]
  | cons : ∀ x y l, x ≤ y → sorted (y :: l) → sorted (x :: y :: l)

/-- List indexing (equivalent to Coq's `nth_error`). -/
def nthError : List Nat → Nat → Option Nat
  | [], _ => none
  | h :: _, 0 => some h
  | _ :: t, n + 1 => nthError t n

/-- `nthError` agrees with Lean's built-in `GetElem?` bracket notation.
    We use `nthError` in proofs because `GetElem?` is opaque to `intro`/`unfold`/`simp`,
    but they compute the same thing. -/
theorem nthError_eq_getElem? (l : List Nat) (i : Nat) : nthError l i = l[i]? := by
  induction l generalizing i with
  | nil => simp [nthError]
  | cons h t ih =>
    cases i with
    | zero => simp [nthError]
    | succ n => simp [nthError, ih]

/-- Alternative sortedness via indexing: for any i < j in range,
    the element at i ≤ element at j. -/
def sorted' (al : List Nat) : Prop :=
  ∀ i j iv jv,
    i < j →
    nthError al i = some iv →
    nthError al j = some jv →
    iv ≤ jv

/-- A correct sorting algorithm produces a sorted permutation of its input. -/
def is_a_sorting_algorithm (f : List Nat → List Nat) : Prop :=
  ∀ al, List.Perm al (f al) ∧ sorted (f al)

-- ============================================
-- Section: Proof of Correctness
-- ============================================

/-- VFA Exercise: insert_sorted (3 stars).
    Inserting into a sorted list preserves sortedness. -/
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

/-- VFA Exercise: sort_sorted (2 stars).
    Insertion sort produces a sorted list. -/
theorem sort_sorted : ∀ l, sorted (sort l) := by
  intro l
  induction l with
  | nil => exact sorted.nil
  | cons h t ih => exact insert_sorted h (sort t) ih

/-- VFA Exercise: insert_perm (3 stars).
    Inserting an element produces a permutation. -/
lemma insert_perm : ∀ x l, List.Perm (x :: l) (insert x l) := by
  intro x l
  induction l with
  | nil => exact List.Perm.refl _
  | cons h t ih =>
    simp only [insert]
    split_ifs with hle
    · exact List.Perm.refl _
    · -- Goal: (x :: h :: t).Perm (h :: insert x t)
      -- Step 1: swap x and h
      -- Step 2: cons h over ih
      exact (List.Perm.swap h x t).trans (List.Perm.cons h ih)

/-- VFA Exercise: sort_perm (3 stars).
    Insertion sort produces a permutation of its input. -/
theorem sort_perm : ∀ l, List.Perm l (sort l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons h t ih =>
    exact (List.Perm.cons h ih).trans (insert_perm h (sort t))

/-- VFA Exercise: insertion_sort_correct (1 star). -/
theorem insertion_sort_correct : is_a_sorting_algorithm sort :=
  fun al => ⟨sort_perm al, sort_sorted al⟩

-- ============================================
-- Section: Validating the Specification
-- ============================================

/-- VFA Exercise: sorted_sorted' (4 stars, advanced).
    The inductive `sorted` implies the index-based `sorted'`. -/
lemma sorted_sorted' : ∀ al, sorted al → sorted' al := by
  intro al hs
  induction hs with
  | nil =>
    intro i j iv jv _ hi _
    simp [nthError] at hi
  | single x =>
    intro i j iv jv hij hi hj
    match i, j with
    | 0, 0 => omega
    | 0, j + 1 => simp [nthError] at hj
    | i + 1, _ => simp [nthError] at hi
  | cons x y l hxy _hyl ih =>
    intro i j iv jv hij hi hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 =>
      simp [nthError] at hi hj; subst hi; subst hj; exact hxy
    | 0, j + 2 =>
      simp [nthError] at hi hj; subst hi
      have := ih 0 (j + 1) y jv (by omega) rfl hj
      omega
    | i + 1, j + 1 =>
      simp [nthError] at hi hj
      exact ih i j iv jv (by omega) hi hj

/-- VFA Exercise: sorted'_sorted (3 stars, advanced).
    The index-based `sorted'` implies the inductive `sorted`. -/
lemma sorted'_sorted : ∀ al, sorted' al → sorted al := by
  intro al hs
  match al with
  | [] => exact sorted.nil
  | [_] => exact sorted.single _
  | a :: b :: t =>
    apply sorted.cons
    · exact hs 0 1 a b (by omega) rfl rfl
    · apply sorted'_sorted
      intro i j iv jv hij hi hj
      exact hs (i + 1) (j + 1) iv jv (by omega)
        (by simp [nthError]; exact hi) (by simp [nthError]; exact hj)

-- ============================================
-- Section: Bundled version (code_with_proof pattern)
-- ============================================

/-- Bundled insertion sort: returns the sorted list together with proofs
    that it is sorted and a permutation of the input. -/
def verifiedSort (l : List Nat) :
    {l' : List Nat // List.Perm l l' ∧ sorted l'} :=
  ⟨sort l, sort_perm l, sort_sorted l⟩

end VFA.Sort
