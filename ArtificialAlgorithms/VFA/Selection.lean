import Mathlib
import ArtificialAlgorithms.VFA.Sort
import ArtificialAlgorithms.VFA.Multiset

/-!
# VFA Chapter: Selection (Selection Sort)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html

## Overview
Defines selection sort using a fuel-based approach and proves it correct:
the output is a sorted permutation of the input. Also includes an optional
multiset-based correctness proof.

## Mathlib Mappings
- VFA `sorted` ↦ reused from `VFA.Sort.sorted`
- VFA `is_a_sorting_algorithm` ↦ reused from `VFA.Sort.is_a_sorting_algorithm`
- VFA `Permutation` ↦ `List.Perm`

## Note on termination
The VFA chapter uses a fuel-based approach (`selsort l n`) to handle non-structural
recursion. In production Lean 4, one would use `termination_by l.length` instead.
We translate the fuel-based version faithfully since all exercises depend on it.
-/

namespace VFA.Selection

open VFA.Sort (sorted is_a_sorting_algorithm)
open VFA.Multiset (contents singleton union multiset is_a_sorting_algorithm')

-- ============================================
-- Section: The Selection-Sort Program
-- ============================================

/-- Select the smallest element from `x :: l`, returning `(min, rest)`.
    `select x l = (y, r)` means `y` is the smallest of `x :: l` and
    `r` contains the remaining elements. -/
def select (x : Nat) (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x ≤ h then
      let (j, l') := select x t
      (j, h :: l')
    else
      let (j, l') := select h t
      (j, x :: l')

/-- Fuel-based selection sort. When fuel `n` runs out, returns `[]`. -/
def selsort (l : List Nat) (n : Nat) : List Nat :=
  match l, n with
  | _, 0 => []  -- ran out of fuel
  | [], _ => []
  | x :: r, n' + 1 =>
    let (y, r') := select x r
    y :: selsort r' n'

/-- Selection sort: uses list length as fuel. -/
def selection_sort (l : List Nat) : List Nat :=
  selsort l l.length

-- Examples

example : selsort [3, 1, 4, 1, 5] 3 ≠ [1, 1, 3, 4, 5] := by native_decide

example : selsort [3, 1, 4, 1, 5] 10 = [1, 1, 3, 4, 5] := by native_decide

example : selection_sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
    = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide

-- ============================================
-- Section: Simp lemmas for select and selsort
-- ============================================

@[simp] lemma select_nil (x : Nat) : select x [] = (x, []) := rfl

@[simp] lemma selsort_zero (l : List Nat) : selsort l 0 = [] := by
  simp [selsort]

@[simp] lemma selsort_nil (n : Nat) : selsort [] n = [] := by
  cases n <;> simp [selsort]

-- ============================================
-- Section: Proof of Correctness
-- ============================================

/-- `le_all x xs` means `x` is less than or equal to every element of `xs`. -/
def le_all (x : Nat) (xs : List Nat) : Prop := ∀ y ∈ xs, x ≤ y

-- ============================================
-- Permutation lemmas
-- ============================================

/-- VFA Exercise: select_perm (2 stars).
    `select` returns a permutation of its input. -/
lemma select_perm : ∀ x l y r,
    select x l = (y, r) → List.Perm (x :: l) (y :: r) := by
  intro x l
  -- We need the IH to be general in x, so revert x and do induction on l
  revert x
  induction l with
  | nil =>
    intro x y r h
    simp [select] at h
    obtain ⟨rfl, rfl⟩ := h
    exact List.Perm.refl _
  | cons h t ih =>
    intro x y r hsel
    unfold select at hsel
    by_cases hle : x ≤ h
    · simp only [if_pos hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      -- Goal: (x :: h :: t).Perm (j :: h :: l')
      have ihperm := ih x j l' hsel_eq
      -- ihperm : (x :: t).Perm (j :: l')
      -- Strategy: (x :: h :: t) -> (h :: x :: t) -> (h :: j :: l') -> (j :: h :: l')
      exact ((List.Perm.swap h x t).trans (List.Perm.cons h ihperm)).trans
        (List.Perm.swap h j l').symm
    · simp only [if_neg hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      -- Goal: (x :: h :: t).Perm (j :: x :: l')
      have ihperm := ih h j l' hsel_eq
      -- ihperm : (h :: t).Perm (j :: l')
      -- Strategy: (x :: h :: t) -> (x :: j :: l') -> (j :: x :: l')
      exact ((List.Perm.cons x ihperm).trans (List.Perm.swap x j l').symm)

/-- VFA Exercise: select_rest_length (1 star).
    `select` returns a list of the same length. -/
lemma select_rest_length : ∀ x l y r,
    select x l = (y, r) → l.length = r.length := by
  intro x l y r h
  have hp := select_perm x l y r h
  have := hp.length_eq
  simp at this
  exact this

/-- VFA Exercise: selsort_perm (3 stars).
    If sufficient fuel is provided, `selsort` produces a permutation. -/
lemma selsort_perm : ∀ n l,
    l.length = n → List.Perm l (selsort l n) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact List.Perm.refl _
  | succ n ih =>
    intro l hl
    match hm : l with
    | [] => simp [selsort]
    | x :: r =>
      simp [selsort]
      obtain ⟨y, r', hsel⟩ : ∃ y r', select x r = (y, r') := ⟨_, _, rfl⟩
      rw [hsel]
      -- Goal: (x :: r).Perm (y :: selsort r' n)
      have hlen : r.length = r'.length := select_rest_length x r y r' hsel
      have hpsel := select_perm x r y r' hsel
      have hrlen : r'.length = n := by simp at hl; omega
      have ihperm := ih r' hrlen
      exact hpsel.trans (List.Perm.cons y ihperm)

/-- VFA Exercise: selection_sort_perm (1 star).
    `selection_sort` produces a permutation. -/
lemma selection_sort_perm : ∀ l,
    List.Perm l (selection_sort l) := by
  intro l
  exact selsort_perm l.length l rfl

-- ============================================
-- Ordering lemmas
-- ============================================

/-- VFA Exercise: select_fst_leq (2 stars).
    The first component of `select x _` is <= `x`. -/
lemma select_fst_leq : ∀ al bl x y,
    select x al = (y, bl) → y ≤ x := by
  intro al
  induction al with
  | nil =>
    intro bl x y h
    simp [select] at h
    obtain ⟨rfl, _⟩ := h; omega
  | cons h t ih =>
    intro bl x y hsel
    unfold select at hsel
    by_cases hle : x ≤ h
    · simp only [if_pos hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, _⟩ := hsel
      exact ih l' x j hsel_eq
    · simp only [if_neg hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, _⟩ := hsel
      have := ih l' h j hsel_eq
      omega

/-- VFA Exercise: le_all_le_one (1 star).
    If `y` is <= all elements of `lst`, and `n` is in `lst`, then `y <= n`. -/
lemma le_all_le_one : ∀ lst y n,
    le_all y lst → n ∈ lst → y ≤ n := by
  intro lst y n hall hin
  exact hall n hin

/-- VFA Exercise: select_smallest (2 stars).
    The first component of `select` is <= all elements of the second component. -/
lemma select_smallest : ∀ al bl x y,
    select x al = (y, bl) → le_all y bl := by
  intro al
  induction al with
  | nil =>
    intro bl x y h
    simp [select] at h
    obtain ⟨_, rfl⟩ := h
    intro z hz
    exact absurd hz (List.not_mem_nil)
  | cons h t ih =>
    intro bl x y hsel
    unfold select at hsel
    by_cases hle : x ≤ h
    · simp only [if_pos hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      -- Goal: le_all j (h :: l')
      intro z hz
      cases hz with
      | head => -- z = h
        have := select_fst_leq t l' x j hsel_eq
        omega
      | tail _ hz' => -- z ∈ l'
        exact ih l' x j hsel_eq z hz'
    · simp only [if_neg hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      -- Goal: le_all j (x :: l')
      intro z hz
      cases hz with
      | head => -- z = x
        have := select_fst_leq t l' h j hsel_eq
        omega
      | tail _ hz' => -- z ∈ l'
        exact ih l' h j hsel_eq z hz'

/-- VFA Exercise: select_in (2 stars).
    The element returned by `select` is in the original list. -/
lemma select_in : ∀ al bl x y,
    select x al = (y, bl) → y ∈ x :: al := by
  intro al
  induction al with
  | nil =>
    intro bl x y h
    simp [select] at h
    obtain ⟨rfl, _⟩ := h
    exact List.mem_cons_self
  | cons h t ih =>
    intro bl x y hsel
    unfold select at hsel
    by_cases hle : x ≤ h
    · simp only [if_pos hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, _⟩ := hsel
      have hmem := ih l' x j hsel_eq
      -- j ∈ x :: t, need j ∈ x :: h :: t
      cases hmem with
      | head => exact List.mem_cons_self
      | tail _ hm => exact List.mem_cons_of_mem x (List.mem_cons_of_mem h hm)
    · simp only [if_neg hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, _⟩ := hsel
      have hmem := ih l' h j hsel_eq
      -- j ∈ h :: t, need j ∈ x :: h :: t
      exact List.mem_cons_of_mem x hmem

-- ============================================
-- Sortedness lemmas
-- ============================================

/-- VFA Exercise: cons_of_small_maintains_sort (3 stars).
    Adding a small element to a selection-sorted list maintains sortedness. -/
lemma cons_of_small_maintains_sort : ∀ bl y n,
    n = bl.length →
    le_all y bl →
    sorted (selsort bl n) →
    sorted (y :: selsort bl n) := by
  intro bl y n hn hleall hsorted
  -- Case split on the result of selsort bl n
  generalize hcase : selsort bl n = result at hsorted ⊢
  match result with
  | [] => exact sorted.single y
  | z :: zs =>
    apply sorted.cons
    · -- Need: y ≤ z
      -- z is the head of selsort bl n, which is a permutation of bl
      -- So z ∈ bl, and le_all y bl gives y ≤ z
      have hperm := selsort_perm n bl (by omega)
      rw [hcase] at hperm
      have hz_in_bl : z ∈ bl := hperm.symm.mem_iff.mp List.mem_cons_self
      exact hleall z hz_in_bl
    · exact hsorted

/-- VFA Exercise: selsort_sorted (2 stars).
    `selsort` produces a sorted list when given sufficient fuel. -/
lemma selsort_sorted : ∀ n al,
    al.length = n → sorted (selsort al n) := by
  intro n
  induction n with
  | zero =>
    intro al hal
    have : al = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact sorted.nil
  | succ n ih =>
    intro al hal
    match hm : al with
    | [] => simp; exact sorted.nil
    | x :: r =>
      simp [selsort]
      obtain ⟨y, r', hsel⟩ : ∃ y r', select x r = (y, r') := ⟨_, _, rfl⟩
      rw [hsel]
      -- Goal: sorted (y :: selsort r' n)
      have hrlen : r'.length = n := by
        have := select_rest_length x r y r' hsel
        simp at hal; omega
      have hsmall := select_smallest r r' x y hsel
      apply cons_of_small_maintains_sort r' y n hrlen.symm hsmall
      exact ih r' hrlen

/-- VFA Exercise: selection_sort_sorted (1 star).
    `selection_sort` produces a sorted list. -/
lemma selection_sort_sorted : ∀ al,
    sorted (selection_sort al) := by
  intro al
  exact selsort_sorted al.length al rfl

/-- VFA Exercise: selection_sort_is_correct (1 star).
    `selection_sort` is a correct sorting algorithm. -/
theorem selection_sort_is_correct :
    is_a_sorting_algorithm selection_sort :=
  fun al => ⟨selection_sort_perm al, selection_sort_sorted al⟩

-- ============================================
-- Section: Selection Sort with Multisets (Optional)
-- ============================================

open VFA.Multiset (union_swap contents_cons singleton_self singleton_other
  union_apply empty_apply)

/-- VFA Exercise: select_contents (3 stars, optional).
    `select` preserves multiset contents. -/
lemma select_contents : ∀ al bl x y,
    select x al = (y, bl) →
    union (singleton x) (contents al) = union (singleton y) (contents bl) := by
  intro al
  induction al with
  | nil =>
    intro bl x y h
    simp [select] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons h t ih =>
    intro bl x y hsel
    unfold select at hsel
    by_cases hle : x ≤ h
    · simp only [if_pos hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      have ih_eq := ih l' x j hsel_eq
      -- Goal: union (singleton x) (contents (h :: t))
      --     = union (singleton j) (contents (h :: l'))
      simp only [contents_cons]
      rw [union_swap (singleton x) (singleton h) (contents t)]
      rw [ih_eq]
      rw [union_swap (singleton j) (singleton h) (contents l')]
    · simp only [if_neg hle] at hsel
      obtain ⟨j, l', hsel_eq⟩ : ∃ j l', select h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel_eq] at hsel
      simp at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      have ih_eq := ih l' h j hsel_eq
      -- Goal: union (singleton x) (contents (h :: t))
      --     = union (singleton j) (contents (x :: l'))
      simp only [contents_cons]
      -- LHS: union (singleton x) (union (singleton h) (contents t))
      -- RHS: union (singleton j) (union (singleton x) (contents l'))
      -- ih_eq : union (singleton h) (contents t) = union (singleton j) (contents l')
      -- Subst ih_eq into LHS inner part:
      rw [ih_eq]
      -- LHS now: union (singleton x) (union (singleton j) (contents l'))
      -- RHS: union (singleton j) (union (singleton x) (contents l'))
      exact union_swap (singleton x) (singleton j) (contents l')

/-- VFA Exercise: selection_sort_contents (3 stars, optional).
    `selection_sort` preserves multiset contents. -/
lemma selection_sort_contents : ∀ n l,
    l.length = n →
    contents l = contents (selection_sort l) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rfl
  | succ n ih =>
    intro l hl
    match hm : l with
    | [] => rfl
    | x :: r =>
      -- selection_sort (x :: r) = selsort (x :: r) (x :: r).length
      -- = let (y, r') := select x r; y :: selsort r' ((x :: r).length - 1)
      -- We need: contents (x :: r) = contents (selection_sort (x :: r))
      -- Use perm_contents since selection_sort produces a permutation
      exact VFA.Multiset.perm_contents (x :: r) (selection_sort (x :: r))
        (selection_sort_perm (x :: r))

/-- VFA Exercise: selection_sort_correct' (1 star, optional).
    `selection_sort` is correct w.r.t. the multiset specification. -/
theorem selection_sort_correct' :
    is_a_sorting_algorithm' selection_sort :=
  fun al => ⟨selection_sort_contents al.length al rfl, selection_sort_sorted al⟩

end VFA.Selection
