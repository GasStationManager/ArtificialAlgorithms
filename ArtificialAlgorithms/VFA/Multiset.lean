import Mathlib
import ArtificialAlgorithms.VFA.Sort

/-!
# VFA Chapter: Multiset (Insertion Sort with Multisets)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Multiset.html

## Overview
Verifies insertion sort using multisets (bags) as an alternative to permutations.
A multiset is represented as a function from values to their multiplicities.
The chapter proves that permutation-based and multiset-based specifications
of sorting are equivalent.

## Mathlib Mappings
- VFA's function-based `multiset` ↦ translated faithfully (exercises depend on it)
- Mathlib production alternative: `Mathlib.Data.Multiset.Basic` (quotient of lists by permutation)
- VFA `Permutation` ↦ `List.Perm`
-/

namespace VFA.Multiset

open VFA.Sort

-- ============================================
-- Section: Multisets
-- ============================================

/-- Type synonym for values (natural numbers). -/
abbrev value := Nat

/-- A multiset maps each value to its multiplicity (number of occurrences). -/
def multiset := value → Nat

/-- The empty multiset has multiplicity 0 for every value. -/
def empty : multiset :=
  fun _ => 0

/-- Multiset containing exactly one occurrence of `v`. -/
def singleton (v : value) : multiset :=
  fun x => if x = v then 1 else 0

/-- The union of two multisets is their pointwise sum. -/
def union (a b : multiset) : multiset :=
  fun x => a x + b x

-- ============================================
-- Section: Multiset Properties
-- ============================================

/-- VFA Exercise: union_assoc (1 star).
    Multiset union is associative. -/
lemma union_assoc : ∀ a b c : multiset,
    union a (union b c) = union (union a b) c := by
  intro a b c
  funext x
  unfold union
  omega

/-- VFA Exercise: union_comm (1 star).
    Multiset union is commutative. -/
lemma union_comm : ∀ a b : multiset,
    union a b = union b a := by
  intro a b
  funext x
  unfold union
  omega

/-- VFA Exercise: union_swap (2 stars).
    Multisets in a nested union can be swapped. -/
lemma union_swap : ∀ a b c : multiset,
    union a (union b c) = union b (union a c) := by
  intro a b c
  rw [union_assoc, union_assoc]
  congr 1
  exact union_comm a b

-- ============================================
-- Section: Specification of Sorting
-- ============================================

/-- Extract the contents of a list as a multiset. -/
def contents : List value → multiset
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)

@[simp] lemma contents_nil : contents [] = empty := rfl
@[simp] lemma contents_cons (a : value) (bl : List value) :
    contents (a :: bl) = union (singleton a) (contents bl) := rfl

/-- VFA Example: sort preserves contents on a concrete list.
    After `funext`, we reduce the `sort` computation and close with `simp`+`omega`. -/
example : contents (Sort.sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])
    = contents [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] := by
  -- First reduce sort to a concrete list
  have hsort : Sort.sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
      = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by native_decide
  rw [hsort]
  -- Now both sides are contents of concrete lists of the same multiset.
  funext x
  simp only [contents, union, singleton, empty]
  split_ifs <;> omega

/-- A sorting algorithm that preserves contents and produces a sorted list. -/
def is_a_sorting_algorithm' (f : List Nat → List Nat) : Prop :=
  ∀ al, contents al = contents (f al) ∧ sorted (f al)

-- ============================================
-- Section: Verification of Insertion Sort
-- ============================================

/-- VFA Exercise: insert_contents (3 stars).
    Insertion sort's `insert` produces the same contents as prepending. -/
lemma insert_contents : ∀ x l,
    contents (Sort.insert x l) = contents (x :: l) := by
  intro x l
  induction l with
  | nil => rfl
  | cons h t ih =>
    unfold Sort.insert
    by_cases hle : x ≤ h
    · simp only [if_pos hle]
    · simp only [if_neg hle]
      show contents (h :: Sort.insert x t) = contents (x :: h :: t)
      simp only [contents_cons]
      rw [ih]
      exact union_swap (singleton h) (singleton x) (contents t)

/-- VFA Exercise: sort_contents (2 stars).
    Insertion sort preserves contents. -/
theorem sort_contents : ∀ l,
    contents l = contents (Sort.sort l) := by
  intro l
  induction l with
  | nil => rfl
  | cons h t ih =>
    show contents (h :: t) = contents (Sort.sort (h :: t))
    unfold Sort.sort
    rw [insert_contents]
    simp only [contents_cons]
    rw [ih]

/-- VFA Exercise: insertion_sort_correct (1 star).
    Insertion sort is correct w.r.t. the multiset specification. -/
theorem insertion_sort_correct : is_a_sorting_algorithm' Sort.sort :=
  fun al => ⟨sort_contents al, sort_sorted al⟩

-- ============================================
-- Section: Equivalence of Permutation and Multiset Specifications
-- ============================================

-- Forward Direction

/-- VFA Exercise: perm_contents (3 stars).
    If two lists are permutations, they have the same contents. -/
lemma perm_contents : ∀ al bl : List Nat,
    List.Perm al bl → contents al = contents bl := by
  intro al bl h
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [contents_cons]
    rw [ih]
  | swap x y l =>
    -- swap x y l : (y :: x :: l).Perm (x :: y :: l)
    -- Goal: contents (y :: x :: l) = contents (x :: y :: l)
    simp only [contents_cons]
    exact union_swap (singleton y) (singleton x) (contents l)
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

-- ============================================
-- Backward Direction (Advanced)
-- ============================================

/-- Helper: `singleton v v = 1`. -/
@[simp] lemma singleton_self (v : value) : singleton v v = 1 := by
  unfold singleton; simp

/-- Helper: `singleton v x = 0` when `x ≠ v`. -/
@[simp] lemma singleton_other {v x : value} (h : x ≠ v) : singleton v x = 0 := by
  unfold singleton; simp [h]

/-- Helper: unfold union applied to a value. -/
@[simp] lemma union_apply (a b : multiset) (x : value) : union a b x = a x + b x := rfl

/-- Helper: unfold empty applied to a value. -/
@[simp] lemma empty_apply (x : value) : empty x = 0 := rfl

/-- VFA Exercise: contents_nil_inv (2 stars, advanced).
    If the contents of a list maps everything to 0, the list is nil. -/
lemma contents_nil_inv : ∀ l, (∀ x, 0 = contents l x) → l = [] := by
  intro l h
  match l with
  | [] => rfl
  | a :: t =>
    exfalso
    have := h a
    simp only [contents_cons, union_apply, singleton_self] at this
    omega

/-- VFA Exercise: contents_cons_inv (3 stars, advanced).
    If `x` has multiplicity `n+1` in `l`, then `l` splits around an occurrence of `x`. -/
lemma contents_cons_inv : ∀ l x n,
    n + 1 = contents l x →
    ∃ l1 l2, l = l1 ++ x :: l2 ∧ contents (l1 ++ l2) x = n := by
  intro l
  induction l with
  | nil =>
    intro x n h
    simp [contents_nil] at h
  | cons a t ih =>
    intro x n h
    by_cases hax : a = x
    · -- a = x: split here with l1 = [], l2 = t
      subst hax
      refine ⟨[], t, by simp, ?_⟩
      simp [contents_cons] at h ⊢
      omega
    · -- a ≠ x: the occurrence must be deeper in t
      have hh : n + 1 = contents t x := by
        simp [contents_cons, singleton_other (Ne.symm hax)] at h
        omega
      obtain ⟨l1, l2, hl, hc⟩ := ih x n hh
      refine ⟨a :: l1, l2, by simp [hl], ?_⟩
      simp only [List.cons_append, contents_cons, union_apply,
        singleton_other (Ne.symm hax)]
      omega

/-- VFA Exercise: contents_insert_other (2 stars, advanced).
    Inserting `x` into a list doesn't change the count of any other element `y ≠ x`. -/
lemma contents_insert_other : ∀ l1 l2 x y,
    y ≠ x → contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 x y hyx
    simp only [List.nil_append, contents_cons, union_apply, singleton_other hyx]
    omega
  | cons a t ih =>
    intro l2 x y hyx
    simp only [List.cons_append, contents_cons, union_apply]
    rw [ih l2 x y hyx]

/-- VFA Exercise: contents_perm (3 stars, advanced).
    If two lists have the same contents, they are permutations. -/
lemma contents_perm : ∀ al bl,
    contents al = contents bl → List.Perm al bl := by
  intro al
  induction al with
  | nil =>
    intro bl h
    have hbl : bl = [] := by
      apply contents_nil_inv
      intro x
      have := congr_fun h x
      simp only [contents_nil, empty_apply] at this
      omega
    subst hbl
    exact List.Perm.refl _
  | cons a t ih =>
    intro bl h
    -- a has multiplicity ≥ 1 in contents bl
    have ha : contents bl a ≥ 1 := by
      have := congr_fun h a
      simp only [contents_cons, union_apply, singleton_self] at this
      omega
    -- So we can split bl around a
    obtain ⟨l1, l2, hbl, hc⟩ := contents_cons_inv bl a (contents bl a - 1) (by omega)
    -- Now show contents t = contents (l1 ++ l2)
    have ht : contents t = contents (l1 ++ l2) := by
      funext x
      by_cases hax : x = a
      · -- x = a case: use hc to relate the multiplicities
        rw [hax]
        have ha_eq := congr_fun h a
        simp only [contents_cons, union_apply, singleton_self] at ha_eq
        omega
      · -- x ≠ a case: use contents_insert_other
        have hx := congr_fun h x
        simp only [contents_cons, union_apply, singleton_other hax] at hx
        simp only [Nat.zero_add] at hx
        rw [hbl] at hx
        rw [contents_insert_other l1 l2 a x hax] at hx
        omega
    have hperm_t : List.Perm t (l1 ++ l2) := ih (l1 ++ l2) ht
    rw [hbl]
    -- Goal: List.Perm (a :: t) (l1 ++ a :: l2)
    exact (List.Perm.cons a hperm_t).trans List.perm_middle.symm

-- ============================================
-- Section: The Main Theorem
-- ============================================

/-- VFA Exercise: same_contents_iff_perm (1 star).
    Multiset equality and permutation are equivalent. -/
theorem same_contents_iff_perm : ∀ al bl,
    contents al = contents bl ↔ List.Perm al bl :=
  fun al bl => ⟨contents_perm al bl, perm_contents al bl⟩

/-- VFA Exercise: sort_specifications_equivalent (2 stars).
    The permutation-based and multiset-based sorting specifications are equivalent. -/
theorem sort_specifications_equivalent : ∀ f,
    is_a_sorting_algorithm f ↔ is_a_sorting_algorithm' f := by
  intro f
  constructor
  · intro h al
    obtain ⟨hp, hs⟩ := h al
    exact ⟨perm_contents al (f al) hp, hs⟩
  · intro h al
    obtain ⟨hc, hs⟩ := h al
    exact ⟨contents_perm al (f al) hc, hs⟩

end VFA.Multiset
