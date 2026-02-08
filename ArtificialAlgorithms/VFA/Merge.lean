import Mathlib
import ArtificialAlgorithms.VFA.Sort

/-!
# VFA Chapter: Merge (Merge Sort)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Merge.html

## Overview
Defines merge sort on lists of natural numbers and proves it correct: the output
is a sorted permutation of the input. Includes two-step list induction, the split
and merge helper functions, and full correctness proofs.

## Mathlib Mappings
- VFA `sorted` ↦ reused from `VFA.Sort.sorted`
- VFA `is_a_sorting_algorithm` ↦ reused from `VFA.Sort.is_a_sorting_algorithm`
- VFA `Permutation` ↦ `List.Perm`
-/

namespace VFA.Merge

open VFA.Sort (sorted is_a_sorting_algorithm)

-- ============================================
-- Section: Split and its properties
-- ============================================

/-- Two-step list induction principle.
    Handles cases `[]`, `[a]`, and `a :: b :: l` (with IH on `l`). -/
@[elab_as_elim]
theorem list_ind2 {P : List α → Prop}
    (hnil : P [])
    (hone : ∀ a, P [a])
    (hcons2 : ∀ a b l, P l → P (a :: b :: l))
    (l : List α) : P l := by
  match l with
  | [] => exact hnil
  | [a] => exact hone a
  | a :: b :: rest => exact hcons2 a b rest (list_ind2 hnil hone hcons2 rest)

/-- Split a list by alternating elements into two sublists. Polymorphic. -/
def split {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x1 :: x2 :: l' =>
    let (l1, l2) := split l'
    (x1 :: l1, x2 :: l2)

#eval split [1, 2, 3, 4, 5]  -- ([1, 3, 5], [2, 4])

/-- `split` does not increase length (weak version). -/
lemma split_len {α : Type} : ∀ (l : List α) (l1 l2 : List α),
    split l = (l1, l2) →
    l1.length ≤ l.length ∧ l2.length ≤ l.length := by
  intro l
  induction l using list_ind2 with
  | hnil =>
    intro l1 l2 h; simp [split] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | hone a =>
    intro l1 l2 h; simp [split] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | hcons2 a b l ih =>
    intro l1 l2 h
    unfold split at h
    obtain ⟨l1', l2', hsp⟩ : ∃ l1' l2', split l = (l1', l2') := ⟨_, _, rfl⟩
    rw [hsp] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have ⟨h1, h2⟩ := ih l1' l2' hsp
    simp; omega

/-- `split` on a list of length ≥ 2 produces strictly shorter sublists. -/
lemma split_len_lt {α : Type} : ∀ (a b : α) (rest l1 l2 : List α),
    split (a :: b :: rest) = (l1, l2) →
    l1.length < (a :: b :: rest).length ∧ l2.length < (a :: b :: rest).length := by
  intro a b rest l1 l2 h
  unfold split at h
  obtain ⟨l1', l2', hsp⟩ : ∃ l1' l2', split rest = (l1', l2') := ⟨_, _, rfl⟩
  rw [hsp] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
  have ⟨h1, h2⟩ := split_len rest l1' l2' hsp
  simp; omega

/-- VFA Exercise: split_perm (3 stars).
    Splitting preserves permutation: `l` is a permutation of `l1 ++ l2`. -/
lemma split_perm {α : Type} : ∀ (l l1 l2 : List α),
    split l = (l1, l2) → List.Perm l (l1 ++ l2) := by
  intro l
  induction l using list_ind2 with
  | hnil =>
    intro l1 l2 h; simp [split] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | hone a =>
    intro l1 l2 h; simp [split] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | hcons2 a b l ih =>
    intro l1 l2 h
    unfold split at h
    obtain ⟨l1', l2', hsp⟩ : ∃ l1' l2', split l = (l1', l2') := ⟨_, _, rfl⟩
    rw [hsp] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
    have ihp := ih l1' l2' hsp
    -- Goal: (a :: b :: l).Perm ((a :: l1') ++ (b :: l2'))
    -- i.e. (a :: b :: l).Perm (a :: l1' ++ b :: l2')
    -- From IH: l.Perm (l1' ++ l2')
    -- Need: (a :: b :: l).Perm (a :: l1' ++ b :: l2')
    -- Step: a :: b :: l → a :: b :: (l1' ++ l2') → a :: (l1' ++ b :: l2')
    simp only [List.cons_append]
    exact (List.Perm.cons a (List.Perm.cons b ihp)).trans
      (List.Perm.cons a (List.perm_middle.symm))

-- ============================================
-- Section: Defining Merge
-- ============================================

/-- Merge two sorted lists into a sorted list.
    Uses well-founded recursion on the combined lengths. -/
def merge : List Nat → List Nat → List Nat
  | [], l2 => l2
  | l1, [] => l1
  | a1 :: l1', a2 :: l2' =>
    if a1 ≤ a2 then a1 :: merge l1' (a2 :: l2')
    else a2 :: merge (a1 :: l1') l2'
termination_by l1 l2 => l1.length + l2.length

#eval merge [1, 3, 5] [2, 4, 6]  -- [1, 2, 3, 4, 5, 6]

/-- Sanity check: merge with ≤ comparison at the head. -/
lemma merge2 : ∀ (x1 x2 : Nat) r1 r2,
    x1 ≤ x2 →
    merge (x1 :: r1) (x2 :: r2) = x1 :: merge r1 (x2 :: r2) := by
  intro x1 x2 r1 r2 h
  simp [merge, h]

/-- Base case: merging with empty left list is identity. -/
@[simp] lemma merge_nil_l : ∀ l, merge [] l = l := by
  intro l; simp [merge]

/-- Base case: merging with empty right list is identity. -/
@[simp] lemma merge_nil_r : ∀ l, merge l [] = l := by
  intro l; cases l <;> simp [merge]

-- ============================================
-- Section: Defining Mergesort
-- ============================================

/-- Helper for mergesort termination: split on a list of length ≥ 2
    produces a first component strictly shorter. -/
lemma split_len_fst_lt {α : Type} (a b : α) (rest : List α) :
    (split (a :: b :: rest)).1.length < (a :: b :: rest).length := by
  have h := split_len_lt a b rest (split (a :: b :: rest)).1 (split (a :: b :: rest)).2 rfl
  exact h.1

/-- Helper for mergesort termination: split on a list of length ≥ 2
    produces a second component strictly shorter. -/
lemma split_len_snd_lt {α : Type} (a b : α) (rest : List α) :
    (split (a :: b :: rest)).2.length < (a :: b :: rest).length := by
  have h := split_len_lt a b rest (split (a :: b :: rest)).1 (split (a :: b :: rest)).2 rfl
  exact h.2

/-- Merge sort on lists of natural numbers. -/
def mergesort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | a :: b :: rest =>
    merge (mergesort (split (a :: b :: rest)).1) (mergesort (split (a :: b :: rest)).2)
termination_by l => l.length
decreasing_by
  · exact split_len_fst_lt a b rest
  · exact split_len_snd_lt a b rest

#eval! mergesort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
-- [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]

-- ============================================
-- Section: Correctness -- Sortedness
-- ============================================

/-- VFA Exercise: sorted_merge1 (2 stars).
    Prepending a small element to a sorted merge result is sorted. -/
lemma sorted_merge1 : ∀ x x1 l1 x2 l2,
    x ≤ x1 → x ≤ x2 →
    sorted (merge (x1 :: l1) (x2 :: l2)) →
    sorted (x :: merge (x1 :: l1) (x2 :: l2)) := by
  intro x x1 l1 x2 l2 h1 h2 hs
  unfold merge at hs ⊢
  by_cases hle : x1 ≤ x2
  · simp only [if_pos hle] at hs ⊢
    exact sorted.cons x x1 _ h1 hs
  · simp only [if_neg hle] at hs ⊢
    exact sorted.cons x x2 _ h2 hs

/-- VFA Exercise: sorted_merge (4 stars).
    Merge of two sorted lists is sorted. Requires nested induction. -/
lemma sorted_merge : ∀ l1, sorted l1 →
    ∀ l2, sorted l2 →
    sorted (merge l1 l2) := by
  intro l1
  induction l1 with
  | nil => intro hs1 l2 hs2; simp; exact hs2
  | cons x1 r1 ih1 =>
    intro hs1 l2
    induction l2 with
    | nil => intro hs2; simp; exact hs1
    | cons x2 r2 ih2 =>
      intro hs2
      unfold merge
      by_cases hle : x1 ≤ x2
      · simp only [if_pos hle]
        -- Goal: sorted (x1 :: merge r1 (x2 :: r2))
        -- Need sorted (merge r1 (x2 :: r2)) first
        have hsr1 : sorted r1 := by
          cases hs1 with
          | single _ => exact sorted.nil
          | cons _ _ _ _ htl => exact htl
        have hsm := ih1 hsr1 (x2 :: r2) hs2
        -- Now build sorted (x1 :: merge r1 (x2 :: r2))
        -- Need to case split on r1
        match r1 with
        | [] =>
          simp
          exact sorted.cons x1 x2 r2 hle hs2
        | y1 :: r1' =>
          apply sorted_merge1 x1 y1 r1' x2 r2
          · cases hs1 with
            | cons _ _ _ hxy htl => exact hxy
          · exact hle
          · exact hsm
      · simp only [if_neg hle]
        -- Goal: sorted (x2 :: merge (x1 :: r1) r2)
        have hsr2 : sorted r2 := by
          cases hs2 with
          | single _ => exact sorted.nil
          | cons _ _ _ _ htl => exact htl
        have hsm := ih2 hsr2
        -- Need to case split on r2
        match r2 with
        | [] =>
          simp
          exact sorted.cons x2 x1 r1 (by omega) hs1
        | y2 :: r2' =>
          apply sorted_merge1 x2 x1 r1 y2 r2'
          · omega
          · cases hs2 with
            | cons _ _ _ hxy htl => exact hxy
          · exact hsm

/-- VFA Exercise: mergesort_sorts (2 stars).
    Mergesort produces a sorted list. -/
lemma mergesort_sorts_aux : ∀ n (l : List Nat), l.length ≤ n → sorted (mergesort l) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [mergesort]; exact sorted.nil
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp [mergesort]; exact sorted.nil
    | [x] => simp [mergesort]; exact sorted.single x
    | a :: b :: rest =>
      unfold mergesort
      have hfst := split_len_fst_lt a b rest
      have hsnd := split_len_snd_lt a b rest
      have hs1 := ih (split (a :: b :: rest)).1 (by omega)
      have hs2 := ih (split (a :: b :: rest)).2 (by omega)
      exact sorted_merge _ hs1 _ hs2

lemma mergesort_sorts : ∀ l, sorted (mergesort l) := by
  intro l; exact mergesort_sorts_aux l.length l (le_refl _)

-- ============================================
-- Section: Correctness -- Permutation
-- ============================================

/-- VFA Exercise: merge_perm (3 stars, advanced).
    Merge is a permutation of the concatenation. -/
lemma merge_perm : ∀ (l1 l2 : List Nat),
    List.Perm (l1 ++ l2) (merge l1 l2) := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a1 l1' ih1 =>
    intro l2
    induction l2 with
    | nil => simp
    | cons a2 l2' ih2 =>
      unfold merge
      by_cases hle : a1 ≤ a2
      · simp only [if_pos hle]
        -- Goal: ((a1 :: l1') ++ (a2 :: l2')).Perm (a1 :: merge l1' (a2 :: l2'))
        -- LHS = a1 :: l1' ++ a2 :: l2'
        -- RHS = a1 :: merge l1' (a2 :: l2')
        -- By IH: (l1' ++ a2 :: l2').Perm (merge l1' (a2 :: l2'))
        simp only [List.cons_append]
        exact List.Perm.cons a1 (ih1 (a2 :: l2'))
      · simp only [if_neg hle]
        -- Goal: ((a1 :: l1') ++ (a2 :: l2')).Perm (a2 :: merge (a1 :: l1') l2')
        -- LHS = a1 :: l1' ++ a2 :: l2'
        -- Need to move a2 to the front
        -- Strategy: (a1 :: l1') ++ (a2 :: l2')
        --         = a1 :: (l1' ++ (a2 :: l2'))
        --         ~  a1 :: a2 :: (l1' ++ l2')          (by perm_middle)
        --         ~  a2 :: a1 :: (l1' ++ l2')          (by swap)
        --         ~  a2 :: ((a1 :: l1') ++ l2')         (by assoc)
        --         ~  a2 :: merge (a1 :: l1') l2'        (by ih2)
        simp only [List.cons_append]
        -- (a1 :: (l1' ++ a2 :: l2')).Perm (a2 :: merge (a1 :: l1') l2')
        -- a1 :: (l1' ++ a2 :: l2') ~ a2 :: (a1 :: l1' ++ l2') ~ a2 :: merge (a1::l1') l2'
        have step1 : List.Perm (a1 :: (l1' ++ a2 :: l2')) (a1 :: a2 :: (l1' ++ l2')) :=
          List.Perm.cons a1 List.perm_middle
        have step2 : List.Perm (a1 :: a2 :: (l1' ++ l2')) (a2 :: a1 :: (l1' ++ l2')) :=
          List.Perm.swap a2 a1 _
        -- a2 :: a1 :: (l1' ++ l2') = a2 :: ((a1 :: l1') ++ l2')
        have step3 : (a2 :: a1 :: (l1' ++ l2')) = (a2 :: ((a1 :: l1') ++ l2')) := by
          simp [List.cons_append]
        have step4 : List.Perm (a2 :: ((a1 :: l1') ++ l2')) (a2 :: merge (a1 :: l1') l2') :=
          List.Perm.cons a2 ih2
        exact step1.trans (step2.trans (step3 ▸ step4))

/-- VFA Exercise: mergesort_perm (3 stars, advanced).
    Mergesort produces a permutation of its input. -/
lemma mergesort_perm_aux : ∀ n (l : List Nat), l.length ≤ n → List.Perm l (mergesort l) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [mergesort]
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp [mergesort]
    | [x] => simp [mergesort]
    | a :: b :: rest =>
      unfold mergesort
      have hfst := split_len_fst_lt a b rest
      have hsnd := split_len_snd_lt a b rest
      -- l ~ split.1 ++ split.2 (by split_perm)
      have hsp := split_perm (a :: b :: rest) (split (a :: b :: rest)).1
          (split (a :: b :: rest)).2 rfl
      -- split.1 ~ mergesort split.1 (by IH)
      have hp1 := ih (split (a :: b :: rest)).1 (by omega)
      -- split.2 ~ mergesort split.2 (by IH)
      have hp2 := ih (split (a :: b :: rest)).2 (by omega)
      -- split.1 ++ split.2 ~ mergesort split.1 ++ mergesort split.2 (by append_perm)
      have happ := hp1.append hp2
      -- mergesort split.1 ++ mergesort split.2 ~ merge (mergesort split.1) (mergesort split.2)
      have hmerge := merge_perm (mergesort (split (a :: b :: rest)).1)
          (mergesort (split (a :: b :: rest)).2)
      exact hsp.trans (happ.trans hmerge)

lemma mergesort_perm : ∀ l, List.Perm l (mergesort l) := by
  intro l; exact mergesort_perm_aux l.length l (le_refl _)

/-- Top-level correctness: mergesort is a correct sorting algorithm. -/
theorem mergesort_correct : is_a_sorting_algorithm mergesort :=
  fun al => ⟨mergesort_perm al, mergesort_sorts al⟩

-- ============================================
-- Section: Bundled version (code_with_proof pattern)
-- ============================================

/-- Bundled mergesort: returns the sorted list together with proofs. -/
def verifiedMergesort (l : List Nat) :
    {l' : List Nat // List.Perm l l' ∧ sorted l'} :=
  ⟨mergesort l, mergesort_perm l, mergesort_sorts l⟩

end VFA.Merge
