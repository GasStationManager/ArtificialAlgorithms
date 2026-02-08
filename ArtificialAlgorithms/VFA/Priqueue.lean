import Mathlib

/-!
# VFA Chapter: Priqueue
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Priqueue.html

## Overview
Priority queues with a simple unsorted-list implementation. Defines the
`Priqueue` interface (class) and proves that `List Nat` satisfies it using
a `selectMax` helper that finds and removes the maximum element.

## Mathlib Mappings
- VFA `Permutation` ↦ `List.Perm` (Mathlib)
- VFA `Forall` ↦ `List.Forall` / `∀ x ∈ l, P x`
- VFA `select` (max) ↦ fresh `selectMax` (mirrors Selection chapter's min-select)
- VFA `Module Type PRIQUEUE` ↦ `class Priqueue`
- VFA `Module List_Priqueue` ↦ `instance : Priqueue (List Nat)`
-/

namespace VFA.Priqueue

set_option linter.dupNamespace false

-- ============================================
-- Section: Priority Queue Interface
-- ============================================

/-- Abstract interface for a priority queue with natural-number keys.
    Operations: `empty`, `insert`, `deleteMax`, `merge`.
    Correctness is specified via a representation invariant `priq` and
    an abstraction relation `Abs` to `List Nat`. -/
class Priqueue (PQ : Type) where
  empty : PQ
  insert : Nat → PQ → PQ
  deleteMax : PQ → Option (Nat × PQ)
  merge : PQ → PQ → PQ
  priq : PQ → Prop
  Abs : PQ → List Nat → Prop
  can_relate : ∀ p, priq p → ∃ al, Abs p al
  abs_perm : ∀ p al bl, priq p → Abs p al → Abs p bl → List.Perm al bl
  empty_priq : priq empty
  empty_relate : Abs empty []
  insert_priq : ∀ k p, priq p → priq (insert k p)
  insert_relate : ∀ p al k, priq p → Abs p al → Abs (insert k p) (k :: al)
  delete_max_None_relate : ∀ p, priq p → (Abs p [] ↔ deleteMax p = none)
  delete_max_Some_priq : ∀ p q k, priq p → deleteMax p = some (k, q) → priq q
  delete_max_Some_relate : ∀ p q k pl ql, priq p → Abs p pl →
    deleteMax p = some (k, q) → Abs q ql →
    List.Perm pl (k :: ql) ∧ List.Forall (· ≤ k) ql
  merge_priq : ∀ p q, priq p → priq q → priq (merge p q)
  merge_relate : ∀ p q pl ql al, priq p → priq q →
    Abs p pl → Abs q ql → Abs (merge p q) al → List.Perm al (pl ++ ql)

-- ============================================
-- Section: selectMax (Max-Selection Helper)
-- ============================================

/-- Select the maximum from `x :: l`, returning `(max, rest)`.
    Mirrors Selection.select but uses `≥` instead of `≤`. -/
def selectMax (x : Nat) (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x ≥ h then
      let (j, l') := selectMax x t
      (j, h :: l')
    else
      let (j, l') := selectMax h t
      (j, x :: l')

/-- `selectMax` returns a permutation of its input. -/
lemma selectMax_perm (x : Nat) (l : List Nat) :
    let (j, r) := selectMax x l
    List.Perm (x :: l) (j :: r) := by
  revert x
  induction l with
  | nil => intro x; simp [selectMax]
  | cons h t ih =>
    intro x
    unfold selectMax
    by_cases hge : x ≥ h
    · simp only [if_pos hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]
      have := ih x; rw [hsel] at this
      -- this : List.Perm (x :: t) (j :: l')
      -- Goal: List.Perm (x :: h :: t) (j :: h :: l')
      exact ((List.Perm.swap h x t).trans (List.Perm.cons h this)).trans
        (List.Perm.swap h j l').symm
    · simp only [if_neg hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]
      have := ih h; rw [hsel] at this
      -- this : List.Perm (h :: t) (j :: l')
      -- Goal: List.Perm (x :: h :: t) (j :: x :: l')
      exact (List.Perm.cons x this).trans (List.Perm.swap x j l').symm

/-- The selected element is ≥ the original candidate. -/
lemma selectMax_fst_ge (x : Nat) (l : List Nat) :
    (selectMax x l).1 ≥ x := by
  revert x
  induction l with
  | nil => intro x; simp [selectMax]
  | cons h t ih =>
    intro x
    unfold selectMax
    by_cases hge : x ≥ h
    · simp only [if_pos hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]; simp
      have := ih x; rw [hsel] at this; simp at this
      exact this
    · simp only [if_neg hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]; simp
      have := ih h; rw [hsel] at this; simp at this
      omega

/-- The selected element is ≥ all elements in the returned list. -/
lemma selectMax_biggest (x : Nat) (l : List Nat) :
    let (j, r) := selectMax x l
    ∀ y ∈ r, y ≤ j := by
  revert x
  induction l with
  | nil => intro x; simp [selectMax]
  | cons h t ih =>
    intro x
    unfold selectMax
    by_cases hge : x ≥ h
    · simp only [if_pos hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax x t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]
      intro y hy
      cases hy with
      | head => -- y = h
        have := selectMax_fst_ge x t; rw [hsel] at this; simp at this
        omega
      | tail _ hy' => -- y ∈ l'
        have := ih x; rw [hsel] at this
        exact this y hy'
    · simp only [if_neg hge]
      obtain ⟨j, l', hsel⟩ : ∃ j l', selectMax h t = (j, l') := ⟨_, _, rfl⟩
      rw [hsel]
      intro y hy
      cases hy with
      | head => -- y = x
        have := selectMax_fst_ge h t; rw [hsel] at this; simp at this
        omega
      | tail _ hy' => -- y ∈ l'
        have := ih h; rw [hsel] at this
        exact this y hy'

-- ============================================
-- Section: List Priority Queue Implementation
-- ============================================

/-- The list-based priority queue: unsorted list of natural numbers. -/
abbrev ListPQ := List Nat

instance : Priqueue ListPQ where
  empty := []
  insert k p := k :: p
  deleteMax p :=
    match p with
    | [] => none
    | i :: p' => some (selectMax i p')
  merge p q := p ++ q
  priq _ := True
  Abs p al := p = al

  can_relate := fun p _ => ⟨p, rfl⟩

  abs_perm := fun _ _ _ _ hab1 hab2 => by
    subst hab1; subst hab2; exact List.Perm.refl _

  empty_priq := trivial
  empty_relate := rfl

  insert_priq := fun _ _ _ => trivial

  insert_relate := fun _ _ _ _ hab => by
    subst hab; rfl

  delete_max_None_relate := fun p _ => by
    constructor
    · intro h; subst h; simp
    · intro h; cases p with
      | nil => rfl
      | cons _ _ => simp at h

  delete_max_Some_priq := fun _ _ _ _ _ => trivial

  delete_max_Some_relate := fun p q k pl ql _ habs_p hsome habs_q => by
    subst habs_p; subst habs_q
    cases p with
    | nil => simp at hsome
    | cons i p' =>
      have hsel : selectMax i p' = (k, q) := by simpa using hsome
      constructor
      · have hp := selectMax_perm i p'; rw [hsel] at hp; exact hp
      · have hb := selectMax_biggest i p'; rw [hsel] at hb
        exact List.forall_iff_forall_mem.mpr hb

  merge_priq := fun _ _ _ _ => trivial

  merge_relate := fun _ _ _ _ _ _ _ hab_p hab_q hab_m => by
    subst hab_p; subst hab_q; subst hab_m
    exact List.Perm.refl _

end VFA.Priqueue
