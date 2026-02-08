import Mathlib

/-!
# VFA Chapter: Maps (Total and Partial Maps)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Maps.html

## Overview
Defines total maps (functions from `Nat` to `A` with a default value) and partial maps
(total maps with `Option A` values). Proves fundamental properties: empty lookup,
update-lookup interaction, shadowing, identity update, and update permutation.
These maps are foundational infrastructure for the SearchTree chapter.

## Mathlib Mappings
- VFA `total_map A` ↦ `Nat → A` (plain function type, no Mathlib equivalent)
- VFA `partial_map A` ↦ `Nat → Option A` (via `total_map (Option A)`)
- VFA `functional_extensionality` ↦ `funext` (built-in Lean 4)
- VFA `Nat.eqb` decidability ↦ `DecidableEq Nat` (built-in Lean 4)
- Mathlib production alternative: `Finmap`, `Finsupp`, `HashMap`
-/

namespace VFA.Maps

-- ============================================
-- Section: Total Maps
-- ============================================

/-- A total map over type `A` is a function from `Nat` to `A`.
    Lookup is just function application. -/
def TotalMap (A : Type) : Type := Nat → A

/-- The empty total map returns the default value `v` for all keys. -/
def t_empty {A : Type} (v : A) : TotalMap A :=
  fun _ => v

/-- Update a total map at key `x` with value `v`.
    Uses `DecidableEq Nat` for the key comparison. -/
def t_update {A : Type} (m : TotalMap A) (x : Nat) (v : A) : TotalMap A :=
  fun x' => if x = x' then v else m x'

/-- Concrete example map: maps 3 ↦ true, everything else ↦ false. -/
def examplemap : TotalMap Bool :=
  t_update (t_update (t_empty false) 1 false) 3 true

-- Verify the example map computes correctly (replaces the four update_example proofs)
#eval examplemap 0  -- false
#eval examplemap 1  -- false
#eval examplemap 2  -- false
#eval examplemap 3  -- true

-- ============================================
-- Section: Total Map Lemmas
-- ============================================

/-- VFA Exercise: t_apply_empty (1 star).
    The empty map returns its default element for all keys. -/
theorem t_apply_empty : ∀ (A : Type) (x : Nat) (v : A), t_empty v x = v := by
  intros
  rfl

/-- VFA Exercise: t_update_eq (1 star).
    Updating at key `x` then looking up `x` returns the new value. -/
theorem t_update_eq : ∀ (A : Type) (m : TotalMap A) (x : Nat) (v : A),
    t_update m x v x = v := by
  intros
  unfold t_update
  simp

/-- VFA Exercise: t_update_neq (1 star).
    Updating at `x1`, looking up different `x2`, returns the original value. -/
theorem t_update_neq : ∀ (A : Type) (v : A) (x1 x2 : Nat) (m : TotalMap A),
    x1 ≠ x2 → t_update m x1 v x2 = m x2 := by
  intro A v x1 x2 m h
  unfold t_update
  simp [h]

/-- VFA Exercise: t_update_shadow (1 star).
    Double update at the same key keeps only the last value. -/
theorem t_update_shadow : ∀ (A : Type) (m : TotalMap A) (v1 v2 : A) (x : Nat),
    t_update (t_update m x v1) x v2 = t_update m x v2 := by
  intro A m v1 v2 x
  funext x'
  unfold t_update
  by_cases h : x = x' <;> simp [h]

/-- VFA Exercise: t_update_same (1 star).
    Updating with the current value is the identity. -/
theorem t_update_same : ∀ (A : Type) (x : Nat) (m : TotalMap A),
    t_update m x (m x) = m := by
  intro A x m
  funext x'
  unfold t_update
  by_cases h : x = x'
  · simp [h]
  · simp [h]

/-- VFA Exercise: t_update_permute (1 star).
    Swapping order of updates at distinct keys gives the same map. -/
theorem t_update_permute : ∀ (A : Type) (v1 v2 : A) (x1 x2 : Nat) (m : TotalMap A),
    x2 ≠ x1 →
    t_update (t_update m x2 v2) x1 v1 = t_update (t_update m x1 v1) x2 v2 := by
  intro A v1 v2 x1 x2 m h
  funext x'
  unfold t_update
  by_cases h1 : x1 = x'
  · by_cases h2 : x2 = x'
    · exfalso; exact h (h2.trans h1.symm)
    · simp [h1, h2]
  · by_cases h2 : x2 = x'
    · simp [h1, h2]
    · simp [h1, h2]

-- ============================================
-- Section: Partial Maps
-- ============================================

/-- A partial map is a total map with `Option A` values, defaulting to `none`. -/
def PartialMap (A : Type) : Type := TotalMap (Option A)

/-- The empty partial map returns `none` for all keys. -/
def p_empty {A : Type} : PartialMap A :=
  t_empty none

/-- Update a partial map at key `x` with value `v` (wrapped in `some`). -/
def p_update {A : Type} (m : PartialMap A) (x : Nat) (v : A) : PartialMap A :=
  t_update m x (some v)

-- ============================================
-- Section: Partial Map Lemmas
-- ============================================

/-- The empty partial map returns `none` for all keys. -/
theorem apply_empty : ∀ (A : Type) (x : Nat), @p_empty A x = none := by
  intro A x
  unfold p_empty
  rw [t_apply_empty]

/-- Updating at key `x` then looking up `x` returns `some v`. -/
theorem update_eq : ∀ (A : Type) (m : PartialMap A) (x : Nat) (v : A),
    p_update m x v x = some v := by
  intro A m x v
  unfold p_update
  rw [t_update_eq]

/-- Updating at `x2`, looking up different `x1`, returns the original value. -/
theorem update_neq : ∀ (A : Type) (v : A) (x1 x2 : Nat) (m : PartialMap A),
    x2 ≠ x1 → p_update m x2 v x1 = m x1 := by
  intro A v x1 x2 m h
  unfold p_update
  exact t_update_neq (Option A) (some v) x2 x1 m h

/-- Double update at the same key keeps only the last value. -/
theorem update_shadow : ∀ (A : Type) (m : PartialMap A) (v1 v2 : A) (x : Nat),
    p_update (p_update m x v1) x v2 = p_update m x v2 := by
  intro A m v1 v2 x
  unfold p_update
  rw [t_update_shadow]

/-- Updating with the current value is the identity (requires `m x = some v`). -/
theorem update_same : ∀ (A : Type) (v : A) (x : Nat) (m : PartialMap A),
    m x = some v → p_update m x v = m := by
  intro A v x m h
  unfold p_update
  rw [← h]
  exact t_update_same (Option A) x m

/-- Swapping order of updates at distinct keys gives the same map. -/
theorem update_permute : ∀ (A : Type) (v1 v2 : A) (x1 x2 : Nat) (m : PartialMap A),
    x2 ≠ x1 →
    p_update (p_update m x2 v2) x1 v1 = p_update (p_update m x1 v1) x2 v2 := by
  intro A v1 v2 x1 x2 m h
  unfold p_update
  exact t_update_permute (Option A) (some v1) (some v2) x1 x2 m h

end VFA.Maps
