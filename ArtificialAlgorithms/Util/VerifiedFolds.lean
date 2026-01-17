import Mathlib

namespace RMP
namespace Coding

/-!
# Verified Folds

Reusable components for certified folds over lists and arrays.

## Overview

This module provides infrastructure for writing fold operations that maintain
and prove invariants as they process elements. Two main patterns are supported:

1. **List folds with self-tracking accumulators** (`ListFoldAcc`): The accumulator
   tracks which elements it has seen, building up a proof that relates to the
   original list via permutation.

2. **Array folds with index-tracking accumulators** (`ArrayFold`, `ArrMinAcc`):
   The accumulator tracks how many elements have been processed, with proofs
   that the invariant holds for all indices below the current position.

## Example

See `ListMinAcc` for a list minimum example and `ArrMinAcc` / `findMinArr` for
an array minimum example.
-/

/-- A generic accumulator for certified list folds.

The accumulator bundles:
- `seen`: the list of elements processed so far (in reverse order for `foldl`)
- `val`: the current accumulated value
- `property`: a proof that some property `P` holds between `val` and `seen`

After folding over a list `xs` with initial accumulator having `seen = init.seen`,
the final `seen` field will be `xs.reverse ++ init.seen`. Use a permutation
argument to relate this back to the original list. -/
structure ListFoldAcc (α β : Type*) (P : β → List α → Prop) where
  seen : List α
  val : β
  property : P val seen

namespace ListFoldAcc

variable {α β : Type*} {P : β → List α → Prop}

/-- Extend the accumulator with a new element.

Given a step function and a proof that stepping preserves the property
(when prepending the new element to `seen`), this produces a new accumulator
with the element added to `seen`. -/
def extend (step : β → α → β)
    (h_step : ∀ acc x seen, P acc seen → P (step acc x) (x :: seen))
    (acc : ListFoldAcc α β P) (x : α) : ListFoldAcc α β P :=
  ⟨x :: acc.seen, step acc.val x, h_step acc.val x acc.seen acc.property⟩

/-- After folding over `xs`, the `seen` field equals `xs.reverse ++ init.seen`.

This is the key lemma for relating the accumulator's tracked elements back to
the original list. Combined with `List.Perm.mem_iff`, this allows transferring
properties proved about `seen` to the original list. -/
theorem foldl_seen (step : β → α → β)
    (h_step : ∀ acc x seen, P acc seen → P (step acc x) (x :: seen))
    (xs : List α) (init : ListFoldAcc α β P) :
    (xs.foldl (extend step h_step) init).seen = xs.reverse ++ init.seen := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl_cons, extend, ih, List.reverse_cons, List.append_assoc]

/-- Run a certified fold over a non-empty list, returning the result with
a permutation proof relating `seen` to the original list.

This is the main entry point for users. Given:
- A non-empty list `x :: xs`
- A singleton constructor for the first element
- A step function and proof that it preserves the property

Returns the final accumulator along with a proof that `acc.seen` is a
permutation of the original list. Use `perm.mem_iff` to transfer membership
properties. -/
def run (step : β → α → β)
    (h_step : ∀ acc x seen, P acc seen → P (step acc x) (x :: seen))
    (x : α) (xs : List α)
    (singleton : (y : α) → ListFoldAcc α β P)
    (h_singleton : ∀ y, (singleton y).seen = [y]) :
    {acc : ListFoldAcc α β P // acc.seen.Perm (x :: xs)} :=
  let init := singleton x
  let acc := xs.foldl (extend step h_step) init
  have h_seen : acc.seen = xs.reverse ++ [x] := by
    rw [foldl_seen step h_step xs init, h_singleton]
  have h_perm : acc.seen.Perm (x :: xs) := by
    rw [h_seen]
    have h1 : (xs.reverse ++ [x]).Perm ([x] ++ xs.reverse) := List.perm_append_comm
    have h2 : ([x] ++ xs.reverse).Perm ([x] ++ xs) :=
      List.Perm.append_left [x] (List.reverse_perm xs)
    exact h1.trans h2
  ⟨acc, h_perm⟩

end ListFoldAcc

/-! ### Example: List Minimum with Self-Tracking Accumulator

`ListMinAcc` demonstrates using `ListFoldAcc` to find the minimum of a list.
The key insight is that `foldl` builds `seen` in reverse order, so we use
a permutation argument to relate `seen` back to the original list. -/

/-- Accumulator for finding the minimum of a list.

The property states that `val` is both a member of `seen` and is ≤ all
elements of `seen`. -/
abbrev ListMinAcc := ListFoldAcc Int Int (fun val seen => val ∈ seen ∧ ∀ x ∈ seen, val ≤ x)

namespace ListMinAcc

/-- Create an accumulator from a single element. -/
def singleton (x : Int) : ListMinAcc :=
  ⟨[x], x, List.mem_singleton_self x, fun y hy => by simp_all⟩

/-- The singleton's seen list is just the element. -/
theorem singleton_seen (x : Int) : (singleton x).seen = [x] := rfl

/-- The step function: take the minimum of the accumulator and new element. -/
def step (acc : Int) (x : Int) : Int := min acc x

/-- Proof that `step` preserves the minimum property. -/
theorem step_preserves : ∀ acc x seen,
    (acc ∈ seen ∧ ∀ y ∈ seen, acc ≤ y) →
    (step acc x ∈ x :: seen ∧ ∀ y ∈ x :: seen, step acc x ≤ y) := by
  intro acc x seen ⟨h_mem, h_min⟩
  simp only [step, min_def]
  split_ifs with h
  · -- case: acc ≤ x, so min acc x = acc
    constructor
    · exact List.mem_cons_of_mem x h_mem
    · intro y hy
      cases List.mem_cons.mp hy with
      | inl heq => subst heq; exact h
      | inr hmem => exact h_min y hmem
  · -- case: x < acc, so min acc x = x
    constructor
    · simp only [List.mem_cons]; left; trivial
    · intro y hy
      cases List.mem_cons.mp hy with
      | inl heq => simp [heq]
      | inr hmem =>
        have := h_min y hmem
        omega

end ListMinAcc

/-- Find the minimum element of a non-empty list, with proofs of membership
and minimality.

This demonstrates the list accumulator pattern using `ListFoldAcc.run`:
1. Provide singleton constructor, step function, and preservation proof
2. `run` handles the fold and permutation automatically
3. Transfer properties using `perm.mem_iff` -/
def findMinList (l : List Int) (h : l ≠ []) :
    {y : Int // y ∈ l ∧ ∀ x ∈ l, y ≤ x} :=
  match l with
  | [] => absurd rfl h
  | x :: xs =>
    let ⟨acc, h_perm⟩ := ListFoldAcc.run
      ListMinAcc.step ListMinAcc.step_preserves x xs
      ListMinAcc.singleton ListMinAcc.singleton_seen
    ⟨acc.val,
     h_perm.mem_iff.mp acc.property.1,
     fun z hz => acc.property.2 z (h_perm.mem_iff.mpr hz)⟩

/-! ### Generic Array Fold Utilities

These functions support the pattern of iterating over an array with an
accumulator that tracks how many elements have been processed via an
`upTo` field. The `complete` function iterates until all elements are
processed, and `complete_upTo_eq` proves that the final `upTo` equals
the array size. -/

namespace ArrayFold

/-- Iterate an `extend` function until all array elements are processed.

Given:
- An array `a`
- A function `upTo : β → Nat` extracting the current index from the accumulator
- An `extend` function that processes one more element
- A proof that `extend` increments `upTo` by 1

This function repeatedly calls `extend` until `upTo acc = a.size`. -/
def complete {α β : Type*} (a : Array α) (upTo : β → Nat)
    (extend : (acc : β) → (h : upTo acc < a.size) → β)
    (upTo_extend : ∀ acc h, upTo (extend acc h) = upTo acc + 1)
    (acc : β) : β :=
  if h : upTo acc < a.size then
    complete a upTo extend upTo_extend (extend acc h)
  else
    acc
termination_by a.size - upTo acc
decreasing_by rw [upTo_extend]; omega

/-- After `complete` finishes, `upTo` equals the array size.

This theorem is essential for proving that the final accumulator's invariant
covers all array elements: if your invariant says "property holds for indices
< upTo", then after `complete` it holds for all indices < a.size. -/
theorem complete_upTo_eq {α β : Type*} (a : Array α) (upTo : β → Nat)
    (extend : (acc : β) → (h : upTo acc < a.size) → β)
    (upTo_extend : ∀ acc h, upTo (extend acc h) = upTo acc + 1)
    (acc : β) (h_bound : upTo acc ≤ a.size) :
    upTo (complete a upTo extend upTo_extend acc) = a.size := by
  rw [complete]
  by_cases h : upTo acc < a.size
  · have h_bound' : upTo (extend acc h) ≤ a.size := by
      have : upTo acc + 1 ≤ a.size := Nat.succ_le_iff.mpr h
      simpa [upTo_extend] using this
    simpa [h, upTo_extend] using
      (complete_upTo_eq (a := a) (upTo := upTo) (extend := extend)
        (upTo_extend := upTo_extend) (acc := extend acc h) h_bound')
  · have h_ge : a.size ≤ upTo acc := Nat.le_of_not_gt h
    simp [Nat.le_antisymm h_bound h_ge]
termination_by a.size - upTo acc
decreasing_by rw [upTo_extend]; omega

end ArrayFold

/-- A generic accumulator for certified array folds.

The accumulator bundles:
- `upTo`: number of elements processed so far (indices 0..upTo-1)
- `val`: the current accumulated value
- `bound`: proof that `upTo ≤ a.size`
- `property`: a proof that property `P` holds for `val` given we've processed `upTo` elements

The property `P` typically has the form "val satisfies some condition for all
indices < upTo". After `complete`, `upTo = a.size`, so the property holds for
all elements. -/
structure ArrayFoldAcc {α : Type*} (a : Array α) (β : Type*) (P : β → Nat → Prop) where
  upTo : Nat
  val : β
  bound : upTo ≤ a.size
  property : P val upTo

namespace ArrayFoldAcc

variable {α β : Type*} {a : Array α} {P : β → Nat → Prop}

/-- Extend the accumulator by processing one more element.

Given a step function and proof that stepping preserves the property
(extending from index `upTo` to `upTo + 1`), produce a new accumulator. -/
def extend
    (step : β → (i : Nat) → (hi : i < a.size) → β)
    (h_step : ∀ val i (hi : i < a.size), P val i → P (step val i hi) (i + 1))
    (acc : ArrayFoldAcc a β P) (h : acc.upTo < a.size) : ArrayFoldAcc a β P :=
  ⟨acc.upTo + 1, step acc.val acc.upTo h, Nat.succ_le_iff.mpr h,
   h_step acc.val acc.upTo h acc.property⟩

theorem upTo_extend
    (step : β → (i : Nat) → (hi : i < a.size) → β)
    (h_step : ∀ val i (hi : i < a.size), P val i → P (step val i hi) (i + 1))
    (acc : ArrayFoldAcc a β P) (h : acc.upTo < a.size) :
    (extend step h_step acc h).upTo = acc.upTo + 1 := rfl

/-- Process all remaining elements of the array. -/
def complete
    (step : β → (i : Nat) → (hi : i < a.size) → β)
    (h_step : ∀ val i (hi : i < a.size), P val i → P (step val i hi) (i + 1))
    (acc : ArrayFoldAcc a β P) : ArrayFoldAcc a β P :=
  ArrayFold.complete a (fun acc => acc.upTo)
    (fun acc h => extend step h_step acc h)
    (fun acc h => upTo_extend step h_step acc h)
    acc

/-- After `complete`, the accumulator has processed all elements. -/
theorem complete_upTo_eq
    (step : β → (i : Nat) → (hi : i < a.size) → β)
    (h_step : ∀ val i (hi : i < a.size), P val i → P (step val i hi) (i + 1))
    (acc : ArrayFoldAcc a β P) : (complete step h_step acc).upTo = a.size :=
  ArrayFold.complete_upTo_eq a (fun acc => acc.upTo)
    (fun acc h => extend step h_step acc h)
    (fun acc h => upTo_extend step h_step acc h)
    acc acc.bound

/-- Run a certified fold over a non-empty array.

This is the main entry point for users. Given:
- A singleton constructor for the first element
- A step function and proof that it preserves the property

Returns the final accumulator with `upTo = a.size`, so the property
holds for all elements. -/
def run
    (singleton : (h : 0 < a.size) → ArrayFoldAcc a β P)
    (step : β → (i : Nat) → (hi : i < a.size) → β)
    (h_step : ∀ val i (hi : i < a.size), P val i → P (step val i hi) (i + 1))
    (h : 0 < a.size) :
    {acc : ArrayFoldAcc a β P // acc.upTo = a.size} :=
  let acc := complete step h_step (singleton h)
  ⟨acc, complete_upTo_eq step h_step (singleton h)⟩

end ArrayFoldAcc

/-! ### Example: Array Minimum with Self-Tracking Accumulator

`ArrMinAcc` demonstrates the index-tracking pattern for arrays. The accumulator
tracks how many elements have been processed (`upTo`) and maintains the invariant
that `val` is the minimum of `a[0..upTo)`. -/

/-- Accumulator for finding the minimum of an array, tracking progress via `upTo`.

This is an example of the self-tracking accumulator pattern for arrays:
- `upTo`: number of elements processed so far
- `val`: current minimum value
- `bound`: proof that `upTo ≤ a.size`
- `nonempty`: proof that we've seen at least one element
- `isMin`: proof that `val` is ≤ all elements in `a[0..upTo)` -/
structure ArrMinAcc (a : Array Int) where
  upTo : Nat
  val : Int
  bound : upTo ≤ a.size
  nonempty : 0 < upTo
  isMin : ∀ j : Nat, j < upTo → (hj : j < a.size) → val ≤ a[j]

namespace ArrMinAcc

/-- Create an accumulator from the first element of a non-empty array. -/
def singleton (a : Array Int) (h : 0 < a.size) : ArrMinAcc a :=
  ⟨1, a[0], Nat.succ_le_iff.mpr h, Nat.succ_pos 0, fun j hj _ => by
    have : j = 0 := Nat.lt_one_iff.mp hj
    simp [this]⟩

/-- Extend the accumulator by processing one more element at index `upTo`. -/
def extend (acc : ArrMinAcc a) (h : acc.upTo < a.size) : ArrMinAcc a :=
  let x := a[acc.upTo]
  if hle : x ≤ acc.val then
    ⟨acc.upTo + 1, x, Nat.succ_le_iff.mpr h, Nat.succ_pos _, fun j hj hjs => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact le_trans hle (acc.isMin j hj' hjs)
      · subst hj'; rfl⟩
  else
    ⟨acc.upTo + 1, acc.val, Nat.succ_le_iff.mpr h, Nat.succ_pos _, fun j hj hjs => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact acc.isMin j hj' hjs
      · subst hj'
        exact le_of_lt (lt_of_not_ge hle)⟩

theorem upTo_extend (acc : ArrMinAcc a) (h : acc.upTo < a.size) :
    (extend acc h).upTo = acc.upTo + 1 := by
  by_cases hle : a[acc.upTo] ≤ acc.val
  · simp [extend, hle]
  · simp [extend, hle]

/-- Process all remaining elements of the array. -/
def complete (acc : ArrMinAcc a) : ArrMinAcc a :=
  ArrayFold.complete a ArrMinAcc.upTo
    (fun acc h => extend acc h)
    (fun acc h => upTo_extend (acc := acc) h)
    acc

/-- After `complete`, the accumulator has processed all elements. -/
theorem complete_upTo_eq (acc : ArrMinAcc a) : (acc.complete).upTo = a.size := by
  apply ArrayFold.complete_upTo_eq (a := a) (upTo := ArrMinAcc.upTo)
    (extend := fun acc h => extend acc h)
    (upTo_extend := fun acc h => upTo_extend (acc := acc) h)
    (acc := acc)
    (h_bound := acc.bound)

end ArrMinAcc

/-- Find the minimum element of a non-empty array, with a proof that the
result is ≤ all elements.

This demonstrates the self-tracking accumulator pattern:
1. Create a singleton accumulator from the first element
2. Call `complete` to process all remaining elements
3. Extract the value with its proof -/
def findMinArr (a : Array Int) (h : 0 < a.size) :
    {y : Int // ∀ j : Nat, (hj : j < a.size) → y ≤ a[j]} := by
  let acc := (ArrMinAcc.singleton a h).complete
  have h_upTo : acc.upTo = a.size := ArrMinAcc.complete_upTo_eq (ArrMinAcc.singleton a h)
  refine ⟨acc.val, ?_⟩
  intro j hj
  have hj' : j < acc.upTo := by
    simpa [h_upTo] using hj
  exact acc.isMin j hj' hj

/-! ### Simplified Array Minimum using `ArrayFoldAcc`

This shows how `ArrayFoldAcc` simplifies the implementation by handling
the `upTo` tracking and `complete` logic generically. -/

/-- Property for array minimum: val is ≤ all elements at indices < upTo. -/
abbrev ArrMinProp (a : Array Int) := fun (val : Int) (upTo : Nat) =>
  ∀ j < upTo, (hj : j < a.size) → val ≤ a[j]

/-- Singleton constructor for array minimum accumulator. -/
def arrMinSingleton (a : Array Int) (h : 0 < a.size) :
    ArrayFoldAcc a Int (ArrMinProp a) :=
  ⟨1, a[0], h, fun j hj _ => by simp [Nat.lt_one_iff.mp hj]⟩

/-- The step function for array minimum. -/
def arrMinStep (a : Array Int) (val : Int) (i : Nat) (hi : i < a.size) : Int :=
  min val a[i]

/-- Proof that arrMinStep preserves the minimum property. -/
theorem arrMinStep_preserves (a : Array Int) :
    ∀ val i (hi : i < a.size), ArrMinProp a val i →
      ArrMinProp a (arrMinStep a val i hi) (i + 1) := by
  intro val i hi hprop j hj hjs
  simp only [arrMinStep, min_def]
  split_ifs with hle
  · -- case: val ≤ a[i], so min = val
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · exact hprop j hj' hjs
    · exact hle
  · -- case: a[i] < val, so min = a[i]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · exact le_of_lt (lt_of_lt_of_le (lt_of_not_ge hle) (hprop j hj' hjs))
    · rfl

/-- Find array minimum using the generic `ArrayFoldAcc.run`.

This is simpler than `findMinArr` because `ArrayFoldAcc` handles
the iteration and proof that all elements are processed. -/
def findMinArr' (a : Array Int) (h : 0 < a.size) :
    {y : Int // ∀ j : Nat, (hj : j < a.size) → y ≤ a[j]} :=
  let ⟨acc, h_upTo⟩ := ArrayFoldAcc.run
    (arrMinSingleton a) (arrMinStep a) (arrMinStep_preserves a) h
  ⟨acc.val, fun j hj => acc.property j (h_upTo ▸ hj) hj⟩

/-! ### Alternative: Using `Fin.dfoldl` with Dependent Motive

For those comfortable with dependent types, `Fin.dfoldl` provides a compact
way to write verified folds. The motive tracks a strengthening invariant:
after processing `i` elements, the property holds for all indices `< i`. -/

/-- Find array minimum using `Fin.dfoldl` with a dependent motive.

This is the most compact approach but requires familiarity with dependent
fold APIs. The motive `fun i => {y // ∀ j, j.val < i.val → y ≤ a[j]}`
says "after processing `i` elements, we have the minimum of those elements."

Compared to `ArrayFoldAcc`:
- More compact (single definition vs. structure + methods)
- Less reusable (motive is inline)
- Requires understanding `Fin.dfoldl` signature -/
def findMinArrFin (a : Array Int) (h : 0 < a.size) :
    {y : Int // ∀ i : Fin a.size, y ≤ a[i]} :=
  -- Motive: after processing i elements, we have min of first i elements
  let motive : Fin (a.size + 1) → Type := fun i =>
    {y : Int // ∀ j : Fin a.size, j.val < i.val → y ≤ a[j]}
  -- Initial value: first element, property holds vacuously for j < 0
  let init : motive 0 := ⟨a[0]'h, fun j hj => by simp at hj⟩
  -- Step: extend from i to i+1 by taking min with a[i]
  let step : (i : Fin a.size) → motive i.castSucc → motive i.succ := fun i ⟨acc, hacc⟩ =>
    if hle : a[i] ≤ acc then
      ⟨a[i], fun j hj => by
        simp only [Fin.val_succ] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
        · exact le_trans hle (hacc j hj')
        · have : j = i := Fin.ext hj_eq
          subst this; rfl⟩
    else
      ⟨acc, fun j hj => by
        simp only [Fin.val_succ] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
        · exact hacc j hj'
        · have : j = i := Fin.ext hj_eq
          subst this; omega⟩
  -- Run the fold and extract result
  let ⟨result, hresult⟩ := Fin.dfoldl a.size motive step init
  ⟨result, fun i => hresult i (by simp [Fin.last])⟩

end Coding
end RMP
