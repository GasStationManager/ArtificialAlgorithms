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

/-! ## Alternative: Direct foldl with Manual Induction

This section demonstrates an alternative pattern for verified folds using direct
`List.foldl` with manual induction on the list suffix. This approach is cleaner than
`ListFoldAcc` when:

- The invariant depends on indices into the original list (e.g., `prices.getD i 0`)
- You don't need permutation reasoning
- You're processing a list suffix with `foldl`

**Example: Maximum Stock Profit**

Given a list of stock prices where `prices[i]` is the price on day `i`, find the
maximum profit from buying on one day and selling on a later day. The algorithm
maintains:
- `minPrice`: minimum price seen so far (can buy at this price)
- `maxProfit`: best profit achievable (max of `price - minPrice` seen so far)

**Key Pattern:**
1. Define an invariant structure with `k_bound : k ≤ list.length` and properties for indices `< k`
2. Prove `init`: invariant holds at k=1 after processing first element
3. Prove `step`: invariant preservation from k to k+1
4. Prove `foldl_invariant_aux`: induction on suffix with `h_suffix : list.drop k = suffix`
5. Final theorem applying the aux lemma
-/

/-- State for max profit calculation: tracks minimum price seen and best profit so far -/
structure MaxProfitState where
  minPrice : Int
  maxProfit : Int
  deriving Repr, DecidableEq

/-- Minimum of first k elements of prices (prices[0..k)) -/
def minOfFirstK (prices : List Int) (k : Nat) : Int :=
  if k = 0 then 0  -- vacuous case
  else (List.range k).foldl (fun acc i => min acc (prices.getD i 0)) (prices.getD 0 0)

/-- Invariant after processing k prices from the list.

The key insight is that we track:
- `minPrice`: the minimum of prices[0..k), so we can "buy" at this price
- `maxProfit`: the maximum achievable profit considering all buy/sell pairs in [0, k)

The property `maxP_ge` captures: for any day j < k, if we sell on day j, the best
profit (buying at the minimum price up to and including day j) is bounded by maxProfit.
-/
structure MaxProfitInv (prices : List Int) (state : MaxProfitState) (k : Nat) : Prop where
  k_bound : k ≤ prices.length
  -- minPrice equals minimum of prices[0..k)
  minP_eq : k > 0 → state.minPrice = minOfFirstK prices k
  -- maxProfit is non-negative (we can always choose not to trade)
  maxP_nonneg : 0 ≤ state.maxProfit
  -- maxProfit bounds the profit of selling on any day j < k
  -- (buying at the running minimum up to that point)
  maxP_ge : ∀ j, j < k → prices.getD j 0 - minOfFirstK prices (j + 1) ≤ state.maxProfit

/-- Step function: update state with the next price -/
def maxProfitStep (state : MaxProfitState) (price : Int) : MaxProfitState :=
  { minPrice := min state.minPrice price
    maxProfit := max state.maxProfit (price - state.minPrice) }

/-- Initialize state with the first price: minPrice = price, maxProfit = 0 -/
def maxProfitInit (price : Int) : MaxProfitState :=
  { minPrice := price, maxProfit := 0 }

/-! ### Key Lemmas -/

/-- Helper: minOfFirstK for k+1 equals min of minOfFirstK k and prices[k] -/
theorem minOfFirstK_succ (prices : List Int) (k : Nat) (hk_pos : k > 0) (_hk : k < prices.length) :
    minOfFirstK prices (k + 1) = min (minOfFirstK prices k) (prices.getD k 0) := by
  simp only [minOfFirstK]
  have hk1 : k + 1 ≠ 0 := by omega
  have hkne : k ≠ 0 := by omega
  simp only [hk1, hkne, ↓reduceIte, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Init lemma: After processing the first element, the invariant holds at k=1 -/
theorem maxProfitInv_init (prices : List Int) (h : prices.length > 0) :
    MaxProfitInv prices (maxProfitInit (prices.getD 0 0)) 1 := by
  constructor
  · -- k_bound: 1 ≤ prices.length
    exact h
  · -- minP_eq: minPrice = minOfFirstK prices 1
    intro _
    simp only [maxProfitInit, minOfFirstK]
    have h1 : (1 : Nat) ≠ 0 := by omega
    simp only [h1, ↓reduceIte, List.range_one, List.foldl_cons, List.foldl_nil, min_self]
  · -- maxP_nonneg: 0 ≤ maxProfit
    simp [maxProfitInit]
  · -- maxP_ge: for all j < 1, profit bound holds
    intro j hj
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst hj0
    simp only [maxProfitInit, minOfFirstK, Nat.zero_add]
    have h1 : (1 : Nat) ≠ 0 := by omega
    simp only [h1, ↓reduceIte, List.range_one, List.foldl_cons, List.foldl_nil, min_self, sub_self, le_refl]

/-- Step lemma: If invariant holds at k with k > 0, it holds at k+1 after processing prices[k] -/
theorem maxProfitInv_step (prices : List Int) (state : MaxProfitState) (k : Nat)
    (hinv : MaxProfitInv prices state k) (hk_pos : k > 0) (hk : k < prices.length) :
    MaxProfitInv prices (maxProfitStep state (prices.getD k 0)) (k + 1) := by
  constructor
  · -- k_bound: k + 1 ≤ prices.length
    omega
  · -- minP_eq: new minPrice = minOfFirstK prices (k+1)
    intro _
    simp only [maxProfitStep]
    have hmin := hinv.minP_eq hk_pos
    rw [hmin, minOfFirstK_succ prices k hk_pos hk]
  · -- maxP_nonneg: 0 ≤ max state.maxProfit (price - state.minPrice)
    simp only [maxProfitStep]
    exact le_max_of_le_left hinv.maxP_nonneg
  · -- maxP_ge: for all j < k+1, profit bound holds
    intro j hj
    simp only [maxProfitStep]
    -- Case split: j < k or j = k
    by_cases hjlt : j < k
    · -- Case j < k: use hinv.maxP_ge
      have h := hinv.maxP_ge j hjlt
      calc prices.getD j 0 - minOfFirstK prices (j + 1)
          ≤ state.maxProfit := h
        _ ≤ max state.maxProfit (prices.getD k 0 - state.minPrice) := le_max_left _ _
    · -- Case j = k: need to show prices[k] - minOfFirstK(k+1) ≤ max(...)
      have hjk : j = k := by omega
      subst hjk
      -- state.minPrice = minOfFirstK prices j
      have hmin := hinv.minP_eq hk_pos
      -- minOfFirstK prices (j+1) = min (minOfFirstK prices j) (prices.getD j 0)
      rw [minOfFirstK_succ prices j hk_pos hk, ← hmin]
      -- Now goal has state.minPrice instead of minOfFirstK prices j
      -- Case split on whether state.minPrice ≤ prices[j]
      by_cases hle : state.minPrice ≤ prices.getD j 0
      · -- Case state.minPrice ≤ prices[j]: min = state.minPrice
        rw [min_eq_left hle]
        exact le_max_right _ _
      · -- Case state.minPrice > prices[j]: min = prices[j], so diff = 0
        push_neg at hle
        rw [min_eq_right (Int.le_of_lt hle)]
        simp only [sub_self]
        exact le_max_of_le_left hinv.maxP_nonneg

/-- Auxiliary lemma: foldl over suffix maintains invariant.
    This uses induction on the suffix with the connection `suffix = prices.drop k`. -/
theorem maxProfitInv_foldl_aux (prices : List Int) (state : MaxProfitState) (k : Nat)
    (suffix : List Int) (h_suffix : suffix = prices.drop k)
    (hinv : MaxProfitInv prices state k) (hk_pos : k > 0) :
    MaxProfitInv prices (suffix.foldl maxProfitStep state) (k + suffix.length) := by
  induction suffix generalizing k state with
  | nil => simp [hinv]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hk : k < prices.length := by
      have hlen : (x :: xs).length = (prices.drop k).length := by rw [h_suffix]
      simp only [List.length_cons, List.length_drop] at hlen
      omega
    have hdrop_form : prices.drop k = prices[k] :: prices.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [hdrop_form] at h_suffix
    injection h_suffix with hx_eq hxs_eq
    have hx_getD : x = prices.getD k 0 := by rw [hx_eq, ← List.getD_eq_getElem prices 0 hk]
    have hinv_next : MaxProfitInv prices (maxProfitStep state (prices.getD k 0)) (k + 1) :=
      maxProfitInv_step prices state k hinv hk_pos hk
    -- Need to use IH: xs = prices.drop (k+1), state' = maxProfitStep state x, start at k+1
    rw [hx_getD]
    have hk1_pos : k + 1 > 0 := by omega
    have h_result := ih (maxProfitStep state (prices.getD k 0)) (k + 1) hxs_eq hinv_next hk1_pos
    -- Fix the arithmetic: k + (xs.length + 1) = (k + 1) + xs.length
    convert h_result using 1
    omega

/-- Main computation: fold over the list to compute max profit -/
def maxProfitCompute (prices : List Int) : MaxProfitState :=
  match prices with
  | [] => { minPrice := 0, maxProfit := 0 }
  | p :: ps => ps.foldl maxProfitStep (maxProfitInit p)

/-- Final theorem: maxProfitCompute satisfies the full invariant -/
theorem maxProfitCompute_spec (prices : List Int) (h : prices.length > 0) :
    MaxProfitInv prices (maxProfitCompute prices) prices.length := by
  match prices with
  | [] => simp at h
  | p :: ps =>
    simp only [maxProfitCompute, List.length_cons]
    -- Initial state after first element
    have h_init : MaxProfitInv (p :: ps) (maxProfitInit p) 1 := by
      have : (p :: ps).getD 0 0 = p := by simp
      rw [← this]
      exact maxProfitInv_init (p :: ps) (by simp)
    -- Apply the auxiliary lemma with suffix = ps = (p :: ps).drop 1
    have h_suffix : ps = (p :: ps).drop 1 := by simp
    have h_result := maxProfitInv_foldl_aux (p :: ps) (maxProfitInit p) 1 ps h_suffix h_init (by omega)
    -- 1 + ps.length = ps.length + 1
    rw [Nat.add_comm] at h_result
    exact h_result

/-- Extract max profit value with correctness guarantee -/
def maxProfit (prices : List Int) (h : prices.length > 0) :
    { profit : Int // profit ≥ 0 ∧
      ∀ j, j < prices.length →
        prices.getD j 0 - minOfFirstK prices (j + 1) ≤ profit } :=
  let state := maxProfitCompute prices
  let spec := maxProfitCompute_spec prices h
  ⟨state.maxProfit, spec.maxP_nonneg, spec.maxP_ge⟩

/-! ### Documentation: When to Use This Pattern

**Use direct foldl with manual induction when:**
- Your invariant references indices into the original list (e.g., `list.getD i default`)
- You need to track progress via index `k` rather than a `seen` list
- The fold processes elements in order and you need "prefix" properties

**Use `ListFoldAcc` instead when:**
- You need permutation proofs (the `seen` list tracks exactly what was processed)
- The order of processing doesn't matter for the property
- You're computing something like a minimum/maximum where membership matters

**Key differences:**
- `ListFoldAcc` uses a `seen : List α` field that builds up the processed elements
- Direct foldl uses an index `k : Nat` representing "processed first k elements"
- `ListFoldAcc` requires proving `acc.seen.Perm original_list` at the end
- Direct foldl requires proving the induction step connects `suffix = list.drop k`
-/

/-! ## Stateful Folds with Auxiliary Data

This section demonstrates how to track multiple auxiliary values through a fold while
maintaining provable invariants. The key pattern is:

1. **Bundle all tracked state into a single structure** with explicit invariants
2. **Use `Array (Option α)` instead of `HashMap`** for bounded categories
3. **Prove invariants about each tracked value** and show how they compose

### Why Array over HashMap

Using `Array (Option Int)` instead of `HashMap Nat Int`:
1. Array indexing is total for valid indices (no `Option` wrapping for known-present keys)
2. Size invariant (`arr.size = k`) is easy to maintain
3. Avoids HashMap-specific proof obligations
4. Aligns with existing `ArrayFoldAcc` patterns

### Example: Maximum Subarray Sum Divisible by k

Given an array of integers, find the maximum subarray sum where the subarray length
is divisible by `k`. The algorithm uses prefix sums and modular arithmetic:

- `subarraySum[i..j] = prefixSum[j] - prefixSum[i-1]`
- Length `(j - i + 1)` is divisible by `k` iff `j % k == (i - 1) % k`
- Track `minPrefixByMod[m]` = minimum prefix sum among indices with `index % k == m`
- Max subarray sum = max over all `j` of `prefixSum[j] - minPrefixByMod[j % k]`

Note: We track prefix sums at indices 0, 1, ..., n where prefixSum[0] = 0 and
prefixSum[i] = arr[0] + ... + arr[i-1] for i > 0. A subarray arr[i..j] has
sum prefixSum[j+1] - prefixSum[i], and length (j - i + 1).
-/

/-- Prefix sum up to index i: sum of arr[0..i) -/
def prefixSumAt (arr : List Int) (i : Nat) : Int :=
  (arr.take i).sum

/-- Minimum of a list of integers, or none if empty -/
def listMinOpt (l : List Int) : Option Int :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (min m x)) none

/-- Maximum of a list of integers, or none if empty -/
def listMaxOpt (l : List Int) : Option Int :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (max m x)) none

theorem listMinOpt_nil : listMinOpt [] = none := rfl
theorem listMinOpt_singleton (x : Int) : listMinOpt [x] = some x := rfl
theorem listMaxOpt_nil : listMaxOpt [] = none := rfl
theorem listMaxOpt_singleton (x : Int) : listMaxOpt [x] = some x := rfl

/-- Adding an element to listMaxOpt -/
theorem listMaxOpt_append_singleton (l : List Int) (x : Int) :
    listMaxOpt (l ++ [x]) = match listMaxOpt l with
      | none => some x
      | some m => some (max m x) := by
  simp only [listMaxOpt, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Combining two Options with max -/
def optionMax (a b : Option Int) : Option Int :=
  match a, b with
  | none, none => none
  | some m, none => some m
  | none, some c => some c
  | some m, some c => some (max m c)

theorem listMaxOpt_append (l1 l2 : List Int) :
    listMaxOpt (l1 ++ l2) = optionMax (listMaxOpt l1) (listMaxOpt l2) := by
  induction l2 using List.reverseRecOn generalizing l1 with
  | nil =>
    simp [listMaxOpt_nil, optionMax]
    cases listMaxOpt l1 <;> rfl
  | append_singleton l2 x ih =>
    rw [← List.append_assoc, listMaxOpt_append_singleton, ih, listMaxOpt_append_singleton]
    cases listMaxOpt l1 <;> cases listMaxOpt l2 <;> simp [optionMax, max_assoc]

/-- Adding an element to listMinOpt -/
theorem listMinOpt_append_singleton (l : List Int) (x : Int) :
    listMinOpt (l ++ [x]) = match listMinOpt l with
      | none => some x
      | some m => some (min m x) := by
  simp only [listMinOpt, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- prefixSumAt step lemma -/
theorem prefixSumAt_succ (arr : List Int) (idx : Nat) (hidx : idx < arr.length) :
    prefixSumAt arr (idx + 1) = prefixSumAt arr idx + arr[idx] := by
  simp only [prefixSumAt]
  rw [List.take_add_one]
  -- arr[idx]? = some arr[idx] when idx < arr.length
  have hgetElem? : arr[idx]? = some arr[idx] := List.getElem?_eq_getElem hidx
  rw [hgetElem?]
  simp only [Option.toList, List.sum_append, List.sum_singleton]

/-- prefixSumAt step lemma using getD -/
theorem prefixSumAt_succ' (arr : List Int) (idx : Nat) (hidx : idx < arr.length) :
    prefixSumAt arr (idx + 1) = prefixSumAt arr idx + arr.getD idx 0 := by
  rw [prefixSumAt_succ arr idx hidx]
  simp only [List.getD, List.getElem?_eq_getElem hidx, Option.getD_some]

/-- Helper: updating Option Int with min -/
def updateMinOpt (old : Option Int) (x : Int) : Option Int :=
  match old with
  | none => some x
  | some m => some (min m x)

/-- Helper: updating Option Int with max -/
def updateMaxOpt (old : Option Int) (x : Int) : Option Int :=
  match old with
  | none => some x
  | some m => some (max m x)

/-- State for max subarray sum calculation where length is divisible by k.

Tracks:
- `idx`: number of elements processed (0 to arr.length)
- `prefixSum`: current prefix sum = arr[0] + ... + arr[idx-1]
- `minByMod`: array of size k where minByMod[m] = min prefix sum among indices with index % k = m
- `maxSum`: best subarray sum found so far (None if no valid subarray yet)
-/
structure MaxSubarraySumState (arr : List Int) (k : Nat) where
  idx : Nat
  prefixSum : Int
  minByMod : Array (Option Int)  -- size k
  maxSum : Option Int
  deriving Repr

/-- Minimum prefix sum among indices ≤ n with index % k = m -/
def minPrefixByMod (arr : List Int) (k : Nat) (n : Nat) (m : Nat) : Option Int :=
  listMinOpt ((List.range (n + 1)).filter (· % k = m) |>.map (prefixSumAt arr))

/-- minPrefixByMod step for different mod class (unchanged) -/
theorem minPrefixByMod_step_ne' (arr : List Int) (k : Nat) (_hk : k > 0) (idx : Nat) (m : Nat)
    (_hm : m < k) (hne : m ≠ (idx + 1) % k) :
    minPrefixByMod arr k (idx + 1) m = minPrefixByMod arr k idx m := by
  simp only [minPrefixByMod]
  congr 1
  rw [List.range_succ]
  simp only [List.filter_append, List.map_append, List.filter_singleton]
  have hne' : ¬((idx + 1) % k = m) := fun h => hne h.symm
  simp only [hne', decide_false, cond_false, List.map_nil, List.append_nil]

/-- minPrefixByMod step for same mod class (adds new element with min) -/
theorem minPrefixByMod_step_eq' (arr : List Int) (k : Nat) (_hk : k > 0) (idx : Nat) (m : Nat)
    (_hm : m < k) (heq : m = (idx + 1) % k) :
    minPrefixByMod arr k (idx + 1) m = match minPrefixByMod arr k idx m with
      | none => some (prefixSumAt arr (idx + 1))
      | some oldMin => some (min oldMin (prefixSumAt arr (idx + 1))) := by
  simp only [minPrefixByMod]
  rw [List.range_succ]
  simp only [List.filter_append, List.map_append, List.filter_singleton]
  have heq' : (idx + 1) % k = m := heq.symm
  simp only [heq', decide_true, cond_true, List.map_singleton]
  rw [listMinOpt_append_singleton]

/-- Maximum subarray sum with length divisible by k, considering subarrays ending at positions ≤ n -/
def maxSubarraySumSpec (arr : List Int) (k : Nat) (n : Nat) : Option Int :=
  -- For each ending position j in [1, n], compute the best sum if we have a matching start
  let candidates := (List.range n).filterMap fun j =>
    -- j+1 is the ending prefix index; we need a start with same mod class
    match minPrefixByMod arr k j ((j + 1) % k) with
    | none => none
    | some minP => some (prefixSumAt arr (j + 1) - minP)
  listMaxOpt candidates

/-- The candidate at position idx for maxSubarraySumSpec -/
def maxSubarraySumCandidate (arr : List Int) (k : Nat) (idx : Nat) : Option Int :=
  match minPrefixByMod arr k idx ((idx + 1) % k) with
  | none => none
  | some minP => some (prefixSumAt arr (idx + 1) - minP)

/-- Step lemma for maxSubarraySumSpec: adding one more position -/
theorem maxSubarraySumSpec_step (arr : List Int) (k : Nat) (idx : Nat) :
    maxSubarraySumSpec arr k (idx + 1) =
      optionMax (maxSubarraySumSpec arr k idx) (maxSubarraySumCandidate arr k idx) := by
  simp only [maxSubarraySumSpec, maxSubarraySumCandidate]
  rw [List.range_succ, List.filterMap_append, listMaxOpt_append]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases minPrefixByMod arr k idx ((idx + 1) % k) <;> rfl

/-- Invariant for MaxSubarraySumState after processing idx prefix sums (indices 0..idx).

The key properties are:
1. `idx_bound`: we haven't processed more than arr.length + 1 prefix indices
2. `minByMod_size`: the modular tracking array has exactly k entries
3. `prefix_correct`: prefixSum equals the actual prefix sum at idx
4. `min_correct`: minByMod[m] tracks minimum prefix sum with index % k = m, for indices ≤ idx
5. `maxSum_correct`: maxSum equals the best subarray sum found so far
-/
structure MaxSubarraySumInv (arr : List Int) (k : Nat) (_hk : k > 0)
    (state : MaxSubarraySumState arr k) (idx : Nat) : Prop where
  idx_eq : state.idx = idx
  idx_bound : idx ≤ arr.length
  minByMod_size : state.minByMod.size = k
  prefix_correct : state.prefixSum = prefixSumAt arr idx
  -- minByMod[m] equals the minimum prefix sum spec (using getD with none default)
  min_correct : ∀ m < k, state.minByMod.getD m none = minPrefixByMod arr k idx m
  maxSum_correct : state.maxSum = maxSubarraySumSpec arr k idx

/-- Step function: process the next element arr[idx] -/
def maxSubarraySumStep (arr : List Int) (k : Nat) (hk : k > 0)
    (state : MaxSubarraySumState arr k) (hsize : state.minByMod.size = k)
    (_hidx : state.idx < arr.length) : MaxSubarraySumState arr k :=
  let newIdx := state.idx + 1
  let newPrefixSum := state.prefixSum + arr.getD state.idx 0
  let modClass := newIdx % k
  have hmod : modClass < k := Nat.mod_lt newIdx hk
  have hmod' : modClass < state.minByMod.size := by rw [hsize]; exact hmod
  -- Update minByMod for the new prefix sum
  let oldMin := state.minByMod[modClass]'hmod'
  let newMin := match oldMin with
    | none => newPrefixSum
    | some m => min m newPrefixSum
  let newMinByMod := state.minByMod.set modClass (some newMin) hmod'
  -- Compute candidate max sum: newPrefixSum - minByMod[modClass]
  -- This represents a subarray ending at newIdx with length divisible by k
  let candidateSum := match oldMin with
    | none => none  -- No previous prefix with same mod class
    | some minPrev => some (newPrefixSum - minPrev)
  -- Update maxSum
  let newMaxSum := match state.maxSum, candidateSum with
    | none, none => none
    | some m, none => some m
    | none, some c => some c
    | some m, some c => some (max m c)
  { idx := newIdx
    prefixSum := newPrefixSum
    minByMod := newMinByMod
    maxSum := newMaxSum }

/-- Initial state: idx=0, prefixSum=0, minByMod[0]=Some 0, others=None -/
def maxSubarraySumInit (arr : List Int) (k : Nat) (_hk : k > 0) :
    MaxSubarraySumState arr k :=
  { idx := 0
    prefixSum := 0
    -- Initialize: minByMod[0] = Some 0 (prefix sum at index 0), others = None
    minByMod := (Array.range k).map (fun i => if i = 0 then some 0 else none)
    maxSum := none }

theorem maxSubarraySumInit_minByMod_size (arr : List Int) (k : Nat) (hk : k > 0) :
    (maxSubarraySumInit arr k hk).minByMod.size = k := by
  simp [maxSubarraySumInit]

/-- Init lemma: initial state satisfies invariant at idx=0 -/
theorem maxSubarraySumInv_init (arr : List Int) (k : Nat) (hk : k > 0) :
    MaxSubarraySumInv arr k hk (maxSubarraySumInit arr k hk) 0 := by
  constructor
  · -- idx_eq
    rfl
  · -- idx_bound
    exact Nat.zero_le _
  · -- minByMod_size
    exact maxSubarraySumInit_minByMod_size arr k hk
  · -- prefix_correct
    simp [maxSubarraySumInit, prefixSumAt]
  · -- min_correct
    intro m hm
    simp only [maxSubarraySumInit, minPrefixByMod]
    simp
    by_cases hm0 : m = 0
    · subst hm0
      simp [listMinOpt, prefixSumAt, hk]
    · simp [listMinOpt, hm, hm0]
      have h0mod : (0 : Nat) % k = 0 := Nat.zero_mod k
      grind
  · -- maxSum_correct
    simp [maxSubarraySumInit, maxSubarraySumSpec, listMaxOpt]

/-- Helper: Array.getD after Array.set at the same index -/
theorem Array.getD_set_eq' (arr : Array α) (i : Nat) (v : α) (hi : i < arr.size) (d : α) :
    (arr.set i v hi).getD i d = v := by
  simp [Array.getD, Array.size_set, hi]

/-- Helper: Array.getD after Array.set at a different index -/
theorem Array.getD_set_ne' (arr : Array α) (i j : Nat) (v : α) (hi : i < arr.size) (d : α)
    (hne : j ≠ i) (hj : j < arr.size) :
    (arr.set i v hi).getD j d = arr.getD j d := by
  simp only [Array.getD, Array.size_set, hj, dite_true]
  exact Array.getElem_set_ne hi hj hne.symm

/-- Step lemma: invariant preserved when processing next element -/
theorem maxSubarraySumInv_step (arr : List Int) (k : Nat) (hk : k > 0)
    (state : MaxSubarraySumState arr k) (idx : Nat)
    (hinv : MaxSubarraySumInv arr k hk state idx) (hidx : idx < arr.length) :
    MaxSubarraySumInv arr k hk
      (maxSubarraySumStep arr k hk state hinv.minByMod_size (by rw [hinv.idx_eq]; exact hidx)) (idx + 1) := by
  -- Useful abbreviations
  let modClass := (idx + 1) % k
  have hmod : modClass < k := Nat.mod_lt (idx + 1) hk
  have hmod_size : modClass < state.minByMod.size := by rw [hinv.minByMod_size]; exact hmod
  have hidx' : state.idx < arr.length := by rw [hinv.idx_eq]; exact hidx
  -- Construct the invariant
  constructor
  · -- idx_eq: newIdx = idx + 1
    simp only [maxSubarraySumStep]
    rw [hinv.idx_eq]
  · -- idx_bound: idx + 1 ≤ arr.length
    omega
  · -- minByMod_size: size preserved by Array.set
    simp only [maxSubarraySumStep]
    rw [Array.size_set]
    exact hinv.minByMod_size
  · -- prefix_correct: newPrefixSum = prefixSumAt arr (idx + 1)
    simp only [maxSubarraySumStep]
    rw [hinv.prefix_correct, hinv.idx_eq]
    exact (prefixSumAt_succ' arr idx hidx).symm
  · -- min_correct: updated minByMod matches minPrefixByMod spec at idx + 1
    intro m hm
    simp only [maxSubarraySumStep]
    -- We have state.minByMod.set modClass (some newMin)
    -- where modClass = (state.idx + 1) % k = (idx + 1) % k
    have hmod_eq : (state.idx + 1) % k = modClass := by rw [hinv.idx_eq]
    by_cases hmeq : m = modClass
    · -- Case: m = modClass (the updated index)
      subst hmeq
      simp only [hmod_eq]
      rw [Array.getD_set_eq']
      -- Now need to show: some newMin = minPrefixByMod arr k (idx + 1) modClass
      rw [minPrefixByMod_step_eq' arr k hk idx modClass hmod rfl]
      -- Show the min computation matches
      have hprev := hinv.min_correct modClass hmod
      -- oldMin = state.minByMod[modClass] via getElem
      have holdMin : state.minByMod[modClass]'hmod_size = state.minByMod.getD modClass none := by
        simp [Array.getD, hmod_size]
      rw [holdMin, hprev]
      -- newPrefixSum = prefixSumAt arr (idx + 1)
      have hnewPfx : state.prefixSum + arr.getD state.idx 0 = prefixSumAt arr (idx + 1) := by
        rw [hinv.prefix_correct, hinv.idx_eq, prefixSumAt_succ' arr idx hidx]
      rw [hnewPfx]
      -- The match cases align
      cases hcase : minPrefixByMod arr k idx modClass
      · simp
      · simp
    · -- Case: m ≠ modClass (unchanged index)
      have hm_size : m < state.minByMod.size := by rw [hinv.minByMod_size]; exact hm
      simp only [hmod_eq]
      rw [Array.getD_set_ne' _ _ _ _ hmod_size _ hmeq hm_size]
      rw [minPrefixByMod_step_ne' arr k hk idx m hm hmeq]
      exact hinv.min_correct m hm
  · -- maxSum_correct: updated maxSum matches maxSubarraySumSpec at idx + 1
    simp only [maxSubarraySumStep]
    rw [maxSubarraySumSpec_step arr k idx]
    rw [hinv.maxSum_correct]
    have hmod_eq : (state.idx + 1) % k = (idx + 1) % k := by rw [hinv.idx_eq]
    have hmod_size : (state.idx + 1) % k < state.minByMod.size := by
      rw [hinv.minByMod_size]; exact Nat.mod_lt (state.idx + 1) hk
    have hmc : (idx + 1) % k < k := Nat.mod_lt (idx + 1) hk
    have hmin_inv : state.minByMod.getD ((idx + 1) % k) none = minPrefixByMod arr k idx ((idx + 1) % k) :=
      hinv.min_correct ((idx + 1) % k) hmc
    have hnewPfx : state.prefixSum + arr.getD state.idx 0 = prefixSumAt arr (idx + 1) := by
      rw [hinv.prefix_correct, hinv.idx_eq, prefixSumAt_succ' arr idx hidx]
    have hgetD_eq : state.minByMod[(state.idx + 1) % k]'hmod_size =
        state.minByMod.getD ((state.idx + 1) % k) none := by simp [Array.getD, hmod_size]
    have hmin_eq : state.minByMod[(state.idx + 1) % k]'hmod_size =
        minPrefixByMod arr k idx ((idx + 1) % k) := by rw [hgetD_eq, hmod_eq, hmin_inv]
    simp only [hmod_eq, hnewPfx, maxSubarraySumCandidate, optionMax]
    -- Case on minPrefixByMod, and use hmin_eq to relate
    cases hcase : minPrefixByMod arr k idx ((idx + 1) % k) with
    | none =>
      have hstate_none : state.minByMod[(state.idx + 1) % k]'hmod_size = none := by
        rw [hmin_eq]; exact hcase
      simp only [hmod_eq] at hstate_none
      simp only [hstate_none]
    | some val =>
      have hstate_some : state.minByMod[(state.idx + 1) % k]'hmod_size = some val := by
        rw [hmin_eq]; exact hcase
      simp only [hmod_eq] at hstate_some
      simp only [hstate_some]

/-- Compute max subarray sum by folding over the array -/
def maxSubarraySumCompute (arr : List Int) (k : Nat) (hk : k > 0) :
    MaxSubarraySumState arr k :=
  let rec loop (state : MaxSubarraySumState arr k)
      (hinv : MaxSubarraySumInv arr k hk state state.idx) :
      MaxSubarraySumState arr k :=
    if h : state.idx < arr.length then
      let state' := maxSubarraySumStep arr k hk state hinv.minByMod_size h
      have hinv' : MaxSubarraySumInv arr k hk state' state'.idx := by
        have heq : state.idx = state.idx := rfl
        have := maxSubarraySumInv_step arr k hk state state.idx
          (heq ▸ hinv) h
        have hidx_eq : state'.idx = state.idx + 1 := by simp [maxSubarraySumStep, state']
        rw [hidx_eq]
        exact this
      loop state' hinv'
    else
      state
  termination_by arr.length - state.idx
  decreasing_by simp [maxSubarraySumStep]; omega
  loop (maxSubarraySumInit arr k hk) (maxSubarraySumInv_init arr k hk)

/-- Helper: loop returns state with invariant at arr.length -/
theorem maxSubarraySumCompute_loop_spec (arr : List Int) (k : Nat) (hk : k > 0)
    (state : MaxSubarraySumState arr k) (hinv : MaxSubarraySumInv arr k hk state state.idx) :
    MaxSubarraySumInv arr k hk (maxSubarraySumCompute.loop arr k hk state hinv) arr.length := by
  unfold maxSubarraySumCompute.loop
  split
  · -- state.idx < arr.length: recursive case
    rename_i h
    let state' := maxSubarraySumStep arr k hk state hinv.minByMod_size h
    have hinv' : MaxSubarraySumInv arr k hk state' state'.idx := by
      have heq : state.idx = state.idx := rfl
      have := maxSubarraySumInv_step arr k hk state state.idx (heq ▸ hinv) h
      have hidx_eq : state'.idx = state.idx + 1 := by simp [maxSubarraySumStep, state']
      rw [hidx_eq]
      exact this
    exact maxSubarraySumCompute_loop_spec arr k hk state' hinv'
  · -- state.idx >= arr.length: base case
    rename_i h
    have hge : state.idx ≥ arr.length := Nat.ge_of_not_lt h
    have heq : state.idx = arr.length := Nat.le_antisymm hinv.idx_bound hge
    rw [← heq, ← hinv.idx_eq]
    exact hinv
termination_by arr.length - state.idx
decreasing_by simp [maxSubarraySumStep]; omega

/-- Final specification theorem -/
theorem maxSubarraySumCompute_spec (arr : List Int) (k : Nat) (hk : k > 0) :
    MaxSubarraySumInv arr k hk (maxSubarraySumCompute arr k hk) arr.length := by
  unfold maxSubarraySumCompute
  exact maxSubarraySumCompute_loop_spec arr k hk _ (maxSubarraySumInv_init arr k hk)

/-- Extract the result with correctness proof -/
def maxSubarraySum (arr : List Int) (k : Nat) (hk : k > 0) :
    { result : Option Int // result = maxSubarraySumSpec arr k arr.length } :=
  let state := maxSubarraySumCompute arr k hk
  let spec := maxSubarraySumCompute_spec arr k hk
  ⟨state.maxSum, spec.maxSum_correct⟩

/-! ### Documentation: Design Choices

**Why `Array (Option Int)` over `HashMap Nat Int`:**

```lean
-- DON'T: HashMap makes invariants hard to prove
structure BadState where
  minByMod : Std.HashMap Nat Int  -- Hard to reason about

-- DO: Array with bounded size
structure GoodState (k : Nat) where
  minByMod : Array (Option Int)
  minByMod_size : minByMod.size = k  -- Easy invariant
```

Problems with HashMap:
1. `HashMap.find?` returns `Option` even for keys that "should" be present
2. Proving `∀ m < k, HashMap.find? m = ...` requires reasoning about HashMap internals
3. No simple lemmas connecting HashMap state to pure functional specifications

Benefits of Array:
1. `arr[m]?` is `some x` iff `m < arr.size` and `arr[m] = x`
2. Size invariant `arr.size = k` is trivial to maintain through `Array.set`
3. Direct correspondence between array state and mathematical specification

**Composing Multiple Invariants:**

The `MaxSubarraySumInv` structure demonstrates bundling multiple related invariants:
- `prefix_correct`: relates `prefixSum` to actual prefix sums
- `min_correct`: relates `minByMod` array to minimum computations
- `maxSum_correct`: relates `maxSum` to the optimization objective

Each invariant can be proven independently in the step lemma, then composed.
-/

end Coding
end RMP
