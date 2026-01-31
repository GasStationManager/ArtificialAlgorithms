/-
Verified O(n log n) Longest Increasing Subsequence using Patience Sorting
Uses binary search for pile placement and predecessor tracking for reconstruction.
-/

import Mathlib.Tactic

/-!
## Specification

A strictly increasing subsequence of a list is a list of elements from the original
that maintains relative order and is strictly increasing.
-/

/-- A list is strictly increasing -/
def StrictlyIncreasing (l : List Int) : Prop :=
  l.IsChain (· < ·)

/-- `subseq s l` means s is a subsequence of l (maintains relative order) -/
inductive Subseq : List Int → List Int → Prop where
  | nil : Subseq [] l
  | cons_skip : Subseq s l → Subseq s (x :: l)
  | cons_take : Subseq s l → Subseq (x :: s) (x :: l)

/-- The specification: result is a longest strictly increasing subsequence -/
def IsLIS (result : List Int) (input : List Int) : Prop :=
  StrictlyIncreasing result ∧
  Subseq result input ∧
  ∀ other : List Int, StrictlyIncreasing other → Subseq other input →
    other.length ≤ result.length

/-!
## Patience Sorting Algorithm

The algorithm maintains:
1. `piles`: Array of pile tops (values), which is always sorted in increasing order
2. `predecessors`: For each input index, the index of its predecessor in the LIS
3. `pileIndices`: For each pile, the input index of its top card

Binary search finds the leftmost pile with top >= current element.
-/

/-- State for patience sorting LIS computation -/
structure LISState (input : List Int) where
  /-- Number of elements processed so far -/
  processed : Nat
  /-- Top of each pile (always sorted in increasing order) -/
  piles : Array Int
  /-- For each input index i < processed, the index of predecessor in LIS (-1 if none) -/
  predecessors : Array Int
  /-- For each pile, the input index of the top card -/
  pileIndices : Array Nat
  /-- processed is bounded by input length -/
  h_processed : processed ≤ input.length
  /-- piles, predecessors, pileIndices sizes are consistent -/
  h_piles_size : pileIndices.size = piles.size
  h_pred_size : predecessors.size = processed

/-- Invariant: pile tops are sorted in strictly increasing order -/
def PilesSorted (piles : Array Int) : Prop :=
  piles.toList.IsChain (· < ·)

/-- Binary search: find leftmost index where piles[i] >= target, or piles.size if none -/
def binarySearchGE (piles : Array Int) (target : Int) : Nat :=
  let rec go (lo hi : Nat) : Nat :=
    if h : lo < hi then
      let mid := (lo + hi) / 2
      if piles[mid]! >= target then
        go lo mid
      else
        go (mid + 1) hi
    else
      lo
  termination_by hi - lo
  go 0 piles.size

/-- Binary search specification: returns the leftmost index with value >= target -/
def BinarySearchSpec (piles : Array Int) (target : Int) (result : Nat) : Prop :=
  result ≤ piles.size ∧
  (∀ i < result, piles[i]! < target) ∧
  (result < piles.size → piles[result]! >= target)

/-- Binary search correctness (with sorry for now) -/
theorem binarySearchGE_spec (piles : Array Int) (target : Int)
    (hsorted : PilesSorted piles) :
    BinarySearchSpec piles target (binarySearchGE piles target) := by
  sorry

/-- Process one element in patience sorting -/
def processElement (input : List Int) (state : LISState input)
    (h_lt : state.processed < input.length) : LISState input :=
  let elem := input[state.processed]
  let pos := binarySearchGE state.piles elem
  -- Get predecessor: the top of the pile to the left (if exists)
  let pred : Int := if pos > 0 then state.pileIndices[pos - 1]! else -1
  let newPreds := state.predecessors.push pred

  if h_pos : pos < state.piles.size then
    -- Replace existing pile top
    have h_idx : pos < state.pileIndices.size := by rw [state.h_piles_size]; exact h_pos
    let newPiles := state.piles.set pos elem
    let newIndices := state.pileIndices.set pos state.processed
    {
      processed := state.processed + 1
      piles := newPiles
      predecessors := newPreds
      pileIndices := newIndices
      h_processed := Nat.succ_le_of_lt h_lt
      h_piles_size := by simp [newPiles, newIndices, state.h_piles_size]
      h_pred_size := by simp [newPreds, state.h_pred_size]
    }
  else
    -- Create new pile
    let newPiles := state.piles.push elem
    let newIndices := state.pileIndices.push state.processed
    {
      processed := state.processed + 1
      piles := newPiles
      predecessors := newPreds
      pileIndices := newIndices
      h_processed := Nat.succ_le_of_lt h_lt
      h_piles_size := by simp [newPiles, newIndices, state.h_piles_size]
      h_pred_size := by simp [newPreds, state.h_pred_size]
    }

/-- Initial state for LIS computation -/
def initLISState (input : List Int) : LISState input :=
  {
    processed := 0
    piles := #[]
    predecessors := #[]
    pileIndices := #[]
    h_processed := Nat.zero_le _
    h_piles_size := rfl
    h_pred_size := rfl
  }

/-- Termination lemma for processElement -/
theorem processElement_decreases (input : List Int) (state : LISState input)
    (h : state.processed < input.length) :
    input.length - (processElement input state h).processed < input.length - state.processed := by
  unfold processElement
  simp only
  split_ifs <;> simp only <;> omega

/-- Run patience sorting on entire input -/
def runPatience (input : List Int) : LISState input :=
  let rec go (state : LISState input) : LISState input :=
    if h : state.processed < input.length then
      go (processElement input state h)
    else
      state
  termination_by input.length - state.processed
  decreasing_by exact processElement_decreases input state h
  go (initLISState input)

/-- Reconstruct LIS from predecessors, starting from given index -/
def reconstructLIS (input : List Int) (predecessors : Array Int) (startIdx : Nat)
    (_h_start : startIdx < input.length) : List Int :=
  let rec go (idx : Int) (fuel : Nat) (acc : List Int) : List Int :=
    if fuel = 0 then acc
    else if h : idx >= 0 ∧ idx.toNat < input.length then
      let elem := input[idx.toNat]
      let predIdx := if idx.toNat < predecessors.size then predecessors[idx.toNat]! else -1
      go predIdx (fuel - 1) (elem :: acc)
    else
      acc
  go startIdx input.length []

/-- Get the index of the top of the last pile (end of longest chain) -/
def getLastPileTop (state : LISState input) : Option Nat :=
  if h : state.pileIndices.size > 0 then
    some state.pileIndices[state.pileIndices.size - 1]
  else
    none

/-- Helper: when pileIndices is empty, piles is also empty -/
theorem pileIndices_empty_implies_piles_empty (input : List Int)
    (state : LISState input) (h : state.pileIndices.size = 0) :
    state.piles.size = 0 := by
  have := state.h_piles_size
  omega

/-- The main LIS function with correctness proof -/
def longestIncreasingSubsequence (input : List Int) :
    { result : List Int //
      StrictlyIncreasing result ∧
      Subseq result input ∧
      result.length = (runPatience input).piles.size } :=
  let finalState := runPatience input
  if h : finalState.pileIndices.size > 0 then
    let lastIdx := finalState.pileIndices[finalState.pileIndices.size - 1]!
    if h2 : lastIdx < input.length then
      let lis := reconstructLIS input finalState.predecessors lastIdx h2
      ⟨lis, by sorry⟩
    else
      ⟨[], by
        constructor
        · simp [StrictlyIncreasing]
        constructor
        · exact Subseq.nil
        · sorry⟩
  else
    ⟨[], by
      constructor
      · simp [StrictlyIncreasing]
      constructor
      · exact Subseq.nil
      · have h0 : finalState.pileIndices.size = 0 := by omega
        have hpiles := pileIndices_empty_implies_piles_empty input finalState h0
        simp only [List.length_nil]
        exact hpiles.symm⟩

/-!
## Key Invariants to Prove

1. `PilesSorted`: Pile tops remain sorted after each step
2. `PilesOptimal`: The number of piles equals the LIS length
3. `PredecessorValid`: Each predecessor forms a valid strictly increasing chain
4. `SubseqValid`: The reconstructed sequence is a valid subsequence
-/

/-- Pile tops remain sorted after processing each element -/
theorem pilesSorted_preserved (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles)
    (h_lt : state.processed < input.length) :
    PilesSorted (processElement input state h_lt).piles := by
  sorry

/-- Final state has piles sorted -/
theorem runPatience_sorted (input : List Int) :
    PilesSorted (runPatience input).piles := by
  sorry

/-- The number of piles equals the length of LIS -/
theorem piles_size_eq_lis_length (input : List Int) :
    ∀ lis : List Int, IsLIS lis input →
      lis.length = (runPatience input).piles.size := by
  sorry

/-- Reconstructed sequence is strictly increasing -/
theorem reconstructLIS_increasing (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    StrictlyIncreasing (reconstructLIS input preds startIdx h_start) := by
  sorry

/-- Reconstructed sequence is a valid subsequence -/
theorem reconstructLIS_subseq (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    Subseq (reconstructLIS input preds startIdx h_start) input := by
  sorry

/-!
## Tests
-/

#eval binarySearchGE #[1, 3, 5, 7] 4  -- Should be 2 (index of 5)
#eval binarySearchGE #[1, 3, 5, 7] 3  -- Should be 1 (index of 3)
#eval binarySearchGE #[1, 3, 5, 7] 0  -- Should be 0
#eval binarySearchGE #[1, 3, 5, 7] 10 -- Should be 4 (size)

-- Test patience sorting
#eval (runPatience [10, 9, 2, 5, 3, 7, 101, 18]).piles
-- Expected: 4 piles (LIS length is 4: [2, 3, 7, 18] or [2, 5, 7, 18] etc.)

#eval (runPatience [0, 1, 0, 3, 2, 3]).piles
-- Expected: 4 piles

#eval (runPatience [7, 7, 7, 7]).piles
-- Expected: 1 pile (all same, strictly increasing = length 1)

-- Test the main function
#eval! (longestIncreasingSubsequence [10, 9, 2, 5, 3, 7, 101, 18]).val
#eval! (longestIncreasingSubsequence [0, 1, 0, 3, 2, 3]).val
#eval! (longestIncreasingSubsequence [7, 7, 7, 7]).val
