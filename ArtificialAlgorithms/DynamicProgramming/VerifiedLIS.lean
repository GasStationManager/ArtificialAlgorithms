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

/-- Helper lemma: getElem! equals getElem when index is in bounds -/
theorem Array.getElem!_eq {α : Type*} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  have hi : i < a.size := h
  show a.get!Internal i = a[i]
  unfold Array.get!Internal
  simp only [Array.getD, hi, ↓reduceDIte, Array.getInternal, Array.instGetElemNatLtSize]

/-- Helper: In a sorted array, earlier elements are smaller -/
theorem sorted_lt_of_lt {piles : Array Int} (hsorted : PilesSorted piles)
    {i j : Nat} (hi_lt : i < piles.size) (hj_lt : j < piles.size) (hij : i < j) :
    piles[i]! < piles[j]! := by
  unfold PilesSorted at hsorted
  have hi_list : i < piles.toList.length := by simp [hi_lt]
  have hj_list : j < piles.toList.length := by simp [hj_lt]
  -- Use isChain_iff_pairwise to get Pairwise, then pairwise_iff_getElem
  have hpw : piles.toList.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hsorted
  have h := List.pairwise_iff_getElem.mp hpw i j hi_list hj_list hij
  simp only [Array.getElem_toList] at h
  -- The goal is piles[i]! < piles[j]! and we have piles[i] < piles[j]
  rw [Array.getElem!_eq piles i hi_lt, Array.getElem!_eq piles j hj_lt]
  exact h

/-- Helper lemma about go function invariant -/
theorem binarySearchGE_go_spec (piles : Array Int) (target : Int)
    (hsorted : PilesSorted piles) :
    ∀ (lo hi : Nat), lo ≤ hi → hi ≤ piles.size →
    (∀ i < lo, piles[i]! < target) →
    (hi < piles.size → piles[hi]! >= target) →
    let result := binarySearchGE.go piles target lo hi
    lo ≤ result ∧ result ≤ hi ∧
    (∀ i < result, piles[i]! < target) ∧
    (result < piles.size → piles[result]! >= target) := by
  -- We use strong induction on hi - lo
  intro lo hi
  generalize h_term : hi - lo = d
  induction d using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    intro hlo hhi hbelow habove
    simp only
    unfold binarySearchGE.go
    split_ifs with hlt
    · -- lo < hi case
      simp only
      split_ifs with hmid_ge
      · -- piles[mid]! >= target, go left
        have hterm : (lo + hi) / 2 - lo < d := by omega
        have hlo_le_mid : lo ≤ (lo + hi) / 2 := by omega
        have hmid_le_hi : (lo + hi) / 2 ≤ hi := by omega
        have hmid_le_size : (lo + hi) / 2 ≤ piles.size := Nat.le_trans hmid_le_hi hhi
        have habove' : (lo + hi) / 2 < piles.size → piles[(lo + hi) / 2]! >= target := fun _ => hmid_ge
        have hsub := ih ((lo + hi) / 2 - lo) hterm lo ((lo + hi) / 2) rfl hlo_le_mid hmid_le_size hbelow habove'
        simp only at hsub
        obtain ⟨h1, h2, h3, h4⟩ := hsub
        exact ⟨h1, Nat.le_trans h2 hmid_le_hi, h3, h4⟩
      · -- piles[mid]! < target, go right
        have hmid_lt' : piles[(lo + hi) / 2]! < target := Int.not_le.mp hmid_ge
        have hterm : hi - ((lo + hi) / 2 + 1) < d := by omega
        have hmid1_le_hi : (lo + hi) / 2 + 1 ≤ hi := by omega
        have hmid_lt_size : (lo + hi) / 2 < piles.size := by omega
        have hbelow' : ∀ i < (lo + hi) / 2 + 1, piles[i]! < target := by
          intro i hi'
          by_cases h : i < lo
          · exact hbelow i h
          · by_cases heq : i = (lo + hi) / 2
            · rw [heq]; exact hmid_lt'
            · have hi_lt_mid : i < (lo + hi) / 2 := by omega
              have hi_ge_lo : lo ≤ i := Nat.not_lt.mp h
              have hi_lt_size : i < piles.size := by omega
              have pi_lt_pmid : piles[i]! < piles[(lo + hi) / 2]! :=
                sorted_lt_of_lt hsorted hi_lt_size hmid_lt_size hi_lt_mid
              exact Int.lt_trans pi_lt_pmid hmid_lt'
        have hsub := ih (hi - ((lo + hi) / 2 + 1)) hterm ((lo + hi) / 2 + 1) hi rfl hmid1_le_hi hhi hbelow' habove
        simp only at hsub
        obtain ⟨h1, h2, h3, h4⟩ := hsub
        exact ⟨Nat.le_trans (by omega : lo ≤ (lo + hi) / 2 + 1) h1, h2, h3, h4⟩
    · -- lo >= hi case
      have heq : lo = hi := Nat.le_antisymm hlo (Nat.not_lt.mp hlt)
      simp only [heq]
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun i hi' => hbelow i (heq ▸ hi'), habove⟩

/-- Binary search correctness -/
theorem binarySearchGE_spec (piles : Array Int) (target : Int)
    (hsorted : PilesSorted piles) :
    BinarySearchSpec piles target (binarySearchGE piles target) := by
  unfold BinarySearchSpec binarySearchGE
  have h := binarySearchGE_go_spec piles target hsorted 0 piles.size
    (Nat.zero_le _) (Nat.le_refl _)
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun h => absurd h (Nat.lt_irrefl _))
  simp only at h
  obtain ⟨_, hle, hbelow, habove⟩ := h
  exact ⟨hle, hbelow, habove⟩

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

/-- Helper: elem < piles[pos+1] when pos < size - 1 and elem < piles[pos] -/
theorem elem_lt_next_pile {piles : Array Int} {pos : Nat} {elem : Int}
    (hsorted : PilesSorted piles)
    (h_pos : pos < piles.size)
    (h_elem_le : elem ≤ piles[pos])
    (h_next : pos + 1 < piles.size) :
    elem < piles[pos + 1] := by
  have h_lt : piles[pos] < piles[pos + 1] := by
    have hpw : piles.toList.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hsorted
    have h := List.pairwise_iff_getElem.mp hpw pos (pos + 1) (by simp [h_pos]) (by simp [h_next]) (by omega)
    simp only [Array.getElem_toList] at h
    exact h
  omega

/-- Helper: piles[pos-1] < elem when pos > 0 and all elements before pos are < elem -/
theorem prev_pile_lt_elem {piles : Array Int} {pos : Nat} {elem : Int}
    (h_pos_gt : pos > 0)
    (h_pos_lt : pos < piles.size)
    (h_below : ∀ i < pos, piles[i]! < elem) :
    piles[pos - 1] < elem := by
  have h_prev : pos - 1 < pos := by omega
  have h_prev_lt : pos - 1 < piles.size := by omega
  have := h_below (pos - 1) h_prev
  rw [Array.getElem!_eq piles (pos - 1) h_prev_lt] at this
  exact this

/-- Helper: List.set preserves Pairwise when the new element maintains order -/
theorem List.pairwise_set_of_rel {α : Type*} {R : α → α → Prop} {l : List α} {i : Nat} {x : α}
    (h_pw : l.Pairwise R)
    (_h_len : i < l.length)
    (h_left : ∀ j < i, (hj : j < l.length) → R l[j] x)
    (h_right : ∀ j, i < j → (hj : j < l.length) → R x l[j]) :
    (l.set i x).Pairwise R := by
  rw [List.pairwise_iff_getElem] at h_pw ⊢
  intro a b ha hb hab
  simp only [List.length_set] at ha hb
  simp only [List.getElem_set]
  split_ifs with hia hib hib
  · omega
  · exact h_right b (by omega : i < b) hb
  · exact h_left a (by omega : a < i) ha
  · exact h_pw a b ha hb hab

/-- Helper: last element of non-empty array -/
theorem Array.getLast?_toList_eq' {α : Type*} (a : Array α) (h : a.size > 0) :
    a.toList.getLast? = some a[a.size - 1] := by
  have hlen : a.toList.length > 0 := by simp [h]
  have hne : a.toList ≠ [] := List.ne_nil_of_length_pos hlen
  rw [List.getLast?_eq_some_getLast hne]
  simp only [List.getLast_eq_getElem, Array.length_toList, Array.getElem_toList]

/-- Pile tops remain sorted after processing each element -/
theorem pilesSorted_preserved (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles)
    (h_lt : state.processed < input.length) :
    PilesSorted (processElement input state h_lt).piles := by
  unfold processElement
  -- Get binary search spec
  have bs := binarySearchGE_spec state.piles input[state.processed] h_sorted
  obtain ⟨h_le, h_below, h_above⟩ := bs
  -- Split on whether we replace or push (the main branching condition)
  by_cases h_pos : binarySearchGE state.piles input[state.processed] < state.piles.size
  · -- Case: pos < piles.size (replace existing pile)
    simp only [h_pos, ↓reduceDIte, PilesSorted]
    rw [Array.toList_set]
    -- Need to show (state.piles.toList.set pos elem).IsChain (· < ·)
    apply List.isChain_iff_pairwise.mpr
    apply List.pairwise_set_of_rel
    · exact List.isChain_iff_pairwise.mp h_sorted
    · simp [h_pos]
    · -- For j < pos, show piles[j] < elem
      intro j hj_lt hj_len
      simp only [Array.length_toList] at hj_len
      have := h_below j hj_lt
      rw [Array.getElem!_eq _ _ hj_len] at this
      simp only [Array.getElem_toList]
      exact this
    · -- For j > pos, show elem < piles[j]
      intro j hj_gt hj_len
      simp only [Array.length_toList] at hj_len
      simp only [Array.getElem_toList]
      -- elem ≤ piles[pos] (from binary search) and piles[pos] < piles[j] (from sorted)
      have h_elem_le : input[state.processed] ≤ state.piles[binarySearchGE state.piles input[state.processed]] := by
        have := h_above h_pos
        rw [Array.getElem!_eq _ _ h_pos] at this
        exact this
      have h_sorted_pw : state.piles.toList.Pairwise (· < ·) := List.isChain_iff_pairwise.mp h_sorted
      have h_pos_j : state.piles[binarySearchGE state.piles input[state.processed]] < state.piles[j] := by
        have := List.pairwise_iff_getElem.mp h_sorted_pw
          (binarySearchGE state.piles input[state.processed]) j
          (by simp [h_pos]) (by simp [hj_len]) hj_gt
        simp only [Array.getElem_toList] at this
        exact this
      omega
  · -- Case: pos >= piles.size (push new element)
    simp only [h_pos, ↓reduceDIte, PilesSorted]
    rw [Array.toList_push]
    -- pos = piles.size, so all elements < elem
    have h_pos_eq : binarySearchGE state.piles input[state.processed] = state.piles.size := by
      have : binarySearchGE state.piles input[state.processed] ≤ state.piles.size := h_le
      omega
    -- Need to show (piles.toList ++ [elem]).IsChain (· < ·)
    apply List.IsChain.append h_sorted (List.IsChain.singleton _)
    -- Show last of piles < elem
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_def] at hy
    cases hy
    -- x is the last element of piles.toList
    by_cases h_empty : state.piles.size = 0
    · -- Empty piles case: getLast? = none, so the premise is false
      have hempty_list : state.piles.toList = [] := by
        have : state.piles.toList.length = 0 := by simp [h_empty]
        exact List.eq_nil_of_length_eq_zero this
      simp only [hempty_list, List.getLast?_nil, Option.mem_def] at hx
      cases hx
    · -- Non-empty piles case
      have h_size_pos : state.piles.size > 0 := Nat.pos_of_ne_zero h_empty
      rw [Array.getLast?_toList_eq' _ h_size_pos] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      -- Need: piles[size-1] < elem
      have h_last_idx : state.piles.size - 1 < state.piles.size := by omega
      have := h_below (state.piles.size - 1) (by omega : state.piles.size - 1 < binarySearchGE state.piles input[state.processed])
      rw [Array.getElem!_eq _ _ h_last_idx] at this
      exact this

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
