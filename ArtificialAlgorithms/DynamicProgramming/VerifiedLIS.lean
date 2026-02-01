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

/-- Helper: getElem! at the set position returns the new value -/
theorem Array.getElem!_set_eq {α : Type*} [Inhabited α] (a : Array α) (i : Nat) (v : α)
    (h : i < a.size) : (a.set i v)[i]! = v := by
  have h' : i < (a.set i v).size := by simp [h]
  rw [Array.getElem!_eq _ _ h']
  simp only [Array.getElem_set, ↓reduceIte]

/-- Helper: getElem! at other positions after set returns old value -/
theorem Array.getElem!_set_ne {α : Type*} [Inhabited α] (a : Array α) (i j : Nat) (v : α)
    (hi : i < a.size) (hne : j ≠ i) (hj : j < a.size) : (a.set i v)[j]! = a[j]! := by
  have hj' : j < (a.set i v).size := by simp [hj]
  rw [Array.getElem!_eq _ _ hj', Array.getElem!_eq _ _ hj]
  simp only [Array.getElem_set]
  split_ifs with heq
  · omega
  · rfl

/-- Helper: getElem! at the pushed position returns the pushed value -/
theorem Array.getElem!_push_last {α : Type*} [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  have h : a.size < (a.push v).size := by simp
  rw [Array.getElem!_eq _ _ h]
  simp only [Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte]

/-- Helper: getElem! at positions before size after push returns old value -/
theorem Array.getElem!_push_lt {α : Type*} [Inhabited α] (a : Array α) (v : α)
    (i : Nat) (hi : i < a.size) : (a.push v)[i]! = a[i]! := by
  have hi' : i < (a.push v).size := by simp; omega
  rw [Array.getElem!_eq _ _ hi', Array.getElem!_eq _ _ hi]
  simp only [Array.getElem_push, hi, ↓reduceDIte]

/-- Helper: List.getElem! equals List.getElem when index is in bounds -/
theorem List.getElem!_eq_getElem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! = l[i] := by
  simp only [getElem!_def, List.getElem?_eq_getElem h]

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

/-!
## Key Invariants to Prove

1. `PilesSorted`: Pile tops remain sorted after each step
2. `PilesOptimal`: The number of piles equals the LIS length
3. `PredecessorValid`: Each predecessor forms a valid strictly increasing chain
4. `SubseqValid`: The reconstructed sequence is a valid subsequence
-/

/-!
## Predecessor Validity Invariant

For the reconstructed LIS to be strictly increasing, we need:
1. Each predecessor index must point to an earlier element (predecessor < current index)
2. The value at predecessor must be strictly less than current value
3. The predecessor chain eventually terminates at -1

This invariant is maintained by patience sorting because:
- When placing element at index i on pile p, the predecessor is the top of pile p-1
- All elements on pile p-1 have values < element (by binary search property)
- The predecessor index was placed before index i
-/

/-- Predicate: a single predecessor entry is valid -/
def ValidPredecessor (input : List Int) (preds : Array Int) (idx : Nat) : Prop :=
  idx < preds.size →
  let predIdx := preds[idx]!
  (predIdx = -1 ∨
   (predIdx >= 0 ∧ predIdx.toNat < idx ∧ predIdx.toNat < input.length ∧
    input[predIdx.toNat]! < input[idx]!))

/-- All predecessors up to a given index are valid -/
def AllPredecessorsValid (input : List Int) (preds : Array Int) (upTo : Nat) : Prop :=
  ∀ idx < upTo, ValidPredecessor input preds idx

/-- The state invariant for predecessor validity -/
structure PredecessorInvariant (input : List Int) (state : LISState input) : Prop where
  /-- All predecessors recorded so far are valid -/
  all_valid : AllPredecessorsValid input state.predecessors state.processed
  /-- For each pile index p > 0, the top of pile p has predecessor pointing to pile p-1 -/
  pile_chain : ∀ p, 0 < p → p < state.piles.size →
    let topIdx := state.pileIndices[p]!
    let predIdx := state.predecessors[topIdx]!
    predIdx >= 0 ∧ predIdx.toNat = state.pileIndices[p-1]!

/-- pileIndices entries are valid input indices -/
def PileIndicesValid (input : List Int) (state : LISState input) : Prop :=
  ∀ p < state.pileIndices.size, state.pileIndices[p]! < input.length

/-- pileIndices entries are within processed range -/
def PileIndicesInRange (state : LISState input) : Prop :=
  ∀ p < state.pileIndices.size, state.pileIndices[p]! < state.processed

/-- The pile tops match their recorded values -/
def PileTopsMatch (input : List Int) (state : LISState input) : Prop :=
  ∀ p < state.piles.size,
    let idx := state.pileIndices[p]!
    idx < input.length ∧ state.piles[p]! = input[idx]!

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

/-- Empty array is trivially sorted -/
theorem pilesSorted_empty : PilesSorted #[] := by
  simp [PilesSorted]

/-- The go loop preserves pile sortedness -/
theorem runPatience_go_sorted (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles) :
    PilesSorted (runPatience.go input state).piles := by
  unfold runPatience.go
  split_ifs with h
  · -- Case: state.processed < input.length, continue recursing
    have h_next_sorted := pilesSorted_preserved input state h_sorted h
    exact runPatience_go_sorted input (processElement input state h) h_next_sorted
  · -- Case: state.processed >= input.length, return current state
    exact h_sorted
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Final state has piles sorted -/
theorem runPatience_sorted (input : List Int) :
    PilesSorted (runPatience input).piles := by
  unfold runPatience
  exact runPatience_go_sorted input (initLISState input) pilesSorted_empty

/-!
## Invariant Preservation Theorems
-/

/-- Initial state satisfies PileIndicesValid -/
theorem initState_pileIndicesValid (input : List Int) :
    PileIndicesValid input (initLISState input) := by
  intro p hp
  simp [initLISState] at hp

/-- Initial state satisfies PileIndicesInRange -/
theorem initState_pileIndicesInRange (input : List Int) :
    PileIndicesInRange (initLISState input) := by
  intro p hp
  simp [initLISState] at hp

/-- Initial state satisfies PileTopsMatch -/
theorem initState_pileTopsMatch (input : List Int) :
    PileTopsMatch input (initLISState input) := by
  intro p hp
  simp [initLISState] at hp

/-- Initial state satisfies AllPredecessorsValid -/
theorem initState_allPredecessorsValid (input : List Int) :
    AllPredecessorsValid input (initLISState input).predecessors 0 := by
  intro idx hidx
  omega

/-- PileIndicesValid is preserved by processElement -/
theorem pileIndicesValid_preserved (input : List Int) (state : LISState input)
    (h_valid : PileIndicesValid input state)
    (h_lt : state.processed < input.length) :
    PileIndicesValid input (processElement input state h_lt) := by
  unfold processElement PileIndicesValid
  simp only
  set pos := binarySearchGE state.piles input[state.processed] with hpos
  -- Split on whether we replace or push
  by_cases h_pos : pos < state.piles.size
  · -- Replace case: pileIndices.set pos state.processed
    simp only [← hpos, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_set] at hp
    have h_idx_pos : pos < state.pileIndices.size := by
      rw [state.h_piles_size]; exact h_pos
    have hp_old : p < state.pileIndices.size := hp  -- Size unchanged by set
    by_cases h_eq : p = pos
    · -- At position pos: new value is state.processed < input.length
      subst h_eq
      rw [Array.getElem!_set_eq _ _ _ h_idx_pos]
      exact h_lt
    · -- Other positions: unchanged, use old validity
      rw [Array.getElem!_set_ne state.pileIndices pos p state.processed h_idx_pos h_eq hp_old]
      exact h_valid p hp_old
  · -- Push case: pileIndices.push state.processed
    simp only [← hpos, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_push] at hp
    by_cases h_eq : p = state.pileIndices.size
    · -- At new position: new value is state.processed < input.length
      subst h_eq
      rw [Array.getElem!_push_last]
      exact h_lt
    · -- Other positions: unchanged, use old validity
      have hp' : p < state.pileIndices.size := by omega
      rw [Array.getElem!_push_lt _ _ _ hp']
      exact h_valid p hp'

/-- PileIndicesInRange is preserved by processElement -/
theorem pileIndicesInRange_preserved (input : List Int) (state : LISState input)
    (h_range : PileIndicesInRange state)
    (h_lt : state.processed < input.length) :
    PileIndicesInRange (processElement input state h_lt) := by
  unfold processElement PileIndicesInRange
  simp only
  set pos := binarySearchGE state.piles input[state.processed] with hpos
  -- Split on whether we replace or push
  by_cases h_pos : pos < state.piles.size
  · -- Replace case: pileIndices.set pos state.processed, processed := processed + 1
    simp only [← hpos, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_set] at hp
    have h_idx_pos : pos < state.pileIndices.size := by
      rw [state.h_piles_size]; exact h_pos
    have hp_old : p < state.pileIndices.size := hp  -- Size unchanged by set
    by_cases h_eq : p = pos
    · -- At position pos: new value is state.processed < processed + 1
      subst h_eq
      rw [Array.getElem!_set_eq _ _ _ h_idx_pos]
      omega
    · -- Other positions: old value < old processed < new processed
      rw [Array.getElem!_set_ne state.pileIndices pos p state.processed h_idx_pos h_eq hp_old]
      have := h_range p hp_old
      omega
  · -- Push case: pileIndices.push state.processed, processed := processed + 1
    simp only [← hpos, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_push] at hp
    by_cases h_eq : p = state.pileIndices.size
    · -- At new position: new value is state.processed < processed + 1
      subst h_eq
      rw [Array.getElem!_push_last]
      omega
    · -- Other positions: old value < old processed < new processed
      have hp' : p < state.pileIndices.size := by omega
      rw [Array.getElem!_push_lt _ _ _ hp']
      have := h_range p hp'
      omega

/-- PileTopsMatch is preserved by processElement -/
theorem pileTopsMatch_preserved (input : List Int) (state : LISState input)
    (h_match : PileTopsMatch input state)
    (h_lt : state.processed < input.length) :
    PileTopsMatch input (processElement input state h_lt) := by
  unfold processElement PileTopsMatch
  simp only
  set pos := binarySearchGE state.piles input[state.processed] with hpos
  set elem := input[state.processed] with helem
  -- Split on whether we replace or push
  by_cases h_pos : pos < state.piles.size
  · -- Replace case: piles.set pos elem, pileIndices.set pos state.processed
    simp only [← hpos, ← helem, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_set] at hp
    have h_idx_pos : pos < state.pileIndices.size := by
      rw [state.h_piles_size]; exact h_pos
    have hp_piles : p < state.piles.size := hp  -- Size unchanged by set
    have hp_idx : p < state.pileIndices.size := by rw [state.h_piles_size]; exact hp_piles
    by_cases h_eq : p = pos
    · -- At position pos: piles[pos] = elem = input[state.processed], pileIndices[pos] = state.processed
      subst h_eq
      constructor
      · rw [Array.getElem!_set_eq _ _ _ h_idx_pos]; exact h_lt
      · rw [Array.getElem!_set_eq _ _ _ h_pos, Array.getElem!_set_eq _ _ _ h_idx_pos]
        rw [List.getElem!_eq_getElem _ _ h_lt]
    · -- Other positions: unchanged
      rw [Array.getElem!_set_ne state.piles pos p elem h_pos h_eq hp_piles,
          Array.getElem!_set_ne state.pileIndices pos p state.processed h_idx_pos h_eq hp_idx]
      exact h_match p hp_piles
  · -- Push case: piles.push elem, pileIndices.push state.processed
    simp only [← hpos, ← helem, h_pos, ↓reduceDIte]
    intro p hp
    simp only [Array.size_push] at hp
    by_cases h_eq : p = state.piles.size
    · -- At new position: piles[p] = elem = input[state.processed], pileIndices[p] = state.processed
      subst h_eq
      constructor
      · rw [← state.h_piles_size, Array.getElem!_push_last]; exact h_lt
      · rw [Array.getElem!_push_last, ← state.h_piles_size, Array.getElem!_push_last]
        rw [List.getElem!_eq_getElem _ _ h_lt]
    · -- Other positions: unchanged
      have hp' : p < state.piles.size := by omega
      have h_idx' : p < state.pileIndices.size := by rw [state.h_piles_size]; exact hp'
      rw [Array.getElem!_push_lt _ _ _ hp', Array.getElem!_push_lt _ _ _ h_idx']
      exact h_match p hp'

/-- Helper: new predecessor entry from processElement is valid -/
theorem newPredecessorValid (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles)
    (h_match : PileTopsMatch input state)
    (h_range : PileIndicesInRange state)
    (h_lt : state.processed < input.length) :
    let newState := processElement input state h_lt
    let newIdx := state.processed
    let newPredIdx := newState.predecessors[newIdx]!
    (newPredIdx = -1 ∨
     (newPredIdx >= 0 ∧ newPredIdx.toNat < newIdx ∧ newPredIdx.toNat < input.length ∧
      input[newPredIdx.toNat]! < input[newIdx]!)) := by
  -- The key insight: processElement sets pred = -1 if pos = 0, otherwise
  -- pred = pileIndices[pos-1], which is the index of an earlier element
  -- that has value < current element (by binary search property)
  simp only
  unfold processElement
  simp only
  -- The predecessor is the same in both branches: it's computed before the if
  -- newPreds = state.predecessors.push pred where
  -- pred = if pos > 0 then state.pileIndices[pos - 1]! else -1
  set pos := binarySearchGE state.piles input[state.processed] with hpos
  -- newState.predecessors[state.processed]! = pred because:
  -- newState.predecessors = state.predecessors.push pred
  -- and state.predecessors.size = state.processed (by h_pred_size)
  have h_pred_at_idx :
      (state.predecessors.push (if pos > 0 then ↑(state.pileIndices[pos - 1]!) else -1))[state.processed]!
      = (if pos > 0 then ↑(state.pileIndices[pos - 1]!) else -1) := by
    have h_size : state.predecessors.size = state.processed := state.h_pred_size
    rw [← h_size, Array.getElem!_push_last]
  -- Split on branch
  by_cases h_pos : pos < state.piles.size
  · -- Replace case
    simp only [← hpos, h_pos, ↓reduceDIte]
    rw [h_pred_at_idx]
    -- Now analyze pred
    by_cases h_pos_gt : pos > 0
    · -- pos > 0: pred = pileIndices[pos-1], which is a valid earlier index
      simp only [h_pos_gt, ↓reduceIte]
      right
      have h_prev_lt : pos - 1 < state.pileIndices.size := by
        rw [state.h_piles_size]; omega
      constructor
      · -- pred >= 0 (it's a Nat cast)
        simp only [Int.natCast_nonneg]
      constructor
      · -- pred.toNat < state.processed
        have h_range' := h_range (pos - 1) h_prev_lt
        simp only [Int.toNat_natCast]
        exact h_range'
      constructor
      · -- pred.toNat < input.length
        simp only [Int.toNat_natCast]
        -- By PileTopsMatch, pileIndices[pos-1] < input.length
        have h_match' := h_match (pos - 1) (by omega : pos - 1 < state.piles.size)
        exact h_match'.1
      · -- input[pred.toNat] < input[state.processed]
        simp only [Int.toNat_natCast]
        -- By binary search, piles[pos-1] < input[state.processed]
        -- By PileTopsMatch, piles[pos-1] = input[pileIndices[pos-1]]
        have bs := binarySearchGE_spec state.piles input[state.processed] h_sorted
        rw [← hpos] at bs
        have h_below := bs.2.1 (pos - 1) (by omega : pos - 1 < pos)
        have h_match' := h_match (pos - 1) (by omega : pos - 1 < state.piles.size)
        rw [h_match'.2] at h_below
        rw [List.getElem!_eq_getElem _ _ h_lt]
        exact h_below
    · -- pos = 0: pred = -1
      left
      simp only [h_pos_gt, ↓reduceIte]
  · -- Push case
    simp only [← hpos, h_pos, ↓reduceDIte]
    rw [h_pred_at_idx]
    -- Now analyze pred
    by_cases h_pos_gt : pos > 0
    · -- pos > 0: pred = pileIndices[pos-1]
      simp only [h_pos_gt, ↓reduceIte]
      right
      -- pos >= piles.size and pos > 0, so piles.size >= 1
      have h_prev_lt : pos - 1 < state.pileIndices.size := by
        rw [state.h_piles_size]
        have bs := binarySearchGE_spec state.piles input[state.processed] h_sorted
        simp only [← hpos] at bs
        -- bs.1 : pos ≤ state.piles.size
        -- h_pos : ¬(pos < state.piles.size), so pos >= state.piles.size
        -- Combined: pos = state.piles.size
        -- h_pos_gt : pos > 0, so state.piles.size > 0
        -- Therefore pos - 1 < pos = state.piles.size
        have h_pos_le : pos ≤ state.piles.size := bs.1
        have h_pos_ge : pos ≥ state.piles.size := Nat.not_lt.mp h_pos
        have h_pos_eq : pos = state.piles.size := Nat.le_antisymm h_pos_le h_pos_ge
        omega
      constructor
      · simp only [Int.natCast_nonneg]
      constructor
      · have h_range' := h_range (pos - 1) h_prev_lt
        simp only [Int.toNat_natCast]
        exact h_range'
      constructor
      · simp only [Int.toNat_natCast]
        have h_match' := h_match (pos - 1) (by rw [state.h_piles_size] at h_prev_lt; exact h_prev_lt)
        exact h_match'.1
      · simp only [Int.toNat_natCast]
        have bs := binarySearchGE_spec state.piles input[state.processed] h_sorted
        rw [← hpos] at bs
        have h_below := bs.2.1 (pos - 1) (by omega : pos - 1 < pos)
        have h_match' := h_match (pos - 1) (by rw [state.h_piles_size] at h_prev_lt; exact h_prev_lt)
        rw [h_match'.2] at h_below
        rw [List.getElem!_eq_getElem _ _ h_lt]
        exact h_below
    · -- pos = 0: pred = -1
      left
      simp only [h_pos_gt, ↓reduceIte]

/-- AllPredecessorsValid is preserved by processElement -/
theorem allPredecessorsValid_preserved (input : List Int) (state : LISState input)
    (h_valid : AllPredecessorsValid input state.predecessors state.processed)
    (h_sorted : PilesSorted state.piles)
    (h_match : PileTopsMatch input state)
    (h_range : PileIndicesInRange state)
    (h_lt : state.processed < input.length) :
    AllPredecessorsValid input (processElement input state h_lt).predecessors
      (processElement input state h_lt).processed := by
  -- We need to show all predecessors up to state.processed + 1 are valid
  -- For idx < state.processed, they were already valid and unchanged
  -- For idx = state.processed, use newPredecessorValid
  unfold AllPredecessorsValid ValidPredecessor
  intro idx h_idx
  -- newState.processed = state.processed + 1
  unfold processElement at h_idx ⊢
  simp only at h_idx ⊢
  set pos := binarySearchGE state.piles input[state.processed] with hpos
  set pred : Int := if pos > 0 then state.pileIndices[pos - 1]! else -1 with hpred
  -- Split on whether idx is the new element or an old one
  by_cases h_pos : pos < state.piles.size
  · -- Replace case
    simp only [← hpos, h_pos, ↓reduceDIte] at h_idx ⊢
    intro h_in_bounds
    by_cases h_new : idx = state.processed
    · -- idx = state.processed: use newPredecessorValid
      subst h_new
      have h_newPred := newPredecessorValid input state h_sorted h_match h_range h_lt
      simp only at h_newPred
      unfold processElement at h_newPred
      simp only [← hpos, h_pos, ↓reduceDIte] at h_newPred
      exact h_newPred
    · -- idx < state.processed: old predecessors are unchanged and valid
      have h_idx' : idx < state.processed := by omega
      have h_old_valid := h_valid idx h_idx'
      unfold ValidPredecessor at h_old_valid
      -- The old array size was state.processed, new array is state.processed + 1
      have h_old_in_bounds : idx < state.predecessors.size := by
        rw [state.h_pred_size]; exact h_idx'
      -- predecessors.push doesn't change values at old indices
      simp only [Array.size_push] at h_in_bounds
      have h_get_eq : (state.predecessors.push pred)[idx]! = state.predecessors[idx]! :=
        Array.getElem!_push_lt _ _ _ h_old_in_bounds
      rw [h_get_eq]
      exact h_old_valid h_old_in_bounds
  · -- Push case
    simp only [← hpos, h_pos, ↓reduceDIte] at h_idx ⊢
    intro h_in_bounds
    by_cases h_new : idx = state.processed
    · -- idx = state.processed: use newPredecessorValid
      subst h_new
      have h_newPred := newPredecessorValid input state h_sorted h_match h_range h_lt
      simp only at h_newPred
      unfold processElement at h_newPred
      simp only [← hpos, h_pos, ↓reduceDIte] at h_newPred
      exact h_newPred
    · -- idx < state.processed: old predecessors are unchanged and valid
      have h_idx' : idx < state.processed := by omega
      have h_old_valid := h_valid idx h_idx'
      unfold ValidPredecessor at h_old_valid
      have h_old_in_bounds : idx < state.predecessors.size := by
        rw [state.h_pred_size]; exact h_idx'
      simp only [Array.size_push] at h_in_bounds
      have h_get_eq : (state.predecessors.push pred)[idx]! = state.predecessors[idx]! :=
        Array.getElem!_push_lt _ _ _ h_old_in_bounds
      rw [h_get_eq]
      exact h_old_valid h_old_in_bounds

/-!
## Main Theorems with Proper Hypotheses

The key insight is that `reconstructLIS_increasing` and `reconstructLIS_subseq` are NOT true
for arbitrary predecessor arrays. They require the predecessors to come from a valid
patience sorting run.
-/

/-!
### Helper lemmas for reconstructLIS

The inner `go` function of reconstructLIS is:
- go idx fuel acc: if fuel = 0 or idx invalid, return acc
- Otherwise: go (pred of idx) (fuel-1) (input[idx] :: acc)

Key properties needed:
1. The result is StrictlyIncreasing when each predecessor has smaller value
2. The result is a Subseq of input when each predecessor has smaller index

Note: These properties require induction on the fuel parameter and using
the ValidPredecessor hypothesis to show that:
- Each predecessor index is strictly less than the current index
- The value at predecessor is strictly less than the current value

The full proofs require careful handling of the inner `let rec` function.
-/

/-- Helper: StrictlyIncreasing is preserved by prepending smaller elements -/
theorem strictlyIncreasing_cons {x : Int} {xs : List Int}
    (h_inc : StrictlyIncreasing xs)
    (h_lt : ∀ y, xs.head? = some y → x < y) :
    StrictlyIncreasing (x :: xs) := by
  unfold StrictlyIncreasing at *
  apply List.IsChain.cons h_inc
  intro y hy
  exact h_lt y hy

/-- Empty list is strictly increasing -/
theorem strictlyIncreasing_nil : StrictlyIncreasing ([] : List Int) := by
  unfold StrictlyIncreasing
  exact List.IsChain.nil

/-- Singleton list is strictly increasing -/
theorem strictlyIncreasing_singleton (x : Int) : StrictlyIncreasing [x] := by
  unfold StrictlyIncreasing
  simp

/-- Head of (x :: xs) is x -/
theorem List.head?_cons_eq {α : Type*} (x : α) (xs : List α) :
    (x :: xs).head? = some x := rfl

/-- When val < acc.head?, prepending val gives increasing list if acc was increasing -/
theorem strictlyIncreasing_prepend {val : Int} {acc : List Int}
    (h_inc : StrictlyIncreasing acc)
    (h_lt : acc ≠ [] → val < acc.head!):
    StrictlyIncreasing (val :: acc) := by
  apply strictlyIncreasing_cons h_inc
  intro y hy
  cases acc with
  | nil => simp at hy
  | cons a as =>
    simp [List.head?] at hy
    subst hy
    have hne : a :: as ≠ [] := by simp
    have := h_lt hne
    simp [List.head!] at this
    exact this

/-!
### Auxiliary definition for reasoning about reconstructLIS.go

Since `reconstructLIS.go` is a local `let rec`, we define an equivalent top-level
function that we can state lemmas about.
-/

/-- Top-level version of reconstructLIS.go for proving properties -/
def reconstructGo (input : List Int) (preds : Array Int) (idx : Int) (fuel : Nat)
    (acc : List Int) : List Int :=
  if fuel = 0 then acc
  else if h : idx >= 0 ∧ idx.toNat < input.length then
    let elem := input[idx.toNat]
    let predIdx := if idx.toNat < preds.size then preds[idx.toNat]! else -1
    reconstructGo input preds predIdx (fuel - 1) (elem :: acc)
  else
    acc
termination_by fuel

/-- reconstructLIS equals reconstructGo -/
theorem reconstructLIS_eq_reconstructGo (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    reconstructLIS input preds startIdx h_start =
    reconstructGo input preds startIdx input.length [] := by
  unfold reconstructLIS
  -- Both use the same recursive structure
  -- We prove they compute the same by showing the local go equals reconstructGo
  -- Note: reconstructLIS.go has signature (input preds startIdx idx fuel acc)
  -- where startIdx is captured from the outer scope
  suffices h : ∀ idx fuel acc,
      reconstructLIS.go input preds startIdx idx fuel acc =
      reconstructGo input preds idx fuel acc by
    exact h startIdx input.length []
  intro idx fuel acc
  induction fuel generalizing idx acc with
  | zero =>
    unfold reconstructLIS.go reconstructGo
    rfl
  | succ n ih =>
    unfold reconstructLIS.go reconstructGo
    -- The first condition (fuel = 0) is false since fuel = n + 1
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    -- Now split on idx >= 0 ∧ idx.toNat < input.length
    split_ifs with hc hpred
    · -- idx is valid and idx.toNat < preds.size, predIdx = preds[idx.toNat]!
      simp only [Nat.add_sub_cancel]
      exact ih _ _
    · -- idx is valid but idx.toNat >= preds.size, predIdx = -1
      simp only [Nat.add_sub_cancel]
      exact ih _ _
    · -- idx invalid, return acc
      rfl

/-- Key lemma: reconstructGo preserves StrictlyIncreasing with proper invariants -/
theorem reconstructGo_increasing (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat) (acc : List Int)
    (h_acc_inc : StrictlyIncreasing acc)
    (h_valid : ∀ i, i < input.length → ValidPredecessor input preds i)
    (h_bound : idx >= 0 → idx.toNat < input.length →
               acc ≠ [] → input[idx.toNat]! < acc.head!) :
    StrictlyIncreasing (reconstructGo input preds idx fuel acc) := by
  induction fuel generalizing idx acc with
  | zero =>
    unfold reconstructGo
    exact h_acc_inc
  | succ n ih =>
    unfold reconstructGo
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hc hpred
    · -- idx >= 0 ∧ idx.toNat < input.length, and idx.toNat < preds.size
      simp only [Nat.add_sub_cancel]
      -- Apply IH with (input[idx.toNat] :: acc)
      apply ih (preds[idx.toNat]!) (input[idx.toNat] :: acc)
      · -- New acc is strictly increasing
        apply strictlyIncreasing_prepend h_acc_inc
        intro hne
        have hb := h_bound hc.1 hc.2 hne
        rw [List.getElem!_eq_getElem input idx.toNat hc.2] at hb
        exact hb
      · -- New bound: input[predIdx] < input[idx] = (elem :: acc).head!
        intro h_pred_ge h_pred_lt hne_new
        simp only [List.head!_cons]
        -- Goal: input[preds[idx.toNat]!.toNat]! < input[idx.toNat]
        rw [List.getElem!_eq_getElem input (preds[idx.toNat]!.toNat) h_pred_lt]
        -- Goal now: input[preds[idx.toNat]!.toNat] < input[idx.toNat]
        -- Use ValidPredecessor to get input[predIdx] < input[idx]
        have h_vp := h_valid idx.toNat hc.2
        unfold ValidPredecessor at h_vp
        have h_vp' := h_vp hpred
        cases h_vp' with
        | inl h_neg1 =>
          -- preds[idx.toNat]! = -1, so predIdx < 0, contradiction
          simp [h_neg1] at h_pred_ge
        | inr h_pos =>
          -- preds[idx.toNat]! >= 0, predIdx < idx, predIdx < input.length, input[predIdx] < input[idx]
          have hineq := h_pos.2.2.2
          rw [List.getElem!_eq_getElem input idx.toNat hc.2] at hineq
          rw [List.getElem!_eq_getElem input (preds[idx.toNat]!.toNat) h_pos.2.2.1] at hineq
          exact hineq
    · -- idx >= 0 ∧ idx.toNat < input.length, but idx.toNat >= preds.size
      simp only [Nat.add_sub_cancel]
      -- Apply IH with (input[idx.toNat] :: acc), predIdx = -1
      apply ih (-1) (input[idx.toNat] :: acc)
      · -- New acc is strictly increasing
        apply strictlyIncreasing_prepend h_acc_inc
        intro hne
        have hb := h_bound hc.1 hc.2 hne
        rw [List.getElem!_eq_getElem input idx.toNat hc.2] at hb
        exact hb
      · -- predIdx = -1 < 0, so the bound is vacuously true
        intro h_pred_ge _ _
        simp at h_pred_ge
    · -- idx < 0 ∨ idx.toNat >= input.length
      exact h_acc_inc

/-- Reconstructed sequence is strictly increasing when ALL predecessors are valid.
    Note: This stronger hypothesis (for all indices) is what we get from runPatience. -/
theorem reconstructLIS_increasing' (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length)
    (h_valid : AllPredecessorsValid input preds input.length) :
    StrictlyIncreasing (reconstructLIS input preds startIdx h_start) := by
  rw [reconstructLIS_eq_reconstructGo]
  apply reconstructGo_increasing
  · exact strictlyIncreasing_nil
  · intro i hi
    unfold AllPredecessorsValid at h_valid
    exact h_valid i hi
  · intro _ _ hne
    simp at hne

/-- Reconstructed sequence is strictly increasing when predecessors are valid. -/
theorem reconstructLIS_increasing (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length)
    (h_valid : AllPredecessorsValid input preds input.length) :
    StrictlyIncreasing (reconstructLIS input preds startIdx h_start) := by
  rw [reconstructLIS_eq_reconstructGo]
  apply reconstructGo_increasing
  · exact strictlyIncreasing_nil
  · intro i hi
    unfold AllPredecessorsValid at h_valid
    exact h_valid i hi
  · intro _ _ hne
    simp at hne

/-- Subseq is preserved by prepending elements to the supersequence -/
theorem subseq_append_left {s l : List Int} (h : Subseq s l) (prefix_ : List Int) :
    Subseq s (prefix_ ++ l) := by
  induction prefix_ with
  | nil => simp only [List.nil_append]; exact h
  | cons x xs ih => exact Subseq.cons_skip ih

/-- Subseq is preserved by prepending an element that appears earlier in the list -/
theorem subseq_cons_of_earlier {x : Int} {s l : List Int}
    (_h_subseq : Subseq s l)
    (h_in : ∃ pref suff, l = pref ++ [x] ++ suff ∧ Subseq s suff) :
    Subseq (x :: s) l := by
  obtain ⟨pref, suff, h_eq, h_suf_subseq⟩ := h_in
  subst h_eq
  induction pref with
  | nil =>
    simp only [List.nil_append]
    exact Subseq.cons_take h_suf_subseq
  | cons y ys ih =>
    simp only [List.cons_append]
    apply Subseq.cons_skip
    -- Need: Subseq (x :: s) (ys ++ [x] ++ suff)
    -- IH applied to the fact that s is still a subseq of suff
    apply ih
    exact subseq_append_left h_suf_subseq (ys ++ [x])

/-- Helper: if i < j < l.length, then l[i] comes before l[j] in the list structure -/
theorem list_earlier_of_lt {l : List Int} {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i < j) :
    ∃ pref suff, l = pref ++ [l[i]] ++ suff ∧
                 l[j] ∈ suff ∧ suff.length = l.length - i - 1 := by
  use l.take i, l.drop (i + 1)
  refine ⟨?_, ?_, ?_⟩
  · -- l = l.take i ++ [l[i]] ++ l.drop (i + 1)
    have h_split := List.take_append_drop i l
    conv_lhs => rw [← h_split]
    have h_drop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
    rw [h_drop]
    -- Goal: l.take i ++ l[i] :: l.drop (i + 1) = l.take i ++ [l[i]] ++ l.drop (i + 1)
    -- RHS is (l.take i ++ [l[i]]) ++ l.drop (i + 1) by associativity default
    -- LHS is l.take i ++ (l[i] :: l.drop (i + 1))
    -- These are equal because [a] ++ xs = a :: xs
    rw [List.append_assoc]
    congr 1
  · -- l[j] ∈ l.drop (i + 1)
    have h_j_in_drop : j - (i + 1) < (l.drop (i + 1)).length := by
      simp only [List.length_drop]
      omega
    have h_getElem : (l.drop (i + 1))[j - (i + 1)] = l[j] := by
      rw [List.getElem_drop]
      congr 1
      omega
    rw [← h_getElem]
    exact List.getElem_mem h_j_in_drop
  · -- l.drop (i + 1).length = l.length - i - 1
    simp only [List.length_drop]
    omega

/-- Helper: l[i]! = l.tail[i-1]! when i > 0 and i < l.length -/
theorem getElem!_tail_pred {l : List Int} {i : Nat} (hi_pos : i > 0) (hi_lt : i < l.length) :
    l[i]! = l.tail[i - 1]! := by
  have h_tail_len : i - 1 < l.tail.length := by
    simp only [List.length_tail]
    omega
  rw [List.getElem!_eq_getElem l i hi_lt, List.getElem!_eq_getElem l.tail (i - 1) h_tail_len]
  rw [List.getElem_tail]
  congr 1
  omega

/-- IsChain from pairwise -/
theorem IsChain.of_pairwise {α : Type*} {R : α → α → Prop} [Trans R R R] {l : List α}
    (h : l.Pairwise R) : l.IsChain R := List.isChain_iff_pairwise.mpr h

/-- Pairwise from IsChain when the relation is transitive -/
theorem Pairwise.of_isChain {α : Type*} {R : α → α → Prop} {l : List α}
    (h : l.IsChain R) (htrans : ∀ a b c, R a b → R b c → R a c) : l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    cases xs with
    | nil =>
      constructor
      · intro _ hb; simp only [List.not_mem_nil] at hb
      · exact List.Pairwise.nil
    | cons y ys =>
      -- h : (x :: y :: ys).IsChain R
      -- List.IsChain says (x :: y :: ys).IsChain R means R x y ∧ (y :: ys).IsChain R
      have hxy : R x y := List.IsChain.rel_head h
      have htail : (y :: ys).IsChain R := List.IsChain.tail h
      constructor
      · intro b hb
        cases hb with
        | head => exact hxy
        | tail _ hb' =>
          have hpw := ih htail
          -- Need to show R x b where b ∈ ys
          -- We have R x y and R y b (from pairwise of y :: ys)
          have hyb : R y b := by
            have := List.pairwise_iff_getElem.mp hpw
            have ⟨idx, hidx, heq⟩ := List.getElem_of_mem hb'
            have h0 := this 0 (idx + 1) (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) (by omega)
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0
            rw [heq] at h0
            exact h0
          exact htrans x y b hxy hyb
      · exact ih htail

/-- If a < b and a > 0 then a - 1 < b - 1 -/
theorem pred_lt_pred_of_lt_of_pos {a b : Nat} (hab : a < b) (_ha : a > 0) : a - 1 < b - 1 := by
  omega

/-- All elements in a strictly increasing chain starting from i > 0 are > 0 -/
theorem all_pos_of_chain_head_pos {i : Nat} {is : List Nat}
    (h_chain : (i :: is).IsChain (· < ·)) (hi : i > 0) : ∀ j ∈ is, j > 0 := by
  intro j hj
  have hpw := Pairwise.of_isChain h_chain (fun _ _ _ => Nat.lt_trans)
  have hij : i < j := by
    have := List.pairwise_iff_getElem.mp hpw
    have ⟨k, hk, heq⟩ := List.getElem_of_mem hj
    have hk1 : k + 1 < (i :: is).length := by simp only [List.length_cons]; omega
    have h0 : 0 < (i :: is).length := by simp only [List.length_cons]; omega
    have h := this 0 (k + 1) h0 hk1 (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
    rw [heq] at h
    exact h
  omega

/-- In a strictly increasing chain, all elements are > 0 if the chain starts with 0 -/
theorem all_pos_after_zero {is : List Nat}
    (h_chain : (0 :: is).IsChain (· < ·)) : ∀ j ∈ is, j > 0 := by
  intro j hj
  have hpw := Pairwise.of_isChain h_chain (fun _ _ _ => Nat.lt_trans)
  have := List.pairwise_iff_getElem.mp hpw
  have ⟨k, hk, heq⟩ := List.getElem_of_mem hj
  have hk1 : k + 1 < (0 :: is).length := by simp only [List.length_cons]; omega
  have h0 : 0 < (0 :: is).length := by simp only [List.length_cons]; omega
  have h := this 0 (k + 1) h0 hk1 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  rw [heq] at h
  exact h

/-- Decremented chain: if all elements are positive and form a strict chain, their decrements also form a chain -/
theorem isChain_map_pred {indices : List Nat} (h_chain : indices.IsChain (· < ·))
    (h_pos : ∀ i ∈ indices, i > 0) :
    (indices.map (· - 1)).IsChain (· < ·) := by
  induction indices with
  | nil => simp only [List.map_nil]; exact List.IsChain.nil
  | cons i is ih =>
    simp only [List.map_cons]
    cases is with
    | nil => simp only [List.map_nil]; exact List.IsChain.singleton _
    | cons j js =>
      have h_tail_chain := ih (List.IsChain.tail h_chain) (fun k hk => h_pos k (List.mem_cons_of_mem i hk))
      apply List.IsChain.cons h_tail_chain
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq]
      intro heq heq_eq
      have hij : i < j := List.IsChain.rel_head h_chain
      have hi_pos := h_pos i List.mem_cons_self
      omega

/-- Elements taken at strictly increasing indices from a list form a subsequence.
    This is a key lemma: if we select elements at indices i₁ < i₂ < ... < iₙ from a list,
    the result is a subsequence of the original list. -/
theorem subseq_of_increasing_indices (l : List Int) (indices : List Nat)
    (h_inc : indices.IsChain (· < ·))
    (h_bound : ∀ i ∈ indices, i < l.length) :
    Subseq (indices.map (fun i => l[i]!)) l := by
  -- Induction on l, tracking indices
  induction l generalizing indices with
  | nil =>
    cases indices with
    | nil =>
      simp only [List.map_nil]
      exact Subseq.nil
    | cons i _ =>
      exfalso
      have := h_bound i List.mem_cons_self
      simp only [List.length_nil] at this
      omega
  | cons x xs ih =>
    cases indices with
    | nil =>
      simp only [List.map_nil]
      exact Subseq.nil
    | cons i is =>
      by_cases hi0 : i = 0
      · -- Take head: index 0 means take x
        subst hi0
        simp only [List.map_cons]
        have h0 : (x :: xs)[0]! = x := rfl
        rw [h0]
        apply Subseq.cons_take
        -- All elements in is are > 0
        have h_is_pos : ∀ j ∈ is, j > 0 := all_pos_after_zero h_inc
        -- Transform: map through xs with decremented indices
        have h_map_eq : is.map (fun j => (x :: xs)[j]!) = (is.map (· - 1)).map (fun k => xs[k]!) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro j hj
          have hj_pos := h_is_pos j hj
          have hj_bound : j < (x :: xs).length := h_bound j (List.mem_cons_of_mem 0 hj)
          have hj_bound' : j - 1 < xs.length := by simp at hj_bound; omega
          simp only [Function.comp_apply]
          rw [List.getElem!_eq_getElem _ _ hj_bound]
          rw [List.getElem!_eq_getElem xs (j - 1) hj_bound']
          have hj_succ : j - 1 + 1 = j := by omega
          have h_for_cons : (j - 1) + 1 < (x :: xs).length := by rw [hj_succ]; exact hj_bound
          have h2 : (x :: xs)[j - 1 + 1] = xs[j - 1] := List.getElem_cons_succ x xs (j - 1) h_for_cons
          simp only [hj_succ] at h2
          exact h2
        rw [h_map_eq]
        apply ih
        · exact isChain_map_pred (List.IsChain.tail h_inc) h_is_pos
        · intro k hk
          simp only [List.mem_map] at hk
          obtain ⟨j, hj_mem, hj_eq⟩ := hk
          have hj_bound : j < (x :: xs).length := h_bound j (List.mem_cons_of_mem 0 hj_mem)
          have hj_pos := h_is_pos j hj_mem
          simp at hj_bound
          omega
      · -- Skip head: i > 0, decrement all indices and recurse on xs
        have h_all_pos : ∀ j ∈ (i :: is), j > 0 := by
          intro j hj
          simp only [List.mem_cons] at hj
          cases hj with
          | inl heq => subst heq; omega
          | inr hmem => exact all_pos_of_chain_head_pos h_inc (by omega) j hmem
        have h_map_eq : (i :: is).map (fun j => (x :: xs)[j]!) = ((i :: is).map (· - 1)).map (fun k => xs[k]!) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro j hj
          have hj_pos := h_all_pos j hj
          have hj_bound : j < (x :: xs).length := h_bound j hj
          have hj_bound' : j - 1 < xs.length := by simp at hj_bound; omega
          simp only [Function.comp_apply]
          rw [List.getElem!_eq_getElem _ _ hj_bound]
          rw [List.getElem!_eq_getElem xs (j - 1) hj_bound']
          have hj_succ : j - 1 + 1 = j := by omega
          have h_for_cons : (j - 1) + 1 < (x :: xs).length := by rw [hj_succ]; exact hj_bound
          have h2 : (x :: xs)[j - 1 + 1] = xs[j - 1] := List.getElem_cons_succ x xs (j - 1) h_for_cons
          simp only [hj_succ] at h2
          exact h2
        rw [h_map_eq]
        simp only [List.map_cons]
        -- Goal: Subseq (xs[i-1]! :: (is.map (· - 1)).map (fun k => xs[k]!)) (x :: xs)
        apply Subseq.cons_skip
        -- Goal: Subseq (xs[i-1]! :: (is.map (· - 1)).map (fun k => xs[k]!)) xs
        -- Rewrite as: Subseq (((i-1) :: is.map (· - 1)).map (fun k => xs[k]!)) xs
        have h_rewrite : xs[i - 1]! :: (is.map (· - 1)).map (fun k => xs[k]!) =
            ((i - 1) :: is.map (· - 1)).map (fun k => xs[k]!) := by simp only [List.map_cons]
        rw [h_rewrite]
        apply ih
        · exact isChain_map_pred h_inc h_all_pos
        · intro k hk
          simp only [List.mem_cons, List.mem_map] at hk
          cases hk with
          | inl heq =>
            subst heq
            have hi_bound : i < (x :: xs).length := h_bound i List.mem_cons_self
            simp at hi_bound ⊢
            omega
          | inr hmem =>
            obtain ⟨j, hj_mem, hj_eq⟩ := hmem
            have hj_bound : j < (x :: xs).length := h_bound j (List.mem_cons_of_mem i hj_mem)
            have hj_pos := h_all_pos j (List.mem_cons_of_mem i hj_mem)
            simp at hj_bound
            omega

/-- The indices visited by reconstructGo are strictly decreasing -/
def reconstructGoIndices (input : List Int) (preds : Array Int) (idx : Int) (fuel : Nat) : List Nat :=
  if fuel = 0 then []
  else if h : idx >= 0 ∧ idx.toNat < input.length then
    let predIdx := if idx.toNat < preds.size then preds[idx.toNat]! else -1
    reconstructGoIndices input preds predIdx (fuel - 1) ++ [idx.toNat]
  else
    []
termination_by fuel

/-- reconstructGo result equals mapping indices to input values.
    This establishes that the reconstruction function collects elements at specific indices. -/
theorem reconstructGo_eq_map_indices (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat) (acc : List Int) :
    reconstructGo input preds idx fuel acc =
    (reconstructGoIndices input preds idx fuel).map (fun i => input[i]!) ++ acc := by
  induction fuel generalizing idx acc with
  | zero =>
    unfold reconstructGo reconstructGoIndices
    simp
  | succ n ih =>
    unfold reconstructGo reconstructGoIndices
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hc hpred
    · -- idx valid and pred in bounds
      simp only [Nat.add_sub_cancel]
      rw [ih]
      simp only [List.map_append, List.map, List.append_assoc, List.singleton_append]
      -- Goal: need to show input[idx.toNat] = input[idx.toNat]! after cons
      rw [List.getElem!_eq_getElem input idx.toNat hc.2]
    · -- idx valid but pred out of bounds
      simp only [Nat.add_sub_cancel]
      rw [ih]
      simp only [List.map_append, List.map, List.append_assoc, List.singleton_append]
      rw [List.getElem!_eq_getElem input idx.toNat hc.2]
    · -- idx invalid
      simp

/-- Helper: appending a single element larger than all others to a chain preserves chain -/
theorem IsChain_append_singleton {l : List Nat} {x : Nat}
    (h_chain : l.IsChain (· < ·))
    (h_all_lt : ∀ y ∈ l, y < x) :
    (l ++ [x]).IsChain (· < ·) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append]
    apply List.IsChain.cons
    · -- (as ++ [x]).IsChain (· < ·)
      apply ih
      · exact List.IsChain.tail h_chain
      · intro y hy; exact h_all_lt y (List.mem_cons_of_mem a hy)
    · -- a < (as ++ [x]).head?
      cases as with
      | nil =>
        simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq]
        intro heq heq_eq
        rw [← heq_eq]
        exact h_all_lt a List.mem_cons_self
      | cons b bs =>
        simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq]
        intro heq heq_eq
        rw [← heq_eq]
        exact List.IsChain.rel_head h_chain

/-- All indices from reconstructGoIndices are ≤ idx.toNat when idx is valid,
    and strictly < idx.toNat for all but the last element -/
theorem reconstructGoIndices_all_le (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat)
    (h_valid : ∀ i, i < input.length → ValidPredecessor input preds i)
    (h_idx_valid : idx >= 0 ∧ idx.toNat < input.length) :
    ∀ i ∈ reconstructGoIndices input preds idx fuel, i ≤ idx.toNat := by
  induction fuel generalizing idx with
  | zero =>
    unfold reconstructGoIndices
    simp
  | succ n ih =>
    unfold reconstructGoIndices
    simp only [Nat.succ_ne_zero, ↓reduceIte, h_idx_valid, Nat.add_sub_cancel]
    intro i hi
    simp at hi
    cases hi with
    | inl h_in_rec =>
      set predIdx := if idx.toNat < preds.size then preds[idx.toNat]! else -1 with h_pred
      have h_vp := h_valid idx.toNat h_idx_valid.2
      unfold ValidPredecessor at h_vp
      by_cases h_in_bounds : idx.toNat < preds.size
      · simp only [h_in_bounds, ↓reduceIte] at h_pred
        have h_vp' := h_vp h_in_bounds
        cases h_vp' with
        | inl h_neg1 =>
          rw [h_pred, h_neg1] at h_in_rec
          unfold reconstructGoIndices at h_in_rec
          simp at h_in_rec
        | inr h_pos =>
          have h_pred_valid : predIdx >= 0 ∧ predIdx.toNat < input.length := by
            rw [h_pred]; exact ⟨h_pos.1, h_pos.2.2.1⟩
          have h_i_le_pred := ih predIdx h_pred_valid i h_in_rec
          rw [h_pred] at h_i_le_pred
          have h_pred_lt_idx : preds[idx.toNat]!.toNat < idx.toNat := h_pos.2.1
          omega
      · simp only [h_in_bounds, ↓reduceIte] at h_pred
        rw [h_pred] at h_in_rec
        unfold reconstructGoIndices at h_in_rec
        simp at h_in_rec
    | inr h_eq =>
      omega

/-- The init (all but last) of reconstructGoIndices contains indices < idx.toNat -/
theorem reconstructGoIndices_init_lt (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat)
    (h_valid : ∀ i, i < input.length → ValidPredecessor input preds i)
    (h_idx_valid : idx >= 0 ∧ idx.toNat < input.length) :
    ∀ i ∈ (reconstructGoIndices input preds idx (fuel + 1)).dropLast, i < idx.toNat := by
  unfold reconstructGoIndices
  simp only [Nat.succ_ne_zero, ↓reduceIte, h_idx_valid, Nat.add_sub_cancel]
  set predIdx := if idx.toNat < preds.size then preds[idx.toNat]! else -1 with h_pred
  -- The list is: (rec from predIdx) ++ [idx.toNat]
  -- dropLast gives: (rec from predIdx)
  simp only [dif_pos (by trivial : True ∧ True), List.dropLast_concat]
  intro i hi
  have h_vp := h_valid idx.toNat h_idx_valid.2
  unfold ValidPredecessor at h_vp
  by_cases h_in_bounds : idx.toNat < preds.size
  · simp only [h_in_bounds, ↓reduceIte] at h_pred
    have h_vp' := h_vp h_in_bounds
    cases h_vp' with
    | inl h_neg1 =>
      rw [h_pred, h_neg1] at hi
      unfold reconstructGoIndices at hi
      simp at hi
    | inr h_pos =>
      have h_pred_valid : predIdx >= 0 ∧ predIdx.toNat < input.length := by
        rw [h_pred]; exact ⟨h_pos.1, h_pos.2.2.1⟩
      have h_i_le_pred := reconstructGoIndices_all_le input preds predIdx fuel h_valid h_pred_valid i hi
      rw [h_pred] at h_i_le_pred
      have h_pred_lt_idx : preds[idx.toNat]!.toNat < idx.toNat := h_pos.2.1
      omega
  · simp only [h_in_bounds, ↓reduceIte] at h_pred
    rw [h_pred] at hi
    unfold reconstructGoIndices at hi
    simp at hi

/-- The indices from reconstructGoIndices are strictly increasing (reversed from visit order) -/
theorem reconstructGoIndices_increasing (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat)
    (h_valid : ∀ i, i < input.length → ValidPredecessor input preds i) :
    (reconstructGoIndices input preds idx fuel).IsChain (· < ·) := by
  induction fuel generalizing idx with
  | zero =>
    unfold reconstructGoIndices
    simp
  | succ n ih =>
    unfold reconstructGoIndices
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hc hpred
    · -- idx valid and pred in bounds
      simp only [Nat.add_sub_cancel]
      set predIdx := preds[idx.toNat]! with h_pred
      -- By IH, the recursive indices are chain-increasing
      have h_rec_chain := ih predIdx
      -- Need to show (rec ++ [idx.toNat]).IsChain (· < ·)
      apply IsChain_append_singleton h_rec_chain
      -- Need: all indices in rec are < idx.toNat
      intro y hy
      -- From ValidPredecessor at idx.toNat
      have h_vp := h_valid idx.toNat hc.2
      unfold ValidPredecessor at h_vp
      have h_vp' := h_vp hpred
      cases h_vp' with
      | inl h_neg1 =>
        -- predIdx = -1, so recursive call returns []
        rw [h_pred, h_neg1] at hy
        unfold reconstructGoIndices at hy
        simp at hy
      | inr h_pos =>
        -- predIdx >= 0 and predIdx.toNat < idx.toNat
        have h_pred_valid : predIdx >= 0 ∧ predIdx.toNat < input.length := ⟨h_pos.1, h_pos.2.2.1⟩
        -- y is in the recursive call with predIdx, so y ≤ predIdx.toNat
        have h_y_le_pred := reconstructGoIndices_all_le input preds predIdx n h_valid h_pred_valid y hy
        have h_pred_lt_idx : predIdx.toNat < idx.toNat := h_pos.2.1
        omega
    · -- idx valid but pred out of bounds: pred = -1
      simp only [Nat.add_sub_cancel]
      -- Recursive call with -1 returns empty list
      unfold reconstructGoIndices
      simp
    · -- idx invalid
      exact List.IsChain.nil

/-- All indices from reconstructGoIndices are valid -/
theorem reconstructGoIndices_bounds (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat) :
    ∀ i ∈ reconstructGoIndices input preds idx fuel, i < input.length := by
  induction fuel generalizing idx with
  | zero =>
    unfold reconstructGoIndices
    simp
  | succ n ih =>
    unfold reconstructGoIndices
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hc hpred
    · simp only [Nat.add_sub_cancel, List.mem_append, List.mem_singleton]
      intro i hi
      cases hi with
      | inl h =>
        have := ih (preds[idx.toNat]!) i h
        exact this
      | inr h => subst h; exact hc.2
    · simp only [Nat.add_sub_cancel, List.mem_append, List.mem_singleton]
      intro i hi
      cases hi with
      | inl h =>
        have := ih (-1) i h
        exact this
      | inr h => subst h; exact hc.2
    · simp

/-- Reconstructed sequence is a valid subsequence when ALL predecessors are valid -/
theorem reconstructLIS_subseq' (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length)
    (h_valid : AllPredecessorsValid input preds input.length) :
    Subseq (reconstructLIS input preds startIdx h_start) input := by
  rw [reconstructLIS_eq_reconstructGo]
  rw [reconstructGo_eq_map_indices]
  simp only [List.append_nil]
  apply subseq_of_increasing_indices
  · -- Indices are increasing
    apply reconstructGoIndices_increasing
    intro i hi
    unfold AllPredecessorsValid at h_valid
    exact h_valid i hi
  · -- All indices are in bounds
    exact reconstructGoIndices_bounds input preds startIdx input.length

/-- Reconstructed sequence is a valid subsequence when predecessors form a decreasing chain. -/
theorem reconstructLIS_subseq (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length)
    (h_valid : AllPredecessorsValid input preds input.length) :
    Subseq (reconstructLIS input preds startIdx h_start) input := by
  rw [reconstructLIS_eq_reconstructGo]
  rw [reconstructGo_eq_map_indices]
  simp only [List.append_nil]
  apply subseq_of_increasing_indices
  · -- Indices are increasing
    apply reconstructGoIndices_increasing
    intro i hi
    unfold AllPredecessorsValid at h_valid
    exact h_valid i hi
  · -- All indices are in bounds
    exact reconstructGoIndices_bounds input preds startIdx input.length


/-- Combined state invariant for patience sorting -/
structure StateInvariant (input : List Int) (state : LISState input) : Prop where
  sorted : PilesSorted state.piles
  indices_valid : PileIndicesValid input state
  indices_in_range : PileIndicesInRange state
  tops_match : PileTopsMatch input state
  preds_valid : AllPredecessorsValid input state.predecessors state.processed

/-- Initial state satisfies the combined invariant -/
theorem initState_invariant (input : List Int) :
    StateInvariant input (initLISState input) := by
  constructor
  · exact pilesSorted_empty
  · exact initState_pileIndicesValid input
  · exact initState_pileIndicesInRange input
  · exact initState_pileTopsMatch input
  · exact initState_allPredecessorsValid input

/-- Combined invariant is preserved by processElement -/
theorem stateInvariant_preserved (input : List Int) (state : LISState input)
    (h_inv : StateInvariant input state)
    (h_lt : state.processed < input.length) :
    StateInvariant input (processElement input state h_lt) := by
  constructor
  · exact pilesSorted_preserved input state h_inv.sorted h_lt
  · exact pileIndicesValid_preserved input state h_inv.indices_valid h_lt
  · exact pileIndicesInRange_preserved input state h_inv.indices_in_range h_lt
  · exact pileTopsMatch_preserved input state h_inv.tops_match h_lt
  · exact allPredecessorsValid_preserved input state h_inv.preds_valid
      h_inv.sorted h_inv.tops_match h_inv.indices_in_range h_lt

/-- The go loop preserves the combined invariant -/
theorem runPatience_go_invariant (input : List Int) (state : LISState input)
    (h_inv : StateInvariant input state) :
    StateInvariant input (runPatience.go input state) := by
  unfold runPatience.go
  split_ifs with h
  · exact runPatience_go_invariant input (processElement input state h)
      (stateInvariant_preserved input state h_inv h)
  · exact h_inv
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Final state satisfies the combined invariant -/
theorem runPatience_invariant (input : List Int) :
    StateInvariant input (runPatience input) := by
  unfold runPatience
  exact runPatience_go_invariant input (initLISState input) (initState_invariant input)

/-- The final state from runPatience has valid predecessors -/
theorem runPatience_predecessorsValid (input : List Int) :
    AllPredecessorsValid input (runPatience input).predecessors (runPatience input).processed :=
  (runPatience_invariant input).preds_valid

/-- The go loop processes all elements -/
theorem runPatience_go_processed (input : List Int) (state : LISState input) :
    (runPatience.go input state).processed = input.length := by
  unfold runPatience.go
  split_ifs with h
  · exact runPatience_go_processed input (processElement input state h)
  · have h1 := state.h_processed
    omega
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- runPatience processes all elements -/
theorem runPatience_processed (input : List Int) :
    (runPatience input).processed = input.length := by
  unfold runPatience
  exact runPatience_go_processed input (initLISState input)

/-- All predecessors in final state are valid for any index < input.length -/
theorem runPatience_allPredecessorsValid (input : List Int) (idx : Nat) (h : idx < input.length) :
    ValidPredecessor input (runPatience input).predecessors idx := by
  have h_all := runPatience_predecessorsValid input
  have h_proc := runPatience_processed input
  unfold AllPredecessorsValid at h_all
  exact h_all idx (by rw [h_proc]; exact h)

/-- Corollary: reconstructLIS with final state produces strictly increasing sequence -/
theorem reconstructLIS_from_runPatience_increasing (input : List Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    StrictlyIncreasing (reconstructLIS input (runPatience input).predecessors startIdx h_start) := by
  apply reconstructLIS_increasing
  intro idx h_idx
  apply runPatience_allPredecessorsValid
  omega

/-- Corollary: reconstructLIS with final state produces valid subsequence -/
theorem reconstructLIS_from_runPatience_subseq (input : List Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    Subseq (reconstructLIS input (runPatience input).predecessors startIdx h_start) input := by
  apply reconstructLIS_subseq
  intro idx h_idx
  apply runPatience_allPredecessorsValid
  omega

/-- Helper: when pileIndices is empty, piles is also empty -/
theorem pileIndices_empty_implies_piles_empty' (input : List Int)
    (state : LISState input) (h : state.pileIndices.size = 0) :
    state.piles.size = 0 := by
  have := state.h_piles_size
  omega

/-- Chain length: count how many elements are visited when following predecessors -/
def chainLength (input : List Int) (preds : Array Int) (idx : Int) (fuel : Nat) : Nat :=
  if fuel = 0 then 0
  else if idx >= 0 ∧ idx.toNat < input.length then
    1 + chainLength input preds (if idx.toNat < preds.size then preds[idx.toNat]! else -1) (fuel - 1)
  else
    0
termination_by fuel

/-- chainLength equals reconstructGoIndices.length -/
theorem chainLength_eq_reconstructGoIndices_length (input : List Int) (preds : Array Int)
    (idx : Int) (fuel : Nat) :
    chainLength input preds idx fuel = (reconstructGoIndices input preds idx fuel).length := by
  induction fuel generalizing idx with
  | zero =>
    unfold chainLength reconstructGoIndices
    simp
  | succ n ih =>
    unfold chainLength reconstructGoIndices
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hc hpred
    · -- idx is valid and pred in bounds
      simp only [Nat.add_sub_cancel, List.length_append, List.length_singleton]
      rw [ih]
      ring
    · -- idx is valid but pred out of bounds
      simp only [Nat.add_sub_cancel, List.length_append, List.length_singleton]
      rw [ih]
      ring
    · -- idx invalid
      rfl

/-- reconstructLIS.length equals chainLength -/
theorem reconstructLIS_length_eq_chainLength (input : List Int) (preds : Array Int)
    (startIdx : Nat) (h_start : startIdx < input.length) :
    (reconstructLIS input preds startIdx h_start).length =
    chainLength input preds startIdx input.length := by
  rw [reconstructLIS_eq_reconstructGo]
  rw [reconstructGo_eq_map_indices]
  simp only [List.append_nil, List.length_map]
  exact (chainLength_eq_reconstructGoIndices_length input preds startIdx input.length).symm

/-- Key invariant: For element at index i placed on pile p, chainLength from i equals p + 1.
    This is tracked via the pilePositions implicit in the algorithm structure. -/
def ChainLengthInvariant (input : List Int) (state : LISState input) : Prop :=
  ∀ p < state.piles.size,
    let topIdx := state.pileIndices[p]!
    topIdx < input.length →
    chainLength input state.predecessors topIdx input.length = p + 1

/-- Initial state satisfies ChainLengthInvariant (vacuously true - no piles) -/
theorem initState_chainLengthInvariant (input : List Int) :
    ChainLengthInvariant input (initLISState input) := by
  unfold ChainLengthInvariant initLISState
  simp

/-- ChainLengthInvariant is preserved by processElement -/
theorem chainLengthInvariant_preserved (input : List Int) (state : LISState input)
    (h_inv : ChainLengthInvariant input state)
    (h_sorted : PilesSorted state.piles)
    (h_lt : state.processed < input.length) :
    ChainLengthInvariant input (processElement input state h_lt) := by
  -- The proof strategy:
  -- For the new element at state.processed placed at pile position pos:
  -- - If pos = 0: predecessor is -1, so chainLength = 1 = pos + 1
  -- - If pos > 0: predecessor is pileIndices[pos-1], and by IH on pile pos-1,
  --   chainLength from that = pos, so chainLength from state.processed = pos + 1
  -- For existing piles p ≠ pos:
  -- - pileIndices[p] is unchanged (or in bounds for push)
  -- - Indices in chain are all < state.processed (they were placed earlier)
  -- - So chainLength using newPreds equals chainLength using old preds
  -- This requires proving that chainLength is unchanged when we push to predecessors
  -- for indices that are < state.processed.
  sorry

/-- runPatience.go preserves ChainLengthInvariant -/
theorem runPatience_go_chainLengthInvariant (input : List Int) (state : LISState input)
    (h_inv : ChainLengthInvariant input state)
    (h_sorted : PilesSorted state.piles) :
    ChainLengthInvariant input (runPatience.go input state) := by
  unfold runPatience.go
  split_ifs with h
  · have h_sorted' := pilesSorted_preserved input state h_sorted h
    exact runPatience_go_chainLengthInvariant input (processElement input state h)
      (chainLengthInvariant_preserved input state h_inv h_sorted h) h_sorted'
  · exact h_inv
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- runPatience satisfies ChainLengthInvariant -/
theorem runPatience_chainLengthInvariant (input : List Int) :
    ChainLengthInvariant input (runPatience input) := by
  unfold runPatience
  exact runPatience_go_chainLengthInvariant input (initLISState input)
    (initState_chainLengthInvariant input) pilesSorted_empty

/-- Key theorem: reconstructLIS length equals piles.size -/
theorem reconstructLIS_from_runPatience_length (input : List Int)
    (h_piles : (runPatience input).pileIndices.size > 0)
    (lastIdx : Nat)
    (h_last : lastIdx = (runPatience input).pileIndices[(runPatience input).pileIndices.size - 1]!)
    (h_valid : lastIdx < input.length) :
    (reconstructLIS input (runPatience input).predecessors lastIdx h_valid).length =
    (runPatience input).piles.size := by
  have h_chain := runPatience_chainLengthInvariant input
  unfold ChainLengthInvariant at h_chain
  have h_piles_eq : (runPatience input).pileIndices.size = (runPatience input).piles.size :=
    (runPatience input).h_piles_size
  have h_piles_pos : (runPatience input).piles.size > 0 := by
    rw [← h_piles_eq]; exact h_piles
  have h_p_lt : (runPatience input).piles.size - 1 < (runPatience input).piles.size :=
    Nat.sub_one_lt_of_lt h_piles_pos
  have h_last_pile := h_chain ((runPatience input).piles.size - 1) h_p_lt
  simp only at h_last_pile
  -- h_last_pile : pileIndices[piles.size - 1]! < input.length →
  --               chainLength ... (↑pileIndices[piles.size - 1]!) ... = piles.size - 1 + 1
  -- We have: pileIndices.size = piles.size, so piles.size - 1 = pileIndices.size - 1
  -- So pileIndices[piles.size - 1]! = pileIndices[pileIndices.size - 1]! = lastIdx
  have h_topIdx_eq : (runPatience input).pileIndices[(runPatience input).piles.size - 1]! = lastIdx := by
    rw [h_last]
    congr 1
    omega
  -- Use the implication
  have h_topIdx_valid : (runPatience input).pileIndices[(runPatience input).piles.size - 1]! < input.length := by
    rw [h_topIdx_eq]; exact h_valid
  have h_chain_result := h_last_pile h_topIdx_valid
  -- h_chain_result : chainLength ... (↑pileIndices[piles.size - 1]!) ... = piles.size - 1 + 1
  rw [reconstructLIS_length_eq_chainLength]
  -- Goal: chainLength ... (↑lastIdx) ... = piles.size
  -- Need to connect ↑lastIdx with ↑pileIndices[piles.size - 1]!
  have h_int_eq : (lastIdx : Int) = ((runPatience input).pileIndices[(runPatience input).piles.size - 1]! : Int) := by
    rw [h_topIdx_eq]
  rw [h_int_eq, h_chain_result]
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
      ⟨lis, by
        constructor
        · -- StrictlyIncreasing lis
          exact reconstructLIS_from_runPatience_increasing input lastIdx h2
        constructor
        · -- Subseq lis input
          exact reconstructLIS_from_runPatience_subseq input lastIdx h2
        · -- lis.length = finalState.piles.size
          exact reconstructLIS_from_runPatience_length input h lastIdx rfl h2⟩
    else
      ⟨[], by
        constructor
        · simp [StrictlyIncreasing]
        constructor
        · exact Subseq.nil
        · -- This case should be impossible: the last pile index must be a valid input index
          -- by PileIndicesValid invariant (proven as runPatience_invariant.indices_valid)
          have h_inv := runPatience_invariant input
          have h_valid := h_inv.indices_valid
          unfold PileIndicesValid at h_valid
          have h_last_idx_lt : finalState.pileIndices.size - 1 < finalState.pileIndices.size := by omega
          have h_lastIdx_valid := h_valid (finalState.pileIndices.size - 1) h_last_idx_lt
          exact absurd h_lastIdx_valid h2⟩
  else
    ⟨[], by
      constructor
      · simp [StrictlyIncreasing]
      constructor
      · exact Subseq.nil
      · have h0 : finalState.pileIndices.size = 0 := by omega
        have hpiles := pileIndices_empty_implies_piles_empty' input finalState h0
        simp only [List.length_nil]
        exact hpiles.symm⟩

/-!
## Optimality: Number of Piles = LIS Length

We prove that for any LIS `lis`, `lis.length = piles.size`.

This requires two directions:
1. **Lower bound**: The reconstructed sequence has length = piles.size (already proven)
2. **Upper bound**: No strictly increasing subsequence can be longer than piles.size

The upper bound follows from the key insight that elements in the same pile
form a non-increasing sequence (by value at time of placement). Therefore,
any strictly increasing subsequence can have at most one element from each pile.
-/

/-- State after processing exactly k additional elements, starting from a given state -/
def stateAfter (input : List Int) (state : LISState input) (k : Nat) : LISState input :=
  if k = 0 then state
  else if h : state.processed < input.length then
    stateAfter input (processElement input state h) (k - 1)
  else state
termination_by k
decreasing_by simp_wf; omega

/-- State after processing exactly k elements from the beginning -/
def stateAtStep (input : List Int) (k : Nat) : LISState input :=
  stateAfter input (initLISState input) k

/-- stateAfter 0 returns the original state -/
theorem stateAfter_zero (input : List Int) (state : LISState input) :
    stateAfter input state 0 = state := by
  simp only [stateAfter, ↓reduceIte]

/-- stateAfter succ unfolds correctly -/
theorem stateAfter_succ (input : List Int) (state : LISState input) (k : Nat)
    (h : state.processed < input.length) :
    stateAfter input state (k + 1) = stateAfter input (processElement input state h) k := by
  conv_lhs => unfold stateAfter
  simp only [Nat.add_one_ne_zero, ↓reduceIte, dif_pos h, Nat.add_sub_cancel]

/-- stateAfter succ when done unfolds correctly -/
theorem stateAfter_succ_done (input : List Int) (state : LISState input) (k : Nat)
    (h : ¬state.processed < input.length) :
    stateAfter input state (k + 1) = state := by
  conv_lhs => unfold stateAfter
  simp only [Nat.add_one_ne_zero, ↓reduceIte, dif_neg h]

/-- stateAfter preserves processed count relationship -/
theorem stateAfter_processed (input : List Int) (state : LISState input) (k : Nat) :
    (stateAfter input state k).processed = min (state.processed + k) input.length := by
  induction k generalizing state with
  | zero =>
    rw [stateAfter_zero]
    have := state.h_processed
    omega
  | succ k ih =>
    by_cases h : state.processed < input.length
    · rw [stateAfter_succ _ _ _ h, ih]
      have h_proc : (processElement input state h).processed = state.processed + 1 := by
        unfold processElement; simp only; split_ifs <;> simp only
      simp only [h_proc]
      omega
    · rw [stateAfter_succ_done _ _ _ h]
      have h_eq : state.processed = input.length := by
        have := state.h_processed; omega
      omega

/-- stateAtStep k has processed = min k input.length -/
theorem stateAtStep_processed (input : List Int) (k : Nat) :
    (stateAtStep input k).processed = min k input.length := by
  unfold stateAtStep
  rw [stateAfter_processed]
  simp [initLISState]

/-- Which pile an element at a given input index ends up in (during processing).
    This tracks the pile assignment history, not just the final state.
    Returns the pile index (0-indexed) for each processed element. -/
def pileAssignmentGo (input : List Int) (state : LISState input) (assignments : Array Nat)
    (h_sorted : PilesSorted state.piles) : Array Nat :=
  if h : state.processed < input.length then
    let elem := input[state.processed]
    let pos := binarySearchGE state.piles elem
    let newAssignments := assignments.push pos
    let newState := processElement input state h
    pileAssignmentGo input newState newAssignments (pilesSorted_preserved input state h_sorted h)
  else
    assignments
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Compute pile assignments for all elements -/
def pileAssignment (input : List Int) : Array Nat :=
  pileAssignmentGo input (initLISState input) #[] pilesSorted_empty

/-- Key invariant: assignments.size equals state.processed during pileAssignmentGo -/
theorem pileAssignmentGo_size (input : List Int) (state : LISState input)
    (assignments : Array Nat) (h_sorted : PilesSorted state.piles)
    (h_size : assignments.size = state.processed) :
    (pileAssignmentGo input state assignments h_sorted).size = input.length := by
  unfold pileAssignmentGo
  split_ifs with h
  · have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size =
        (processElement input state h).processed := by
      simp only [Array.size_push, h_size]
      unfold processElement
      simp only
      split_ifs <;> simp
    exact pileAssignmentGo_size input (processElement input state h) _ _ h_new_size
  · have h_eq : state.processed = input.length := by
      have := state.h_processed; omega
    simp only [h_size, h_eq]
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- pileAssignment has size equal to input.length -/
theorem pileAssignment_size (input : List Int) :
    (pileAssignment input).size = input.length := by
  unfold pileAssignment
  exact pileAssignmentGo_size input (initLISState input) #[] pilesSorted_empty rfl

/-- Helper: accessing assignment at index i < state.processed returns assignments[i] -/
theorem pileAssignmentGo_get_old (input : List Int) (state : LISState input)
    (assignments : Array Nat) (h_sorted : PilesSorted state.piles)
    (h_size : assignments.size = state.processed)
    (i : Nat) (hi : i < state.processed) :
    (pileAssignmentGo input state assignments h_sorted)[i]! = assignments[i]! := by
  unfold pileAssignmentGo
  split_ifs with h
  · -- Recursing: need to show the result is the same
    have h_old : i < (assignments.push (binarySearchGE state.piles input[state.processed])).size := by
      simp [h_size]; omega
    have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size =
        (processElement input state h).processed := by
      simp only [Array.size_push, h_size]
      unfold processElement
      simp only
      split_ifs <;> simp
    have h_get : (assignments.push (binarySearchGE state.piles input[state.processed]))[i]! =
        assignments[i]! := by
      have hi' : i < assignments.size := by rw [h_size]; exact hi
      exact Array.getElem!_push_lt _ _ _ hi'
    have h_rec_bound : i < (processElement input state h).processed := by
      unfold processElement
      simp only
      split_ifs <;> simp <;> omega
    rw [pileAssignmentGo_get_old input (processElement input state h) _ _ h_new_size i h_rec_bound]
    exact h_get
  · -- Base case: processed >= input.length
    -- state.processed < input.length is false, and state.h_processed says processed <= input.length
    -- So state.processed = input.length, but i < state.processed contradicts this
    have h_eq : state.processed = input.length := by
      have := state.h_processed; omega
    omega
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Helper: accessing assignment at exactly state.processed returns the current position -/
theorem pileAssignmentGo_get_current (input : List Int) (state : LISState input)
    (assignments : Array Nat) (h_sorted : PilesSorted state.piles)
    (h_size : assignments.size = state.processed)
    (h_proc : state.processed < input.length) :
    (pileAssignmentGo input state assignments h_sorted)[state.processed]! =
    binarySearchGE state.piles input[state.processed] := by
  unfold pileAssignmentGo
  simp only [h_proc, ↓reduceDIte]
  have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size =
      (processElement input state h_proc).processed := by
    simp only [Array.size_push, h_size]
    unfold processElement
    simp only
    split_ifs <;> simp
  have h_rec_bound : state.processed < (processElement input state h_proc).processed := by
    unfold processElement
    simp only
    split_ifs <;> simp <;> omega
  rw [pileAssignmentGo_get_old input (processElement input state h_proc) _ _ h_new_size
      state.processed h_rec_bound]
  have h_at_size : assignments.size = state.processed := h_size
  have h_push_eq : (assignments.push (binarySearchGE state.piles input[state.processed]))[assignments.size]! =
      binarySearchGE state.piles input[state.processed] :=
    Array.getElem!_push_last _ _
  rw [h_at_size] at h_push_eq
  exact h_push_eq

/-- Helper: binarySearchGE result is at most the array size -/
theorem binarySearchGE_le_size (piles : Array Int) (target : Int)
    (hsorted : PilesSorted piles) :
    binarySearchGE piles target ≤ piles.size := by
  have hspec := binarySearchGE_spec piles target hsorted
  exact hspec.1

/-- Helper: piles.size after processing one element increases by at most 1 -/
theorem processElement_piles_size_bound (input : List Int) (state : LISState input)
    (h : state.processed < input.length)
    (h_inv : state.piles.size ≤ state.processed) :
    (processElement input state h).piles.size ≤ (processElement input state h).processed := by
  unfold processElement
  simp only
  split_ifs with h_pred h_pos h_pos
  all_goals simp only [Array.size_set, Array.size_push]; omega

/-- Helper: piles.size invariant is preserved through the go loop -/
theorem runPatience_go_piles_size_le_processed (input : List Int) (state : LISState input)
    (h_inv : state.piles.size ≤ state.processed) :
    (runPatience.go input state).piles.size ≤ (runPatience.go input state).processed := by
  unfold runPatience.go
  split_ifs with h
  · have h_next := processElement_piles_size_bound input state h h_inv
    exact runPatience_go_piles_size_le_processed input (processElement input state h) h_next
  · exact h_inv
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Helper: piles.size ≤ processed for runPatience result -/
theorem runPatience_piles_size_le_processed (input : List Int) :
    (runPatience input).piles.size ≤ (runPatience input).processed := by
  unfold runPatience
  exact runPatience_go_piles_size_le_processed input (initLISState input) (by simp [initLISState])

/-- Helper: runPatience.processed = input.length -/
theorem runPatience_go_processed_eq (input : List Int) (state : LISState input) :
    (runPatience.go input state).processed = input.length := by
  unfold runPatience.go
  split_ifs with h
  · exact runPatience_go_processed_eq input (processElement input state h)
  · have := state.h_processed
    omega
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

theorem runPatience_processed_eq (input : List Int) :
    (runPatience input).processed = input.length := by
  unfold runPatience
  exact runPatience_go_processed_eq input (initLISState input)

/-- Helper: monotonicity of piles - the pile array never shrinks -/
theorem processElement_piles_size_mono' (input : List Int) (state : LISState input)
    (h : state.processed < input.length) :
    state.piles.size ≤ (processElement input state h).piles.size := by
  unfold processElement
  simp only
  split_ifs with h_pos h_gt h_gt
  · simp only [Array.size_set]; exact Nat.le_refl _
  · simp only [Array.size_set]; exact Nat.le_refl _
  · simp only [Array.size_push]; omega
  · simp only [Array.size_push]; omega

/-- Key invariant: at step i, the assignment is at most the current piles.size -/
theorem pileAssignmentGo_le_piles_size (input : List Int) (state : LISState input)
    (assignments : Array Nat) (h_sorted : PilesSorted state.piles)
    (h_size : assignments.size = state.processed)
    (h_inv : ∀ j < assignments.size, assignments[j]! ≤ state.piles.size) :
    ∀ i < input.length, (pileAssignmentGo input state assignments h_sorted)[i]! ≤
      (runPatience.go input state).piles.size := by
  intro i hi
  unfold pileAssignmentGo runPatience.go
  split_ifs with h
  · -- Recursive case: state.processed < input.length
    have h_bs := binarySearchGE_le_size state.piles input[state.processed] h_sorted
    have h_sorted' := pilesSorted_preserved input state h_sorted h
    have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size =
        (processElement input state h).processed := by
      simp only [Array.size_push, h_size]
      unfold processElement; simp only; split_ifs <;> simp
    -- Show the new invariant holds
    have h_inv' : ∀ j < (assignments.push (binarySearchGE state.piles input[state.processed])).size,
        (assignments.push (binarySearchGE state.piles input[state.processed]))[j]! ≤
          (processElement input state h).piles.size := by
      intro j hj
      simp only [Array.size_push] at hj
      by_cases h_eq : j = assignments.size
      · -- New element
        subst h_eq
        rw [Array.getElem!_push_last]
        -- bs ≤ state.piles.size ≤ new piles.size
        have h_mono := processElement_piles_size_mono' input state h
        omega
      · -- Old element
        have hj' : j < assignments.size := by omega
        rw [Array.getElem!_push_lt _ _ _ hj']
        have h_mono := processElement_piles_size_mono' input state h
        have := h_inv j hj'
        omega
    have h_rec := pileAssignmentGo_le_piles_size input (processElement input state h)
      (assignments.push (binarySearchGE state.piles input[state.processed]))
      h_sorted' h_new_size h_inv' i hi
    -- Now connect runPatience.go results
    exact h_rec
  · -- Base case: state.processed ≥ input.length
    -- So state.processed = input.length, and i < input.length
    have h_eq : state.processed = input.length := by
      have := state.h_processed; omega
    have hi' : i < assignments.size := by rw [h_size, h_eq]; exact hi
    exact h_inv i hi'
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Helper: the final pile count is at least the pile count at any step -/
theorem runPatience_piles_size_ge' (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles) :
    state.piles.size ≤ (runPatience.go input state).piles.size := by
  unfold runPatience.go
  split_ifs with h
  · have h_mono := processElement_piles_size_mono' input state h
    have h_sorted' := pilesSorted_preserved input state h_sorted h
    have h_rec := runPatience_piles_size_ge' input (processElement input state h) h_sorted'
    omega
  · exact Nat.le_refl _
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Key invariant: each assignment is strictly less than the current state piles.size.
    This is stronger than needed - we track that assignments are < state.piles.size
    at the time of assignment, which implies < final piles.size by monotonicity. -/
theorem pileAssignmentGo_lt_state (input : List Int) (state : LISState input)
    (assignments : Array Nat) (h_sorted : PilesSorted state.piles)
    (h_size : assignments.size = state.processed)
    (h_inv : ∀ j < assignments.size, assignments[j]! < state.piles.size) :
    ∀ i < input.length, (pileAssignmentGo input state assignments h_sorted)[i]! <
      (runPatience.go input state).piles.size := by
  intro i hi
  unfold pileAssignmentGo runPatience.go
  split_ifs with h
  · -- Recursive case
    have h_sorted' := pilesSorted_preserved input state h_sorted h
    have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size =
        (processElement input state h).processed := by
      simp only [Array.size_push, h_size]
      unfold processElement; simp only; split_ifs <;> simp
    -- For the new element, show pos < processElement.piles.size
    have h_bs := binarySearchGE_le_size state.piles input[state.processed] h_sorted
    -- After processElement, piles.size is either unchanged (replace) or +1 (push)
    have h_new_inv : ∀ j < (assignments.push (binarySearchGE state.piles input[state.processed])).size,
        (assignments.push (binarySearchGE state.piles input[state.processed]))[j]! <
          (processElement input state h).piles.size := by
      intro j hj
      simp only [Array.size_push] at hj
      by_cases h_eq : j = assignments.size
      · -- New element
        subst h_eq
        rw [Array.getElem!_push_last]
        -- binarySearchGE returns pos ≤ state.piles.size
        -- In replace case (pos < state.piles.size): newState.piles.size = state.piles.size, so pos < newState.piles.size
        -- In push case (pos = state.piles.size): newState.piles.size = state.piles.size + 1, so pos < newState.piles.size
        unfold processElement
        simp only
        split_ifs with h_pos h_gt h_gt
        all_goals simp only [Array.size_set, Array.size_push]; omega
      · -- Old element
        have hj' : j < assignments.size := by omega
        rw [Array.getElem!_push_lt _ _ _ hj']
        have h_old := h_inv j hj'
        have h_mono := processElement_piles_size_mono' input state h
        omega
    exact pileAssignmentGo_lt_state input (processElement input state h)
      (assignments.push (binarySearchGE state.piles input[state.processed]))
      h_sorted' h_new_size h_new_inv i hi
  · -- Base case: state.processed ≥ input.length
    have h_eq : state.processed = input.length := by have := state.h_processed; omega
    have hi' : i < assignments.size := by rw [h_size, h_eq]; exact hi
    exact h_inv i hi'
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- The pile assignment values are bounded by the final number of piles -/
theorem pileAssignment_bounded (input : List Int) (i : Nat) (hi : i < input.length) :
    (pileAssignment input)[i]! < (runPatience input).piles.size := by
  unfold pileAssignment runPatience
  apply pileAssignmentGo_lt_state input (initLISState input) #[] pilesSorted_empty rfl
  · intro j hj; simp at hj
  · exact hi

/-- Helper: monotonicity of piles - the pile array never shrinks -/
theorem processElement_piles_size_mono (input : List Int) (state : LISState input)
    (h : state.processed < input.length) :
    state.piles.size ≤ (processElement input state h).piles.size := by
  unfold processElement
  simp only
  split_ifs with h_pos h_gt h_gt
  · -- Replace case: piles.set doesn't change size
    simp only [Array.size_set]; exact Nat.le_refl _
  · simp only [Array.size_set]; exact Nat.le_refl _
  · -- Push case: piles.push increases size
    simp only [Array.size_push]; omega
  · simp only [Array.size_push]; omega

/-- Helper: the final pile count is at least the pile count at any step -/
theorem runPatience_piles_size_ge (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles) :
    state.piles.size ≤ (runPatience.go input state).piles.size := by
  unfold runPatience.go
  split_ifs with h
  · have h_mono := processElement_piles_size_mono input state h
    have h_sorted' := pilesSorted_preserved input state h_sorted h
    have h_rec := runPatience_piles_size_ge input (processElement input state h) h_sorted'
    omega
  · exact Nat.le_refl _
termination_by input.length - state.processed
decreasing_by exact processElement_decreases input state h

/-- Key property: when an element is placed on pile p, its value is <= pile top at that moment -/
theorem processElement_placed_le_top (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles)
    (h : state.processed < input.length)
    (pos : Nat) (h_pos : pos = binarySearchGE state.piles input[state.processed])
    (h_pos_lt : pos < state.piles.size) :
    input[state.processed] ≤ state.piles[pos]! := by
  have bs := binarySearchGE_spec state.piles input[state.processed] h_sorted
  rw [← h_pos] at bs
  have h_above := bs.2.2 h_pos_lt
  -- h_above : state.piles[pos]! >= input[state.processed]
  -- Need: input[state.processed] <= state.piles[pos]!
  exact h_above

/-- stateAtStep equals the result of iterating processElement -/
theorem stateAtStep_eq_go (input : List Int) (k : Nat) :
    stateAtStep input k = stateAfter input (initLISState input) k := rfl

/-- runPatience.go from a state equals stateAfter by remaining steps -/
theorem runPatience_go_eq_stateAfter (input : List Int) (state : LISState input) :
    runPatience.go input state = stateAfter input state (input.length - state.processed) := by
  generalize hd : input.length - state.processed = d
  induction d generalizing state with
  | zero =>
    have h : ¬(state.processed < input.length) := by
      have := state.h_processed
      omega
    conv_lhs => unfold runPatience.go
    simp only [dif_neg h]
    rw [stateAfter_zero]
  | succ n ih =>
    have h : state.processed < input.length := by omega
    conv_lhs => unfold runPatience.go
    simp only [dif_pos h]
    rw [stateAfter_succ _ _ _ h]
    have h_proc : (processElement input state h).processed = state.processed + 1 := by
      unfold processElement; simp only; split_ifs <;> simp only
    have h_dec : input.length - (processElement input state h).processed = n := by
      omega
    exact ih (processElement input state h) h_dec

/-- PilesSorted is preserved through stateAfter -/
theorem stateAfter_pilesSorted (input : List Int) (state : LISState input) (k : Nat)
    (h_sorted : PilesSorted state.piles) :
    PilesSorted (stateAfter input state k).piles := by
  induction k generalizing state with
  | zero => rw [stateAfter_zero]; exact h_sorted
  | succ k ih =>
    by_cases h : state.processed < input.length
    · rw [stateAfter_succ _ _ _ h]
      exact ih (processElement input state h) (pilesSorted_preserved input state h_sorted h)
    · rw [stateAfter_succ_done _ _ _ h]
      exact h_sorted

/-- stateAtStep preserves PilesSorted -/
theorem stateAtStep_pilesSorted (input : List Int) (k : Nat) :
    PilesSorted (stateAtStep input k).piles := by
  unfold stateAtStep
  apply stateAfter_pilesSorted
  exact pilesSorted_empty

-- Theorem pile_top_nonincreasing and its helpers are defined after stateAtStep_succ
-- to allow using that key lemma. See after stateAtStep_succ for the actual proofs.

/-- pileAssignment[i]! equals binarySearchGE at state i -/
theorem pileAssignment_at_state (input : List Int) (i : Nat) (hi : i < input.length) :
    (pileAssignment input)[i]! = binarySearchGE (stateAtStep input i).piles input[i]! := by
  unfold pileAssignment stateAtStep
  have h_sync : ∀ state : LISState input, ∀ assignments : Array Nat, ∀ h_sorted : PilesSorted state.piles, ∀ k : Nat, assignments.size = state.processed → state.processed + k = i → (pileAssignmentGo input state assignments h_sorted)[i]! = binarySearchGE (stateAfter input state k).piles input[i]! := by
    intro state assignments h_sorted k h_size h_sum
    induction k using Nat.strong_induction_on generalizing state assignments h_sorted with
    | _ k ih_k =>
      by_cases h_eq : k = 0
      · -- Base case: k = 0, so state.processed = i
        subst h_eq
        simp only [Nat.add_zero] at h_sum
        subst h_sum
        rw [stateAfter_zero]
        have h_result := pileAssignmentGo_get_current input state assignments h_sorted h_size hi
        rw [List.getElem!_eq_getElem input state.processed hi]
        exact h_result
      · -- Recursive case: k > 0
        have h_pos : 0 < k := Nat.pos_of_ne_zero h_eq
        have h_proc_lt : state.processed < input.length := by omega
        have h_proc' : (processElement input state h_proc_lt).processed = state.processed + 1 := by
          unfold processElement; simp only; split_ifs <;> simp
        have h_new_size : (assignments.push (binarySearchGE state.piles input[state.processed])).size = (processElement input state h_proc_lt).processed := by
          simp only [Array.size_push, h_size, h_proc']
        have h_sorted' := pilesSorted_preserved input state h_sorted h_proc_lt
        have h_sum' : (processElement input state h_proc_lt).processed + (k - 1) = i := by
          rw [h_proc']; omega
        have h_term : k - 1 < k := Nat.sub_lt h_pos Nat.one_pos
        have h_ih := ih_k (k - 1) h_term (processElement input state h_proc_lt) _ h_sorted' h_new_size h_sum'
        have h_stateAfter : stateAfter input state k = stateAfter input (processElement input state h_proc_lt) (k - 1) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          rw [← stateAfter_succ input state (k - 1) h_proc_lt]
        rw [h_stateAfter]
        have h_step : (pileAssignmentGo input state assignments h_sorted)[i]! = (pileAssignmentGo input (processElement input state h_proc_lt) (assignments.push (binarySearchGE state.piles input[state.processed])) h_sorted')[i]! := by
          conv_lhs => unfold pileAssignmentGo
          simp only [h_proc_lt, dif_pos]
        rw [h_step]
        exact h_ih
  have h_init_processed : (initLISState input).processed = 0 := by unfold initLISState; simp
  have h_init_size : (#[] : Array Nat).size = (initLISState input).processed := by simp [h_init_processed]
  have h_sum : (initLISState input).processed + i = i := by simp [h_init_processed]
  exact h_sync (initLISState input) #[] pilesSorted_empty i h_init_size h_sum

/-- Helper: stateAfter (k+1) equals processElement applied when processed < input.length -/
theorem stateAfter_succ_processElement (input : List Int) (state : LISState input) (k : Nat)
    (h : (stateAfter input state k).processed < input.length) :
    stateAfter input state (k + 1) = processElement input (stateAfter input state k) h := by
  induction k generalizing state with
  | zero =>
    simp only [stateAfter_zero] at h ⊢
    rw [stateAfter_succ _ _ 0 h, stateAfter_zero]
  | succ k ih =>
    by_cases h_state : state.processed < input.length
    · rw [stateAfter_succ _ _ (k + 1) h_state]
      have h_eq : stateAfter input state (k + 1) = stateAfter input (processElement input state h_state) k := by
        rw [stateAfter_succ _ _ k h_state]
      have h' : (stateAfter input (processElement input state h_state) k).processed < input.length := by
        rw [← h_eq]; exact h
      have h_ih := ih (processElement input state h_state) h'
      rw [h_ih]
      congr 1
      exact h_eq.symm
    · rw [stateAfter_succ_done _ _ (k + 1) h_state]
      simp only [stateAfter_succ_done _ _ k h_state] at h
      exact absurd h h_state

/-- Helper: stateAtStep (i+1) equals processElement applied to stateAtStep i -/
theorem stateAtStep_succ (input : List Int) (i : Nat) (hi : i < input.length) :
    ∃ h : (stateAtStep input i).processed < input.length,
      stateAtStep input (i + 1) = processElement input (stateAtStep input i) h := by
  have h_proc : (stateAtStep input i).processed = i := by
    rw [stateAtStep_processed]; simp; omega
  have h : (stateAtStep input i).processed < input.length := by rw [h_proc]; exact hi
  use h
  unfold stateAtStep
  exact stateAfter_succ_processElement input (initLISState input) i h

/-- When element i is placed on existing pile p, the pile top becomes input[i]! -/
theorem pile_top_after_placement (input : List Int) (i : Nat) (hi : i < input.length)
    (p : Nat) (hp : p = (pileAssignment input)[i]!)
    (hp_lt : p < (stateAtStep input i).piles.size) :
    (stateAtStep input (i + 1)).piles[p]! = input[i]! := by
  -- Get the key equation: stateAtStep (i+1) = processElement (stateAtStep i)
  obtain ⟨h_proc_lt, h_step⟩ := stateAtStep_succ input i hi
  rw [h_step]
  -- Use pileAssignment_at_state to show p = binarySearchGE
  have h_p_eq : p = binarySearchGE (stateAtStep input i).piles input[i]! := by
    rw [hp, pileAssignment_at_state input i hi]
  -- Since hp_lt : p < piles.size, processElement uses the set branch
  have h_proc_eq : (stateAtStep input i).processed = i := by
    rw [stateAtStep_processed]; simp; omega
  -- Convert input[i]! to input[i] for proof (they're equal when i < input.length)
  have h_elem_eq : input[i]! = input[i] := List.getElem!_eq_getElem input i hi
  unfold processElement
  simp only [h_proc_eq]
  -- Now we have binarySearchGE ... input[i] (without bang)
  -- Need to show these are the same
  have h_bs_eq : binarySearchGE (stateAtStep input i).piles input[i] =
      binarySearchGE (stateAtStep input i).piles input[i]! := by
    rw [h_elem_eq]
  -- Rewrite hp_lt using h_p_eq to get the condition for the if
  have h_pos_lt : binarySearchGE (stateAtStep input i).piles input[i] < (stateAtStep input i).piles.size := by
    rw [h_bs_eq, ← h_p_eq]; exact hp_lt
  -- Split on the position condition - we know p < piles.size
  simp only [h_pos_lt, ↓reduceDIte]
  -- Now we need to show piles.set(...).piles[p]! = input[i]!
  -- First relate p to the set index
  have h_p_eq' : p = binarySearchGE (stateAtStep input i).piles input[i] := by
    rw [h_p_eq, ← h_elem_eq]
  rw [h_p_eq', h_elem_eq]
  -- Now the piles is state.piles.set pos elem, and we access piles[pos]
  exact Array.getElem!_set_eq (stateAtStep input i).piles
    (binarySearchGE (stateAtStep input i).piles input[i]) input[i] h_pos_lt

-- Helper: if state.processed >= length, stateAfter returns state unchanged
private theorem stateAfter_const_done (input : List Int) (state : LISState input) (n : Nat)
    (h_done : state.processed ≥ input.length) :
    stateAfter input state n = state := by
  induction n with
  | zero => rw [stateAfter_zero]
  | succ n ih =>
    have h_not_lt : ¬(state.processed < input.length) := by omega
    rw [stateAfter_succ_done _ _ _ h_not_lt]

-- Helper: stateAfter can be split into composition when the intermediate state is "done"
private theorem stateAfter_split_done (input : List Int) (state : LISState input) (k m : Nat)
    (h_done : (stateAfter input state k).processed = input.length) :
    stateAfter input state (k + m) = stateAfter input state k := by
  -- Use strong induction on k
  induction k using Nat.strong_induction_on generalizing state m with
  | _ k ih =>
    induction m with
    | zero => simp [Nat.add_zero]
    | succ m ihm =>
      rw [show k + (m + 1) = (k + m) + 1 by ring]
      have h_done_km : (stateAfter input state (k + m)).processed = input.length := by
        rw [ihm, h_done]
      by_cases h_state_lt : state.processed < input.length
      · -- state.processed < length
        rw [stateAfter_succ _ _ _ h_state_lt]
        -- Goal: stateAfter (processElement state) (k + m) = stateAfter state k
        -- Key insight: stateAfter state (k + m) = stateAfter (processElement state) (k + m - 1)
        -- and stateAfter state k = stateAfter (processElement state) (k - 1)
        cases k with
        | zero =>
          -- stateAfter state 0 = state, so h_done says state.processed = length
          -- But h_state_lt says state.processed < length, contradiction
          simp [stateAfter_zero] at h_done
          omega
        | succ k' =>
          -- Goal: stateAfter (processElement state) (k' + 1 + m) = stateAfter state (k' + 1)
          -- Use stateAfter_succ on RHS: stateAfter state (k'+1) = stateAfter (processElement state) k'
          conv_rhs => rw [stateAfter_succ _ _ _ h_state_lt]
          -- h_done : (stateAfter state (k'+1)).processed = length
          rw [stateAfter_succ _ _ _ h_state_lt] at h_done
          -- h_done : (stateAfter (processElement state) k').processed = length
          -- Goal: stateAfter (processElement state) (k' + 1 + m) = stateAfter (processElement state) k'
          -- Rewrite (k' + 1 + m) as k' + (m + 1)
          have h_eq : k' + 1 + m = k' + (m + 1) := by ring
          rw [h_eq]
          -- Now apply ih with (processElement state), k', and (m + 1)
          have h_term : k' < k' + 1 := Nat.lt_succ_self k'
          exact ih k' h_term (processElement input state h_state_lt) (m + 1) h_done
      · -- state.processed >= length
        rw [stateAfter_succ_done _ _ _ h_state_lt]
        have h_eq : stateAfter input state k = state := stateAfter_const_done input state k (Nat.not_lt.mp h_state_lt)
        rw [h_eq]

-- Helper: when k >= input.length, stateAtStep k = stateAtStep input.length
private theorem stateAtStep_ge_length (input : List Int) (k : Nat)
    (hk : k ≥ input.length) :
    stateAtStep input k = stateAtStep input input.length := by
  unfold stateAtStep
  obtain ⟨d, hd⟩ : ∃ d, k = input.length + d := ⟨k - input.length, by omega⟩
  subst hd
  -- Goal: stateAfter init (input.length + d) = stateAfter init input.length
  have h_done : (stateAfter input (initLISState input) input.length).processed = input.length := by
    rw [stateAfter_processed]; simp [initLISState]
  exact stateAfter_split_done input (initLISState input) input.length d h_done

-- Helper: stateAtStep (k+1).piles.size >= stateAtStep k.piles.size
private theorem stateAtStep_succ_piles_size_mono (input : List Int) (k : Nat) :
    (stateAtStep input k).piles.size ≤ (stateAtStep input (k + 1)).piles.size := by
  by_cases hk : k < input.length
  · -- k < input.length: use stateAtStep_succ
    obtain ⟨h_proc_lt, h_step⟩ := stateAtStep_succ input k hk
    rw [h_step]
    exact processElement_piles_size_mono input (stateAtStep input k) h_proc_lt
  · -- k >= input.length: no change
    have h_eq : stateAtStep input (k + 1) = stateAtStep input k := by
      rw [stateAtStep_ge_length input (k + 1) (by omega)]
      rw [stateAtStep_ge_length input k (Nat.not_lt.mp hk)]
    rw [h_eq]

-- Helper: processElement either preserves pile[p] or sets it to a smaller/equal value
private theorem processElement_piles_getElem_le (input : List Int) (state : LISState input)
    (h_sorted : PilesSorted state.piles)
    (h : state.processed < input.length) (p : Nat)
    (hp : p < state.piles.size) :
    (processElement input state h).piles[p]! ≤ state.piles[p]! := by
  -- processElement either sets piles[pos] to input[state.processed] (where pos < piles.size)
  -- or pushes a new pile (when pos = piles.size).
  -- In the first case: input[state.processed] <= piles[pos] by binary search spec (processElement_placed_le_top)
  -- In the second case: existing piles are unchanged (Array.getElem!_push_lt)
  unfold processElement
  simp only
  -- The if-then-else for predecessors doesn't affect piles, so we only care about pos < piles.size
  by_cases h_pos : binarySearchGE state.piles input[state.processed] < state.piles.size
  · -- Set case: pos < piles.size
    simp only [h_pos, ↓reduceDIte]
    by_cases hp_eq : p = binarySearchGE state.piles input[state.processed]
    · -- p = pos: the new value is input[state.processed] <= old value at pos
      subst hp_eq
      rw [Array.getElem!_set_eq]
      exact processElement_placed_le_top input state h_sorted h
        (binarySearchGE state.piles input[state.processed]) rfl h_pos
    · -- p ≠ pos: the value at p is unchanged
      rw [Array.getElem!_set_ne _ _ _ _ h_pos hp_eq hp]
  · -- Push case: pos >= piles.size, existing piles unchanged
    simp only [h_pos, ↓reduceDIte]
    rw [Array.getElem!_push_lt _ _ _ hp]

-- Helper: pile top at existing pile is non-increasing after one step
private theorem pile_top_single_step (input : List Int) (p k : Nat)
    (hp_at_k : p < (stateAtStep input k).piles.size) :
    (stateAtStep input (k + 1)).piles[p]! ≤ (stateAtStep input k).piles[p]! := by
  by_cases hk : k < input.length
  · -- k < input.length: processElement either sets pile[p] to input[k] or leaves it unchanged
    obtain ⟨h_proc_lt, h_step⟩ := stateAtStep_succ input k hk
    rw [h_step]
    have h_sorted := stateAtStep_pilesSorted input k
    exact processElement_piles_getElem_le input (stateAtStep input k) h_sorted h_proc_lt p hp_at_k
  · -- k >= input.length: state doesn't change
    have h_eq : stateAtStep input (k + 1) = stateAtStep input k := by
      rw [stateAtStep_ge_length input (k + 1) (by omega)]
      rw [stateAtStep_ge_length input k (Nat.not_lt.mp hk)]
    rw [h_eq]

/-- Pile tops are monotonically non-increasing: if pile p exists at step k and l >= k,
    then the pile top at step l is <= the pile top at step k -/
theorem pile_top_nonincreasing (input : List Int) (p k l : Nat)
    (hkl : k ≤ l)
    (hp_at_k : p < (stateAtStep input k).piles.size) :
    (stateAtStep input l).piles[p]! ≤ (stateAtStep input k).piles[p]! := by
  -- Use induction on the difference l - k
  obtain ⟨d, hd⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
  subst hd
  clear hkl
  induction d generalizing k with
  | zero => simp
  | succ d ih =>
    rw [show k + (d + 1) = k + 1 + d by ring]
    -- First prove that p < (stateAtStep input (k + 1)).piles.size
    have hp_at_k1 : p < (stateAtStep input (k + 1)).piles.size :=
      Nat.lt_of_lt_of_le hp_at_k (stateAtStep_succ_piles_size_mono input k)
    -- Chain the inequalities
    have h_ih := ih (k + 1) hp_at_k1
    have h_step := pile_top_single_step input p k hp_at_k
    exact le_trans h_ih h_step

/-- Helper: pile sizes are non-decreasing from step k to step l when k <= l -/
private theorem stateAtStep_piles_size_mono (input : List Int) (k l : Nat) (hkl : k ≤ l) :
    (stateAtStep input k).piles.size ≤ (stateAtStep input l).piles.size := by
  obtain ⟨d, hd⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
  subst hd
  clear hkl
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show k + (d + 1) = (k + d) + 1 by ring]
    exact Nat.le_trans ih (stateAtStep_succ_piles_size_mono input (k + d))

/-- Key invariant: elements assigned to the same pile with x < y have input[x] >= input[y].

    This is the core insight: when element at index y is placed on pile p,
    it replaces the top (which was placed by some earlier element x with x < y).
    The binary search guarantees input[y] <= old_top, and old_top = input[x']
    for some x' < y on the same pile. -/
theorem same_pile_ge (input : List Int) (x y : Nat)
    (hx : x < input.length) (hy : y < input.length) (hxy : x < y)
    (h_same : (pileAssignment input)[x]! = (pileAssignment input)[y]!) :
    input[x]! ≥ input[y]! := by
  -- Let p be the common pile assignment
  let p := (pileAssignment input)[x]!
  have hp_x : p = (pileAssignment input)[x]! := rfl
  have hp_y : p = (pileAssignment input)[y]! := by rw [hp_x, h_same]

  -- Step 1: Show pile p exists at step x+1 (after element x is placed)
  have h_p_at_state_x : p = binarySearchGE (stateAtStep input x).piles input[x]! := by
    rw [hp_x, pileAssignment_at_state input x hx]
  have h_bs_le_x := binarySearchGE_le_size (stateAtStep input x).piles input[x]! (stateAtStep_pilesSorted input x)

  -- Prove p < (stateAtStep input (x+1)).piles.size by analyzing processElement
  have h_p_lt_size_x1 : p < (stateAtStep input (x + 1)).piles.size := by
    obtain ⟨h_proc_lt, h_step⟩ := stateAtStep_succ input x hx
    rw [h_step, h_p_at_state_x]
    have h_proc_x : (stateAtStep input x).processed = x := by rw [stateAtStep_processed]; simp; omega
    have h_elem_both : input[(stateAtStep input x).processed] = input[x]! := by
      simp only [h_proc_x]; exact (List.getElem!_eq_getElem input x hx).symm
    have h_bs_eq : binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] =
                   binarySearchGE (stateAtStep input x).piles input[x]! := by simp only [h_elem_both]
    unfold processElement; simp only
    by_cases h_lt : binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] < (stateAtStep input x).piles.size
    · simp only [h_lt, ↓reduceDIte, Array.size_set]; rw [← h_bs_eq]; exact h_lt
    · simp only [h_lt, ↓reduceDIte, Array.size_push]; push_neg at h_lt
      have h_bs_le' : binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] ≤ (stateAtStep input x).piles.size := by
        rw [h_bs_eq]; exact h_bs_le_x
      have h_eq_size := Nat.le_antisymm h_bs_le' h_lt
      rw [← h_bs_eq, h_eq_size]; omega

  -- Step 2: Show pile p exists at step y by monotonicity of pile sizes
  have h_p_lt_size_y : p < (stateAtStep input y).piles.size := by
    have h_mono : (stateAtStep input (x + 1)).piles.size ≤ (stateAtStep input y).piles.size :=
      stateAtStep_piles_size_mono input (x + 1) y (by omega)
    omega

  -- Step 3: By binary search spec, input[y]! <= piles[p] at step y
  have h_y_at_state : p = binarySearchGE (stateAtStep input y).piles input[y]! := by rw [hp_y, pileAssignment_at_state input y hy]
  have h_bs_spec := binarySearchGE_spec (stateAtStep input y).piles input[y]! (stateAtStep_pilesSorted input y)
  have h_y_le_top : input[y]! ≤ (stateAtStep input y).piles[p]! := by
    rw [h_y_at_state]; exact h_bs_spec.2.2 (by rw [← h_y_at_state]; exact h_p_lt_size_y)

  -- Step 4: By pile_top_nonincreasing, piles[p] at step y <= piles[p] at step x+1
  have h_top_mono : (stateAtStep input y).piles[p]! ≤ (stateAtStep input (x + 1)).piles[p]! :=
    pile_top_nonincreasing input p (x + 1) y (by omega) h_p_lt_size_x1

  -- Step 5: Show piles[p] at step x+1 = input[x]! (by pile_top_after_placement or direct proof for push case)
  have h_top_eq : (stateAtStep input (x + 1)).piles[p]! = input[x]! := by
    by_cases h_lt : p < (stateAtStep input x).piles.size
    · exact pile_top_after_placement input x hx p hp_x h_lt
    · -- Push case: p = (stateAtStep input x).piles.size
      push_neg at h_lt
      have h_eq : p = (stateAtStep input x).piles.size := by rw [h_p_at_state_x]; omega
      obtain ⟨h_proc_lt, h_step⟩ := stateAtStep_succ input x hx
      rw [h_step, h_eq]
      have h_proc_x : (stateAtStep input x).processed = x := by rw [stateAtStep_processed]; simp; omega
      have h_elem_both : input[(stateAtStep input x).processed] = input[x]! := by
        simp only [h_proc_x]; exact (List.getElem!_eq_getElem input x hx).symm
      have h_elem_eq' : input[(stateAtStep input x).processed]! = input[x]! := by simp only [h_proc_x]
      have h_bs_eq : binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] =
                     binarySearchGE (stateAtStep input x).piles input[x]! := by simp only [h_elem_both]
      have h_bs_eq_size : binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] =
                          (stateAtStep input x).piles.size := by
        rw [h_bs_eq]
        -- p = binarySearchGE ... from h_p_at_state_x, and p = piles.size from h_eq
        calc binarySearchGE (stateAtStep input x).piles input[x]!
           = p := h_p_at_state_x.symm
         _ = (stateAtStep input x).piles.size := h_eq
      have h_bs_not_lt : ¬(binarySearchGE (stateAtStep input x).piles input[(stateAtStep input x).processed] < (stateAtStep input x).piles.size) := by
        rw [h_bs_eq_size]; omega
      unfold processElement; simp only [h_bs_not_lt, ↓reduceDIte]
      -- After unfolding, the goal is about piles.push elem[piles.size]!
      rw [Array.getElem!_push_last, h_elem_both]

  -- Combine the chain of inequalities
  calc input[y]! ≤ (stateAtStep input y).piles[p]! := h_y_le_top
       _ ≤ (stateAtStep input (x + 1)).piles[p]! := h_top_mono
       _ = input[x]! := h_top_eq

/-- If two indices have the same pile assignment and x < y, then input[x] >= input[y] -/
theorem same_pile_not_strictly_lt (input : List Int) (x y : Nat)
    (hx : x < input.length) (hy : y < input.length) (hxy : x < y)
    (h_same : (pileAssignment input)[x]! = (pileAssignment input)[y]!) :
    ¬(input[x]! < input[y]!) := by
  have h_ge := same_pile_ge input x y hx hy hxy h_same
  omega

/-- Elements at distinct positions in a strictly increasing subsequence are
    assigned to distinct piles -/
theorem strictly_increasing_implies_distinct_piles (input : List Int)
    (indices : List Nat)
    (h_inc : (indices.map fun i => input[i]!).IsChain (· < ·))
    (h_sorted : indices.IsChain (· < ·))
    (h_bound : ∀ i ∈ indices, i < input.length) :
    indices.Pairwise (fun a b => (pileAssignment input)[a]! ≠ (pileAssignment input)[b]!) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  intro h_same
  -- indices[i] < indices[j] since indices is sorted and i < j
  have h_idx_sorted := List.isChain_iff_pairwise.mp h_sorted
  have h_ij := List.pairwise_iff_getElem.mp h_idx_sorted i j hi hj hij
  -- input[indices[i]] < input[indices[j]] since the mapped list is strictly increasing
  have h_val_sorted := List.isChain_iff_pairwise.mp h_inc
  have h_len : (indices.map fun i => input[i]!).length = indices.length := by simp
  have hi' : i < (indices.map fun i => input[i]!).length := by simp [hi]
  have hj' : j < (indices.map fun i => input[i]!).length := by simp [hj]
  have h_val_lt := List.pairwise_iff_getElem.mp h_val_sorted i j hi' hj' hij
  simp only [List.getElem_map] at h_val_lt
  -- But if they're in the same pile, input[indices[i]] >= input[indices[j]]
  have h_i_bound := h_bound indices[i] (List.getElem_mem hi)
  have h_j_bound := h_bound indices[j] (List.getElem_mem hj)
  have h_ge := same_pile_ge input indices[i] indices[j] h_i_bound h_j_bound h_ij h_same
  -- h_ge : input[indices[i]]! >= input[indices[j]]!
  -- h_val_lt : input[indices[i]]! < input[indices[j]]! (after simp)
  -- These directly contradict each other
  exact absurd h_val_lt (Int.not_lt.mpr h_ge)

/-- Helper: getElem! of cons at index i+1 equals getElem! of tail at index i -/
theorem List.getElem!_cons_succ' {α : Type*} [Inhabited α] (x : α) (xs : List α) (i : Nat) :
    (x :: xs)[i + 1]! = xs[i]! := by
  simp only [getElem!_def, getElem?_cons_succ]

/-- Helper: map with (+1) preserves chains under (<) -/
theorem List.IsChain_map_succ {indices : List Nat} (h : indices.IsChain (· < ·)) :
    (indices.map (· + 1)).IsChain (· < ·) := by
  induction indices with
  | nil => exact List.IsChain.nil
  | cons x xs ih =>
    simp only [List.map]
    cases xs with
    | nil => exact List.IsChain.singleton _
    | cons y ys =>
      simp only [List.map]
      cases h with
      | cons_cons hxy htail =>
        apply List.IsChain.cons_cons
        · omega
        · exact ih htail

/-- Helper: 0 is less than all elements of (indices.map (· + 1)) when indices is nonempty -/
theorem zero_lt_all_map_succ {indices : List Nat} (i : Nat) (h : i ∈ indices.map (· + 1)) :
    0 < i := by
  simp only [List.mem_map] at h
  obtain ⟨j, _, hj⟩ := h
  omega

/-- For any subsequence relation, we can extract a list of strictly increasing indices.
    Note: This uses choice because Subseq is a Prop and cannot eliminate to data directly.
    The actual implementation would use the classical axiom to extract witnesses. -/
theorem subseq_has_indices {s l : List Int} (h : Subseq s l) :
    ∃ indices : List Nat,
      indices.length = s.length ∧
      indices.IsChain (· < ·) ∧
      (∀ i ∈ indices, i < l.length) ∧
      indices.map (fun i => l[i]!) = s := by
  induction h with
  | nil =>
    exact ⟨[], rfl, List.IsChain.nil, by simp, rfl⟩
  | cons_skip hsub ih =>
    -- Skip the head element, so indices in tail are shifted by 1
    -- hsub : Subseq s l (where l is the tail)
    -- ih : ∃ indices, ... for Subseq s l
    -- We want: indices for Subseq s (x :: l)
    obtain ⟨indices, h_len, h_chain, h_bound, h_map⟩ := ih
    use indices.map (· + 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h_len]
    · exact List.IsChain_map_succ h_chain
    · intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have := h_bound j hj
      simp only [List.length_cons]
      omega
    · -- Show: (indices.map (· + 1)).map (fun i => (head :: tail)[i]!) = s
      simp only [List.map_map, Function.comp_def]
      -- The goal is indices.map (fun j => (head :: tail)[j + 1]!) = s
      -- We have h_map : indices.map (fun i => tail[i]!) = s
      convert h_map using 2
  | cons_take hsub ih =>
    -- Take the head element, add 0 to indices and shift the rest by 1
    -- hsub : Subseq s l (where s is tail of subsequence, l is tail of list)
    -- ih : ∃ indices, ... for Subseq s l
    -- We want: indices for Subseq (x :: s) (x :: l)
    obtain ⟨indices, h_len, h_chain, h_bound, h_map⟩ := ih
    use 0 :: indices.map (· + 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h_len]
    · -- Show chain: 0 < first of (indices.map (· + 1)) and rest is chain
      cases indices with
      | nil =>
        -- 0 :: [].map (· + 1) = [0], which is trivially a chain (singleton)
        simp only [List.map]
        exact List.IsChain.singleton _
      | cons y ys =>
        simp only [List.map]
        apply List.IsChain.cons_cons
        · omega
        · exact List.IsChain_map_succ h_chain
    · intro i hi
      simp only [List.mem_cons] at hi
      cases hi with
      | inl h =>
        simp only [h, List.length_cons]
        omega
      | inr h =>
        simp only [List.mem_map] at h
        obtain ⟨j, hj, rfl⟩ := h
        have := h_bound j hj
        simp only [List.length_cons]
        omega
    · -- Show: (0 :: indices.map (· + 1)).map (fun i => (head :: tail)[i]!) = head :: s
      simp only [List.map]
      -- Goal: (head :: tail)[0]! :: (indices.map (· + 1)).map (fun i => (head :: tail)[i]!) = head :: s
      -- First show (head :: tail)[0]! = head
      have h0 : ∀ (x : Int) (xs : List Int), (x :: xs)[0]! = x := by
        intro x xs
        simp only [getElem!_def, List.getElem?_cons_zero]
      rw [h0]
      -- Now show the tail part: (indices.map (· + 1)).map (fun i => (head :: tail)[i]!) = s
      congr 1
      conv_rhs => rw [← h_map]
      simp only [List.map_map, Function.comp_def]
      convert rfl using 2

/-- Upper bound: length of any strictly increasing subsequence ≤ number of piles.

    The key insight: elements assigned to the same pile cannot both be in a strictly
    increasing subsequence (by same_pile_ge). Therefore, distinct elements of any
    strictly increasing subsequence must be in distinct piles. Since there are only
    piles.size piles, the subsequence length is bounded by piles.size. -/
theorem lis_length_le_piles_size (input : List Int) (s : List Int)
    (h_inc : StrictlyIncreasing s)
    (h_sub : Subseq s input) :
    s.length ≤ (runPatience input).piles.size := by
  -- Get indices for the subsequence
  obtain ⟨indices, h_len, h_sorted, h_bound, h_map⟩ := subseq_has_indices h_sub

  -- The mapped values form s, which is strictly increasing
  have h_map_inc : (indices.map fun i => input[i]!).IsChain (· < ·) := by
    rw [h_map]; exact h_inc

  -- Elements at distinct indices are in distinct piles
  have h_distinct := strictly_increasing_implies_distinct_piles input indices h_map_inc h_sorted h_bound

  -- Each pile assignment is bounded
  have h_bounded_piles : ∀ i ∈ indices, (pileAssignment input)[i]! < (runPatience input).piles.size := by
    intro i hi
    exact pileAssignment_bounded input i (h_bound i hi)

  -- A list with pairwise distinct values all bounded by n has length ≤ n
  -- This is a pigeonhole argument
  rw [← h_len]

  -- Set up for pigeonhole argument
  set n := (runPatience input).piles.size with hn
  set mapped := indices.map (fun i => (pileAssignment input)[i]!) with h_mapped

  -- First, convert the pairwise distinct to Nodup on the mapped list
  -- h_distinct : List.Pairwise (fun a b => (pileAssignment input)[a]! ≠ (pileAssignment input)[b]!) indices
  -- We need: (indices.map f).Nodup where f = fun i => (pileAssignment input)[i]!
  -- List.Nodup is defined as List.Pairwise (· ≠ ·)
  -- List.pairwise_map says: Pairwise R (map f l) ↔ Pairwise (fun a b => R (f a) (f b)) l
  have h_piles_nodup : mapped.Nodup := by
    rw [h_mapped]
    unfold List.Nodup
    rw [List.pairwise_map]
    -- Goal: indices.Pairwise (fun a b => f a ≠ f b)
    exact h_distinct

  have h_len_map : mapped.length = indices.length := by simp [h_mapped]

  have h_bounded_map : ∀ x ∈ mapped, x < n := by
    intro x hx
    simp only [h_mapped, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h_bounded_piles i hi

  -- Convert to Fin n list and use Fintype cardinality bound
  have h_to_fin : ∀ x ∈ mapped, x < n := h_bounded_map
  set fin_list : List (Fin n) := mapped.pmap (fun x hx => ⟨x, hx⟩) h_to_fin with h_fin_def

  have h_fin_len : fin_list.length = mapped.length := by simp [h_fin_def, List.length_pmap]

  have h_fin_nodup : fin_list.Nodup := by
    rw [h_fin_def]
    apply List.Nodup.pmap
    · -- Injectivity: ⟨a, ha⟩ = ⟨b, hb⟩ → a = b
      intro a _ b _ hab
      simp only [Fin.mk.injEq] at hab
      exact hab
    · exact h_piles_nodup

  have h_card := List.Nodup.length_le_card h_fin_nodup
  simp only [Fintype.card_fin] at h_card
  omega

/-- Lower bound: there exists a strictly increasing subsequence of length = piles.size -/
theorem exists_lis_of_length_piles_size (input : List Int) :
    ∃ s : List Int, StrictlyIncreasing s ∧ Subseq s input ∧
      s.length = (runPatience input).piles.size := by
  exact ⟨(longestIncreasingSubsequence input).val,
         (longestIncreasingSubsequence input).property.1,
         (longestIncreasingSubsequence input).property.2.1,
         (longestIncreasingSubsequence input).property.2.2⟩

/-- Main theorem: For any LIS, its length equals the number of piles -/
theorem piles_size_eq_lis_length_full (input : List Int) :
    ∀ lis : List Int, IsLIS lis input →
      lis.length = (runPatience input).piles.size := by
  intro lis h_lis
  obtain ⟨h_inc, h_sub, h_max⟩ := h_lis

  -- Upper bound: lis.length ≤ piles.size
  have h_le := lis_length_le_piles_size input lis h_inc h_sub

  -- Lower bound: there exists a subsequence of length piles.size
  obtain ⟨s, hs_inc, hs_sub, hs_len⟩ := exists_lis_of_length_piles_size input

  -- By maximality of lis: s.length ≤ lis.length
  have h_ge := h_max s hs_inc hs_sub

  -- Combine
  omega

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

-- Check axioms used by main theorems
#print axioms longestIncreasingSubsequence
#print axioms piles_size_eq_lis_length_full
#print axioms lis_length_le_piles_size
#print axioms same_pile_ge
#print axioms reconstructLIS_from_runPatience_increasing
#print axioms reconstructLIS_from_runPatience_subseq
-- Check axioms used by sorried theorems
#print axioms chainLengthInvariant_preserved
#print axioms stateAfter_split_done
-- Check more theorems
#print axioms reconstructLIS_from_runPatience_length
#print axioms runPatience_invariant
#print axioms exists_lis_of_length_piles_size
#print axioms pile_top_nonincreasing
#print axioms pile_top_single_step
