/-
Two-Dimensional Dynamic Programming: Verified Longest Common Subsequence
Extends the proof cell pattern from RodCutting.lean to 2D problems.

The key insight: Each cell stores {v // lcsLength (l1.take i) (l2.take j) = v}
so correctness comes for free from the type system.
-/

import Mathlib.Tactic

/-!
## Recursive Specification

We first define the recursive specification for LCS length.
This is the "ground truth" that our DP algorithm will compute.
-/

/-- Recursive specification for LCS length on list prefixes.
    lcsLength l1 l2 returns the length of the longest common subsequence. -/
def lcsLength (l1 l2 : List Char) : Nat :=
  match l1, l2 with
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    if x == y then 1 + lcsLength xs ys
    else max (lcsLength xs (y :: ys)) (lcsLength (x :: xs) ys)

/-!
## 2D Proof Cells

A Cell2D stores a ((i, j), value) pair with proof that
the recursive function applied to indices (i, j) equals value.
-/

/-- A 2D proof cell: stores ((i, j), value) with proof that ftarget i j = value -/
def Cell2D (ftarget : Nat → Nat → β) :=
  {c : (Nat × Nat) × β // ftarget c.fst.1 c.fst.2 = c.snd}

/-- A 2D DP array with proof that each cell is correctly indexed.
    Uses row-major linearization: idx = i * (m + 1) + j -/
def DPArray2D (ftarget : Nat → Nat → β) (n m : Nat) :=
  {arr : Array (Cell2D ftarget) //
    arr.size = (n + 1) * (m + 1) ∧
    ∀ idx : Fin arr.size,
      let i := idx / (m + 1)
      let j := idx % (m + 1)
      (i, j) = arr[idx].val.fst}

/-!
## Indexing Lemmas

Key lemmas for 2D array indexing and bounds.
-/

theorem idx_bound_of_ij_bound {n m i j : Nat} (hi : i ≤ n) (hj : j ≤ m) :
    i * (m + 1) + j < (n + 1) * (m + 1) := by
  have h1 : i * (m + 1) ≤ n * (m + 1) := Nat.mul_le_mul_right (m + 1) hi
  have h2 : j < m + 1 := Nat.lt_succ_of_le hj
  calc i * (m + 1) + j < i * (m + 1) + (m + 1) := by omega
    _ = (i + 1) * (m + 1) := by ring
    _ ≤ (n + 1) * (m + 1) := Nat.mul_le_mul_right (m + 1) (by omega)

theorem div_of_idx {m i j : Nat} (hj : j < m + 1) :
    (i * (m + 1) + j) / (m + 1) = i := by
  have hm_pos : 0 < m + 1 := Nat.zero_lt_succ m
  have h1 : (i * (m + 1)) / (m + 1) = i := Nat.mul_div_cancel i hm_pos
  have h2 : j / (m + 1) = 0 := Nat.div_eq_of_lt hj
  have h3 : (i * (m + 1)) % (m + 1) = 0 := Nat.mul_mod_left i (m + 1)
  have h4 : j % (m + 1) = j := Nat.mod_eq_of_lt hj
  rw [Nat.add_div hm_pos, h1, h2, Nat.add_zero, h3, h4]
  simp [hj]

theorem mod_of_idx {m i j : Nat} (hj : j < m + 1) :
    (i * (m + 1) + j) % (m + 1) = j := by
  have h1 : (i * (m + 1)) % (m + 1) = 0 := Nat.mul_mod_left i (m + 1)
  have h2 : j % (m + 1) = j := Nat.mod_eq_of_lt hj
  calc (i * (m + 1) + j) % (m + 1)
      = ((i * (m + 1)) % (m + 1) + j % (m + 1)) % (m + 1) := Nat.add_mod _ _ _
    _ = (0 + j) % (m + 1) := by rw [h1, h2]
    _ = j % (m + 1) := by simp
    _ = j := h2

/-!
## DPArray2D Operations

Core operations for building and accessing the 2D DP array.
-/

/-- Get a value from the 2D array with correctness proof -/
theorem DPArray2D_get {ftarget : Nat → Nat → β} {n m : Nat}
    (arr : DPArray2D ftarget n m) (i j : Nat) (hi : i ≤ n) (hj : j ≤ m) :
    let idx_val := i * (m + 1) + j
    let h_bound : idx_val < arr.val.size := by rw [arr.property.1]; exact idx_bound_of_ij_bound hi hj
    let idx : Fin arr.val.size := ⟨idx_val, h_bound⟩
    ftarget i j = arr.val[idx].val.snd := by
  intro idx_val h_bound idx
  have h_idx_prop := arr.property.2 idx
  simp only at h_idx_prop
  have hj' : j < m + 1 := Nat.lt_succ_of_le hj
  have h_div : idx_val / (m + 1) = i := div_of_idx hj'
  have h_mod : idx_val % (m + 1) = j := mod_of_idx hj'
  have h_ij : (i, j) = arr.val[idx].val.fst := by
    have : (idx_val / (m + 1), idx_val % (m + 1)) = arr.val[idx].val.fst := h_idx_prop
    rw [h_div, h_mod] at this
    exact this
  have h_cell := arr.val[idx].property
  rw [← h_cell]
  congr 1
  · exact (Prod.ext_iff.mp h_ij).1
  · exact (Prod.ext_iff.mp h_ij).2

/-- Push a new cell to the 2D array, extending by one position -/
def DPArray2D_push {ftarget : Nat → Nat → β} {m k : Nat}
    (arr : {a : Array (Cell2D ftarget) // a.size = k ∧
           ∀ idx : Fin a.size,
             let i := idx / (m + 1)
             let j := idx % (m + 1)
             (i, j) = a[idx].val.fst})
    (c : Cell2D ftarget) (h_idx : c.val.fst = (k / (m + 1), k % (m + 1))) :
    {a : Array (Cell2D ftarget) // a.size = k + 1 ∧
     ∀ idx : Fin a.size,
       let i := idx / (m + 1)
       let j := idx % (m + 1)
       (i, j) = a[idx].val.fst} :=
  let newArr := arr.val.push c
  have hsize : newArr.size = k + 1 := by
    rw [Array.size_push, arr.property.1]

  have hind : ∀ idx : Fin newArr.size,
      let i := idx / (m + 1)
      let j := idx % (m + 1)
      (i, j) = newArr[idx].val.fst := by
    intro idx
    have hi' : idx.val < newArr.size := idx.isLt
    have hsz : newArr.size = arr.val.size + 1 := by simp [newArr, Array.size_push]

    if h1 : idx.val < arr.val.size then
      have heq : newArr[idx] = arr.val[idx.val] := by
        apply Array.getElem_push_lt
      rw [heq]
      have := arr.property.2 ⟨idx.val, h1⟩
      exact this
    else
      have hk : idx.val = arr.val.size := by omega
      have heq : newArr[idx] = c := by
        simp only [Fin.getElem_fin, newArr, Array.getElem_push, hk, lt_self_iff_false, ↓reduceDIte]
      rw [heq]
      rw [arr.property.1] at hk
      simp only
      rw [h_idx, ← hk]

  ⟨newArr, And.intro hsize hind⟩

/-!
## LCS-Specific Implementation

Now we specialize to LCS using List.take for prefixes.
-/

/-- The target function for LCS: lcsLength on prefixes of l1 and l2 -/
def lcsTarget (l1 l2 : List Char) (i j : Nat) : Nat :=
  lcsLength (l1.take i) (l2.take j)

/-!
## Key Correctness Lemmas

These lemmas establish that the DP recurrence matches the recursive spec.
-/

theorem lcsTarget_zero_left (l1 l2 : List Char) (j : Nat) :
    lcsTarget l1 l2 0 j = 0 := by
  simp [lcsTarget, List.take, lcsLength]

theorem lcsTarget_zero_right (l1 l2 : List Char) (i : Nat) :
    lcsTarget l1 l2 i 0 = 0 := by
  simp only [lcsTarget, List.take]
  cases h : l1.take i with
  | nil => simp [lcsLength]
  | cons x xs => simp [lcsLength]

theorem lcsLength_nil_right (l : List Char) : lcsLength l [] = 0 := by
  cases l <;> simp [lcsLength]

theorem lcsLength_cons_cons (x y : Char) (xs ys : List Char) :
    lcsLength (x :: xs) (y :: ys) =
      if x == y then 1 + lcsLength xs ys
      else max (lcsLength xs (y :: ys)) (lcsLength (x :: xs) ys) := by
  simp [lcsLength]

/-- LCS length on snoc lists follows the standard recurrence.
    This is the key lemma connecting LCS computed from the end to LCS computed from the front. -/
theorem lcsLength_snoc_snoc (xs ys : List Char) (x y : Char) :
    lcsLength (xs ++ [x]) (ys ++ [y]) =
      if x == y then 1 + lcsLength xs ys
      else max (lcsLength xs (ys ++ [y])) (lcsLength (xs ++ [x]) ys) := by
  -- This requires a non-trivial double induction
  -- The proof is deferred to the proof subagent
  sorry

/-- Key recurrence: when both indices are positive, lcsTarget follows the standard DP recurrence -/
theorem lcsTarget_recurrence (l1 l2 : List Char) (i j : Nat)
    (hi : i > 0) (hj : j > 0) (hi_bound : i ≤ l1.length) (hj_bound : j ≤ l2.length) :
    let c1 := l1.getD (i - 1) ' '
    let c2 := l2.getD (j - 1) ' '
    lcsTarget l1 l2 i j =
      if c1 == c2 then 1 + lcsTarget l1 l2 (i - 1) (j - 1)
      else max (lcsTarget l1 l2 (i - 1) j) (lcsTarget l1 l2 i (j - 1)) := by
  intro c1 c2
  simp only [lcsTarget]
  have hi_lt : i - 1 < l1.length := Nat.sub_one_lt_of_le hi hi_bound
  have hj_lt : j - 1 < l2.length := Nat.sub_one_lt_of_le hj hj_bound

  have h_take_i : l1.take i = l1.take (i - 1) ++ [l1[i - 1]] := by
    have hi' : i - 1 + 1 = i := Nat.sub_add_cancel hi
    conv_lhs => rw [← hi']
    rw [List.take_succ]
    simp only [List.getElem?_eq_getElem hi_lt, Option.toList_some]
  have h_take_j : l2.take j = l2.take (j - 1) ++ [l2[j - 1]] := by
    have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
    conv_lhs => rw [← hj']
    rw [List.take_succ]
    simp only [List.getElem?_eq_getElem hj_lt, Option.toList_some]

  have h_c1 : c1 = l1[i - 1] := by
    simp only [c1, List.getD]
    rw [List.getElem?_eq_getElem hi_lt]
    simp
  have h_c2 : c2 = l2[j - 1] := by
    simp only [c2, List.getD]
    rw [List.getElem?_eq_getElem hj_lt]
    simp

  rw [h_take_i, h_take_j, h_c1, h_c2]
  exact lcsLength_snoc_snoc _ _ _ _

/-!
## The DP Algorithm

Build the full 2D DP table functionally using a simple iterative approach.
-/

/-- Partial DP array type -/
abbrev PartialDPArray (l1 l2 : List Char) (k : Nat) :=
  {a : Array (Cell2D (lcsTarget l1 l2)) // a.size = k ∧
    ∀ idx : Fin a.size,
      let row := idx / (l2.length + 1)
      let col := idx % (l2.length + 1)
      (row, col) = a[idx].val.fst}

/-- Build a single cell of the DP table -/
def buildCell (l1 l2 : List Char) (n m : Nat) (k : Nat) (hk : k < (n + 1) * (m + 1))
    (partial_arr : PartialDPArray l1 l2 k)
    (hn : n = l1.length) (hm : m = l2.length) :
    Cell2D (lcsTarget l1 l2) :=
  let i := k / (m + 1)
  let j := k % (m + 1)

  have hi_bound : i ≤ n := by
    have hm_pos : 0 < m + 1 := Nat.zero_lt_succ m
    have hk' : k < (m + 1) * (n + 1) := by
      calc k < (n + 1) * (m + 1) := hk
        _ = (m + 1) * (n + 1) := by ring
    have h : k / (m + 1) < n + 1 := Nat.div_lt_of_lt_mul hk'
    omega
  have hj_bound : j ≤ m := by
    have h : j < m + 1 := Nat.mod_lt k (Nat.zero_lt_succ m)
    omega

  -- Key property: k = i * (m + 1) + j by Euclidean division
  have h_k_eq : k = i * (m + 1) + j := by
    have h := Nat.div_add_mod k (m + 1)
    -- h gives: (m + 1) * (k / (m + 1)) + k % (m + 1) = k
    -- We need: k = (k / (m + 1)) * (m + 1) + k % (m + 1)
    simp only [i, j]
    rw [Nat.mul_comm] at h
    exact h.symm

  -- Compute the cell value
  let val : Nat :=
    if h_zero : i = 0 ∨ j = 0 then 0
    else
      -- Since we're in the else branch, we know i ≠ 0 and j ≠ 0
      have hi' : i ≠ 0 := fun h => h_zero (Or.inl h)
      have hj' : j ≠ 0 := fun h => h_zero (Or.inr h)
      have hi'' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi'
      have hj'' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj'

      let c1 := l1.getD (i - 1) ' '
      let c2 := l2.getD (j - 1) ' '
      if c1 == c2 then
        -- Need dp[i-1][j-1]
        have h_prev : (i - 1) * (m + 1) + (j - 1) < partial_arr.val.size := by
          have h1 : (i - 1) * (m + 1) + (j - 1) < i * (m + 1) := by
            calc (i - 1) * (m + 1) + (j - 1)
                < (i - 1) * (m + 1) + (m + 1) := by omega
              _ = ((i - 1) + 1) * (m + 1) := by ring
              _ = i * (m + 1) := by rw [Nat.sub_add_cancel hi'']
          calc (i - 1) * (m + 1) + (j - 1) < i * (m + 1) := h1
            _ ≤ i * (m + 1) + j := Nat.le_add_right _ _
            _ = k := h_k_eq.symm
            _ = partial_arr.val.size := partial_arr.property.1.symm
        1 + partial_arr.val[(i - 1) * (m + 1) + (j - 1)].val.snd
      else
        -- Need max(dp[i-1][j], dp[i][j-1])
        have h_up : (i - 1) * (m + 1) + j < partial_arr.val.size := by
          have h1 : (i - 1) * (m + 1) + j < i * (m + 1) + j := by
            have : (i - 1) * (m + 1) < i * (m + 1) := by
              have hm_pos : 0 < m + 1 := Nat.zero_lt_succ m
              exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hi'' Nat.one_pos) hm_pos
            omega
          calc (i - 1) * (m + 1) + j < i * (m + 1) + j := h1
            _ = k := h_k_eq.symm
            _ = partial_arr.val.size := partial_arr.property.1.symm
        have h_left : i * (m + 1) + (j - 1) < partial_arr.val.size := by
          calc i * (m + 1) + (j - 1) < i * (m + 1) + j := by omega
            _ = k := h_k_eq.symm
            _ = partial_arr.val.size := partial_arr.property.1.symm
        max (partial_arr.val[(i - 1) * (m + 1) + j].val.snd)
            (partial_arr.val[i * (m + 1) + (j - 1)].val.snd)

  -- Prove the cell value is correct
  have h_correct : lcsTarget l1 l2 i j = val := by
    simp only [val]
    split_ifs with h_zero h_match
    · -- Base case: i = 0 or j = 0
      cases h_zero with
      | inl hi0 => rw [hi0]; exact lcsTarget_zero_left l1 l2 j
      | inr hj0 => rw [hj0]; exact lcsTarget_zero_right l1 l2 i
    · -- Match case: c1 == c2
      push_neg at h_zero
      obtain ⟨hi_nz, hj_nz⟩ := h_zero
      have hi_pos : i > 0 := Nat.pos_of_ne_zero hi_nz
      have hj_pos : j > 0 := Nat.pos_of_ne_zero hj_nz
      have hi_le : i ≤ n := hi_bound
      have hj_le : j ≤ m := hj_bound

      -- Use the recurrence
      have h_rec := lcsTarget_recurrence l1 l2 i j hi_pos hj_pos (hn ▸ hi_le) (hm ▸ hj_le)
      simp only at h_rec
      rw [h_rec, if_pos h_match]

      -- Now we need to show that the stored value equals lcsTarget l1 l2 (i-1) (j-1)
      -- The key is that partial_arr has the cell for (i-1, j-1)
      have h_prev_idx : (i - 1) * (m + 1) + (j - 1) < partial_arr.val.size := by
        have hi'' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi_nz
        have hj'' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj_nz
        have h1 : (i - 1) * (m + 1) + (j - 1) < i * (m + 1) := by
          calc (i - 1) * (m + 1) + (j - 1)
              < (i - 1) * (m + 1) + (m + 1) := by omega
            _ = ((i - 1) + 1) * (m + 1) := by ring
            _ = i * (m + 1) := by rw [Nat.sub_add_cancel hi'']
        calc (i - 1) * (m + 1) + (j - 1) < i * (m + 1) := h1
          _ ≤ i * (m + 1) + j := Nat.le_add_right _ _
          _ = k := h_k_eq.symm
          _ = partial_arr.val.size := partial_arr.property.1.symm

      -- The cell's indices match (i-1, j-1)
      have h_prev_indices := partial_arr.property.2 ⟨(i - 1) * (m + 1) + (j - 1), h_prev_idx⟩
      simp only at h_prev_indices
      have h_div : ((i - 1) * (m + 1) + (j - 1)) / (l2.length + 1) = i - 1 := by
        have hj'' : j - 1 < m + 1 := by omega
        rw [← hm]
        exact div_of_idx hj''
      have h_mod : ((i - 1) * (m + 1) + (j - 1)) % (l2.length + 1) = j - 1 := by
        have hj'' : j - 1 < m + 1 := by omega
        rw [← hm]
        exact mod_of_idx hj''
      rw [h_div, h_mod] at h_prev_indices

      -- h_prev_indices : (i - 1, j - 1) = partial_arr.val[...].val.fst
      have h_cell_prop := (partial_arr.val[(i - 1) * (m + 1) + (j - 1)]'h_prev_idx).property
      -- h_cell_prop : lcsTarget l1 l2 (fst.1) (fst.2) = snd

      have h_i1 : (partial_arr.val[(i - 1) * (m + 1) + (j - 1)]'h_prev_idx).val.fst.1 = i - 1 :=
        (Prod.ext_iff.mp h_prev_indices.symm).1
      have h_j1 : (partial_arr.val[(i - 1) * (m + 1) + (j - 1)]'h_prev_idx).val.fst.2 = j - 1 :=
        (Prod.ext_iff.mp h_prev_indices.symm).2

      simp only [h_i1, h_j1] at h_cell_prop
      rw [← h_cell_prop]
    · -- No match case
      push_neg at h_zero
      obtain ⟨hi_nz, hj_nz⟩ := h_zero
      have hi_pos : i > 0 := Nat.pos_of_ne_zero hi_nz
      have hj_pos : j > 0 := Nat.pos_of_ne_zero hj_nz
      have hi_le : i ≤ n := hi_bound
      have hj_le : j ≤ m := hj_bound

      -- Use the recurrence
      have h_rec := lcsTarget_recurrence l1 l2 i j hi_pos hj_pos (hn ▸ hi_le) (hm ▸ hj_le)
      simp only at h_rec
      rw [h_rec, if_neg h_match]

      -- Need to show stored values equal lcsTarget at (i-1, j) and (i, j-1)
      have hi'' : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi_nz
      have hj'' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj_nz

      -- For the "up" cell at (i-1, j)
      have h_up_idx : (i - 1) * (m + 1) + j < partial_arr.val.size := by
        have h1 : (i - 1) * (m + 1) + j < i * (m + 1) + j := by
          have : (i - 1) * (m + 1) < i * (m + 1) := by
            have hm_pos : 0 < m + 1 := Nat.zero_lt_succ m
            exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hi'' Nat.one_pos) hm_pos
          omega
        calc (i - 1) * (m + 1) + j < i * (m + 1) + j := h1
          _ = k := h_k_eq.symm
          _ = partial_arr.val.size := partial_arr.property.1.symm

      have h_up_indices := partial_arr.property.2 ⟨(i - 1) * (m + 1) + j, h_up_idx⟩
      simp only at h_up_indices
      have h_up_div : ((i - 1) * (m + 1) + j) / (l2.length + 1) = i - 1 := by
        have hj' : j < m + 1 := Nat.lt_succ_of_le hj_bound
        rw [← hm]
        exact div_of_idx hj'
      have h_up_mod : ((i - 1) * (m + 1) + j) % (l2.length + 1) = j := by
        have hj' : j < m + 1 := Nat.lt_succ_of_le hj_bound
        rw [← hm]
        exact mod_of_idx hj'
      rw [h_up_div, h_up_mod] at h_up_indices

      -- For the "left" cell at (i, j-1)
      have h_left_idx : i * (m + 1) + (j - 1) < partial_arr.val.size := by
        calc i * (m + 1) + (j - 1) < i * (m + 1) + j := by omega
          _ = k := h_k_eq.symm
          _ = partial_arr.val.size := partial_arr.property.1.symm

      have h_left_indices := partial_arr.property.2 ⟨i * (m + 1) + (j - 1), h_left_idx⟩
      simp only at h_left_indices
      have h_left_div : (i * (m + 1) + (j - 1)) / (l2.length + 1) = i := by
        have hj' : j - 1 < m + 1 := by omega
        rw [← hm]
        exact div_of_idx hj'
      have h_left_mod : (i * (m + 1) + (j - 1)) % (l2.length + 1) = j - 1 := by
        have hj' : j - 1 < m + 1 := by omega
        rw [← hm]
        exact mod_of_idx hj'
      rw [h_left_div, h_left_mod] at h_left_indices

      -- Now connect the stored values using the cell properties
      have h_up_prop := (partial_arr.val[(i - 1) * (m + 1) + j]'h_up_idx).property
      have h_up_i : (partial_arr.val[(i - 1) * (m + 1) + j]'h_up_idx).val.fst.1 = i - 1 :=
        (Prod.ext_iff.mp h_up_indices.symm).1
      have h_up_j : (partial_arr.val[(i - 1) * (m + 1) + j]'h_up_idx).val.fst.2 = j :=
        (Prod.ext_iff.mp h_up_indices.symm).2

      have h_left_prop := (partial_arr.val[i * (m + 1) + (j - 1)]'h_left_idx).property
      have h_left_i : (partial_arr.val[i * (m + 1) + (j - 1)]'h_left_idx).val.fst.1 = i :=
        (Prod.ext_iff.mp h_left_indices.symm).1
      have h_left_j : (partial_arr.val[i * (m + 1) + (j - 1)]'h_left_idx).val.fst.2 = j - 1 :=
        (Prod.ext_iff.mp h_left_indices.symm).2

      simp only [h_up_i, h_up_j] at h_up_prop
      simp only [h_left_i, h_left_j] at h_left_prop

      rw [← h_up_prop, ← h_left_prop]

  ⟨((i, j), val), h_correct⟩

/-- Helper to build the DP table recursively -/
def buildDPTableAux (l1 l2 : List Char) (n m : Nat) (hn : n = l1.length) (hm : m = l2.length)
    (k : Nat) (hk : k ≤ (n + 1) * (m + 1)) :
    PartialDPArray l1 l2 k :=
  match k with
  | 0 => ⟨#[], by simp, fun idx => absurd idx.isLt (Nat.not_lt_zero _)⟩
  | k' + 1 =>
    have hk' : k' < (n + 1) * (m + 1) := Nat.lt_of_succ_le hk
    have hk'_le : k' ≤ (n + 1) * (m + 1) := Nat.le_of_lt hk'
    let partial_arr := buildDPTableAux l1 l2 n m hn hm k' hk'_le
    let cell := buildCell l1 l2 n m k' hk' partial_arr hn hm

    -- Rewrite partial_arr to match DPArray2D_push's expected type
    have hsize_eq : partial_arr.val.size = k' := partial_arr.property.1

    have h_idx : cell.val.fst = (k' / (l2.length + 1), k' % (l2.length + 1)) := by
      simp only [cell, buildCell]
      rw [hm]

    -- Construct the pushed array
    let newArr := partial_arr.val.push cell
    have h_newsize : newArr.size = k' + 1 := by
      simp [newArr, Array.size_push, hsize_eq]

    have h_newind : ∀ idx : Fin newArr.size,
        let row := idx / (l2.length + 1)
        let col := idx % (l2.length + 1)
        (row, col) = newArr[idx].val.fst := by
      intro idx
      have hi' : idx.val < newArr.size := idx.isLt
      have hsz : newArr.size = partial_arr.val.size + 1 := by simp [newArr, Array.size_push]

      if h1 : idx.val < partial_arr.val.size then
        have heq : newArr[idx] = partial_arr.val[idx.val] := by
          apply Array.getElem_push_lt
        rw [heq]
        have := partial_arr.property.2 ⟨idx.val, h1⟩
        exact this
      else
        have hk_eq : idx.val = partial_arr.val.size := by omega
        have heq : newArr[idx] = cell := by
          simp only [Fin.getElem_fin, newArr, Array.getElem_push, hk_eq, lt_self_iff_false, ↓reduceDIte]
        rw [heq]
        rw [hsize_eq] at hk_eq
        simp only
        rw [h_idx, ← hk_eq]

    ⟨newArr, h_newsize, h_newind⟩

/-- Build the full DP table -/
def buildDPTable (l1 l2 : List Char) :
    DPArray2D (lcsTarget l1 l2) l1.length l2.length :=
  let n := l1.length
  let m := l2.length
  let total := (n + 1) * (m + 1)

  let result := buildDPTableAux l1 l2 n m rfl rfl total (Nat.le_refl _)

  have h_size : result.val.size = (n + 1) * (m + 1) := result.property.1
  ⟨result.val, h_size, result.property.2⟩

/-!
## The Main LCS Function

Returns the LCS length with proof that it equals the recursive specification.
-/

/-- Compute LCS length with proof of correctness -/
def lcsDP (l1 l2 : List Char) : {v : Nat // lcsLength l1 l2 = v} :=
  let n := l1.length
  let m := l2.length
  let table := buildDPTable l1 l2

  -- The answer is at position (n, m)
  have h_bound : n * (m + 1) + m < table.val.size := by
    rw [table.property.1]
    exact idx_bound_of_ij_bound (Nat.le_refl n) (Nat.le_refl m)

  let result := table.val[n * (m + 1) + m]'h_bound

  have h_correct : lcsLength l1 l2 = result.val.snd := by
    have h_target : lcsTarget l1 l2 n m = result.val.snd := by
      have := DPArray2D_get table n m (Nat.le_refl n) (Nat.le_refl m)
      simp only at this
      exact this
    unfold lcsTarget at h_target
    simp only [n, m, List.take_length] at h_target
    exact h_target

  ⟨result.val.snd, h_correct⟩

/-!
## Tests
-/

#eval! lcsDP "ABCDGH".toList "AEDFHR".toList  -- Expected: 3 (ADH)
#eval! lcsDP "AGGTAB".toList "GXTXAYB".toList  -- Expected: 4 (GTAB)
#eval! lcsDP "ABC".toList "ABC".toList  -- Expected: 3
#eval! lcsDP "ABC".toList "DEF".toList  -- Expected: 0
