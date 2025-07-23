/-
Binary Search
By Sonnet 4, on Claude Desktop with LeanTool and LeanExplore
Prompted with the function signature:
```
def binary_search_aux(arr : Array Nat) (target : Nat) 
(h : arr.toList.Sorted (· ≤ ·)) (lo : Nat) (hi : Nat)
(h_lo : lo < arr.size) (h_hi : hi < arr.size)
: {result : Option Nat //match result with
  |some i => arr[i]? = some target
  |none => Not (∃ i, i>=lo ∧ i<=hi ∧  arr[i]? = some target)
} :=sorry
```
This continuation prompt was helpful:
"please continue. try to maintain a syntactically valid proof sketch with sorrys, and iteratively refine. If a sorry could not be immediately solved, try to get the goal (via check_lean), and come up with an informal proof sketch for the goal. Then turn it into a formal Lean proof sketch."
-/

import Mathlib

-- The specification for binary search: either we find an index with the target,
-- or we prove no such index exists in the given range
def binary_search_spec (arr : Array Nat) (target : Nat) (lo hi : Nat) (result : Option Nat) : Prop :=
  match result with
  | some i => arr[i]? = some target
  | none => ¬ (∃ i, lo ≤ i ∧ i ≤ hi ∧ arr[i]? = some target)

-- Helper lemma: if array is sorted, then elements maintain ordering by index
lemma sorted_array_monotone (arr : Array Nat) (h : arr.toList.Sorted (· ≤ ·)) 
    (i j : Nat) (hi : i < arr.size) (hj : j < arr.size) (hij : i ≤ j) : 
    arr[i] ≤ arr[j] := by
  have hi_fin : i < arr.toList.length := by simp [hi]
  have hj_fin : j < arr.toList.length := by simp [hj]
  have hij_fin : (⟨i, hi_fin⟩ : Fin arr.toList.length) ≤ ⟨j, hj_fin⟩ := hij
  have h_get := List.Sorted.rel_get_of_le h hij_fin
  simp_all only [Array.length_toList, Fin.mk_le_mk, List.get_eq_getElem, Array.getElem_toList]

-- Complete binary search implementation with all proofs!
def binary_search_aux(arr : Array Nat) (target : Nat) 
(h : arr.toList.Sorted (· ≤ ·)) (lo : Nat) (hi : Nat)
(h_lo : lo < arr.size) (h_hi : hi < arr.size)
: {result : Option Nat // binary_search_spec arr target lo hi result} := 
if h_empty : lo > hi then
  ⟨none, by
    simp [binary_search_spec]
    intro i h_lo_le h_hi_le h_target
    omega⟩
else
  let mid := (lo + hi) / 2
  have h_le : lo ≤ hi := Nat.le_of_not_gt h_empty
  have h_mid_le_hi : mid ≤ hi := by omega 
  have h_lo_le_mid : lo ≤ mid := by omega
  have h_mid_valid : mid < arr.size := Nat.lt_of_le_of_lt h_mid_le_hi h_hi
  
  have h_mid_some : arr[mid]? = some arr[mid] := by
    rw [Array.getElem?_eq_getElem h_mid_valid]
  let mid_val := arr[mid]
  
  if h_eq : mid_val = target then
    ⟨some mid, by
      simp [binary_search_spec]
      rw [h_mid_some]
      unfold mid_val at h_eq
      rw [h_eq]⟩
  else if h_lt : mid_val < target then
    if h_can_right : mid + 1 ≤ hi ∧ mid + 1 < arr.size then
      have h_term : hi - (mid + 1) < hi - lo := by omega
      let sub_result := binary_search_aux arr target h (mid + 1) hi h_can_right.2 h_hi
      ⟨sub_result.val, by
        have h_sub_spec := sub_result.property
        cases h_sub : sub_result.val with
        | none =>
          simp [binary_search_spec]
          intro i h_lo_le h_hi_le h_target_at_i
          rw [h_sub] at h_sub_spec
          simp [binary_search_spec] at h_sub_spec
          if h_i_le_mid : i ≤ mid then
            have h_i_valid : i < arr.size := by omega
            have h_arr_i_le_mid : arr[i] ≤ arr[mid] := 
              sorted_array_monotone arr h i mid h_i_valid h_mid_valid h_i_le_mid
            have h_target_eq : arr[i]? = some target := h_target_at_i
            rw [Array.getElem?_eq_getElem h_i_valid] at h_target_eq
            have h_target_val : arr[i] = target := by simp at h_target_eq; exact h_target_eq
            rw [h_target_val] at h_arr_i_le_mid
            unfold mid_val at h_lt
            omega
          else
            push_neg at h_i_le_mid
            have h_i_ge : mid + 1 ≤ i := h_i_le_mid
            exact h_sub_spec i h_i_ge h_hi_le h_target_at_i
        | some j =>
          simp [binary_search_spec]
          rw [h_sub] at h_sub_spec
          simp [binary_search_spec] at h_sub_spec
          exact h_sub_spec⟩
    else
      ⟨none, by
        simp [binary_search_spec]
        intro i h_lo_le h_hi_le h_target_at_i
        have h_i_le_mid : i ≤ mid := by
          by_contra h_not_le
          push_neg at h_not_le
          have h_i_gt_mid : i > mid := h_not_le
          have h_i_ge_mid_plus : i ≥ mid + 1 := h_i_gt_mid
          have h_mid_plus_le_hi : mid + 1 ≤ hi := h_i_ge_mid_plus.trans h_hi_le
          have h_mid_plus_lt_size : mid + 1 < arr.size := by omega
          exact h_can_right ⟨h_mid_plus_le_hi, h_mid_plus_lt_size⟩
        
        have h_i_valid : i < arr.size := by omega
        have h_arr_i_le_mid : arr[i] ≤ arr[mid] := 
          sorted_array_monotone arr h i mid h_i_valid h_mid_valid h_i_le_mid
        have h_target_eq : arr[i]? = some target := h_target_at_i
        rw [Array.getElem?_eq_getElem h_i_valid] at h_target_eq
        have h_target_val : arr[i] = target := by simp at h_target_eq; exact h_target_eq
        rw [h_target_val] at h_arr_i_le_mid
        unfold mid_val at h_lt
        omega⟩
  else
    have h_mid_ge_target : target ≤ mid_val := Nat.le_of_not_gt h_lt
    if h_can_left : mid > 0 ∧ lo ≤ mid - 1 ∧ mid - 1 < arr.size then
      have h_term : (mid - 1) - lo < hi - lo := by omega
      let sub_result := binary_search_aux arr target h lo (mid - 1) h_lo h_can_left.2.2
      ⟨sub_result.val, by
        have h_sub_spec := sub_result.property
        cases h_sub : sub_result.val with
        | none =>
          simp [binary_search_spec]
          intro i h_lo_le h_hi_le h_target_at_i
          rw [h_sub] at h_sub_spec
          simp [binary_search_spec] at h_sub_spec
          if h_i_ge_mid : i ≥ mid then
            have h_i_valid : i < arr.size := by omega
            have h_mid_le_arr_i : arr[mid] ≤ arr[i] := 
              sorted_array_monotone arr h mid i h_mid_valid h_i_valid h_i_ge_mid
            have h_target_eq : arr[i]? = some target := h_target_at_i
            rw [Array.getElem?_eq_getElem h_i_valid] at h_target_eq
            have h_target_val : arr[i] = target := by simp at h_target_eq; exact h_target_eq
            rw [h_target_val] at h_mid_le_arr_i
            have h_arr_mid_ge_target : arr[mid] ≥ target := by
              unfold mid_val at h_mid_ge_target
              exact h_mid_ge_target
            have h_mid_eq_target : arr[mid] = target := by omega
            have h_mid_val_eq_target : mid_val = target := by
              unfold mid_val
              exact h_mid_eq_target
            exact h_eq h_mid_val_eq_target
          else
            push_neg at h_i_ge_mid
            have h_i_le : i ≤ mid - 1 := Nat.le_sub_one_of_lt h_i_ge_mid
            exact h_sub_spec i h_lo_le h_i_le h_target_at_i
        | some j =>
          simp [binary_search_spec]
          rw [h_sub] at h_sub_spec
          simp [binary_search_spec] at h_sub_spec
          exact h_sub_spec⟩
    else
      ⟨none, by
        simp [binary_search_spec]
        intro i h_lo_le h_hi_le h_target_at_i
        -- Final case: use omega to prove i = mid directly
        push_neg at h_can_left
        
        -- Show i ≤ mid (same argument as before)
        have h_i_le_mid : i ≤ mid := by
          by_contra h_not_le
          push_neg at h_not_le
          have h_i_valid : i < arr.size := by omega
          have h_mid_le_arr_i : arr[mid] ≤ arr[i] := 
            sorted_array_monotone arr h mid i h_mid_valid h_i_valid (Nat.le_of_lt h_not_le)
          have h_target_eq : arr[i]? = some target := h_target_at_i
          rw [Array.getElem?_eq_getElem h_i_valid] at h_target_eq
          have h_target_val : arr[i] = target := by simp at h_target_eq; exact h_target_eq
          rw [h_target_val] at h_mid_le_arr_i
          have h_arr_mid_ge_target : arr[mid] ≥ target := by
            unfold mid_val at h_mid_ge_target
            exact h_mid_ge_target
          have h_mid_eq_target : arr[mid] = target := by omega
          have h_mid_val_eq_target : mid_val = target := by
            unfold mid_val
            exact h_mid_eq_target
          exact h_eq h_mid_val_eq_target
        
        -- Show i ≥ mid using omega-friendly reasoning
        have h_i_ge_mid : i ≥ mid := by
          -- Since h_can_left is false and we know various constraints, 
          -- we can derive lo ≥ mid using omega
          have h_lo_ge_mid : lo ≥ mid := by omega
          exact le_trans h_lo_ge_mid h_lo_le
        
        -- So i = mid
        have h_i_eq_mid : i = mid := by omega
        
        -- Derive contradiction
        rw [h_i_eq_mid] at h_target_at_i
        have h_target_eq : arr[mid]? = some target := h_target_at_i
        rw [Array.getElem?_eq_getElem h_mid_valid] at h_target_eq
        have h_target_val : arr[mid] = target := by simp at h_target_eq; exact h_target_eq
        have h_mid_val_eq_target : mid_val = target := by
          unfold mid_val
          exact h_target_val
        exact h_eq h_mid_val_eq_target⟩
termination_by hi - lo

