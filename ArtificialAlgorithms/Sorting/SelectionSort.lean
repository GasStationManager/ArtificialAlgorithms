/-
Selection Sort
By Sonnet 4, on Claude Desktop with LeanTool and LeanExplore
Prompted with the following implementation + proof sketch, which was adapted from an earlier implementation by Grok 4 + Sonnet 4
```
import Mathlib
-- Helper function to find minimum element in a list
def findMin (l : List Int) (h: l.length > 0)
: {y:Int// y∈ l ∧ ∀ x∈ l, y≤ x} :=
  match hm:l with
  | [] => ⟨0, by grind⟩ 
  | [x] => ⟨ x, by sorry⟩ 
  | x :: y:: xs => 
    let res:= findMin (y::xs) (by simp) 
    ⟨if x ≤ res then x else res, by sorry⟩ 

-- Helper function to remove first occurrence of an element
def removeFirst (l : List Int) (val : Int) (h: val∈ l)
: {y:List Int // l.Perm (val::y)} :=
  match l with
  | [] => ⟨ [], by grind⟩ 
  | x :: xs => 
    if hif: x = val then 
      ⟨ xs,by sorry⟩  
    else 
      let res:=removeFirst xs val (by grind)
      ⟨ x :: res, by sorry⟩  

-- Main selection sort function
def selectionSort (l : List Int) 
: {y:List Int //y.Sorted (· ≤ ·) ∧ y.Perm l} :=
  if hlen:l.length=0 then
    ⟨ [], by sorry⟩ 
  else 
    let minv:= findMin l (by grind) 
    let rest:=removeFirst l minv (by grind)
    have: rest.val.length<l.length :=by 
      have hpermlen: l.length = (minv.val::rest.val).length:=by grind [List.Perm.length_eq]
      sorry
    ⟨ minv :: selectionSort rest, sorry⟩ 
termination_by l.length
```
-/

import Mathlib

-- Helper function to find minimum element in a list
def findMin (l : List Int) (h: l ≠ [])
: {y:Int// y∈ l ∧ ∀ x∈ l, y≤ x} :=
  match l with
  | [] => by contradiction
  | [x] => ⟨ x, by simp⟩ 
  | x :: y:: xs => 
    let res:= findMin (y::xs) (by simp) 
    ⟨if x ≤ res.val then x else res.val, by
      constructor
      · -- proving membership 
        split_ifs with h_cond
        · -- case x ≤ res, so we choose x
          simp [List.mem_cons]
        · -- case x > res, so we choose res
          have : res.val ∈ y::xs := res.2.1
          exact List.mem_cons_of_mem x this
      · -- proving minimality
        intro z hz
        split_ifs with h_cond
        · -- case x ≤ res, so we chose x
          rw [List.mem_cons] at hz
          cases hz with
          | inl h_eq => simp [h_eq]
          | inr h_mem => 
            have h_res_le_z : res.val ≤ z := res.2.2 z h_mem
            exact le_trans h_cond h_res_le_z
        · -- case x > res, so we chose res  
          rw [List.mem_cons] at hz
          cases hz with
          | inl h_eq => 
            simp [h_eq]
            exact le_of_not_le h_cond
          | inr h_mem =>
            exact res.2.2 z h_mem⟩ 

-- Helper function to remove first occurrence of an element
def removeFirst (l : List Int) (val : Int) (h: val∈ l)
: {y:List Int // l.Perm (val::y)} :=
  match l with
  | [] => by simp at h
  | x :: xs => 
    if hif: x = val then 
      ⟨ xs, by rw [hif]⟩  
    else 
      let res:=removeFirst xs val (by 
        rw [List.mem_cons] at h
        cases h with
        | inl h_eq => rw [h_eq] at hif; contradiction
        | inr h_mem => exact h_mem)
      ⟨ x :: res.val, by
        -- need to prove (x :: xs).Perm (val :: x :: res.val)
        -- we know xs.Perm (val :: res.val) from res.2
        have h_perm : xs.Perm (val :: res.val) := res.2
        -- so (x :: xs).Perm (x :: val :: res.val)
        have h1 : (x :: xs).Perm (x :: val :: res.val) := List.Perm.cons x h_perm
        -- and (x :: val :: res.val).Perm (val :: x :: res.val) by swapping
        have h2 : (x :: val :: res.val).Perm (val :: x :: res.val) := List.Perm.swap val x res.val
        exact List.Perm.trans h1 h2⟩  

-- Main selection sort function
def selectionSort (l : List Int) 
: {y:List Int //y.Sorted (· ≤ ·) ∧ y.Perm l} :=
  if hlen:l = [] then
    ⟨ [], by 
      constructor
      · exact List.sorted_nil
      · simp [hlen]⟩ 
  else 
    let minv:= findMin l hlen
    let rest:=removeFirst l minv.val (by exact minv.2.1)
    have h_len: rest.val.length < l.length :=by 
      have hpermlen: l.length = (minv.val::rest.val).length:=by 
        rw [List.Perm.length_eq]
        exact rest.2
      simp [List.length_cons] at hpermlen
      linarith
    ⟨ minv.val :: (selectionSort rest.val).val, by
      let sorted_rest := selectionSort rest.val
      constructor
      · -- prove sorted
        rw [List.sorted_cons]
        constructor
        · -- prove minv.val ≤ all elements in sorted_rest.val  
          intro b hb
          -- b ∈ sorted_rest.val, and sorted_rest.val.Perm rest.val
          have h_b_in_rest : b ∈ rest.val := by
            have h_perm_rest : sorted_rest.val.Perm rest.val := sorted_rest.2.2
            exact List.Perm.mem_iff h_perm_rest |>.mp hb
          -- rest.val came from removing minv.val from l, so b was in l originally
          have h_b_in_l : b ∈ l := by
            have h_rest_perm : l.Perm (minv.val :: rest.val) := rest.2
            have h_b_in_cons : b ∈ (minv.val :: rest.val) := List.mem_cons_of_mem minv.val h_b_in_rest
            exact List.Perm.mem_iff h_rest_perm.symm |>.mp h_b_in_cons
          exact minv.2.2 b h_b_in_l
        · -- prove sorted_rest.val is sorted
          exact sorted_rest.2.1
      · -- prove permutation
        have h_rest_perm : l.Perm (minv.val :: rest.val) := rest.2
        have h_sorted_perm : sorted_rest.val.Perm rest.val := sorted_rest.2.2
        have h_cons_perm : (minv.val :: sorted_rest.val).Perm (minv.val :: rest.val) := 
          List.Perm.cons minv.val h_sorted_perm
        exact List.Perm.trans h_cons_perm h_rest_perm.symm⟩ 
termination_by l.length

