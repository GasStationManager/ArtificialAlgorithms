/-
Insertion Sort
By Opus 4, on Claude Desktop with LeanTool and LeanExplore MCP tools
Prompted with starter code:
```
import Mathlib

def my_insert (x : Nat) (l : List Nat) (hl: l.Sorted (· ≤ ·)) 
: {y:List Nat//y.Sorted (· ≤ ·) ∧ y.Perm (x::l)} :=
  match hm:l with
  | [] => ⟨ [x], by simp[List.Sorted]⟩ 
  | h :: t => 
    if hcomp: x ≤ h then 
      ⟨ x :: h :: t,
        by {
          sorry
        }⟩  
    else 
      have: t.Sorted (· ≤ ·):=by {
        sorry
      }
      let res:=my_insert x t this
      ⟨ h :: res.val,by {
        sorry
      }⟩ 

def my_sort (l : List Nat) 
: {y:List Nat//y.Sorted (· ≤ ·) ∧
  l.Perm y} :=
  match l with
  | [] => ⟨[], by sorry⟩ 
  | h :: t => 
    let recval:=my_sort t
    let res:=my_insert h recval.val recval.2.left
    ⟨ res.val, by sorry⟩ 
```
-/

import Mathlib

/-- Insert a natural number into a sorted list, maintaining sortedness and proving the result
    is a permutation of the original element prepended to the list -/
def my_insert (x : Nat) (l : List Nat) (hl: l.Sorted (· ≤ ·)) 
: {y:List Nat//y.Sorted (· ≤ ·) ∧ y.Perm (x::l)} :=
  match hm:l with
  | [] => ⟨ [x], by simp[List.Sorted]⟩ 
  | h :: t => 
    if hcomp: x ≤ h then 
      ⟨ x :: h :: t,
        by {
          constructor
          · -- Prove x :: h :: t is sorted
            rw [List.sorted_cons]
            constructor
            · -- Prove ∀ b ∈ h :: t, x ≤ b
              intro b hb
              cases hb with
              | head => exact hcomp
              | tail _ hb' =>
                have h_le_b : h ≤ b := List.rel_of_pairwise_cons hl hb'
                exact Nat.le_trans hcomp h_le_b
            · -- h :: t is sorted
              exact hl
          · -- Prove x :: h :: t ~ x :: h :: t
            exact List.Perm.refl _
        }⟩  
    else 
      have: t.Sorted (· ≤ ·):=by {
        exact List.Sorted.of_cons hl
      }
      let res:=my_insert x t this
      ⟨ h :: res.val,by {
        constructor
        · -- Prove h :: res.val is sorted
          rw [List.sorted_cons]
          constructor
          · -- Prove ∀ b ∈ res.val, h ≤ b
            intro b hb
            -- b is in res.val, which is a permutation of x :: t
            have b_in_xt : b ∈ x :: t := res.2.2.subset hb
            cases b_in_xt with
            | head => 
              -- b = x, and we know h < x
              have h_lt_x : h < x := Nat.lt_of_not_le hcomp
              exact Nat.le_of_lt h_lt_x
            | tail _ hb_in_t =>
              -- b ∈ t, and since h :: t is sorted, h ≤ b
              exact List.rel_of_pairwise_cons hl hb_in_t
          · -- res.val is sorted
            exact res.2.1
        · -- Prove h :: res.val ~ x :: h :: t
          -- res.val ~ x :: t, so h :: res.val ~ h :: x :: t
          have perm1 : (h :: res.val).Perm (h :: x :: t) := List.Perm.cons h res.2.2
          -- h :: x :: t ~ x :: h :: t (by swap)
          have perm2 : (h :: x :: t).Perm (x :: h :: t) := List.Perm.swap x h t
          -- Transitivity
          exact List.Perm.trans perm1 perm2
      }⟩ 

/-- Sort a list of natural numbers using insertion sort, proving the result is sorted
    and is a permutation of the original list -/
def my_sort (l : List Nat) 
: {y:List Nat//y.Sorted (· ≤ ·) ∧ l.Perm y} :=
  match l with
  | [] => ⟨[], by 
    constructor
    · -- Empty list is sorted
      exact List.sorted_nil
    · -- [] ~ []
      exact List.Perm.refl []
  ⟩ 
  | h :: t => 
    let recval:=my_sort t
    let res:=my_insert h recval.val recval.2.left
    ⟨ res.val, by 
      constructor
      · -- res.val is sorted (by construction of my_insert)
        exact res.2.1
      · -- (h :: t) ~ res.val
        -- We have: t ~ recval.val (from recursive call)
        -- We have: res.val ~ h :: recval.val (from my_insert)
        -- So we need: h :: t ~ h :: recval.val ~ res.val
        have perm1 : (h :: t).Perm (h :: recval.val) := List.Perm.cons h recval.2.2
        have perm2 : res.val.Perm (h :: recval.val) := res.2.2
        exact List.Perm.trans perm1 perm2.symm
    ⟩

