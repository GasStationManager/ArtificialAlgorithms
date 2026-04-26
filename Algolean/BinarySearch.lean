/-
Binary search expressed in the (vendored mini-)Algolean query model,
together with a worst-case complexity bound of `1 + Nat.log 2 (n + 1)`
read queries on a vector of length `n`.
-/

import Algolean.ReadOnlyVec
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic

namespace Algolean

open Prog

/--
Binary search on a sorted vector `v : Vector α n` for an element `x : α`,
expressed as a program in the `ReadOnlyVec α` query model.
-/
def binarySearchAlg [BEq α] [LawfulBEq α] (le : α → α → Bool) (v : Vector α n) (x : α)
    : Prog (ReadOnlyVec α) Bool := do
  if h : n = 0 then return false
  else
    let mid : Fin n := ⟨n / 2, Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)⟩
    let midval ← FreeM.lift (ReadOnlyVec.read v mid)
    if midval == x then
      return true
    else if le midval x then
      binarySearchAlg le (v.extract (mid + 1) n) x
    else
      binarySearchAlg le (v.extract 0 mid) x
termination_by n
decreasing_by
  all_goals simp_wf; omega

/-- Step lemma: `1 + log₂ a ≤ log₂ b` whenever `2 * a ≤ b` and `a ≠ 0`. -/
private lemma one_add_log_le_log_of_two_mul_le {a b : ℕ}
    (ha : a ≠ 0) (h : 2 * a ≤ b) :
    1 + Nat.log 2 a ≤ Nat.log 2 b := by
  calc
    1 + Nat.log 2 a = Nat.log 2 (a * 2) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.log_mul_base (b := 2) (n := a) (by decide : 1 < 2) ha).symm
    _ ≤ Nat.log 2 b := Nat.log_mono_right (Nat.mul_comm 2 a ▸ h)

/--
Time-complexity bound (auxiliary form): the number of `read` queries performed
by `binarySearchAlg` on a vector of length `n` is at most `1 + log₂ n` when
`n > 0`, and `0` when `n = 0`.
-/
private lemma binarySearchAlg_time_aux [BEq α] [LawfulBEq α] (le : α → α → Bool) (x : α) :
    ∀ (n : ℕ) (v : Vector α n),
      (binarySearchAlg le v x).time ReadOnlyVec.natCost ≤
        if n = 0 then 0 else 1 + Nat.log 2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v
    by_cases hn : n = 0
    · subst hn
      rw [binarySearchAlg]
      simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      -- Unfold one step of `binarySearchAlg`.
      rw [binarySearchAlg]
      simp only [hn, ↓reduceDIte, FreeM.lift_def, FreeM.bind_eq_bind, FreeM.liftBind_bind,
        FreeM.pure_bind, time_liftBind, ReadOnlyVec.natCost_cost,
        ReadOnlyVec.natCost_evalQuery, if_false]
      -- The remaining goal has the form
      --   1 + time (if v[mid] == x then return true
      --             else if le v[mid] x then bSA right else bSA left) ≤ 1 + Nat.log 2 n
      split_ifs with hEq hLe
      · -- found it
        simp
      · -- recurse on the right half: size is `min n n - (n/2 + 1) = n - (n/2 + 1) < n`.
        have hsize_lt : min n n - (n / 2 + 1) < n := by
          rw [Nat.min_self]; omega
        have ih_right := ih _ hsize_lt (v.extract (n / 2 + 1) n)
        -- Replace `min n n` by `n` everywhere in the IH bound.
        simp only [Nat.min_self] at ih_right
        have hrec :
            (binarySearchAlg le (v.extract (n / 2 + 1) n) x).time ReadOnlyVec.natCost
              ≤ Nat.log 2 n := by
          by_cases hsz : n - (n / 2 + 1) = 0
          · refine le_trans ?_ (Nat.zero_le _)
            simpa [hsz] using ih_right
          · refine le_trans ?_ (one_add_log_le_log_of_two_mul_le hsz ?_)
            · simpa [hsz] using ih_right
            · have : 2 * (n - (n / 2 + 1)) ≤ n := by omega
              exact this
        exact Nat.add_le_add_left hrec 1
      · -- recurse on the left half: size is `min (n/2) n - 0 = n/2 < n`.
        have hmle : (n / 2) ≤ n := Nat.le_of_lt (Nat.div_lt_self hpos (by decide))
        have hsize_lt : min (n / 2) n - 0 < n := by
          rw [Nat.sub_zero, Nat.min_eq_left hmle]
          exact Nat.div_lt_self hpos (by decide)
        have ih_left := ih _ hsize_lt (v.extract 0 (n / 2))
        -- Replace `min (n/2) n - 0` by `n/2` in the IH bound.
        simp only [Nat.sub_zero, Nat.min_eq_left hmle] at ih_left
        have hrec :
            (binarySearchAlg le (v.extract 0 (n / 2)) x).time ReadOnlyVec.natCost
              ≤ Nat.log 2 n := by
          by_cases hsz : n / 2 = 0
          · refine le_trans ?_ (Nat.zero_le _)
            simpa [hsz] using ih_left
          · refine le_trans ?_ (one_add_log_le_log_of_two_mul_le hsz ?_)
            · simpa [hsz] using ih_left
            · have : 2 * (n / 2) ≤ n := by omega
              exact this
        exact Nat.add_le_add_left hrec 1

/--
Headline complexity bound: `binarySearchAlg` performs at most `1 + log₂ (n + 1)`
read queries on a vector of length `n`, for any `n` (including `n = 0`).
-/
theorem binarySearchAlg_time_le [BEq α] [LawfulBEq α] (le : α → α → Bool)
    (v : Vector α n) (x : α) :
    (binarySearchAlg le v x).time ReadOnlyVec.natCost ≤ 1 + Nat.log 2 (n + 1) := by
  by_cases hn : n = 0
  · subst hn
    have h := binarySearchAlg_time_aux (le := le) (x := x) 0 v
    have h0 : (binarySearchAlg le v x).time ReadOnlyVec.natCost ≤ 0 := by simpa using h
    exact le_trans h0 (Nat.zero_le _)
  · have h := binarySearchAlg_time_aux (le := le) (x := x) n v
    have h1 : (binarySearchAlg le v x).time ReadOnlyVec.natCost ≤ 1 + Nat.log 2 n := by
      simpa [hn] using h
    have hmono : Nat.log 2 n ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (Nat.le_add_right n 1)
    exact le_trans h1 (Nat.add_le_add_left hmono 1)

/-! ### Correctness -/

section Correctness
variable {α : Type}

/-- Pairwise relations are preserved under `Vector.extract`. -/
private lemma pairwise_extract (R : α → α → Prop) {n : ℕ} {v : Vector α n}
    (h : v.toList.Pairwise R) (start stop : ℕ) :
    (v.extract start stop).toList.Pairwise R := by
  rw [Vector.toList_extract]
  exact h.drop.take

/-- Every element of `v.extract start stop` is also an element of `v`. -/
private lemma mem_of_mem_extract {n : ℕ} {v : Vector α n} {start stop : ℕ} {x : α}
    (hx : x ∈ v.extract start stop) : x ∈ v := by
  rw [← Vector.mem_toList_iff] at hx ⊢
  rw [Vector.toList_extract] at hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

variable [BEq α] [LawfulBEq α]

/--
Correctness: under `le` antisymmetric and `v` sorted, `binarySearchAlg` evaluates
to `true` exactly when `x` belongs to `v`.
-/
theorem binarySearchAlg_eval (le : α → α → Bool) [Std.Antisymm (fun a b => le a b = true)] :
    ∀ (n : ℕ) (v : Vector α n) (x : α),
      v.toList.Pairwise (fun a b => le a b = true) →
      ((binarySearchAlg le v x).eval ReadOnlyVec.natCost = true ↔ x ∈ v) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v x hSorted
    by_cases hn : n = 0
    · -- n = 0: vector is empty so x ∉ v, and the algorithm returns false.
      subst hn
      have hxv : ¬ x ∈ v := by
        intro h
        rw [← Vector.mem_toList_iff] at h
        have hempty : v.toList = [] :=
          List.length_eq_zero_iff.mp (by simp)
        rw [hempty] at h
        exact absurd h List.not_mem_nil
      rw [binarySearchAlg]
      simp only [↓reduceDIte]
      show (Prog.eval (FreeM.pure false) ReadOnlyVec.natCost = true) ↔ x ∈ v
      simp
      exact hxv
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hn2 : n / 2 < n := Nat.div_lt_self hpos (by decide)
      let mid : Fin n := ⟨n / 2, hn2⟩
      have hmid_lt : (mid : ℕ) < v.toList.length := by simp
      have hmid_val : v[mid] = v[n / 2] := rfl
      rw [binarySearchAlg]
      simp only [hn, ↓reduceDIte, FreeM.lift_def, FreeM.bind_eq_bind, FreeM.liftBind_bind,
        FreeM.pure_bind, Prog.eval_liftBind, ReadOnlyVec.natCost_evalQuery]
      split_ifs with hEq hLe
      · -- found
        have hmid_eq : v[mid] = x := LawfulBEq.eq_of_beq hEq
        constructor
        · intro _
          rw [← hmid_eq]
          exact Vector.getElem_mem mid.isLt
        · intro _; rfl
      · -- recurse right
        have hsize_lt : min n n - ((mid : ℕ) + 1) < n := by
          rw [Nat.min_self]; omega
        have ih_right := ih _ hsize_lt (v.extract ((mid : ℕ) + 1) n) x
          (pairwise_extract _ hSorted _ _)
        rw [ih_right]
        have hmid_ne : v[mid] ≠ x := by
          intro h
          apply hEq
          rw [h]
          exact BEq.rfl
        constructor
        · -- x ∈ v.extract → x ∈ v
          exact mem_of_mem_extract
        · intro hx
          rw [← Vector.mem_toList_iff] at hx
          have hsplit : x ∈ v.toList.take ((mid : ℕ) + 1) ∨ x ∈ v.toList.drop ((mid : ℕ) + 1) := by
            have := List.take_append_drop ((mid : ℕ) + 1) v.toList ▸ hx
            exact List.mem_append.mp this
          rcases hsplit with hL | hR
          · -- x in take (mid+1): split into take mid and {v[mid]}
            rw [List.take_succ_eq_append_getElem hmid_lt] at hL
            rcases List.mem_append.mp hL with h | h
            · -- x ∈ take mid → by sorted, le x v[mid]; antisymm → x = v[mid] : contradiction
              have hmid_mem_drop : v.toList[(mid : ℕ)] ∈ v.toList.drop (mid : ℕ) := by
                rw [List.drop_eq_getElem_cons hmid_lt]; exact List.mem_cons_self
              have hxle : le x v.toList[(mid : ℕ)] = true :=
                hSorted.rel_of_mem_take_of_mem_drop h hmid_mem_drop
              have hxle' : le x v[mid] = true := by simpa using hxle
              have : x = v[mid] :=
                Std.Antisymm.antisymm (r := fun a b => le a b = true) _ _ hxle' hLe
              exact absurd this.symm hmid_ne
            · -- x = v.toList[mid] = v[mid]: contradicts hmid_ne
              rw [List.mem_singleton] at h
              have : v[mid] = x := by
                have : v[mid] = v.toList[(mid : ℕ)] := by simp
                rw [this]; exact h.symm
              exact absurd this hmid_ne
          · -- x ∈ drop (mid+1) → x ∈ v.extract (mid+1) n
            rw [← Vector.mem_toList_iff, Vector.toList_extract]
            have htake :
                (v.toList.drop ((mid : ℕ) + 1)).take (n - ((mid : ℕ) + 1)) =
                  v.toList.drop ((mid : ℕ) + 1) := by
              apply List.take_of_length_le; simp
            rw [htake]; exact hR
      · -- recurse left
        have hmle : (mid : ℕ) ≤ n := Nat.le_of_lt mid.isLt
        have hsize_lt : min (mid : ℕ) n - 0 < n := by
          rw [Nat.sub_zero, Nat.min_eq_left hmle]; exact hn2
        have ih_left := ih _ hsize_lt (v.extract 0 (mid : ℕ)) x
          (pairwise_extract _ hSorted _ _)
        rw [ih_left]
        have hmid_ne : v[mid] ≠ x := by
          intro h
          apply hEq
          rw [h]
          exact BEq.rfl
        constructor
        · exact mem_of_mem_extract
        · intro hx
          rw [← Vector.mem_toList_iff] at hx
          have hsplit : x ∈ v.toList.take (mid : ℕ) ∨ x ∈ v.toList.drop (mid : ℕ) := by
            have := List.take_append_drop (mid : ℕ) v.toList ▸ hx
            exact List.mem_append.mp this
          rcases hsplit with hL | hR
          · -- x ∈ take mid → x ∈ v.extract 0 mid
            rw [← Vector.mem_toList_iff, Vector.toList_extract]
            have htake :
                (v.toList.drop 0).take ((mid : ℕ) - 0) = v.toList.take (mid : ℕ) := by
              simp
            rw [htake]; exact hL
          · -- x ∈ drop mid → x = v[mid] or x ∈ drop (mid+1) (sorted ⇒ le v[mid] x ⇒ contradicts hLe)
            rw [List.drop_eq_getElem_cons hmid_lt] at hR
            rcases List.mem_cons.mp hR with h | h
            · -- x = v.toList[mid] = v[mid]: contradicts hmid_ne
              have : v[mid] = x := by
                have : v[mid] = v.toList[(mid : ℕ)] := by simp
                rw [this]; exact h.symm
              exact absurd this hmid_ne
            · -- x ∈ drop (mid+1): le v[mid] x by sorted, but ¬hLe
              have hmid_mem_take : v.toList[(mid : ℕ)] ∈ v.toList.take ((mid : ℕ) + 1) := by
                rw [List.take_succ_eq_append_getElem hmid_lt]
                exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
              have hxle : le v.toList[(mid : ℕ)] x = true :=
                hSorted.rel_of_mem_take_of_mem_drop hmid_mem_take h
              have : le v[mid] x = true := by simpa using hxle
              exact absurd this hLe

end Correctness

end Algolean
