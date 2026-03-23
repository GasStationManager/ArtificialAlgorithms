/-
# AddTwoNumbers — Verified Efficient Linked-List Addition

Add two non-negative integers represented as linked lists of digits
in reverse order (least significant digit first). Each element is a
single digit (0–9). Return the sum as a linked list, also in reverse order.

Source: Verina benchmark `verina_advanced_5`

## Approach
Imperative loop with mvcgen verification. Uses `for` over `List.zipWithAll`
to process both lists in a single pass, then handles the final carry.
This compiles to an efficient loop (no stack overflow on large inputs).

Done by Claude Opus 4.6 on Claude Code using the mvcgen skill.
-/

import Std.Tactic.Do
import Mathlib

open Std.Do

set_option maxHeartbeats 1600000

/-! ## Specification -/

def listToNat : List Nat → Nat
  | []      => 0
  | d :: ds => d + 10 * listToNat ds

def addTwoNumbers_precond (l1 l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])

def addTwoNumbers_postcond (l1 l2 result : List Nat)
    (_h_precond : addTwoNumbers_precond l1 l2) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10)

/-! ## Implementation -/

def addTwoNumbers_body (l1 l2 : List Nat) : Id (List Nat) := do
  let pairs := List.zipWithAll (fun a b => (a.getD 0, b.getD 0)) l1 l2
  let mut carry := 0
  let mut result : Array Nat := #[]
  for pair in pairs do
    let s := pair.1 + pair.2 + carry
    result := result.push (s % 10)
    carry := s / 10
  if carry > 0 then
    result := result.push carry
  return result.toList

def addTwoNumbers (l1 l2 : List Nat) (_h : addTwoNumbers_precond l1 l2) : List Nat :=
  (addTwoNumbers_body l1 l2).run

/-! ## Helper lemmas -/

@[simp] theorem listToNat_nil : listToNat [] = 0 := rfl
@[simp] theorem listToNat_cons (d : Nat) (ds : List Nat) :
    listToNat (d :: ds) = d + 10 * listToNat ds := rfl

theorem listToNat_append_singleton (l : List Nat) (d : Nat) :
    listToNat (l ++ [d]) = listToNat l + d * 10 ^ l.length := by
  induction l with
  | nil => simp [listToNat]
  | cons x xs ih => simp [listToNat, ih]; ring

theorem listToNat_zipWithAll_fst (l1 l2 : List Nat) :
    listToNat ((List.zipWithAll (fun a b => (a.getD 0, b.getD 0)) l1 l2).map Prod.fst)
    = listToNat l1 := by
  rw [List.map_zipWithAll]
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil => rfl
    | cons y ys _ =>
      simp only [List.zipWithAll]
      show listToNat (List.map (fun (_ : Nat) => (none : Option Nat).getD 0) (y :: ys)) = 0
      induction (y :: ys) with
      | nil => rfl
      | cons _ _ ih2 => show 0 + 10 * _ = 0; linarith [ih2]
  | cons x xs ih =>
    cases l2 with
    | nil =>
      simp only [List.zipWithAll]
      show listToNat (List.map (fun (a : Nat) => (some a : Option Nat).getD 0) (x :: xs)) = _
      induction (x :: xs) with
      | nil => rfl
      | cons a as ih2 => show a + 10 * _ = a + 10 * _; linarith [ih2]
    | cons y ys =>
      simp only [List.zipWithAll, listToNat, Option.getD_some]; linarith [ih ys]

theorem listToNat_zipWithAll_snd (l1 l2 : List Nat) :
    listToNat ((List.zipWithAll (fun a b => (a.getD 0, b.getD 0)) l1 l2).map Prod.snd)
    = listToNat l2 := by
  rw [List.map_zipWithAll]
  induction l2 generalizing l1 with
  | nil =>
    induction l1 with
    | nil => rfl
    | cons x xs _ =>
      simp only [List.zipWithAll]
      show listToNat (List.map (fun (_ : Nat) => (none : Option Nat).getD 0) (x :: xs)) = 0
      induction (x :: xs) with
      | nil => rfl
      | cons _ _ ih2 => show 0 + 10 * _ = 0; linarith [ih2]
  | cons y ys ih =>
    cases l1 with
    | nil =>
      simp only [List.zipWithAll]
      show listToNat (List.map (fun (b : Nat) => (some b : Option Nat).getD 0) (y :: ys)) = _
      induction (y :: ys) with
      | nil => rfl
      | cons a as ih2 => show a + 10 * _ = a + 10 * _; linarith [ih2]
    | cons x xs =>
      simp only [List.zipWithAll, listToNat, Option.getD_some]; linarith [ih xs]

theorem zipWithAll_digit_bound (l1 l2 : List Nat) (hd1 : ∀ d ∈ l1, d < 10) (hd2 : ∀ d ∈ l2, d < 10)
    (p : Nat × Nat) (hp : p ∈ List.zipWithAll (fun a b => (a.getD 0, b.getD 0)) l1 l2) :
    p.1 < 10 ∧ p.2 < 10 := by
  induction l1 generalizing l2 p with
  | nil =>
    cases l2 with
    | nil => simp [List.zipWithAll] at hp
    | cons y ys =>
      simp only [List.zipWithAll, List.mem_map] at hp
      obtain ⟨b, hb_mem, hb_eq⟩ := hp; subst hb_eq
      simp [Option.getD_none, Option.getD_some]; exact hd2 b hb_mem
  | cons x xs ih =>
    cases l2 with
    | nil =>
      simp only [List.zipWithAll, List.mem_map] at hp
      obtain ⟨a, ha_mem, ha_eq⟩ := hp; subst ha_eq
      simp [Option.getD_none, Option.getD_some]; exact hd1 a ha_mem
    | cons y ys =>
      simp only [List.zipWithAll, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [Option.getD_some]
        exact ⟨hd1 x (List.mem_cons.mpr (.inl rfl)), hd2 y (List.mem_cons.mpr (.inl rfl))⟩
      · exact ih ys (fun d hd => hd1 d (List.mem_cons.mpr (.inr hd)))
          (fun d hd => hd2 d (List.mem_cons.mpr (.inr hd))) p hp

theorem mod_div_identity (s n : Nat) :
    (s % 10) * 10 ^ n + (s / 10) * 10 ^ (n + 1) = s * 10 ^ n := by
  rw [pow_succ]
  calc s % 10 * 10 ^ n + s / 10 * (10 ^ n * 10)
      = (s % 10 + 10 * (s / 10)) * 10 ^ n := by ring
    _ = s * 10 ^ n := by rw [Nat.mod_add_div]

/-! ## Correctness proof via mvcgen -/

theorem addTwoNumbers_body_spec (l1 l2 : List Nat)
    (hd1 : ∀ d ∈ l1, d < 10) (hd2 : ∀ d ∈ l2, d < 10) :
    ⦃⌜True⌝⦄ addTwoNumbers_body l1 l2
    ⦃⇓ r => ⌜listToNat r = listToNat l1 + listToNat l2 ∧ ∀ d ∈ r, d < 10⌝⦄ := by
  unfold addTwoNumbers_body
  mvcgen invariants
  · ⇓⟨cursor, ⟨carry, result⟩⟩ =>
      ⌜listToNat result.toList + carry * 10 ^ result.size
        = listToNat (cursor.prefix.map Prod.fst) + listToNat (cursor.prefix.map Prod.snd)
      ∧ carry ≤ 1
      ∧ (∀ d ∈ result.toList, d < 10)
      ∧ result.size = cursor.prefix.length⌝
  -- vc1.step: loop invariant preserved
  case vc1.step =>
    next pref cur suff h_split b _ _ _ h_full =>
    obtain ⟨h_inv, h_carry, h_digits, h_size⟩ := h_full
    have h_cur_mem : cur ∈ List.zipWithAll (fun a b => (a.getD 0, b.getD 0)) l1 l2 := by
      rw [h_split]; simp
    obtain ⟨h_c1, h_c2⟩ := zipWithAll_digit_bound l1 l2 hd1 hd2 cur h_cur_mem
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Numerical invariant
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [listToNat_append_singleton, listToNat_append_singleton]; simp only [List.length_map]
      -- The goal has let-bound result✝ and carry✝; rewrite to unfold them
      rw [show (b.snd.push ((cur.1 + cur.2 + b.fst) % 10)).toList
        = b.snd.toList ++ [(cur.1 + cur.2 + b.fst) % 10] from Array.toList_push ..]
      rw [listToNat_append_singleton, Array.length_toList]
      rw [show (b.snd.push ((cur.1 + cur.2 + b.fst) % 10)).size
        = b.snd.size + 1 from Array.size_push ..]
      rw [h_size] at h_inv ⊢
      -- Zeta-reduce the let bindings
      change listToNat b.snd.toList
        + (cur.1 + cur.2 + b.fst) % 10 * 10 ^ pref.length
        + (cur.1 + cur.2 + b.fst) / 10 * 10 ^ (pref.length + 1)
        = _
      nlinarith [mod_div_identity (cur.1 + cur.2 + b.fst) pref.length]
    · omega
    · intro d hd; rw [Array.toList_push] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact h_digits d hd
      · subst hd; exact Nat.mod_lt _ (by omega)
    · -- |result| = |prefix ++ [cur]|
      change (b.snd.push _).size = _
      simp [Array.size_push, h_size, List.length_append]
  -- vc3: carry > 0 after loop
  case vc3.post.success.isTrue =>
    next r _ h_pos h_full =>
    obtain ⟨h_inv, h_carry, h_digits, _⟩ := h_full
    rw [listToNat_zipWithAll_fst, listToNat_zipWithAll_snd] at h_inv
    constructor
    · rw [Array.toList_push, listToNat_append_singleton, Array.length_toList]; linarith
    · intro d hd; rw [Array.toList_push] at hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact h_digits d hd
      · subst hd; omega
  -- vc4: carry = 0 after loop
  case vc4.post.success.isFalse =>
    next r _ h_not_pos h_full =>
    obtain ⟨h_inv, _, h_digits, _⟩ := h_full
    rw [listToNat_zipWithAll_fst, listToNat_zipWithAll_snd] at h_inv
    have h_zero : r.fst = 0 := by omega
    rw [h_zero] at h_inv; simp at h_inv
    exact ⟨h_inv, h_digits⟩

/-! ## Connecting to function definition -/

theorem addTwoNumbers_correct (l1 l2 : List Nat) (h : addTwoNumbers_precond l1 l2) :
    listToNat (addTwoNumbers l1 l2 h) = listToNat l1 + listToNat l2 :=
  (addTwoNumbers_body_spec l1 l2 h.2.2.1 h.2.2.2.1 trivial).1

theorem addTwoNumbers_digits_bound (l1 l2 : List Nat) (h : addTwoNumbers_precond l1 l2) :
    ∀ d ∈ addTwoNumbers l1 l2 h, d < 10 :=
  (addTwoNumbers_body_spec l1 l2 h.2.2.1 h.2.2.2.1 trivial).2

theorem addTwoNumbers_spec_satisfied (l1 l2 : List Nat)
    (h_precond : addTwoNumbers_precond l1 l2) :
    addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2 h_precond) h_precond :=
  ⟨addTwoNumbers_correct l1 l2 h_precond,
   addTwoNumbers_digits_bound l1 l2 h_precond⟩
