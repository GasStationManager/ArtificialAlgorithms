import Mathlib
import ArtificialAlgorithms.VFA.Maps

/-!
# VFA Chapter: Trie
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Trie.html

## Overview
Efficient lookup tables using binary tries keyed on positive binary numbers.
Includes a pedagogical development of binary number arithmetic, the trie data
structure with O(log N) lookup/insert, and an ADT correctness proof relating
tries to total maps.

## Mathlib Mappings
- VFA `positive` ↦ fresh `Positive` inductive (pedagogical)
- VFA `comparison` ↦ `Ordering` (Lean built-in)
- VFA `total_map` ↦ `VFA.Maps.TotalMap` (from Maps chapter)
- VFA `t_empty`/`t_update` ↦ `VFA.Maps.t_empty`/`VFA.Maps.t_update`
-/

namespace VFA.Trie

open VFA.Maps

-- ============================================
-- Section: Binary Number Representations
-- ============================================

/-- Positive binary numbers (Coq's `positive` type).
  - `xH` = 1
  - `xO p` = 2 * p (low bit 0)
  - `xI p` = 2 * p + 1 (low bit 1) -/
inductive Positive : Type where
  | xH : Positive
  | xO : Positive → Positive
  | xI : Positive → Positive
  deriving Repr, DecidableEq, BEq

namespace Positive

/-- Convert a positive number to a natural number. -/
def toNat : Positive → Nat
  | xH => 1
  | xO p => 2 * p.toNat
  | xI p => 2 * p.toNat + 1

def ten : Positive := xO (xI (xO xH))

#eval ten.toNat  -- 10

/-- Successor of a positive number. -/
def succ : Positive → Positive
  | xI p => xO (succ p)
  | xO p => xI p
  | xH => xO xH

/-- Addition with carry. -/
def addc : Bool → Positive → Positive → Positive
  | false, xI p, xI q => xO (addc true p q)
  | false, xI p, xO q => xI (addc false p q)
  | false, xI p, xH => xO (succ p)
  | false, xO p, xI q => xI (addc false p q)
  | false, xO p, xO q => xO (addc false p q)
  | false, xO p, xH => xI p
  | false, xH, xI q => xO (succ q)
  | false, xH, xO q => xI q
  | false, xH, xH => xO xH
  | true, xI p, xI q => xI (addc true p q)
  | true, xI p, xO q => xO (addc true p q)
  | true, xI p, xH => xI (succ p)
  | true, xO p, xI q => xO (addc true p q)
  | true, xO p, xO q => xI (addc false p q)
  | true, xO p, xH => xO (succ p)
  | true, xH, xI q => xI (succ q)
  | true, xH, xO q => xO (succ q)
  | true, xH, xH => xI xH

/-- Addition of positive numbers. -/
def add (x y : Positive) : Positive := addc false x y

/-- `toNat p ≥ 1` for all positive numbers. -/
theorem toNat_pos (p : Positive) : p.toNat > 0 := by
  induction p with
  | xH => simp [toNat]
  | xO p ih => simp [toNat]; omega
  | xI p ih => simp [toNat]

/-- Successor is correct: `toNat (succ p) = toNat p + 1`. -/
theorem succ_correct (p : Positive) : (succ p).toNat = p.toNat + 1 := by
  induction p with
  | xH => simp [succ, toNat]
  | xO p _ => simp [succ, toNat]
  | xI p ih => simp [succ, toNat, ih]; omega

/-- Addition with carry is correct. -/
theorem addc_correct (c : Bool) (p q : Positive) :
    (addc c p q).toNat = (if c then 1 else 0) + p.toNat + q.toNat := by
  induction p generalizing c q with
  | xH =>
    cases q with
    | xH => cases c <;> simp [addc, toNat]
    | xO q => cases c <;> simp [addc, toNat, succ_correct] <;> omega
    | xI q => cases c <;> simp [addc, toNat, succ_correct] <;> omega
  | xO p ih =>
    cases q with
    | xH => cases c <;> simp [addc, toNat, succ_correct]; omega
    | xO q => cases c <;> simp [addc, toNat, ih] <;> omega
    | xI q => cases c <;> simp [addc, toNat, ih] <;> omega
  | xI p ih =>
    cases q with
    | xH => cases c <;> simp [addc, toNat, succ_correct] <;> omega
    | xO q => cases c <;> simp [addc, toNat, ih] <;> omega
    | xI q => cases c <;> simp [addc, toNat, ih] <;> omega

/-- Addition is correct: `toNat (add p q) = toNat p + toNat q`. -/
theorem add_correct (p q : Positive) : (add p q).toNat = p.toNat + q.toNat := by
  unfold add; rw [addc_correct]; simp

/-- Three-way comparison of positive numbers. -/
def compare : Positive → Positive → Ordering
  | xI p, xI q => compare p q
  | xI p, xO q => match compare p q with | .lt => .lt | _ => .gt
  | xI _, xH => .gt
  | xO p, xI q => match compare p q with | .gt => .gt | _ => .lt
  | xO p, xO q => compare p q
  | xO _, xH => .gt
  | xH, xI _ => .lt
  | xH, xO _ => .lt
  | xH, xH => .eq

/-- Comparison is correct with respect to `toNat`. -/
theorem compare_correct (x y : Positive) :
    match compare x y with
    | .lt => x.toNat < y.toNat
    | .eq => x.toNat = y.toNat
    | .gt => x.toNat > y.toNat := by
  induction x generalizing y with
  | xH =>
    cases y with
    | xH => simp [compare, toNat]
    | xO q => simp [compare, toNat]; have := toNat_pos q; omega
    | xI q => simp [compare, toNat]; have := toNat_pos q; omega
  | xO p ih =>
    cases y with
    | xH => simp [compare, toNat]; have := toNat_pos p; omega
    | xO q =>
      simp [compare, toNat]
      have := ih q
      revert this; cases compare p q <;> intro h <;> omega
    | xI q =>
      simp only [compare, toNat]
      have := ih q
      revert this; cases compare p q <;> intro h <;> omega
  | xI p ih =>
    cases y with
    | xH => simp [compare, toNat]; have := toNat_pos p; omega
    | xO q =>
      simp only [compare, toNat]
      have := ih q
      revert this; cases compare p q <;> intro h <;> omega
    | xI q =>
      simp [compare, toNat]
      have := ih q
      revert this; cases compare p q <;> intro h <;> omega

end Positive

-- ============================================
-- Section: Trie Data Structure
-- ============================================

set_option linter.dupNamespace false in
/-- Binary trie. `Leaf` is the empty trie; `Node l x r` stores value `x` at
    the current position, with left subtrie `l` (for `xO`) and right subtrie
    `r` (for `xI`). -/
inductive Trie (A : Type) : Type where
  | Leaf : Trie A
  | Node : Trie A → A → Trie A → Trie A
  deriving Repr

/-- A trie table: a default value paired with a trie. -/
def TrieTable (A : Type) : Type := A × Trie A

/-- Empty trie table with a given default. -/
def TrieTable.empty {A : Type} (default : A) : TrieTable A :=
  (default, Trie.Leaf)

/-- Look up a key in a trie, returning `default` for missing entries. -/
def look {A : Type} (default : A) (i : Positive) (m : Trie A) : A :=
  match m with
  | Trie.Leaf => default
  | Trie.Node l x r =>
    match i with
    | Positive.xH => x
    | Positive.xO i' => look default i' l
    | Positive.xI i' => look default i' r

/-- Look up a key in a trie table. -/
def lookup {A : Type} (i : Positive) (t : TrieTable A) : A :=
  look t.1 i t.2

/-- Insert a value at a key in a trie. -/
def ins {A : Type} (default : A) (i : Positive) (a : A) (m : Trie A) : Trie A :=
  match m with
  | Trie.Leaf =>
    match i with
    | Positive.xH => Trie.Node Trie.Leaf a Trie.Leaf
    | Positive.xO i' => Trie.Node (ins default i' a Trie.Leaf) default Trie.Leaf
    | Positive.xI i' => Trie.Node Trie.Leaf default (ins default i' a Trie.Leaf)
  | Trie.Node l o r =>
    match i with
    | Positive.xH => Trie.Node l a r
    | Positive.xO i' => Trie.Node (ins default i' a l) o r
    | Positive.xI i' => Trie.Node l o (ins default i' a r)

/-- Insert a value at a key in a trie table. -/
def trieInsert {A : Type} (i : Positive) (a : A) (t : TrieTable A) : TrieTable A :=
  (t.1, ins t.1 i a t.2)

-- Example: three and ten mapped to true
def three_ten : TrieTable Bool :=
  trieInsert (.xI .xH) true (trieInsert (.xO (.xI (.xO .xH))) true (TrieTable.empty false))

#eval lookup (.xI .xH) three_ten          -- true (key 3)
#eval lookup (.xO (.xI (.xO .xH))) three_ten  -- true (key 10)
#eval lookup (.xO .xH) three_ten          -- false (key 2)

-- ============================================
-- Section: FastEnough (O(N log N) collision counting)
-- ============================================

/-- Count duplicate entries in a list using a trie table. -/
def collisionLoop (input : List Positive) (c : Nat) (table : TrieTable Bool) : Nat :=
  match input with
  | [] => c
  | a :: al =>
    if lookup a table then collisionLoop al (1 + c) table
    else collisionLoop al c (trieInsert a true table)

def collisions (input : List Positive) : Nat :=
  collisionLoop input 0 (TrieTable.empty false)

#eval collisions [.xI .xH, .xH, .xO (.xO .xH), .xH,
                  .xI (.xO .xH), .xI (.xO (.xO .xH)),
                  .xO .xH, .xO (.xI .xH)]  -- 1 (only xH is duplicated)

-- ============================================
-- Section: Correctness of Trie Operations
-- ============================================

/-- Looking up any key in a Leaf returns the default. -/
theorem look_leaf {A : Type} (a : A) (j : Positive) : look a j Trie.Leaf = a := by
  cases j <;> simp [look]

/-- Looking up the key we just inserted returns the inserted value. -/
theorem look_ins_same {A : Type} (a : A) (k : Positive) (v : A) (t : Trie A) :
    look a k (ins a k v t) = v := by
  induction k generalizing t with
  | xH => cases t <;> simp [ins, look]
  | xO k ih => cases t <;> simp [ins, look, ih]
  | xI k ih => cases t <;> simp [ins, look, ih]

/-- Looking up a different key after insert returns the original value. -/
theorem look_ins_other {A : Type} (a : A) (j k : Positive) (v : A) (t : Trie A)
    (hjk : j ≠ k) : look a j (ins a k v t) = look a j t := by
  induction j generalizing k t with
  | xH =>
    cases k with
    | xH => exact absurd rfl hjk
    | xO k' => cases t <;> simp [ins, look]
    | xI k' => cases t <;> simp [ins, look]
  | xO j ih =>
    cases k with
    | xH => cases t <;> simp [ins, look]
    | xO k' =>
      have hjk' : j ≠ k' := fun h => hjk (congr_arg Positive.xO h)
      have := fun t => ih k' t hjk'
      cases t <;> simp [ins, look, this]
    | xI k' => cases t <;> simp [ins, look]
  | xI j ih =>
    cases k with
    | xH => cases t <;> simp [ins, look]
    | xO k' => cases t <;> simp [ins, look]
    | xI k' =>
      have hjk' : j ≠ k' := fun h => hjk (congr_arg Positive.xI h)
      have := fun t => ih k' t hjk'
      cases t <;> simp [ins, look, this]

-- ============================================
-- Section: Bijection Between Positive and Nat
-- ============================================

/-- Convert a natural number to a positive: `0 ↦ xH`, `1 ↦ xO xH`, etc.
    This maps `n` to the `(n+1)`-th positive number. -/
def nat2pos : Nat → Positive
  | 0 => Positive.xH
  | n + 1 => Positive.succ (nat2pos n)

/-- Convert a positive number to a natural number (inverse of `nat2pos`).
    Maps `xH` to `0`, the `(n+1)`-th positive to `n`. -/
def pos2nat (p : Positive) : Nat := p.toNat - 1

/-- Helper: `nat2pos n` has `toNat` equal to `n + 1`. -/
private theorem nat2pos_toNat (n : Nat) : (nat2pos n).toNat = n + 1 := by
  induction n with
  | zero => simp [nat2pos, Positive.toNat]
  | succ n ih => simp [nat2pos, Positive.succ_correct, ih]

/-- `toNat` is injective on `Positive`. -/
private theorem toNat_injective (p q : Positive) (h : p.toNat = q.toNat) : p = q := by
  induction p generalizing q with
  | xH =>
    cases q with
    | xH => rfl
    | xO q => simp [Positive.toNat] at h; have := Positive.toNat_pos q; omega
    | xI q => simp [Positive.toNat] at h; have := Positive.toNat_pos q; omega
  | xO p ih =>
    cases q with
    | xH => simp [Positive.toNat] at h
    | xO q => simp [Positive.toNat] at h; exact congr_arg Positive.xO (ih q (by omega))
    | xI q => simp [Positive.toNat] at h; omega
  | xI p ih =>
    cases q with
    | xH => simp [Positive.toNat] at h; have := Positive.toNat_pos p; omega
    | xO q => simp [Positive.toNat] at h; omega
    | xI q => simp [Positive.toNat] at h; exact congr_arg Positive.xI (ih q (by omega))

/-- Roundtrip: `nat2pos (pos2nat p) = p`. -/
theorem pos2nat2pos (p : Positive) : nat2pos (pos2nat p) = p := by
  apply toNat_injective
  rw [nat2pos_toNat, pos2nat]
  have := Positive.toNat_pos p
  omega

/-- Roundtrip: `pos2nat (nat2pos i) = i`. -/
theorem nat2pos2nat (i : Nat) : pos2nat (nat2pos i) = i := by
  simp [pos2nat, nat2pos_toNat]

/-- `pos2nat` is injective. -/
theorem pos2nat_injective (p q : Positive) (h : pos2nat p = pos2nat q) : p = q := by
  have := congr_arg nat2pos h
  rwa [pos2nat2pos, pos2nat2pos] at this

/-- `nat2pos` is injective. -/
theorem nat2pos_injective (i j : Nat) (h : nat2pos i = nat2pos j) : i = j := by
  have := congr_arg pos2nat h
  rwa [nat2pos2nat, nat2pos2nat] at this

-- ============================================
-- Section: Table ADT Proofs
-- ============================================

/-- Representation invariant for trie tables. All tries are well-formed. -/
def is_trie {A : Type} (_ : TrieTable A) : Prop := True

/-- Abstraction function: interpret a trie table as a function on `Nat`. -/
def abstract {A : Type} (t : TrieTable A) (n : Nat) : A :=
  lookup (nat2pos n) t

/-- Abstraction relation: the trie table realizes a total map. -/
def Abs {A : Type} (t : TrieTable A) (m : TotalMap A) : Prop :=
  abstract t = m

theorem empty_is_trie {A : Type} (default : A) : is_trie (TrieTable.empty default) :=
  trivial

theorem insert_is_trie {A : Type} (i : Positive) (x : A) (t : TrieTable A)
    (_ : is_trie t) : is_trie (trieInsert i x t) :=
  trivial

theorem empty_relate {A : Type} (default : A) :
    Abs (TrieTable.empty default) (t_empty default) := by
  ext n
  simp [abstract, lookup, TrieTable.empty, look_leaf, t_empty]

theorem lookup_relate {A : Type} (i : Positive) (t : TrieTable A) (m : TotalMap A)
    (_ : is_trie t) (habs : Abs t m) : lookup i t = m (pos2nat i) := by
  have : abstract t = m := habs
  have := congr_fun this (pos2nat i)
  simp [abstract, pos2nat2pos] at this
  exact this

theorem insert_relate {A : Type} (k : Positive) (v : A) (t : TrieTable A) (cts : TotalMap A)
    (_ : is_trie t) (habs : Abs t cts) :
    Abs (trieInsert k v t) (t_update cts (pos2nat k) v) := by
  ext n
  simp only [Abs, abstract, lookup, trieInsert] at *
  by_cases heq : pos2nat k = n
  · subst heq
    rw [pos2nat2pos, look_ins_same]
    exact (t_update_eq A cts (pos2nat k) v).symm
  · have hne : nat2pos n ≠ k := by
      intro h; exact heq (by rw [← h, nat2pos2nat])
    rw [look_ins_other _ _ _ _ _ hne]
    rw [t_update_neq A v (pos2nat k) n cts heq]
    exact congr_fun habs n

-- Sanity check
example : Abs
    (trieInsert (.xI .xH) true (trieInsert (.xO (.xI (.xO .xH))) true (TrieTable.empty false)))
    (t_update (t_update (t_empty false) (pos2nat (.xO (.xI (.xO .xH)))) true)
              (pos2nat (.xI .xH)) true) := by
  apply insert_relate
  · exact trivial
  · apply insert_relate
    · exact trivial
    · exact empty_relate false

end VFA.Trie
