import Mathlib
import ArtificialAlgorithms.VFA.Maps
import ArtificialAlgorithms.VFA.Sort

/-!
# VFA Chapter: SearchTree (Binary Search Trees)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html

## Overview
Defines binary search trees (BSTs) and proves correctness of lookup/insert operations
via three approaches: algebraic specification, elements-based specification, and
model-based specification. Includes in-order traversal, sorted elements, and
abstraction to partial maps.

## Mathlib Mappings
- VFA `key` ↦ `Nat` (used directly, no alias)
- VFA `tree V` ↦ `inductive Tree (V : Type)`
- VFA `ForallT` ↦ recursive def (not inductive)
- VFA `BST` ↦ inductive prop
- VFA `partial_map` ↦ `VFA.Maps.PartialMap`
- VFA `empty` ↦ `VFA.Maps.p_empty`
- VFA `update` ↦ `VFA.Maps.p_update`
- VFA `NoDup` ↦ `List.Nodup` (Mathlib)
- VFA `Sort.sorted` ↦ `VFA.Sort.sorted`
-/

namespace VFA.SearchTree

open VFA.Maps (TotalMap t_empty t_update PartialMap p_empty p_update
               t_update_eq t_update_neq t_update_shadow t_update_same t_update_permute
               t_apply_empty apply_empty update_eq update_neq update_shadow update_permute)
open VFA.Sort (sorted)

-- ============================================
-- Section: BST Implementation
-- ============================================

/-- Binary search tree with keys of type `Nat` and values of type `V`.
    `E` is the empty tree, `T l k v r` is a node. -/
inductive Tree (V : Type) : Type where
  | E : Tree V
  | T : Tree V → Nat → V → Tree V → Tree V
  deriving Repr, DecidableEq, BEq

/-- Example tree:
        4 → "four"
       /         \
    2 → "two"   5 → "five"
-/
def exTree : Tree String :=
  .T (.T .E 2 "two" .E) 4 "four" (.T .E 5 "five" .E)

/-- The empty BST. -/
def emptyTree {V : Type} : Tree V := .E

/-- Check whether key `k` is bound in tree `t`. -/
def bound {V : Type} (k : Nat) (t : Tree V) : Bool :=
  match t with
  | .E => false
  | .T l x _ r => if k < x then bound k l else if x < k then bound k r else true

/-- Look up key `k` in tree `t`, returning default `d` if not found. -/
def lookup {V : Type} (d : V) (k : Nat) (t : Tree V) : V :=
  match t with
  | .E => d
  | .T l x v r => if k < x then lookup d k l else if x < k then lookup d k r else v

/-- Insert key `k` with value `v` into tree `t`. -/
def insert {V : Type} (k : Nat) (v : V) (t : Tree V) : Tree V :=
  match t with
  | .E => .T .E k v .E
  | .T l x v' r =>
    if k < x then .T (insert k v l) x v' r
    else if x < k then .T l x v' (insert k v r)
    else .T l k v r

-- ============================================
-- Section: Tests
-- ============================================

example : insert 5 "five" (insert 2 "two" (insert 4 "four" emptyTree)) = exTree := by
  native_decide

example : lookup "" 5 exTree = "five" := by native_decide
example : lookup "" 3 exTree = "" := by native_decide
example : bound 3 exTree = false := by native_decide

-- ============================================
-- Section: NotBst
-- ============================================

namespace NotBst

def t : Tree String :=
  .T (.T .E 5 "five" .E) 4 "four" (.T .E 2 "two" .E)

example : lookup "" 2 t ≠ "two" := by native_decide

end NotBst

-- ============================================
-- Section: BST Invariant
-- ============================================

/-- Universal predicate over all nodes of a tree. -/
def ForallT {V : Type} (P : Nat → V → Prop) : Tree V → Prop
  | .E => True
  | .T l k v r => P k v ∧ ForallT P l ∧ ForallT P r

/-- The BST invariant: keys in the left subtree are less than the root,
    keys in the right subtree are greater than the root. -/
inductive BST {V : Type} : Tree V → Prop where
  | E : BST .E
  | T : ∀ l x v r,
      ForallT (fun y _ => y < x) l →
      ForallT (fun y _ => x < y) r →
      BST l → BST r →
      BST (.T l x v r)

example : BST exTree := by
  unfold exTree
  apply BST.T
  · exact ⟨by norm_num, trivial, trivial⟩
  · exact ⟨by norm_num, trivial, trivial⟩
  · exact BST.T _ _ _ _ trivial trivial BST.E BST.E
  · exact BST.T _ _ _ _ trivial trivial BST.E BST.E

example : ¬ BST NotBst.t := by
  unfold NotBst.t; intro h
  cases h with
  | T l x v r hl _ _ _ =>
    obtain ⟨h5, _, _⟩ := hl; omega

theorem empty_tree_BST : ∀ (V : Type), BST (@emptyTree V) :=
  fun _ => BST.E

lemma ForallT_insert : ∀ {V : Type} (P : Nat → V → Prop) (t : Tree V),
    ForallT P t → ∀ (k : Nat) (v : V), P k v → ForallT P (insert k v t) := by
  intro V P t ht k v hpkv
  induction t with
  | E => exact ⟨hpkv, trivial, trivial⟩
  | T l x v' r ihl ihr =>
    obtain ⟨hpxv', hfl, hfr⟩ := ht
    unfold insert
    split
    · exact ⟨hpxv', ihl hfl, hfr⟩
    · split
      · exact ⟨hpxv', hfl, ihr hfr⟩
      · exact ⟨hpkv, hfl, hfr⟩

theorem insert_BST : ∀ {V : Type} (k : Nat) (v : V) (t : Tree V),
    BST t → BST (insert k v t) := by
  intro V k v t hbst
  induction hbst with
  | E => exact BST.T _ _ _ _ trivial trivial BST.E BST.E
  | T l x v' r hfl hfr hbl hbr ihl ihr =>
    unfold insert
    split
    · next h => exact BST.T _ _ _ _ (ForallT_insert _ _ hfl k v h) hfr ihl hbr
    · split
      · next h1 h2 => exact BST.T _ _ _ _ hfl (ForallT_insert _ _ hfr k v h2) hbl ihr
      · next h1 h2 =>
        have heq : k = x := by omega
        subst heq; exact BST.T _ _ _ _ hfl hfr hbl hbr

-- ============================================
-- Section: Correctness of BST Operations (Algebraic Specification)
-- ============================================

theorem lookup_empty : ∀ {V : Type} (d : V) (k : Nat), lookup d k emptyTree = d :=
  fun _ _ => rfl

-- Helper: three-way case split on Nat comparison
private lemma trichotomy (a b : Nat) : a < b ∨ b < a ∨ a = b := by omega

theorem lookup_insert_eq : ∀ {V : Type} (t : Tree V) (d : V) (k : Nat) (v : V),
    lookup d k (insert k v t) = v := by
  intro V t d k v
  induction t with
  | E => simp [insert, lookup]
  | T l x v' r ihl ihr =>
    unfold insert; split
    · next h => unfold lookup; simp [h, ihl]
    · split
      · next h1 h2 => unfold lookup; simp [show ¬ k < x from h1, h2, ihr]
      · next h1 h2 =>
        have : k = x := by omega
        subst this; simp [lookup]

theorem lookup_insert_neq : ∀ {V : Type} (t : Tree V) (d : V) (k k' : Nat) (v : V),
    k ≠ k' → lookup d k' (insert k v t) = lookup d k' t := by
  intro V t d k k' v hne
  induction t with
  | E =>
    simp only [insert, lookup]
    -- Goal involves: if k' < k then ... else if k < k' then ... else ...
    -- and the RHS is just d
    split
    · rfl  -- k' < k: lookup on E = d
    · split
      · rfl  -- k < k': lookup on E = d
      · -- k' = k: contradicts hne
        next h1 h2 => exfalso; exact hne (by omega)
  | T l x v' r ihl ihr =>
    unfold insert
    rcases trichotomy k x with hkx | hxk | hkeq
    · -- k < x: insert into left
      simp only [if_pos hkx]; unfold lookup
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]; exact ihl
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]
      · -- k' = x: both sides look up x in original tree
        rw [h3]; simp only [show ¬ x < x by omega, ite_false]
    · -- x < k: insert into right
      simp only [if_neg (show ¬ k < x by omega), if_pos hxk]; unfold lookup
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]; exact ihr
      · -- k' = x
        rw [h3]; simp only [show ¬ x < x by omega, ite_false]
    · -- k = x
      rw [hkeq]; simp only [Nat.lt_irrefl, ite_false]; unfold lookup
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]
      · exfalso; exact hne (hkeq.trans h3.symm)

theorem bound_empty : ∀ {V : Type} (k : Nat), bound k (@emptyTree V) = false :=
  fun _ => rfl

theorem bound_insert_eq : ∀ {V : Type} (k : Nat) (t : Tree V) (v : V),
    bound k (insert k v t) = true := by
  intro V k t v
  induction t with
  | E => simp [insert, bound]
  | T l x v' r ihl ihr =>
    unfold insert; split
    · next h => unfold bound; simp [h, ihl]
    · split
      · next h1 h2 => unfold bound; simp [show ¬ k < x from h1, h2, ihr]
      · next h1 h2 =>
        have : k = x := by omega
        subst this; simp [bound]

theorem bound_insert_neq : ∀ {V : Type} (k k' : Nat) (t : Tree V) (v : V),
    k ≠ k' → bound k' (insert k v t) = bound k' t := by
  intro V k k' t v hne
  induction t with
  | E =>
    simp only [insert, bound]
    split
    · rfl
    · split
      · rfl
      · next h1 h2 => exfalso; exact hne (by omega)
  | T l x v' r ihl ihr =>
    unfold insert
    rcases trichotomy k x with hkx | hxk | hkeq
    · simp only [if_pos hkx]; unfold bound
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]; exact ihl
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]
      · rw [h3]; simp only [show ¬ x < x by omega, ite_false]
    · simp only [if_neg (show ¬ k < x by omega), if_pos hxk]; unfold bound
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]; exact ihr
      · rw [h3]; simp only [show ¬ x < x by omega, ite_false]
    · rw [hkeq]; simp only [Nat.lt_irrefl, ite_false]; unfold bound
      rcases trichotomy k' x with h1 | h2 | h3
      · simp only [if_pos h1]
      · simp only [if_neg (show ¬ k' < x by omega), if_pos h2]
      · exfalso; exact hne (hkeq.trans h3.symm)

theorem bound_default : ∀ {V : Type} (k : Nat) (d : V) (t : Tree V),
    bound k t = false → lookup d k t = d := by
  intro V k d t hbound
  induction t with
  | E => rfl
  | T l x v r ihl ihr =>
    unfold bound at hbound; unfold lookup
    rcases trichotomy k x with h1 | h2 | h3
    · simp [h1] at hbound ⊢; exact ihl hbound
    · simp [show ¬ k < x by omega, h2] at hbound ⊢; exact ihr hbound
    · subst h3; simp at hbound

-- ============================================
-- Section: BSTs vs. Higher-order Functions (Optional)
-- ============================================

lemma lookup_insert_shadow : ∀ {V : Type} (t : Tree V) (v v' d : V) (k k' : Nat),
    lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t) := by
  intro V t v v' d k k'
  by_cases h : k = k'
  · subst h; rw [lookup_insert_eq, lookup_insert_eq]
  · rw [lookup_insert_neq _ _ _ _ _ h, lookup_insert_neq _ _ _ _ _ h,
         lookup_insert_neq _ _ _ _ _ h]

lemma lookup_insert_same : ∀ {V : Type} (k k' : Nat) (d : V) (t : Tree V),
    lookup d k' (insert k (lookup d k t) t) = lookup d k' t := by
  intro V k k' d t
  by_cases h : k = k'
  · subst h; rw [lookup_insert_eq]
  · rw [lookup_insert_neq _ _ _ _ _ h]

lemma lookup_insert_permute : ∀ {V : Type} (v1 v2 d : V) (k1 k2 k' : Nat) (t : Tree V),
    k1 ≠ k2 →
    lookup d k' (insert k1 v1 (insert k2 v2 t))
    = lookup d k' (insert k2 v2 (insert k1 v1 t)) := by
  intro V v1 v2 d k1 k2 k' t hne
  by_cases h1 : k1 = k'
  · subst h1
    rw [lookup_insert_eq, lookup_insert_neq _ _ _ _ _ (Ne.symm hne), lookup_insert_eq]
  · by_cases h2 : k2 = k'
    · subst h2
      rw [lookup_insert_neq _ _ _ _ _ hne, lookup_insert_eq, lookup_insert_eq]
    · rw [lookup_insert_neq _ _ _ _ _ h1, lookup_insert_neq _ _ _ _ _ h2,
           lookup_insert_neq _ _ _ _ _ h2, lookup_insert_neq _ _ _ _ _ h1]

lemma insert_shadow_equality : ∀ {V : Type} (t : Tree V) (k : Nat) (v v' : V),
    insert k v (insert k v' t) = insert k v t := by
  intro V t k v v'
  induction t with
  | E => simp [insert]
  | T l x v'' r ihl ihr =>
    rcases trichotomy k x with hkx | hxk | hkeq
    · -- k < x
      show insert k v (insert k v' (.T l x v'' r)) = insert k v (.T l x v'' r)
      simp only [insert, if_pos hkx, ihl]
    · -- x < k
      show insert k v (insert k v' (.T l x v'' r)) = insert k v (.T l x v'' r)
      simp only [insert, if_neg (show ¬ k < x by omega), if_pos hxk, ihr]
    · -- k = x
      subst hkeq
      show insert k v (insert k v' (.T l k v'' r)) = insert k v (.T l k v'' r)
      simp only [insert, Nat.lt_irrefl, ite_false]

lemma insert_same_equality_breaks :
    ∃ (V : Type) (d : V) (t : Tree V) (k : Nat),
      insert k (lookup d k t) t ≠ t := by
  exact ⟨Nat, 0, .E, 0, by native_decide⟩

lemma insert_permute_equality_breaks :
    ∃ (V : Type) (v1 v2 : V) (k1 k2 : Nat) (t : Tree V),
      k1 ≠ k2 ∧ insert k1 v1 (insert k2 v2 t) ≠ insert k2 v2 (insert k1 v1 t) := by
  exact ⟨Nat, 0, 0, 0, 1, .E, by omega, by native_decide⟩

-- ============================================
-- Section: Converting a BST to a List
-- ============================================

def elements {V : Type} (t : Tree V) : List (Nat × V) :=
  match t with
  | .E => []
  | .T l k v r => elements l ++ [(k, v)] ++ elements r

example : elements exTree = [(2, "two"), (4, "four"), (5, "five")] := by native_decide

-- ============================================
-- Part 1: Same Bindings
-- ============================================

theorem elements_complete : ∀ {V : Type} (k : Nat) (v : V) (d : V) (t : Tree V),
    bound k t = true → lookup d k t = v → (k, v) ∈ elements t := by
  intro V k v d t
  induction t with
  | E => intro h; simp [bound] at h
  | T l x v' r ihl ihr =>
    intro hbound hlookup
    unfold bound at hbound; unfold lookup at hlookup; unfold elements
    rcases trichotomy k x with h1 | h2 | h3
    · simp [h1] at hbound hlookup
      exact List.mem_append_left _ (List.mem_append_left _ (ihl hbound hlookup))
    · simp [show ¬ k < x by omega, h2] at hbound hlookup
      exact List.mem_append_right _ (ihr hbound hlookup)
    · subst h3; simp at hlookup; subst hlookup
      exact List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))

def uncurry {X Y Z : Type} (f : X → Y → Z) : X × Y → Z
  | (a, b) => f a b

lemma elements_preserves_forall : ∀ {V : Type} (P : Nat → V → Prop) (t : Tree V),
    ForallT P t → List.Forall (uncurry P) (elements t) := by
  intro V P t hft
  induction t with
  | E => simp [elements]
  | T l x v r ihl ihr =>
    obtain ⟨hpxv, hfl, hfr⟩ := hft
    unfold elements
    rw [List.forall_append, List.forall_append]
    refine ⟨⟨ihl hfl, ?_⟩, ihr hfr⟩
    rw [List.forall_cons]
    exact ⟨hpxv, by simp⟩

lemma elements_preserves_relation :
    ∀ {V : Type} (k k' : Nat) (v : V) (t : Tree V) (R : Nat → Nat → Prop),
    ForallT (fun y _ => R y k') t → (k, v) ∈ elements t → R k k' := by
  intro V k k' v t R hft hmem
  have hfa := elements_preserves_forall (fun y _ => R y k') t hft
  rw [List.forall_iff_forall_mem] at hfa
  exact hfa _ hmem

theorem elements_correct : ∀ {V : Type} (k : Nat) (v : V) (d : V) (t : Tree V),
    BST t → (k, v) ∈ elements t → bound k t = true ∧ lookup d k t = v := by
  intro V k v d t hbst hmem
  induction hbst with
  | E => simp [elements] at hmem
  | T l x v' r hfl hfr _ _ ihl ihr =>
    unfold elements at hmem
    rw [List.mem_append] at hmem
    unfold bound lookup
    rcases hmem with hmem_left | hmem_right
    · rw [List.mem_append] at hmem_left
      rcases hmem_left with hmem_l | hmem_mid
      · have hlt : k < x := elements_preserves_relation k x v l (· < ·) hfl hmem_l
        simp [hlt, ihl hmem_l]
      · simp at hmem_mid
        obtain ⟨rfl, rfl⟩ := hmem_mid
        simp
    · have hgt : x < k := elements_preserves_relation k x v r (fun a b => b < a) hfr hmem_right
      simp [show ¬ k < x by omega, hgt, ihr hmem_right]

theorem elements_complete_inverse : ∀ {V : Type} (k : Nat) (v : V) (t : Tree V),
    BST t → bound k t = false → (k, v) ∉ elements t := by
  intro V k v t hbst hbound hmem
  have ⟨hb, _⟩ := elements_correct k v v t hbst hmem
  simp [hb] at hbound

lemma bound_value : ∀ {V : Type} (k : Nat) (t : Tree V),
    bound k t = true → ∃ v, ∀ d, lookup d k t = v := by
  intro V k t hbound
  induction t with
  | E => simp [bound] at hbound
  | T l x v r ihl ihr =>
    unfold bound at hbound; unfold lookup
    rcases trichotomy k x with h1 | h2 | h3
    · simp [h1] at hbound ⊢; exact ihl hbound
    · simp [show ¬ k < x by omega, h2] at hbound ⊢; exact ihr hbound
    · subst h3; simp; exact ⟨v, fun _ => rfl⟩

theorem elements_correct_inverse : ∀ {V : Type} (k : Nat) (t : Tree V),
    (∀ v, (k, v) ∉ elements t) → bound k t = false := by
  intro V k t hnot
  by_cases h : bound k t = true
  · obtain ⟨v, hv⟩ := bound_value k t h
    exact absurd (elements_complete k v v t h (hv v)) (hnot v)
  · simp at h; exact h

-- ============================================
-- Part 2: Sorted (Advanced)
-- ============================================

lemma sorted_app : ∀ l1 l2 x,
    sorted l1 → sorted l2 →
    List.Forall (fun n => n < x) l1 →
    List.Forall (fun n => x < n) l2 →
    sorted (l1 ++ x :: l2) := by
  intro l1 l2 x hs1 hs2 hlt hgt
  induction hs1 with
  | nil =>
    simp
    match l2, hs2, hgt with
    | [], _, _ => exact sorted.single x
    | y :: ys, hsl2, hgt2 =>
      rw [List.forall_cons] at hgt2
      exact sorted.cons x y ys (by omega) hsl2
  | single a =>
    simp
    rw [List.forall_cons] at hlt
    match l2, hs2, hgt with
    | [], _, _ => exact sorted.cons a x [] (by omega) (sorted.single x)
    | y :: ys, hsl2, hgt2 =>
      rw [List.forall_cons] at hgt2
      exact sorted.cons a x (y :: ys) (by omega) (sorted.cons x y ys (by omega) hsl2)
  | cons a b t hab hbt ih =>
    simp
    rw [List.forall_cons] at hlt
    exact sorted.cons a b (t ++ x :: l2) hab (ih hlt.2)

def listKeys {V : Type} (lst : List (Nat × V)) : List Nat :=
  lst.map Prod.fst

theorem sorted_elements : ∀ {V : Type} (t : Tree V),
    BST t → sorted (listKeys (elements t)) := by
  intro V t hbst
  induction hbst with
  | E => exact sorted.nil
  | T l x v r hfl hfr _ _ ihl ihr =>
    unfold elements
    simp only [listKeys, List.map_append, List.map_cons, List.map_nil]
    -- Goal: sorted (map(el l) ++ [x] ++ map(el r))
    rw [List.append_assoc, List.singleton_append]
    -- Goal: sorted (map(el l) ++ x :: map(el r))
    apply sorted_app
    · exact ihl
    · exact ihr
    · have hfa := elements_preserves_forall (fun y _ => y < x) l hfl
      rw [List.forall_iff_forall_mem] at hfa ⊢
      intro n hn; rw [List.mem_map] at hn
      obtain ⟨⟨k', v'⟩, hmem, rfl⟩ := hn
      exact hfa ⟨k', v'⟩ hmem
    · have hfa := elements_preserves_forall (fun y _ => x < y) r hfr
      rw [List.forall_iff_forall_mem] at hfa ⊢
      intro n hn; rw [List.mem_map] at hn
      obtain ⟨⟨k', v'⟩, hmem, rfl⟩ := hn
      exact hfa ⟨k', v'⟩ hmem

-- ============================================
-- Part 3: No Duplicates (Advanced, Optional)
-- ============================================

def disjoint {X : Type} (l1 l2 : List X) : Prop :=
  ∀ x, x ∈ l1 → x ∉ l2

theorem elements_nodup_keys : ∀ {V : Type} (t : Tree V),
    BST t → List.Nodup (listKeys (elements t)) := by
  intro V t hbst
  induction hbst with
  | E => exact List.nodup_nil
  | T l x v r hfl hfr _ _ ihl ihr =>
    unfold elements
    simp only [listKeys, List.map_append, List.map_cons, List.map_nil]
    rw [List.append_assoc, List.singleton_append]
    -- Goal: Nodup (map l ++ x :: map r)
    rw [List.nodup_append_comm]
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · -- x ∉ map r ++ map l
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with hmem_r | hmem_l
      · rw [List.mem_map] at hmem_r
        obtain ⟨⟨k', v'⟩, hmem', heq⟩ := hmem_r
        have := elements_preserves_relation k' x v' r (fun a b => b < a) hfr hmem'
        simp at heq; omega
      · rw [List.mem_map] at hmem_l
        obtain ⟨⟨k', v'⟩, hmem', heq⟩ := hmem_l
        have := elements_preserves_relation k' x v' l (· < ·) hfl hmem'
        simp at heq; omega
    · rw [List.nodup_append_comm]
      apply List.Nodup.append
      · exact ihl
      · exact ihr
      · intro a ha1 ha2
        rw [List.mem_map] at ha1 ha2
        obtain ⟨⟨k1, v1⟩, hmem1, heq1⟩ := ha1
        obtain ⟨⟨k2, v2⟩, hmem2, heq2⟩ := ha2
        simp at heq1 heq2
        have hlt := elements_preserves_relation k1 x v1 l (· < ·) hfl hmem1
        have hgt := elements_preserves_relation k2 x v2 r (fun a b => b < a) hfr hmem2
        rw [← heq1, ← heq2] at *
        omega

-- ============================================
-- Section: A Faster elements Implementation
-- ============================================

def fastElementsTr {V : Type} (t : Tree V) (acc : List (Nat × V)) : List (Nat × V) :=
  match t with
  | .E => acc
  | .T l k v r => fastElementsTr l ((k, v) :: fastElementsTr r acc)

def fastElements {V : Type} (t : Tree V) : List (Nat × V) :=
  fastElementsTr t []

lemma fast_elements_tr_helper : ∀ {V : Type} (t : Tree V) (lst : List (Nat × V)),
    fastElementsTr t lst = elements t ++ lst := by
  intro V t
  induction t with
  | E => intro lst; rfl
  | T l x v r ihl ihr =>
    intro lst
    simp only [fastElementsTr, elements]
    rw [ihr lst, ihl]
    simp [List.append_assoc]

lemma fast_elements_eq_elements : ∀ {V : Type} (t : Tree V),
    fastElements t = elements t := by
  intro V t; simp [fastElements, fast_elements_tr_helper]

theorem fast_elements_correct : ∀ {V : Type} (k : Nat) (v : V) (d : V) (t : Tree V),
    BST t → (k, v) ∈ fastElements t → bound k t = true ∧ lookup d k t = v := by
  intro V k v d t hbst hmem
  rw [fast_elements_eq_elements] at hmem
  exact elements_correct k v d t hbst hmem

-- ============================================
-- Section: Algebraic Specification of elements
-- ============================================

lemma elements_empty : ∀ (V : Type), @elements V emptyTree = [] :=
  fun _ => rfl

def kvsInsert {V : Type} (k : Nat) (v : V) (kvs : List (Nat × V)) : List (Nat × V) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
    if k < k' then (k, v) :: kvs
    else if k' < k then (k', v') :: kvsInsert k v kvs'
    else (k, v) :: kvs'

lemma kvs_insert_split : ∀ {V : Type} (v v0 : V) (e1 e2 : List (Nat × V)) (k k0 : Nat),
    List.Forall (fun p => p.1 < k0) e1 →
    List.Forall (fun p => k0 < p.1) e2 →
    kvsInsert k v (e1 ++ (k0, v0) :: e2) =
    if k < k0 then (kvsInsert k v e1) ++ (k0, v0) :: e2
    else if k0 < k then e1 ++ (k0, v0) :: (kvsInsert k v e2)
    else e1 ++ (k, v) :: e2 := by
  intro V v v0 e1 e2 k k0 hlt hgt
  induction e1 with
  | nil =>
    simp only [List.nil_append, kvsInsert]
    rcases trichotomy k k0 with h1 | h2 | h3
    · simp [h1]
    · simp [show ¬ k < k0 by omega, h2]
    · simp [show ¬ k < k0 by omega, show ¬ k0 < k by omega]
  | cons p e1' ih =>
    obtain ⟨k', v'⟩ := p
    rw [List.forall_cons] at hlt
    simp at hlt
    simp only [List.cons_append, kvsInsert]
    rcases trichotomy k k' with hkk' | hk'k | hkeq
    · -- k < k' (which means k < k0)
      simp only [if_pos hkk']
      have : k < k0 := by omega
      simp [this]
    · -- k' < k
      simp only [if_neg (show ¬ k < k' by omega), if_pos hk'k]
      rw [ih hlt.2]
      -- Goal: (k', v') :: (if k < k0 then ...) = if k < k0 then (k', v') :: ... else ...
      rcases trichotomy k k0 with h1 | h2 | h3
      · simp [h1]
      · simp [show ¬ k < k0 by omega, h2]
      · simp [show ¬ k < k0 by omega, show ¬ k0 < k by omega]
    · -- k = k' (which means k < k0)
      rw [hkeq]
      simp only [ite_false, show ¬ k' < k' by omega]
      have : k' < k0 := hlt.1
      simp [show k' < k0 from this]

lemma kvs_insert_elements : ∀ {V : Type} (t : Tree V),
    BST t → ∀ (k : Nat) (v : V),
    elements (insert k v t) = kvsInsert k v (elements t) := by
  intro V t hbst
  induction hbst with
  | E => intro k v; rfl
  | T l x v' r hfl hfr _ _ ihl ihr =>
    intro k v
    have hfa_l : List.Forall (fun p => p.1 < x) (elements l) := by
      have hfa := elements_preserves_forall (fun y _ => y < x) l hfl
      rw [List.forall_iff_forall_mem] at hfa ⊢; exact hfa
    have hfa_r : List.Forall (fun p => x < p.1) (elements r) := by
      have hfa := elements_preserves_forall (fun y _ => x < y) r hfr
      rw [List.forall_iff_forall_mem] at hfa ⊢; exact hfa
    unfold insert; split
    · next h => simp [elements, ihl, kvs_insert_split v v' _ _ k x hfa_l hfa_r, h]
    · split
      · next h1 h2 => simp [elements, ihr, kvs_insert_split v v' _ _ k x hfa_l hfa_r, h1, h2]
      · next h1 h2 => simp [elements, kvs_insert_split v v' _ _ k x hfa_l hfa_r, h1, h2]

-- ============================================
-- Section: Model-based Specifications
-- ============================================

def mapOfList {V : Type} (el : List (Nat × V)) : PartialMap V :=
  match el with
  | [] => p_empty
  | (k, v) :: el' => p_update (mapOfList el') k v

def Abs {V : Type} (t : Tree V) : PartialMap V :=
  mapOfList (elements t)

def find {V : Type} (d : V) (k : Nat) (m : PartialMap V) : V :=
  match m k with
  | some v => v
  | none => d

def mapBound {V : Type} (k : Nat) (m : PartialMap V) : Bool :=
  match m k with
  | some _ => true
  | none => false

lemma in_fst : ∀ {X Y : Type} (lst : List (X × Y)) (x : X) (y : Y),
    (x, y) ∈ lst → x ∈ lst.map Prod.fst := by
  intro X Y lst x y hmem
  rw [List.mem_map]
  exact ⟨(x, y), hmem, rfl⟩

lemma in_map_of_list : ∀ {V : Type} (el : List (Nat × V)) (k : Nat) (v : V),
    List.Nodup (el.map Prod.fst) → (k, v) ∈ el → (mapOfList el) k = some v := by
  intro V el k v hnd hmem
  induction el with
  | nil => simp at hmem
  | cons p el' ih =>
    obtain ⟨k', v'⟩ := p
    simp only [mapOfList, p_update, t_update]
    rw [List.map_cons] at hnd
    have hnd' := List.Nodup.of_cons hnd
    rw [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem'
    · simp
    · have hne : k' ≠ k := by
        intro heq
        have hmem_fst : k ∈ (el'.map Prod.fst) := in_fst el' k v hmem'
        rw [← heq] at hmem_fst
        exact (List.nodup_cons.mp hnd).1 hmem_fst
      simp [hne]; exact ih hnd' hmem'

lemma not_in_map_of_list : ∀ {V : Type} (el : List (Nat × V)) (k : Nat),
    k ∉ el.map Prod.fst → (mapOfList el) k = none := by
  intro V el k hnotin
  induction el with
  | nil => simp [mapOfList, p_empty, t_empty]
  | cons p el' ih =>
    obtain ⟨k', v'⟩ := p
    simp only [mapOfList, p_update, t_update]
    rw [List.map_cons, List.mem_cons] at hnotin
    push_neg at hnotin
    have hne : k' ≠ k := by
      intro heq
      exact hnotin.1 (heq ▸ rfl)
    simp [hne]; exact ih hnotin.2

lemma empty_relate : ∀ (V : Type), @Abs V emptyTree = p_empty :=
  fun _ => rfl

theorem bound_relate : ∀ {V : Type} (t : Tree V) (k : Nat),
    BST t → mapBound k (Abs t) = bound k t := by
  intro V t k hbst
  unfold mapBound Abs
  by_cases hb : bound k t = true
  · obtain ⟨v, hv⟩ := bound_value k t hb
    rw [in_map_of_list _ k v (elements_nodup_keys t hbst) (elements_complete k v v t hb (hv v))]
    simp [hb]
  · have hb' : bound k t = false := by
      rcases Bool.eq_false_or_eq_true (bound k t) with h | h <;> simp_all
    rw [hb']
    have hnotin : k ∉ (elements t).map Prod.fst := by
      intro hmem; rw [List.mem_map] at hmem
      obtain ⟨⟨k', v'⟩, hmem', rfl⟩ := hmem
      have ⟨h, _⟩ := elements_correct k' v' v' t hbst hmem'
      simp [hb'] at h
    rw [not_in_map_of_list _ k hnotin]

lemma lookup_relate : ∀ {V : Type} (t : Tree V) (d : V) (k : Nat),
    BST t → find d k (Abs t) = lookup d k t := by
  intro V t d k hbst
  unfold find Abs
  by_cases hb : bound k t = true
  · obtain ⟨v, hv⟩ := bound_value k t hb
    rw [in_map_of_list _ k v (elements_nodup_keys t hbst) (elements_complete k v v t hb (hv v))]
    exact (hv d).symm
  · have hb' : bound k t = false := by
      rcases Bool.eq_false_or_eq_true (bound k t) with h | h <;> simp_all
    have hnotin : k ∉ (elements t).map Prod.fst := by
      intro hmem; rw [List.mem_map] at hmem
      obtain ⟨⟨k', v'⟩, hmem', rfl⟩ := hmem
      have ⟨h, _⟩ := elements_correct k' v' v' t hbst hmem'
      simp [hb'] at h
    rw [not_in_map_of_list _ k hnotin]
    exact (bound_default k d t hb').symm

lemma insert_relate : ∀ {V : Type} (t : Tree V) (k : Nat) (v : V),
    BST t → Abs (insert k v t) = p_update (Abs t) k v := by
  intro V t k v hbst
  simp only [Abs]
  rw [kvs_insert_elements t hbst k v]
  generalize elements t = l
  induction l with
  | nil => simp [kvsInsert, mapOfList, p_update]
  | cons p l' ih =>
    obtain ⟨k', v'⟩ := p
    simp only [kvsInsert]
    split
    · simp [mapOfList]
    · split
      · next h1 h2 =>
        simp only [mapOfList]; rw [ih]
        simp only [p_update]
        rw [t_update_permute (Option V) (some v') (some v) k' k _ (by omega)]
      · next h1 h2 =>
        have heq : k = k' := by omega
        subst heq; simp only [mapOfList, p_update]
        rw [t_update_shadow]

lemma elements_relate : ∀ {V : Type} (t : Tree V),
    BST t → mapOfList (elements t) = Abs t :=
  fun _ _ => rfl

-- ============================================
-- Section: Alternative Abstraction Relation (Optional, Advanced)
-- ============================================

def union {X : Type} (m1 m2 : PartialMap X) : PartialMap X :=
  fun k =>
    match (m1 k, m2 k) with
    | (none, none) => none
    | (none, some v) => some v
    | (some v, none) => some v
    | (some _, some _) => none

lemma union_left : ∀ {X : Type} (m1 m2 : PartialMap X) (k : Nat),
    m2 k = none → union m1 m2 k = m1 k := by
  intro X m1 m2 k h2; unfold union; rw [h2]; cases m1 k <;> rfl

lemma union_right : ∀ {X : Type} (m1 m2 : PartialMap X) (k : Nat),
    m1 k = none → union m1 m2 k = m2 k := by
  intro X m1 m2 k h1; unfold union; rw [h1]; cases m2 k <;> rfl

lemma union_both : ∀ {X : Type} (m1 m2 : PartialMap X) (k : Nat) (v1 v2 : X),
    m1 k = some v1 → m2 k = some v2 → union m1 m2 k = none := by
  intro X m1 m2 k v1 v2 h1 h2; unfold union; rw [h1, h2]

lemma union_update_right : ∀ {X : Type} (m1 m2 : PartialMap X) (k : Nat) (v : X),
    m1 k = none →
    p_update (union m1 m2) k v = union m1 (p_update m2 k v) := by
  intro X m1 m2 k v h1; funext k'
  simp only [p_update, t_update, union]
  by_cases h : k = k'
  · subst h; simp [h1]
  · simp [h]

lemma union_update_left : ∀ {X : Type} (m1 m2 : PartialMap X) (k : Nat) (v : X),
    m2 k = none →
    p_update (union m1 m2) k v = union (p_update m1 k v) m2 := by
  intro X m1 m2 k v h2; funext k'
  simp only [p_update, t_update, union]
  by_cases h : k = k'
  · subst h; simp [h2]
  · simp [h]

def mapOfTree {V : Type} (t : Tree V) : PartialMap V :=
  match t with
  | .E => p_empty
  | .T l k v r => p_update (union (mapOfTree l) (mapOfTree r)) k v

lemma map_of_tree_prop : ∀ {V : Type} (P : Nat → V → Prop) (t : Tree V),
    ForallT P t → ∀ k v, (mapOfTree t) k = some v → P k v := by
  intro V P t hft
  induction t with
  | E => intro k v h; simp [mapOfTree, p_empty, t_empty] at h
  | T l x v' r ihl ihr =>
    intro k w h
    obtain ⟨hpxv', hfl, hfr⟩ := hft
    simp only [mapOfTree, p_update, t_update] at h
    by_cases heq : x = k
    · subst heq; simp at h; rw [← h]; exact hpxv'
    · simp [heq] at h; unfold union at h
      cases hl : mapOfTree l k <;> cases hr : mapOfTree r k <;> simp [hl, hr] at h
      · exact h ▸ ihr hfr k _ hr
      · exact h ▸ ihl hfl k _ hl

def Abs' {V : Type} (t : Tree V) : PartialMap V := mapOfTree t

lemma empty_relate' : ∀ (V : Type), @Abs' V emptyTree = p_empty :=
  fun _ => rfl

private lemma mapOfTree_none_lt : ∀ {V : Type} (k : Nat) (t : Tree V),
    BST t → ForallT (fun y _ => y < k) t → (mapOfTree t) k = none := by
  intro V k t hbst
  induction hbst with
  | E => intro _; simp [mapOfTree, p_empty, t_empty]
  | T l x v r hfl hfr _ _ ihl ihr =>
    intro hft
    obtain ⟨hxk, hftl, hftr⟩ := hft
    simp only [mapOfTree, p_update, t_update]
    have hne : x ≠ k := by omega
    simp [hne]
    rw [union_left _ _ k (ihr hftr)]; exact ihl hftl

private lemma mapOfTree_none_gt : ∀ {V : Type} (k : Nat) (t : Tree V),
    BST t → ForallT (fun y _ => k < y) t → (mapOfTree t) k = none := by
  intro V k t hbst
  induction hbst with
  | E => intro _; simp [mapOfTree, p_empty, t_empty]
  | T l x v r hfl hfr _ _ ihl ihr =>
    intro hft
    obtain ⟨hxk, hftl, hftr⟩ := hft
    simp only [mapOfTree, p_update, t_update]
    have hne : x ≠ k := by omega
    simp [hne]
    rw [union_right _ _ k (ihl hftl)]; exact ihr hftr

private lemma bst_left_none {V : Type} (k x : Nat) (l : Tree V)
    (hbst : BST l) (hfl : ForallT (fun y _ => y < x) l) (hkx : x ≤ k) :
    mapOfTree l k = none := by
  apply mapOfTree_none_lt k l hbst
  clear hbst; induction l with
  | E => trivial
  | T _ _ _ _ ihl ihr =>
    obtain ⟨hlx, hfll, hflr⟩ := hfl
    exact ⟨by omega, ihl hfll, ihr hflr⟩

private lemma bst_right_none {V : Type} (k x : Nat) (r : Tree V)
    (hbst : BST r) (hfr : ForallT (fun y _ => x < y) r) (hkx : k ≤ x) :
    mapOfTree r k = none := by
  apply mapOfTree_none_gt k r hbst
  clear hbst; induction r with
  | E => trivial
  | T _ _ _ _ ihl ihr =>
    obtain ⟨hrx, hfrl, hfrr⟩ := hfr
    exact ⟨by omega, ihl hfrl, ihr hfrr⟩

theorem bound_relate' : ∀ {V : Type} (t : Tree V) (k : Nat),
    BST t → mapBound k (Abs' t) = bound k t := by
  intro V t k hbst
  induction hbst with
  | E => rfl
  | T l x v r hfl hfr hbl hbr ihl ihr =>
    simp only [Abs', mapOfTree, mapBound, p_update, t_update]
    by_cases heq : x = k
    · subst heq; simp [bound]
    · simp [heq]; unfold bound
      rcases trichotomy k x with h1 | h2 | h3
      · simp [h1]
        rw [union_left _ _ k (bst_right_none k x r hbr hfr (by omega))]
        have : mapBound k (Abs' l) = bound k l := ihl
        simp only [Abs', mapBound] at this
        exact this
      · simp [show ¬ k < x by omega, h2]
        rw [union_right _ _ k (bst_left_none k x l hbl hfl (by omega))]
        have : mapBound k (Abs' r) = bound k r := ihr
        simp only [Abs', mapBound] at this
        exact this
      · exfalso; exact heq (h3.symm)

lemma lookup_relate' : ∀ {V : Type} (d : V) (t : Tree V) (k : Nat),
    BST t → find d k (Abs' t) = lookup d k t := by
  intro V d t k hbst
  induction hbst with
  | E => rfl
  | T l x v r hfl hfr hbl hbr ihl ihr =>
    simp only [Abs', mapOfTree, find, p_update, t_update]
    by_cases heq : x = k
    · subst heq; simp [lookup]
    · simp [heq]; unfold lookup
      rcases trichotomy k x with h1 | h2 | h3
      · simp [h1]
        rw [union_left _ _ k (bst_right_none k x r hbr hfr (by omega))]
        have : find d k (Abs' l) = lookup d k l := ihl
        simp only [Abs', find] at this
        exact this
      · simp [show ¬ k < x by omega, h2]
        rw [union_right _ _ k (bst_left_none k x l hbl hfl (by omega))]
        have : find d k (Abs' r) = lookup d k r := ihr
        simp only [Abs', find] at this
        exact this
      · exfalso; exact heq (h3.symm)

lemma insert_relate' : ∀ {V : Type} (k : Nat) (v : V) (t : Tree V),
    BST t → Abs' (insert k v t) = p_update (Abs' t) k v := by
  intro V k v t hbst
  induction hbst with
  | E =>
    funext k'; simp [Abs', insert, mapOfTree, p_update, t_update, union, p_empty, t_empty]
  | T l x v' r hfl hfr hbl hbr ihl ihr =>
    have ihl' : mapOfTree (insert k v l) = p_update (mapOfTree l) k v := by
      have := ihl; simp only [Abs'] at this; exact this
    have ihr' : mapOfTree (insert k v r) = p_update (mapOfTree r) k v := by
      have := ihr; simp only [Abs'] at this; exact this
    show Abs' (insert k v (.T l x v' r)) = p_update (Abs' (.T l x v' r)) k v
    unfold insert
    rcases trichotomy k x with hkx | hxk | hkeq
    · -- k < x: insert into left subtree
      simp only [if_pos hkx, Abs', mapOfTree]
      rw [ihl']
      rw [← union_update_left _ _ k v (bst_right_none k x r hbr hfr (by omega))]
      simp only [p_update]
      rw [t_update_permute (Option V) (some v) (some v') k x _ (by omega)]
    · -- x < k: insert into right subtree
      simp only [if_neg (show ¬ k < x by omega), if_pos hxk, Abs', mapOfTree]
      rw [ihr']
      rw [← union_update_right _ _ k v (bst_left_none k x l hbl hfl (by omega))]
      simp only [p_update]
      rw [t_update_permute (Option V) (some v) (some v') k x _ (by omega)]
    · -- k = x
      subst hkeq; simp only [Nat.lt_irrefl, ite_false, Abs', mapOfTree, p_update]
      rw [t_update_shadow]

lemma map_of_list_app : ∀ {V : Type} (el1 el2 : List (Nat × V)),
    disjoint (el1.map Prod.fst) (el2.map Prod.fst) →
    mapOfList (el1 ++ el2) = union (mapOfList el1) (mapOfList el2) := by
  intro V el1 el2 hdisj
  induction el1 with
  | nil =>
    simp [mapOfList]; funext k
    simp [union, p_empty, t_empty]; cases mapOfList el2 k <;> rfl
  | cons p el1' ih =>
    obtain ⟨k, v⟩ := p
    simp [List.cons_append, mapOfList]
    rw [ih (fun x hx1 hx2 => hdisj x (List.mem_cons_of_mem _ hx1) hx2)]
    rw [List.map_cons] at hdisj
    have hk_notin : k ∉ el2.map Prod.fst := by
      intro hmem
      exact hdisj k (List.mem_cons.mpr (Or.inl rfl)) hmem
    rw [← union_update_left _ _ k v (not_in_map_of_list el2 k hk_notin)]

lemma elements_relate' : ∀ {V : Type} (t : Tree V),
    BST t → mapOfList (elements t) = Abs' t := by
  intro V t hbst
  induction hbst with
  | E => simp [elements, Abs', mapOfTree, mapOfList]
  | T l x v r hfl hfr hbl hbr ihl ihr =>
    unfold elements
    -- Goal: mapOfList (elements l ++ [(x, v)] ++ elements r) = Abs' (T l x v r)
    rw [List.append_assoc, List.singleton_append]
    -- Goal: mapOfList (elements l ++ (x, v) :: elements r) = Abs' (T l x v r)
    have hdisj_lr : disjoint (List.map Prod.fst (elements l))
        (List.map Prod.fst ((x, v) :: elements r)) := by
      intro a ha1 ha2
      rw [List.mem_map] at ha1
      obtain ⟨⟨k1, v1⟩, hmem1, rfl⟩ := ha1
      have hlt := elements_preserves_relation k1 x v1 l (· < ·) hfl hmem1
      rw [List.map_cons, List.mem_cons] at ha2
      rcases ha2 with rfl | ha2
      · omega
      · rw [List.mem_map] at ha2
        obtain ⟨⟨k2, v2⟩, hmem2, rfl⟩ := ha2
        have hgt := elements_preserves_relation k2 x v2 r (fun a b => b < a) hfr hmem2
        omega
    rw [map_of_list_app (elements l) ((x, v) :: elements r) hdisj_lr]
    -- Goal: union (mapOfList (elements l)) (mapOfList ((x, v) :: elements r)) = Abs' (T l x v r)
    simp only [mapOfList]
    -- mapOfList ((x, v) :: elements r) = p_update (mapOfList (elements r)) x v
    rw [ihl, ihr]
    simp only [Abs', mapOfTree]
    rw [← union_update_right _ _ x v (bst_left_none x x l hbl hfl (by omega))]

end VFA.SearchTree
