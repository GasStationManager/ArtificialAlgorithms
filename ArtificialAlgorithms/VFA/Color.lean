import Mathlib

/-!
# VFA Chapter: Color (Graph Coloring)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Color.html

## Overview
Kempe's algorithm for K-coloring an undirected graph. Given a palette of K colors
and a graph, the algorithm removes low-degree nodes one at a time (building a stack),
then colors them in reverse order, always picking the smallest available color.

## Mathlib Mappings
- Coq `positive` ↦ `Nat`
- Coq `PositiveSet` ↦ `Finset Nat`
- Coq `PositiveMap` ↦ `Graph` structure / `List (Nat × Nat)` for coloring
- Coq `S.cardinal` ↦ `Finset.card`
- Coq `S.choose` ↦ `Finset.min'`
- Coq `Function` with `{measure}` ↦ `termination_by` + `decreasing_by`
-/

namespace VFA.Color

-- ============================================
-- Section: Graph Representation
-- ============================================

/-- A finite graph: a set of nodes with an adjacency function.
    Replaces Coq's `nodemap nodeset` (`M.t S.t`). -/
structure Graph where
  nodes : Finset Nat
  adj : Nat → Finset Nat

/-- Adjacency is symmetric (VFA `undirected`). -/
def Graph.Undirected (g : Graph) : Prop :=
  ∀ i j, j ∈ g.adj i → i ∈ g.adj j

/-- No node is adjacent to itself (VFA `no_selfloop`). -/
def Graph.NoSelfloop (g : Graph) : Prop :=
  ∀ i, i ∉ g.adj i

/-- Remove a node from the graph (VFA `remove_node`). -/
def Graph.removeNode (n : Nat) (g : Graph) : Graph where
  nodes := g.nodes.erase n
  adj := fun i => (g.adj i).erase n

-- ============================================
-- Section: Set Infrastructure (VFA Exercises)
-- ============================================

-- VFA Exercise: Snot_in_empty (2★)
theorem not_mem_empty_set (n : Nat) : n ∉ (∅ : Finset Nat) :=
  Finset.notMem_empty n

-- VFA Exercise: Sremove_cardinal_less (4★)
theorem erase_card_lt_of_mem {s : Finset Nat} {i : Nat} (h : i ∈ s) :
    (s.erase i).card < s.card :=
  Finset.card_erase_lt_of_mem h

-- VFA Exercise: fold_right_rev_left (2★)
theorem foldl_eq_foldr_rev {α β : Type} (f : α → β → α) (init : α) (l : List β) :
    List.foldl f init l = List.foldr (fun x y => f y x) init l.reverse := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldr_append, List.foldr_cons,
               List.foldr_nil]
    exact ih (f init h)

-- VFA Exercise: subset_nodes_sub (3★)
theorem filter_sub_nodes (p : Nat → Prop) [DecidablePred p] (g : Graph) :
    g.nodes.filter p ⊆ g.nodes :=
  Finset.filter_subset _ _

-- ============================================
-- Section: Kempe's Node Selection
-- ============================================

/-- Kempe's node selection: repeatedly remove a low-degree node.
    VFA Exercise: select_terminates (3★) — proved via decreasing_by. -/
def select (K : Nat) (g : Graph) : List Nat :=
  let low := g.nodes.filter (fun n => decide ((g.adj n).card < K))
  if h : low.Nonempty then
    let n := low.min' h
    n :: select K (g.removeNode n)
  else []
termination_by g.nodes.card
decreasing_by
  simp only [Graph.removeNode]
  exact Finset.card_erase_lt_of_mem
    (Finset.filter_subset _ _ (Finset.min'_mem _ h))

-- ============================================
-- Section: Coloring
-- ============================================

/-- Look up a node's color in an association-list coloring. -/
def colorLookup : Nat → List (Nat × Nat) → Option Nat
  | _, [] => none
  | n, (k, v) :: rest => if k = n then some v else colorLookup n rest

/-- Colors assigned to nodes in a set under coloring f (VFA `colors_of`). -/
def colorsOf (f : List (Nat × Nat)) (s : Finset Nat) : Finset Nat :=
  s.biUnion (fun n => match colorLookup n f with
    | some c => {c}
    | none => ∅)

/-- Color one node: pick the smallest available color (VFA `color1`). -/
def color1 (palette : Finset Nat) (g : Graph) (n : Nat)
    (f : List (Nat × Nat)) : List (Nat × Nat) :=
  let used := colorsOf f (g.adj n)
  let avail := palette \ used
  if _h : avail.Nonempty then (n, avail.min' _h) :: f
  else f

/-- Kempe's graph coloring (VFA `color`). -/
def color (palette : Finset Nat) (g : Graph) : List (Nat × Nat) :=
  (select palette.card g).foldr (color1 palette g) []

-- ============================================
-- Section: Correctness
-- ============================================

/-- A coloring is valid (VFA `coloring_ok`). -/
def coloringOk (palette : Finset Nat) (g : Graph) (f : List (Nat × Nat)) : Prop :=
  ∀ i j, j ∈ g.adj i →
    (∀ ci, colorLookup i f = some ci → ci ∈ palette) ∧
    (∀ ci cj, colorLookup i f = some ci → colorLookup j f = some cj → ci ≠ cj)

private lemma colorLookup_cons_eq (n v : Nat) (rest : List (Nat × Nat)) :
    colorLookup n ((n, v) :: rest) = some v := by
  unfold colorLookup; exact if_pos rfl

private lemma colorLookup_cons_ne {k m : Nat} {v : Nat} {rest : List (Nat × Nat)}
    (h : k ≠ m) :
    colorLookup m ((k, v) :: rest) = colorLookup m rest := by
  simp [colorLookup, h]

-- VFA Exercise: in_colors_of_1 (3★)
lemma mem_colorsOf {f : List (Nat × Nat)} {s : Finset Nat} {i c : Nat}
    (hi : i ∈ s) (hc : colorLookup i f = some c) :
    c ∈ colorsOf f s := by
  simp only [colorsOf, Finset.mem_biUnion]
  exact ⟨i, hi, by rw [hc]; exact Finset.mem_singleton_self c⟩

private lemma color1_ok {palette : Finset Nat} {g : Graph} {n : Nat}
    {f : List (Nat × Nat)}
    (hns : g.NoSelfloop) (hud : g.Undirected)
    (hf : coloringOk palette g f) :
    coloringOk palette g (color1 palette g n f) := by
  unfold color1
  -- Split on whether an available color exists
  by_cases havail : (palette \ colorsOf f (g.adj n)).Nonempty
  · -- Available color exists: we prepend (n, c) to f
    simp only [dif_pos havail]
    set c := (palette \ colorsOf f (g.adj n)).min' havail with hc_def
    have hc_mem := Finset.min'_mem _ havail
    rw [← hc_def] at hc_mem
    have hc_pal : c ∈ palette := (Finset.mem_sdiff.mp hc_mem).1
    have hc_fresh : c ∉ colorsOf f (g.adj n) := (Finset.mem_sdiff.mp hc_mem).2
    intro i j hij
    constructor
    · -- Part 1: assigned colors are in palette
      intro ci hci
      by_cases hin : n = i
      · rw [← hin, colorLookup_cons_eq] at hci
        injection hci with hci; subst hci; exact hc_pal
      · rw [colorLookup_cons_ne hin] at hci; exact (hf i j hij).1 ci hci
    · -- Part 2: adjacent nodes get different colors
      intro ci cj hci hcj
      by_cases hin : n = i
      · -- i = n: ci = c
        subst hin; rw [colorLookup_cons_eq] at hci
        injection hci with hci; subst hci
        by_cases hjn : n = j
        · subst hjn; exact absurd hij (hns n)
        · rw [colorLookup_cons_ne hjn] at hcj
          intro heq; exact hc_fresh (heq ▸ mem_colorsOf hij hcj)
      · by_cases hjn : n = j
        · -- j = n: cj = c
          subst hjn; rw [colorLookup_cons_eq] at hcj
          injection hcj with hcj; subst hcj
          rw [colorLookup_cons_ne hin] at hci
          intro heq; exact hc_fresh (heq ▸ mem_colorsOf (hud i n hij) hci)
        · -- Neither is n: delegate to hf
          rw [colorLookup_cons_ne hin] at hci
          rw [colorLookup_cons_ne hjn] at hcj
          exact (hf i j hij).2 ci cj hci hcj
  · -- No available color: coloring unchanged
    simp only [dif_neg havail]; exact hf

-- VFA Exercise: color_correct (4★)
theorem color_correct (palette : Finset Nat) (g : Graph)
    (hns : g.NoSelfloop) (hud : g.Undirected) :
    coloringOk palette g (color palette g) := by
  unfold color
  generalize select palette.card g = stack
  induction stack with
  | nil =>
    intro i j _
    exact ⟨fun _ h => by simp [colorLookup] at h,
           fun _ _ h => by simp [colorLookup] at h⟩
  | cons _ _ ih =>
    simp only [List.foldr_cons]
    exact color1_ok hns hud ih

-- ============================================
-- Section: Test Case
-- ============================================

/-- Add an undirected edge to a graph. -/
def addEdge (e : Nat × Nat) (g : Graph) : Graph where
  nodes := insert e.1 (insert e.2 g.nodes)
  adj := fun n =>
    if n = e.1 then insert e.2 (g.adj n)
    else if n = e.2 then insert e.1 (g.adj n)
    else g.adj n

/-- Build a graph from a list of undirected edges. -/
def mkGraph (edges : List (Nat × Nat)) : Graph :=
  edges.foldr addEdge ⟨∅, fun _ => ∅⟩

def testPalette : Finset Nat := {1, 2, 3}

def testG : Graph :=
  mkGraph [(5,6), (6,2), (5,2), (1,5), (1,2), (2,4), (1,4)]

-- Finset.toList is noncomputable; use the coloring output to verify nodes
-- #eval testG.nodes  -- nodes: {1, 2, 4, 5, 6}

#eval (color testPalette testG).map (fun (n, c) => (n, c))

end VFA.Color
