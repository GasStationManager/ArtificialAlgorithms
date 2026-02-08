import Mathlib

/-!
# VFA Chapter: Redblack (Red-Black Trees)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html

## Overview
Red-black trees are balanced binary search trees using Okasaki's insertion algorithm.
This chapter verifies the BST invariant, lookup correctness, red-black invariant,
and approximate balance (height ≤ 2 * mindepth + 1).

## Mathlib Mappings
- VFA `int` (axiomatized key) ↦ `Int`
- VFA `Abs k` ↦ `k` (identity — Int is concrete)
- VFA `ltb` ↦ decidable `<` on `Int`
- VFA `color` ↦ `inductive Color`
- VFA `tree V` ↦ `inductive RBTree V` (separate from SearchTree.Tree)
-/

namespace VFA.Redblack

-- ============================================
-- Section: Implementation
-- ============================================

abbrev Key := Int

inductive Color where
  | red | black
  deriving DecidableEq, Repr

inductive RBTree (V : Type) : Type where
  | E : RBTree V
  | T : Color → RBTree V → Key → V → RBTree V → RBTree V
  deriving Repr

open Color RBTree

def emptyTree (V : Type) : RBTree V := E

def lookup {V : Type} (d : V) (x : Key) (t : RBTree V) : V :=
  match t with
  | E => d
  | T _ l k v r => if x < k then lookup d x l else if k < x then lookup d x r else v

def balance {V : Type} (c : Color) (t1 : RBTree V) (k : Key) (vk : V)
    (t2 : RBTree V) : RBTree V :=
  match c with
  | red => T red t1 k vk t2
  | black =>
    match t1 with
    | T red (T red a x vx b) y vy c' =>
        T red (T black a x vx b) y vy (T black c' k vk t2)
    | T red a x vx (T red b y vy c') =>
        T red (T black a x vx b) y vy (T black c' k vk t2)
    | _ =>
      match t2 with
      | T red (T red b y vy c') z vz d =>
          T red (T black t1 k vk b) y vy (T black c' z vz d)
      | T red b y vy (T red c' z vz d) =>
          T red (T black t1 k vk b) y vy (T black c' z vz d)
      | _ => T black t1 k vk t2

def ins {V : Type} (x : Key) (vx : V) (t : RBTree V) : RBTree V :=
  match t with
  | E => T red E x vx E
  | T c a y vy b =>
    if x < y then balance c (ins x vx a) y vy b
    else if y < x then balance c a y vy (ins x vx b)
    else T c a x vx b

def makeBlack {V : Type} (t : RBTree V) : RBTree V :=
  match t with
  | E => E
  | T _ a x vx b => T black a x vx b

def insert {V : Type} (x : Key) (vx : V) (t : RBTree V) : RBTree V :=
  makeBlack (ins x vx t)

def elementsAux {V : Type} (t : RBTree V) (acc : List (Key × V)) : List (Key × V) :=
  match t with
  | E => acc
  | T _ l k v r => elementsAux l ((k, v) :: elementsAux r acc)

def elements {V : Type} (t : RBTree V) : List (Key × V) := elementsAux t []

-- ============================================
-- Section: Case-Analysis Automation
-- ============================================

-- Every branch of balance returns T _, so balance never returns E
private lemma balance_isT {V : Type} (c : Color) (l : RBTree V) (k : Key) (v : V)
    (r : RBTree V) : ∃ c' l' k' v' r', balance c l k v r = T c' l' k' v' r' := by
  unfold balance
  repeat first | exact ⟨_, _, _, _, _, rfl⟩ | split

private lemma balance_ne_E {V : Type} (c : Color) (l : RBTree V) (k : Key) (v : V)
    (r : RBTree V) : balance c l k v r ≠ E := by
  obtain ⟨c', l', k', v', r', h⟩ := balance_isT c l k v r
  rw [h]; exact nofun

theorem ins_not_E {V : Type} (x : Key) (vx : V) (t : RBTree V) : ins x vx t ≠ E := by
  cases t with
  | E => simp [ins]
  | T c l k v r =>
    simp only [ins]; split
    · exact balance_ne_E c (ins x vx l) k v r
    · split
      · exact balance_ne_E c l k v (ins x vx r)
      · exact nofun

-- ============================================
-- Section: BST Invariant
-- ============================================

def ForallT {V : Type} (P : Key → V → Prop) : RBTree V → Prop
  | E => True
  | T _ l k v r => P k v ∧ ForallT P l ∧ ForallT P r

inductive BST {V : Type} : RBTree V → Prop where
  | E : BST E
  | T : ∀ (c : Color) (l : RBTree V) (k : Key) (v : V) (r : RBTree V),
      ForallT (fun k' _ => k' < k) l →
      ForallT (fun k' _ => k' > k) r →
      BST l → BST r →
      BST (T c l k v r)

theorem empty_tree_BST {V : Type} : BST (emptyTree V) := BST.E

lemma ForallT_imp {V : Type} {P Q : Key → V → Prop} {t : RBTree V}
    (h : ForallT P t) (hpq : ∀ k v, P k v → Q k v) : ForallT Q t := by
  induction t with
  | E => trivial
  | T c l k v r ihl ihr =>
    obtain ⟨hpkv, hfl, hfr⟩ := h
    exact ⟨hpq k v hpkv, ihl hfl, ihr hfr⟩

lemma ForallT_greater {V : Type} {t : RBTree V} {k k0 : Key}
    (h : ForallT (fun k' _ => k' > k) t) (hgt : k > k0) :
    ForallT (fun k' _ => k' > k0) t :=
  ForallT_imp h (fun _ _ h' => lt_trans hgt h')

lemma ForallT_less {V : Type} {t : RBTree V} {k k0 : Key}
    (h : ForallT (fun k' _ => k' < k) t) (hlt : k < k0) :
    ForallT (fun k' _ => k' < k0) t :=
  ForallT_imp h (fun _ _ h' => lt_trans h' hlt)

-- balance preserves BST: automated case analysis over all rotation cases
lemma balance_BST {V : Type} {c : Color} {l : RBTree V} {k : Key} {v : V} {r : RBTree V}
    (PL : ForallT (fun k' _ => k' < k) l)
    (PR : ForallT (fun k' _ => k' > k) r)
    (BL : BST l) (BR : BST r) :
    BST (balance c l k v r) := by
  unfold balance; split
  · exact BST.T _ _ _ _ _ PL PR BL BR  -- red
  · split
    · -- LL rotation
      simp only [ForallT] at PL
      obtain ⟨hyk, ⟨hxk, hfak, hfbk⟩, hfck⟩ := PL
      cases BL with | T _ _ _ _ _ hfly hfry bl bc' =>
      simp only [ForallT] at hfly
      obtain ⟨hxy, hfaly, hfbly⟩ := hfly
      cases bl with | T _ _ _ _ _ hfax hfbx ba bb =>
      exact BST.T _ _ _ _ _ ⟨hxy, hfaly, hfbly⟩
        ⟨hyk, hfry, ForallT_greater PR hyk⟩
        (BST.T _ _ _ _ _ hfax hfbx ba bb)
        (BST.T _ _ _ _ _ hfck PR bc' BR)
    · -- LR rotation
      simp only [ForallT] at PL
      obtain ⟨hxk, hfak, hyk, hfbk, hfck⟩ := PL
      cases BL with | T _ _ _ _ _ hflx hfrx ba blr =>
      simp only [ForallT] at hfrx
      obtain ⟨hyx, hfbx, hfcx⟩ := hfrx
      cases blr with | T _ _ _ _ _ hfby hfcy bb bc' =>
      exact BST.T _ _ _ _ _
        ⟨hyx, ForallT_less hflx hyx, hfby⟩
        ⟨hyk, hfcy, ForallT_greater PR hyk⟩
        (BST.T _ _ _ _ _ hflx hfbx ba bb)
        (BST.T _ _ _ _ _ hfck PR bc' BR)
    · split
      · -- RL rotation
        simp only [ForallT] at PR
        obtain ⟨hzk, ⟨hyk, hfbk, hfck⟩, hfdk⟩ := PR
        cases BR with | T _ _ _ _ _ hflz hfrz brl bd =>
        simp only [ForallT] at hflz
        obtain ⟨hyz, hfbz, hfcz⟩ := hflz
        cases brl with | T _ _ _ _ _ hfby hfcy bb bc' =>
        exact BST.T _ _ _ _ _
          ⟨hyk, ForallT_less PL hyk, hfby⟩
          ⟨hyz, hfcy, ForallT_greater hfrz hyz⟩
          (BST.T _ _ _ _ _ PL hfbk BL bb)
          (BST.T _ _ _ _ _ hfcz hfrz bc' bd)
      · -- RR rotation
        simp only [ForallT] at PR
        obtain ⟨hyk, hfbk, hzk, hfck, hfdk⟩ := PR
        cases BR with | T _ _ _ _ _ hfly hfry bb brr =>
        simp only [ForallT] at hfry
        obtain ⟨hzy, hfcy, hfdy⟩ := hfry
        cases brr with | T _ _ _ _ _ hfcz hfdz bc' bd =>
        exact BST.T _ _ _ _ _
          ⟨hyk, ForallT_less PL hyk, hfly⟩
          ⟨hzy, hfcy, hfdy⟩
          (BST.T _ _ _ _ _ PL hfbk BL bb)
          (BST.T _ _ _ _ _ hfcz hfdz bc' bd)
      · exact BST.T _ _ _ _ _ PL PR BL BR  -- default

-- balance preserves ForallT: nodes are just rearranged
lemma balanceP {V : Type} {P : Key → V → Prop} {c : Color} {l r : RBTree V} {k : Key} {v : V}
    (hl : ForallT P l) (hr : ForallT P r) (hkv : P k v) :
    ForallT P (balance c l k v r) := by
  unfold balance
  split
  · exact ⟨hkv, hl, hr⟩
  · split
    · next a x vx b y vy c' =>  -- LL
      simp only [ForallT] at hl; obtain ⟨hpy, ⟨hpx, hpa, hpb⟩, hpc⟩ := hl
      exact ⟨hpy, ⟨hpx, hpa, hpb⟩, ⟨hkv, hpc, hr⟩⟩
    · next a x vx b y vy c' =>  -- LR
      simp only [ForallT] at hl; obtain ⟨hpx, hpa, ⟨hpy, hpb, hpc⟩⟩ := hl
      exact ⟨hpy, ⟨hpx, hpa, hpb⟩, ⟨hkv, hpc, hr⟩⟩
    · split
      · next b y vy c' z vz d =>  -- RL
        simp only [ForallT] at hr; obtain ⟨hpz, ⟨hpy, hpb, hpc⟩, hpd⟩ := hr
        exact ⟨hpy, ⟨hkv, hl, hpb⟩, ⟨hpz, hpc, hpd⟩⟩
      · next b y vy c' z vz d =>  -- RR
        simp only [ForallT] at hr; obtain ⟨hpy, hpb, ⟨hpz, hpc, hpd⟩⟩ := hr
        exact ⟨hpy, ⟨hkv, hl, hpb⟩, ⟨hpz, hpc, hpd⟩⟩
      · exact ⟨hkv, hl, hr⟩

lemma insP {V : Type} {P : Key → V → Prop} {t : RBTree V} {k : Key} {v : V}
    (ht : ForallT P t) (hkv : P k v) : ForallT P (ins k v t) := by
  induction t with
  | E => exact ⟨hkv, trivial, trivial⟩
  | T c l y vy r ihl ihr =>
    simp only [ForallT] at ht; obtain ⟨hpy, hfl, hfr⟩ := ht
    simp only [ins]; split
    · exact balanceP (ihl hfl) hfr hpy
    · split
      · exact balanceP hfl (ihr hfr) hpy
      · exact ⟨hkv, hfl, hfr⟩

lemma ins_BST {V : Type} {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : BST (ins k v t) := by
  induction h with
  | E => exact BST.T _ _ _ _ _ trivial trivial BST.E BST.E
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]; split
    · next hlt => exact balance_BST (insP hfl hlt) hfr ihl hr
    · split
      · next hge hgt => exact balance_BST hfl (insP hfr hgt) hl ihr
      · next hge hle =>
        have : k = y := Int.le_antisymm (Int.not_lt.mp hle) (Int.not_lt.mp hge)
        subst this; exact BST.T _ _ _ _ _ hfl hfr hl hr

theorem insert_BST {V : Type} {t : RBTree V} {v : V} {k : Key}
    (h : BST t) : BST (insert k v t) := by
  unfold insert
  have hins := ins_BST h (k := k) (v := v)
  cases hm : ins k v t with
  | E => exact BST.E
  | T c l x vx r =>
    rw [hm] at hins; simp [makeBlack]
    cases hins with
    | T _ _ _ _ _ fl fr bl br => exact BST.T _ _ _ _ _ fl fr bl br

-- ============================================
-- Section: Verification
-- ============================================

theorem lookup_empty {V : Type} (d : V) (k : Key) : lookup d k (emptyTree V) = d := rfl

private lemma lookup_makeBlack {V : Type} (d : V) (k : Key) (t : RBTree V) :
    lookup d k (makeBlack t) = lookup d k t := by
  cases t <;> simp [makeBlack, lookup]

-- balance preserves lookup semantics
lemma balance_lookup {V : Type} (d : V) {c : Color} {k k' : Key} {v : V}
    {l r : RBTree V}
    (BL : BST l) (BR : BST r)
    (PL : ForallT (fun k' _ => k' < k) l)
    (PR : ForallT (fun k' _ => k' > k) r) :
    lookup d k' (balance c l k v r) =
      if k' < k then lookup d k' l
      else if k < k' then lookup d k' r
      else v := by
  unfold balance; split
  · simp [lookup]  -- red case: trivial
  · split
    · -- LL rotation: need x < y, y < k
      simp only [ForallT] at PL
      obtain ⟨hyk, ⟨_, _, _⟩, _⟩ := PL
      cases BL with | T _ _ _ _ _ hfly _ _ _ =>
      simp only [ForallT] at hfly; obtain ⟨hxy, _, _⟩ := hfly
      simp [lookup]; split_ifs <;> (first | rfl | (exfalso; linarith))
    · -- LR rotation: need x < y, y < k
      simp only [ForallT] at PL
      obtain ⟨hxk, _, hyk, _, _⟩ := PL
      cases BL with | T _ _ _ _ _ _ hfrx _ _ =>
      simp only [ForallT] at hfrx; obtain ⟨hyx, _, _⟩ := hfrx
      simp [lookup]; split_ifs <;> (first | rfl | (exfalso; linarith))
    · split
      · -- RL rotation: need y < z, y > k
        simp only [ForallT] at PR
        obtain ⟨hzk, ⟨hyk, _, _⟩, _⟩ := PR
        cases BR with | T _ _ _ _ _ hflz _ _ _ =>
        simp only [ForallT] at hflz; obtain ⟨hyz, _, _⟩ := hflz
        simp [lookup]; split_ifs <;> (first | rfl | (exfalso; linarith))
      · -- RR rotation: need y > k, z > y
        simp only [ForallT] at PR
        obtain ⟨hyk, _, hzk, _, _⟩ := PR
        cases BR with | T _ _ _ _ _ _ hfry _ _ =>
        simp only [ForallT] at hfry; obtain ⟨hzy, _, _⟩ := hfry
        simp [lookup]; split_ifs <;> (first | rfl | (exfalso; linarith))
      · simp [lookup]  -- default case: trivial

lemma lookup_ins_eq {V : Type} (d : V) {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : lookup d k (ins k v t) = v := by
  induction h with
  | E => simp [ins, lookup]
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]; split
    · next hlt =>
      rw [balance_lookup d (ins_BST hl) hr (insP hfl hlt) hfr]
      simp [show k < y from hlt, ihl]
    · split
      · next hge hgt =>
        rw [balance_lookup d hl (ins_BST hr) hfl (insP hfr hgt)]
        simp [show ¬ k < y from not_lt.mpr hgt.le, show y < k from hgt, ihr]
      · next hge hle =>
        have : k = y := Int.le_antisymm (Int.not_lt.mp hle) (Int.not_lt.mp hge)
        subst this; simp [lookup]

theorem lookup_ins_neq {V : Type} (d : V) {t : RBTree V} {k k' : Key} {v : V}
    (h : BST t) (hne : k ≠ k') :
    lookup d k' (ins k v t) = lookup d k' t := by
  induction h with
  | E =>
    simp only [ins, lookup]
    split
    · rfl
    · split
      · rfl
      · next h1 h2 => exact absurd (Int.le_antisymm (Int.not_lt.mp h2) (Int.not_lt.mp h1)) hne.symm
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]; split
    · next hlt =>
      rw [balance_lookup d (ins_BST hl) hr (insP hfl hlt) hfr]
      simp only [lookup]; split
      · next hk'y => simp [ihl]
      · split
        · next h1 h2 => simp_all
        · next h1 h2 =>
          have : k' = y := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
          subst this; simp
    · split
      · next hge hgt =>
        rw [balance_lookup d hl (ins_BST hr) hfl (insP hfr hgt)]
        simp only [lookup]; split
        · next hk'y => simp
        · split
          · next h1 h2 => simp [ihr]
          · next h1 h2 =>
            have : k' = y := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
            subst this; simp
      · next hge hle =>
        have hky : k = y := le_antisymm (not_lt.mp hle) (not_lt.mp hge)
        subst hky; simp [lookup]
        rcases lt_trichotomy k' k with h | h | h
        · simp [h]
        · exact absurd h.symm hne
        · simp [h, not_lt.mpr h.le]

theorem lookup_insert_eq {V : Type} (d : V) {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : lookup d k (insert k v t) = v := by
  simp only [insert, lookup_makeBlack]; exact lookup_ins_eq d h

theorem lookup_insert_neq {V : Type} (d : V) {t : RBTree V} {k k' : Key} {v : V}
    (h : BST t) (hne : k ≠ k') :
    lookup d k' (insert k v t) = lookup d k' t := by
  simp only [insert, lookup_makeBlack]; exact lookup_ins_neq d h hne

-- ============================================
-- Section: Efficiency (Red-Black Invariants)
-- ============================================

inductive RB {V : Type} : RBTree V → Color → Nat → Prop where
  | leaf : ∀ (c : Color), RB E c 0
  | r : ∀ (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l red n → RB r red n → RB (T red l k v r) black n
  | b : ∀ (c : Color) (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l black n → RB r black n → RB (T black l k v r) c (n + 1)

lemma RB_blacken_parent {V : Type} {t : RBTree V} {n : Nat}
    (h : RB t red n) : RB t black n := by
  cases h with
  | leaf => exact RB.leaf _
  | b c l r k v n hl hr => exact RB.b _ _ _ _ _ _ hl hr

inductive NearlyRB {V : Type} : RBTree V → Nat → Prop where
  | r : ∀ (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l black n → RB r black n → NearlyRB (T red l k v r) n
  | b : ∀ (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l black n → RB r black n → NearlyRB (T black l k v r) (n + 1)

private lemma RB_to_NearlyRB {V : Type} {t : RBTree V} {n : Nat}
    (h : RB t black n) (hne : t ≠ E) : NearlyRB t n := by
  cases h with
  | leaf => exact absurd rfl hne
  | r l r k v _ hl hr =>
    exact NearlyRB.r _ _ _ _ _ (RB_blacken_parent hl) (RB_blacken_parent hr)
  | b _ l r k v _ hl hr => exact NearlyRB.b _ _ _ _ _ hl hr

private lemma balance_RB_l {V : Type} {l : RBTree V} {k : Key} {v : V} {r : RBTree V} {n : Nat}
    (hl : NearlyRB l n) (hr : RB r black n) :
    RB (balance black l k v r) black (n + 1) := by
  cases hl with
  | r a b x vx _ ha hb =>
    -- l = T red a x vx b. Check a for LL, b for LR, else default.
    cases ha with
    | leaf =>
      -- a = E, n = 0
      cases hb with
      | leaf =>
        -- b = E. No LL, no LR. Fallthrough → check r.
        cases hr with
        | leaf => simp [balance]; exact RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)) (RB.leaf _)
        | r rl rr rk rvk _ hrl hrr =>
          cases hrl; cases hrr
          simp [balance]
          exact RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _))
            (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _))
      | r b1 b2 bk bvk _ hb1 hb2 =>
        -- b = T red. LR fires. (hb1, hb2 : RB _ red 0 → leaf)
        cases hb1; cases hb2
        simp [balance]
        exact RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ (RB.leaf _) (RB.leaf _))
          (RB.b _ _ _ _ _ _ (RB.leaf _) hr)
    | r a1 a2 ak avk _ ha1 ha2 =>
      -- a = T red. LL fires.
      simp [balance]
      exact RB.r _ _ _ _ _
        (RB.b _ _ _ _ _ _ (RB_blacken_parent ha1) (RB_blacken_parent ha2))
        (RB.b _ _ _ _ _ _ hb hr)
    | b _ a1 a2 ak avk m ha1 ha2 =>
      -- a = T black, n = m + 1. Check b for LR.
      cases hb with
      | r b1 b2 bk bvk _ hb1 hb2 =>
        -- b = T red. LR fires.
        simp [balance]
        exact RB.r _ _ _ _ _
          (RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ ha1 ha2) (RB_blacken_parent hb1))
          (RB.b _ _ _ _ _ _ (RB_blacken_parent hb2) hr)
      | b _ b1 b2 bk bvk m' hb1' hb2' =>
        -- Both T black. Default. Check r.
        cases hr with
        | r rl rr rk rvk _ hrl hrr =>
          cases hrl with
          | b _ _ _ _ _ _ hrl1 hrl2 =>
            cases hrr with
            | b _ _ _ _ _ _ hrr1 hrr2 =>
              simp [balance]
              exact RB.b _ _ _ _ _ _
                (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ ha1 ha2) (RB.b _ _ _ _ _ _ hb1' hb2'))
                (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hrl1 hrl2) (RB.b _ _ _ _ _ _ hrr1 hrr2))
        | b _ rl rr rk rvk _ hrl hrr =>
          simp [balance]
          exact RB.b _ _ _ _ _ _
            (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ ha1 ha2) (RB.b _ _ _ _ _ _ hb1' hb2'))
            (RB.b _ _ _ _ _ _ hrl hrr)
  | b a bt x vx _ ha hb =>
    -- l = T black. No LL/LR. Check r.
    cases hr with
    | r rl rr rk rvk _ hrl hrr =>
      cases hrl with
      | b _ _ _ _ _ _ hrl1 hrl2 =>
        cases hrr with
        | b _ _ _ _ _ _ hrr1 hrr2 =>
          simp [balance]
          exact RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ ha hb)
            (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hrl1 hrl2) (RB.b _ _ _ _ _ _ hrr1 hrr2))
    | b _ rl rr rk rvk _ hrl hrr =>
      simp [balance]
      exact RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ ha hb) (RB.b _ _ _ _ _ _ hrl hrr)

private lemma balance_RB_r {V : Type} {l : RBTree V} {k : Key} {v : V} {r : RBTree V} {n : Nat}
    (hl : RB l black n) (hr : NearlyRB r n) :
    RB (balance black l k v r) black (n + 1) := by
  cases hr with
  | r a b x vx _ ha hb =>
    -- r = T red a x vx b. Check a for RL, b for RR.
    cases ha with
    | leaf =>
      -- a = E, n = 0
      cases hb with
      | leaf =>
        -- b = E. Default. Case-split hl for t1 match.
        cases hl with
        | leaf =>
          simp [balance]
          exact RB.b _ _ _ _ _ _ (RB.leaf _) (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _))
        | r ll lr lk lvk _ hll hlr =>
          cases hll; cases hlr
          simp [balance]
          exact RB.b _ _ _ _ _ _
            (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _))
            (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _))
      | r b1 b2 bk bvk _ hb1 hb2 =>
        -- b = T red. RR fires. (hb1, hb2 : RB _ red 0 → leaf)
        cases hb1; cases hb2
        cases hl with
        | leaf =>
          simp [balance]
          exact RB.r _ _ _ _ _
            (RB.b _ _ _ _ _ _ (RB.leaf _) (RB.leaf _))
            (RB.b _ _ _ _ _ _ (RB.leaf _) (RB.leaf _))
        | r ll lr lk lvk _ hll hlr =>
          cases hll; cases hlr
          simp [balance]
          exact RB.r _ _ _ _ _
            (RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)) (RB.leaf _))
            (RB.b _ _ _ _ _ _ (RB.leaf _) (RB.leaf _))
    | r a1 a2 ak avk _ ha1 ha2 =>
      -- a = T red. RL fires. Case-split hl for t1 match.
      cases hl with
      | leaf =>
        simp [balance]
        exact RB.r _ _ _ _ _
          (RB.b _ _ _ _ _ _ (RB.leaf _) (RB_blacken_parent ha1))
          (RB.b _ _ _ _ _ _ (RB_blacken_parent ha2) hb)
      | r ll lr lk lvk _ hll hlr =>
        cases hll with
        | leaf =>
          cases hlr with
          | leaf =>
            simp [balance]
            exact RB.r _ _ _ _ _
              (RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)) (RB_blacken_parent ha1))
              (RB.b _ _ _ _ _ _ (RB_blacken_parent ha2) hb)
        | b _ _ _ _ _ _ hll1 hll2 =>
          cases hlr with
          | b _ _ _ _ _ _ hlr1 hlr2 =>
            simp [balance]
            exact RB.r _ _ _ _ _
              (RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hll1 hll2) (RB.b _ _ _ _ _ _ hlr1 hlr2)) (RB_blacken_parent ha1))
              (RB.b _ _ _ _ _ _ (RB_blacken_parent ha2) hb)
      | b _ ll lr lk lvk _ hll hlr =>
        simp [balance]
        exact RB.r _ _ _ _ _
          (RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ hll hlr) (RB_blacken_parent ha1))
          (RB.b _ _ _ _ _ _ (RB_blacken_parent ha2) hb)
    | b _ a1 a2 ak avk m ha1 ha2 =>
      -- a = T black, n = m+1. Check b for RR.
      cases hb with
      | r b1 b2 bk bvk _ hb1 hb2 =>
        -- b = T red. RR fires. Case-split hl for t1 match.
        cases hl with
        | r ll lr lk lvk _ hll hlr =>
          cases hll with
          | b _ _ _ _ _ _ hll1 hll2 =>
            cases hlr with
            | b _ _ _ _ _ _ hlr1 hlr2 =>
              simp [balance]
              exact RB.r _ _ _ _ _
                (RB.b _ _ _ _ _ _
                  (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hll1 hll2) (RB.b _ _ _ _ _ _ hlr1 hlr2))
                  (RB.b _ _ _ _ _ _ ha1 ha2))
                (RB.b _ _ _ _ _ _ (RB_blacken_parent hb1) (RB_blacken_parent hb2))
        | b _ ll lr lk lvk _ hll hlr =>
          simp [balance]
          exact RB.r _ _ _ _ _
            (RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ hll hlr) (RB.b _ _ _ _ _ _ ha1 ha2))
            (RB.b _ _ _ _ _ _ (RB_blacken_parent hb1) (RB_blacken_parent hb2))
      | b _ b1 b2 bk bvk m' hb1' hb2' =>
        -- Both T black. Default. Case-split hl for t1 match.
        cases hl with
        | r ll lr lk lvk _ hll hlr =>
          cases hll with
          | b _ _ _ _ _ _ hll1 hll2 =>
            cases hlr with
            | b _ _ _ _ _ _ hlr1 hlr2 =>
              simp [balance]
              exact RB.b _ _ _ _ _ _
                (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hll1 hll2) (RB.b _ _ _ _ _ _ hlr1 hlr2))
                (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ ha1 ha2) (RB.b _ _ _ _ _ _ hb1' hb2'))
        | b _ ll lr lk lvk _ hll hlr =>
          simp [balance]
          exact RB.b _ _ _ _ _ _
            (RB.b _ _ _ _ _ _ hll hlr)
            (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ ha1 ha2) (RB.b _ _ _ _ _ _ hb1' hb2'))
  | b a bt x vx _ ha hb =>
    -- r = T black. No RL/RR. Default. Case-split hl for t1 match.
    cases hl with
    | r ll lr lk lvk _ hll hlr =>
      cases hll with
      | b _ _ _ _ _ _ hll1 hll2 =>
        cases hlr with
        | b _ _ _ _ _ _ hlr1 hlr2 =>
          simp [balance]
          exact RB.b _ _ _ _ _ _
            (RB.r _ _ _ _ _ (RB.b _ _ _ _ _ _ hll1 hll2) (RB.b _ _ _ _ _ _ hlr1 hlr2))
            (RB.b _ _ _ _ _ _ ha hb)
    | b _ ll lr lk lvk _ hll hlr =>
      simp [balance]
      exact RB.b _ _ _ _ _ _ (RB.b _ _ _ _ _ _ hll hlr) (RB.b _ _ _ _ _ _ ha hb)

lemma ins_RB {V : Type} (k : Key) (v : V) (t : RBTree V) (n : Nat) :
    (RB t black n → NearlyRB (ins k v t) n) ∧
    (RB t red n → RB (ins k v t) black n) := by
  induction t generalizing n with
  | E =>
    exact ⟨fun h => by cases h; exact NearlyRB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _),
           fun h => by cases h; exact RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)⟩
  | T c l y vy r ihl ihr =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with
      | r _ _ _ _ _ hl hr =>
        simp only [ins]; split
        · simp only [balance]
          exact NearlyRB.r _ _ _ _ _ ((ihl _).2 hl) (RB_blacken_parent hr)
        · split
          · simp only [balance]
            exact NearlyRB.r _ _ _ _ _ (RB_blacken_parent hl) ((ihr _).2 hr)
          · exact NearlyRB.r _ _ _ _ _ (RB_blacken_parent hl) (RB_blacken_parent hr)
      | b _ _ _ _ _ _ hl hr =>
        simp only [ins]; split
        · exact RB_to_NearlyRB (balance_RB_l ((ihl _).1 hl) hr) (balance_ne_E _ _ _ _ _)
        · split
          · exact RB_to_NearlyRB (balance_RB_r hl ((ihr _).1 hr)) (balance_ne_E _ _ _ _ _)
          · exact NearlyRB.b _ _ _ _ _ hl hr
    · cases h with
      | b _ _ _ _ _ _ hl hr =>
        simp only [ins]; split
        · exact balance_RB_l ((ihl _).1 hl) hr
        · split
          · exact balance_RB_r hl ((ihr _).1 hr)
          · exact RB.b _ _ _ _ _ _ hl hr

theorem ins_red {V : Type} {t : RBTree V} {k : Key} {v : V} {n : Nat}
    (h : RB t red n) : RB (ins k v t) black n :=
  (ins_RB k v t n).2 h

lemma RB_blacken_root {V : Type} {t : RBTree V} {n : Nat}
    (h : RB t black n) : ∃ n', RB (makeBlack t) red n' := by
  cases h with
  | leaf => exact ⟨0, RB.leaf _⟩
  | r l r k v _ hl hr =>
    exact ⟨_ + 1, RB.b _ _ _ _ _ _ (RB_blacken_parent hl) (RB_blacken_parent hr)⟩
  | b c l r k v _ hl hr => exact ⟨_ + 1, RB.b _ _ _ _ _ _ hl hr⟩

theorem insert_RB {V : Type} {t : RBTree V} {k : Key} {v : V} {n : Nat}
    (h : RB t red n) : ∃ n', RB (insert k v t) red n' := by
  unfold insert; exact RB_blacken_root (ins_red h)

-- ============================================
-- Section: Approximate Balance
-- ============================================

def height {V : Type} : RBTree V → Nat
  | E => 0
  | T _ l _ _ r => 1 + max (height l) (height r)

def mindepth {V : Type} : RBTree V → Nat
  | E => 0
  | T _ l _ _ r => 1 + min (mindepth l) (mindepth r)

private lemma RB_height_le {V : Type} {t : RBTree V} {c : Color} {n : Nat}
    (h : RB t c n) : height t ≤ 2 * n + (match c with | .black => 1 | .red => 0) := by
  induction h with
  | leaf c => cases c <;> simp [height]
  | r l r k v n _ _ ihl ihr => simp [height] at *; omega
  | b c l r k v n _ _ ihl ihr =>
    unfold height; cases c <;> simp_all <;> omega

private lemma RB_mindepth_ge {V : Type} {t : RBTree V} {c : Color} {n : Nat}
    (h : RB t c n) : mindepth t ≥ n := by
  induction h with
  | leaf _ => simp [mindepth]
  | r l r k v n _ _ ihl ihr => simp [mindepth]; omega
  | b c l r k v n _ _ ihl ihr => simp [mindepth]; omega

theorem redblack_balanced {V : Type} {t : RBTree V} {c : Color} {n : Nat}
    (h : RB t c n) : height t ≤ 2 * mindepth t + 1 := by
  have hh := RB_height_le h
  have hm := RB_mindepth_ge h
  cases c <;> simp at hh <;> omega

end VFA.Redblack
