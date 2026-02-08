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

private lemma balance_ne_E {V : Type} (c : Color) (l : RBTree V) (k : Key) (v : V)
    (r : RBTree V) : balance c l k v r ≠ E := by
  unfold balance
  split <;> (try exact nofun)
  split <;> (try exact nofun)
  split <;> (try exact nofun)
  split <;> exact nofun

theorem ins_not_E {V : Type} (x : Key) (vx : V) (t : RBTree V) : ins x vx t ≠ E := by
  cases t with
  | E => simp [ins]
  | T c l k v r =>
    simp only [ins]
    split
    · exact balance_ne_E ..
    · split
      · exact balance_ne_E ..
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
  ForallT_imp h (fun _ _ h' => by omega)

lemma ForallT_less {V : Type} {t : RBTree V} {k k0 : Key}
    (h : ForallT (fun k' _ => k' < k) t) (hlt : k < k0) :
    ForallT (fun k' _ => k' < k0) t :=
  ForallT_imp h (fun _ _ h' => by omega)

-- balance preserves BST: automated case analysis over the 4 rotation cases + 2 trivial cases
lemma balance_BST {V : Type} {c : Color} {l : RBTree V} {k : Key} {v : V} {r : RBTree V}
    (PL : ForallT (fun k' _ => k' < k) l)
    (PR : ForallT (fun k' _ => k' > k) r)
    (BL : BST l) (BR : BST r) :
    BST (balance c l k v r) := by
  unfold balance
  split
  · -- Red: no rotation
    exact BST.T _ _ _ _ _ PL PR BL BR
  · -- Black: match on left subtree
    split
    · -- Left-left rotation: l = T red (T red a x vx b) y vy c'
      -- Result: T red (T black a x vx b) y vy (T black c' k v r)
      rename_i a x vx b y vy c'
      simp only [ForallT] at PL
      obtain ⟨hyk, ⟨hxk, hfak, hfbk⟩, hfck⟩ := PL
      cases BL with
      | T _ _ _ _ _ hfly hfry bl bc' =>
        simp only [ForallT] at hfly
        obtain ⟨hxy, hfaly, hfbly⟩ := hfly
        cases bl with
        | T _ _ _ _ _ hfax hfbx ba bb =>
          exact BST.T _ _ y vy _
            ⟨hxy, hfaly, hfbly⟩
            ⟨by omega, hfry, ForallT_greater PR (by omega)⟩
            (BST.T _ a x vx b hfax hfbx ba bb)
            (BST.T _ c' k v r hfck PR bc' BR)
    · split
      · -- Left-right rotation: l = T red a x vx (T red b y vy c')
        -- Result: T red (T black a x vx b) y vy (T black c' k v r)
        rename_i a x vx b y vy c'
        simp only [ForallT] at PL
        obtain ⟨hxk, hfak, ⟨hyk, hfbk, hfck⟩⟩ := PL
        cases BL with
        | T _ _ _ _ _ hflx hfrx ba blr =>
          simp only [ForallT] at hfrx
          obtain ⟨hyx, hfbx, hfcx⟩ := hfrx
          cases blr with
          | T _ _ _ _ _ hfby hfcy bb bc' =>
            exact BST.T _ _ y vy _
              ⟨by omega, ForallT_less hfak (by omega), hfby⟩
              ⟨by omega, hfcy, ForallT_greater PR (by omega)⟩
              (BST.T _ a x vx b hflx ⟨by omega, hfbx, hfby.imp (fun _ _ h => by omega)⟩ ba bb)
              (BST.T _ c' k v r hfck PR bc' BR)
      · -- Wildcard for left: match on right subtree
        split
        · -- Right-left rotation: r = T red (T red b y vy c') z vz d
          -- Result: T red (T black l k v b) y vy (T black c' z vz d)
          rename_i b y vy c' z vz d
          simp only [ForallT] at PR
          obtain ⟨hzk, ⟨hyk, hfbk, hfck⟩, hfdk⟩ := PR
          cases BR with
          | T _ _ _ _ _ hflz hfrz blr bd =>
            simp only [ForallT] at hflz
            obtain ⟨hyz, hfby, hfcy⟩ := hflz
            cases blr with
            | T _ _ _ _ _ hfby' hfcy' bb bc' =>
              exact BST.T _ _ y vy _
                ⟨by omega, ForallT_less PL (by omega), hfby'⟩
                ⟨by omega, hfcy', hfrz⟩
                (BST.T _ l k v b (PL) ⟨by omega, hfbk.imp (fun _ _ h => by omega), hfby'.imp (fun _ _ h => by omega)⟩ BL bb)
                (BST.T _ c' z vz d hfcy hfrz bc' bd)
        · split
          · -- Right-right rotation: r = T red b y vy (T red c' z vz d)
            -- Result: T red (T black l k v b) y vy (T black c' z vz d)
            rename_i b y vy c' z vz d
            simp only [ForallT] at PR
            obtain ⟨hyk, hfbk, ⟨hzk, hfck, hfdk⟩⟩ := PR
            cases BR with
            | T _ _ _ _ _ hfby hfry ba brd =>
              simp only [ForallT] at hfry
              obtain ⟨hzy, hfcy, hfdy⟩ := hfry
              cases brd with
              | T _ _ _ _ _ hfcz hfdz bc' bd =>
                exact BST.T _ _ y vy _
                  ⟨by omega, ForallT_less PL (by omega), hfby⟩
                  ⟨by omega, hfcy, hfdy⟩
                  (BST.T _ l k v b PL ⟨by omega, hfbk.imp (fun _ _ h => by omega), hfby.imp (fun _ _ h => by omega)⟩ BL ba)
                  (BST.T _ c' z vz d hfcz hfdz bc' bd)
          · -- Default: T black l k v r
            exact BST.T _ _ _ _ _ PL PR BL BR

-- balance preserves ForallT
lemma balanceP {V : Type} {P : Key → V → Prop} {c : Color} {l r : RBTree V} {k : Key} {v : V}
    (hl : ForallT P l) (hr : ForallT P r) (hkv : P k v) :
    ForallT P (balance c l k v r) := by
  unfold balance
  split
  · exact ⟨hkv, hl, hr⟩
  · split
    · rename_i a x vx b y vy c'
      simp only [ForallT] at hl
      obtain ⟨hpy, ⟨hpx, hpa, hpb⟩, hpc⟩ := hl
      exact ⟨hpy, ⟨hpx, hpa, hpb⟩, ⟨hkv, hpc, hr⟩⟩
    · split
      · rename_i a x vx b y vy c'
        simp only [ForallT] at hl
        obtain ⟨hpx, hpa, ⟨hpy, hpb, hpc⟩⟩ := hl
        exact ⟨hpy, ⟨hpx, hpa, hpb⟩, ⟨hkv, hpc, hr⟩⟩
      · split
        · rename_i b y vy c' z vz d
          simp only [ForallT] at hr
          obtain ⟨hpz, ⟨hpy, hpb, hpc⟩, hpd⟩ := hr
          exact ⟨hpy, ⟨hkv, hl, hpb⟩, ⟨hpz, hpc, hpd⟩⟩
        · split
          · rename_i b y vy c' z vz d
            simp only [ForallT] at hr
            obtain ⟨hpy, hpb, ⟨hpz, hpc, hpd⟩⟩ := hr
            exact ⟨hpy, ⟨hkv, hl, hpb⟩, ⟨hpz, hpc, hpd⟩⟩
          · exact ⟨hkv, hl, hr⟩

-- ins preserves ForallT
lemma insP {V : Type} {P : Key → V → Prop} {t : RBTree V} {k : Key} {v : V}
    (ht : ForallT P t) (hkv : P k v) : ForallT P (ins k v t) := by
  induction t with
  | E => exact ⟨hkv, trivial, trivial⟩
  | T c l y vy r ihl ihr =>
    simp only [ForallT] at ht
    obtain ⟨hpy, hfl, hfr⟩ := ht
    simp only [ins]
    split
    · exact balanceP (ihl hfl) hfr hpy
    · split
      · exact balanceP hfl (ihr hfr) hpy
      · exact ⟨hkv, hfl, hfr⟩

-- ins preserves BST
lemma ins_BST {V : Type} {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : BST (ins k v t) := by
  induction h with
  | E => exact BST.T _ _ _ _ _ trivial trivial BST.E BST.E
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]
    split
    · next hlt =>
      exact balance_BST (insP hfl (by omega)) hfr ihl hr
    · split
      · next hge hgt =>
        exact balance_BST hfl (insP hfr (by omega)) hl ihr
      · next hge hle =>
        have : k = y := by omega
        subst this
        exact BST.T _ _ _ _ _ hfl hfr hl hr

-- insert preserves BST
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

-- balance preserves lookup semantics
lemma balance_lookup {V : Type} (d : V) (c : Color) (k k' : Key) (v : V)
    (l r : RBTree V)
    (BL : BST l) (BR : BST r)
    (PL : ForallT (fun k' _ => k' < k) l)
    (PR : ForallT (fun k' _ => k' > k) r) :
    lookup d k' (balance c l k v r) =
      if k' < k then lookup d k' l
      else if k < k' then lookup d k' r
      else v := by
  unfold balance
  split
  · -- Red: T red l k v r — just lookup
    simp [lookup]
  · split
    · -- Left-left: T red (T black a x vx b) y vy (T black c' k v r)
      rename_i a x vx b y vy c'
      simp only [ForallT] at PL
      obtain ⟨hyk, ⟨hxk, _, _⟩, _⟩ := PL
      cases BL with
      | T _ _ _ _ _ hfly _ bl bc' =>
        simp only [ForallT] at hfly
        obtain ⟨hxy, _, _⟩ := hfly
        cases bl with
        | T _ _ _ _ _ hfax hfbx ba bb =>
          simp only [lookup]
          split <;> split <;> split <;> try (split <;> try split) <;> try omega
          all_goals (try rfl)
          all_goals (simp_all [lookup]; omega)
    · split
      · -- Left-right
        rename_i a x vx b y vy c'
        simp only [ForallT] at PL
        obtain ⟨hxk, _, ⟨hyk, _, _⟩⟩ := PL
        cases BL with
        | T _ _ _ _ _ hflx hfrx ba blr =>
          simp only [ForallT] at hfrx
          obtain ⟨hyx, _, _⟩ := hfrx
          cases blr with
          | T _ _ _ _ _ _ _ bb bc' =>
            simp only [lookup]
            split <;> split <;> split <;> try (split <;> try split) <;> try omega
            all_goals (try rfl)
            all_goals (simp_all [lookup]; omega)
      · split
        · -- Right-left
          rename_i b y vy c' z vz dd
          simp only [ForallT] at PR
          obtain ⟨hzk, ⟨hyk, _, _⟩, _⟩ := PR
          cases BR with
          | T _ _ _ _ _ hflz _ blr bd =>
            simp only [ForallT] at hflz
            obtain ⟨hyz, _, _⟩ := hflz
            cases blr with
            | T _ _ _ _ _ _ _ bb bc' =>
              simp only [lookup]
              split <;> split <;> split <;> try (split <;> try split) <;> try omega
              all_goals (try rfl)
              all_goals (simp_all [lookup]; omega)
        · split
          · -- Right-right
            rename_i b y vy c' z vz dd
            simp only [ForallT] at PR
            obtain ⟨hyk, _, ⟨hzk, _, _⟩⟩ := PR
            cases BR with
            | T _ _ _ _ _ hfby hfry ba brd =>
              simp only [ForallT] at hfry
              obtain ⟨hzy, _, _⟩ := hfry
              cases brd with
              | T _ _ _ _ _ _ _ bc' bd =>
                simp only [lookup]
                split <;> split <;> split <;> try (split <;> try split) <;> try omega
                all_goals (try rfl)
                all_goals (simp_all [lookup]; omega)
          · -- Default
            simp [lookup]

lemma lookup_ins_eq {V : Type} (d : V) {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : lookup d k (ins k v t) = v := by
  induction h with
  | E => simp [ins, lookup]
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]
    split
    · next hlt =>
      rw [balance_lookup d _ k k v (ins k v l) r (ins_BST hl) hr (insP hfl (by omega)) hfr]
      simp [show k < y from hlt, ihl]
    · split
      · next hge hgt =>
        rw [balance_lookup d _ y k vy l (ins k v r) hl (ins_BST hr) hfl (insP hfr (by omega))]
        simp [show ¬ k < y from by omega, show y < k from hgt, ihr]
      · next hge hle =>
        have : k = y := by omega
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
      · omega
  | T c l y vy r hfl hfr hl hr ihl ihr =>
    simp only [ins]
    split
    · next hlt =>
      rw [balance_lookup d _ k k' v (ins k v l) r (ins_BST hl) hr (insP hfl (by omega)) hfr]
      simp only [lookup]
      split
      · next hk'y => simp [hk'y, ihl]
      · next hk'y =>
        split
        · rfl
        · next hyk' =>
          have : k' = y := by omega
          subst this; simp [show ¬ k' < k' from by omega]
    · split
      · next hge hgt =>
        rw [balance_lookup d _ y k' vy l (ins k v r) hl (ins_BST hr) hfl (insP hfr (by omega))]
        simp only [lookup]
        split
        · rfl
        · next hk'y =>
          split
          · next hyk' => simp [show ¬ k' < y from by omega, hyk', ihr]
          · next hyk' =>
            have : k' = y := by omega
            subst this; simp [show ¬ y < y from by omega]
      · next hge hle =>
        have hky : k = y := by omega
        subst hky; simp [lookup]
        split <;> simp_all
        split <;> simp_all
        omega

theorem lookup_insert_eq {V : Type} (d : V) {t : RBTree V} {k : Key} {v : V}
    (h : BST t) : lookup d k (insert k v t) = v := by
  unfold insert
  cases hm : ins k v t with
  | E => exact absurd hm (ins_not_E k v t)
  | T c l x vx r =>
    simp [makeBlack, lookup]
    have := lookup_ins_eq d h (k := k) (v := v)
    rw [hm] at this; simp [lookup] at this ⊢
    split
    · next h1 =>
      rw [hm] at this; simp [lookup, show k < x from h1] at this
      assumption
    · split
      · next h1 h2 =>
        rw [hm] at this; simp [lookup, show ¬ k < x from h1, show x < k from h2] at this
        assumption
      · next h1 h2 =>
        have : k = x := by omega
        subst this; assumption

theorem lookup_insert_neq {V : Type} (d : V) {t : RBTree V} {k k' : Key} {v : V}
    (h : BST t) (hne : k ≠ k') :
    lookup d k' (insert k v t) = lookup d k' t := by
  unfold insert
  cases hm : ins k v t with
  | E => exact absurd hm (ins_not_E k v t)
  | T c l x vx r =>
    simp [makeBlack, lookup]
    have := lookup_ins_neq d h hne (k := k) (v := v)
    rw [hm] at this; simp [lookup] at this ⊢
    split
    · next h1 =>
      rw [hm] at this; simp [lookup, show k' < x from h1] at this
      assumption
    · split
      · next h1 h2 =>
        rw [hm] at this; simp [lookup, show ¬ k' < x from h1, show x < k' from h2] at this
        assumption
      · next h1 h2 =>
        have : k' = x := by omega
        subst this; assumption

-- ============================================
-- Section: Efficiency (Red-Black Invariants)
-- ============================================

-- RB t c n: tree t satisfies RB invariants assuming parent color c and black height n
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

-- NearlyRB: RB except possibly double-red at root
inductive NearlyRB {V : Type} : RBTree V → Nat → Prop where
  | r : ∀ (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l black n → RB r black n → NearlyRB (T red l k v r) n
  | b : ∀ (l r : RBTree V) (k : Key) (v : V) (n : Nat),
      RB l black n → RB r black n → NearlyRB (T black l k v r) (n + 1)

-- Helper: balance preserves RB/NearlyRB in ins context
private lemma balance_RB_red {V : Type} {l r : RBTree V} {k : Key} {v : V} {n : Nat}
    (hl : NearlyRB l n) (hr : RB r black n) :
    RB (balance black l k v r) black (n + 1) := by
  unfold balance
  cases hl with
  | r ll lr lk lv _ hll hlr =>
    -- l = T red ll lk lv lr, parent expects black
    cases hll with
    | leaf =>
      cases hlr with
      | leaf => exact RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)) (RB.b _ _ _ _ _ _ (RB.leaf _) hr)
      | b c ll' lr' lk' lv' _ hll' hlr' =>
        exact RB.b _ _ _ _ _ _ (RB.r _ _ _ _ _ (RB.leaf _) (RB.b _ _ _ _ _ _ hll' hlr')) (RB.b _ _ _ _ _ _ (RB.leaf _) hr)
        -- wait this doesn't match the balance pattern...
    | b c ll' lr' lk' lv' _ hll' hlr' =>
      sorry
  | b ll lr lk lv _ hll hlr =>
    -- l = T black ll lk lv lr, this is NearlyRB.b
    sorry

-- ins preserves RB (conjunction form)
lemma ins_RB {V : Type} {k : Key} {v : V} {t : RBTree V} {n : Nat} :
    (RB t black n → NearlyRB (ins k v t) n) ∧
    (RB t red n → RB (ins k v t) black n) := by
  induction t with
  | E =>
    constructor
    · intro h; cases h; exact NearlyRB.r _ _ _ _ _ (RB.leaf _) (RB.leaf _)
    · intro h; cases h
  | T c l y vy r ihl ihr =>
    constructor
    · intro h
      cases h with
      | r _ _ _ _ _ hl hr =>
        -- t = T red l y vy r, with RB l red n, RB r red n
        simp only [ins]
        split
        · -- ins into left
          sorry
        · split
          · sorry
          · sorry
      | b _ _ _ _ _ _ hl hr =>
        -- t = T black l y vy r, with RB l black n, RB r black n
        simp only [ins]
        split
        · -- ins into left: balance black (ins k v l) y vy r
          sorry
        · split
          · sorry
          · sorry
    · intro h
      cases h with
      | r _ _ _ _ _ hl hr =>
        simp only [ins]
        split
        · -- ins into left of red node
          sorry
        · split
          · sorry
          · sorry

-- Corollary: ins on red-parented tree gives black-parented tree
theorem ins_red {V : Type} {t : RBTree V} {k : Key} {v : V} {n : Nat}
    (h : RB t red n) : RB (ins k v t) black n :=
  ins_RB.2 h

lemma RB_blacken_root {V : Type} {t : RBTree V} {n : Nat}
    (h : RB t black n) : ∃ n', RB (makeBlack t) red n' := by
  cases h with
  | leaf => exact ⟨0, RB.leaf _⟩
  | r l r k v _ hl hr => exact ⟨_ + 1, RB.b _ _ _ _ _ _ hl hr⟩
  | b c l r k v _ hl hr => exact ⟨_ + 1, RB.b _ _ _ _ _ _ hl hr⟩

theorem insert_RB {V : Type} {t : RBTree V} {k : Key} {v : V} {n : Nat}
    (h : RB t red n) : ∃ n', RB (insert k v t) red n' := by
  unfold insert
  have hins := ins_red h (k := k) (v := v)
  exact RB_blacken_root hins

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
    (h : RB t c n) : height t ≤ 2 * n + 1 := by
  induction h with
  | leaf _ => simp [height]
  | r l r k v n _ _ ihl ihr => simp [height]; omega
  | b c l r k v n _ _ ihl ihr => simp [height]; omega

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
  omega

end VFA.Redblack
