import Mathlib

/-!
# VFA Chapter: Binom
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/Binom.html

## Overview
Binomial queues: a mergeable priority queue with O(log N) insert, delete_max,
and merge operations. Implements the PRIQUEUE interface with a list of
power-of-2 heaps.

## Mathlib Mappings
- VFA `Permutation` ↦ `List.Perm` (Mathlib)
- VFA `Forall` ↦ `List.Forall` / `∀ x ∈ l, P x`
- VFA `tree`/`priqueue` ↦ fresh `BinomTree`/`BinomPQ`
-/

namespace VFA.Binom

-- ============================================
-- Section: Program
-- ============================================

/-- Binary tree for binomial queues. -/
inductive BinomTree : Type where
  | Leaf : BinomTree
  | Node : Nat → BinomTree → BinomTree → BinomTree
  deriving Repr, DecidableEq

/-- A binomial priority queue is a list of trees. -/
abbrev BinomPQ := List BinomTree

def empty : BinomPQ := []

/-- Merge two trees of the same rank. The larger key becomes root. -/
def smash (t u : BinomTree) : BinomTree :=
  match t, u with
  | .Node x t1 .Leaf, .Node y u1 .Leaf =>
    if x > y then .Node x (.Node y u1 t1) .Leaf
    else .Node y (.Node x t1 u1) .Leaf
  | _, _ => .Leaf -- bogus value for ill-formed trees

/-- Insert a tree into a priqueue with carry propagation. -/
def carry (q : BinomPQ) (t : BinomTree) : BinomPQ :=
  match q, t with
  | [], .Leaf => []
  | [], _ => [t]
  | .Leaf :: q', _ => t :: q'
  | u :: q', .Leaf => u :: q'
  | u :: q', _ => .Leaf :: carry q' (smash t u)

/-- Insert a key into a binomial queue. -/
def insert (x : Nat) (q : BinomPQ) : BinomPQ :=
  carry q (.Node x .Leaf .Leaf)

/-- Merge two priqueues with carry. -/
def join (p q : BinomPQ) (c : BinomTree) : BinomPQ :=
  match p, q, c with
  | [], _, _ => carry q c
  | _, [], _ => carry p c
  | .Leaf :: p', .Leaf :: q', _ => c :: join p' q' .Leaf
  | .Leaf :: p', q1 :: q', .Leaf => q1 :: join p' q' .Leaf
  | .Leaf :: p', q1 :: q', .Node _ _ _ => .Leaf :: join p' q' (smash c q1)
  | p1 :: p', .Leaf :: q', .Leaf => p1 :: join p' q' .Leaf
  | p1 :: p', .Leaf :: q', .Node _ _ _ => .Leaf :: join p' q' (smash c p1)
  | p1 :: p', q1 :: q', _ => c :: join p' q' (smash p1 q1)
  termination_by p.length + q.length
  decreasing_by all_goals simp_all [List.length_cons]; omega

/-- Unzip a tree's left spine into a priqueue using CPS. -/
def unzip (t : BinomTree) (cont : BinomPQ → BinomPQ) : BinomPQ :=
  match t with
  | .Node x t1 t2 => unzip t2 (fun q => .Node x t1 .Leaf :: cont q)
  | .Leaf => cont []

/-- Delete max from a single tree, returning the remaining elements as a priqueue. -/
def heapDeleteMax (t : BinomTree) : BinomPQ :=
  match t with
  | .Node _ t1 .Leaf => unzip t1 id
  | _ => [] -- bogus value

/-- Find the maximum key in a priqueue, with accumulator. -/
def findMax' (current : Nat) (q : BinomPQ) : Nat :=
  match q with
  | [] => current
  | .Leaf :: q' => findMax' current q'
  | .Node x _ _ :: q' => findMax' (if x > current then x else current) q'

/-- Find the maximum key in a priqueue. -/
def findMax (q : BinomPQ) : Option Nat :=
  match q with
  | [] => none
  | .Leaf :: q' => findMax q'
  | .Node x _ _ :: q' => some (findMax' x q')

/-- Auxiliary: locate the tree containing the max, split it out. -/
def deleteMaxAux (m : Nat) (p : BinomPQ) : BinomPQ × BinomPQ :=
  match p with
  | .Leaf :: p' =>
    let (j, k) := deleteMaxAux m p'
    (.Leaf :: j, k)
  | .Node x t1 .Leaf :: p' =>
    if m > x then
      let (j, k) := deleteMaxAux m p'
      (.Node x t1 .Leaf :: j, k)
    else
      (.Leaf :: p', heapDeleteMax (.Node x t1 .Leaf))
  | _ => ([], []) -- bogus value

/-- Delete the maximum element from a binomial queue. -/
def deleteMax (q : BinomPQ) : Option (Nat × BinomPQ) :=
  match findMax q with
  | none => none
  | some m =>
    let (p', q') := deleteMaxAux m q
    some (m, join p' q' .Leaf)

/-- Merge two binomial queues. -/
def merge (p q : BinomPQ) : BinomPQ := join p q .Leaf

-- ============================================
-- Section: Characterization Predicates
-- ============================================

/-- `pow2heap' n m t`: `t` is a complete binary tree of depth `n` with all keys ≤ `m`. -/
def pow2heap' : Nat → Nat → BinomTree → Prop
  | 0, _, .Leaf => True
  | 0, _, .Node _ _ _ => False
  | _ + 1, _, .Leaf => False
  | n + 1, m, .Node k l r => m ≥ k ∧ pow2heap' n k l ∧ pow2heap' n m r

/-- `pow2heap n t`: `t` is a power-of-2 heap of depth `n`. -/
def pow2heap (n : Nat) (t : BinomTree) : Prop :=
  match t with
  | .Node m t1 .Leaf => pow2heap' n m t1
  | _ => False

/-- `priq' i l`: `l` is a valid binomial queue starting from rank `i`. -/
def priq' : Nat → BinomPQ → Prop
  | _, [] => True
  | i, t :: l' => (t = .Leaf ∨ pow2heap i t) ∧ priq' (i + 1) l'

/-- `priq q`: `q` is a valid binomial queue. -/
def priq (q : BinomPQ) : Prop := priq' 0 q

-- ============================================
-- Section: Invariant Preservation
-- ============================================

theorem empty_priq : priq empty := trivial

theorem smash_valid (n : Nat) (t u : BinomTree) :
    pow2heap n t → pow2heap n u → pow2heap (n + 1) (smash t u) := by
  intro ht hu
  cases t with
  | Leaf => simp [pow2heap] at ht
  | Node x t1 t2 =>
    cases u with
    | Leaf => simp [pow2heap] at hu
    | Node y u1 u2 =>
      cases t2 with
      | Node _ _ _ => simp [pow2heap] at ht
      | Leaf =>
        cases u2 with
        | Node _ _ _ => simp [pow2heap] at hu
        | Leaf =>
          simp [smash]
          by_cases hxy : x > y
          · simp [hxy, pow2heap, pow2heap']
            exact ⟨by omega, hu, ht⟩
          · simp [hxy, pow2heap, pow2heap']
            exact ⟨by omega, ht, hu⟩

theorem carry_valid (n : Nat) (q : BinomPQ) (hq : priq' n q)
    (t : BinomTree) (ht : t = .Leaf ∨ pow2heap n t) : priq' n (carry q t) := by
  induction q generalizing n t with
  | nil =>
    cases t with
    | Leaf => unfold carry; exact trivial
    | Node x t1 t2 =>
      unfold carry priq'; exact ⟨ht, trivial⟩
  | cons u q' ih =>
    obtain ⟨hu, hq'⟩ := hq
    cases t with
    | Leaf =>
      cases u with
      | Leaf => unfold carry priq'; exact ⟨Or.inl rfl, hq'⟩
      | Node x u1 u2 => unfold carry priq'; exact ⟨hu, hq'⟩
    | Node y t1 t2 =>
      cases u with
      | Leaf => unfold carry priq'; exact ⟨ht, hq'⟩
      | Node x u1 u2 =>
        unfold carry priq'
        exact ⟨Or.inl rfl, ih (n + 1) hq' _ (Or.inr (smash_valid n _ _ (ht.elim (by simp) id) (hu.elim (by simp) id)))⟩

theorem insert_priq (x : Nat) (q : BinomPQ) (hq : priq q) : priq (insert x q) := by
  unfold insert priq
  apply carry_valid 0 q hq
  right; simp [pow2heap, pow2heap']

theorem join_valid (p q : BinomPQ) (c : BinomTree) (n : Nat)
    (hp : priq' n p) (hq : priq' n q) (hc : c = .Leaf ∨ pow2heap n c) :
    priq' n (join p q c) := by
  induction p generalizing q c n with
  | nil =>
    unfold join; exact carry_valid n q hq c hc
  | cons p1 p' ihp =>
    cases q with
    | nil =>
      unfold join; exact carry_valid n (p1 :: p') hp c hc
    | cons q1 q' =>
      obtain ⟨hp1, hp'⟩ := hp
      obtain ⟨hq1, hq'⟩ := hq
      cases p1 with
      | Leaf =>
        cases q1 with
        | Leaf =>
          unfold join priq'
          exact ⟨hc, ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl)⟩
        | Node y u1 u2 =>
          cases c with
          | Leaf =>
            unfold join priq'
            exact ⟨hq1, ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl)⟩
          | Node z z1 z2 =>
            unfold join priq'
            exact ⟨Or.inl rfl, ihp q' _ (n + 1) hp' hq'
              (Or.inr (smash_valid n _ _ (hc.elim (by simp) id) (hq1.elim (by simp) id)))⟩
      | Node x t1 t2 =>
        cases q1 with
        | Leaf =>
          cases c with
          | Leaf =>
            unfold join priq'
            exact ⟨hp1, ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl)⟩
          | Node z z1 z2 =>
            unfold join priq'
            exact ⟨Or.inl rfl, ihp q' _ (n + 1) hp' hq'
              (Or.inr (smash_valid n _ _ (hc.elim (by simp) id) (hp1.elim (by simp) id)))⟩
        | Node y u1 u2 =>
          unfold join priq'
          exact ⟨hc, ihp q' _ (n + 1) hp' hq'
            (Or.inr (smash_valid n _ _ (hp1.elim (by simp) id) (hq1.elim (by simp) id)))⟩

theorem merge_priq (p q : BinomPQ) (hp : priq p) (hq : priq q) :
    priq (merge p q) := by
  unfold merge priq; exact join_valid p q .Leaf 0 hp hq (Or.inl rfl)

-- ============================================
-- Section: Abstraction Relation
-- ============================================

/-- The multiset of keys in a tree, up to permutation. -/
inductive TreeElems : BinomTree → List Nat → Prop where
  | leaf : TreeElems .Leaf []
  | node : ∀ {v tl tr bl br b},
    TreeElems tl bl → TreeElems tr br →
    List.Perm b (v :: bl ++ br) →
    TreeElems (.Node v tl tr) b

/-- The multiset of keys in a binomial queue, up to permutation. -/
inductive PriqueueElems : BinomPQ → List Nat → Prop where
  | nil : PriqueueElems [] []
  | cons : ∀ {t q bt bq b},
    TreeElems t bt → PriqueueElems q bq →
    List.Perm b (bt ++ bq) →
    PriqueueElems (t :: q) b

/-- Abstraction relation for binomial queues. -/
def Abs (p : BinomPQ) (al : List Nat) : Prop := PriqueueElems p al

-- ============================================
-- Section: Abstraction Relation Proofs
-- ============================================

theorem tree_elems_ext (t : BinomTree) (e1 e2 : List Nat)
    (hp : List.Perm e1 e2) (h : TreeElems t e1) : TreeElems t e2 := by
  cases h with
  | leaf => exact hp.nil_eq ▸ TreeElems.leaf
  | node hl hr hperm =>
    exact TreeElems.node hl hr (hp.symm.trans hperm)

theorem tree_perm (t : BinomTree) (e1 e2 : List Nat)
    (h1 : TreeElems t e1) (h2 : TreeElems t e2) : List.Perm e1 e2 := by
  induction t generalizing e1 e2 with
  | Leaf =>
    cases h1; cases h2; exact List.Perm.refl _
  | Node v tl tr ihl ihr =>
    cases h1 with | node h1l h1r hp1 =>
    cases h2 with | node h2l h2r hp2 =>
    exact hp1.trans ((List.Perm.cons v
      ((ihl _ _ h1l h2l).append (ihr _ _ h1r h2r))).trans hp2.symm)

theorem priqueue_elems_ext (q : BinomPQ) (e1 e2 : List Nat)
    (hp : List.Perm e1 e2) (h : PriqueueElems q e1) : PriqueueElems q e2 := by
  cases h with
  | nil => exact hp.nil_eq ▸ PriqueueElems.nil
  | cons ht hq hperm =>
    exact PriqueueElems.cons ht hq (hp.symm.trans hperm)

private theorem perm_of_priqueue_elems (p : BinomPQ) (al bl : List Nat)
    (ha : PriqueueElems p al) (hb : PriqueueElems p bl) : List.Perm al bl := by
  induction p generalizing al bl with
  | nil => cases ha; cases hb; exact List.Perm.refl _
  | cons t q ih =>
    cases ha with | cons hat haq hpa =>
    cases hb with | cons hbt hbq hpb =>
    exact hpa.trans (((tree_perm t _ _ hat hbt).append (ih _ _ haq hbq)).trans hpb.symm)

theorem abs_perm (p : BinomPQ) (al bl : List Nat)
    (_ : priq p) (ha : Abs p al) (hb : Abs p bl) : List.Perm al bl :=
  perm_of_priqueue_elems p al bl ha hb

theorem tree_can_relate (t : BinomTree) : ∃ al, TreeElems t al := by
  induction t with
  | Leaf => exact ⟨[], TreeElems.leaf⟩
  | Node v tl tr ihl ihr =>
    obtain ⟨bl, hbl⟩ := ihl
    obtain ⟨br, hbr⟩ := ihr
    exact ⟨v :: bl ++ br, TreeElems.node hbl hbr (List.Perm.refl _)⟩

theorem can_relate (p : BinomPQ) (_ : priq p) : ∃ al, Abs p al := by
  suffices h : ∀ q : BinomPQ, ∃ al, PriqueueElems q al from h p
  intro q; induction q with
  | nil => exact ⟨[], PriqueueElems.nil⟩
  | cons t q' ih =>
    obtain ⟨bt, hbt⟩ := tree_can_relate t
    obtain ⟨bq, hbq⟩ := ih
    exact ⟨bt ++ bq, PriqueueElems.cons hbt hbq (List.Perm.refl _)⟩

theorem empty_relate : Abs empty [] := PriqueueElems.nil

theorem smash_elems (n : Nat) (t u : BinomTree) (bt bu : List Nat)
    (ht : pow2heap n t) (hu : pow2heap n u)
    (hbt : TreeElems t bt) (hbu : TreeElems u bu) :
    TreeElems (smash t u) (bt ++ bu) := by
  cases t with
  | Leaf => simp [pow2heap] at ht
  | Node x t1 t2 =>
    cases u with
    | Leaf => simp [pow2heap] at hu
    | Node y u1 u2 =>
      cases t2 with
      | Node _ _ _ => simp [pow2heap] at ht
      | Leaf =>
        cases u2 with
        | Node _ _ _ => simp [pow2heap] at hu
        | Leaf =>
          cases hbt with | node h1l h1r hp1 =>
          cases hbu with | node h2l h2r hp2 =>
          cases h1r; cases h2r
          simp [List.append_nil] at hp1 hp2
          simp [smash]
          by_cases hxy : x > y
          · simp [hxy]
            exact TreeElems.node (TreeElems.node h2l h1l (List.Perm.refl _)) TreeElems.leaf
              ((hp1.append hp2).trans
                (List.Perm.cons x (List.perm_middle.trans (List.Perm.cons y List.perm_append_comm)))
                |>.trans (by simp))
          · simp [hxy]
            exact TreeElems.node (TreeElems.node h1l h2l (List.Perm.refl _)) TreeElems.leaf
              ((hp1.append hp2).trans
                ((List.Perm.cons x List.perm_middle).trans (List.Perm.swap y x _))
                |>.trans (by simp))

theorem carry_elems (n : Nat) (q : BinomPQ) (hq : priq' n q)
    (t : BinomTree) (ht : t = .Leaf ∨ pow2heap n t)
    (eq_ : List Nat) (et : List Nat)
    (heq : PriqueueElems q eq_) (het : TreeElems t et) :
    PriqueueElems (carry q t) (eq_ ++ et) := by
  induction q generalizing n t eq_ et with
  | nil =>
    cases heq
    cases t with
    | Leaf => cases het; unfold carry; exact PriqueueElems.nil
    | Node x t1 t2 =>
      unfold carry
      exact PriqueueElems.cons het PriqueueElems.nil (by simp)
  | cons u q' ih =>
    obtain ⟨hu, hq'⟩ := hq
    cases heq with | @cons _ _ bt_u bq _ hut huq hperm =>
    cases t with
    | Leaf =>
      cases het; simp
      cases u with
      | Leaf =>
        cases hut; unfold carry
        exact PriqueueElems.cons TreeElems.leaf huq hperm
      | Node x u1 u2 =>
        unfold carry
        exact PriqueueElems.cons hut huq hperm
    | Node y t1 t2 =>
      cases u with
      | Leaf =>
        cases hut; unfold carry
        exact PriqueueElems.cons het huq
          ((hperm.append (List.Perm.refl et)).trans List.perm_append_comm)
      | Node x u1 u2 =>
        unfold carry
        have smash_he := smash_elems n (.Node y t1 t2) (.Node x u1 u2) et bt_u
          (ht.elim (by simp) id) (hu.elim (by simp) id) het hut
        have carry_he := ih (n + 1) hq' (smash (.Node y t1 t2) (.Node x u1 u2))
          (Or.inr (smash_valid n _ _ (ht.elim (by simp) id) (hu.elim (by simp) id)))
          bq (et ++ bt_u) huq smash_he
        have perm_step : List.Perm (eq_ ++ et) (bq ++ (et ++ bt_u)) := by
          have h1 := hperm.append (List.Perm.refl et)
          rw [List.append_assoc] at h1
          exact h1.trans (by rw [show bq ++ (et ++ bt_u) = (bq ++ et) ++ bt_u from
            (List.append_assoc ..).symm]; exact List.perm_append_comm)
        exact PriqueueElems.cons TreeElems.leaf carry_he perm_step

-- Helper: swapping first two list segments under permutation
private theorem perm_swap_prefix (a b c : List Nat) :
    List.Perm (a ++ (b ++ c)) (b ++ (a ++ c)) := by
  have h := (List.perm_append_comm (l₁ := a) (l₂ := b)).append (List.Perm.refl c)
  rwa [List.append_assoc, List.append_assoc] at h

theorem insert_relate (p : BinomPQ) (al : List Nat) (k : Nat)
    (_ : priq p) (hab : Abs p al) : Abs (insert k p) (k :: al) := by
  unfold insert
  have hte : TreeElems (.Node k .Leaf .Leaf) [k] :=
    TreeElems.node TreeElems.leaf TreeElems.leaf (by simp)
  exact priqueue_elems_ext _ _ _ List.perm_append_comm
    (carry_elems 0 p ‹priq p› _ (Or.inr (by simp [pow2heap, pow2heap'])) al [k] hab hte)

theorem join_elems (p q : BinomPQ) (c : BinomTree) (n : Nat)
    (hp : priq' n p) (hq : priq' n q) (hc : c = .Leaf ∨ pow2heap n c)
    (pe qe ce : List Nat)
    (hpe : PriqueueElems p pe) (hqe : PriqueueElems q qe) (hce : TreeElems c ce) :
    PriqueueElems (join p q c) (ce ++ pe ++ qe) := by
  induction p generalizing q c n pe qe ce with
  | nil =>
    cases hpe; unfold join; simp
    exact priqueue_elems_ext _ _ _ List.perm_append_comm
      (carry_elems n q hq c hc qe ce hqe hce)
  | cons p1 p' ihp =>
    cases q with
    | nil =>
      cases hqe; unfold join; simp
      exact priqueue_elems_ext _ _ _ List.perm_append_comm
        (carry_elems n (p1 :: p') hp c hc pe ce hpe hce)
    | cons q1 q' =>
      obtain ⟨hp1, hp'⟩ := hp
      obtain ⟨hq1, hq'⟩ := hq
      cases hpe with | @cons _ _ bt_p bpe _ hpt hpq hpperm =>
      cases hqe with | @cons _ _ bt_q bqe _ hqt hqq hqperm =>
      cases p1 with
      | Leaf =>
        cases hpt
        cases q1 with
        | Leaf =>
          cases hqt; unfold join
          have join_he := ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl) bpe bqe []
            hpq hqq TreeElems.leaf
          exact PriqueueElems.cons hce join_he (by
            simp only [List.append_assoc, List.nil_append]
            exact (List.Perm.refl ce).append (hpperm.append hqperm))
        | Node y u1 u2 =>
          cases c with
          | Leaf =>
            cases hce; unfold join; simp
            have join_he := ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl) bpe bqe []
              hpq hqq TreeElems.leaf
            exact PriqueueElems.cons hqt join_he (by
              simp only [List.nil_append]
              exact (hpperm.append hqperm).trans (perm_swap_prefix bpe bt_q bqe))
          | Node z z1 z2 =>
            unfold join
            have smash_he := smash_elems n (.Node z z1 z2) (.Node y u1 u2) ce bt_q
              (hc.elim (by simp) id) (hq1.elim (by simp) id) hce hqt
            have join_he := ihp q' (smash (.Node z z1 z2) (.Node y u1 u2)) (n + 1) hp' hq'
              (Or.inr (smash_valid n _ _ (hc.elim (by simp) id) (hq1.elim (by simp) id)))
              bpe bqe (ce ++ bt_q) hpq hqq smash_he
            exact PriqueueElems.cons TreeElems.leaf join_he (by
              simp only [List.append_assoc, List.nil_append]
              exact (List.Perm.refl ce).append (
                (hpperm.append hqperm).trans (perm_swap_prefix bpe bt_q bqe)))
      | Node x t1 t2 =>
        cases q1 with
        | Leaf =>
          cases hqt
          cases c with
          | Leaf =>
            cases hce; unfold join; simp
            have join_he := ihp q' .Leaf (n + 1) hp' hq' (Or.inl rfl) bpe bqe []
              hpq hqq TreeElems.leaf
            exact PriqueueElems.cons hpt join_he (by
              simp only [List.nil_append]
              exact (hpperm.append hqperm).trans (by simp [List.append_assoc]))
          | Node z z1 z2 =>
            unfold join
            have smash_he := smash_elems n (.Node z z1 z2) (.Node x t1 t2) ce bt_p
              (hc.elim (by simp) id) (hp1.elim (by simp) id) hce hpt
            have join_he := ihp q' (smash (.Node z z1 z2) (.Node x t1 t2)) (n + 1) hp' hq'
              (Or.inr (smash_valid n _ _ (hc.elim (by simp) id) (hp1.elim (by simp) id)))
              bpe bqe (ce ++ bt_p) hpq hqq smash_he
            exact PriqueueElems.cons TreeElems.leaf join_he (by
              simp only [List.append_assoc, List.nil_append]
              exact (List.Perm.refl ce).append (
                (hpperm.append hqperm).trans (by simp [List.append_assoc])))
        | Node y u1 u2 =>
          unfold join
          have smash_he := smash_elems n (.Node x t1 t2) (.Node y u1 u2) bt_p bt_q
            (hp1.elim (by simp) id) (hq1.elim (by simp) id) hpt hqt
          have join_he := ihp q' (smash (.Node x t1 t2) (.Node y u1 u2)) (n + 1) hp' hq'
            (Or.inr (smash_valid n _ _ (hp1.elim (by simp) id) (hq1.elim (by simp) id)))
            bpe bqe (bt_p ++ bt_q) hpq hqq smash_he
          exact PriqueueElems.cons hce join_he (by
            simp only [List.append_assoc]
            exact (List.Perm.refl ce).append (
              (hpperm.append hqperm).trans (by
                rw [List.append_assoc]
                exact (List.Perm.refl bt_p).append (perm_swap_prefix bpe bt_q bqe))))

theorem merge_relate (p q : BinomPQ) (pl ql al : List Nat)
    (_ : priq p) (_ : priq q) (hp : Abs p pl) (hq : Abs q ql) (hm : Abs (merge p q) al) :
    List.Perm al (pl ++ ql) := by
  unfold merge at hm
  have join_he := join_elems p q .Leaf 0 ‹priq p› ‹priq q› (Or.inl rfl) pl ql [] hp hq TreeElems.leaf
  simp at join_he
  exact perm_of_priqueue_elems _ _ _ hm join_he

-- Helper lemmas for delete_max proofs
private theorem tree_elems_nil_leaf (t : BinomTree) (h : TreeElems t []) : t = .Leaf := by
  cases h with
  | leaf => rfl
  | node _ _ hperm => exact absurd hperm.length_eq (by simp)

private theorem findMax_eq_none_of_all_leaf :
    ∀ q : BinomPQ, (∀ t ∈ q, t = .Leaf) → findMax q = none := by
  intro q; induction q with
  | nil => simp [findMax]
  | cons t q' ih =>
    intro hall
    have ht : t = .Leaf := hall t (by simp)
    subst ht; unfold findMax
    exact ih (fun u hm => hall u (by simp [hm]))

private theorem all_leaf_of_findMax_eq_none :
    ∀ q : BinomPQ, findMax q = none → (∀ t ∈ q, t = .Leaf) := by
  intro q; induction q with
  | nil => simp
  | cons t q' ih =>
    intro h
    cases t with
    | Leaf =>
      unfold findMax at h
      intro u hu; rcases List.mem_cons.mp hu with rfl | hm
      · rfl
      · exact ih h u hm
    | Node x t1 t2 =>
      unfold findMax at h; simp at h

private theorem priqueue_elems_nil_all_leaf (q : BinomPQ) (h : PriqueueElems q []) :
    ∀ t ∈ q, t = .Leaf := by
  induction q with
  | nil => simp
  | cons t q' ih =>
    cases h with | @cons t _ bt bq _ ht hq hperm =>
    have : bt = [] ∧ bq = [] := by
      have hlen := hperm.length_eq; simp at hlen
      exact ⟨by cases bt <;> simp_all, by cases bq <;> simp_all⟩
    obtain ⟨rfl, rfl⟩ := this
    intro u hu; rcases List.mem_cons.mp hu with rfl | hm
    · exact tree_elems_nil_leaf _ ht
    · exact ih hq u hm

private theorem all_leaf_priqueue_elems_nil (q : BinomPQ) (h : ∀ t ∈ q, t = .Leaf) :
    PriqueueElems q [] := by
  induction q with
  | nil => exact PriqueueElems.nil
  | cons t q' ih =>
    have ht : t = .Leaf := h t (by simp)
    subst ht
    exact PriqueueElems.cons TreeElems.leaf
      (ih (fun u hm => h u (by simp [hm]))) (by simp)

theorem delete_max_None_relate (p : BinomPQ) (_ : priq p) :
    (Abs p [] ↔ deleteMax p = none) := by
  constructor
  · intro h
    have := findMax_eq_none_of_all_leaf p (priqueue_elems_nil_all_leaf p h)
    simp [deleteMax, this]
  · intro h
    unfold deleteMax at h
    split at h <;> simp at h
    rename_i hfm
    exact all_leaf_priqueue_elems_nil p (all_leaf_of_findMax_eq_none p hfm)

-- Helper: unzip with suffix preserves priq
private lemma unzip_priq_gen (d : Nat) (m : Nat) (t : BinomTree)
    (suffix : BinomPQ) (ht : pow2heap' d m t) (hs : priq' d suffix) :
    priq' 0 (unzip t (fun q => suffix ++ q)) := by
  induction t generalizing d m suffix with
  | Leaf =>
    cases d with
    | zero => unfold unzip; simpa
    | succ => simp [pow2heap'] at ht
  | Node k t1 t2 _ iht2 =>
    cases d with
    | zero => simp [pow2heap'] at ht
    | succ d' =>
      obtain ⟨_, ht1, ht2⟩ := ht
      unfold unzip
      exact iht2 d' m (.Node k t1 .Leaf :: suffix) ht2 ⟨Or.inr ht1, hs⟩

private lemma heapDeleteMax_priq (n : Nat) (t : BinomTree) (ht : pow2heap n t) :
    priq (heapDeleteMax t) := by
  cases t with
  | Leaf => simp [pow2heap] at ht
  | Node x t1 t2 =>
    cases t2 with
    | Node _ _ _ => simp [pow2heap] at ht
    | Leaf =>
      unfold heapDeleteMax priq
      exact unzip_priq_gen n x t1 [] ht trivial

private lemma deleteMaxAux_fst_priq (m : Nat) (n : Nat) (p : BinomPQ) (hp : priq' n p) :
    priq' n (deleteMaxAux m p).1 := by
  induction p generalizing n with
  | nil => simp [deleteMaxAux]; trivial
  | cons t p' ih =>
    obtain ⟨ht, hp'⟩ := hp
    cases t with
    | Leaf =>
      unfold deleteMaxAux
      constructor
      · left; rfl
      · exact ih (n + 1) hp'
    | Node x t1 t2 =>
      cases t2 with
      | Node _ _ _ => unfold deleteMaxAux; exact trivial
      | Leaf =>
        unfold deleteMaxAux
        by_cases hm : m > x
        · simp [hm]; exact ⟨ht, ih (n + 1) hp'⟩
        · simp [hm]; exact ⟨Or.inl rfl, hp'⟩

private lemma deleteMaxAux_snd_priq (m : Nat) (n : Nat) (p : BinomPQ) (hp : priq' n p) :
    priq (deleteMaxAux m p).2 := by
  induction p generalizing n with
  | nil => simp [deleteMaxAux]; trivial
  | cons t p' ih =>
    obtain ⟨ht, hp'⟩ := hp
    cases t with
    | Leaf =>
      unfold deleteMaxAux
      exact ih (n + 1) hp'
    | Node x t1 t2 =>
      cases t2 with
      | Node _ _ _ => unfold deleteMaxAux; trivial
      | Leaf =>
        unfold deleteMaxAux
        by_cases hm : m > x
        · simp [hm]; exact ih (n + 1) hp'
        · simp [hm]; exact heapDeleteMax_priq n _ (ht.elim (by simp) id)

theorem delete_max_Some_priq (p q : BinomPQ) (k : Nat)
    (hp : priq p) (hdm : deleteMax p = some (k, q)) : priq q := by
  have hfm : ∃ m, findMax p = some m := by
    cases h : findMax p with
    | none => simp [deleteMax, h] at hdm
    | some m => exact ⟨m, rfl⟩
  obtain ⟨m, hfm⟩ := hfm
  simp only [deleteMax, hfm] at hdm
  have hdm' : m = k ∧ join (deleteMaxAux m p).1 (deleteMaxAux m p).2 .Leaf = q := by
    revert hdm
    generalize deleteMaxAux m p = dma
    intro hdm
    exact ⟨(Prod.mk.inj (Option.some.inj hdm)).1, (Prod.mk.inj (Option.some.inj hdm)).2⟩
  obtain ⟨rfl, rfl⟩ := hdm'
  exact merge_priq _ _ (deleteMaxAux_fst_priq m 0 p hp) (deleteMaxAux_snd_priq m 0 p hp)

-- Helper: pow2heap' implies all keys ≤ bound
private lemma pow2heap'_keys_le (n m : Nat) (t : BinomTree) (te : List Nat)
    (ht : pow2heap' n m t) (hte : TreeElems t te) : ∀ x ∈ te, x ≤ m := by
  induction t generalizing n m te with
  | Leaf => cases hte; simp
  | Node k t1 t2 ih1 ih2 =>
    cases n with
    | zero => simp [pow2heap'] at ht
    | succ n' =>
      obtain ⟨hmk, ht1, ht2⟩ := ht
      cases hte with
      | node h1 h2 hperm =>
        intro x hx
        have hx' := hperm.mem_iff.mp hx
        simp [List.mem_append] at hx'
        rcases hx' with rfl | hx' | hx'
        · exact hmk
        · exact le_trans (ih1 n' k _ ht1 h1 x hx') hmk
        · exact ih2 n' m _ ht2 h2 x hx'

-- Helper: findMax' ≥ current
private lemma findMax'_ge (c : Nat) (q : BinomPQ) : findMax' c q ≥ c := by
  induction q generalizing c with
  | nil => simp [findMax']
  | cons t q' ih =>
    cases t with
    | Leaf => unfold findMax'; exact ih c
    | Node x _ _ =>
      unfold findMax'
      by_cases h : x > c
      · simp [h]; exact le_trans (Nat.le_of_lt h) (ih x)
      · simp [h]; exact ih c

-- Helper: findMax' ≥ all roots in q
private lemma findMax'_ge_roots (c : Nat) (q : BinomPQ) :
    ∀ t ∈ q, ∀ x t1 t2, t = .Node x t1 t2 → findMax' c q ≥ x := by
  induction q generalizing c with
  | nil => simp
  | cons t q' ih =>
    intro u hu x t1 t2 heq
    cases hu with
    | head =>
      subst heq
      unfold findMax'
      by_cases h : x > c
      · simp [h]; exact findMax'_ge x q'
      · simp [h]; exact le_trans (Nat.le_of_not_lt h) (findMax'_ge c q')
    | tail _ hm =>
      cases t with
      | Leaf => unfold findMax'; exact ih c u hm x t1 t2 heq
      | Node y _ _ =>
        unfold findMax'
        by_cases h : y > c
        · simp [h]; exact ih y u hm x t1 t2 heq
        · simp [h]; exact ih c u hm x t1 t2 heq

-- Helper: findMax' returns either the accumulator or a root in q
private lemma findMax'_eq_or_mem (c : Nat) (q : BinomPQ) :
    findMax' c q = c ∨ ∃ t ∈ q, ∃ x t1 t2, t = .Node x t1 t2 ∧ findMax' c q = x := by
  induction q generalizing c with
  | nil => left; simp [findMax']
  | cons t q' ih =>
    cases t with
    | Leaf =>
      unfold findMax'
      rcases ih c with h | ⟨t, ht, x, t1, t2, heq, hval⟩
      · left; exact h
      · right; exact ⟨t, ⟨List.mem_cons_of_mem _ ht, x, t1, t2, heq, hval⟩⟩
    | Node y u1 u2 =>
      unfold findMax'
      by_cases h : y > c
      · simp only [if_pos h]
        rcases ih y with hval | ⟨t, ht, x, t1, t2, heq, hval⟩
        · right; exact ⟨.Node y u1 u2, ⟨by simp, y, u1, u2, rfl, hval⟩⟩
        · right; exact ⟨t, ⟨List.mem_cons_of_mem _ ht, x, t1, t2, heq, hval⟩⟩
      · simp only [if_neg h]
        rcases ih c with hval | ⟨t, ht, x, t1, t2, heq, hval⟩
        · left; exact hval
        · right; exact ⟨t, ⟨List.mem_cons_of_mem _ ht, x, t1, t2, heq, hval⟩⟩

-- Helper: findMax returns the max root, which is ≥ all roots
private lemma findMax_ge_all_roots (p : BinomPQ) (m : Nat)
    (hfm : findMax p = some m) :
    ∀ t ∈ p, ∀ x t1 t2, t = .Node x t1 t2 → m ≥ x := by
  induction p with
  | nil => simp [findMax] at hfm
  | cons t p' ih =>
    cases t with
    | Leaf =>
      unfold findMax at hfm
      intro u hu x t1 t2 heq
      cases hu with
      | head => simp at heq
      | tail _ hm => exact ih hfm u hm x t1 t2 heq
    | Node y u1 u2 =>
      have hfm' : findMax' y p' = m := by unfold findMax at hfm; simpa using hfm
      intro u hu x t1 t2 heq
      cases hu with
      | head => cases heq; rw [← hfm']; exact findMax'_ge y p'
      | tail _ hm => rw [← hfm']; exact findMax'_ge_roots y p' u hm x t1 t2 heq

-- Helper: findMax returns a value that is a root of some tree in p
private lemma findMax_has_eq_root (p : BinomPQ) (m : Nat) (hfm : findMax p = some m) :
    ∃ t ∈ p, ∃ x t1 t2, t = .Node x t1 t2 ∧ x = m := by
  induction p with
  | nil => simp [findMax] at hfm
  | cons t p' ih =>
    cases t with
    | Leaf =>
      unfold findMax at hfm
      obtain ⟨t, ht, x, t1, t2, heq, hval⟩ := ih hfm
      exact ⟨t, ⟨List.mem_cons_of_mem _ ht, x, t1, t2, heq, hval⟩⟩
    | Node y u1 u2 =>
      have hfm' : findMax' y p' = m := by unfold findMax at hfm; simpa using hfm
      rcases findMax'_eq_or_mem y p' with hval | ⟨t, ht, x, t1, t2, heq, hval⟩
      · exact ⟨.Node y u1 u2, ⟨by simp, y, u1, u2, rfl, hval.symm.trans hfm'⟩⟩
      · exact ⟨t, ⟨List.mem_cons_of_mem _ ht, x, t1, t2, heq, hval.symm.trans hfm'⟩⟩

-- Helper: in a valid priqueue, all Node trees have .Leaf right child
private lemma priq_mem_node_leaf (p : BinomPQ) (n : Nat) (hp : priq' n p)
    (t : BinomTree) (ht : t ∈ p) (x : Nat) (t1 t2 : BinomTree) (heq : t = .Node x t1 t2) :
    t2 = .Leaf := by
  induction p generalizing n with
  | nil => simp at ht
  | cons u p' ih =>
    obtain ⟨hu, hp'⟩ := hp
    rcases List.mem_cons.mp ht with rfl | hm
    · subst heq
      rcases hu with h | h
      · simp at h
      · exact match t2, h with | .Leaf, _ => rfl
    · exact ih (n + 1) hp' hm

-- Helper: all elements in a valid priqueue ≤ all roots' upper bound
private lemma priq_elems_le (p : BinomPQ) (k : Nat) (n : Nat)
    (hp : priq' n p) (pe : List Nat) (hpe : PriqueueElems p pe)
    (hge : ∀ t ∈ p, ∀ x t1 t2, t = .Node x t1 t2 → k ≥ x) :
    ∀ x ∈ pe, x ≤ k := by
  induction p generalizing n pe with
  | nil => cases hpe; simp
  | cons t p' ih =>
    obtain ⟨ht, hp'⟩ := hp
    cases hpe with
    | cons hbt hbq hperm =>
      intro x hx
      have hx' := hperm.mem_iff.mp hx
      simp [List.mem_append] at hx'
      rcases hx' with hx' | hx'
      · cases t with
        | Leaf => cases hbt; simp at hx'
        | Node y t1 t2 =>
          cases t2 with
          | Node _ _ _ => exact absurd (ht.resolve_left (by simp)) (by simp [pow2heap])
          | Leaf =>
            have hky : k ≥ y := hge _ (by simp) y t1 .Leaf rfl
            cases hbt with
            | node hbl1 hbr1 hperm_bt =>
              cases hbr1; simp at hperm_bt
              have hx_in := hperm_bt.mem_iff.mp hx'
              simp at hx_in
              rcases hx_in with rfl | hx_in
              · exact hky
              · exact le_trans (pow2heap'_keys_le n y t1 _ (ht.resolve_left (by simp)) hbl1 x hx_in) hky
      · exact ih (n + 1) hp' _ hbq
          (fun u hu y t1 t2 heq => hge u (List.mem_cons_of_mem _ hu) y t1 t2 heq) x hx'

-- Helper: unzip element tracking with CPS
private lemma unzip_elems_gen (d : Nat) (m : Nat) (t : BinomTree)
    (suffix : BinomPQ) (te se : List Nat)
    (ht : pow2heap' d m t) (hte : TreeElems t te)
    (hs : PriqueueElems suffix se) :
    PriqueueElems (unzip t (fun q => suffix ++ q)) (te ++ se) := by
  induction t generalizing d m suffix te se with
  | Leaf =>
    cases d with
    | zero => cases hte; unfold unzip; simpa
    | succ => simp [pow2heap'] at ht
  | Node k t1 t2 _ iht2 =>
    cases d with
    | zero => simp [pow2heap'] at ht
    | succ d' =>
      obtain ⟨_, ht1, ht2⟩ := ht
      cases hte with
      | node h1 h2 hperm =>
        rename_i bl br
        unfold unzip
        have h_node : TreeElems (.Node k t1 .Leaf) (k :: bl) :=
          TreeElems.node h1 TreeElems.leaf (by simp)
        have h_new_suffix : PriqueueElems (.Node k t1 .Leaf :: suffix) ((k :: bl) ++ se) :=
          PriqueueElems.cons h_node hs (List.Perm.refl _)
        have h_ih := iht2 d' m (.Node k t1 .Leaf :: suffix) br ((k :: bl) ++ se) ht2 h2 h_new_suffix
        have goal_perm : List.Perm (br ++ (k :: bl ++ se)) (te ++ se) := by
          have h1 := (perm_swap_prefix (k :: bl) br se).symm
          simp only [List.cons_append] at h1
          have h2 := hperm.symm.append (List.Perm.refl se)
          simp only [List.cons_append, List.append_assoc] at h2
          exact h1.trans h2
        exact priqueue_elems_ext _ _ _ goal_perm h_ih

-- Helper: heapDeleteMax element tracking
private lemma heapDeleteMax_elems (n : Nat) (x : Nat) (t1 : BinomTree)
    (bt : List Nat)
    (ht : pow2heap' n x t1) (hbt : TreeElems t1 bt) :
    PriqueueElems (heapDeleteMax (.Node x t1 .Leaf)) bt := by
  unfold heapDeleteMax
  have := unzip_elems_gen n x t1 [] bt [] ht hbt PriqueueElems.nil
  simpa using this

-- Helper: deleteMaxAux element split (with findMax info, produces m :: pe' ++ qe')
private lemma deleteMaxAux_elems (m n : Nat) (p : BinomPQ) (hp : priq' n p)
    (pe : List Nat) (hpe : PriqueueElems p pe)
    (hge : ∀ t ∈ p, ∀ x t1 t2, t = .Node x t1 t2 → m ≥ x)
    (hextr : ∃ t ∈ p, ∃ x t1, t = .Node x t1 .Leaf ∧ x ≥ m) :
    ∃ pe' qe', PriqueueElems (deleteMaxAux m p).1 pe' ∧
      PriqueueElems (deleteMaxAux m p).2 qe' ∧
      List.Perm pe (m :: (pe' ++ qe')) := by
  induction p generalizing n pe with
  | nil =>
    obtain ⟨t, ht, _⟩ := hextr; simp at ht
  | cons t p' ih =>
    obtain ⟨ht, hp'⟩ := hp
    have hge' : ∀ u ∈ p', ∀ x t1 t2, u = .Node x t1 t2 → m ≥ x :=
      fun u hu => hge u (List.mem_cons_of_mem _ hu)
    cases hpe with
    | cons hbt hbq hperm =>
      rename_i bt bq
      cases t with
      | Leaf =>
        cases hbt
        unfold deleteMaxAux
        have hextr' : ∃ t ∈ p', ∃ x t1, t = .Node x t1 .Leaf ∧ x ≥ m := by
          obtain ⟨t, ht, rest⟩ := hextr
          cases ht with
          | head => obtain ⟨_, _, h, _⟩ := rest; simp at h
          | tail _ hm => exact ⟨t, ⟨hm, rest⟩⟩
        obtain ⟨pe', qe', hpe', hqe', hperm'⟩ := ih (n + 1) hp' bq hbq hge' hextr'
        exact ⟨pe', qe',
          PriqueueElems.cons TreeElems.leaf hpe' (by simp),
          hqe',
          by simp at hperm; exact hperm.trans hperm'⟩
      | Node x t1 t2 =>
        cases t2 with
        | Node _ _ _ => exact absurd (ht.resolve_left (by simp)) (by simp [pow2heap])
        | Leaf =>
          unfold deleteMaxAux
          by_cases hm : m > x
          · -- m > x: skip this tree, extract from p'
            have hextr' : ∃ t ∈ p', ∃ y u1, t = .Node y u1 .Leaf ∧ y ≥ m := by
              obtain ⟨t, ht, y, u1, htnode, hym⟩ := hextr
              cases ht with
              | head => cases htnode; omega
              | tail _ hm' => exact ⟨t, ⟨hm', y, u1, htnode, hym⟩⟩
            obtain ⟨pe', qe', hpe', hqe', hperm'⟩ := ih (n + 1) hp' bq hbq hge' hextr'
            refine ⟨bt ++ pe', qe', ?_, ?_, ?_⟩
            · simp [hm]; exact PriqueueElems.cons hbt hpe' (List.Perm.refl _)
            · simp [hm]; exact hqe'
            · -- pe ~ bt ++ bq, bq ~ m :: pe' ++ qe'
              -- bt ++ m :: (pe' ++ qe') ~ m :: bt ++ (pe' ++ qe') by perm_middle
              exact hperm.trans (((List.Perm.refl bt).append hperm').trans
                (by rw [List.append_assoc]; exact List.perm_middle))
          · -- ¬(m > x): x ≥ m and m ≥ x, so x = m. Extract this tree.
            have hxm : x = m := by
              have := hge (.Node x t1 .Leaf) (by simp) x t1 .Leaf rfl; omega
            obtain ⟨bl, hbl⟩ := tree_can_relate t1
            have hbt_perm : List.Perm bt (x :: bl) :=
              tree_perm _ _ _ hbt (TreeElems.node hbl TreeElems.leaf (by simp))
            refine ⟨bq, bl, ?_, ?_, ?_⟩
            · simp [show ¬(m > x) from hm]
              exact PriqueueElems.cons TreeElems.leaf hbq (by simp)
            · simp [show ¬(m > x) from hm]
              exact heapDeleteMax_elems n x t1 bl (ht.resolve_left (by simp)) hbl
            · exact hperm.trans ((hbt_perm.append (List.Perm.refl bq)).trans
                (hxm ▸ List.Perm.cons x List.perm_append_comm))

theorem delete_max_Some_relate (p q : BinomPQ) (k : Nat) (pl ql : List Nat)
    (hp : priq p) (hpl : Abs p pl) (hdm : deleteMax p = some (k, q)) (hql : Abs q ql) :
    List.Perm pl (k :: ql) ∧ List.Forall (· ≤ k) ql := by
  -- Step 1: Parse deleteMax to extract findMax and deleteMaxAux info
  have hfm : ∃ m, findMax p = some m := by
    cases h : findMax p with
    | none => simp [deleteMax, h] at hdm
    | some m => exact ⟨m, rfl⟩
  obtain ⟨m, hfm⟩ := hfm
  simp only [deleteMax, hfm] at hdm
  have hdm' : m = k ∧ join (deleteMaxAux m p).1 (deleteMaxAux m p).2 .Leaf = q := by
    revert hdm; generalize deleteMaxAux m p = dma; intro hdm
    exact ⟨(Prod.mk.inj (Option.some.inj hdm)).1, (Prod.mk.inj (Option.some.inj hdm)).2⟩
  obtain ⟨rfl, rfl⟩ := hdm'
  -- Now k = m, q = join (deleteMaxAux m p).1 (deleteMaxAux m p).2 .Leaf
  -- Step 2: Get findMax properties
  have hge : ∀ t ∈ p, ∀ x t1 t2, t = .Node x t1 t2 → m ≥ x :=
    findMax_ge_all_roots p m hfm
  have hextr : ∃ t ∈ p, ∃ x t1, t = .Node x t1 .Leaf ∧ x ≥ m := by
    obtain ⟨t, ht, x, t1, t2, heq, hxm⟩ := findMax_has_eq_root p m hfm
    have ht2 := priq_mem_node_leaf p 0 hp t ht x t1 t2 heq
    exact ⟨t, ⟨ht, x, t1, by rw [heq, ht2]; constructor <;> [rfl; omega]⟩⟩
  -- Step 3: Use deleteMaxAux_elems
  obtain ⟨pe', qe', hpe', hqe', hperm_pl⟩ :=
    deleteMaxAux_elems m 0 p hp pl hpl hge hextr
  -- hperm_pl : List.Perm pl (m :: (pe' ++ qe'))
  -- Step 4: Get elements of q via join_elems
  have hq_elems : PriqueueElems (join (deleteMaxAux m p).1 (deleteMaxAux m p).2 .Leaf)
      (pe' ++ qe') := by
    have h := join_elems (deleteMaxAux m p).1 (deleteMaxAux m p).2 .Leaf 0
      (deleteMaxAux_fst_priq m 0 p hp) (deleteMaxAux_snd_priq m 0 p hp)
      (Or.inl rfl) pe' qe' [] hpe' hqe' TreeElems.leaf
    simpa using h
  -- Step 5: Relate ql to pe' ++ qe'
  have hql_perm : List.Perm ql (pe' ++ qe') :=
    abs_perm _ ql (pe' ++ qe')
      (merge_priq _ _ (deleteMaxAux_fst_priq m 0 p hp) (deleteMaxAux_snd_priq m 0 p hp))
      hql hq_elems
  -- Step 6: Prove both parts
  constructor
  · -- Part 1: List.Perm pl (m :: ql)
    exact hperm_pl.trans (List.Perm.cons m hql_perm.symm)
  · -- Part 2: List.Forall (· ≤ m) ql
    have hle_all : ∀ x ∈ pl, x ≤ m := priq_elems_le p m 0 hp pl hpl hge
    exact List.forall_iff_forall_mem.mpr fun x hx =>
      hle_all x (hperm_pl.mem_iff.mpr (List.mem_cons_of_mem _
        (hql_perm.mem_iff.mp hx)))

end VFA.Binom
