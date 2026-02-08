import Mathlib
import ArtificialAlgorithms.VFA.Maps
import ArtificialAlgorithms.VFA.SearchTree

/-!
# VFA Chapter: ADT (Abstract Data Types)
Translated from Verified Functional Algorithms (Software Foundations Vol. 3)
Original: https://softwarefoundations.cis.upenn.edu/vfa-current/ADT.html

## Overview
Demonstrates ADT verification through four progressively sophisticated approaches:
(1) equational specification, (2) representation invariants, (3) model-based
specification, and (4) subset types. Applied to both tables (maps) and queues.

## Mathlib Mappings
- VFA `Module Type Table` ↦ `class Table` (Lean typeclass)
- VFA `Module FunTable` ↦ `instance : Table V (Nat → V)` (function-based)
- VFA `Module ListsTable` ↦ `instance : Table V (List (Nat × V))` (assoc list)
- VFA `Module TreeTable` ↦ `instance : Table V (Tree V)` (BST, wraps SearchTree)
- VFA `subset type {x : A | P}` ↦ `{x : A // P x}` (Lean Subtype)
- VFA `sig/exist/proj1_sig` ↦ `Subtype/⟨_, _⟩/.val/.property`
-/

namespace VFA.ADT

open VFA.Maps (PartialMap p_empty p_update t_update t_update_eq t_update_neq
               t_update_shadow t_update_permute t_apply_empty)
open VFA.SearchTree (Tree emptyTree bound lookup insert BST ForallT
                     empty_tree_BST insert_BST
                     lookup_empty lookup_insert_eq lookup_insert_neq
                     bound_empty bound_insert_eq bound_insert_neq
                     elements elements_complete elements_correct
                     elements_nodup_keys bound_value bound_default
                     mapOfList Abs find mapBound
                     empty_relate bound_relate lookup_relate insert_relate elements_relate)

-- ============================================
-- Section: The Table ADT
-- ============================================

/-- An association table ADT: maps keys (Nat) to values (V).
    Coq's `Module Type Table` becomes a Lean class.
    The three axioms form the equational specification. -/
class Table (V : Type) (table : Type) where
  default : V
  empty : table
  get : Nat → table → V
  set : Nat → V → table → table
  get_empty_default : ∀ (k : Nat), get k empty = default
  get_set_same : ∀ (k : Nat) (v : V) (t : table), get k (set k v t) = v
  get_set_other : ∀ (k k' : Nat) (v : V) (t : table),
    k ≠ k' → get k' (set k v t) = get k' t

-- ============================================
-- Section: Implementing Table with Functions
-- ============================================

/-- Function-based table: `table := Nat → V`. The simplest implementation. -/
def FunTable (V : Type) := Nat → V

def FunTable.empty (default : V) : FunTable V := fun _ => default

def FunTable.get (_ : V) (k : Nat) (t : FunTable V) : V := t k

def FunTable.set' (k : Nat) (v : V) (t : FunTable V) : FunTable V :=
  fun k' => if k = k' then v else t k'

instance (default : V) : Table V (FunTable V) where
  default := default
  empty := FunTable.empty default
  get := FunTable.get default
  set := FunTable.set'
  get_empty_default := fun _ => rfl
  get_set_same := by
    intro k v t; unfold FunTable.get FunTable.set'; simp
  get_set_other := by
    intro k k' v t hne; unfold FunTable.get FunTable.set'; simp [hne]

-- ============================================
-- Section: Implementing Table with Lists
-- ============================================

/-- Association list table: `table := List (Nat × V)`. -/
def ListTable (V : Type) := List (Nat × V)

def ListTable.empty : ListTable V := []

def ListTable.get (default : V) (k : Nat) : ListTable V → V
  | [] => default
  | (k', v) :: t => if k = k' then v else ListTable.get default k t

def ListTable.set' (k : Nat) (v : V) (t : ListTable V) : ListTable V :=
  (k, v) :: t

instance (default : V) : Table V (ListTable V) where
  default := default
  empty := ListTable.empty
  get := ListTable.get default
  set := ListTable.set'
  get_empty_default := fun _ => rfl
  get_set_same := by
    intro k v t; unfold ListTable.get ListTable.set'; simp
  get_set_other := by
    intro k k' v t hne
    show ListTable.get default k' ((k, v) :: t) = ListTable.get default k' t
    simp only [ListTable.get, Ne.symm hne, ↓reduceIte]

-- ============================================
-- Section: Implementing Table with BSTs
-- ============================================

/-- BST-based table wrapping SearchTree operations.
    The three Table axioms follow immediately from SearchTree lemmas. -/
instance (default : V) : Table V (VFA.SearchTree.Tree V) where
  default := default
  empty := emptyTree
  get := fun k t => lookup default k t
  set := fun k v t => insert k v t
  get_empty_default := fun k => lookup_empty default k
  get_set_same := fun k v t => lookup_insert_eq t default k v
  get_set_other := fun k k' v t hne => lookup_insert_neq t default k k' v hne

-- ============================================
-- Section: Extended Table with elements
-- ============================================

/-- Extended table with `bound`, `elements`, and a representation invariant `rep_ok`.

    The first attempt (without rep_ok) fails because `elements_correct` requires
    the BST invariant. This revised version includes `rep_ok` as a precondition.
    Coq's `Module Type ETable` with `Include Table`. -/
class ETable (V : Type) (table : Type) extends Table V table where
  rep_ok : table → Prop
  bound' : Nat → table → Bool
  elements : table → List (Nat × V)
  empty_ok : rep_ok empty
  set_ok : ∀ (k : Nat) (v : V) (t : table), rep_ok t → rep_ok (set k v t)
  bound_empty : ∀ (k : Nat), bound' k empty = false
  bound_set_same : ∀ (k : Nat) (v : V) (t : table), bound' k (set k v t) = true
  bound_set_other : ∀ (k k' : Nat) (v : V) (t : table),
    k ≠ k' → bound' k' (set k v t) = bound' k' t
  elements_complete : ∀ (k : Nat) (v : V) (t : table),
    rep_ok t → bound' k t = true → get k t = v → (k, v) ∈ elements t
  elements_correct : ∀ (k : Nat) (v : V) (t : table),
    rep_ok t → (k, v) ∈ elements t → bound' k t = true ∧ get k t = v

/-- BST implementation of ETable. -/
instance (default : V) : ETable V (VFA.SearchTree.Tree V) where
  default := default
  empty := emptyTree
  get := fun k t => lookup default k t
  set := fun k v t => insert k v t
  get_empty_default := fun k => lookup_empty default k
  get_set_same := fun k v t => lookup_insert_eq t default k v
  get_set_other := fun k k' v t hne => lookup_insert_neq t default k k' v hne
  rep_ok := BST
  bound' := bound
  elements := elements
  empty_ok := empty_tree_BST V
  set_ok := fun k v t hbst => insert_BST k v t hbst
  bound_empty := fun k => bound_empty k
  bound_set_same := fun k v t => bound_insert_eq k t v
  bound_set_other := fun k k' v t hne => bound_insert_neq k k' t v hne
  elements_complete := fun k v t _ hbound hget =>
    elements_complete k v default t hbound hget
  elements_correct := fun k v t hbst hmem =>
    elements_correct k v default t hbst hmem

-- ============================================
-- Section: Model-based Specification
-- ============================================

/-- Model-based specification for tables.
    Uses an abstraction function `Abs : table → PartialMap V` to relate
    concrete operations to an abstract model. -/
class ETableAbs (V : Type) (table : Type) extends Table V table where
  rep_ok : table → Prop
  bound' : Nat → table → Bool
  elements : table → List (Nat × V)
  Abs : table → PartialMap V
  empty_ok : rep_ok empty
  set_ok : ∀ (k : Nat) (v : V) (t : table), rep_ok t → rep_ok (set k v t)
  empty_relate : Abs empty = p_empty
  bound_relate : ∀ (t : table) (k : Nat), rep_ok t → mapBound k (Abs t) = bound' k t
  lookup_relate : ∀ (t : table) (k : Nat), rep_ok t → find default k (Abs t) = get k t
  insert_relate : ∀ (t : table) (k : Nat) (v : V),
    rep_ok t → p_update (Abs t) k v = Abs (set k v t)
  elements_relate : ∀ (t : table), rep_ok t → Abs t = mapOfList (elements t)

/-- BST implementation of model-based table spec.
    All proofs delegate to SearchTree's model-based spec lemmas. -/
instance (default : V) : ETableAbs V (VFA.SearchTree.Tree V) where
  default := default
  empty := emptyTree
  get := fun k t => lookup default k t
  set := fun k v t => insert k v t
  get_empty_default := fun k => lookup_empty default k
  get_set_same := fun k v t => lookup_insert_eq t default k v
  get_set_other := fun k k' v t hne => lookup_insert_neq t default k k' v hne
  rep_ok := BST
  bound' := bound
  elements := elements
  Abs := Abs
  empty_ok := empty_tree_BST V
  set_ok := fun k v t hbst => insert_BST k v t hbst
  empty_relate := empty_relate V
  bound_relate := fun t k hbst => bound_relate t k hbst
  lookup_relate := fun t k hbst => lookup_relate t default k hbst
  insert_relate := fun t k v hbst => (insert_relate t k v hbst).symm
  elements_relate := fun t hbst => elements_relate t hbst

-- ============================================
-- Section: Queue ADT (Algebraic Specification)
-- ============================================

/-- FIFO queue with algebraic (equational) specification.
    `peek` takes a default value for totality; `deq` on empty returns empty. -/
class Queue (V : Type) (queue : Type) where
  empty : queue
  is_empty : queue → Bool
  enq : queue → V → queue
  deq : queue → queue
  peek : V → queue → V
  is_empty_empty : is_empty empty = true
  is_empty_nonempty : ∀ q v, is_empty (enq q v) = false
  peek_empty : ∀ d, peek d empty = d
  peek_nonempty : ∀ d q v, peek d (enq q v) = peek v q
  deq_empty : deq empty = empty
  deq_nonempty : ∀ q v,
    deq (enq q v) = if is_empty q then q else enq (deq q) v

/-- List-based queue: front of list = front of queue.
    `enq` is O(n) (appends to back), `deq`/`peek` are O(1). -/
instance : Queue Nat (List Nat) where
  empty := []
  is_empty := List.isEmpty
  enq := fun q v => q ++ [v]
  deq := fun q => match q with | [] => [] | _ :: t => t
  peek := fun d q => match q with | [] => d | h :: _ => h
  is_empty_empty := rfl
  is_empty_nonempty := by intro q v; cases q <;> rfl
  peek_empty := fun _ => rfl
  peek_nonempty := by intro d q v; cases q <;> rfl
  deq_empty := rfl
  deq_nonempty := by intro q v; cases q <;> rfl

-- ============================================
-- Section: Queue with Model-based Specification
-- ============================================

/-- Model-based queue specification using `Abs : queue → List V`.
    The abstraction function maps the concrete queue to a simple list. -/
class QueueAbs (V : Type) (queue : Type) where
  empty : queue
  is_empty : queue → Bool
  enq : queue → V → queue
  deq : queue → queue
  peek : V → queue → V
  Abs : queue → List V
  empty_relate : Abs empty = []
  enq_relate : ∀ q v, Abs (enq q v) = Abs q ++ [v]
  peek_relate : ∀ d q, peek d q = (Abs q).head?.getD d
  deq_relate : ∀ q, Abs (deq q) = (Abs q).tail

/-- Two-list queue: `(front, back)` where `Abs (f, b) = f ++ b.reverse`.
    Achieves amortized O(1) for all operations. -/
def TwoListQueue (V : Type) := List V × List V

namespace TwoListQueue

def Abs (q : TwoListQueue V) : List V := q.1 ++ q.2.reverse

def empty : TwoListQueue V := ([], [])

def is_empty (q : TwoListQueue V) : Bool :=
  match q with
  | ([], []) => true
  | _ => false

def enq (q : TwoListQueue V) (v : V) : TwoListQueue V :=
  (q.1, v :: q.2)

def deq (q : TwoListQueue V) : TwoListQueue V :=
  match q with
  | ([], []) => ([], [])
  | ([], b) =>
    match b.reverse with
    | [] => ([], [])
    | _ :: f => (f, [])
  | (_ :: f, b) => (f, b)

def peek (d : V) (q : TwoListQueue V) : V :=
  match q with
  | ([], []) => d
  | ([], b) =>
    match b.reverse with
    | [] => d
    | v :: _ => v
  | (v :: _, _) => v

theorem empty_relate : Abs (empty : TwoListQueue V) = [] := rfl

theorem enq_relate (q : TwoListQueue V) (v : V) :
    Abs (enq q v) = Abs q ++ [v] := by
  simp [Abs, enq, List.reverse_cons, List.append_assoc]

theorem peek_relate (d : V) (q : TwoListQueue V) :
    peek d q = (Abs q).head?.getD d := by
  match q with
  | ([], []) => rfl
  | ([], h :: t) =>
    simp only [peek, Abs, List.nil_append, List.reverse_cons]
    have hne : t.reverse ++ [h] ≠ [] := by simp
    match heq : t.reverse ++ [h] with
    | [] => exact absurd heq hne
    | v :: f => simp [List.head?, Option.getD]
  | (v :: f, b) =>
    simp [peek, Abs, List.head?, Option.getD]

theorem deq_relate (q : TwoListQueue V) :
    Abs (deq q) = (Abs q).tail := by
  match q with
  | ([], []) => rfl
  | ([], h :: t) =>
    simp only [deq, Abs, List.nil_append, List.reverse_cons]
    have hne : t.reverse ++ [h] ≠ [] := by simp
    match heq : t.reverse ++ [h] with
    | [] => exact absurd heq hne
    | v :: f => simp [List.tail]
  | (_ :: f, b) =>
    simp [deq, Abs]

instance : QueueAbs V (TwoListQueue V) where
  empty := empty
  is_empty := is_empty
  enq := enq
  deq := deq
  peek := peek
  Abs := Abs
  empty_relate := empty_relate
  enq_relate := enq_relate
  peek_relate := peek_relate
  deq_relate := deq_relate

end TwoListQueue

-- ============================================
-- Section: Subset Types for ADT Invariants
-- ============================================

/-- Extended table using subset types to enforce the BST invariant.
    Unlike ETable, `rep_ok` is baked into the `table` type itself,
    so it doesn't appear as a precondition in specifications.

    This is the Lean-idiomatic approach — a natural fit for Lean's
    Subtype (`{x : A // P x}`). -/
class ETableSubset (V : Type) (table : Type) extends Table V table where
  bound' : Nat → table → Bool
  elements : table → List (Nat × V)
  bound_empty : ∀ (k : Nat), bound' k empty = false
  bound_set_same : ∀ (k : Nat) (v : V) (t : table), bound' k (set k v t) = true
  bound_set_other : ∀ (k k' : Nat) (v : V) (t : table),
    k ≠ k' → bound' k' (set k v t) = bound' k' t
  elements_complete : ∀ (k : Nat) (v : V) (t : table),
    bound' k t = true → get k t = v → (k, v) ∈ elements t
  elements_correct : ∀ (k : Nat) (v : V) (t : table),
    (k, v) ∈ elements t → bound' k t = true ∧ get k t = v

-- BST table with subset types: `table := {t : Tree V // BST t}`.
-- The BST invariant is enforced by the type, not by preconditions.
namespace TreeSubset

def BSTTree (V : Type) := {t : VFA.SearchTree.Tree V // BST t}

@[simp] def stEmpty : BSTTree V :=
  ⟨emptyTree, empty_tree_BST V⟩

@[simp] def stGet (default : V) (k : Nat) (t : BSTTree V) : V :=
  lookup default k t.val

@[simp] def stSet (k : Nat) (v : V) (t : BSTTree V) : BSTTree V :=
  ⟨insert k v t.val, insert_BST k v t.val t.property⟩

@[simp] def stBound (k : Nat) (t : BSTTree V) : Bool :=
  bound k t.val

@[simp] def stElements (t : BSTTree V) : List (Nat × V) :=
  elements t.val

instance (default : V) : ETableSubset V (BSTTree V) where
  default := default
  empty := stEmpty
  get := stGet default
  set := stSet
  get_empty_default := by intro k; simp [lookup_empty]
  get_set_same := by intro k v t; simp [lookup_insert_eq]
  get_set_other := by intro k k' v t hne; simp [lookup_insert_neq _ _ _ _ _ hne]
  bound' := stBound
  elements := stElements
  bound_empty := by intro k; simp [bound_empty]
  bound_set_same := by intro k v t; simp [bound_insert_eq]
  bound_set_other := by intro k k' v t hne; simp [bound_insert_neq _ _ _ _ hne]
  elements_complete := by
    intro k v t hbound hget; simp at hbound hget
    exact elements_complete k v default t.val hbound hget
  elements_correct := by
    intro k v t hmem; simp at hmem
    have h := elements_correct k v default t.val t.property hmem
    simp; exact h

end TreeSubset

-- ============================================
-- Section: Summary
-- ============================================

/-!
## ADT Verification Approaches

### Equational Specification
- Define a **representation invariant** for legal values of the representation type
- Prove each operation **preserves** the invariant
- Verify the **equational specification** using the invariant

### Model-based Specification
- Define and verify preservation of the representation invariant
- Define an **abstraction function** relating concrete to abstract types
- Prove operations **commute** with the abstraction function

### Subset Types (Lean-idiomatic)
- Encode the representation invariant directly in the **type** (`{t : Tree V // BST t}`)
- Operations carry proofs: construction guarantees invariant preservation
- No `rep_ok` preconditions needed in specifications
- This is the recommended approach in Lean 4 — matches the `code_with_proofs` skill's subtype pattern
-/

end VFA.ADT
