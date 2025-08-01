import Mathlib

-- Value Iteration Algorithm for Markov Decision Processes
-- Using Rat (rational numbers) for computability and provability

-- Define a Markov Decision Process (MDP)
structure MDP (S : Type) (A : Type) where
  -- List of all states
  states : List S
  -- List of all actions
  actions : List A
  -- States list must be non-empty
  states_nonempty : states.length > 0
  -- Actions list must be non-empty
  actions_nonempty : actions.length > 0
  -- Transition function: P(s' | s, a)
  P : S → A → S → ℚ
  -- Reward function: R(s, a)  
  R : S → A → ℚ
  -- Transition probabilities must be non-negative
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  -- Transition probabilities must sum to 1 for each state-action pair
  P_sum_one : ∀ s ∈ states, ∀ a ∈ actions, (states.map (P s a)).sum = 1

-- Value function type
def ValueFunction (S : Type) := S → ℚ

-- Helper to find maximum over a list
def listMax : List ℚ → ℚ
  | [] => 0
  | [x] => x
  | x :: xs => max x (listMax xs)

-- Bellman operator for value iteration
def bellmanOperator {S A : Type} (mdp : MDP S A) (γ : ℚ) (v : ValueFunction S) : ValueFunction S :=
  fun s => 
    listMax (mdp.actions.map fun a =>
      mdp.R s a + γ * (mdp.states.map (fun s' => mdp.P s a s' * v s')).sum)

-- Value iteration algorithm (computable)
def valueIteration {S A : Type} (mdp : MDP S A) (γ : ℚ) : Nat → ValueFunction S
  | 0 => fun _ => 0
  | n + 1 => bellmanOperator mdp γ (valueIteration mdp γ n)

-- Optimal value function specification
def isOptimalValueFunction {S A : Type} (mdp : MDP S A) (γ : ℚ) (v : ValueFunction S) : Prop :=
  ∀ s ∈ mdp.states, v s = bellmanOperator mdp γ v s

-- Convergence check (computable version)
def hasConverged {S A : Type} (mdp : MDP S A) (v1 v2 : ValueFunction S) (ε : ℚ) : Bool :=
  mdp.states.all fun s => abs (v1 s - v2 s) < ε

-- Main value iteration with convergence check
def valueIterationWithConvergence {S A : Type} (mdp : MDP S A) (γ : ℚ) (ε : ℚ) (maxIter : Nat) : ValueFunction S × Nat :=
  let rec loop : Nat → ValueFunction S → ValueFunction S × Nat
    | 0, v => (v, maxIter)
    | n + 1, v => 
      let v' := bellmanOperator mdp γ v
      if hasConverged mdp v v' ε then
        (v', maxIter - n)
      else
        loop n v'
  loop maxIter (fun _ => 0)

-- Theoretical specifications for convergence proofs

/-
## Proof Sketch for Value Iteration Convergence

The convergence proof follows these key steps:

1. **Contraction Property**: Show that the Bellman operator T is a γ-contraction
   in the supremum norm, i.e., ||T(v₁) - T(v₂)||∞ ≤ γ||v₁ - v₂||∞

2. **Banach Fixed Point Theorem**: Since T is a contraction on a complete metric
   space (bounded functions with sup norm), it has a unique fixed point v*

3. **Convergence**: The sequence v_n = T^n(v₀) converges to v* for any initial v₀

4. **Optimality**: The fixed point v* satisfies the Bellman equation and is therefore
   the optimal value function

5. **Error Bounds**: After n iterations, ||v_n - v*||∞ ≤ γⁿ/(1-γ) · ||v₁ - v₀||∞
-/

-- Define supremum norm for value functions
def supNorm {S A : Type} (mdp : MDP S A) (v : ValueFunction S) : ℚ :=
  listMax (mdp.states.map fun s => abs (v s))

-- Define the difference of two value functions
def vDiff {S : Type} (v₁ v₂ : ValueFunction S) : ValueFunction S :=
  fun s => v₁ s - v₂ s

-- Convergence specification
def convergesTo {S A : Type} (mdp : MDP S A) (seq : Nat → ValueFunction S) (limit : ValueFunction S) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ s ∈ mdp.states, abs (seq n s - limit s) < ε

-- Main convergence theorem
theorem valueIterationConverges {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) :
    ∃ v_star, isOptimalValueFunction mdp γ v_star ∧ 
    convergesTo mdp (valueIteration mdp γ) v_star := by
  -- The proof uses the Banach fixed point theorem:
  -- 1. The Bellman operator T is a γ-contraction (by bellmanContraction)
  -- 2. Since γ < 1, T has a unique fixed point v_star
  -- 3. The fixed point v_star satisfies v_star = T(v_star), so it's optimal
  -- 4. Value iteration v_n = T^n(v_0) converges to v_star
  
  -- Step 1: Construct the optimal value function as the limit
  -- For now, we'll use a constructive approach via the contraction mapping
  
  -- We need to show there exists a v_star that is both optimal and the limit
  -- This follows from the Banach fixed point theorem applied to the Bellman operator
  
  -- The key insight: since T is a contraction, the sequence T^n(0) converges
  -- to the unique fixed point, which must be the optimal value function
  
  sorry -- This requires the full Banach fixed point theorem development

-- Helper lemma for bounding listMax (moved here to fix scoping)
lemma listMax_le_of_forall_le {l : List ℚ} {b : ℚ} (hb : 0 ≤ b) (h : ∀ x ∈ l, x ≤ b) : listMax l ≤ b := by
  induction l with
  | nil => unfold listMax; exact hb
  | cons x xs ih => 
    unfold listMax
    cases xs with
    | nil => exact h x (by simp)
    | cons y ys => 
      apply max_le
      · exact h x (by simp)
      · apply ih
        intros z hz
        exact h z (by simp [hz])

-- Supremum norm is non-negative (moved here for ordering)
lemma supNorm_nonneg {S A : Type} (mdp : MDP S A) (v : ValueFunction S) : 0 ≤ supNorm mdp v := by
  -- supNorm is the maximum of absolute values, which are all non-negative
  unfold supNorm
  -- Simple proof: listMax of non-negative numbers is non-negative
  -- We use a general property that we need to establish
  sorry -- Need: if all elements of list are ≥ 0, then listMax ≥ 0

-- Key insight: bound Q-value differences (moved here for ordering)
lemma qvalue_bound {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ) (v₁ v₂ : ValueFunction S) 
    (s : S) (hs : s ∈ mdp.states) (a : A) (ha : a ∈ mdp.actions) :
    abs ((mdp.R s a + γ * (mdp.states.map (fun s' => mdp.P s a s' * v₁ s')).sum) -
         (mdp.R s a + γ * (mdp.states.map (fun s' => mdp.P s a s' * v₂ s')).sum)) ≤ 
    γ * supNorm mdp (vDiff v₁ v₂) := by
  simp only [add_sub_add_left_eq_sub]
  rw [← mul_sub, abs_mul, abs_of_nonneg hγ]
  sorry -- Complex proof involving list manipulation lemmas

-- Helper lemma: |max f - max g| ≤ max |f - g| (simplified for compilation)
lemma listMax_abs_diff_le {l : List α} (f g : α → ℚ) :
    abs (listMax (l.map f) - listMax (l.map g)) ≤ listMax (l.map (fun a => abs (f a - g a))) := by
  sorry -- Technical but standard property of maximum functions

-- Contraction proof for individual states (moved here for ordering)
theorem bellmanContractionPointwise {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) (v₁ v₂ : ValueFunction S) :
    ∀ s ∈ mdp.states, abs (bellmanOperator mdp γ v₁ s - bellmanOperator mdp γ v₂ s) ≤ 
    γ * supNorm mdp (vDiff v₁ v₂) := by
  intro s hs
  unfold bellmanOperator
  apply le_trans (listMax_abs_diff_le _ _)
  apply listMax_le_of_forall_le (mul_nonneg hγ.1 (supNorm_nonneg mdp (vDiff v₁ v₂)))
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, h_eq⟩ := hx
  rw [← h_eq]
  exact qvalue_bound mdp γ hγ.1 v₁ v₂ s hs a ha

-- Contraction property of Bellman operator (main result)
theorem bellmanContraction {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) (v₁ v₂ : ValueFunction S) :
    supNorm mdp (vDiff (bellmanOperator mdp γ v₁) (bellmanOperator mdp γ v₂)) ≤ 
    γ * supNorm mdp (vDiff v₁ v₂) := by
  -- Use the pointwise contraction result and the definition of supNorm
  unfold supNorm vDiff
  -- Show that all elements in the list are bounded by γ * supNorm
  apply listMax_le_of_forall_le (mul_nonneg hγ.1 (supNorm_nonneg mdp (vDiff v₁ v₂)))
  intro x hx
  -- x is of the form |T(v₁)(s) - T(v₂)(s)| for some state s
  obtain ⟨s, hs, h_eq⟩ := List.mem_map.mp hx
  rw [← h_eq]
  -- Apply the pointwise contraction result
  exact bellmanContractionPointwise mdp γ hγ v₁ v₂ s hs

-- DUPLICATE REMOVED: supNorm_nonneg and le_listMax_of_mem already defined above

-- Helper lemma for max difference
lemma abs_listMax_sub_le (b : ℚ) {l₁ l₂ : List ℚ} (h : l₁.length = l₂.length) 
    (hl : ∀ i, ∀ hi : i < l₁.length, abs (l₁.get ⟨i, hi⟩ - l₂.get ⟨i, h ▸ hi⟩) ≤ b) :
    abs (listMax l₁ - listMax l₂) ≤ b := by
  sorry  -- This is complex, let's focus on the main theorem

-- DUPLICATE REMOVED: listMax_abs_diff_le already defined above

-- Key lemma: |max(as) - max(bs)| ≤ max(|as - bs|) for lists
lemma listMax_abs_sub_le {l₁ l₂ : List ℚ} (h : l₁.length = l₂.length) :
    abs (listMax l₁ - listMax l₂) ≤ 
    listMax (List.zipWith (fun a b => abs (a - b)) l₁ l₂) := by
  sorry

-- Triangle inequality for list sums
lemma list_triangle_inequality (l : List ℚ) :
    abs l.sum ≤ (l.map abs).sum := by
  have h1 : l.sum = (l : Multiset ℚ).sum := by rfl
  have h2 : (l.map abs).sum = ((l.map abs) : Multiset ℚ).sum := by rfl
  rw [h1, h2]
  have h3 : ((l.map abs) : Multiset ℚ) = (l : Multiset ℚ).map abs := by
    simp only [Multiset.map_coe]
  rw [h3]
  exact Multiset.abs_sum_le_sum_abs

-- Lemma: sum difference equals difference of sums
lemma list_sum_sub_eq (l : List ℚ) (f g : ℚ → ℚ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    abel

-- Triangle inequality for weighted sums
lemma weighted_sum_abs_le {S : Type} (states : List S) (P : S → ℚ) (f : S → ℚ) 
    (hP : ∀ s ∈ states, 0 ≤ P s) :
    abs ((states.map (fun s => P s * f s)).sum) ≤ 
    (states.map (fun s => P s * abs (f s))).sum := by
  -- Use triangle inequality
  apply le_trans (list_triangle_inequality _)
  -- Show that |P * f| = P * |f| for each element
  simp only [List.map_map]
  apply List.sum_le_sum
  intro x hx
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg (hP x hx)]

-- DUPLICATE REMOVED: qvalue_bound already defined above

-- DUPLICATE REMOVED: bellmanContractionPointwise already defined above

-- Uniqueness of optimal value function
theorem uniqueOptimalValue {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) :
    ∀ v₁ v₂, isOptimalValueFunction mdp γ v₁ → 
             isOptimalValueFunction mdp γ v₂ → 
             ∀ s ∈ mdp.states, v₁ s = v₂ s := by
  intro v₁ v₂ h₁ h₂ s hs
  -- If both v₁ and v₂ are optimal, then:
  -- v₁ = T(v₁) and v₂ = T(v₂) by definition of optimal value function
  -- So v₁ - v₂ = T(v₁) - T(v₂)
  -- By the contraction property: ||T(v₁) - T(v₂)||∞ ≤ γ · ||v₁ - v₂||∞
  -- This gives ||v₁ - v₂||∞ ≤ γ · ||v₁ - v₂||∞
  -- Since γ < 1, this implies ||v₁ - v₂||∞ = 0
  -- Therefore v₁ = v₂ pointwise
  
  -- Apply the optimal value function property
  have eq₁ : v₁ s = bellmanOperator mdp γ v₁ s := h₁ s hs
  have eq₂ : v₂ s = bellmanOperator mdp γ v₂ s := h₂ s hs
  
  -- Use contraction property
  have contract := bellmanContraction mdp γ hγ v₁ v₂
  
  -- The key insight: since v₁ = T(v₁) and v₂ = T(v₂),
  -- we have supNorm(v₁ - v₂) = supNorm(T(v₁) - T(v₂)) ≤ γ · supNorm(v₁ - v₂)
  -- Since γ < 1, this forces supNorm(v₁ - v₂) = 0
  
  sorry -- Technical: need to show that supNorm = 0 implies pointwise equality

-- Error bound for finite iterations
theorem valueIterationError {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) (n : Nat) :
    ∃ v_star, isOptimalValueFunction mdp γ v_star ∧ 
    supNorm mdp (vDiff (valueIteration mdp γ n) v_star) ≤ 
    (γ ^ n) / (1 - γ) * supNorm mdp (vDiff (valueIteration mdp γ 1) (valueIteration mdp γ 0)) := by
  sorry

-- Explicit convergence rate
theorem convergenceRate {S A : Type} (mdp : MDP S A) (γ : ℚ) (hγ : 0 ≤ γ ∧ γ < 1) :
    ∀ n : Nat, supNorm mdp (vDiff (valueIteration mdp γ (n + 1)) (valueIteration mdp γ n)) ≤
    γ^n * supNorm mdp (vDiff (valueIteration mdp γ 1) (valueIteration mdp γ 0)) := by
  sorry

-- Example: Simple 2-state, 2-action MDP
section Example

inductive ExampleState : Type where
  | s1 : ExampleState
  | s2 : ExampleState
  deriving DecidableEq

inductive ExampleAction : Type where  
  | a1 : ExampleAction
  | a2 : ExampleAction
  deriving DecidableEq

-- Define a simple MDP
def simpleMDP : MDP ExampleState ExampleAction where
  states := [ExampleState.s1, ExampleState.s2]
  actions := [ExampleAction.a1, ExampleAction.a2]
  states_nonempty := by simp
  actions_nonempty := by simp
  -- Transition probabilities
  P := fun s a s' => match s, a, s' with
    | ExampleState.s1, ExampleAction.a1, ExampleState.s1 => 7/10
    | ExampleState.s1, ExampleAction.a1, ExampleState.s2 => 3/10
    | ExampleState.s1, ExampleAction.a2, ExampleState.s1 => 2/10
    | ExampleState.s1, ExampleAction.a2, ExampleState.s2 => 8/10
    | ExampleState.s2, ExampleAction.a1, ExampleState.s1 => 4/10
    | ExampleState.s2, ExampleAction.a1, ExampleState.s2 => 6/10
    | ExampleState.s2, ExampleAction.a2, ExampleState.s1 => 9/10
    | ExampleState.s2, ExampleAction.a2, ExampleState.s2 => 1/10
  -- Rewards
  R := fun s a => match s, a with
    | ExampleState.s1, ExampleAction.a1 => 5
    | ExampleState.s1, ExampleAction.a2 => 10
    | ExampleState.s2, ExampleAction.a1 => -1
    | ExampleState.s2, ExampleAction.a2 => 2
  -- Proof that probabilities are non-negative
  P_nonneg := by
    intro s a s'
    cases s <;> cases a <;> cases s' <;> norm_num
  -- Proof that probabilities sum to 1
  P_sum_one := by
    intro s hs a ha
    cases s <;> cases a <;> simp [List.sum_cons, List.sum_nil, List.map] <;> norm_num

-- Run value iteration for 10 steps with discount factor 0.9
def v10 := valueIteration simpleMDP (9/10) 10

-- Evaluate the value function at state s1
-- #eval v10 ExampleState.s1

-- Evaluate the value function at state s2  
-- #eval v10 ExampleState.s2

-- Run value iteration with convergence check
def vConverged := valueIterationWithConvergence simpleMDP (9/10) (1/100) 100

-- #eval vConverged.1 ExampleState.s1  -- Value at s1
-- #eval vConverged.1 ExampleState.s2  -- Value at s2
-- #eval vConverged.2           -- Number of iterations taken

end Example