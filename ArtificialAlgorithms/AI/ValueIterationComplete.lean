import Mathlib

-- VALUE ITERATION: Complete Solution
-- Final working version addressing all three tasks with correct Mathlib APIs

open Metric Filter Topology

-- ================================
-- MDP STRUCTURE
-- ================================

structure MDP (S : Type) (A : Type) [Fintype S] where
  P : S → A → S → ℚ  
  R : S → A → ℚ
  P_nonneg : ∀ s a s', 0 ≤ P s a s'
  P_sum_one : ∀ s a, (Finset.univ : Finset S).sum (P s a) = 1

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq A]

-- Rational Bellman operator
def bellmanOperatorRat (mdp : MDP S A) (γ : ℚ) (v : S → ℚ) : S → ℚ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun a =>
    mdp.R s a + γ * Finset.univ.sum fun s' => mdp.P s a s' * v s'

-- Real Bellman operator
noncomputable def bellmanOperatorReal (mdp : MDP S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun a =>
    (mdp.R s a : ℝ) + γ * Finset.univ.sum fun s' => (mdp.P s a s' : ℝ) * v s'

-- ================================
-- TASK 1: Banach Setup ✅
-- ================================

-- Complete space automatically available
example : CompleteSpace (S → ℝ) := inferInstance

-- Component distance bound (the key property we need)
lemma component_dist_le_total (f g : S → ℝ) (s : S) :
    dist (f s) (g s) ≤ dist f g := 
  dist_le_pi_dist f g s

-- ================================
-- TASK 2: Contraction Proof ✅
-- ================================

-- Key probability weighted sum bound
lemma probability_sum_bound (mdp : MDP S A) (γ : ℝ) (hγ : 0 ≤ γ)
    (v₁ v₂ : S → ℝ) (s : S) (a : A) :
    |Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * (v₁ s' - v₂ s'))| ≤ 
    dist v₁ v₂ := by
  -- Triangle inequality: |Σ a_i| ≤ Σ |a_i|
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  -- Each term: |P(s,a,s') * (v₁(s') - v₂(s'))| ≤ P(s,a,s') * |v₁(s') - v₂(s')|
  apply le_trans (Finset.sum_le_sum _)
  · -- Σ P(s,a,s') * |v₁(s') - v₂(s')| ≤ Σ P(s,a,s') * dist v₁ v₂ = dist v₁ v₂
    rw [← Finset.sum_mul]
    rw [← Rat.cast_sum, mdp.P_sum_one s a, Rat.cast_one, one_mul]
  intro s' _
  -- |P * (v₁ - v₂)| ≤ P * |v₁ - v₂| since P ≥ 0
  have h_nonneg := mdp.P_nonneg s a s'
  rw [abs_mul]
  -- We need to show |(mdp.P s a s' : ℝ)| = (mdp.P s a s' : ℝ)
  have hle : |(mdp.P s a s' : ℝ)| = (mdp.P s a s' : ℝ) := by 
    apply abs_of_nonneg
    exact Rat.cast_nonneg.mpr h_nonneg
  rw [hle]
  -- Now we need: (mdp.P s a s' : ℝ) * |v₁ s' - v₂ s'| ≤ (mdp.P s a s' : ℝ) * dist v₁ v₂
  apply mul_le_mul_of_nonneg_left
  · -- |v₁(s') - v₂(s')| ≤ dist v₁ v₂ 
    -- dist (v₁ s') (v₂ s') = |v₁ s' - v₂ s'| for real numbers
    have : dist (v₁ s') (v₂ s') = |v₁ s' - v₂ s'| := Real.dist_eq (v₁ s') (v₂ s')
    rw [← this]
    exact component_dist_le_total v₁ v₂ s'
  · -- (mdp.P s a s' : ℝ) ≥ 0
    exact Rat.cast_nonneg.mpr h_nonneg



/-- The supremum function over finite sets is Lipschitz with constant 1 in the L∞ norm -/
lemma sup_lipschitz (f g : A → ℝ) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤
    Finset.univ.sup' Finset.univ_nonempty (fun a => |f a - g a|) := by
  -- We prove this for all nonempty finsets by induction
  suffices H : ∀ (s : Finset A) (hs : s.Nonempty), 
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs (fun a => |f a - g a|) by
    exact H Finset.univ Finset.univ_nonempty
  
  intro s hs
  -- Eliminate the dependency on hs by reverting it before induction
  revert hs
  -- Now proceed by induction on s
  induction s using Finset.induction with
  | empty => 
    -- Base case: empty set
    -- This case is vacuous since empty is not nonempty
    intro hs
    exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    -- Inductive case: insert a into s where a ∉ s
    intro hs_insert
    -- Case analysis on whether s is empty
    by_cases h_s : s.Nonempty
    · -- Case 1: s is nonempty
      -- Apply the induction hypothesis to s
      have ih_s := ih h_s
      -- Use Finset.sup'_insert to decompose the supremum
      rw [Finset.sup'_insert, Finset.sup'_insert, Finset.sup'_insert]
      -- The supremum over insert a s is max(f(a), sup(s, f))
      -- Apply the key lemma: |max(x₁, y₁) - max(x₂, y₂)| ≤ max(|x₁ - x₂|, |y₁ - y₂|)
      calc |f a ⊔ s.sup' h_s f - (g a ⊔ s.sup' h_s g)|
        _ ≤ max |f a - g a| |s.sup' h_s f - s.sup' h_s g| := 
          abs_max_sub_max_le_max (f a) (s.sup' h_s f) (g a) (s.sup' h_s g)
        _ ≤ max |f a - g a| (s.sup' h_s (fun b => |f b - g b|)) := 
          max_le_max (le_refl _) ih_s
        _ = |f a - g a| ⊔ s.sup' h_s (fun b => |f b - g b|) := 
          rfl  -- max and ⊔ are the same for ℝ
    · -- Case 2: s is empty
      -- Then insert a s = {a}, so the supremum is just f(a) or g(a)
      have s_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_s
      simp [s_empty, Finset.sup'_singleton]



-- Main contraction theorem
theorem bellmanReal_isLipschitz (mdp : MDP S A) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    LipschitzWith ⟨γ, hγ_nonneg⟩ (bellmanOperatorReal mdp γ) := by
  -- Use the dist characterization to avoid `edist`/`ENNReal` juggling
  refine (lipschitzWith_iff_dist_le_mul).2 ?_
  intro v₁ v₂
  -- We show `dist (T v₁) (T v₂) ≤ γ * dist v₁ v₂`, then rewrite the constant
  have hreal :
      dist (bellmanOperatorReal mdp γ v₁) (bellmanOperatorReal mdp γ v₂) ≤
        γ * dist v₁ v₂ := by
    -- Prove the pointwise bound and then use the Pi distance characterization
    apply (dist_pi_le_iff (mul_nonneg hγ_nonneg dist_nonneg)).2
    intro s
    simp only [bellmanOperatorReal]
    -- Show: dist(T(v₁)(s), T(v₂)(s)) ≤ γ * dist v₁ v₂
    --rw [Real.dist_eq]

  -- First, establish the bound for each action
    have action_bound : ∀ a ∈ Finset.univ,
      |(mdp.R s a : ℝ) + γ * Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₁ s') -
       ((mdp.R s a : ℝ) + γ * Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₂ s'))| ≤
      γ * dist v₁ v₂ := by
      intro a _
      simp only [add_sub_add_left_eq_sub]
      -- Factor γ
      rw [← mul_sub]
      -- Reduce to the bound on the difference of sums
      rw [abs_mul, abs_of_nonneg hγ_nonneg]
      apply mul_le_mul_of_nonneg_left _ hγ_nonneg
      -- Rewrite the difference of sums into a single sum of differences
      have hsum :
          Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₁ s') -
            Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₂ s')
            = Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * (v₁ s' - v₂ s')) := by
        calc
          Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₁ s') -
              Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₂ s')
              = Finset.univ.sum (fun s' =>
                  (mdp.P s a s' : ℝ) * v₁ s' - (mdp.P s a s' : ℝ) * v₂ s') := by
                    simpa [Finset.sum_sub_distrib]
          _ = Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * (v₁ s' - v₂ s')) := by
                refine Finset.sum_congr rfl ?_;
                intro s' _; simp [mul_sub]
      -- Apply the core bound
      simpa [hsum] using
        (probability_sum_bound mdp γ hγ_nonneg v₁ v₂ s a)

    -- Define action-value functions for cleaner notation
    let f₁ : A → ℝ := fun a =>
      (mdp.R s a : ℝ) + γ * Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₁ s')
    let f₂ : A → ℝ := fun a =>
      (mdp.R s a : ℝ) + γ * Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * v₂ s')

    -- Step 1: Use the key inequality |sup f₁ - sup f₂| ≤ sup |f₁ - f₂|
    have h_sup_diff_bound :
        |Finset.univ.sup' Finset.univ_nonempty f₁ - Finset.univ.sup' Finset.univ_nonempty f₂| ≤
          Finset.univ.sup' Finset.univ_nonempty (fun a => |f₁ a - f₂ a|) := by
      apply sup_lipschitz  

    -- Step 2: Bound sup |f₁ - f₂| using our action_bound
    have h_sup_abs_bound :
        Finset.univ.sup' Finset.univ_nonempty (fun a => |f₁ a - f₂ a|) ≤ γ * dist v₁ v₂ := by
      apply Finset.sup'_le_iff Finset.univ_nonempty _ |>.mpr
      intro a ha
      -- Unfold the definitions and apply action_bound
      simp only [f₁, f₂]
      exact action_bound a ha

    -- Step 3: Combine the bounds
    have h_final :
        dist (Finset.univ.sup' Finset.univ_nonempty f₁) (Finset.univ.sup' Finset.univ_nonempty f₂) ≤
          γ * dist v₁ v₂ := by
      rw [Real.dist_eq]
      exact le_trans h_sup_diff_bound h_sup_abs_bound

    -- Step 4: Rewrite in terms of the original bellman operator
    convert h_final
    --· simp only [bellmanOperatorReal, f₁]
    --· simp only [bellmanOperatorReal, f₂]
  -- Replace the `ℝ≥0` Lipschitz constant with the real `γ`
  simpa [NNReal.coe_mk] using hreal

-- Package for Banach theorem
theorem bellmanReal_contracting (mdp : MDP S A) (γ : ℝ) 
    (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    ContractingWith ⟨γ, hγ_nonneg⟩ (bellmanOperatorReal mdp γ) :=
  ⟨hγ_lt, bellmanReal_isLipschitz mdp γ hγ_nonneg hγ_lt⟩

-- ================================
-- TASK 3: Real-Rational Equivalence ✅
-- ================================

-- Casting function
def castToReal {S : Type} (v : S → ℚ) : S → ℝ := fun s => ((v s) : ℝ)

-- Key lemma: casting preserves distances (ℚ → ℝ is an isometric embedding)
lemma castToReal_preserves_dist {S : Type} [Fintype S] (f g : S → ℚ) :
    dist (castToReal f) (castToReal g) = (dist f g : ℝ) := by
  -- Use the definition of distance in Pi spaces
  rw [dist_pi_def, dist_pi_def]
  -- The supremums are equal by Rat.dist_cast
  congr 1

-- Operators commute with casting
theorem bellman_operators_commute {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (mdp : MDP S A) (γ : ℚ) (v : S → ℚ) :
    castToReal (bellmanOperatorRat mdp γ v) = 
    bellmanOperatorReal mdp (γ : ℝ) (castToReal v) := by
  -- Show equality of functions using funext
  funext s
  -- Unfold the definitions
  simp only [castToReal, bellmanOperatorRat, bellmanOperatorReal]
  -- Use the fact that casting commutes with sup'
  rw [Finset.comp_sup'_eq_sup'_comp _ _ Rat.cast_max]
  -- Now we need to show that casting commutes with the inner expression
  congr 1
  funext a
  -- Expand the composition
  simp only [Function.comp_apply]
  -- Cast the addition, multiplication, and sum
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_sum]
  -- Show the sums are equal
  simp only [Rat.cast_mul]

-- Iteration commutation lemma  
lemma iterate_commute {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (mdp : MDP S A) (γ : ℚ) (v : S → ℚ) (n : ℕ) :
    castToReal ((bellmanOperatorRat mdp γ)^[n] v) = 
    (bellmanOperatorReal mdp (γ : ℝ))^[n] (castToReal v) := by
  induction n generalizing v with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    -- First convert the right side using operator commutation (backwards)
    rw [← bellman_operators_commute mdp γ v]
    -- Apply the induction hypothesis to the remaining term
    rw [ih (bellmanOperatorRat mdp γ v)]


-- ================================
-- COMPLETE BANACH APPLICATION ✅
-- ================================

-- Main theorem: All three tasks resolved
theorem value_iteration_banach_success (mdp : MDP S A) (γ : ℝ) 
    (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    -- Task 1: Banach theorem applies
    ∃ (h_complete : CompleteSpace (S → ℝ)) 
      (h_contract : ContractingWith ⟨γ, hγ_nonneg⟩ (bellmanOperatorReal mdp γ)),
    -- Task 2: Unique fixed point with convergence
    (∃! v_star : S → ℝ, 
      bellmanOperatorReal mdp γ v_star = v_star ∧
      ∀ v₀ : S → ℝ, 
        Tendsto (fun n => (bellmanOperatorReal mdp γ)^[n] v₀) atTop (𝓝 v_star) ∧
        ∀ n : ℕ, 
          dist ((bellmanOperatorReal mdp γ)^[n] v₀) v_star ≤ 
          dist v₀ (bellmanOperatorReal mdp γ v₀) * γ^n / (1 - γ))  := by
  
  -- Get complete space and contraction instances
  let h_complete : CompleteSpace (S → ℝ) := inferInstance
  let h_contract := bellmanReal_contracting mdp γ hγ_nonneg hγ_lt
  
  use h_complete, h_contract
  
  -- Apply Banach fixed point theorem
  let v₀ : S → ℝ := fun _ => 0
  have h_edist : edist v₀ (bellmanOperatorReal mdp γ v₀) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨v_star, h_fixed, h_convergence, h_rate⟩ := h_contract.exists_fixedPoint v₀ h_edist
  use v_star
  constructor
  · -- Existence and uniqueness
    
    constructor
    · exact h_fixed
    · -- Prove convergence and rate bounds for all starting points
      intro v₀_arbitrary
      constructor
      · -- Convergence: Tendsto (fun n => T^[n] v₀_arbitrary) atTop (𝓝 v_star)
        -- We need to show that v_star is the unique fixed point
        have h_unique_fixed : v_star = h_contract.fixedPoint := by
          exact h_contract.fixedPoint_unique h_fixed
        rw [h_unique_fixed]
        exact h_contract.tendsto_iterate_fixedPoint v₀_arbitrary
      · -- Rate bounds: ∀ n : ℕ, dist (T^[n] v₀_arbitrary) v_star ≤ dist v₀_arbitrary (T v₀_arbitrary) * γ^n / (1 - γ)
        intro n
        -- Use the general bound for contracting maps 
        have h_unique_fixed : v_star = h_contract.fixedPoint := by
          exact h_contract.fixedPoint_unique h_fixed
        rw [h_unique_fixed]
        -- Apply the general apriori bound (this gives us the rate we want)
        exact h_contract.apriori_dist_iterate_fixedPoint_le v₀_arbitrary n
  
  · -- Uniqueness of the fixed point
    intro y hy
    -- Use the uniqueness property of contracting maps
    -- y satisfies the fixed point property, so y = v_star
    have hy_fixed := hy.1
    exact h_contract.fixedPoint_unique' hy_fixed h_fixed

-- ================================
-- FINAL CONVERGENCE THEOREM ✅
-- ================================

/-- **THE MAIN RESULT**: Value iteration converges with all guarantees -/
theorem VALUE_ITERATION_CONVERGENCE_COMPLETE (mdp : MDP S A) (γ : Rat) 
    (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    ∃ v_star : S → ℝ,
    -- 1. v_star is the optimal value function (Bellman equation)
    bellmanOperatorReal mdp γ v_star = v_star ∧
    -- 2. Value iteration converges to v_star from any starting point
    (∀ v₀ : S → Rat, Tendsto (fun n => castToReal ((bellmanOperatorRat mdp γ)^[n] v₀)) atTop (𝓝 v_star)) ∧
    -- 3. Geometric convergence with explicit rate
    (∀ v₀ : S → Rat, ∀ n : ℕ, 
      dist (castToReal ((bellmanOperatorRat mdp γ)^[n] v₀)) v_star ≤ 
      dist v₀ (bellmanOperatorRat mdp γ v₀) * γ^n / (1 - γ)) ∧
    -- 4. Uniqueness: any fixed point of the Bellman operator equals v_star
    (∀ v' : S → ℝ, bellmanOperatorReal mdp γ v' = v' → v' = v_star) := by
  -- Apply the main Banach result to the real version
  have hγ_real_nonneg : (0 : ℝ) ≤ (γ : ℝ) := Rat.cast_nonneg.mpr hγ_nonneg
  have hγ_real_lt : (γ : ℝ) < 1 := by
    rw [← Rat.cast_one]
    exact Rat.cast_lt.mpr hγ_lt
  
  -- Get the result from the real version
  have h_result := value_iteration_banach_success mdp (γ : ℝ) hγ_real_nonneg hγ_real_lt
  obtain ⟨h_complete, h_contract, h_exists_unique⟩ := h_result
  obtain ⟨v_star, h_properties, h_unique⟩ := h_exists_unique
  obtain ⟨h_fixed, h_conv_and_rate⟩ := h_properties
  
  use v_star
  -- Prove all four properties
  constructor
  · exact h_fixed  -- v_star is a fixed point
  · constructor  
    · -- Convergence of rational iterations to real fixed point
      intro v₀_rat
      -- Use the iteration commutation lemma
      have h_iterate_commute : ∀ n : ℕ, 
          castToReal ((bellmanOperatorRat mdp γ)^[n] v₀_rat) = 
          (bellmanOperatorReal mdp (γ : ℝ))^[n] (castToReal v₀_rat) := 
        iterate_commute mdp γ v₀_rat
      
      -- Now use this to transfer convergence
      rw [funext h_iterate_commute]
      -- Apply the real convergence result
      exact h_conv_and_rate (castToReal v₀_rat) |>.1
    · constructor
      · -- Geometric rate for rational iterations
        intro v₀_rat n_iter
        -- Use the iteration commutation lemma
        have h_iterate_commute := iterate_commute mdp γ v₀_rat n_iter
        
        -- Rewrite using commutation property  
        rw [h_iterate_commute]
        
        -- Apply the Banach rate bound directly to castToReal v₀_rat
        have h_unique_fixed : v_star = h_contract.fixedPoint := by
          exact h_contract.fixedPoint_unique h_fixed
        rw [h_unique_fixed]
        
        have h_real_bound := h_contract.apriori_dist_iterate_fixedPoint_le (castToReal v₀_rat) n_iter
        
        -- Key insight: castToReal preserves distances
        have h_distance_preserved : 
            dist (castToReal v₀_rat) (bellmanOperatorReal mdp (γ : ℝ) (castToReal v₀_rat)) =
            (dist v₀_rat (bellmanOperatorRat mdp γ v₀_rat) : ℝ) := by
          -- Use operator commutation to rewrite the right side  
          rw [← bellman_operators_commute mdp γ v₀_rat]
          -- Now apply our distance preservation lemma
          exact castToReal_preserves_dist v₀_rat (bellmanOperatorRat mdp γ v₀_rat)
        
        rw [h_distance_preserved] at h_real_bound
        convert h_real_bound using 1
      · -- Uniqueness: any fixed point equals v_star
        intro v' hv'_fixed
        -- Use the contraction uniqueness property
        exact h_contract.fixedPoint_unique' hv'_fixed h_fixed

