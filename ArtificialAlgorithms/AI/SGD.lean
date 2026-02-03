import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import ArtificialAlgorithms.AI.RobbinsSiegmund

set_option maxHeartbeats 0

open MeasureTheory ProbabilityTheory Filter Topology BigOperators QLS.Stoch
open scoped RealInnerProductSpace

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Stochastic Algorithm recursion defined in Eq (2.5):
X_{n+1} = X_n - γ_{n+1} h(X_n) + γ_{n+1}(ΔM_{n+1} + R_{n+1}) -/
def StochasticAlgorithm (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM R : ℕ → Ω → E) : Prop :=
  ∀ n ω, X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • (ΔM (n + 1) ω + R (n + 1) ω)

/-- Assumptions for Theorem 2.3.6.
Encapsulates H1 (Drift), H2 (Perturbations), and step size conditions. -/
structure SGD_Convergence_Assumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM R : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E) -- explicit gradient function
    (ℱ : Filtration ℕ m0) : Prop where

  -- Step Size Conditions (Eq 2.6)
  gamma_pos : ∀ n, 0 < γ n
  gamma_sum_inf : ¬ Summable γ  -- ∑ γ_n = +∞
  gamma_sq_sum_fin : Summable (fun n => (γ n) ^ 2)  -- ∑ γ_n² < +∞
  gamma_le_one : ∀ n, γ n ≤ 1  -- Standard in Robbins-Monro; ensures drift bounds hold

  -- Regularity of V (C² L-smooth / sub-quadratic)
  V_smooth : ContDiff ℝ 2 V
  V_grad_eq : ∀ x, gradient V x = gradV x
  V_grad_lipschitz : ∃ L : ℝ, 0 < L ∧ ∀ x y, ‖gradV x - gradV y‖ ≤ L * ‖x - y‖

  -- (H1) Drift Assumptions
  V_lower_bound : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ V x
  V_coercive : Tendsto V (cocompact E) atTop
  drift_nonneg : ∀ x, 0 ≤ @inner ℝ _ _ (gradV x) (h x)
  growth_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖h x‖^2 + ‖gradV x‖^2 ≤ C * (1 + V x)

  -- Regularity of drift direction (standard in stochastic optimization)
  -- Required for measurability of U' = γ * ⟨∇V, h⟩ composed with the process X
  h_continuous : Continuous h

  -- (H2) Perturbations
  -- (i) ΔM is a martingale difference sequence with conditional variance bound
  martingale_diff_adapted : Adapted ℱ ΔM
  martingale_diff_condexp : ∀ n, μ[ΔM (n + 1)|ℱ n] =ᵐ[μ] 0
  martingale_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (1 + V (X n ω))
  -- L² integrability of ΔM (required for conditional variance bound to be meaningful)
  martingale_diff_L2 : ∀ n, Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ

  -- (ii) R is predictable with conditional variance bound
  remainder_adapted : Adapted ℱ R
  remainder_condvar_bound : ∃ C : ℝ, 0 < C ∧ ∀ n,
    μ[fun ω => ‖R (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun ω => C * (γ (n + 1))^2 * (1 + V (X n ω))
  -- L² integrability of R (required for conditional variance bound to be meaningful)
  remainder_L2 : ∀ n, Integrable (fun ω => ‖R (n + 1) ω‖^2) μ

  -- Process adaptedness (implicit in standard probability theory but explicit here)
  -- X_n is F_n-measurable for all n
  X_adapted : Adapted ℱ X

  -- Initial condition has finite expected energy (standard assumption in stochastic analysis)
  -- Without this, V(X_0) can be non-integrable even on a probability space
  V_X0_integrable : Integrable (fun ω => V (X 0 ω)) μ

/-- Theorem 2.3.6: Convergence of the Stochastic Gradient Method.

Under assumptions (H1) and (H2), one has:
(a) sup_{n≥0} E[V(X_n)] < +∞
(b) ∑_{n≥0} γ_{n+1}⟨∇V, h⟩(X_n) < +∞ a.s.
(c) V(X_n) → V_∞ ∈ L¹ a.s.
(d) X_n - X_{n-1} → 0 a.s. and in L²

The proof applies the Robbins-Siegmund theorem after deriving:
E[V(X_{n+1}) | F_n] ≤ V(X_n)(1 + C γ_{n+1}²) - γ_{n+1}⟨∇V(X_n), h(X_n)⟩ -/
/-
SANITY CHECK PASSED: The theorem statement is mathematically plausible.
The mapping to robbinsSiegmund_full is:
  - RS `V` ↦ SGD `V ∘ X`
  - RS `U` ↦ SGD drift term `γ * ⟨gradV, h⟩`
  - RS `α` ↦ SGD `C * γ²`
  - RS `β` ↦ `0`
-/
theorem convergence_stochastic_gradient_method
    (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM R : ℕ → Ω → E) (V : E → ℝ) (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (proc : StochasticAlgorithm X γ h ΔM R)
    (asm : SGD_Convergence_Assumptions μ X γ h ΔM R V gradV ℱ) :
    -- (a) sup E[V(X_n)] < +∞
    (BddAbove (Set.range fun n => ∫ ω, V (X n ω) ∂μ)) ∧
    -- (b) ∑ γ_{n+1}⟨∇V, h⟩(X_n) < +∞ a.s.
    (∀ᵐ ω ∂μ, Summable (fun n => γ (n + 1) * @inner ℝ _ _ (gradV (X n ω)) (h (X n ω)))) ∧
    -- (c) V(X_n) → V_∞ ∈ L¹ a.s.
    (∃ V_inf : Ω → ℝ, Integrable V_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => V (X n ω)) atTop (nhds (V_inf ω))) ∧
    -- (d) X_{n+1} - X_n → 0 a.s. and in L²
    (∀ᵐ ω ∂μ, Tendsto (fun n => X (n + 1) ω - X n ω) atTop (nhds 0)) ∧
    (Tendsto (fun n => ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ) atTop (nhds 0)) := by
  /-
  Proof Strategy:
  1. Define RS parameters: V' = V ∘ X, α' = C * γ², β' = 0, U' = drift term
  2. Verify RS hypotheses (adaptedness, predictability, nonnegativity, integrability, bounds)
  3. The key step is proving the drift inequality via Taylor expansion
  4. Apply robbinsSiegmund_full to get (a), (b), (c)
  5. Prove (d) separately using increment bounds and bounded expectations
  -/

  -- Extract constants from assumptions
  obtain ⟨m, hm_pos, hV_lower⟩ := asm.V_lower_bound
  obtain ⟨L, hL_pos, hgrad_lip⟩ := asm.V_grad_lipschitz
  obtain ⟨C_growth, hC_growth_pos, h_growth⟩ := asm.growth_bound
  obtain ⟨C_mart, hC_mart_pos, h_mart_var⟩ := asm.martingale_condvar_bound
  obtain ⟨C_rem, hC_rem_pos, h_rem_var⟩ := asm.remainder_condvar_bound

  -- The drift constant combines Lipschitz constant and variance bounds.
  -- From the Taylor expansion and triangle inequality:
  --   E[‖ΔX‖² | F_t] ≤ 3γ²(‖h‖² + E[‖ΔM‖²] + E[‖R‖²]) ≤ 3γ²(C_growth + C_mart + C_rem)(1+V)
  -- The second-order term: (L/2)E[‖ΔX‖²] ≤ (3L/2)(C_growth + C_mart + C_rem)γ²(1+V)
  -- The remainder inner product: |E[⟨∇V, R⟩]| ≤ √(C_growth·C_rem)·γ(1+V) contributes O(γ²(1+V))
  -- Since V ≥ m > 0, we have (1 + V) ≤ (1 + 1/m) * V.
  -- The factor (1 + L) ensures the bound holds for all L > 0.
  -- The factor 4 provides margin to absorb all contributions.
  let C_drift := 4 * (1 + L) * (L + C_growth + C_mart + C_rem) * (1 + 1 / m)

  -- Define Robbins-Siegmund parameters
  -- V' t ω = V(X_t(ω)) : the Lyapunov function evaluated at the state
  let V' : ℕ → Ω → ℝ := fun n ω => V (X n ω)

  -- α' t ω = C * γ_t² : the multiplicative perturbation (constant in ω)
  let α' : ℕ → Ω → ℝ := fun n _ => C_drift * (γ n) ^ 2

  -- β' t ω = 0 : no additive perturbation term
  let β' : ℕ → Ω → ℝ := fun _ _ => 0

  -- U' t ω = γ_t * ⟨∇V(X_{t-1}), h(X_{t-1})⟩ : the drift term
  -- Note: U'_0 = 0, and U'_{n+1} corresponds to the drift at step n
  let U' : ℕ → Ω → ℝ := fun n ω =>
    if n = 0 then 0
    else γ n * @inner ℝ _ _ (gradV (X (n - 1) ω)) (h (X (n - 1) ω))

  -- =====================================================
  -- SUBTASK 1: Prove V' = V ∘ X is adapted to ℱ
  -- Strategy: V is continuous (from V_smooth), X is adapted (from X_adapted)
  -- Use Continuous.comp_stronglyMeasurable
  -- =====================================================
  have V'_adapted : Adapted ℱ V' := by
    -- SANITY CHECK PASSED
    -- V' n ω = V (X n ω), so V' n = V ∘ (X n)
    -- Since V is C² it's continuous, and X n is F_n-measurable by X_adapted
    -- Composition of continuous with strongly measurable is strongly measurable
    intro n
    exact asm.V_smooth.continuous.comp_stronglyMeasurable (asm.X_adapted n)

  -- =====================================================
  -- SUBTASK 2: Prove V' = V ∘ X is integrable for all n
  -- Requires: V continuous, X measurable with moment bounds
  --
  -- SANITY CHECK PASSED (after adding V_X0_integrable assumption)
  -- The original statement was FALSE without assuming E[V(X_0)] < ∞.
  -- Counterexample: X_0(ω) = 1/ω on (0,1] gives E[V(X_0)] = ∞.
  -- Resolution: Added V_X0_integrable to SGD_Convergence_Assumptions.
  -- =====================================================
  /-
  **Informal Proof of V'_integrable:**

  We prove by induction that E[V(X_n)] < ∞ for all n.

  **Base case (n = 0):**
  By assumption V_X0_integrable: E[V(X_0)] < ∞.

  **Inductive step (n → n+1):**
  Assume E[V(X_n)] < ∞. We show E[V(X_{n+1})] < ∞.

  From Taylor's theorem (L-smoothness of V):
    V(X_{n+1}) ≤ V(X_n) + ⟨∇V(X_n), ΔX⟩ + (L/2)‖ΔX‖²

  where ΔX = X_{n+1} - X_n = γ_{n+1}·(-h(X_n) + ΔM_{n+1} + R_{n+1}).

  Taking expectations:
    E[V(X_{n+1})] ≤ E[V(X_n)] + E[⟨∇V(X_n), ΔX⟩] + (L/2)·E[‖ΔX‖²]

  For the inner product term:
  - E[⟨∇V(X_n), -γh(X_n)⟩] = -γ·E[⟨∇V, h⟩(X_n)] ≤ 0 (by drift_nonneg)
  - E[⟨∇V(X_n), γΔM_{n+1}⟩] = γ·E[E[⟨∇V(X_n), ΔM_{n+1}⟩|F_n]] = 0 (martingale)
  - E[|⟨∇V(X_n), γR_{n+1}⟩|] ≤ γ·E[‖∇V(X_n)‖·‖R_{n+1}‖]
    ≤ γ·√(E[‖∇V‖²]·E[‖R‖²]) (Cauchy-Schwarz)
    ≤ C·γ²·(1 + E[V(X_n)]) (using growth_bound and remainder_condvar_bound)

  For the second-order term:
    E[‖ΔX‖²] = γ²·E[‖-h + ΔM + R‖²] ≤ 3γ²·E[‖h‖² + ‖ΔM‖² + ‖R‖²]
             ≤ 3γ²·(C_growth + C_mart + C_rem·γ²)·(1 + E[V(X_n)])

  Combining: E[V(X_{n+1})] ≤ (1 + C'·γ_{n+1}²)·E[V(X_n)] + C''·γ_{n+1}²

  Since ∑ γ_n² < ∞, the product ∏(1 + C'γ_k²) is bounded.
  By a discrete Gronwall argument: sup_n E[V(X_n)] < ∞.

  In particular, E[V(X_n)] < ∞ for all n, so V(X_n) is integrable.

  **Key Mathlib lemmas:**
  - Integrable.add, Integrable.const_mul for combining integrable functions
  - measure_theory.integral_mono for comparing integrals
  - Nat.rec_on or induction for the inductive structure
  -/
  have V'_integrable : ∀ n, Integrable (V' n) μ := by
    -- SUB 2.1: Base case - V(X_0) integrable from assumption
    have base_case : Integrable (V' 0) μ := asm.V_X0_integrable
    -- SUB 2.2: Prove the recurrence bound E[V(X_{n+1})] ≤ (1+Cγ²)E[V(X_n)] + C'γ²
    -- This follows from the Taylor bound and variance bounds
    -- We prove integrability by induction.
    -- The key is that from V(X_n) integrable + Taylor bound + noise variance bounds,
    -- we get V(X_{n+1}) bounded by an integrable function.
    intro n
    induction n with
    | zero => exact base_case
    | succ n ih =>
      -- ih : Integrable (V' n) μ, i.e., E[|V(X_n)|] < ∞
      -- Need: Integrable (V' (n+1)) μ, i.e., E[|V(X_{n+1})|] < ∞
      --
      -- Strategy: V(X_{n+1}) is measurable (continuous V composed with adapted X).
      -- We construct an integrable bound using Taylor expansion + variance bounds,
      -- then apply Integrable.mono'.

      -- Step 1: V(X_{n+1}) is AEStronglyMeasurable w.r.t. m0
      have hX_sm : StronglyMeasurable (X (n + 1)) :=
        (asm.X_adapted (n + 1)).mono (ℱ.le (n + 1))
      have hV'_meas : AEStronglyMeasurable (V' (n + 1)) μ :=
        (asm.V_smooth.continuous.comp_stronglyMeasurable hX_sm).aestronglyMeasurable

      -- Step 2: Establish auxiliary integrability facts from ih
      -- From ih, V(X_n) is integrable. Since V >= m > 0, we have 1 + V(X_n) integrable.
      have one_plus_V_int : Integrable (fun ω => 1 + V (X n ω)) μ := by
        apply Integrable.add
        · exact integrable_const 1
        · exact ih

      -- Step 3: From growth_bound, h(X_n) and gradV(X_n) have controlled L² norms
      -- ‖h(X_n)‖² + ‖gradV(X_n)‖² ≤ C_growth * (1 + V(X_n))
      -- This means h(X_n) and gradV(X_n) are L²

      -- Step 4: ΔM_{n+1} and R_{n+1} are L² by assumption
      have hDeltaM_L2 : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
      have hR_L2 : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n

      -- Step 5: The Taylor bound gives
      --   V(X_{n+1}) ≤ V(X_n) + ⟨∇V(X_n), X_{n+1} - X_n⟩ + (L/2)‖X_{n+1} - X_n‖²
      -- Each term on the RHS is integrable (by ih, L² bounds, etc.)
      -- Since V >= m > 0, |V(X_{n+1})| = V(X_{n+1}) ≤ RHS, which is integrable.

      -- For now, we use a high-level argument: the bound exists and is integrable.
      -- The detailed calculation follows the informal proof in the comments.

      -- Construct a bound function g such that |V(X_{n+1})| ≤ g a.e. and g is integrable
      -- g = V(X_n) + C * (1 + V(X_n)) + ‖ΔM‖² + ‖R‖²   (schematically)

      -- Simplified proof: use the fact that Taylor expansion gives a finite bound
      -- The key insight is that V(X_{n+1}) can be bounded by a sum of:
      -- (1) V(X_n) - integrable by ih
      -- (2) |⟨∇V(X_n), stuff⟩| - integrable by Cauchy-Schwarz + L² bounds
      -- (3) ‖stuff‖² terms - integrable by L² bounds

      -- Define the bound (simplified: V(X_n) + constants + noise terms)
      -- The constant C_bound combines the Taylor expansion coefficient and growth bound
      -- Constants need to cover:
      -- - (1+V) term: (1 + 3L/2*γ²) * C_growth ≤ (1 + 3L/2) * C_growth  (since γ² ≤ 1)
      -- - noise term: (1/2 + 3L/2) * γ² ≤ (1/2 + 3L/2) * γ²
      let C_bound := (1 + 3 * L / 2) * C_growth
      let C_noise := (1 / 2 + 3 * L / 2) * (γ (n + 1))^2
      let bound : Ω → ℝ := fun ω =>
        V (X n ω) + C_bound * (1 + V (X n ω))
        + C_noise * (‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)

      -- The bound is integrable as sum of integrable functions
      have hbound_int : Integrable bound μ := by
        apply Integrable.add
        apply Integrable.add
        · exact ih
        · exact one_plus_V_int.const_mul _
        · exact (hDeltaM_L2.add hR_L2).const_mul _

      -- The pointwise bound follows from Taylor expansion
      -- V(X_{n+1}) ≤ V(X_n) - γ⟨∇V, h⟩ + γ⟨∇V, ΔM + R⟩ + (L/2)‖ΔX‖²
      -- Using drift_nonneg: -γ⟨∇V, h⟩ ≤ 0
      -- Using ‖ΔX‖² ≤ 3γ²(‖h‖² + ‖ΔM‖² + ‖R‖²)
      -- Using growth_bound: ‖h‖² ≤ C_growth(1 + V) and |⟨∇V, stuff⟩| bounded by similar
      -- Total: V(X_{n+1}) ≤ bound

      apply Integrable.mono' hbound_int hV'_meas
      -- Need: ∀ᵐ ω ∂μ, ‖V' (n + 1) ω‖ ≤ bound ω
      -- i.e., |V(X_{n+1})| ≤ bound
      -- Since V ≥ m > 0, |V| = V, and V(X_{n+1}) ≤ bound follows from Taylor
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (lt_of_lt_of_le hm_pos (hV_lower _)))]
      -- Need: V (X (n + 1) ω) ≤ bound ω
      -- This follows from the Taylor bound + nonnegativity of drift term

      -- Step A: Apply L-smooth descent lemma (Taylor bound)
      -- V(y) ≤ V(x) + ⟨∇V(x), y - x⟩ + (L/2)‖y - x‖²
      -- This will be proven later (taylor_bound) but we need it here for integrability.
      -- We prove a weaker version inline.

      -- Let x = X n ω, y = X (n+1) ω
      let x := X n ω
      let y := X (n + 1) ω

      -- From process update: y - x = γ * (-h(x) + ΔM + R)
      have hupdate : y - x = (γ (n + 1)) • (-h x + ΔM (n + 1) ω + R (n + 1) ω) := by
        simp only [y, x]
        have hp := proc n ω
        -- X_{n+1} = X_n - γ h(X_n) + γ (ΔM + R)
        -- So X_{n+1} - X_n = -γ h + γ(ΔM + R) = γ(-h + ΔM + R)
        simp only [hp, smul_add, smul_neg, neg_add_eq_sub]
        -- Goal: X n ω - γ • h(X n) + γ • (ΔM + R) - X n ω = γ • (-h + ΔM + R)
        -- LHS = -γ • h + γ • ΔM + γ • R = γ • (-h + ΔM + R)
        module

      -- Descent lemma for L-smooth V (from V_smooth and V_grad_lipschitz)
      have descent : V y ≤ V x + @inner ℝ _ _ (gradV x) (y - x) + (L/2) * ‖y - x‖^2 := by
        -- Use convexity + Lipschitz gradient bound
        -- For L-smooth functions: V(y) ≤ V(x) + ⟨∇V(x), y-x⟩ + (L/2)‖y-x‖²
        -- Define the line function g(t) = V(x + t·(y - x))
        let g : ℝ → ℝ := fun t => V (x + t • (y - x))
        -- g is differentiable with g'(t) = ⟨∇V(x + t(y-x)), y-x⟩
        have g_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
            (@inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)) t := by
          intro t _
          have hp_deriv : HasDerivAt (fun s => x + s • (y - x)) (y - x) t := by
            have h1 : HasDerivAt (fun s => s • (y - x)) ((1 : ℝ) • (y - x)) t :=
              (hasDerivAt_id t).smul_const (y - x)
            simp only [one_smul] at h1
            exact h1.const_add x
          have hV_diff : Differentiable ℝ V := asm.V_smooth.differentiable (by decide)
          have hV_grad_at : HasGradientAt V (gradV (x + t • (y - x))) (x + t • (y - x)) := by
            have := (hV_diff (x + t • (y - x))).hasGradientAt
            rw [asm.V_grad_eq] at this
            exact this
          have hV_fderiv := hV_grad_at.hasFDerivAt
          have hcomp := hV_fderiv.comp_hasDerivAt t hp_deriv
          simp only [InnerProductSpace.toDual_apply] at hcomp
          exact hcomp
        -- Apply FTC: g(1) - g(0) = ∫₀¹ g'(t) dt
        have ftc : V y - V x = ∫ t in (0 : ℝ)..(1 : ℝ),
            @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) := by
          let g' : ℝ → ℝ := fun t => @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)
          have hg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
            intro t ht
            have : t ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.uIcc, Set.Icc] at ht ⊢; exact ht
            exact g_deriv t this
          have hint : IntervalIntegrable g' MeasureTheory.volume 0 1 := by
            apply Continuous.intervalIntegrable
            have hgradV_cont : Continuous gradV := by
              have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
              have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
                intro p; rw [← asm.V_grad_eq p, gradient]
              have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
              rw [this]
              exact (LinearIsometryEquiv.continuous _).comp h
            apply continuous_inner.comp₂ _ continuous_const
            exact hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))
          have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv hint
          have hg1 : g 1 = V y := by simp [g]
          have hg0 : g 0 = V x := by simp [g]
          rw [hg1, hg0] at h_ftc
          exact h_ftc.symm
        -- Split the integral
        have split_integral : ∫ t in (0 : ℝ)..(1 : ℝ),
            @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) =
            @inner ℝ _ _ (gradV x) (y - x) +
            ∫ t in (0 : ℝ)..(1 : ℝ),
              @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
          have h_split : ∀ t : ℝ, @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) =
              @inner ℝ _ _ (gradV x) (y - x) + @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
            intro t
            rw [← inner_add_left, add_sub_cancel]
          have h_eq : (fun t : ℝ => @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)) =
              (fun t : ℝ => @inner ℝ _ _ (gradV x) (y - x) + @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)) := by
            funext t; exact h_split t
          rw [h_eq]
          rw [intervalIntegral.integral_add]
          · simp only [intervalIntegral.integral_const, sub_zero, one_smul]
          · exact intervalIntegrable_const
          · apply Continuous.intervalIntegrable
            have hgradV_cont : Continuous gradV := by
              have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
              have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
                intro p; rw [← asm.V_grad_eq p, gradient]
              have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
              rw [this]
              exact (LinearIsometryEquiv.continuous _).comp h
            apply continuous_inner.comp₂ _ continuous_const
            exact (hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
        -- Bound the error integral using Lipschitz of gradV
        have error_bound : ∫ t in (0 : ℝ)..(1 : ℝ),
            @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) ≤
            (L / 2) * ‖y - x‖^2 := by
          have hbound : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
              @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) ≤ L * t * ‖y - x‖^2 := by
            intro t ⟨ht0, _⟩
            have hCS := norm_inner_le_norm (𝕜 := ℝ) (gradV (x + t • (y - x)) - gradV x) (y - x)
            have hLip : ‖gradV (x + t • (y - x)) - gradV x‖ ≤ L * ‖t • (y - x)‖ := by
              have := hgrad_lip (x + t • (y - x)) x
              simp only [add_sub_cancel_left] at this
              exact this
            have hnorm_smul : ‖t • (y - x)‖ = t * ‖y - x‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
            calc @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)
                ≤ |@inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)| := le_abs_self _
              _ ≤ ‖gradV (x + t • (y - x)) - gradV x‖ * ‖y - x‖ := by
                  rw [Real.norm_eq_abs] at hCS; exact hCS
              _ ≤ L * ‖t • (y - x)‖ * ‖y - x‖ := by nlinarith [norm_nonneg (gradV (x + t • (y - x)) - gradV x),
                                                               norm_nonneg (y - x), hLip]
              _ = L * (t * ‖y - x‖) * ‖y - x‖ := by rw [hnorm_smul]
              _ = L * t * ‖y - x‖^2 := by ring
          have hint : IntervalIntegrable (fun t => @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x))
              MeasureTheory.volume 0 1 := by
            apply Continuous.intervalIntegrable
            have hgradV_cont : Continuous gradV := by
              have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
              have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
                intro p; rw [← asm.V_grad_eq p, gradient]
              have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
              rw [this]
              exact (LinearIsometryEquiv.continuous _).comp h
            apply continuous_inner.comp₂ _ continuous_const
            exact (hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
          have hint2 : IntervalIntegrable (fun t => L * t * ‖y - x‖^2) MeasureTheory.volume 0 1 := by
            apply Continuous.intervalIntegrable; continuity
          calc ∫ t in (0 : ℝ)..(1 : ℝ), @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)
              ≤ ∫ t in (0 : ℝ)..(1 : ℝ), L * t * ‖y - x‖^2 := by
                apply intervalIntegral.integral_mono_on (by norm_num) hint hint2
                intro t ht
                exact hbound t ht
            _ = L * ‖y - x‖^2 * ∫ t in (0 : ℝ)..(1 : ℝ), t := by
                rw [← intervalIntegral.integral_const_mul]
                congr 1; funext t; ring
            _ = L * ‖y - x‖^2 * (1 / 2) := by
                congr 1
                rw [integral_id, one_pow, zero_pow (by norm_num : 2 ≠ 0)]
                ring
            _ = (L / 2) * ‖y - x‖^2 := by ring
        -- Combine: V(y) - V(x) ≤ ⟨∇V(x), y-x⟩ + (L/2)·‖y-x‖²
        calc V y = V x + (V y - V x) := by ring
          _ = V x + ∫ t in (0 : ℝ)..(1 : ℝ),
                @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) := by rw [ftc]
          _ = V x + @inner ℝ _ _ (gradV x) (y - x) +
                ∫ t in (0 : ℝ)..(1 : ℝ),
                  @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
              rw [split_integral]; ring
          _ ≤ V x + @inner ℝ _ _ (gradV x) (y - x) + (L / 2) * ‖y - x‖^2 := by
              have h := error_bound
              linarith

      -- The drift term is non-positive by assumption
      have drift_neg : -@inner ℝ _ _ (gradV x) (h x) ≤ 0 := by
        have := asm.drift_nonneg x
        linarith

      -- Full calculation for V(y) ≤ bound is technical.
      -- Key steps:
      -- 1. From descent: V(y) ≤ V(x) + ⟨∇V(x), y-x⟩ + (L/2)‖y-x‖²
      -- 2. Expand ⟨∇V(x), y-x⟩ = γ⟨∇V, -h + ΔM + R⟩ = -γ⟨∇V, h⟩ + γ⟨∇V, ΔM + R⟩
      -- 3. The drift term -γ⟨∇V, h⟩ ≤ 0 by drift_nonneg
      -- 4. Bound |⟨∇V, ΔM + R⟩| using Cauchy-Schwarz and growth bounds
      -- 5. Bound ‖y-x‖² ≤ 3γ²(‖h‖² + ‖ΔM‖² + ‖R‖²)
      -- 6. Use growth_bound to bound ‖h‖² ≤ C_growth(1 + V(x))
      -- 7. Combine to get V(y) ≤ V(x) + C_bound*(1 + V(x)) + C_noise*(‖ΔM‖² + ‖R‖²) = bound

      calc V y ≤ V x + @inner ℝ _ _ (gradV x) (y - x) + (L/2) * ‖y - x‖^2 := descent
        _ ≤ bound ω := by
          simp only [bound, x, y]
          -- Need to show:
          -- V(X_n) + ⟨∇V, y-x⟩ + (L/2)‖y-x‖² ≤ V(X_n) + C_bound*(1+V) + C_noise*(‖ΔM‖²+‖R‖²)
          -- i.e., ⟨∇V, y-x⟩ + (L/2)‖y-x‖² ≤ C_bound*(1+V) + C_noise*(‖ΔM‖²+‖R‖²)

          -- Expand using hupdate: y - x = γ • (-h + ΔM + R)
          -- ⟨∇V, y-x⟩ = γ⟨∇V, -h + ΔM + R⟩ = -γ⟨∇V, h⟩ + γ⟨∇V, ΔM⟩ + γ⟨∇V, R⟩

          -- The drift term -γ⟨∇V, h⟩ ≤ 0
          -- The noise terms |γ⟨∇V, ΔM + R⟩| ≤ γ‖∇V‖(‖ΔM‖ + ‖R‖)
          --   ≤ γ√(C_growth(1+V)) * (‖ΔM‖ + ‖R‖)  [by growth_bound]
          --   ≤ γ * (C_growth(1+V)/2 + (‖ΔM‖ + ‖R‖)²/2)  [by AM-GM: ab ≤ a²/2 + b²/2]
          --   ≤ C_growth * γ² * (1+V) + γ² * (‖ΔM‖² + ‖R‖²)  [simplified]

          -- The quadratic term: ‖y-x‖² = γ²‖-h + ΔM + R‖² ≤ 3γ²(‖h‖² + ‖ΔM‖² + ‖R‖²)
          --   ≤ 3γ² * (C_growth(1+V) + ‖ΔM‖² + ‖R‖²)  [by growth_bound for h]
          -- So (L/2)‖y-x‖² ≤ (3L/2)γ² * (C_growth(1+V) + ‖ΔM‖² + ‖R‖²)

          -- Total: ⟨∇V, y-x⟩ + (L/2)‖y-x‖²
          --   ≤ C_bound * (1+V) + C_noise * (‖ΔM‖² + ‖R‖²)

          -- Step 1: It suffices to show the inner product and quadratic terms are bounded
          suffices hsuff : @inner ℝ _ _ (gradV (X n ω)) (X (n + 1) ω - X n ω) +
                           L / 2 * ‖X (n + 1) ω - X n ω‖ ^ 2 ≤
                           C_bound * (1 + V (X n ω)) +
                           C_noise * (‖ΔM (n + 1) ω‖ ^ 2 + ‖R (n + 1) ω‖ ^ 2) by linarith

          -- Abbreviations for readability
          set gam := γ (n + 1) with hgam_def
          set DM := ΔM (n + 1) ω with hDM_def
          set Rem := R (n + 1) ω with hRem_def
          set gV := gradV (X n ω) with hgV_def
          set hx := h (X n ω) with hhx_def

          -- Step 2: Rewrite using hupdate
          have h_diff : X (n + 1) ω - X n ω = gam • (-hx + DM + Rem) := hupdate
          rw [h_diff]

          -- Step 3: Expand inner product with scalar mult
          rw [inner_smul_right]

          -- Step 4: Split inner product
          have inner_split : @inner ℝ _ _ gV (-hx + DM + Rem) =
              -@inner ℝ _ _ gV hx + @inner ℝ _ _ gV DM + @inner ℝ _ _ gV Rem := by
            rw [inner_add_right, inner_add_right, inner_neg_right]
          rw [inner_split]

          -- Step 5: Bound norm squared
          have norm_sq_smul : ‖gam • (-hx + DM + Rem)‖ ^ 2 = gam^2 * ‖-hx + DM + Rem‖ ^ 2 := by
            rw [norm_smul, mul_pow]
            simp only [Real.norm_eq_abs, sq_abs]
          rw [norm_sq_smul]

          -- Positivity and key bounds
          have hgam_pos : 0 < gam := asm.gamma_pos (n + 1)
          have hgam_nonneg : 0 ≤ gam := le_of_lt hgam_pos
          have hgam_le_one : gam ≤ 1 := asm.gamma_le_one (n + 1)
          have hgam_sq_le : gam^2 ≤ gam := by nlinarith
          have hL_pos' : 0 < L := hL_pos
          have hC_pos : 0 < C_growth := hC_growth_pos
          have hV_nonneg : 0 ≤ V (X n ω) := le_of_lt (lt_of_lt_of_le hm_pos (hV_lower _))
          have h1V_pos : 0 < 1 + V (X n ω) := by linarith

          -- Growth bound
          have growth : ‖hx‖ ^ 2 + ‖gV‖ ^ 2 ≤ C_growth * (1 + V (X n ω)) := h_growth (X n ω)
          have h_norm_bound : ‖hx‖ ^ 2 ≤ C_growth * (1 + V (X n ω)) := by nlinarith [sq_nonneg ‖gV‖]
          have gV_norm_bound : ‖gV‖ ^ 2 ≤ C_growth * (1 + V (X n ω)) := by nlinarith [sq_nonneg ‖hx‖]

          -- Cauchy-Schwarz bounds
          have cs_DM : |@inner ℝ _ _ gV DM| ≤ ‖gV‖ * ‖DM‖ := abs_real_inner_le_norm _ _
          have cs_Rem : |@inner ℝ _ _ gV Rem| ≤ ‖gV‖ * ‖Rem‖ := abs_real_inner_le_norm _ _

          -- Norm triangle inequality bound: ‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)
          have norm_sq_three : ‖-hx + DM + Rem‖ ^ 2 ≤ 3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2) := by
            have h1 : ‖-hx + DM + Rem‖ ≤ ‖-hx‖ + ‖DM‖ + ‖Rem‖ := by
              calc ‖-hx + DM + Rem‖ ≤ ‖-hx + DM‖ + ‖Rem‖ := norm_add_le _ _
                _ ≤ ‖-hx‖ + ‖DM‖ + ‖Rem‖ := by nlinarith [norm_add_le (-hx) DM]
            have h2 : ‖-hx‖ = ‖hx‖ := norm_neg _
            have h3 : (‖hx‖ + ‖DM‖ + ‖Rem‖)^2 ≤ 3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2) := by
              nlinarith [sq_nonneg (‖hx‖ - ‖DM‖), sq_nonneg (‖DM‖ - ‖Rem‖),
                         sq_nonneg (‖hx‖ - ‖Rem‖), sq_nonneg ‖hx‖, sq_nonneg ‖DM‖, sq_nonneg ‖Rem‖]
            calc ‖-hx + DM + Rem‖ ^ 2 ≤ (‖-hx‖ + ‖DM‖ + ‖Rem‖)^2 := by
                  nlinarith [norm_nonneg (-hx + DM + Rem), norm_nonneg (-hx),
                             norm_nonneg DM, norm_nonneg Rem, h1]
              _ = (‖hx‖ + ‖DM‖ + ‖Rem‖)^2 := by rw [h2]
              _ ≤ 3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2) := h3

          -- Drift is nonnegative (inner product ⟨∇V, h⟩ ≥ 0)
          have hdrift_nonneg : 0 ≤ @inner ℝ _ _ gV hx := asm.drift_nonneg (X n ω)

          -- Parametric AM-GM: γ·a·b ≤ a²/2 + γ²·b²/2
          -- Proof: γab = √γ·a · √γ·b ≤ (γa² + γb²)/2 ... wait, that's wrong.
          -- Actually: γab ≤ a²/(2ε) + ε·γ²·b²/2 for ε = 1/γ gives γab ≤ γa²/2 + γb²/2
          -- For ε = 1: γab ≤ a²/2 + γ²b²/2 when γ ≤ 1.
          -- Proof: γab ≤ (a² + b²)/2 · max(γ, γ) = γ(a² + b²)/2 when γ ≤ 1.
          -- That's not quite right either. Let me think again.
          -- We want: γ · ‖gV‖ · ‖DM‖ ≤ ‖gV‖²/2 + γ² · ‖DM‖²/2
          -- i.e., 2γ · ‖gV‖ · ‖DM‖ ≤ ‖gV‖² + γ² · ‖DM‖²
          -- i.e., (‖gV‖ - γ·‖DM‖)² ≥ 0 ✓
          have param_amgm : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
              gam * a * b ≤ a^2 / 2 + gam^2 * b^2 / 2 := by
            intros a b _ _
            have h := sq_nonneg (a - gam * b)
            nlinarith

          -- Main bound calculation using parametric AM-GM
          calc gam * (-@inner ℝ _ _ gV hx + @inner ℝ _ _ gV DM + @inner ℝ _ _ gV Rem) +
               L / 2 * (gam ^ 2 * ‖-hx + DM + Rem‖ ^ 2)
            -- Drop the negative drift term (using -inner ≤ 0)
            ≤ gam * (@inner ℝ _ _ gV DM + @inner ℝ _ _ gV Rem) +
               L / 2 * (gam ^ 2 * ‖-hx + DM + Rem‖ ^ 2) := by nlinarith
            -- Bound inner products by Cauchy-Schwarz
            _ ≤ gam * (‖gV‖ * ‖DM‖ + ‖gV‖ * ‖Rem‖) +
               L / 2 * (gam ^ 2 * ‖-hx + DM + Rem‖ ^ 2) := by
                 have h1 : @inner ℝ _ _ gV DM ≤ |@inner ℝ _ _ gV DM| := le_abs_self _
                 have h2 : @inner ℝ _ _ gV Rem ≤ |@inner ℝ _ _ gV Rem| := le_abs_self _
                 nlinarith [cs_DM, cs_Rem]
            -- Use parametric AM-GM: γab ≤ a²/2 + γ²b²/2
            _ ≤ (‖gV‖^2/2 + gam^2 * ‖DM‖^2/2) + (‖gV‖^2/2 + gam^2 * ‖Rem‖^2/2) +
               L / 2 * (gam ^ 2 * (3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2))) := by
                 have ham1 := param_amgm ‖gV‖ ‖DM‖ (norm_nonneg _) (norm_nonneg _)
                 have ham2 := param_amgm ‖gV‖ ‖Rem‖ (norm_nonneg _) (norm_nonneg _)
                 have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
                 have hgam_sq_nonneg : 0 ≤ gam^2 := sq_nonneg _
                 -- The inner product bound: gam * (‖gV‖*‖DM‖ + ‖gV‖*‖Rem‖) ≤ ‖gV‖² + gam²*(‖DM‖² + ‖Rem‖²)/2
                 have inner_bound : gam * (‖gV‖ * ‖DM‖ + ‖gV‖ * ‖Rem‖) ≤
                     ‖gV‖^2/2 + gam^2 * ‖DM‖^2/2 + (‖gV‖^2/2 + gam^2 * ‖Rem‖^2/2) := by
                   calc gam * (‖gV‖ * ‖DM‖ + ‖gV‖ * ‖Rem‖)
                     = gam * ‖gV‖ * ‖DM‖ + gam * ‖gV‖ * ‖Rem‖ := by ring
                     _ ≤ (‖gV‖^2/2 + gam^2 * ‖DM‖^2/2) + (‖gV‖^2/2 + gam^2 * ‖Rem‖^2/2) := by
                         linarith [ham1, ham2]
                 -- The norm squared bound
                 have norm_bound : L / 2 * (gam ^ 2 * ‖-hx + DM + Rem‖ ^ 2) ≤
                     L / 2 * (gam ^ 2 * (3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2))) := by
                   have hn3 := norm_sq_three
                   have hgam_sq_nonneg : 0 ≤ gam^2 := sq_nonneg _
                   have h1 : gam^2 * ‖-hx + DM + Rem‖ ^ 2 ≤ gam^2 * (3 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2)) :=
                     mul_le_mul_of_nonneg_left hn3 hgam_sq_nonneg
                   have hL_half_nonneg : 0 ≤ L / 2 := by linarith
                   exact mul_le_mul_of_nonneg_left h1 hL_half_nonneg
                 linarith [inner_bound, norm_bound]
            -- Simplify and apply growth bounds
            _ = ‖gV‖^2 + gam^2 * (‖DM‖^2 + ‖Rem‖^2) / 2 +
               (3 * L / 2) * gam ^ 2 * (‖hx‖^2 + ‖DM‖^2 + ‖Rem‖^2) := by ring
            -- Apply growth bound for ‖gV‖² and ‖hx‖²
            _ ≤ C_growth * (1 + V (X n ω)) + gam^2 * (‖DM‖^2 + ‖Rem‖^2) / 2 +
               (3 * L / 2) * gam ^ 2 * (C_growth * (1 + V (X n ω)) + ‖DM‖^2 + ‖Rem‖^2) := by
                  -- First bound: ‖gV‖² ≤ C_growth * (1 + V)
                  have step1 : ‖gV‖^2 ≤ C_growth * (1 + V (X n ω)) := gV_norm_bound
                  -- Second bound: ‖hx‖² ≤ C_growth * (1 + V)
                  have step2 : ‖hx‖^2 ≤ C_growth * (1 + V (X n ω)) := h_norm_bound
                  -- The quadratic term: (3L/2) * γ² * (‖hx‖² + noise)
                  have coef_nonneg : 0 ≤ (3 * L / 2) * gam ^ 2 := by positivity
                  have hx_term : (3 * L / 2) * gam ^ 2 * ‖hx‖^2 ≤
                      (3 * L / 2) * gam ^ 2 * (C_growth * (1 + V (X n ω))) := by
                    exact mul_le_mul_of_nonneg_left step2 coef_nonneg
                  linarith [step1, hx_term, sq_nonneg ‖DM‖, sq_nonneg ‖Rem‖, sq_nonneg gam]
            -- Collect and simplify
            _ = (1 + 3 * L / 2 * gam^2) * C_growth * (1 + V (X n ω)) +
                (1/2 + 3 * L / 2) * gam^2 * (‖DM‖^2 + ‖Rem‖^2) := by ring
            -- Now apply the constant bounds
            -- C_bound = (1 + 3L/2) * C_growth, so (1 + 3L/2*γ²) * C_growth ≤ C_bound since γ² ≤ 1
            -- C_noise = (1/2 + 3L/2) * γ², so the noise term is exact
            _ ≤ C_bound * (1 + V (X n ω)) + C_noise * (‖DM‖ ^ 2 + ‖Rem‖ ^ 2) := by
                  simp only [C_bound, C_noise]
                  -- Need: (1 + 3L/2*γ²)*C_growth*(1+V) + (1/2+3L/2)*γ²*noise
                  --     ≤ (1+3L/2)*C_growth*(1+V) + (1/2+3L/2)*γ²*noise
                  -- The noise terms are equal.
                  -- For the (1+V) term: (1 + 3L/2*γ²)*C_growth ≤ (1+3L/2)*C_growth since γ² ≤ 1.
                  have hgam_sq : gam^2 ≤ 1 := by
                    have hgam_le := asm.gamma_le_one (n + 1)
                    have hgam_pos := le_of_lt (asm.gamma_pos (n + 1))
                    nlinarith [sq_nonneg gam]
                  have h_coef : 1 + 3 * L / 2 * gam^2 ≤ 1 + 3 * L / 2 := by
                    have hL_nn : 0 ≤ L := le_of_lt hL_pos
                    nlinarith [hgam_sq, sq_nonneg gam]
                  have hV_nn : 0 ≤ V (X n ω) := le_of_lt (lt_of_lt_of_le hm_pos (hV_lower _))
                  have h1V_nn : 0 ≤ 1 + V (X n ω) := by linarith
                  have hCg_nn : 0 ≤ C_growth := le_of_lt hC_growth_pos
                  have h_term1 : (1 + 3 * L / 2 * gam^2) * C_growth * (1 + V (X n ω)) ≤
                                 (1 + 3 * L / 2) * C_growth * (1 + V (X n ω)) := by
                    apply mul_le_mul_of_nonneg_right _ h1V_nn
                    exact mul_le_mul_of_nonneg_right h_coef hCg_nn
                  linarith [h_term1]

  -- =====================================================
  -- SUBTASK 3: Prove α' is adapted (trivial: constant in ω)
  -- =====================================================
  have α'_adapted : Adapted ℱ α' := by
    intro n
    exact stronglyMeasurable_const

  -- =====================================================
  -- SUBTASK 4: Prove β' is adapted (trivial: zero)
  -- =====================================================
  have β'_adapted : Adapted ℱ β' := by
    intro n
    exact stronglyMeasurable_const

  -- =====================================================
  -- SUBTASK 5: Prove U' is adapted
  -- Strategy: Case split on n = 0 vs n > 0
  -- - n = 0: U' 0 = 0, constant, hence stronglyMeasurable_const
  -- - n > 0: U' n = γ n * ⟨gradV(X(n-1)), h(X(n-1))⟩
  --   - X(n-1) is F_{n-1}-measurable (by X_adapted) ⊆ F_n-measurable (filtration mono)
  --   - gradV continuous (from V_smooth: V is C², so ∇V is C¹, hence continuous)
  --   - h continuous (from h_continuous assumption)
  --   - Compositions with continuous functions preserve strong measurability
  --   - Inner product and scalar mult preserve strong measurability
  -- SANITY CHECK PASSED (after adding h_continuous assumption)
  -- Mathlib: Continuous.comp_stronglyMeasurable, StronglyMeasurable.inner, StronglyMeasurable.const_smul
  -- =====================================================
  have U'_adapted : Adapted ℱ U' := by
    intro n
    simp only [U']
    by_cases hn : n = 0
    · simp [hn]; exact stronglyMeasurable_const
    · -- n > 0: need to show γ n * ⟨gradV(X(n-1)), h(X(n-1))⟩ is F_n-measurable
      simp [hn]
      -- X(n-1) is F_{n-1}-measurable, hence F_n-measurable by filtration monotonicity
      have hX_meas : StronglyMeasurable[ℱ n] (X (n - 1)) :=
        (asm.X_adapted (n - 1)).mono (ℱ.mono (Nat.pred_le n))
      -- gradV(X(n-1)) is measurable: V smooth ⟹ gradV = gradient V is continuous
      have gradV_cont : Continuous gradV := by
        -- From V_smooth (ContDiff ℝ 2 V), we get:
        -- 1. fderiv ℝ V is continuous (ContDiff.continuous_fderiv with 1 ≤ 2)
        -- 2. gradient V = (toDual ℝ E).symm ∘ (fderiv ℝ V) (definition in Mathlib)
        -- 3. (toDual ℝ E).symm is continuous (linear isometry equiv)
        -- 4. So gradient V is continuous as composition
        -- 5. gradV = gradient V by V_grad_eq, so gradV is continuous
        -- Mathlib: ContDiff.continuous_fderiv, LinearIsometryEquiv.continuous
        exact ((LinearIsometryEquiv.continuous _).comp
          (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
      have hgradV_meas : StronglyMeasurable[ℱ n] (fun ω => gradV (X (n - 1) ω)) :=
        gradV_cont.comp_stronglyMeasurable hX_meas
      -- h(X(n-1)) is measurable by h_continuous
      have hh_meas : StronglyMeasurable[ℱ n] (fun ω => h (X (n - 1) ω)) :=
        asm.h_continuous.comp_stronglyMeasurable hX_meas
      -- Inner product of two strongly measurable functions is strongly measurable
      have hinner_meas : StronglyMeasurable[ℱ n] (fun ω => @inner ℝ _ _ (gradV (X (n - 1) ω)) (h (X (n - 1) ω))) :=
        StronglyMeasurable.inner hgradV_meas hh_meas
      -- Scalar multiplication by constant preserves strong measurability
      exact hinner_meas.const_smul (γ n)

  -- =====================================================
  -- SUBTASK 6: Prove predictability of α'_{n+1} (F_n-measurable)
  -- =====================================================
  have α'_predictable : Adapted ℱ (fun t => α' (t + 1)) := by
    intro n
    exact stronglyMeasurable_const

  -- =====================================================
  -- SUBTASK 7: Prove predictability of β'_{n+1}
  -- =====================================================
  have β'_predictable : Adapted ℱ (fun t => β' (t + 1)) := by
    intro n
    exact stronglyMeasurable_const

  -- =====================================================
  -- SUBTASK 8: Prove predictability of U'_{n+1}
  -- U'_{n+1}(ω) = γ_{n+1} * ⟨∇V(X_n(ω)), h(X_n(ω))⟩ is F_n-measurable
  -- Strategy: U'(n+1) = γ(n+1) * ⟨gradV(X n), h(X n)⟩
  --   - X n is F_n-measurable by X_adapted n (no mono needed!)
  --   - gradV continuous (from V_smooth)
  --   - h continuous (from h_continuous)
  --   - Inner product and scalar mult preserve measurability
  -- SANITY CHECK PASSED
  -- Mathlib: Continuous.comp_stronglyMeasurable, StronglyMeasurable.inner, const_smul
  -- =====================================================
  have U'_predictable : Adapted ℱ (fun t => U' (t + 1)) := by
    intro n
    simp only [U']
    -- U'(n+1): since n+1 > 0, we get γ(n+1) * ⟨gradV(X n), h(X n)⟩
    simp [Nat.succ_ne_zero n]
    -- X n is F_n-measurable directly from X_adapted (no mono needed!)
    have hX_meas : StronglyMeasurable[ℱ n] (X n) := asm.X_adapted n
    -- gradV is continuous (from V_smooth: V is C², so ∇V is C¹, hence continuous)
    have gradV_cont : Continuous gradV := by
      -- From V_smooth (ContDiff ℝ 2 V): fderiv ℝ V is continuous
      -- gradient V = (toDual ℝ E).symm ∘ (fderiv ℝ V), and toDual is continuous
      -- gradV = gradient V by V_grad_eq
      -- Mathlib: ContDiff.continuous_fderiv, LinearIsometryEquiv.continuous
      exact ((LinearIsometryEquiv.continuous _).comp
        (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
    have hgradV_meas : StronglyMeasurable[ℱ n] (fun ω => gradV (X n ω)) :=
      gradV_cont.comp_stronglyMeasurable hX_meas
    -- h(X n) is measurable by h_continuous
    have hh_meas : StronglyMeasurable[ℱ n] (fun ω => h (X n ω)) :=
      asm.h_continuous.comp_stronglyMeasurable hX_meas
    -- Inner product of two strongly measurable functions is strongly measurable
    have hinner_meas : StronglyMeasurable[ℱ n] (fun ω => @inner ℝ _ _ (gradV (X n ω)) (h (X n ω))) :=
      StronglyMeasurable.inner hgradV_meas hh_meas
    -- Scalar multiplication by constant preserves strong measurability
    exact hinner_meas.const_smul (γ (n + 1))

  -- =====================================================
  -- SUBTASK 9: Prove V' ≥ 0
  -- =====================================================
  have V'_nonneg : ∀ t ω, 0 ≤ V' t ω := by
    intro t ω
    simp only [V']
    exact le_trans (le_of_lt hm_pos) (hV_lower (X t ω))

  -- =====================================================
  -- SUBTASK 10: Prove α' ≥ 0
  -- =====================================================
  have hC_drift_nonneg : 0 ≤ C_drift := by
    simp only [C_drift]
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · have h1 : 0 ≤ L := le_of_lt hL_pos
      linarith
    · have h1 : 0 ≤ L := le_of_lt hL_pos
      have h2 : 0 ≤ C_mart := le_of_lt hC_mart_pos
      have h3 : 0 ≤ C_rem := le_of_lt hC_rem_pos
      have h4 : 0 ≤ C_growth := le_of_lt hC_growth_pos
      linarith
    · have hm_inv_nonneg : 0 ≤ 1 / m := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hm_pos)
      linarith

  have α'_nonneg : ∀ t ω, 0 ≤ α' t ω := by
    intro t ω
    simp only [α']
    apply mul_nonneg hC_drift_nonneg
    exact sq_nonneg _

  -- =====================================================
  -- SUBTASK 11: Prove β' ≥ 0 (trivial: β' = 0)
  -- =====================================================
  have β'_nonneg : ∀ t ω, 0 ≤ β' t ω := by
    intro t ω
    simp [β']

  -- =====================================================
  -- SUBTASK 12: Prove U' ≥ 0 (from drift_nonneg and gamma_pos)
  -- =====================================================
  have U'_nonneg : ∀ t ω, 0 ≤ U' t ω := by
    intro t ω
    simp only [U']
    split_ifs with ht
    · exact le_refl 0
    · apply mul_nonneg
      · exact le_of_lt (asm.gamma_pos t)
      · exact asm.drift_nonneg (X (t - 1) ω)

  -- =====================================================
  -- SUBTASK 13: Prove β' is integrable (trivial: integrable_zero)
  -- =====================================================
  have β'_integrable : ∀ t, Integrable (β' t) μ := by
    intro t
    simp only [β']
    exact integrable_const 0

  -- =====================================================
  -- SUBTASK 14: Prove U' is integrable
  --
  -- SANITY CHECK PASSED
  -- =====================================================
  /-
  ## Informal Proof of U'_integrable

  **Goal:** ∀ t, Integrable (U' t) μ

  Where U' t ω = if t = 0 then 0 else γ_t * ⟨gradV(X_{t-1}), h(X_{t-1})⟩

  **Case t = 0:**
  U' 0 = 0 (constant zero function), trivially integrable.
  Mathlib: integrable_const

  **Case t > 0:**
  U' t = γ_t * ⟨gradV(X_{t-1}), h(X_{t-1})⟩

  Step 1: Bound the inner product using Cauchy-Schwarz
    |⟨gradV(x), h(x)⟩| ≤ ‖gradV(x)‖ · ‖h(x)‖

  Step 2: Use the growth_bound assumption
    From growth_bound: ‖h(x)‖² + ‖gradV(x)‖² ≤ C · (1 + V(x))
    This implies: ‖gradV(x)‖ ≤ √(C(1+V(x))) and ‖h(x)‖ ≤ √(C(1+V(x)))
    Therefore: ‖gradV(x)‖ · ‖h(x)‖ ≤ C · (1 + V(x))
    (Using AM-GM: ab ≤ (a² + b²)/2)

  Step 3: Bound U' t
    |U' t ω| ≤ γ_t · |⟨gradV(X_{t-1}), h(X_{t-1})⟩|
             ≤ γ_t · C · (1 + V(X_{t-1} ω))

  Step 4: Conclude integrability
    Since V(X_{t-1}) is integrable (by V'_integrable (t-1)),
    and γ_t, C are finite constants,
    we have U' t is integrable.

  **Key Mathlib lemmas:**
  - abs_inner_le_norm: |⟨u, v⟩| ≤ ‖u‖ · ‖v‖ (Cauchy-Schwarz)
  - Integrable.const_mul: constant multiple preserves integrability
  - Integrable.add: sum of integrable functions is integrable
  - integrable_const: constant functions are integrable
  -/
  have U'_integrable : ∀ t, Integrable (U' t) μ := by
    intro t
    simp only [U']
    split_ifs with ht
    -- Case t = 0: U' 0 = 0, trivially integrable
    · exact integrable_const 0
    -- Case t > 0: U' t = γ_t * ⟨gradV(X_{t-1}), h(X_{t-1})⟩
    · -- SUB 14.1: Show the inner product function is integrable
      -- Use growth_bound: ‖h‖² + ‖gradV‖² ≤ C(1+V)
      -- By AM-GM: ‖gradV‖·‖h‖ ≤ (‖gradV‖² + ‖h‖²)/2 ≤ C(1+V)/2
      -- Cauchy-Schwarz: |⟨gradV, h⟩| ≤ ‖gradV‖·‖h‖ ≤ C(1+V)/2
      have inner_bound : ∀ x, |@inner ℝ _ _ (gradV x) (h x)| ≤ C_growth / 2 * (1 + V x) := by
        intro x
        have hCS := abs_real_inner_le_norm (gradV x) (h x)
        have hAM : ‖gradV x‖ * ‖h x‖ ≤ (‖gradV x‖^2 + ‖h x‖^2) / 2 := by
          have := sq_nonneg (‖gradV x‖ - ‖h x‖)
          nlinarith [sq_nonneg ‖gradV x‖, sq_nonneg ‖h x‖, sq_abs ‖gradV x‖, sq_abs ‖h x‖]
        have hgb := h_growth x
        calc |@inner ℝ _ _ (gradV x) (h x)|
            ≤ ‖gradV x‖ * ‖h x‖ := hCS
          _ ≤ (‖gradV x‖^2 + ‖h x‖^2) / 2 := hAM
          _ ≤ C_growth * (1 + V x) / 2 := by linarith
          _ = C_growth / 2 * (1 + V x) := by ring
      -- SUB 14.2: inner product composed with X_{t-1} is integrable
      have inner_integrable : Integrable (fun ω => @inner ℝ _ _ (gradV (X (t - 1) ω)) (h (X (t - 1) ω))) μ := by
        -- |inner(ω)| ≤ C/2 * (1 + V(X_{t-1}(ω)))
        -- 1 + V(X_{t-1}) is integrable since V(X_{t-1}) is integrable (V'_integrable)
        have V_int : Integrable (fun ω => V (X (t - 1) ω)) μ := V'_integrable (t - 1)
        have one_plus_V_int : Integrable (fun ω => 1 + V (X (t - 1) ω)) μ := by
          exact Integrable.add (integrable_const 1) V_int
        -- Mathlib: Integrable.of_abs_le or similar domination argument
        -- First show gradV is continuous (from V being C²)
        have gradV_cont : Continuous gradV := by
          exact ((LinearIsometryEquiv.continuous _).comp
            (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
        -- X (t-1) is strongly measurable w.r.t. m0 (use Filtration.le and StronglyMeasurable.mono)
        have hX_sm : StronglyMeasurable (X (t - 1)) :=
          (asm.X_adapted (t - 1)).mono (ℱ.le (t - 1))
        have hX_asm : AEStronglyMeasurable (X (t - 1)) μ := hX_sm.aestronglyMeasurable
        -- Compositions with continuous functions are AEStronglyMeasurable
        have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X (t - 1) ω)) μ :=
          gradV_cont.comp_aestronglyMeasurable hX_asm
        have h_X_asm : AEStronglyMeasurable (fun ω => h (X (t - 1) ω)) μ :=
          asm.h_continuous.comp_aestronglyMeasurable hX_asm
        -- Inner product of AEStronglyMeasurable functions is AEStronglyMeasurable
        have inner_asm : AEStronglyMeasurable (fun ω => @inner ℝ _ _ (gradV (X (t - 1) ω)) (h (X (t - 1) ω))) μ :=
          gradV_X_asm.inner h_X_asm
        -- Now use Integrable.mono' with the bound
        have bound_int : Integrable (fun ω => C_growth / 2 * (1 + V (X (t - 1) ω))) μ :=
          one_plus_V_int.const_mul (C_growth / 2)
        apply Integrable.mono' bound_int inner_asm
        filter_upwards with ω
        rw [Real.norm_eq_abs]
        exact inner_bound (X (t - 1) ω)
      -- SUB 14.3: Constant multiple is integrable
      exact Integrable.const_mul inner_integrable (γ t)

  -- =====================================================
  -- SUBTASK 15: Prove product bound ∏(1 + α'_k) ≤ C
  -- Uses: exp(∑ α'_k) bounds the product, and ∑ γ_k² < ∞
  --
  -- SANITY CHECK PASSED
  -- =====================================================
  /-
  ## Informal Proof of prod_bound

  We need to show: ∃ C > 0, ∀ t ω, prodY α' t ω ≤ C

  Where prodY α' t ω = ∏_{k < t} (1 + α' (k+1) ω) = ∏_{k < t} (1 + C_drift · γ_{k+1}²)

  **Step 1: Basic inequality 1 + x ≤ exp(x)**
  For all real x, we have 1 + x ≤ exp(x) (from Taylor expansion of exp).
  Since C_drift > 0 and γ_k² ≥ 0, each term C_drift · γ_k² ≥ 0.

  **Step 2: Apply to each factor**
  For each k: 1 + C_drift · γ_{k+1}² ≤ exp(C_drift · γ_{k+1}²)

  **Step 3: Product bound**
  ∏_{k < t} (1 + C_drift · γ_{k+1}²)
    ≤ ∏_{k < t} exp(C_drift · γ_{k+1}²)        [by prod_le_prod and Step 2]
    = exp(∑_{k < t} C_drift · γ_{k+1}²)        [by exp_sum]
    = exp(C_drift · ∑_{k < t} γ_{k+1}²)        [factor out C_drift]

  **Step 4: Summability bound**
  Since ∑ γ_n² converges (by gamma_sq_sum_fin), the partial sums are bounded:
  ∑_{k < t} γ_{k+1}² ≤ ∑_{n ≥ 1} γ_n² ≤ ∑_{n ≥ 0} γ_n² = ∑' n, γ_n² =: S < ∞

  **Step 5: Uniform bound**
  Therefore: prodY α' t ω ≤ exp(C_drift · S) for all t, ω.
  Choose C = exp(C_drift · S) > 0.  ∎
  -/
  have prod_bound : ∃ C : ℝ, 0 < C ∧ ∀ t ω, prodY α' t ω ≤ C := by
    -- The bound C = exp(C_drift * ∑' n, γ_n²)
    let S := ∑' n, (γ n) ^ 2
    use Real.exp (C_drift * S)
    constructor
    -- Step 5a: C > 0
    · exact Real.exp_pos _
    -- Step 5b: ∀ t ω, prodY α' t ω ≤ C
    intro t ω
    -- prodY α' t ω = ∏_{k < t} (1 + C_drift * γ_{k+1}²)
    simp only [prodY, α']
    -- Step 2-3: ∏(1 + a_k) ≤ exp(∑ a_k)
    have h_prod_le_exp : (Finset.range t).prod (fun k => 1 + C_drift * (γ (k + 1)) ^ 2)
        ≤ Real.exp ((Finset.range t).sum (fun k => C_drift * (γ (k + 1)) ^ 2)) := by
      -- SUB 15.1: Each factor: 1 + x ≤ exp(x)
      have h_factor : ∀ k ∈ Finset.range t,
          1 + C_drift * (γ (k + 1)) ^ 2 ≤ Real.exp (C_drift * (γ (k + 1)) ^ 2) := by
        intro k _
        -- Use Real.add_one_le_exp: x + 1 ≤ exp(x) for all x
        have := Real.add_one_le_exp (C_drift * (γ (k + 1)) ^ 2)
        linarith
      -- SUB 15.2: Apply Finset.prod_le_prod with exp_sum
      calc (Finset.range t).prod (fun k => 1 + C_drift * (γ (k + 1)) ^ 2)
          ≤ (Finset.range t).prod (fun k => Real.exp (C_drift * (γ (k + 1)) ^ 2)) := by
            apply Finset.prod_le_prod
            · intro k _; linarith [mul_nonneg hC_drift_nonneg (sq_nonneg (γ (k + 1)))]
            · exact h_factor
        _ = Real.exp ((Finset.range t).sum (fun k => C_drift * (γ (k + 1)) ^ 2)) := by
            rw [Real.exp_sum]
    -- Step 4: Bound partial sum by total sum
    have h_sum_bound : (Finset.range t).sum (fun k => C_drift * (γ (k + 1)) ^ 2) ≤ C_drift * S := by
      -- Rewrite sum as C_drift * (sum of γ²)
      have h_sum_factor : (Finset.range t).sum (fun k => C_drift * (γ (k + 1)) ^ 2)
          = C_drift * (Finset.range t).sum (fun k => (γ (k + 1)) ^ 2) := by
        rw [← Finset.mul_sum]
      rw [h_sum_factor]
      apply mul_le_mul_of_nonneg_left _ hC_drift_nonneg
      -- SUB 15.3: Partial sum of shifted sequence ≤ infinite sum
      -- ∑_{k<t} γ_{k+1}² ≤ ∑' n, γ_n² = S
      -- Note: The shifted partial sum is ∑_{n=1}^{t} γ_n² which is ≤ ∑_{n≥0} γ_n²
      -- Rewrite the sum to use Finset.image (· + 1) (Finset.range t)
      have h_reindex : (Finset.range t).sum (fun k => (γ (k + 1)) ^ 2)
          = (Finset.image (· + 1) (Finset.range t)).sum (fun n => (γ n) ^ 2) := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact Nat.succ_injective hxy
      rw [h_reindex]
      apply Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) asm.gamma_sq_sum_fin
    calc (Finset.range t).prod (fun k => 1 + C_drift * (γ (k + 1)) ^ 2)
        ≤ Real.exp ((Finset.range t).sum (fun k => C_drift * (γ (k + 1)) ^ 2)) := h_prod_le_exp
      _ ≤ Real.exp (C_drift * S) := by
          apply Real.exp_le_exp_of_le h_sum_bound

  -- =====================================================
  -- SUBTASK 16: Prove ∑ E[β'_t] is summable (trivial: sum of zeros)
  -- =====================================================
  have sum_Eβ : Summable (fun t => ∫ ω, β' t ω ∂μ) := by
    simp only [β']
    have h : (fun t : ℕ => ∫ _ : Ω, (0 : ℝ) ∂μ) = fun _ => 0 := by
      funext t
      simp
    rw [h]
    exact summable_zero

  -- =====================================================
  -- SUBTASK 17: THE KEY LEMMA - Derive the drift inequality
  -- E[V(X_{n+1}) | F_n] ≤ (1 + C γ_{n+1}²) V(X_n) - γ_{n+1} ⟨∇V(X_n), h(X_n)⟩
  --
  -- SANITY CHECK PASSED
  -- The drift inequality is the fundamental result for SGD convergence analysis.
  -- The proof follows from Taylor expansion + martingale properties + variance bounds.
  -- =====================================================

  /-
  ## Informal Proof of condexp_ineq

  Fix t ≥ 0. We show: E[V(X_{t+1}) | F_t] ≤ (1 + C_drift·γ²)·V(X_t) - γ·⟨∇V(X_t), h(X_t)⟩

  **Step 1: Taylor Expansion**
  Since V is C² with L-Lipschitz gradient, by Taylor's theorem:
    V(X_{t+1}) ≤ V(X_t) + ⟨∇V(X_t), ΔX⟩ + (L/2)·‖ΔX‖²
  where ΔX = X_{t+1} - X_t.

  **Step 2: Substitute Recursion**
  From the stochastic algorithm:
    ΔX = γ_{t+1}·(-h(X_t) + ΔM_{t+1} + R_{t+1})

  The linear term expands to:
    ⟨∇V(X_t), ΔX⟩ = -γ·⟨∇V, h⟩ + γ·⟨∇V, ΔM⟩ + γ·⟨∇V, R⟩

  **Step 3: Take Conditional Expectation**
  (a) Martingale term: E[⟨∇V(X_t), ΔM_{t+1}⟩ | F_t] = ⟨∇V(X_t), E[ΔM_{t+1}|F_t]⟩ = 0
      (since ∇V(X_t) is F_t-measurable and E[ΔM_{t+1}|F_t] = 0)

  (b) Second-order bound: Using (a+b+c)² ≤ 3(a²+b²+c²):
      E[‖ΔX‖² | F_t] ≤ 3γ²·(‖h(X_t)‖² + E[‖ΔM‖²|F_t] + E[‖R‖²|F_t])
                     ≤ 3γ²·(C_growth + C_mart + C_rem)·(1 + V(X_t))

  (c) Remainder term: By Cauchy-Schwarz and Jensen:
      |E[⟨∇V, R⟩|F_t]| ≤ ‖∇V(X_t)‖·√E[‖R‖²|F_t] ≤ √(C_growth·C_rem)·γ·(1+V)

  **Step 4: Combine**
  E[V(X_{t+1})|F_t] ≤ V(X_t) - γ⟨∇V, h⟩ + C'·γ²·(1+V)
  where C' = (3L/2)(C_growth + C_mart + C_rem) + √(C_growth·C_rem)

  Using (1+V) ≤ (1+1/m)·V (since V ≥ m):
  E[V(X_{t+1})|F_t] ≤ V(X_t)·(1 + C_drift·γ²) - γ⟨∇V, h⟩

  where C_drift = 4·(L + C_growth + C_mart + C_rem)·(1+1/m) ≥ C'·(1+1/m).  ∎
  -/

  have condexp_ineq : ∀ t,
      μ[fun ω => V' (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + α' (t + 1) ω) * V' t ω + β' (t + 1) ω - U' (t + 1) ω := by
    intro t

    -- Step 1: Taylor expansion bound for L-smooth V
    -- SUBTASK 17a: V(y) ≤ V(x) + ⟨∇V(x), y-x⟩ + (L/2)‖y-x‖² for L-smooth V
    -- SANITY CHECK PASSED
    /-
    **Informal Proof (Descent Lemma for L-smooth functions):**
    Let x, y ∈ E. Define g : [0,1] → ℝ by g(t) = V(x + t·(y - x)).
    Since V is C², g is C¹ with g'(t) = ⟨∇V(x + t(y-x)), y-x⟩.

    By the Fundamental Theorem of Calculus:
      V(y) - V(x) = g(1) - g(0) = ∫₀¹ g'(t) dt = ∫₀¹ ⟨∇V(x + t(y-x)), y-x⟩ dt

    Adding and subtracting ⟨∇V(x), y-x⟩:
      V(y) - V(x) = ⟨∇V(x), y-x⟩ + ∫₀¹ ⟨∇V(x + t(y-x)) - ∇V(x), y-x⟩ dt

    For the integral, use Cauchy-Schwarz and Lipschitz:
      |⟨∇V(x + t(y-x)) - ∇V(x), y-x⟩| ≤ ‖∇V(x + t(y-x)) - ∇V(x)‖ · ‖y-x‖
                                       ≤ L · ‖t(y-x)‖ · ‖y-x‖ = L · t · ‖y-x‖²

    Therefore:
      ∫₀¹ ⟨∇V(x + t(y-x)) - ∇V(x), y-x⟩ dt ≤ ∫₀¹ L·t·‖y-x‖² dt = (L/2) · ‖y-x‖²

    Hence: V(y) ≤ V(x) + ⟨∇V(x), y-x⟩ + (L/2)·‖y-x‖²  ∎
    -/
    have taylor_bound : ∀ x y : E, V y ≤ V x + @inner ℝ _ _ (gradV x) (y - x) + (L / 2) * ‖y - x‖^2 := by
      intro x y
      -- SUB 17a.1: Define the line function g(t) = V(x + t·(y - x))
      let g : ℝ → ℝ := fun t => V (x + t • (y - x))
      -- SUB 17a.2: g is differentiable with g'(t) = ⟨∇V(x + t(y-x)), y-x⟩
      have g_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
          (@inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)) t := by
        intro t _
        -- p(s) = x + s • (y - x) has derivative (y - x) at any point
        have hp_deriv : HasDerivAt (fun s => x + s • (y - x)) (y - x) t := by
          have h1 : HasDerivAt (fun s => s • (y - x)) ((1 : ℝ) • (y - x)) t :=
            (hasDerivAt_id t).smul_const (y - x)
          simp only [one_smul] at h1
          exact h1.const_add x
        -- V is differentiable everywhere since ContDiff ℝ 2
        have hV_diff : Differentiable ℝ V := asm.V_smooth.differentiable (by decide)
        -- At x + t • (y - x), V has gradient gradV (x + t • (y - x))
        have hV_grad_at : HasGradientAt V (gradV (x + t • (y - x))) (x + t • (y - x)) := by
          have := (hV_diff (x + t • (y - x))).hasGradientAt
          rw [asm.V_grad_eq] at this
          exact this
        have hV_fderiv := hV_grad_at.hasFDerivAt
        have hcomp := hV_fderiv.comp_hasDerivAt t hp_deriv
        simp only [InnerProductSpace.toDual_apply] at hcomp
        exact hcomp
      -- SUB 17a.3: Apply FTC: g(1) - g(0) = ∫₀¹ g'(t) dt
      have ftc : V y - V x = ∫ t in (0 : ℝ)..(1 : ℝ),
          @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) := by
        -- Define g'(t) = ⟨∇V(x + t•(y-x)), y-x⟩
        let g' : ℝ → ℝ := fun t => @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)
        -- g has derivative g' at all points in [0, 1]
        have hg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
          intro t ht
          have : t ∈ Set.Icc (0 : ℝ) 1 := by simp [Set.uIcc, Set.Icc] at ht ⊢; exact ht
          exact g_deriv t this
        -- g' is integrable on [0, 1]
        have hint : IntervalIntegrable g' MeasureTheory.volume 0 1 := by
          apply Continuous.intervalIntegrable
          have hgradV_cont : Continuous gradV := by
            have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
            have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
              intro p; rw [← asm.V_grad_eq p, gradient]
            have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
            rw [this]
            exact (LinearIsometryEquiv.continuous _).comp h
          apply continuous_inner.comp₂ _ continuous_const
          exact hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))
        -- Apply FTC
        have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv hint
        -- Simplify: g(1) = V(y), g(0) = V(x)
        have hg1 : g 1 = V y := by simp [g]
        have hg0 : g 0 = V x := by simp [g]
        rw [hg1, hg0] at h_ftc
        exact h_ftc.symm
      -- SUB 17a.4: Split the integral using linearity
      have split_integral : ∫ t in (0 : ℝ)..(1 : ℝ),
          @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) =
          @inner ℝ _ _ (gradV x) (y - x) +
          ∫ t in (0 : ℝ)..(1 : ℝ),
            @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
        -- The integrand splits: ⟨∇V(x + t(y-x)), y-x⟩ = ⟨∇V(x), y-x⟩ + ⟨∇V(x + t(y-x)) - ∇V(x), y-x⟩
        have h_split : ∀ t : ℝ, @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) =
            @inner ℝ _ _ (gradV x) (y - x) + @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
          intro t
          rw [← inner_add_left, add_sub_cancel]
        -- Rewrite the LHS integrand
        have h_eq : (fun t : ℝ => @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x)) =
            (fun t : ℝ => @inner ℝ _ _ (gradV x) (y - x) + @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)) := by
          funext t; exact h_split t
        rw [h_eq]
        -- ∫ (a + f(t)) dt = ∫ a dt + ∫ f(t) dt
        rw [intervalIntegral.integral_add]
        · -- ∫₀¹ ⟨∇V(x), y-x⟩ dt = ⟨∇V(x), y-x⟩ · 1
          simp only [intervalIntegral.integral_const, sub_zero, one_smul]
        · exact intervalIntegrable_const
        · -- Integrability of the difference term
          apply Continuous.intervalIntegrable
          have hgradV_cont : Continuous gradV := by
            have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
            have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
              intro p; rw [← asm.V_grad_eq p, gradient]
            have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
            rw [this]
            exact (LinearIsometryEquiv.continuous _).comp h
          apply continuous_inner.comp₂ _ continuous_const
          exact (hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
      -- SUB 17a.5: Bound the error integral using Lipschitz of gradV
      have error_bound : ∫ t in (0 : ℝ)..(1 : ℝ),
          @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) ≤
          (L / 2) * ‖y - x‖^2 := by
        -- Use |⟨u, v⟩| ≤ ‖u‖·‖v‖ and Lipschitz: ‖gradV(z) - gradV(x)‖ ≤ L·‖z-x‖
        -- For z = x + t·(y-x): ‖z - x‖ = t·‖y-x‖ (for t ≥ 0)
        -- So: |⟨gradV(z) - gradV(x), y-x⟩| ≤ L·t·‖y-x‖²
        -- Integrate: ∫₀¹ L·t·‖y-x‖² dt = (L/2)·‖y-x‖²
        have hbound : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
            @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) ≤ L * t * ‖y - x‖^2 := by
          intro t ⟨ht0, _⟩
          -- Cauchy-Schwarz: ⟨u, v⟩ ≤ |⟨u, v⟩| ≤ ‖u‖ · ‖v‖
          have hCS := norm_inner_le_norm (𝕜 := ℝ) (gradV (x + t • (y - x)) - gradV x) (y - x)
          -- Lipschitz bound: ‖gradV(x + t(y-x)) - gradV(x)‖ ≤ L · ‖t(y-x)‖
          have hLip : ‖gradV (x + t • (y - x)) - gradV x‖ ≤ L * ‖t • (y - x)‖ := by
            have := hgrad_lip (x + t • (y - x)) x
            simp only [add_sub_cancel_left] at this
            exact this
          -- ‖t • (y - x)‖ = t · ‖y - x‖ (since t ≥ 0)
          have hnorm_smul : ‖t • (y - x)‖ = t * ‖y - x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          calc @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)
              ≤ |@inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)| := le_abs_self _
            _ ≤ ‖gradV (x + t • (y - x)) - gradV x‖ * ‖y - x‖ := by
                rw [Real.norm_eq_abs] at hCS; exact hCS
            _ ≤ L * ‖t • (y - x)‖ * ‖y - x‖ := by nlinarith [norm_nonneg (gradV (x + t • (y - x)) - gradV x),
                                                             norm_nonneg (y - x), hLip]
            _ = L * (t * ‖y - x‖) * ‖y - x‖ := by rw [hnorm_smul]
            _ = L * t * ‖y - x‖^2 := by ring
        -- Integrability
        have hint : IntervalIntegrable (fun t => @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x))
            MeasureTheory.volume 0 1 := by
          apply Continuous.intervalIntegrable
          have hgradV_cont : Continuous gradV := by
            have h := asm.V_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ 2)
            have heq : ∀ p, gradV p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := by
              intro p; rw [← asm.V_grad_eq p, gradient]
            have : gradV = fun p => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ V p) := funext heq
            rw [this]
            exact (LinearIsometryEquiv.continuous _).comp h
          apply continuous_inner.comp₂ _ continuous_const
          exact (hgradV_cont.comp (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
        have hint2 : IntervalIntegrable (fun t => L * t * ‖y - x‖^2) MeasureTheory.volume 0 1 := by
          apply Continuous.intervalIntegrable; continuity
        calc ∫ t in (0 : ℝ)..(1 : ℝ), @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x)
            ≤ ∫ t in (0 : ℝ)..(1 : ℝ), L * t * ‖y - x‖^2 := by
              apply intervalIntegral.integral_mono_on (by norm_num) hint hint2
              intro t ht
              exact hbound t ht
          _ = L * ‖y - x‖^2 * ∫ t in (0 : ℝ)..(1 : ℝ), t := by
              rw [← intervalIntegral.integral_const_mul]
              congr 1; funext t; ring
          _ = L * ‖y - x‖^2 * (1 / 2) := by
              congr 1
              rw [integral_id, one_pow, zero_pow (by norm_num : 2 ≠ 0)]
              ring
          _ = (L / 2) * ‖y - x‖^2 := by ring
      -- Combine: V(y) - V(x) ≤ ⟨∇V(x), y-x⟩ + (L/2)·‖y-x‖²
      calc V y = V x + (V y - V x) := by ring
        _ = V x + ∫ t in (0 : ℝ)..(1 : ℝ),
              @inner ℝ _ _ (gradV (x + t • (y - x))) (y - x) := by rw [ftc]
        _ = V x + @inner ℝ _ _ (gradV x) (y - x) +
              ∫ t in (0 : ℝ)..(1 : ℝ),
                @inner ℝ _ _ (gradV (x + t • (y - x)) - gradV x) (y - x) := by
            rw [split_integral]; ring
        _ ≤ V x + @inner ℝ _ _ (gradV x) (y - x) + (L / 2) * ‖y - x‖^2 := by
            have h := error_bound
            linarith

    -- Step 2: Express increment using recursion
    -- SUBTASK 17f: Algebraic manipulation of StochasticAlgorithm recursion
    -- SANITY CHECK PASSED (pure algebra - no counterexample possible)
    /-
    **Informal Proof of increment_eq:**

    From StochasticAlgorithm: X_{t+1} = X_t - γ•h(X_t) + γ•(ΔM + R)
    Subtracting X_t from both sides:
      X_{t+1} - X_t = -γ•h(X_t) + γ•(ΔM + R)
                    = γ•(-h(X_t)) + γ•(ΔM + R)     [by smul_neg: -(c•x) = c•(-x)]
                    = γ•(-h(X_t) + ΔM + R)          [by smul_add: c•x + c•y = c•(x+y)]

    Key Mathlib lemmas:
    - `smul_neg : r • (-x) = -(r • x)` (equivalently: `-(r•x) = r•(-x)`)
    - `smul_add : r • (x + y) = r • x + r • y` (equivalently: inverse direction for factoring)
    -/
    have increment_eq : ∀ ω, X (t + 1) ω - X t ω =
        (γ (t + 1)) • (-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω) := by
      intro ω
      have hrec := proc t ω
      -- hrec : X (t + 1) ω = X t ω - γ • h (X t ω) + γ • (ΔM (t + 1) ω + R (t + 1) ω)
      -- Goal: X (t + 1) ω - X t ω = γ • (-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω)
      -- Strategy: substitute hrec on LHS, then use smul algebra to factor out γ
      calc X (t + 1) ω - X t ω
          = (X t ω - (γ (t + 1)) • h (X t ω) + (γ (t + 1)) • (ΔM (t + 1) ω + R (t + 1) ω)) - X t ω := by
            rw [hrec]
        _ = -(γ (t + 1)) • h (X t ω) + (γ (t + 1)) • (ΔM (t + 1) ω + R (t + 1) ω) := by
            -- Pure additive group simplification: (X - γh + γ(ΔM+R)) - X = -γh + γ(ΔM+R)
            -- Key: X + a + b - X = a + b by additive commutativity/associativity
            -- Convert (-(r • x)) to (-r) • x using neg_smul
            simp only [neg_smul]
            abel
        _ = (γ (t + 1)) • (-h (X t ω)) + (γ (t + 1)) • (ΔM (t + 1) ω + R (t + 1) ω) := by
            -- neg_smul : (-r) • x = -(r • x) = r • (-x) via smul_neg
            -- We have -γ • h on LHS, want γ • (-h) on RHS
            -- smul_neg (backwards): r • (-x) = -(r • x)
            -- neg_smul: (-r) • x = -(r • x)
            -- Combine: (-r) • x = r • (-x)
            rw [neg_smul, smul_neg]
        _ = (γ (t + 1)) • (-h (X t ω) + (ΔM (t + 1) ω + R (t + 1) ω)) := by
            -- smul_add : r • (x + y) = r • x + r • y (backwards)
            rw [← smul_add]
        _ = (γ (t + 1)) • (-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω) := by
            -- associativity of addition: -h + (ΔM + R) = -h + ΔM + R
            congr 1
            -- add_assoc: (a + b) + c = a + (b + c)
            rw [add_assoc]

    -- Step 3: Martingale cancellation
    -- SUBTASK 17b: E[⟨∇V(X_t), ΔM_{t+1}⟩ | F_t] = 0
    -- SANITY CHECK PASSED
    /-
    **Informal Proof of martingale_inner_zero:**

    Goal: E[⟨∇V(X_t), ΔM_{t+1}⟩ | F_t] = 0 a.e.

    Step 1: X_t is F_t-adapted
      By construction of StochasticAlgorithm, X_t depends only on X_0, γ_1,...,γ_t, ΔM_1,...,ΔM_t, R_1,...,R_t,
      all of which are F_t-measurable (by adaptedness of ΔM, R and the recursion).

    Step 2: ∇V(X_t) is F_t-strongly measurable
      Since X_t is F_t-measurable and gradV : E → E is continuous (from V_smooth : ContDiff ℝ 2 V),
      the composition gradV ∘ X_t is F_t-strongly measurable.

    Step 3: Inner product pullout for conditional expectation
      For u : Ω → E that is F_t-strongly measurable and v : Ω → E integrable:
        E[⟨u, v⟩ | F_t] =ᵃᵉ ⟨u, E[v | F_t]⟩
      This follows from:
      - In finite dimensions: decompose using orthonormal basis, ⟨u,v⟩ = Σᵢ uᵢvᵢ,
        apply condExp_mul_of_stronglyMeasurable_left to each component
      - In general Hilbert spaces: use that ⟨u, ·⟩ is continuous linear,
        conditional expectation commutes with bounded linear forms

    Step 4: Apply martingale property
      By assumption martingale_diff_condexp: E[ΔM_{t+1} | F_t] = 0 a.e.

    Step 5: Conclude
      E[⟨∇V(X_t), ΔM_{t+1}⟩ | F_t] = ⟨∇V(X_t), E[ΔM_{t+1} | F_t]⟩ = ⟨∇V(X_t), 0⟩ = 0
      (using inner_zero_right)  ∎
    -/
    have martingale_inner_zero :
        μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) | ℱ t] =ᵐ[μ] 0 := by
      -- SUB 17b.1: X_t is adapted to F_t (follows from StochasticAlgorithm recursion)
      have X_adapted : ∀ s, StronglyMeasurable[ℱ s] (X s) := by
        -- By induction on s. Base case: X_0 is F_0-measurable (assumed or trivial).
        -- Inductive case: X_{s+1} = X_s - γh(X_s) + γ(ΔM_{s+1} + R_{s+1})
        -- Each term is F_{s+1}-measurable by adaptedness of ΔM, R.
        -- asm.X_adapted gives Adapted ℱ X, which is exactly ∀ s, StronglyMeasurable[ℱ s] (X s)
        exact asm.X_adapted
      -- SUB 17b.2: gradV(X_t) is F_t-strongly measurable
      have gradV_Xt_meas : StronglyMeasurable[ℱ t] (fun ω => gradV (X t ω)) := by
        -- gradV is continuous (from V_grad_lipschitz : ∃ L, 0 < L ∧ ∀ x y, ‖gradV x - gradV y‖ ≤ L * ‖x - y‖)
        -- Continuous function composed with strongly measurable function is strongly measurable
        -- Use: Continuous.comp_stronglyMeasurable
        obtain ⟨L, hL_pos, hL_lip⟩ := asm.V_grad_lipschitz
        have gradV_cont : Continuous gradV := by
          have hlip : LipschitzWith (Real.toNNReal L) gradV := by
            apply LipschitzWith.of_dist_le'
            intro x y
            rw [dist_eq_norm, dist_eq_norm]
            exact hL_lip x y
          exact hlip.continuous
        exact gradV_cont.comp_stronglyMeasurable (X_adapted t)
      -- SUB 17b.3: Inner product pullout - E[⟨u, v⟩ | F_t] = ⟨u, E[v | F_t]⟩ when u is F_t-meas
      -- This is the key step: use uniqueness characterization of conditional expectation
      have inner_pullout :
          μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) | ℱ t] =ᵐ[μ]
          fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω) := by
        /-
        **Proof Strategy: Uniqueness characterization of conditional expectation**

        We use ae_eq_condExp_of_forall_setIntegral_eq which states that g =ᵃᵉ E[f|m] iff:
        1. g is m-a.e. strongly measurable
        2. g is integrable on all m-measurable sets of finite measure
        3. ∫_s g = ∫_s f for all m-measurable sets s of finite measure

        For our case, g(ω) = ⟨gradV(X_t ω), E[ΔM_{t+1}|ℱ_t] ω⟩ and f(ω) = ⟨gradV(X_t ω), ΔM_{t+1} ω⟩.

        The key insight is that both gradV(X_t) and E[ΔM|ℱ_t] are ℱ_t-strongly measurable,
        so their inner product is ℱ_t-a.e. strongly measurable.

        For the set integral equality, the proof uses simple function approximation:
        - Approximate gradV(X_t) by ℱ_t-simple functions Σᵢ cᵢ 1_{Aᵢ}
        - For each term: ∫_s ⟨cᵢ 1_{Aᵢ}, v⟩ = ⟨cᵢ, ∫_{s∩Aᵢ} v⟩
        - By setIntegral_condExp: ∫_{s∩Aᵢ} E[v|m] = ∫_{s∩Aᵢ} v for m-measurable s∩Aᵢ
        - Take limits using dominated convergence

        The full formalization requires Mathlib's simple function approximation machinery.
        The result is standard in probability theory (see Durrett, Ch. 5).
        -/
        -- SUB inner_pullout.1: Integrability of the inner product ⟨gradV(X_t), ΔM_{t+1}⟩
        -- Follows from: ‖⟨u,v⟩‖ ≤ ‖u‖‖v‖ and Hölder's inequality with L² bounds
        -- growth_bound gives ‖gradV(x)‖² ≤ C(1+V(x)), martingale_condvar_bound gives L² for ΔM
        have inner_integrable : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) μ := by
          -- Strategy: Use norm bound |⟨u,v⟩| ≤ ‖u‖ * ‖v‖ ≤ (‖u‖² + ‖v‖²)/2
          -- Then show both ‖gradV(X_t)‖² and ‖ΔM_{t+1}‖² are integrable
          -- Step 1: AEStronglyMeasurable for the inner product
          have gradV_cont : Continuous gradV := by
            exact ((LinearIsometryEquiv.continuous _).comp
              (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
          have hX_sm : StronglyMeasurable (X t) := (asm.X_adapted t).mono (ℱ.le t)
          have hX_asm : AEStronglyMeasurable (X t) μ := hX_sm.aestronglyMeasurable
          have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X t ω)) μ :=
            gradV_cont.comp_aestronglyMeasurable hX_asm
          have DeltaM_asm : AEStronglyMeasurable (ΔM (t + 1)) μ :=
            (asm.martingale_diff_adapted (t + 1)).mono (ℱ.le (t + 1)) |>.aestronglyMeasurable
          have inner_asm : AEStronglyMeasurable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) μ :=
            gradV_X_asm.inner DeltaM_asm
          -- Step 2: Bound by (‖gradV‖² + ‖ΔM‖²)/2 using AM-GM and Cauchy-Schwarz
          -- |⟨u,v⟩| ≤ ‖u‖·‖v‖ ≤ (‖u‖² + ‖v‖²)/2
          have norm_bound : ∀ ω, ‖@inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)‖ ≤
              (‖gradV (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) / 2 := by
            intro ω
            have hCS := abs_real_inner_le_norm (gradV (X t ω)) (ΔM (t + 1) ω)
            have hAM : ‖gradV (X t ω)‖ * ‖ΔM (t + 1) ω‖ ≤
                (‖gradV (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) / 2 := by
              have := sq_nonneg (‖gradV (X t ω)‖ - ‖ΔM (t + 1) ω‖)
              nlinarith [sq_nonneg ‖gradV (X t ω)‖, sq_nonneg ‖ΔM (t + 1) ω‖]
            rw [Real.norm_eq_abs]
            linarith
          -- Step 3: Show ‖gradV(X_t)‖² is integrable using growth_bound
          have gradV_sq_integrable : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
            -- From growth_bound: ‖gradV(x)‖² ≤ C_growth * (1 + V(x))
            have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := by
              intro ω
              have := h_growth (X t ω)
              linarith [sq_nonneg ‖h (X t ω)‖]
            have V_int : Integrable (fun ω => V (X t ω)) μ := V'_integrable t
            have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ := by
              exact (Integrable.add (integrable_const 1) V_int).const_mul C_growth
            have gradV_sq_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖^2) μ :=
              gradV_X_asm.norm.pow 2
            have norm_bound : ∀ ω, ‖‖gradV (X t ω)‖^2‖ ≤ C_growth * (1 + V (X t ω)) := by
              intro ω
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              exact bound ω
            exact Integrable.mono' bound_int gradV_sq_asm (ae_of_all _ norm_bound)
          -- Step 4: Show ‖ΔM_{t+1}‖² is integrable using martingale_diff_L2
          have DeltaM_sq_integrable : Integrable (fun ω => ‖ΔM (t + 1) ω‖^2) μ :=
            asm.martingale_diff_L2 t
          -- Step 5: Combine to get integrability of inner product
          have sum_integrable : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) / 2) μ :=
            (gradV_sq_integrable.add DeltaM_sq_integrable).div_const 2
          exact Integrable.mono' sum_integrable inner_asm (ae_of_all _ norm_bound)
        -- SUB inner_pullout.2: IntegrableOn for the candidate function on m-measurable sets
        -- Follows from inner_integrable via Integrable.integrableOn
        have inner_condExp_integrableOn : ∀ s, MeasurableSet[ℱ t] s → μ s < ⊤ →
            IntegrableOn (fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)) s μ := by
          -- Strategy: Show global integrability, then apply Integrable.integrableOn
          -- First prove the inner product is globally integrable using the same technique as inner_integrable
          have inner_condExp_integrable : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)) μ := by
            -- Step 1: AEStronglyMeasurable for the inner product with condExp
            have condExp_asm : AEStronglyMeasurable (μ[ΔM (t + 1) | ℱ t]) μ :=
              stronglyMeasurable_condExp.mono (ℱ.le t) |>.aestronglyMeasurable
            have gradV_cont : Continuous gradV := by
              exact ((LinearIsometryEquiv.continuous _).comp
                (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
            have hX_sm : StronglyMeasurable (X t) := (asm.X_adapted t).mono (ℱ.le t)
            have hX_asm : AEStronglyMeasurable (X t) μ := hX_sm.aestronglyMeasurable
            have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X t ω)) μ :=
              gradV_cont.comp_aestronglyMeasurable hX_asm
            have inner_condExp_asm : AEStronglyMeasurable
                (fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)) μ :=
              gradV_X_asm.inner condExp_asm
            -- Step 2: Bound |⟨u,v⟩| ≤ (‖u‖² + ‖v‖²)/2
            have norm_bound_condExp : ∀ ω, ‖@inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)‖ ≤
                (‖gradV (X t ω)‖^2 + ‖(μ[ΔM (t + 1) | ℱ t]) ω‖^2) / 2 := by
              intro ω
              have hCS := abs_real_inner_le_norm (gradV (X t ω)) ((μ[ΔM (t + 1) | ℱ t]) ω)
              have hAM : ‖gradV (X t ω)‖ * ‖(μ[ΔM (t + 1) | ℱ t]) ω‖ ≤
                  (‖gradV (X t ω)‖^2 + ‖(μ[ΔM (t + 1) | ℱ t]) ω‖^2) / 2 := by
                have := sq_nonneg (‖gradV (X t ω)‖ - ‖(μ[ΔM (t + 1) | ℱ t]) ω‖)
                nlinarith [sq_nonneg ‖gradV (X t ω)‖, sq_nonneg ‖(μ[ΔM (t + 1) | ℱ t]) ω‖]
              rw [Real.norm_eq_abs]
              linarith
            -- Step 3: ‖gradV(X_t)‖² is integrable using growth_bound (reprove since not in scope)
            have gradV_sq_integrable' : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
              have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := by
                intro ω
                have := h_growth (X t ω)
                linarith [sq_nonneg ‖h (X t ω)‖]
              have V_int : Integrable (fun ω => V (X t ω)) μ := V'_integrable t
              have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ := by
                exact (Integrable.add (integrable_const 1) V_int).const_mul C_growth
              have gradV_sq_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖^2) μ :=
                gradV_X_asm.norm.pow 2
              have norm_bound' : ∀ ω, ‖‖gradV (X t ω)‖^2‖ ≤ C_growth * (1 + V (X t ω)) := by
                intro ω
                rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
                exact bound ω
              exact Integrable.mono' bound_int gradV_sq_asm (ae_of_all _ norm_bound')
            -- Step 4: ‖μ[ΔM|ℱ_t]‖² is integrable via L² contractivity of condExp
            have condExp_sq_integrable : Integrable (fun ω => ‖(μ[ΔM (t + 1) | ℱ t]) ω‖^2) μ := by
              -- Use eLpNorm_condExp_le: eLpNorm (μ[f|m]) 2 μ ≤ eLpNorm f 2 μ
              -- ΔM is in L² by martingale_diff_L2
              have DeltaM_asm : AEStronglyMeasurable (ΔM (t + 1)) μ :=
                (asm.martingale_diff_adapted (t + 1)).mono (ℱ.le (t + 1)) |>.aestronglyMeasurable
              have DeltaM_L2 : MemLp (ΔM (t + 1)) 2 μ := by
                rw [memLp_two_iff_integrable_sq_norm DeltaM_asm]
                exact asm.martingale_diff_L2 t
              have condExp_L2 : MemLp (μ[ΔM (t + 1) | ℱ t]) 2 μ := DeltaM_L2.condExp
              exact (memLp_two_iff_integrable_sq_norm condExp_asm).mp condExp_L2
            -- Step 5: Combine to get integrability
            have sum_integrable_condExp : Integrable
                (fun ω => (‖gradV (X t ω)‖^2 + ‖(μ[ΔM (t + 1) | ℱ t]) ω‖^2) / 2) μ :=
              (gradV_sq_integrable'.add condExp_sq_integrable).div_const 2
            exact Integrable.mono' sum_integrable_condExp inner_condExp_asm (ae_of_all _ norm_bound_condExp)
          -- Now apply Integrable.integrableOn
          intro s _ _
          exact inner_condExp_integrable.integrableOn
        -- SUB inner_pullout.3: Set integral equality ∫_s ⟨u, E[v|m]⟩ = ∫_s ⟨u, v⟩
        -- This is the key step requiring simple function approximation for u
        -- For simple u = Σᵢ cᵢ 1_{Aᵢ}: ∫_s ⟨u, v⟩ = Σᵢ ⟨cᵢ, ∫_{s∩Aᵢ} v⟩
        -- By setIntegral_condExp: ∫_{s∩Aᵢ} v = ∫_{s∩Aᵢ} E[v|m] for m-measurable Aᵢ
        -- So ∫_s ⟨u, v⟩ = ∫_s ⟨u, E[v|m]⟩ for simple u, then extend by approximation
        have setIntegral_inner_eq : ∀ s, MeasurableSet[ℱ t] s → μ s < ⊤ →
            ∫ ω in s, @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω) ∂μ =
            ∫ ω in s, @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) ∂μ := by
          -- Strategy: Show ∫_s ⟨u, E[v|m] - v⟩ = 0 when u is m-measurable
          -- Key insight: ∫_s (E[v|m] - v) = 0 by setIntegral_condExp, then use integral_inner
          intro s hs hμs
          -- ΔM is L² hence integrable
          have DeltaM_asm : AEStronglyMeasurable (ΔM (t + 1)) μ :=
            (asm.martingale_diff_adapted (t + 1)).mono (ℱ.le (t + 1)) |>.aestronglyMeasurable
          have DeltaM_L2 : MemLp (ΔM (t + 1)) 2 μ := by
            rw [memLp_two_iff_integrable_sq_norm DeltaM_asm]; exact asm.martingale_diff_L2 t
          have DeltaM_int : Integrable (ΔM (t + 1)) μ := DeltaM_L2.integrable one_le_two
          have condExp_L2 : MemLp (μ[ΔM (t + 1) | ℱ t]) 2 μ := DeltaM_L2.condExp
          have sub_L2 : MemLp (fun ω => (μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)) 2 μ :=
            condExp_L2.sub DeltaM_L2
          -- gradV is continuous and X_t is adapted, so gradV(X_t) is L²
          have gradV_cont : Continuous gradV := ((LinearIsometryEquiv.continuous _).comp
            (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
          have hX_asm : AEStronglyMeasurable (X t) μ :=
            ((asm.X_adapted t).mono (ℱ.le t)).aestronglyMeasurable
          have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X t ω)) μ :=
            gradV_cont.comp_aestronglyMeasurable hX_asm
          have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
            have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
              have hg := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
            exact Integrable.mono' ((Integrable.add (integrable_const 1) (V'_integrable t)).const_mul C_growth)
              (gradV_X_asm.norm.pow 2) (ae_of_all _ (fun ω => by
                rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω))
          have gradV_L2 : MemLp (fun ω => gradV (X t ω)) 2 μ := by
            rw [memLp_two_iff_integrable_sq_norm gradV_X_asm]; exact gradV_sq_int
          -- Inner product of L² functions is L¹ (via AM-GM: |⟨u,v⟩| ≤ (‖u‖² + ‖v‖²)/2)
          have condExp_sub_asm : AEStronglyMeasurable
              (fun ω => (μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)) μ :=
            (stronglyMeasurable_condExp.mono (ℱ.le t) |>.aestronglyMeasurable).sub DeltaM_asm
          have condExp_sub_sq_int : Integrable
              (fun ω => ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖^2) μ :=
            (memLp_two_iff_integrable_sq_norm condExp_sub_asm).mp sub_L2
          have inner_integrable' : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω))
              ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))) μ := by
            have inner_asm : AEStronglyMeasurable (fun ω => @inner ℝ _ _ (gradV (X t ω))
                ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))) μ :=
              gradV_X_asm.inner condExp_sub_asm
            have sum_int : Integrable (fun ω => ‖gradV (X t ω)‖^2 +
                ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖^2) μ :=
              gradV_sq_int.add condExp_sub_sq_int
            refine Integrable.mono' sum_int inner_asm (ae_of_all _ (fun ω => ?_))
            -- |⟨u,v⟩| ≤ ‖u‖*‖v‖ ≤ 2*‖u‖*‖v‖ ≤ ‖u‖² + ‖v‖²
            have h1 := abs_real_inner_le_norm (gradV (X t ω))
              ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))
            have h2 := two_mul_le_add_sq ‖gradV (X t ω)‖
              ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖
            have h3 : ‖gradV (X t ω)‖ * ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖ ≤
                2 * ‖gradV (X t ω)‖ * ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖ :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (norm_nonneg _) one_le_two)
                (norm_nonneg _)
            calc ‖@inner ℝ _ _ (gradV (X t ω)) ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))‖
                = |@inner ℝ _ _ (gradV (X t ω)) ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))| := Real.norm_eq_abs _
              _ ≤ ‖gradV (X t ω)‖ * ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖ := h1
              _ ≤ 2 * ‖gradV (X t ω)‖ * ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖ := h3
              _ ≤ ‖gradV (X t ω)‖^2 + ‖(μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)‖^2 := h2
          -- Key fact: ∫_s (E[v|m] - v) = 0 by setIntegral_condExp
          have hzero : ∫ ω in s, (μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω) ∂μ = 0 := by
            rw [integral_sub integrable_condExp.integrableOn DeltaM_int.integrableOn,
              setIntegral_condExp (ℱ.le t) DeltaM_int hs, sub_self]
          -- It suffices to show ∫_s ⟨u, E[v|m] - v⟩ = 0
          suffices hsuff : ∫ ω in s, @inner ℝ _ _ (gradV (X t ω))
              ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)) ∂μ = 0 by
            have hsplit : ∀ ω, @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω) =
                @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
                @inner ℝ _ _ (gradV (X t ω)) ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)) := by
              intro ω; rw [← inner_add_right, add_sub_cancel]
            have hint1 : IntegrableOn (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) s μ :=
              inner_integrable.integrableOn
            have hint2 : IntegrableOn (fun ω => @inner ℝ _ _ (gradV (X t ω))
                ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω))) s μ :=
              inner_integrable'.integrableOn
            simp_rw [hsplit]; rw [integral_add hint1 hint2, hsuff, add_zero]
          -- Key: for m-measurable u, ∫ ⟨E[f|m], u⟩ = ∫ ⟨f, u⟩ (inner_condExpL2_eq_inner_fun)
          -- Using symmetry: ⟨u, E[f|m]⟩ = ⟨E[f|m], u⟩ for real inner product
          -- So ∫ ⟨u, E[f|m]⟩ = ∫ ⟨E[f|m], u⟩ = ∫ ⟨f, u⟩ = ∫ ⟨u, f⟩
          -- First convert: ⟨u, E[v|m] - v⟩ = ⟨u, E[v|m]⟩ - ⟨u, v⟩
          have h_inner_eq : ∀ ω ∈ s, @inner ℝ _ _ (gradV (X t ω))
              ((μ[ΔM (t + 1) | ℱ t] ω) - (ΔM (t + 1) ω)) =
              @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω) -
                @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) := by
            intro ω _; exact inner_sub_right _ _ _
          rw [setIntegral_congr_fun (ℱ.le t s hs) h_inner_eq,
            integral_sub (inner_condExp_integrableOn s hs hμs) inner_integrable.integrableOn,
            sub_eq_zero]
          -- Now prove: ∫_s ⟨u, E[v|m]⟩ = ∫_s ⟨u, v⟩
          -- By symmetry: ⟨u, E[v|m]⟩ = ⟨E[v|m], u⟩ and ⟨u, v⟩ = ⟨v, u⟩
          -- Use inner_condExpL2_eq_inner_fun: ⟪E[f|m], g⟫_{L²(μ.restrict s)} = ⟪f, g⟫_{L²(μ.restrict s)}
          -- when g is ℱ_t-measurable (restricted to s)
          have h_sym1 : ∀ ω ∈ s, @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω) =
              @inner ℝ _ _ (μ[ΔM (t + 1) | ℱ t] ω) (gradV (X t ω)) := by
            intro ω _; exact real_inner_comm _ _
          have h_sym2 : ∀ ω ∈ s, @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) =
              @inner ℝ _ _ (ΔM (t + 1) ω) (gradV (X t ω)) := by
            intro ω _; exact real_inner_comm _ _
          rw [setIntegral_congr_fun (ℱ.le t s hs) h_sym1,
            setIntegral_congr_fun (ℱ.le t s hs) h_sym2]
          -- Now: ∫_s ⟨E[v|m], u⟩ = ∫_s ⟨v, u⟩ for ℱ_t-measurable u
          -- Use inner_condExpL2_eq_inner_fun: ⟪E[f|m], g⟫_{L²} = ⟪f, g⟫_{L²} when g is m-meas
          -- For set s: use indicator function 1_s * u which is ℱ_t-measurable
          have h_ind_meas : StronglyMeasurable[ℱ t]
              (fun ω => s.indicator (fun ω => gradV (X t ω)) ω) :=
            gradV_Xt_meas.indicator hs
          have h_ind_aemeas : AEStronglyMeasurable[ℱ t]
              (fun ω => s.indicator (fun ω => gradV (X t ω)) ω) μ :=
            h_ind_meas.aestronglyMeasurable
          have h_ind_L2 : MemLp (fun ω => s.indicator (fun ω => gradV (X t ω)) ω) 2 μ :=
            gradV_L2.indicator (ℱ.le t s hs)
          -- Relate toLp coercions to original functions
          have h_cond_ae : (condExpL2 E ℝ (ℱ.le t) DeltaM_L2.toLp : Ω → E) =ᵐ[μ]
              μ[ΔM (t + 1) | ℱ t] := DeltaM_L2.condExpL2_ae_eq_condExp (ℱ.le t)
          have h_DM_ae : (DeltaM_L2.toLp : Ω → E) =ᵐ[μ] ΔM (t + 1) := MemLp.coeFn_toLp DeltaM_L2
          have h_ind_ae : (h_ind_L2.toLp : Ω → E) =ᵐ[μ]
              (fun ω => s.indicator (fun ω => gradV (X t ω)) ω) := MemLp.coeFn_toLp h_ind_L2
          -- Get AEStronglyMeasurable for the toLp version
          have h_ind_aemeas' : AEStronglyMeasurable[ℱ t] (h_ind_L2.toLp : Ω → E) μ :=
            h_ind_aemeas.congr h_ind_ae.symm
          -- Apply inner_condExpL2_eq_inner_fun
          have h1 := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (ℱ.le t) DeltaM_L2.toLp h_ind_L2.toLp h_ind_aemeas'
          simp only [L2.inner_def] at h1
          -- Full integral equality
          have h_eq_inner_full : ∫ ω, @inner ℝ _ _ (μ[ΔM (t + 1) | ℱ t] ω)
              (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ =
              ∫ ω, @inner ℝ _ _ (ΔM (t + 1) ω)
              (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ := by
            calc ∫ ω, @inner ℝ _ _ (μ[ΔM (t + 1) | ℱ t] ω)
                  (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ
                = ∫ ω, @inner ℝ _ _ ((condExpL2 E ℝ (ℱ.le t) DeltaM_L2.toLp : Ω → E) ω)
                  ((h_ind_L2.toLp : Ω → E) ω) ∂μ := by
                    refine integral_congr_ae ?_
                    filter_upwards [h_cond_ae, h_ind_ae] with ω h1' h2'
                    simp only [h1', h2']
              _ = ∫ ω, @inner ℝ _ _ ((DeltaM_L2.toLp : Ω → E) ω) ((h_ind_L2.toLp : Ω → E) ω) ∂μ := h1
              _ = ∫ ω, @inner ℝ _ _ (ΔM (t + 1) ω)
                  (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ := by
                    refine integral_congr_ae ?_
                    filter_upwards [h_DM_ae, h_ind_ae] with ω h1' h2'
                    simp only [h1', h2']
          -- Convert back to set integrals
          calc ∫ ω in s, @inner ℝ _ _ (μ[ΔM (t + 1) | ℱ t] ω) (gradV (X t ω)) ∂μ
              = ∫ ω, @inner ℝ _ _ (μ[ΔM (t + 1) | ℱ t] ω)
                (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ := by
                  rw [← integral_indicator (ℱ.le t s hs)]
                  congr 1; ext ω
                  by_cases hω : ω ∈ s <;> simp [hω, inner_zero_right]
            _ = ∫ ω, @inner ℝ _ _ (ΔM (t + 1) ω)
                (s.indicator (fun ω => gradV (X t ω)) ω) ∂μ := h_eq_inner_full
            _ = ∫ ω in s, @inner ℝ _ _ (ΔM (t + 1) ω) (gradV (X t ω)) ∂μ := by
                  rw [← integral_indicator (ℱ.le t s hs)]
                  congr 1; ext ω
                  by_cases hω : ω ∈ s <;> simp [hω, inner_zero_right]
        -- SUB inner_pullout.4: AEStronglyMeasurable[ℱ t]
        have inner_aemeas : AEStronglyMeasurable[ℱ t]
            (fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)) μ :=
          (gradV_Xt_meas.inner stronglyMeasurable_condExp).aestronglyMeasurable
        -- Combine using ae_eq_condExp_of_forall_setIntegral_eq
        symm
        exact ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) inner_integrable
          inner_condExp_integrableOn setIntegral_inner_eq inner_aemeas
      -- SUB 17b.4: Apply martingale property: E[ΔM_{t+1} | F_t] = 0 a.e.
      have mart_zero : μ[ΔM (t + 1) | ℱ t] =ᵐ[μ] 0 := asm.martingale_diff_condexp t
      -- SUB 17b.5: Substitute zero and use inner_zero_right: ⟨u, 0⟩ = 0
      have inner_with_zero :
          (fun ω => @inner ℝ _ _ (gradV (X t ω)) (μ[ΔM (t + 1) | ℱ t] ω)) =ᵐ[μ] 0 := by
        filter_upwards [mart_zero] with ω hω
        simp only [hω, Pi.zero_apply, inner_zero_right]
      -- Combine: E[⟨∇V, ΔM⟩ | F_t] = ⟨∇V, E[ΔM|F_t]⟩ = ⟨∇V, 0⟩ = 0
      exact inner_pullout.trans inner_with_zero

    -- Step 4: Second-order moment bound
    -- SUBTASK 17c: E[‖X_{t+1} - X_t‖² | F_t] ≤ C·γ²·(1 + V(X_t))
    -- NOTE: The remainder_condvar_bound has an extra γ² factor:
    --   E[‖R‖² | F_t] ≤ C_rem * γ² * (1+V)
    -- So when expanding ‖ΔX‖² = γ² * ‖-h + ΔM + R‖², the R contribution
    -- becomes C_rem * γ⁴, not C_rem * γ². The corrected bound reflects this.
    -- SANITY CHECK PASSED
    /-
    **Informal Proof of second_order_bound:**

    We want: E[‖X_{t+1} - X_t‖² | F_t] ≤ 3γ² * (C_growth + C_mart + C_rem*γ²) * (1+V(X_t))

    Step 1: Express increment using recursion
      ΔX := X_{t+1} - X_t = γ * (-h(X_t) + ΔM_{t+1} + R_{t+1})

    Step 2: Compute squared norm
      ‖ΔX‖² = γ² * ‖-h(X_t) + ΔM_{t+1} + R_{t+1}‖²

    Step 3: Apply triangle inequality for squared norms
      For any a, b, c in a normed space: ‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)
      (This follows from Cauchy-Schwarz: ‖Σaᵢ‖² ≤ n * Σ‖aᵢ‖²)
      So: ‖-h + ΔM + R‖² ≤ 3(‖h‖² + ‖ΔM‖² + ‖R‖²)

    Step 4: Take conditional expectation
      E[‖ΔX‖² | F_t] ≤ 3γ² * E[‖h(X_t)‖² + ‖ΔM‖² + ‖R‖² | F_t]
                     = 3γ² * (‖h(X_t)‖² + E[‖ΔM‖² | F_t] + E[‖R‖² | F_t])
      (since h(X_t) is F_t-measurable)

    Step 5: Apply the given bounds
      - ‖h(X_t)‖² ≤ C_growth * (1 + V(X_t))  (from growth_bound)
      - E[‖ΔM‖² | F_t] ≤ C_mart * (1 + V(X_t))  (from martingale_condvar_bound)
      - E[‖R‖² | F_t] ≤ C_rem * γ² * (1 + V(X_t))  (from remainder_condvar_bound)

    Step 6: Combine
      E[‖ΔX‖² | F_t] ≤ 3γ² * (C_growth + C_mart + C_rem*γ²) * (1 + V(X_t))  ∎
    -/
    have second_order_bound :
        μ[fun ω => ‖X (t + 1) ω - X t ω‖^2 | ℱ t]
          ≤ᵐ[μ] fun ω => 3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω)) := by
      -- SUB 17c.1: Triangle inequality for squared norms
      -- ‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)
      have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
        -- Proof: By triangle inequality and Cauchy-Schwarz
        -- 1. ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖  (norm_add₃_le or iterate norm_add_le)
        -- 2. (‖a‖ + ‖b‖ + ‖c‖)² ≤ 3 * (‖a‖² + ‖b‖² + ‖c‖²)  (sq_sum_le_card_mul_sum_sq from Mathlib)
        -- Mathlib imports: `Mathlib.Algebra.Order.Chebyshev`
        -- Key lemma: `sq_sum_le_card_mul_sum_sq : (∑ i ∈ s, f i)^2 ≤ #s * ∑ i ∈ s, f i^2`
        intro a b c
        have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
          calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
            _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
            _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
        -- Apply sq_sum_le_card_mul_sum_sq for Fin 3
        -- First square the triangle inequality: h1^2 : (‖a‖ + ‖b‖ + ‖c‖)^2
        have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
          have h_nn := norm_nonneg (a + b + c)
          have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
          exact sq_le_sq' (by linarith) h1
        -- Use Cauchy-Schwarz: (x + y + z)^2 ≤ 3*(x^2 + y^2 + z^2)
        -- This is proven from sq_sum_le_card_mul_sum_sq
        let f : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
        have hf0 : f 0 = ‖a‖ := rfl
        have hf1 : f 1 = ‖b‖ := rfl
        have hf2 : f 2 = ‖c‖ := rfl
        have sum_eq : ∑ i : Fin 3, f i = ‖a‖ + ‖b‖ + ‖c‖ := by
          simp only [Fin.sum_univ_three, hf0, hf1, hf2]
        have sum_sq_eq : ∑ i : Fin 3, (f i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by
          simp only [Fin.sum_univ_three, hf0, hf1, hf2]
        have card_eq : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
        have h3 : (∑ i : Fin 3, f i)^2 ≤ 3 * ∑ i : Fin 3, (f i)^2 := by
          calc (∑ i : Fin 3, f i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (f i)^2 :=
              sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
            _ = 3 * ∑ i : Fin 3, (f i)^2 := by simp [card_eq]
        calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
          _ = (∑ i : Fin 3, f i)^2 := by rw [sum_eq]
          _ ≤ 3 * ∑ i : Fin 3, (f i)^2 := h3
          _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
      -- SUB 17c.2: Substitute increment and apply triangle inequality
      have increment_bound : ∀ ω, ‖X (t + 1) ω - X t ω‖^2 ≤
          3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) := by
        intro ω
        have h_incr := increment_eq ω
        -- Substitute: ΔX = γ * (-h + ΔM + R)
        -- Then ‖ΔX‖² = γ² * ‖-h + ΔM + R‖² ≤ 3γ² * (‖h‖² + ‖ΔM‖² + ‖R‖²)
        rw [h_incr]
        -- ‖γ • v‖^2 = |γ|^2 * ‖v‖^2 = γ^2 * ‖v‖^2 (since γ^2 = |γ|^2)
        rw [norm_smul, mul_pow, Real.norm_eq_abs]
        -- Apply norm_sq_sum_le_three: ‖-h + ΔM + R‖^2 ≤ 3*(‖-h‖^2 + ‖ΔM‖^2 + ‖R‖^2)
        have h_tri := norm_sq_sum_le_three (-h (X t ω)) (ΔM (t + 1) ω) (R (t + 1) ω)
        -- ‖-h‖ = ‖h‖ by norm_neg
        rw [norm_neg] at h_tri
        -- Now: |γ|^2 * ‖-h + ΔM + R‖^2 ≤ |γ|^2 * 3*(‖h‖^2 + ‖ΔM‖^2 + ‖R‖^2)
        calc |γ (t + 1)|^2 * ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖^2
            ≤ |γ (t + 1)|^2 * (3 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) := by
              apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
          _ = 3 * γ (t + 1)^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) := by
              rw [sq_abs]; ring
      -- SUB 17c.3: Take conditional expectation and apply bounds
      have condexp_bound :
          μ[fun ω => ‖X (t + 1) ω - X t ω‖^2 | ℱ t]
            ≤ᵐ[μ] fun ω => 3 * (γ (t + 1))^2 *
              (‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
               μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) := by
        -- Strategy: Use condExp_mono to take conditional expectation of increment_bound
        -- Then pull out F_t-measurable terms (h(X_t), γ) using condExp_of_stronglyMeasurable
        -- Integrability comes from martingale_diff_L2 and remainder_L2 assumptions

        -- 1. Get integrability of the pointwise bound
        have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (t + 1) ω‖^2) μ := asm.martingale_diff_L2 t
        have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t

        -- 2. Get measurability
        have hX_sm : StronglyMeasurable (X t) := (asm.X_adapted t).mono (ℱ.le t)
        have h_cont : Continuous h := asm.h_continuous
        have h_X_sm : StronglyMeasurable (fun ω => h (X t ω)) :=
          h_cont.comp_stronglyMeasurable hX_sm

        -- 3. Show RHS integrable
        have h_sq_int : Integrable (fun ω => ‖h (X t ω)‖^2) μ := by
          have V_int := V'_integrable t
          have bound : ∀ ω, ‖h (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖gradV (X t ω)‖]
          have asm' : AEStronglyMeasurable (fun ω => ‖h (X t ω)‖^2) μ :=
            h_X_sm.aestronglyMeasurable.norm.pow 2
          have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ :=
            (Integrable.add (integrable_const 1) V_int).const_mul C_growth
          exact Integrable.mono' bound_int asm'
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)

        -- 4. The pointwise bound from increment_bound
        have pw_bound : ∀ ω, ‖X (t + 1) ω - X t ω‖^2 ≤
            3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) :=
          increment_bound

        -- 5. Apply condExp_mono
        have lhs_int : Integrable (fun ω => ‖X (t + 1) ω - X t ω‖^2) μ := by
          -- ‖ΔX‖² ≤ 3γ²*(‖h‖² + ‖ΔM‖² + ‖R‖²)
          have bound_int : Integrable (fun ω =>
              3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) μ := by
            apply Integrable.const_mul
            exact (h_sq_int.add DeltaM_sq_int).add R_sq_int
          exact Integrable.mono' bound_int (by
            have : AEStronglyMeasurable (fun ω => ‖X (t + 1) ω - X t ω‖^2) μ := by
              apply AEStronglyMeasurable.pow
              apply AEStronglyMeasurable.norm
              exact ((asm.X_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable.sub
                (hX_sm.aestronglyMeasurable)
            exact this) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pw_bound ω)

        -- 6. condExp of pointwise bound
        have mono_step := condExp_mono (m := ℱ t) lhs_int (by
          apply Integrable.const_mul
          exact (h_sq_int.add DeltaM_sq_int).add R_sq_int) (ae_of_all _ pw_bound)

        -- 7. Pull out constant and F_t-measurable h(X_t) term
        -- E[3γ²*(‖h‖² + ‖ΔM‖² + ‖R‖²) | F_t] = 3γ²*(‖h‖² + E[‖ΔM‖²|F_t] + E[‖R‖²|F_t])
        -- This uses:
        -- - condExp_smul: E[c·f | m] = c·E[f|m] for scalar c
        -- - condExp_add: E[f+g | m] = E[f|m] + E[g|m]
        -- - condExp_of_stronglyMeasurable: E[f|m] = f for m-measurable f
        -- Mathematically clear but tedious Lean manipulation due to function equality issues
        have pullout_eq : μ[fun ω => 3 * (γ (t + 1))^2 *
            (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) | ℱ t] ≤ᵐ[μ]
            fun ω => 3 * (γ (t + 1))^2 *
            (‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
             μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) := by
          -- Key steps:
          -- 1. E[c * f | ℱ_t] =ᵃᵉ c * E[f | ℱ_t] (condExp_smul since c is constant)
          -- 2. E[f + g + h | ℱ_t] =ᵃᵉ E[f | ℱ_t] + E[g | ℱ_t] + E[h | ℱ_t] (condExp_add twice)
          -- 3. E[‖h(X_t)‖² | ℱ_t] = ‖h(X_t)‖² (condExp_of_stronglyMeasurable: ℱ_t-measurable)

          -- First, establish that the sum inside is integrable
          have sum_int : Integrable (fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) μ :=
            (h_sq_int.add DeltaM_sq_int).add R_sq_int

          -- The whole function is integrable
          have whole_int : Integrable (fun ω => 3 * (γ (t + 1))^2 *
              (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) μ :=
            sum_int.const_mul _

          -- ‖h(X_t)‖² is ℱ_t-strongly measurable
          -- First, X t is ℱ t-adapted, so (asm.X_adapted t) : StronglyMeasurable[ℱ t] (X t)
          have hX_sm_Ft : StronglyMeasurable[ℱ t] (X t) := asm.X_adapted t
          have h_X_sm_Ft : StronglyMeasurable[ℱ t] (fun ω => h (X t ω)) :=
            h_cont.comp_stronglyMeasurable hX_sm_Ft
          have h_sq_sm : StronglyMeasurable[ℱ t] (fun ω => ‖h (X t ω)‖^2) :=
            h_X_sm_Ft.norm.pow 2

          -- Step 1: Use condExp_add to split the sum
          have h_plus_DeltaM_int : Integrable (fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) μ :=
            h_sq_int.add DeltaM_sq_int

          have add_eq1 : μ[fun ω => (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) + ‖R (t + 1) ω‖^2 | ℱ t] =ᵐ[μ]
              (μ[fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 | ℱ t]) +
              (μ[fun ω => ‖R (t + 1) ω‖^2 | ℱ t]) :=
            condExp_add h_plus_DeltaM_int R_sq_int (ℱ t)

          have add_eq2 : μ[fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 | ℱ t] =ᵐ[μ]
              (μ[fun ω => ‖h (X t ω)‖^2 | ℱ t]) + (μ[fun ω => ‖ΔM (t + 1) ω‖^2 | ℱ t]) :=
            condExp_add h_sq_int DeltaM_sq_int (ℱ t)

          -- Step 2: E[‖h(X_t)‖² | ℱ_t] = ‖h(X_t)‖² since it's ℱ_t-measurable
          have h_sq_condExp : μ[fun ω => ‖h (X t ω)‖^2 | ℱ t] =ᵐ[μ] fun ω => ‖h (X t ω)‖^2 := by
            rw [condExp_of_stronglyMeasurable (ℱ.le t) h_sq_sm h_sq_int]

          -- Step 3: Pull out the constant using condExp_smul
          -- Note: 3 * (γ (t + 1))^2 is a real scalar
          have smul_eq : μ[fun ω => 3 * (γ (t + 1))^2 *
              (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) | ℱ t] =ᵐ[μ]
              fun ω => 3 * (γ (t + 1))^2 * μ[fun ω' =>
              (‖h (X t ω')‖^2 + ‖ΔM (t + 1) ω'‖^2 + ‖R (t + 1) ω'‖^2) | ℱ t] ω := by
            have key : (fun ω => 3 * (γ (t + 1))^2 *
                (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) =
                (fun ω => (3 * (γ (t + 1))^2) •
                (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) := by
              ext ω; simp [smul_eq_mul]
            rw [key]
            have smul_cond := @condExp_smul Ω _ ℝ _ m0 μ _ _ _ _
              (3 * (γ (t + 1))^2)
              (fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) (ℱ t)
            filter_upwards [smul_cond] with ω hω
            simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
            exact hω

          -- Now combine: E[sum | ℱ_t] = E[h_sq] + E[ΔM_sq] + E[R_sq] = h_sq + E[ΔM_sq] + E[R_sq]
          have combined_eq : μ[fun ω => ‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2 | ℱ t] =ᵐ[μ]
              fun ω => ‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
                       μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω := by
            filter_upwards [add_eq1, add_eq2, h_sq_condExp] with ω h1 h2 h3
            simp only [Pi.add_apply] at h1 h2 h3 ⊢
            rw [h1, h2, h3]

          -- Finally, combine smul_eq and combined_eq
          filter_upwards [smul_eq, combined_eq] with ω h_smul h_comb
          rw [h_smul, h_comb]

        -- 8. Chain: LHS ≤ᵐ condExp(pointwise bound) ≤ᵐ RHS
        exact mono_step.trans pullout_eq
      -- SUB 17c.4: Apply the variance bounds from assumptions
      have apply_bounds :
          ∀ᵐ ω ∂μ, 3 * (γ (t + 1))^2 *
            (‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
             μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) ≤
          3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω)) := by
        -- Use:
        -- - h_growth: ‖h(X_t)‖² ≤ C_growth * (1 + V(X_t))
        -- - h_mart_var: E[‖ΔM‖² | F_t] ≤ C_mart * (1 + V(X_t))
        -- - h_rem_var: E[‖R‖² | F_t] ≤ C_rem * γ² * (1 + V(X_t))

        -- Get the three bounds
        have h_bound : ∀ ω, ‖h (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
          have := h_growth (X t ω); linarith [sq_nonneg ‖gradV (X t ω)‖]

        have mart_bound := h_mart_var t
        have rem_bound := h_rem_var t

        -- Combine the a.e. bounds
        filter_upwards [mart_bound, rem_bound] with ω h_mart h_rem

        -- Goal: 3γ² * (‖h‖² + E[‖ΔM‖²] + E[‖R‖²]) ≤ 3γ² * (C_growth + C_mart + C_rem * γ²) * (1 + V)
        -- Since:
        --   ‖h‖² ≤ C_growth * (1 + V)
        --   E[‖ΔM‖²] ≤ C_mart * (1 + V)
        --   E[‖R‖²] ≤ C_rem * γ² * (1 + V)
        -- Sum: ‖h‖² + E[‖ΔM‖²] + E[‖R‖²] ≤ (C_growth + C_mart + C_rem * γ²) * (1 + V)
        have h1 := h_bound ω
        have sum_bound : ‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
            μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω ≤
            (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω)) := by
          calc ‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
                μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω
              ≤ C_growth * (1 + V (X t ω)) + C_mart * (1 + V (X t ω)) +
                C_rem * (γ (t + 1))^2 * (1 + V (X t ω)) := by linarith
            _ = (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω)) := by ring
        calc 3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + μ[fun ω' => ‖ΔM (t + 1) ω'‖^2 | ℱ t] ω +
              μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω)
            ≤ 3 * (γ (t + 1))^2 * ((C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω))) := by
              apply mul_le_mul_of_nonneg_left sum_bound
              apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _)
          _ = 3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω)) := by ring
      -- Combine using transitivity of ≤ᵐ
      exact condexp_bound.trans apply_bounds

    -- Step 5: Remainder inner product bound
    -- SUBTASK 17d: |E[⟨∇V(X_t), R_{t+1}⟩ | F_t]| ≤ C·γ·(1+V)
    -- SANITY CHECK PASSED
    /-
    **Informal Proof of remainder_inner_bound:**

    We want: |E[⟨∇V(X_t), R_{t+1}⟩ | F_t]| ≤ √(C_growth·C_rem) * γ * (1+V(X_t))

    Step 1: Absolute value inside conditional expectation
      |E[⟨∇V(X_t), R⟩ | F_t]| ≤ E[|⟨∇V(X_t), R⟩| | F_t]  (by Jensen/triangle)

    Step 2: Cauchy-Schwarz for inner product
      |⟨∇V(X_t), R⟩| ≤ ‖∇V(X_t)‖ · ‖R‖  (by abs_inner_le_norm)

    Step 3: Pull out F_t-measurable term
      Since X_t is F_t-adapted and gradV is deterministic, ‖∇V(X_t)‖ is F_t-measurable.
      E[‖∇V(X_t)‖ · ‖R‖ | F_t] = ‖∇V(X_t)‖ · E[‖R‖ | F_t]
      (by condExp_of_stronglyMeasurable or condExp_mul)

    Step 4: Jensen's inequality for conditional expectation
      E[‖R‖ | F_t] ≤ √E[‖R‖² | F_t]  (by condExp_mono + sqrt concave)

    Step 5: Apply the given bounds
      From remainder_condvar_bound: E[‖R‖² | F_t] ≤ C_rem · γ² · (1+V(X_t))
      So: E[‖R‖ | F_t] ≤ √(C_rem · γ² · (1+V(X_t))) = γ · √(C_rem · (1+V(X_t)))

      From growth_bound: ‖∇V(X_t)‖² ≤ C_growth · (1+V(X_t))
      So: ‖∇V(X_t)‖ ≤ √(C_growth · (1+V(X_t)))

    Step 6: Combine
      |E[⟨∇V(X_t), R⟩ | F_t]| ≤ ‖∇V(X_t)‖ · E[‖R‖ | F_t]
                              ≤ √(C_growth · (1+V)) · γ · √(C_rem · (1+V))
                              = γ · √(C_growth · C_rem) · (1+V)  ∎
    -/
    have remainder_inner_bound :
        ∀ᵐ ω ∂μ, |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω|
          ≤ Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := by
      -- SUB 17d.1: Bound absolute value of inner product by product of norms
      -- |⟨u, v⟩| ≤ ‖u‖ · ‖v‖ (Cauchy-Schwarz)
      have inner_abs_bound : ∀ u v : E, |@inner ℝ _ _ u v| ≤ ‖u‖ * ‖v‖ := by
        -- Use Mathlib: abs_real_inner_le_norm
        intro u v
        exact abs_real_inner_le_norm u v
      -- SUB 17d.2: Absolute value and conditional expectation
      -- |E[f | F_t]| ≤ E[|f| | F_t] (Jensen's inequality for conditional expectation)
      have condexp_abs_le : ∀ᵐ ω ∂μ,
          |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω| ≤
          μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] ω := by
        -- Use pattern from Mathlib's eLpNorm_one_condExp_le_eLpNorm proof:
        -- |E[f|m]| ≤ E[|f||m] follows from:
        --   E[f|m] ≤ E[|f||m] (since f ≤ |f|)
        --   -E[f|m] = E[-f|m] ≤ E[|f||m] (since -f ≤ |f|)
        -- Combined: |E[f|m]| ≤ E[|f||m]

        -- gradV is continuous (from V_smooth: V is C², so ∇V is C¹, hence continuous)
        have gradV_cont : Continuous gradV := by
          exact ((LinearIsometryEquiv.continuous _).comp
            (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq

        -- Step 1: Show integrability of the inner product (needed for condExp_mono)
        -- Using: |⟨u,v⟩| ≤ ‖u‖*‖v‖ ≤ (‖u‖² + ‖v‖²)/2
        have inner_int : Integrable (fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')) μ := by
          -- Get integrability of ‖gradV(X_t)‖² and ‖R‖²
          have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
            have V_int := V'_integrable t
            have one_plus_V_int : Integrable (fun ω => 1 + V (X t ω)) μ :=
              (integrable_const 1).add V_int
            have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
              have := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
            have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ :=
              one_plus_V_int.const_mul C_growth
            have hX_sm := (asm.X_adapted t).mono (ℱ.le t)
            have gradV_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖^2) μ := by
              apply AEStronglyMeasurable.pow
              apply AEStronglyMeasurable.norm
              exact (gradV_cont.comp_stronglyMeasurable hX_sm).aestronglyMeasurable
            exact Integrable.mono' bound_int gradV_asm (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
          have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
          -- Now prove integrability of inner product using bound |⟨u,v⟩| ≤ (‖u‖² + ‖v‖²)/2
          have hX_sm := (asm.X_adapted t).mono (ℱ.le t)
          have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X t ω)) μ :=
            gradV_cont.comp_aestronglyMeasurable hX_sm.aestronglyMeasurable
          have R_asm : AEStronglyMeasurable (R (t + 1)) μ :=
            ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
          have inner_asm : AEStronglyMeasurable
              (fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')) μ :=
            gradV_X_asm.inner R_asm
          have sum_int : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2) μ :=
            (gradV_sq_int.add R_sq_int).div_const 2
          refine Integrable.mono' sum_int inner_asm (ae_of_all _ fun ω => ?_)
          have h1 := abs_real_inner_le_norm (gradV (X t ω)) (R (t + 1) ω)
          have h2 : ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖ ≤
              (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2 := by nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖R (t + 1) ω‖)]
          calc ‖@inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)‖
              = |@inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)| := Real.norm_eq_abs _
            _ ≤ ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖ := h1
            _ ≤ (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2 := h2

        -- Step 2: Integrability of |inner product|
        have abs_inner_int : Integrable
            (fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')|) μ := inner_int.abs

        -- Step 3: Apply condExp_mono twice (for f and -f) and combine
        have upper_bound : μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ≤ᵐ[μ]
            μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] :=
          condExp_mono inner_int abs_inner_int
            (ae_of_all μ fun ω => le_abs_self _)

        have lower_bound : -μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ≤ᵐ[μ]
            μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] := by
          have h1 : (fun ω => -(μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t]) ω) =ᵐ[μ]
              μ[fun ω' => -@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] :=
            (condExp_neg (m := ℱ t) (fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω'))).symm
          have h2 : μ[fun ω' => -@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ≤ᵐ[μ]
              μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] :=
            condExp_mono inner_int.neg abs_inner_int
              (ae_of_all μ fun ω => neg_le_abs _)
          exact h1.le.trans h2

        filter_upwards [upper_bound, lower_bound] with ω h_upper h_lower
        exact abs_le.mpr ⟨neg_le.mp h_lower, h_upper⟩
      -- SUB 17d.3: Apply Cauchy-Schwarz pointwise
      have apply_cs : ∀ᵐ ω ∂μ,
          μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] ω ≤
          μ[fun ω' => ‖gradV (X t ω')‖ * ‖R (t + 1) ω'‖ | ℱ t] ω := by
        -- Use condExp_mono with the pointwise bound inner_abs_bound
        -- First establish integrability of the norm product
        have gradV_cont : Continuous gradV := by
          exact ((LinearIsometryEquiv.continuous _).comp
            (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
        have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
          have V_int := V'_integrable t
          have one_plus_V_int : Integrable (fun ω => 1 + V (X t ω)) μ :=
            (integrable_const 1).add V_int
          have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
          have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ :=
            one_plus_V_int.const_mul C_growth
          have hX_sm := (asm.X_adapted t).mono (ℱ.le t)
          have gradV_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact (gradV_cont.comp_stronglyMeasurable hX_sm).aestronglyMeasurable
          exact Integrable.mono' bound_int gradV_asm (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
        have sum_int : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2) μ :=
          (gradV_sq_int.add R_sq_int).div_const 2
        -- Integrability of the product ‖gradV‖ * ‖R‖ via bound by sum of squares
        have hX_sm := (asm.X_adapted t).mono (ℱ.le t)
        have gradV_norm_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖) μ :=
          (gradV_cont.comp_aestronglyMeasurable hX_sm.aestronglyMeasurable).norm
        have R_norm_asm : AEStronglyMeasurable (fun ω => ‖R (t + 1) ω‖) μ :=
          ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable.norm
        have prod_norm_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖) μ :=
          gradV_norm_asm.mul R_norm_asm
        have prod_norm_int : Integrable (fun ω => ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖) μ := by
          refine Integrable.mono' sum_int prod_norm_asm (ae_of_all _ fun ω => ?_)
          have h : ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖ ≤
              (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2 := by
            nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖R (t + 1) ω‖)]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact h
        -- Establish integrability of |inner product| (same bound as prod of norms)
        have gradV_X_asm : AEStronglyMeasurable (fun ω => gradV (X t ω)) μ :=
          gradV_cont.comp_aestronglyMeasurable hX_sm.aestronglyMeasurable
        have R_asm : AEStronglyMeasurable (R (t + 1)) μ :=
          ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
        have inner_asm : AEStronglyMeasurable
            (fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')) μ :=
          gradV_X_asm.inner R_asm
        have abs_inner_int : Integrable
            (fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')|) μ := by
          refine Integrable.mono' prod_norm_int inner_asm.norm (ae_of_all _ fun ω => ?_)
          simp only [Real.norm_eq_abs, abs_abs]
          exact inner_abs_bound (gradV (X t ω)) (R (t + 1) ω)
        -- Now apply condExp_mono
        exact condExp_mono abs_inner_int prod_norm_int
          (ae_of_all μ fun ω => inner_abs_bound (gradV (X t ω)) (R (t + 1) ω))
      -- SUB 17d.4: Pull out F_t-measurable ‖∇V(X_t)‖
      -- Since X_t is F_t-adapted, gradV(X_t) is F_t-measurable
      -- E[‖∇V(X_t)‖ · ‖R‖ | F_t] = ‖∇V(X_t)‖ · E[‖R‖ | F_t]
      have pullout_measurable : ∀ᵐ ω ∂μ,
          μ[fun ω' => ‖gradV (X t ω')‖ * ‖R (t + 1) ω'‖ | ℱ t] ω =
          ‖gradV (X t ω)‖ * μ[fun ω' => ‖R (t + 1) ω'‖ | ℱ t] ω := by
        -- Use condExp_mul_of_stronglyMeasurable_left
        -- Key: gradV ∘ X t is F_t-measurable (from adaptedness)
        -- Re-establish key facts that are in earlier proof blocks but not in scope
        have gradV_cont : Continuous gradV := by
          exact ((LinearIsometryEquiv.continuous _).comp
            (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
        have hX_sm : StronglyMeasurable[ℱ t] (X t) := asm.X_adapted t
        -- Step 1: Show ‖gradV (X t ·)‖ is ℱ t-strongly measurable
        have gradV_norm_sm : StronglyMeasurable[ℱ t] (fun ω' => ‖gradV (X t ω')‖) :=
          (gradV_cont.comp_stronglyMeasurable hX_sm).norm
        -- Step 2: Integrability of ‖R(t+1)‖
        have R_asm_t : AEStronglyMeasurable (R (t + 1)) μ :=
          ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
        have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
        have R_memLp : MemLp (R (t + 1)) 2 μ := (memLp_two_iff_integrable_sq_norm R_asm_t).mpr R_sq_int
        have R_norm_int : Integrable (fun ω' => ‖R (t + 1) ω'‖) μ := R_memLp.norm.integrable one_le_two
        -- Step 3: Establish integrability of product (same as in apply_cs proof)
        have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
          have V_int := V'_integrable t
          have one_plus_V_int : Integrable (fun ω => 1 + V (X t ω)) μ :=
            (integrable_const 1).add V_int
          have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
          have bound_int : Integrable (fun ω => C_growth * (1 + V (X t ω))) μ :=
            one_plus_V_int.const_mul C_growth
          have gradV_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact (gradV_cont.comp_stronglyMeasurable (hX_sm.mono (ℱ.le t))).aestronglyMeasurable
          exact Integrable.mono' bound_int gradV_asm (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        have sum_int : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2) μ :=
          (gradV_sq_int.add R_sq_int).div_const 2
        have gradV_norm_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖) μ :=
          (gradV_cont.comp_aestronglyMeasurable (hX_sm.mono (ℱ.le t)).aestronglyMeasurable).norm
        have R_norm_asm : AEStronglyMeasurable (fun ω => ‖R (t + 1) ω‖) μ := R_asm_t.norm
        have prod_norm_asm : AEStronglyMeasurable (fun ω => ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖) μ :=
          gradV_norm_asm.mul R_norm_asm
        have prod_norm_int : Integrable (fun ω => ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖) μ := by
          refine Integrable.mono' sum_int prod_norm_asm (ae_of_all _ fun ω => ?_)
          have h : ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖ ≤
              (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2 := by
            nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖R (t + 1) ω‖)]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact h
        -- Step 4: Apply the pull-out property
        exact condExp_mul_of_stronglyMeasurable_left gradV_norm_sm prod_norm_int R_norm_int
      -- SUB 17d.5: Jensen's inequality: E[‖R‖ | F_t] ≤ √E[‖R‖² | F_t]
      have jensen_sqrt : ∀ᵐ ω ∂μ,
          μ[fun ω' => ‖R (t + 1) ω'‖ | ℱ t] ω ≤
          Real.sqrt (μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) := by
        -- Jensen for concave sqrt: E[f] ≤ sqrt(E[f²])
        -- Strategy: Use E[X]² ≤ E[X²] (Jensen for convex x²) for conditional expectations
        -- This follows from Var[X|F] = E[X²|F] - E[X|F]² ≥ 0
        -- Since E[X|F] ≥ 0 for nonneg X, we get E[X|F] ≤ sqrt(E[X²|F])
        -- Establish integrability requirements
        have R_asm_t' : AEStronglyMeasurable (R (t + 1)) μ :=
          ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
        have R_sq_int' : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
        have R_memLp' : MemLp (R (t + 1)) 2 μ := (memLp_two_iff_integrable_sq_norm R_asm_t').mpr R_sq_int'
        have R_norm_int' : Integrable (fun ω' => ‖R (t + 1) ω'‖) μ := R_memLp'.norm.integrable one_le_two
        have R_norm_sq_int' : Integrable (fun ω => (‖R (t + 1) ω‖)^2) μ := R_sq_int'
        -- Nonnegativity of ‖R‖
        have R_norm_nonneg : ∀ ω, 0 ≤ ‖R (t + 1) ω‖ := fun ω => norm_nonneg _
        -- Conditional expectation of nonnegative function is nonnegative
        have condexp_norm_nonneg : 0 ≤ᵐ[μ] μ[fun ω' => ‖R (t + 1) ω'‖ | ℱ t] :=
          condExp_nonneg (ae_of_all μ R_norm_nonneg)
        have condexp_sq_nonneg : 0 ≤ᵐ[μ] μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] :=
          condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
        -- Key inequality: (E[X|F])² ≤ E[X²|F]
        -- This follows from: Var[X|F] = E[X²|F] - E[X|F]² ≥ 0
        -- We use the conditional variance formula from CondVar
        -- Define the real-valued function f = ‖R‖
        let f : Ω → ℝ := fun ω => ‖R (t + 1) ω‖
        have f_nonneg : ∀ ω, 0 ≤ f ω := fun ω => norm_nonneg _
        have f_asm : AEStronglyMeasurable f μ := R_asm_t'.norm
        have f_sq_int : Integrable (fun ω => f ω ^ 2) μ := R_norm_sq_int'
        have f_memLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq R_asm_t'.norm).mpr f_sq_int
        -- Apply conditional variance formula
        -- condVar_ae_eq_condExp_sq_sub_sq_condExp gives: Var[f|m] = E[f²|m] - E[f|m]²
        -- Since Var = E[(f - E[f|m])²|m] ≥ 0, we have E[f|m]² ≤ E[f²|m]
        have var_nonneg : 0 ≤ᵐ[μ] ProbabilityTheory.condVar (ℱ t) f μ := by
          apply condExp_nonneg
          exact ae_of_all μ fun ω => sq_nonneg _
        have var_eq : ProbabilityTheory.condVar (ℱ t) f μ =ᵐ[μ]
            μ[f ^ 2 | ℱ t] - μ[f | ℱ t] ^ 2 :=
          ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le t) f_memLp
        -- From var_nonneg and var_eq: E[f|m]² ≤ E[f²|m]
        have sq_le : ∀ᵐ ω ∂μ, μ[f | ℱ t] ω ^ 2 ≤ μ[f ^ 2 | ℱ t] ω := by
          filter_upwards [var_nonneg, var_eq] with ω hpos heq
          have : 0 ≤ μ[f ^ 2 | ℱ t] ω - μ[f | ℱ t] ω ^ 2 := by
            simp only [Pi.sub_apply, Pi.pow_apply] at heq
            rw [← heq]; exact hpos
          linarith
        -- Now derive the sqrt inequality
        filter_upwards [condexp_norm_nonneg, condexp_sq_nonneg, sq_le] with ω hpos hsq_pos hsq_le
        -- Use Real.le_sqrt: for 0 ≤ a, a ≤ sqrt(b) iff a² ≤ b
        rw [Real.le_sqrt hpos hsq_pos]
        exact hsq_le
      -- SUB 17d.6: Apply remainder variance bound
      have apply_rem_var : ∀ᵐ ω ∂μ,
          Real.sqrt (μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) ≤
          Real.sqrt (C_rem * (γ (t + 1))^2 * (1 + V (X t ω))) := by
        -- Use h_rem_var t and Real.sqrt_le_sqrt
        filter_upwards [h_rem_var t] with ω hrem
        exact Real.sqrt_le_sqrt hrem
      -- SUB 17d.7: Apply gradient growth bound
      have apply_grad_growth : ∀ ω, ‖gradV (X t ω)‖ ≤ Real.sqrt (C_growth * (1 + V (X t ω))) := by
        -- From h_growth: ‖gradV x‖² ≤ C_growth * (1+V(x))
        intro ω
        have hgb := h_growth (X t ω)
        -- Extract ‖gradV(X t ω)‖² ≤ C_growth * (1 + V(X t ω)) from the sum
        have gradV_sq_bound : ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := by
          have hh_nonneg := sq_nonneg ‖h (X t ω)‖
          linarith
        have hV_nonneg : 0 ≤ C_growth * (1 + V (X t ω)) := by
          have hVx : 0 < 1 + V (X t ω) := by
            have := hV_lower (X t ω)
            linarith
          exact mul_nonneg (le_of_lt hC_growth_pos) (le_of_lt hVx)
        rw [Real.le_sqrt (norm_nonneg _) hV_nonneg]
        exact gradV_sq_bound
      -- SUB 17d.8: Combine all bounds algebraically
      have combine_bounds : ∀ᵐ ω ∂μ,
          ‖gradV (X t ω)‖ * Real.sqrt (C_rem * (γ (t + 1))^2 * (1 + V (X t ω))) ≤
          Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := by
        -- Algebraic manipulation:
        -- ‖∇V‖ ≤ √(C_growth*(1+V)) from apply_grad_growth
        -- √(C_rem*γ²*(1+V)) = γ*√(C_rem*(1+V)) for γ ≥ 0
        -- So: ‖∇V‖ * √(C_rem*γ²*(1+V)) ≤ √(C_growth*(1+V)) * γ * √(C_rem*(1+V))
        --                               = γ * √(C_growth*C_rem) * (1+V)
        -- Key Mathlib lemmas:
        -- - Real.sqrt_mul, Real.sqrt_sq
        -- - Algebraic: √a·√b = √(ab), and √((1+V)²) = 1+V for 1+V ≥ 0
        apply ae_of_all μ
        intro ω
        -- Setup positivity facts
        have hγ_nonneg : 0 ≤ γ (t + 1) := le_of_lt (asm.gamma_pos (t + 1))
        have hV_pos : 0 < 1 + V (X t ω) := by
          have := hV_lower (X t ω)
          linarith
        have hV_nonneg : 0 ≤ 1 + V (X t ω) := le_of_lt hV_pos
        have hC_rem_nonneg : 0 ≤ C_rem := le_of_lt hC_rem_pos
        have hC_growth_nonneg : 0 ≤ C_growth := le_of_lt hC_growth_pos
        have hγ_sq_nonneg : 0 ≤ (γ (t + 1))^2 := sq_nonneg _
        -- From apply_grad_growth
        have grad_bound := apply_grad_growth ω
        -- Rewrite the sqrt on LHS: √(C_rem*γ²*(1+V)) = √(C_rem) * √(γ²) * √(1+V) = √(C_rem) * γ * √(1+V)
        have sqrt_decomp : Real.sqrt (C_rem * (γ (t + 1))^2 * (1 + V (X t ω))) =
            Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω)) := by
          -- First, massage into a form we can use sqrt_mul on
          have h_assoc : C_rem * (γ (t + 1))^2 * (1 + V (X t ω)) =
              C_rem * ((γ (t + 1))^2 * (1 + V (X t ω))) := by ring
          rw [h_assoc]
          rw [Real.sqrt_mul hC_rem_nonneg]
          -- Now massage the inner product
          have h_assoc2 : (γ (t + 1))^2 * (1 + V (X t ω)) =
              (γ (t + 1))^2 * (1 + V (X t ω)) := rfl
          rw [Real.sqrt_mul hγ_sq_nonneg]
          rw [Real.sqrt_sq hγ_nonneg]
          ring
        rw [sqrt_decomp]
        -- LHS ≤ √(C_growth*(1+V)) * √(C_rem) * γ * √(1+V)
        have step1 : ‖gradV (X t ω)‖ * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω))) ≤
            Real.sqrt (C_growth * (1 + V (X t ω))) * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω))) := by
          apply mul_le_mul_of_nonneg_right grad_bound
          apply mul_nonneg
          apply mul_nonneg
          exact Real.sqrt_nonneg _
          exact hγ_nonneg
          exact Real.sqrt_nonneg _
        -- Now simplify the RHS
        -- √(C_growth*(1+V)) * √C_rem * γ * √(1+V) = √(C_growth*C_rem) * √(1+V) * √(1+V) * γ
        --                                         = √(C_growth*C_rem) * (1+V) * γ
        have rhs_eq : Real.sqrt (C_growth * (1 + V (X t ω))) * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω))) =
            Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := by
          rw [Real.sqrt_mul hC_growth_nonneg]
          have sqrt_prod : Real.sqrt (1 + V (X t ω)) * Real.sqrt (1 + V (X t ω)) = 1 + V (X t ω) :=
            Real.mul_self_sqrt hV_nonneg
          calc Real.sqrt C_growth * Real.sqrt (1 + V (X t ω)) * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω)))
              = Real.sqrt C_growth * Real.sqrt C_rem * (γ (t + 1)) * (Real.sqrt (1 + V (X t ω)) * Real.sqrt (1 + V (X t ω))) := by ring
            _ = Real.sqrt C_growth * Real.sqrt C_rem * (γ (t + 1)) * (1 + V (X t ω)) := by rw [sqrt_prod]
            _ = Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := by
                rw [← Real.sqrt_mul hC_growth_nonneg C_rem]
        calc ‖gradV (X t ω)‖ * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω)))
            ≤ Real.sqrt (C_growth * (1 + V (X t ω))) * (Real.sqrt C_rem * (γ (t + 1)) * Real.sqrt (1 + V (X t ω))) := step1
          _ = Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := rhs_eq
      -- Chain the bounds together
      filter_upwards [condexp_abs_le, apply_cs, pullout_measurable, jensen_sqrt, apply_rem_var,
                      combine_bounds] with ω h1 h2 h3 h4 h5 h6
      calc |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω|
          ≤ μ[fun ω' => |@inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω')| | ℱ t] ω := h1
        _ ≤ μ[fun ω' => ‖gradV (X t ω')‖ * ‖R (t + 1) ω'‖ | ℱ t] ω := h2
        _ = ‖gradV (X t ω)‖ * μ[fun ω' => ‖R (t + 1) ω'‖ | ℱ t] ω := h3
        _ ≤ ‖gradV (X t ω)‖ * Real.sqrt (μ[fun ω' => ‖R (t + 1) ω'‖^2 | ℱ t] ω) := by
            apply mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        _ ≤ ‖gradV (X t ω)‖ * Real.sqrt (C_rem * (γ (t + 1))^2 * (1 + V (X t ω))) := by
            apply mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
        _ ≤ Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := h6

    -- Step 6: The key bound (1+V) ≤ (1+1/m)·V using V ≥ m
    -- SANITY CHECK PASSED
    -- Proof strategy: Use `one_le_div` to show 1 ≤ V(x)/m from hV_lower,
    -- then calc chain with ring/linarith to derive 1 + V ≤ (1 + 1/m) * V
    -- Key Mathlib: one_le_div, linarith, ring
    have one_plus_V_bound : ∀ x : E, 1 + V x ≤ (1 + 1/m) * V x := by
      intro x
      have hVx : m ≤ V x := hV_lower x
      have hm_ne : m ≠ 0 := ne_of_gt hm_pos
      have hV_pos : 0 < V x := lt_of_lt_of_le hm_pos hVx
      have key : 1 ≤ V x / m := by rw [one_le_div hm_pos]; exact hVx
      calc 1 + V x = 1 + 1 * V x := by ring
        _ ≤ V x / m + 1 * V x := by linarith
        _ = V x / m + V x := by ring
        _ = V x * (1/m) + V x * 1 := by ring
        _ = V x * (1/m + 1) := by ring
        _ = (1/m + 1) * V x := by ring
        _ = (1 + 1/m) * V x := by ring

    -- Step 7: Combine all bounds to get the drift inequality
    -- SUBTASK 17g: Combine Taylor, martingale, and variance bounds
    -- SANITY CHECK PASSED (algebraic combination of established bounds)
    /-
    **Informal Proof of final combination:**

    We have established:
    - taylor_bound: V(y) ≤ V(x) + ⟨∇V(x), y-x⟩ + (L/2)‖y-x‖²
    - increment_eq: X_{t+1} - X_t = γ·(-h + ΔM + R)
    - martingale_inner_zero: E[⟨∇V, ΔM⟩|F_t] = 0
    - second_order_bound: E[‖ΔX‖²|F_t] ≤ 3γ²(C_growth + C_mart + C_rem·γ²)(1+V)
    - remainder_inner_bound: |E[⟨∇V, R⟩|F_t]| ≤ √(C_growth·C_rem)·γ·(1+V)
    - one_plus_V_bound: 1+V(x) ≤ (1+1/m)·V(x)

    Step A: Apply Taylor bound pointwise
      V(X_{t+1}(ω)) ≤ V(X_t(ω)) + ⟨∇V(X_t), ΔX⟩ + (L/2)‖ΔX‖²

    Step B: Expand inner product using increment_eq
      ⟨∇V(X_t), ΔX⟩ = ⟨∇V, γ·(-h + ΔM + R)⟩
                     = -γ⟨∇V, h⟩ + γ⟨∇V, ΔM⟩ + γ⟨∇V, R⟩

    Step C: Take conditional expectation
      E[V(X_{t+1})|F_t] ≤ V(X_t) - γ⟨∇V, h⟩ + γ·E[⟨∇V, ΔM⟩|F_t]
                         + γ·E[⟨∇V, R⟩|F_t] + (L/2)·E[‖ΔX‖²|F_t]

    Step D: Apply bounds
      - Martingale: E[⟨∇V, ΔM⟩|F_t] = 0
      - Remainder: |γ·E[⟨∇V, R⟩|F_t]| ≤ √(C_growth·C_rem)·γ²·(1+V)
      - Second-order: (L/2)·E[‖ΔX‖²|F_t] ≤ (3L/2)·γ²·(C_growth + C_mart + C_rem·γ²)·(1+V)

    Step E: Combine second-order terms
      Total coefficient C' ≤ √(C_growth·C_rem) + (3L/2)(C_growth + C_mart + C_rem)
      E[V(X_{t+1})|F_t] ≤ V(X_t) - γ⟨∇V, h⟩ + C'·γ²·(1+V)

    Step F: Apply (1+V) ≤ (1+1/m)·V
      C'·γ²·(1+V) ≤ C'·(1+1/m)·γ²·V ≤ C_drift·γ²·V

    Conclusion: E[V(X_{t+1})|F_t] ≤ (1 + C_drift·γ²)·V(X_t) - γ⟨∇V, h⟩  ∎
    -/

    -- SUB 17g.1: Apply Taylor bound pointwise
    have taylor_applied : ∀ ω, V (X (t + 1) ω) ≤
        V (X t ω) + @inner ℝ _ _ (gradV (X t ω)) (X (t + 1) ω - X t ω) +
        (L / 2) * ‖X (t + 1) ω - X t ω‖^2 := by
      intro ω
      exact taylor_bound (X t ω) (X (t + 1) ω)

    -- SUB 17g.2: Expand inner product using increment decomposition
    -- ⟨∇V, γ·(-h + ΔM + R)⟩ = -γ⟨∇V, h⟩ + γ⟨∇V, ΔM⟩ + γ⟨∇V, R⟩
    have inner_expand : ∀ ω,
        @inner ℝ _ _ (gradV (X t ω)) (X (t + 1) ω - X t ω) =
        -γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
        γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
        γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) := by
      intro ω
      rw [increment_eq ω]
      -- Use inner_smul_right: ⟨u, r • v⟩ = r * ⟨u, v⟩
      -- Use inner_add_right: ⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩
      -- Use inner_neg_right: ⟨u, -v⟩ = -⟨u, v⟩
      simp only [inner_smul_right, inner_add_right, inner_neg_right]
      ring

    -- SUB 17g.3: Combine Taylor and inner product expansion pointwise
    have pointwise_bound : ∀ ω, V (X (t + 1) ω) ≤
        V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
        γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
        γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) +
        (L / 2) * ‖X (t + 1) ω - X t ω‖^2 := by
      intro ω
      have h1 := taylor_applied ω
      have h2 := inner_expand ω
      calc V (X (t + 1) ω)
          ≤ V (X t ω) + @inner ℝ _ _ (gradV (X t ω)) (X (t + 1) ω - X t ω) +
            (L / 2) * ‖X (t + 1) ω - X t ω‖^2 := h1
        _ = V (X t ω) + (-γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
            γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)) +
            (L / 2) * ‖X (t + 1) ω - X t ω‖^2 := by rw [h2]
        _ = V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
            γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) +
            (L / 2) * ‖X (t + 1) ω - X t ω‖^2 := by ring

    -- SUB 17g.4: Take conditional expectation of pointwise bound
    -- E[V(X_{t+1})|F_t] ≤ V(X_t) - γ⟨∇V, h⟩ + γ·E[⟨∇V, ΔM⟩|F_t] + γ·E[⟨∇V, R⟩|F_t] + (L/2)·E[‖ΔX‖²|F_t]
    have condexp_pointwise :
        μ[fun ω => V (X (t + 1) ω) | ℱ t] ≤ᵐ[μ]
        fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
          γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (ΔM (t + 1) ω') | ℱ t] ω +
          γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
          (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω := by
      -- Apply condExp_mono to pointwise_bound
      -- Pull out F_t-measurable terms using condExp_of_stronglyMeasurable
      -- Key: V(X_t), γ_{t+1}, ⟨∇V(X_t), h(X_t)⟩ are all F_t-measurable

      -- Step 1: Establish needed measurability and integrability facts
      have gradV_cont : Continuous gradV := by
        exact ((LinearIsometryEquiv.continuous _).comp
          (asm.V_smooth.continuous_fderiv (by decide))).congr asm.V_grad_eq
      have hX_sm : StronglyMeasurable[ℱ t] (X t) := asm.X_adapted t
      have V_Xt_meas : StronglyMeasurable[ℱ t] (fun ω => V (X t ω)) :=
        asm.V_smooth.continuous.comp_stronglyMeasurable hX_sm
      have gradV_Xt_meas : StronglyMeasurable[ℱ t] (fun ω => gradV (X t ω)) :=
        gradV_cont.comp_stronglyMeasurable hX_sm
      have h_Xt_meas : StronglyMeasurable[ℱ t] (fun ω => h (X t ω)) :=
        asm.h_continuous.comp_stronglyMeasurable hX_sm
      have inner_h_meas : StronglyMeasurable[ℱ t] (fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω))) :=
        gradV_Xt_meas.inner h_Xt_meas

      -- Step 2: Integrability of V(X_{t+1})
      have V_Xt1_int : Integrable (fun ω => V (X (t + 1) ω)) μ := V'_integrable (t + 1)

      -- Step 3: Integrability of all terms in pointwise_bound RHS
      have V_Xt_int : Integrable (fun ω => V (X t ω)) μ := V'_integrable t
      have one_plus_V_int : Integrable (fun ω => 1 + V (X t ω)) μ :=
        (integrable_const 1).add V_Xt_int

      have inner_h_int : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω))) μ := by
        -- |⟨∇V, h⟩| ≤ ‖∇V‖ * ‖h‖ ≤ (‖∇V‖² + ‖h‖²)/2 ≤ C_growth/2 * (1+V)
        have bound : ∀ ω, |@inner ℝ _ _ (gradV (X t ω)) (h (X t ω))| ≤ C_growth / 2 * (1 + V (X t ω)) := by
          intro ω
          have h1 := abs_real_inner_le_norm (gradV (X t ω)) (h (X t ω))
          have h2 : ‖gradV (X t ω)‖ * ‖h (X t ω)‖ ≤ (‖gradV (X t ω)‖^2 + ‖h (X t ω)‖^2) / 2 := by
            nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖h (X t ω)‖)]
          have h3 := h_growth (X t ω)
          linarith
        have bound_int : Integrable (fun ω => C_growth / 2 * (1 + V (X t ω))) μ :=
          one_plus_V_int.const_mul _
        exact Integrable.mono' bound_int (inner_h_meas.mono (ℱ.le t)).aestronglyMeasurable
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact bound ω)

      have inner_DM_int : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) μ := by
        have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
          have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
          exact Integrable.mono' (one_plus_V_int.const_mul C_growth)
            ((gradV_Xt_meas.norm.pow 2).mono (ℱ.le t)).aestronglyMeasurable
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        have DM_sq_int : Integrable (fun ω => ‖ΔM (t + 1) ω‖^2) μ := asm.martingale_diff_L2 t
        have sum_int : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) / 2) μ :=
          (gradV_sq_int.add DM_sq_int).div_const 2
        have DM_asm : AEStronglyMeasurable (ΔM (t + 1)) μ :=
          ((asm.martingale_diff_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
        have inner_asm : AEStronglyMeasurable
            (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) μ :=
          (gradV_Xt_meas.mono (ℱ.le t)).aestronglyMeasurable.inner DM_asm
        refine Integrable.mono' sum_int inner_asm (ae_of_all _ fun ω => ?_)
        have h1 := abs_real_inner_le_norm (gradV (X t ω)) (ΔM (t + 1) ω)
        have h2 : ‖gradV (X t ω)‖ * ‖ΔM (t + 1) ω‖ ≤ (‖gradV (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2) / 2 := by
          nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖ΔM (t + 1) ω‖)]
        rw [Real.norm_eq_abs]
        linarith

      have inner_R_int : Integrable (fun ω => @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)) μ := by
        have gradV_sq_int : Integrable (fun ω => ‖gradV (X t ω)‖^2) μ := by
          have bound : ∀ ω, ‖gradV (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖h (X t ω)‖]
          exact Integrable.mono' (one_plus_V_int.const_mul C_growth)
            ((gradV_Xt_meas.norm.pow 2).mono (ℱ.le t)).aestronglyMeasurable
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
        have sum_int : Integrable (fun ω => (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2) μ :=
          (gradV_sq_int.add R_sq_int).div_const 2
        have R_asm : AEStronglyMeasurable (R (t + 1)) μ :=
          ((asm.remainder_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable
        have inner_asm : AEStronglyMeasurable
            (fun ω => @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)) μ :=
          (gradV_Xt_meas.mono (ℱ.le t)).aestronglyMeasurable.inner R_asm
        refine Integrable.mono' sum_int inner_asm (ae_of_all _ fun ω => ?_)
        have h1 := abs_real_inner_le_norm (gradV (X t ω)) (R (t + 1) ω)
        have h2 : ‖gradV (X t ω)‖ * ‖R (t + 1) ω‖ ≤ (‖gradV (X t ω)‖^2 + ‖R (t + 1) ω‖^2) / 2 := by
          nlinarith [sq_nonneg (‖gradV (X t ω)‖ - ‖R (t + 1) ω‖)]
        rw [Real.norm_eq_abs]
        linarith

      have norm_sq_int : Integrable (fun ω => ‖X (t + 1) ω - X t ω‖^2) μ := by
        -- Use second_order_bound integrability argument
        have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (t + 1) ω‖^2) μ := asm.martingale_diff_L2 t
        have R_sq_int : Integrable (fun ω => ‖R (t + 1) ω‖^2) μ := asm.remainder_L2 t
        have h_sq_int : Integrable (fun ω => ‖h (X t ω)‖^2) μ := by
          have bound : ∀ ω, ‖h (X t ω)‖^2 ≤ C_growth * (1 + V (X t ω)) := fun ω => by
            have := h_growth (X t ω); linarith [sq_nonneg ‖gradV (X t ω)‖]
          exact Integrable.mono' (one_plus_V_int.const_mul C_growth)
            ((h_Xt_meas.norm.pow 2).mono (ℱ.le t)).aestronglyMeasurable
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        -- ‖ΔX‖² ≤ 3γ²(‖h‖² + ‖ΔM‖² + ‖R‖²)
        have bound : ∀ ω, ‖X (t + 1) ω - X t ω‖^2 ≤ 3 * (γ (t+1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) := by
          intro ω
          rw [increment_eq ω]
          have h1 : ‖γ (t + 1) • (-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω)‖ =
              |γ (t + 1)| * ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖ := norm_smul _ _
          rw [h1]
          -- (|γ| * ‖...‖)² = γ² * ‖...‖²
          have h1' : (|γ (t + 1)| * ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖)^2 =
              (γ (t + 1))^2 * ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖^2 := by
            rw [mul_pow, sq_abs]
          rw [h1']
          have h2 : ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖ ≤ ‖h (X t ω)‖ + ‖ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖ := by
            calc ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖
                ≤ ‖-h (X t ω) + ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖ := norm_add_le _ _
              _ ≤ ‖-h (X t ω)‖ + ‖ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖ := by linarith [norm_add_le (-h (X t ω)) (ΔM (t + 1) ω)]
              _ = ‖h (X t ω)‖ + ‖ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖ := by rw [norm_neg]
          have h3 : (‖h (X t ω)‖ + ‖ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖)^2 ≤ 3 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) := by
            nlinarith [sq_nonneg ‖h (X t ω)‖, sq_nonneg ‖ΔM (t + 1) ω‖, sq_nonneg ‖R (t + 1) ω‖,
                      sq_nonneg (‖h (X t ω)‖ - ‖ΔM (t + 1) ω‖), sq_nonneg (‖h (X t ω)‖ - ‖R (t + 1) ω‖),
                      sq_nonneg (‖ΔM (t + 1) ω‖ - ‖R (t + 1) ω‖)]
          calc (γ (t + 1))^2 * ‖-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω‖^2
              ≤ (γ (t + 1))^2 * (‖h (X t ω)‖ + ‖ΔM (t + 1) ω‖ + ‖R (t + 1) ω‖)^2 := by
                apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
                apply sq_le_sq' _ h2
                linarith [norm_nonneg (-h (X t ω) + ΔM (t + 1) ω + R (t + 1) ω)]
            _ ≤ (γ (t + 1))^2 * (3 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) := by
                apply mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
            _ = 3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2) := by ring
        have bound_int : Integrable (fun ω => 3 * (γ (t + 1))^2 * (‖h (X t ω)‖^2 + ‖ΔM (t + 1) ω‖^2 + ‖R (t + 1) ω‖^2)) μ := by
          apply Integrable.const_mul
          exact (h_sq_int.add DeltaM_sq_int).add R_sq_int
        have diff_asm : AEStronglyMeasurable (fun ω => X (t + 1) ω - X t ω) μ :=
          ((asm.X_adapted (t+1)).mono (ℱ.le (t+1))).aestronglyMeasurable.sub
            (hX_sm.mono (ℱ.le t)).aestronglyMeasurable
        exact Integrable.mono' bound_int (diff_asm.norm.pow 2)
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)

      -- Step 4: Integrability of pointwise_bound RHS
      have rhs_int : Integrable (fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
          γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
          γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) +
          (L / 2) * ‖X (t + 1) ω - X t ω‖^2) μ := by
        apply Integrable.add
        apply Integrable.add
        apply Integrable.add
        · exact V_Xt_int.sub (inner_h_int.const_mul _)
        · exact inner_DM_int.const_mul _
        · exact inner_R_int.const_mul _
        · exact norm_sq_int.const_mul _

      -- Step 5: Apply condExp_mono
      have mono_step := condExp_mono (m := ℱ t) V_Xt1_int rhs_int (ae_of_all _ pointwise_bound)

      -- Step 6: Rewrite condExp of RHS using linearity and pullout
      -- E[V(X_t) - γ⟨∇V,h⟩ + γ⟨∇V,ΔM⟩ + γ⟨∇V,R⟩ + (L/2)‖ΔX‖² | F_t]
      -- = V(X_t) - γ⟨∇V,h⟩ + γ·E[⟨∇V,ΔM⟩|F_t] + γ·E[⟨∇V,R⟩|F_t] + (L/2)·E[‖ΔX‖²|F_t]

      -- Use condExp linearity lemmas (all are =ᵐ[μ] relations)
      -- Get the condexp rewrite lemmas for F_t-measurable functions (these are true equalities)
      have hVXt : μ[fun ω => V (X t ω) | ℱ t] = fun ω => V (X t ω) :=
        condExp_of_stronglyMeasurable (ℱ.le t) V_Xt_meas V_Xt_int
      have hinnerh : μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) | ℱ t] =
          fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) :=
        condExp_of_stronglyMeasurable (ℱ.le t) inner_h_meas inner_h_int

      -- Build all the =ᵐ[μ] steps for condExp linearity
      have step1 := condExp_add (m := ℱ t)
        (((V_Xt_int.sub (inner_h_int.const_mul (γ (t+1)))).add (inner_DM_int.const_mul (γ (t+1)))).add (inner_R_int.const_mul (γ (t+1))))
        (norm_sq_int.const_mul (L/2))
      have step2 := condExp_add (m := ℱ t)
        ((V_Xt_int.sub (inner_h_int.const_mul (γ (t+1)))).add (inner_DM_int.const_mul (γ (t+1))))
        (inner_R_int.const_mul (γ (t+1)))
      have step3 := condExp_add (m := ℱ t)
        (V_Xt_int.sub (inner_h_int.const_mul (γ (t+1))))
        (inner_DM_int.const_mul (γ (t+1)))
      have step4 := condExp_sub (m := ℱ t) V_Xt_int (inner_h_int.const_mul (γ (t+1)))
      have smul_DM := condExp_smul (μ := μ) (γ (t + 1)) (fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω)) (ℱ t)
      have smul_R := condExp_smul (μ := μ) (γ (t + 1)) (fun ω => @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω)) (ℱ t)
      have smul_norm := condExp_smul (μ := μ) (L / 2) (fun ω => ‖X (t + 1) ω - X t ω‖^2) (ℱ t)
      have smul_h := condExp_smul (μ := μ) (γ (t + 1)) (fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω))) (ℱ t)

      -- Now filter_upwards with mono_step and all the =ᵐ[μ] conditions
      filter_upwards [mono_step, step1, step2, step3, step4, smul_DM, smul_R, smul_norm, smul_h]
        with ω hω h1 h2 h3 h4 hsDM hsR hsnorm hsh
      -- hω : μ[V(X_{t+1})|F_t](ω) ≤ μ[RHS|F_t](ω)
      -- h1-h4, hs* : pointwise versions of the =ᵐ[μ] equalities at ω

      -- Extract pointwise values
      have eq_VXt : μ[fun ω => V (X t ω) | ℱ t] ω = V (X t ω) := congrFun hVXt ω
      have eq_innerh : μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) | ℱ t] ω =
          @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) := congrFun hinnerh ω

      -- Simplify smul to mul in the smul hypotheses
      simp only [Pi.smul_apply, smul_eq_mul] at hsDM hsR hsnorm hsh
      simp only [Pi.add_apply] at h1 h2 h3
      simp only [Pi.sub_apply] at h4

      -- key_eq combines all the condExp linearity facts
      -- E[a-b+c+d+e|F] = E[a|F] - E[b|F] + E[c|F] + E[d|F] + E[e|F]
      -- where E[a|F] = a and E[b|F] = b for F-measurable a,b, and E[c*f|F] = c*E[f|F]
      -- This follows from h1-h4 (condExp_add/sub), hsDM/hsR/hsnorm/hsh (condExp_smul),
      -- and eq_VXt/eq_innerh (condExp_of_stronglyMeasurable)
      have key_eq : μ[fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
              γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
              γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) +
              (L / 2) * ‖X (t + 1) ω - X t ω‖^2 | ℱ t] ω =
          V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
              γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (ΔM (t + 1) ω') | ℱ t] ω +
              γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
              (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω := by
        -- This follows from h1-h4 (condExp_add/sub at ω), hsDM/hsR/hsnorm/hsh (condExp_smul at ω),
        -- and eq_VXt/eq_innerh (condExp_of_stronglyMeasurable at ω).
        -- The proof is tedious due to definitional equality issues between function representations.
        -- First, establish function equalities to bridge `c * f(ω)` and `(c • f) ω`
        have smul_eq_DM : μ[fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (ΔM (t + 1) x) | ℱ t] ω =
            γ (t + 1) * μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) | ℱ t] ω := by
          have h' : (fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (ΔM (t + 1) x)) =
              γ (t + 1) • fun ω => @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) := by
            ext ω'; simp [Pi.smul_apply, smul_eq_mul]
          simp only [h', hsDM]
        have smul_eq_R : μ[fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (R (t + 1) x) | ℱ t] ω =
            γ (t + 1) * μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) | ℱ t] ω := by
          have h' : (fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (R (t + 1) x)) =
              γ (t + 1) • fun ω => @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) := by
            ext ω'; simp [Pi.smul_apply, smul_eq_mul]
          simp only [h', hsR]
        have smul_eq_norm : μ[fun x => (L / 2) * ‖X (t + 1) x - X t x‖^2 | ℱ t] ω =
            (L / 2) * μ[fun ω => ‖X (t + 1) ω - X t ω‖^2 | ℱ t] ω := by
          have h' : (fun x => (L / 2) * ‖X (t + 1) x - X t x‖^2) =
              (L / 2) • fun ω => ‖X (t + 1) ω - X t ω‖^2 := by
            ext ω'; simp [Pi.smul_apply, smul_eq_mul]
          simp only [h', hsnorm]
        have smul_eq_h : μ[fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (h (X t x)) | ℱ t] ω =
            γ (t + 1) * μ[fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) | ℱ t] ω := by
          have h' : (fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (h (X t x))) =
              γ (t + 1) • fun ω => @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) := by
            ext ω'; simp [Pi.smul_apply, smul_eq_mul]
          simp only [h', hsh]
        -- Establish function equality between the original form and the nested form
        have fun_eq : (fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
                γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (ΔM (t + 1) ω) +
                γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (R (t + 1) ω) +
                (L / 2) * ‖X (t + 1) ω - X t ω‖^2) =
            ((((fun ω => V (X t ω)) - fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (h (X t x))) +
                fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (ΔM (t + 1) x)) +
                fun x => γ (t + 1) * @inner ℝ _ _ (gradV (X t x)) (R (t + 1) x)) +
                fun x => (L / 2) * ‖X (t + 1) x - X t x‖^2 := by
          ext ω'; simp only [Pi.add_apply, Pi.sub_apply]
        rw [congrArg (fun f => μ[f | ℱ t] ω) fun_eq]
        rw [h1, h2, h3, h4]
        rw [smul_eq_DM, smul_eq_R, smul_eq_norm, smul_eq_h]
        rw [eq_VXt, eq_innerh]
      linarith [hω, key_eq]

    -- SUB 17g.5: Substitute martingale cancellation
    -- γ·E[⟨∇V, ΔM⟩|F_t] = γ·0 = 0
    have after_martingale :
        μ[fun ω => V (X (t + 1) ω) | ℱ t] ≤ᵐ[μ]
        fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
          γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
          (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω := by
      -- Use martingale_inner_zero: E[⟨∇V, ΔM⟩|F_t] =ᵐ 0
      -- Substitute and simplify
      filter_upwards [condexp_pointwise, martingale_inner_zero] with ω hcondexp hmart
      -- hcondexp : μ[V ∘ X(t+1)|F_t](ω) ≤ V(X_t ω) - γ⟨∇V,h⟩ + γ·E[⟨∇V,ΔM⟩](ω) + γ·E[⟨∇V,R⟩](ω) + (L/2)E[‖ΔX‖²](ω)
      -- hmart : E[⟨∇V,ΔM⟩|F_t](ω) = 0
      simp only [Pi.zero_apply] at hmart
      -- Rewrite hcondexp using hmart
      rw [hmart, mul_zero, add_zero] at hcondexp
      exact hcondexp

    -- Define the coefficient C' for cleaner proofs
    let C' := Real.sqrt (C_growth * C_rem) + (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t+1))^2)

    -- SUB 17g.6: Apply remainder and second-order bounds
    -- Remainder: γ·E[⟨∇V, R⟩|F_t] ≤ γ·|E[⟨∇V, R⟩|F_t]| ≤ √(C_growth·C_rem)·γ²·(1+V)
    -- Second-order: (L/2)·E[‖ΔX‖²|F_t] ≤ (3L/2)·γ²·(C_growth + C_mart + C_rem·γ²)·(1+V)
    have after_bounds :
        μ[fun ω => V (X (t + 1) ω) | ℱ t] ≤ᵐ[μ]
        fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
          C' * (γ (t + 1))^2 * (1 + V (X t ω)) := by
      -- Combine remainder_inner_bound and second_order_bound
      -- Note: The remainder bound gives |E[⟨∇V, R⟩|F_t]| ≤ √(C_growth·C_rem)·γ·(1+V)
      -- Multiplied by γ gives √(C_growth·C_rem)·γ²·(1+V)
      -- Use: |E[f]| ≤ E[|f|] for signed quantities
      filter_upwards [after_martingale, remainder_inner_bound, second_order_bound] with ω hmart hrem hsec
      -- hmart: μ[V(X_{t+1})|F_t](ω) ≤ V(X_t ω) - γ⟨∇V,h⟩ + γ·E[⟨∇V,R⟩](ω) + (L/2)·E[‖ΔX‖²](ω)
      -- hrem: |E[⟨∇V,R⟩|F_t](ω)| ≤ √(C_growth·C_rem)·γ·(1+V)
      -- hsec: E[‖ΔX‖²|F_t](ω) ≤ 3γ²(C_growth + C_mart + C_rem·γ²)(1+V)
      -- Step 1: Bound the remainder term using le_abs_self
      have hrem_bound : γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω ≤
          γ (t + 1) * (Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω))) := by
        have h1 : μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω ≤
            |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω| := le_abs_self _
        have h2 : |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω| ≤
            Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω)) := hrem
        have hγ_nonneg : 0 ≤ γ (t + 1) := le_of_lt (asm.gamma_pos (t + 1))
        calc γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω
            ≤ γ (t + 1) * |μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω| := by
              apply mul_le_mul_of_nonneg_left h1 hγ_nonneg
          _ ≤ γ (t + 1) * (Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω))) := by
              apply mul_le_mul_of_nonneg_left h2 hγ_nonneg
      -- Simplify the remainder bound: γ * (√(C_growth*C_rem) * γ * (1+V)) = √(C_growth*C_rem) * γ² * (1+V)
      have hrem_simp : γ (t + 1) * (Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω))) =
          Real.sqrt (C_growth * C_rem) * (γ (t + 1))^2 * (1 + V (X t ω)) := by ring
      -- Step 2: Bound the second-order term
      have hsec_bound : (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω ≤
          (L / 2) * (3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω))) := by
        have hL_nonneg : 0 ≤ L / 2 := by linarith
        exact mul_le_mul_of_nonneg_left hsec hL_nonneg
      -- Simplify: (L/2) * 3 * γ² * (...) * (1+V) = (3L/2) * γ² * (...) * (1+V)
      have hsec_simp : (L / 2) * (3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω))) =
          (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (γ (t + 1))^2 * (1 + V (X t ω)) := by ring
      -- Step 3: Combine the bounds
      have combined : γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
          (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω ≤
          Real.sqrt (C_growth * C_rem) * (γ (t + 1))^2 * (1 + V (X t ω)) +
          (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (γ (t + 1))^2 * (1 + V (X t ω)) := by
        calc γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
            (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω
            ≤ γ (t + 1) * (Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω))) +
              (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω := by linarith [hrem_bound]
          _ ≤ γ (t + 1) * (Real.sqrt (C_growth * C_rem) * (γ (t + 1)) * (1 + V (X t ω))) +
              (L / 2) * (3 * (γ (t + 1))^2 * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (1 + V (X t ω))) := by
              linarith [hsec_bound]
          _ = Real.sqrt (C_growth * C_rem) * (γ (t + 1))^2 * (1 + V (X t ω)) +
              (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (γ (t + 1))^2 * (1 + V (X t ω)) := by
              rw [hrem_simp, hsec_simp]
      -- Step 4: Factor out to get C' * γ² * (1+V)
      have factor_eq : Real.sqrt (C_growth * C_rem) * (γ (t + 1))^2 * (1 + V (X t ω)) +
          (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (γ (t + 1))^2 * (1 + V (X t ω)) =
          C' * (γ (t + 1))^2 * (1 + V (X t ω)) := by
        simp only [C']
        ring
      -- Final calculation
      calc μ[fun ω' => V (X (t + 1) ω') | ℱ t] ω
          ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            γ (t + 1) * μ[fun ω' => @inner ℝ _ _ (gradV (X t ω')) (R (t + 1) ω') | ℱ t] ω +
            (L / 2) * μ[fun ω' => ‖X (t + 1) ω' - X t ω'‖^2 | ℱ t] ω := hmart
        _ ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            (Real.sqrt (C_growth * C_rem) * (γ (t + 1))^2 * (1 + V (X t ω)) +
            (3 * L / 2) * (C_growth + C_mart + C_rem * (γ (t + 1))^2) * (γ (t + 1))^2 * (1 + V (X t ω))) := by
            linarith [combined]
        _ = V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C' * (γ (t + 1))^2 * (1 + V (X t ω)) := by rw [factor_eq]

    -- SUB 17g.7: Apply (1+V) ≤ (1+1/m)·V bound

    have hC'_nonneg : 0 ≤ C' := by
      simp only [C']
      apply add_nonneg
      · exact Real.sqrt_nonneg _
      · apply mul_nonneg
        · linarith
        · have h1 : 0 ≤ C_growth := le_of_lt hC_growth_pos
          have h2 : 0 ≤ C_mart := le_of_lt hC_mart_pos
          have h3 : 0 ≤ C_rem := le_of_lt hC_rem_pos
          have h4 : 0 ≤ (γ (t+1))^2 := sq_nonneg _
          nlinarith [mul_nonneg h3 h4]

    have after_one_plus_V :
        μ[fun ω => V (X (t + 1) ω) | ℱ t] ≤ᵐ[μ]
        fun ω => V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
          C' * (1 + 1/m) * (γ (t + 1))^2 * V (X t ω) := by
      -- Apply one_plus_V_bound: (1+V) ≤ (1+1/m)·V
      filter_upwards [after_bounds] with ω hω
      have hVbound := one_plus_V_bound (X t ω)
      have h_gamma_sq_nonneg : 0 ≤ (γ (t + 1))^2 := sq_nonneg _
      have hV_nonneg := V'_nonneg t ω
      -- Chain: C' * γ² * (1+V) ≤ C' * γ² * (1+1/m) * V
      have key : C' * (γ (t + 1))^2 * (1 + V (X t ω)) ≤
                 C' * (γ (t + 1))^2 * ((1 + 1/m) * V (X t ω)) := by
        apply mul_le_mul_of_nonneg_left hVbound
        exact mul_nonneg hC'_nonneg h_gamma_sq_nonneg
      calc μ[fun ω' => V (X (t + 1) ω') | ℱ t] ω
          ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C' * (γ (t + 1))^2 * (1 + V (X t ω)) := hω
        _ ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C' * (γ (t + 1))^2 * ((1 + 1/m) * V (X t ω)) := by linarith [key]
        _ = V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C' * (1 + 1/m) * (γ (t + 1))^2 * V (X t ω) := by ring

    -- SUB 17g.8: Show coefficient is bounded by C_drift
    -- C_drift = 4·(L + C_growth + C_mart + C_rem)·(1+1/m)
    -- Need: (√(C_growth·C_rem) + (3L/2)(C_growth + C_mart + C_rem·γ²))·(1+1/m) ≤ C_drift
    have coeff_bound : ∀ γ' : ℝ, 0 ≤ γ' → γ' ≤ 1 →
        (Real.sqrt (C_growth * C_rem) + (3 * L / 2) * (C_growth + C_mart + C_rem * γ'^2)) *
        (1 + 1/m) ≤ C_drift := by
      intro γ' hγ'_nonneg hγ'_le_one
      -- Step 1: AM-GM gives √(C_growth·C_rem) ≤ (C_growth + C_rem)/2
      have hC_growth_nonneg : 0 ≤ C_growth := le_of_lt hC_growth_pos
      have hC_rem_nonneg : 0 ≤ C_rem := le_of_lt hC_rem_pos
      have hC_mart_nonneg : 0 ≤ C_mart := le_of_lt hC_mart_pos
      have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
      have ham_gm : Real.sqrt (C_growth * C_rem) ≤ (C_growth + C_rem) / 2 := by
        have h := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (0:ℝ) ≤ 1/2) hC_growth_nonneg hC_rem_nonneg (by norm_num : (1:ℝ)/2 + 1/2 = 1)
        simp only [Real.rpow_natCast] at h
        calc Real.sqrt (C_growth * C_rem)
            = Real.sqrt C_growth * Real.sqrt C_rem := Real.sqrt_mul hC_growth_nonneg C_rem
          _ = C_growth ^ (1/2 : ℝ) * C_rem ^ (1/2 : ℝ) := by
              rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
          _ ≤ (1/2) * C_growth + (1/2) * C_rem := h
          _ = (C_growth + C_rem) / 2 := by ring
      -- Step 2: γ'² ≤ 1 implies C_rem · γ'² ≤ C_rem
      have hγ'_sq_le : γ'^2 ≤ 1 := by
        calc γ'^2 ≤ 1^2 := sq_le_sq' (by linarith) hγ'_le_one
          _ = 1 := one_pow 2
      have hC_rem_γ'_le : C_rem * γ'^2 ≤ C_rem := by
        calc C_rem * γ'^2 ≤ C_rem * 1 := mul_le_mul_of_nonneg_left hγ'_sq_le hC_rem_nonneg
          _ = C_rem := mul_one C_rem
      -- Step 3: Bound the sum (C_growth + C_mart + C_rem * γ'^2) ≤ (C_growth + C_mart + C_rem)
      have hsum_le : C_growth + C_mart + C_rem * γ'^2 ≤ C_growth + C_mart + C_rem := by linarith
      -- Step 4: Bound the LHS coefficient
      -- LHS = √(C_growth·C_rem) + (3L/2)(C_growth + C_mart + C_rem·γ²)
      --     ≤ (C_growth + C_rem)/2 + (3L/2)(C_growth + C_mart + C_rem)
      have hcoeff_le : Real.sqrt (C_growth * C_rem) + (3 * L / 2) * (C_growth + C_mart + C_rem * γ'^2) ≤
          (C_growth + C_rem) / 2 + (3 * L / 2) * (C_growth + C_mart + C_rem) := by
        have h1 : (3 * L / 2) * (C_growth + C_mart + C_rem * γ'^2) ≤
            (3 * L / 2) * (C_growth + C_mart + C_rem) := by
          apply mul_le_mul_of_nonneg_left hsum_le
          linarith
        linarith [ham_gm, h1]
      -- Step 5: Show that this upper bound is ≤ 4(1+L)(L + C_growth + C_mart + C_rem)
      -- With the (1+L) factor, the bound holds for all L ≥ 0:
      -- LHS = (C_g + C_r)/2 + (3L/2)S where S = C_g + C_m + C_r
      -- RHS = 4(1+L)(L + S) = 4L + 4S + 4L² + 4LS
      -- Since (C_g + C_r)/2 ≤ S, LHS ≤ S + (3/2)LS = S(1 + 3L/2)
      -- We need: S(1 + 3L/2) ≤ 4L + 4S + 4L² + 4LS
      -- i.e., 0 ≤ 4L + 3S + 4L² + (5/2)LS, which is true for L,S ≥ 0
      have hbound : (C_growth + C_rem) / 2 + (3 * L / 2) * (C_growth + C_mart + C_rem) ≤
          4 * (1 + L) * (L + C_growth + C_mart + C_rem) := by
        -- Let S = C_growth + C_mart + C_rem
        set S := C_growth + C_mart + C_rem with hS_def
        have hS_pos : 0 < S := by linarith
        have hS_nonneg : 0 ≤ S := le_of_lt hS_pos
        have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
        -- Step 5a: (C_growth + C_rem)/2 ≤ S/2 since C_growth + C_rem ≤ S
        have h_sum_le_S : C_growth + C_rem ≤ S := by simp only [hS_def]; linarith
        have h_half_le : (C_growth + C_rem) / 2 ≤ S / 2 := by linarith
        -- Step 5b: Upper bound LHS by S/2 + (3L/2)S = S(1/2 + 3L/2)
        have hLHS_le : (C_growth + C_rem) / 2 + (3 * L / 2) * S ≤ S * (1/2 + 3*L/2) := by
          calc (C_growth + C_rem) / 2 + (3 * L / 2) * S
              ≤ S / 2 + (3 * L / 2) * S := by linarith
            _ = S * (1/2 + 3*L/2) := by ring
        -- Step 5c: Expand RHS = 4(1+L)(L+S) = 4L + 4S + 4L² + 4LS
        have hRHS_eq : 4 * (1 + L) * (L + S) = 4*L + 4*S + 4*L^2 + 4*L*S := by ring
        -- Step 5d: Show S(1/2 + 3L/2) ≤ 4L + 4S + 4L² + 4LS
        -- i.e., S/2 + 3LS/2 ≤ 4L + 4S + 4L² + 4LS
        -- i.e., 0 ≤ 4L + 7S/2 + 4L² + 5LS/2, which is true
        have h_final : S * (1/2 + 3*L/2) ≤ 4*L + 4*S + 4*L^2 + 4*L*S := by
          have h1 : S * (1/2 + 3*L/2) = S/2 + 3*L*S/2 := by ring
          have h2 : 0 ≤ 4*L + 7*S/2 + 4*L^2 + 5*L*S/2 := by
            have := sq_nonneg L
            nlinarith [sq_nonneg L, sq_nonneg S]
          linarith
        calc (C_growth + C_rem) / 2 + (3 * L / 2) * (C_growth + C_mart + C_rem)
            = (C_growth + C_rem) / 2 + (3 * L / 2) * S := by simp only [hS_def]
          _ ≤ S * (1/2 + 3*L/2) := hLHS_le
          _ ≤ 4*L + 4*S + 4*L^2 + 4*L*S := h_final
          _ = 4 * (1 + L) * (L + S) := by ring
          _ = 4 * (1 + L) * (L + C_growth + C_mart + C_rem) := by
            show 4 * (1 + L) * (L + (C_growth + C_mart + C_rem)) =
                 4 * (1 + L) * (L + C_growth + C_mart + C_rem)
            ring
      -- Step 6: Multiply by (1 + 1/m) ≥ 1
      have hm_nonneg : 0 ≤ m := le_of_lt hm_pos
      have h_one_plus_inv_m_pos : 0 < 1 + 1/m := by
        have : 0 ≤ 1/m := div_nonneg (by norm_num : (0:ℝ) ≤ 1) hm_nonneg
        linarith
      calc (Real.sqrt (C_growth * C_rem) + (3 * L / 2) * (C_growth + C_mart + C_rem * γ'^2)) * (1 + 1/m)
          ≤ ((C_growth + C_rem) / 2 + (3 * L / 2) * (C_growth + C_mart + C_rem)) * (1 + 1/m) := by
            apply mul_le_mul_of_nonneg_right hcoeff_le (le_of_lt h_one_plus_inv_m_pos)
        _ ≤ (4 * (1 + L) * (L + C_growth + C_mart + C_rem)) * (1 + 1/m) := by
            apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_one_plus_inv_m_pos)
        _ = C_drift := by ring

    -- SUB 17g.9: Final assembly to match RS format
    -- Goal: E[V'(t+1)|F_t] ≤ (1 + α'(t+1)) * V'(t) + β'(t+1) - U'(t+1)
    -- Where: α' = C_drift·γ², β' = 0, U' = γ·⟨∇V, h⟩
    have final_bound :
        μ[fun ω => V (X (t + 1) ω) | ℱ t] ≤ᵐ[μ]
        fun ω => (1 + C_drift * (γ (t + 1))^2) * V (X t ω) + 0 -
          γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) := by
      filter_upwards [after_one_plus_V] with ω hω
      have hV_nonneg := V'_nonneg t ω
      have h_gamma_sq_nonneg : 0 ≤ (γ (t + 1))^2 := sq_nonneg _
      -- Show C' * (1+1/m) ≤ C_drift
      have hC'_bound : C' * (1 + 1/m) ≤ C_drift := by
        have hcoeff := coeff_bound (γ (t + 1)) (le_of_lt (asm.gamma_pos (t + 1))) (asm.gamma_le_one (t + 1))
        exact hcoeff
      -- Then C' * (1+1/m) * γ² * V ≤ C_drift * γ² * V
      have key : C' * (1 + 1/m) * (γ (t + 1))^2 * V (X t ω) ≤
                 C_drift * (γ (t + 1))^2 * V (X t ω) := by
        apply mul_le_mul_of_nonneg_right
        apply mul_le_mul_of_nonneg_right hC'_bound h_gamma_sq_nonneg
        exact hV_nonneg
      calc μ[fun ω' => V (X (t + 1) ω') | ℱ t] ω
          ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C' * (1 + 1/m) * (γ (t + 1))^2 * V (X t ω) := hω
        _ ≤ V (X t ω) - γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) +
            C_drift * (γ (t + 1))^2 * V (X t ω) := by nlinarith [key, hV_nonneg, h_gamma_sq_nonneg]
        _ = (1 + C_drift * (γ (t + 1))^2) * V (X t ω) + 0 -
            γ (t + 1) * @inner ℝ _ _ (gradV (X t ω)) (h (X t ω)) := by ring

    -- Convert to RS format using the definitions
    -- The goal is: μ[V'(t+1)|ℱ t] ≤ᵐ (1 + α'(t+1)) * V'(t) + β'(t+1) - U'(t+1)
    -- Expanding definitions:
    -- V'(t+1)(ω) = V(X(t+1)(ω))
    -- α'(t+1)(ω) = C_drift * γ(t+1)²
    -- β'(t+1)(ω) = 0
    -- U'(t+1)(ω) = γ(t+1) * ⟨∇V(X_t), h(X_t)⟩ (since t+1 ≠ 0)
    filter_upwards [final_bound] with ω hω
    simp only [V', α', β', U', Nat.add_sub_cancel, add_zero]
    -- The if condition (t + 1 = 0) is false, so U'(t+1) = γ(t+1) * ⟨∇V(X_t), h(X_t)⟩
    have ht_ne_zero : t + 1 ≠ 0 := Nat.succ_ne_zero t
    simp only [ht_ne_zero, ↓reduceIte]
    -- hω has "+ 0 -" but goal has just "-", simplify the + 0
    simp only [add_zero] at hω
    exact hω

  -- =====================================================
  -- APPLY ROBBINS-SIEGMUND THEOREM
  -- =====================================================
  have hRS := robbinsSiegmund_full μ ℱ V' U' α' β'
    V'_adapted α'_adapted β'_adapted U'_adapted
    α'_predictable β'_predictable U'_predictable
    V'_nonneg α'_nonneg β'_nonneg U'_nonneg
    V'_integrable β'_integrable U'_integrable
    prod_bound sum_Eβ condexp_ineq

  -- Unpack RS conclusions
  obtain ⟨⟨V_lim, hV_lim_int, hV_lim_tend⟩, hV_sup, hU_sum⟩ := hRS

  -- =====================================================
  -- BUILD SGD CONCLUSIONS FROM RS CONCLUSIONS
  -- =====================================================
  refine ⟨?conc_a, ?conc_b, ?conc_c, ?conc_d_as, ?conc_d_L2⟩

  -- Conclusion (a): sup E[V(X_n)] < ∞
  case conc_a =>
    exact hV_sup

  -- =====================================================
  -- SUBTASK 18: Conclusion (b) - Transfer summability of U' to drift term
  -- RS gives: ∑_{t≥0} U'_t < ∞ a.s.
  -- U'_{t+1} = γ_{t+1} * ⟨∇V(X_t), h(X_t)⟩
  -- So ∑_{n≥0} γ_{n+1} ⟨∇V(X_n), h(X_n)⟩ < ∞ a.s.
  -- =====================================================
  case conc_b =>
    -- SANITY CHECK PASSED (trivial index manipulation)
    /-
    ## Proof Sketch for conc_b

    **Goal:** ∀ᵐ ω ∂μ, Summable (fun n => γ (n + 1) * inner (gradV (X n ω)) (h (X n ω)))

    **Given:** hU_sum : ∀ᵐ ω ∂μ, Summable (fun t => U' t ω)

    **Proof:**
    Step 1: Observe that U'(n+1) = γ(n+1) * ⟨gradV(X n), h(X n)⟩
      - For n+1 ≠ 0 (always true), U' definition gives:
        U' (n+1) ω = γ (n+1) * inner (gradV (X ((n+1)-1) ω)) (h (X ((n+1)-1) ω))
                   = γ (n+1) * inner (gradV (X n ω)) (h (X n ω))

    Step 2: From Summable (U' · ω), deduce Summable (fun n => U' (n+1) ω)
      - Use summable_nat_add_iff: Summable (f · + k) ↔ Summable f
      - Apply .mpr direction with k = 1

    Step 3: Conclude by function equality
      - fun n => γ (n + 1) * inner (gradV (X n ω)) (h (X n ω)) = fun n => U' (n+1) ω

    **Mathlib theorems:**
    - summable_nat_add_iff : Summable (fun n => f (n + k)) ↔ Summable f
    - filter_upwards for a.e. reasoning
    -/
    -- Step 1: Work a.e. using filter_upwards
    filter_upwards [hU_sum] with ω hω_sum
    -- Step 2: Show U' (n+1) equals the target function
    -- SUB 18.1: Use summable_nat_add_iff and convert function equality
    -- Proof: (summable_nat_add_iff 1).2 gives Summable (fun n => U' (n + 1) ω)
    -- Then convert using the definition of U' with n+1 ≠ 0
    -- Mathlib: summable_nat_add_iff, Summable.of_eq, funext
    -- Convert using Summable.congr: if f =ᶠ g then Summable f ↔ Summable g
    apply Summable.congr ((summable_nat_add_iff (1 : ℕ)).mpr hω_sum)
    intro n
    -- Show: U' (n+1) ω = γ (n+1) * inner ...
    -- U' is defined as: if n = 0 then 0 else γ n * inner (gradV (X (n-1) ω)) (h (X (n-1) ω))
    -- For n+1: if (n+1) = 0 then 0 else γ (n+1) * inner (gradV (X ((n+1)-1) ω)) (h (X ((n+1)-1) ω))
    -- Since n+1 ≠ 0, this equals: γ (n+1) * inner (gradV (X n ω)) (h (X n ω))
    show (if n + 1 = 0 then 0 else γ (n + 1) * @inner ℝ _ _ (gradV (X ((n + 1) - 1) ω)) (h (X ((n + 1) - 1) ω)))
       = γ (n + 1) * @inner ℝ _ _ (gradV (X n ω)) (h (X n ω))
    rw [if_neg (Nat.add_one_ne_zero n), Nat.add_sub_cancel]

  -- Conclusion (c): V(X_n) → V_∞ ∈ L¹ a.s.
  case conc_c =>
    exact ⟨V_lim, hV_lim_int, hV_lim_tend⟩

  -- =====================================================
  -- SUBTASK 19: Conclusion (d) part 1 - X_{n+1} - X_n → 0 a.s.
  -- Uses: ‖X_{n+1} - X_n‖ = γ_{n+1} ‖-h(X_n) + ΔM_{n+1} + R_{n+1}‖
  -- And: γ_n → 0 (from gamma_sq_sum_fin), bounded moments
  --
  -- SANITY CHECK PASSED
  -- =====================================================
  /-
  ## Informal Proof of conc_d_as

  **Goal:** X_{n+1} - X_n → 0 a.s.

  **Step 1: Decompose the increment**
  From the stochastic algorithm (proc): X_{n+1} - X_n = γ_{n+1}(-h(X_n) + ΔM_{n+1} + R_{n+1})
  So: ‖X_{n+1} - X_n‖ ≤ γ_{n+1}(‖h(X_n)‖ + ‖ΔM_{n+1}‖ + ‖R_{n+1}‖)

  **Step 2: Show γ_n → 0**
  From gamma_sq_sum_fin: ∑γ_n² < ∞ implies γ_n² → 0, hence γ_n → 0.
  (Use: Summable.tendsto_atTop_zero)

  **Step 3: Show ‖h(X_n)‖ is a.s. bounded**
  From hV_lim_tend: V(X_n) → V_∞ a.s.
  Convergent sequences are bounded: ∃ M, V(X_n(ω)) ≤ M for a.e. ω.
  From growth_bound: ‖h(x)‖² ≤ C(1 + V(x))
  Therefore: ‖h(X_n(ω))‖² ≤ C(1 + M) for a.e. ω.
  Combined with γ_n → 0: γ_n ‖h(X_n)‖ → 0 a.s.

  **Step 4: Show γ_n ΔM_n → 0 a.s. (Martingale convergence)**
  Define S_n = ∑_{k=1}^n γ_k ΔM_k. This is an L² martingale.
  E[‖S_n‖²] = E[∑_{k=1}^n ‖γ_k ΔM_k‖²] (orthogonality of increments)
           ≤ ∑_{k=1}^n γ_k² E[‖ΔM_k‖²]
           ≤ ∑_{k=1}^n γ_k² C(1 + sup E[V(X_{k-1})])
           ≤ C' ∑_{k=1}^∞ γ_k² < ∞
  By L² bounded martingale convergence: S_n converges a.s.
  Convergent series have terms → 0: γ_n ΔM_n → 0 a.s.

  **Step 5: Show γ_n R_n → 0 a.s. (Borel-Cantelli)**
  E[‖R_{n+1}‖² | F_n] ≤ C γ_{n+1}² (1 + V(X_n))
  E[‖R_{n+1}‖²] ≤ C γ_{n+1}² (1 + sup E[V(X_n)]) = C' γ_{n+1}²
  E[‖γ_{n+1} R_{n+1}‖²] ≤ C' γ_{n+1}⁴
  ∑ E[‖γ_n R_n‖²] ≤ C' ∑ γ_n⁴ ≤ C' (∑ γ_n²)² < ∞
  By Chebyshev + Borel-Cantelli: γ_n R_n → 0 a.s.

  **Step 6: Combine**
  ‖X_{n+1} - X_n‖ ≤ γ_{n+1}(‖h(X_n)‖ + ‖ΔM_{n+1}‖ + ‖R_{n+1}‖)
  Each term → 0 a.s., so X_{n+1} - X_n → 0 a.s.  ∎
  -/
  -- =====================================================
  -- REVISED PROOF using Tonelli-based argument
  -- (replaces ~2400 lines of martingale convergence machinery)
  --
  -- Key insight: ∑ E[‖ΔX_n‖²] < ∞ implies ∑ ‖ΔX_n(ω)‖² < ∞ a.s. (Tonelli)
  -- Then: convergent series has terms → 0
  -- =====================================================
  case conc_d_as =>
    -- Define increment bound constant
    let C_incr := 3 * (C_growth + C_mart + C_rem)

    -- Step 1: Get bounded E[V(X_n)] from Robbins-Siegmund
    obtain ⟨M_V, hM_V⟩ := hV_sup.exists_ge 0

    -- Step 2: Prove conditional increment bound (reuse from conc_d_L2 proof pattern)
    have cond_increment_bound : ∀ n,
        μ[fun ω => ‖X (n + 1) ω - X n ω‖^2 | ℱ n]
          ≤ᵐ[μ] fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) := by
      intro n
      -- Re-prove second_order_bound for arbitrary n (following pattern from condexp_ineq proof)
      -- Step 1: Triangle inequality for squared norms
      have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
        intro a b c
        have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
          calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
            _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
            _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
        have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
          have h_nn := norm_nonneg (a + b + c)
          have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
          exact sq_le_sq' (by linarith) h1
        let f : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
        have sum_eq : ∑ i : Fin 3, f i = ‖a‖ + ‖b‖ + ‖c‖ := by simp only [Fin.sum_univ_three]; rfl
        have sum_sq_eq : ∑ i : Fin 3, (f i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by simp only [Fin.sum_univ_three]; rfl
        have h3 : (∑ i : Fin 3, f i)^2 ≤ 3 * ∑ i : Fin 3, (f i)^2 := by
          calc (∑ i : Fin 3, f i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (f i)^2 :=
              sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
            _ = 3 * ∑ i : Fin 3, (f i)^2 := by simp [Fintype.card_fin]
        calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
          _ = (∑ i : Fin 3, f i)^2 := by rw [sum_eq]
          _ ≤ 3 * ∑ i : Fin 3, (f i)^2 := h3
          _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
      -- Step 2: Increment equality from proc
      have increment_eq : ∀ ω, X (n + 1) ω - X n ω =
          γ (n + 1) • (-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω) := by
        intro ω
        have := proc n ω
        simp only [this, smul_add]
        module
      -- Step 3: Pointwise bound on increment squared
      have increment_bound : ∀ ω, ‖X (n + 1) ω - X n ω‖^2 ≤
          3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
        intro ω
        rw [increment_eq]
        rw [norm_smul, mul_pow, Real.norm_eq_abs]
        have h_tri := norm_sq_sum_le_three (-h (X n ω)) (ΔM (n + 1) ω) (R (n + 1) ω)
        rw [norm_neg] at h_tri
        calc |γ (n + 1)|^2 * ‖-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω‖^2
            ≤ |γ (n + 1)|^2 * (3 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
              apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
          _ = 3 * γ (n + 1)^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
              rw [sq_abs]; ring
      -- Step 4: Integrability for condExp_mono
      have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
      have R_sq_int : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n
      have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
      have h_X_sm : StronglyMeasurable (fun ω => h (X n ω)) :=
        asm.h_continuous.comp_stronglyMeasurable hX_sm
      have h_sq_int : Integrable (fun ω => ‖h (X n ω)‖^2) μ := by
        have V_int := V'_integrable n
        have bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
          have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
        have asm' : AEStronglyMeasurable (fun ω => ‖h (X n ω)‖^2) μ :=
          h_X_sm.aestronglyMeasurable.norm.pow 2
        have bound_int : Integrable (fun ω => C_growth * (1 + V (X n ω))) μ :=
          (Integrable.add (integrable_const 1) V_int).const_mul C_growth
        exact Integrable.mono' bound_int asm'
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
      have rhs_int : Integrable (fun ω =>
          3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) μ := by
        apply Integrable.const_mul
        exact (h_sq_int.add DeltaM_sq_int).add R_sq_int
      have lhs_int : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
        exact Integrable.mono' rhs_int (by
          have : AEStronglyMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact ((asm.X_adapted (n+1)).mono (ℱ.le (n+1))).aestronglyMeasurable.sub
              hX_sm.aestronglyMeasurable
          exact this) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact increment_bound ω)
      -- Step 5: Apply condExp_mono to get condexp of increment ≤ condexp of bound
      have mono_step := condExp_mono (m := ℱ n) lhs_int rhs_int (ae_of_all _ increment_bound)
      -- Step 6: The RHS condexp simplifies using the variance bounds
      -- (Following pattern from condexp_ineq proof - pullout_eq step uses sorry there too)
      have condexp_bound_raw :
          μ[fun ω => 3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n]
            ≤ᵐ[μ] fun ω => 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
        have h_bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
          have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
        have mart_bound := h_mart_var n
        have rem_bound := h_rem_var n
        -- Pulling out constants and measurable terms from condexp is complex
        -- Following the same pattern as pullout_eq in condexp_ineq

        -- Step 1: Establish integrability
        have sum_int : Integrable (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) μ :=
          (h_sq_int.add DeltaM_sq_int).add R_sq_int

        -- Step 2: ‖h(X_n)‖² is ℱ_n-strongly measurable
        have hX_sm_Fn : StronglyMeasurable[ℱ n] (X n) := asm.X_adapted n
        have h_X_sm_Fn : StronglyMeasurable[ℱ n] (fun ω => h (X n ω)) :=
          asm.h_continuous.comp_stronglyMeasurable hX_sm_Fn
        have h_sq_sm : StronglyMeasurable[ℱ n] (fun ω => ‖h (X n ω)‖^2) :=
          h_X_sm_Fn.norm.pow 2

        -- Step 3: Use condExp_add to split the sum
        have h_plus_DeltaM_int : Integrable (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2) μ :=
          h_sq_int.add DeltaM_sq_int

        have add_eq1 : μ[fun ω => (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2) + ‖R (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            (μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 | ℱ n]) +
            (μ[fun ω => ‖R (n + 1) ω‖^2 | ℱ n]) :=
          condExp_add h_plus_DeltaM_int R_sq_int (ℱ n)

        have add_eq2 : μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            (μ[fun ω => ‖h (X n ω)‖^2 | ℱ n]) + (μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n]) :=
          condExp_add h_sq_int DeltaM_sq_int (ℱ n)

        -- Step 4: E[‖h(X_n)‖² | ℱ_n] = ‖h(X_n)‖² since it's ℱ_n-measurable
        have h_sq_condExp : μ[fun ω => ‖h (X n ω)‖^2 | ℱ n] =ᵐ[μ] fun ω => ‖h (X n ω)‖^2 := by
          rw [condExp_of_stronglyMeasurable (ℱ.le n) h_sq_sm h_sq_int]

        -- Step 5: Pull out the constant using condExp_smul
        have smul_eq : μ[fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n] =ᵐ[μ]
            fun ω => 3 * (γ (n + 1))^2 * μ[fun ω' =>
            (‖h (X n ω')‖^2 + ‖ΔM (n + 1) ω'‖^2 + ‖R (n + 1) ω'‖^2) | ℱ n] ω := by
          have key : (fun ω => 3 * (γ (n + 1))^2 *
              (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) =
              (fun ω => (3 * (γ (n + 1))^2) •
              (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
            ext ω; simp [smul_eq_mul]
          rw [key]
          have smul_cond := @condExp_smul Ω _ ℝ _ m0 μ _ _ _ _
            (3 * (γ (n + 1))^2)
            (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) (ℱ n)
          filter_upwards [smul_cond] with ω hω
          simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
          exact hω

        -- Step 6: Combine: E[sum | ℱ_n] = E[h_sq] + E[ΔM_sq] + E[R_sq] = h_sq + E[ΔM_sq] + E[R_sq]
        have combined_eq : μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            fun ω => ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                     μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω := by
          filter_upwards [add_eq1, add_eq2, h_sq_condExp] with ω h1 h2 h3
          simp only [Pi.add_apply] at h1 h2 h3 ⊢
          rw [h1, h2, h3]

        -- Step 7: Establish pullout_eq: condExp of LHS =ᵃᵉ 3γ² * (h_sq + condExp[ΔM_sq] + condExp[R_sq])
        have pullout_eq : μ[fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n] =ᵐ[μ]
            fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
             μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω) := by
          filter_upwards [smul_eq, combined_eq] with ω h_smul h_comb
          rw [h_smul, h_comb]

        -- Step 8: Apply the variance bounds from assumptions
        have apply_bounds :
            ∀ᵐ ω ∂μ, 3 * (γ (n + 1))^2 *
              (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
               μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω) ≤
            3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
          filter_upwards [mart_bound, rem_bound] with ω h_mart h_rem
          have h1 := h_bound ω
          have sum_bound : ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
              μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω ≤
              (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
            calc ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                  μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω
                ≤ C_growth * (1 + V (X n ω)) + C_mart * (1 + V (X n ω)) +
                  C_rem * (γ (n + 1))^2 * (1 + V (X n ω)) := by linarith
              _ = (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by ring
          calc 3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω)
              ≤ 3 * (γ (n + 1))^2 * ((C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω))) := by
                apply mul_le_mul_of_nonneg_left sum_bound
                apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _)
            _ = 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by ring

        -- Final step: Combine pullout_eq (equality) with apply_bounds (inequality)
        exact pullout_eq.trans_le apply_bounds
      -- Step 7: Simplify to the target bound
      -- Need: 3γ²(C_growth + C_mart + C_rem*γ²) ≤ C_incr * γ² = 3(C_growth + C_mart + C_rem)*γ²
      -- This requires C_rem*γ² ≤ C_rem, i.e., γ² ≤ 1
      have coeff_bound : ∀ᵐ ω ∂μ, 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) ≤
          C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) := by
        filter_upwards with ω
        simp only [C_incr]
        have h_sq_nonneg := sq_nonneg (γ (n + 1))
        have h_V_nonneg : 0 ≤ 1 + V (X n ω) := by linarith [hV_lower (X n ω)]
        -- Case split on γ² ≤ 1
        by_cases hγ : (γ (n + 1))^2 ≤ 1
        · have h1 : C_rem * (γ (n + 1))^2 ≤ C_rem := by
            calc C_rem * (γ (n + 1))^2 ≤ C_rem * 1 := mul_le_mul_of_nonneg_left hγ (le_of_lt hC_rem_pos)
              _ = C_rem := mul_one _
          calc 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω))
              ≤ 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem) * (1 + V (X n ω)) := by
                apply mul_le_mul_of_nonneg_right _ h_V_nonneg
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) h_sq_nonneg)
                linarith
            _ = 3 * (C_growth + C_mart + C_rem) * (γ (n + 1))^2 * (1 + V (X n ω)) := by ring
        · -- Case γ² > 1: Impossible since γ ≤ 1 by assumption
          exfalso
          have hγ_le_one : γ (n + 1) ≤ 1 := asm.gamma_le_one (n + 1)
          have hγ_nonneg : 0 ≤ γ (n + 1) := le_of_lt (asm.gamma_pos (n + 1))
          have hγ_sq_le : (γ (n + 1))^2 ≤ 1 := by
            have h1 : (γ (n + 1))^2 ≤ (1 : ℝ)^2 := by
              apply sq_le_sq'
              · linarith  -- -1 ≤ γ since 0 ≤ γ
              · exact hγ_le_one
            simp only [one_pow] at h1
            exact h1
          exact hγ hγ_sq_le
      exact mono_step.trans (condexp_bound_raw.trans coeff_bound)

    -- Step 3: Prove unconditional bound E[‖ΔX‖²] ≤ C * (1+M) * γ²
    have integral_bound : ∀ n, ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ ≤
        C_incr * (1 + M_V) * (γ (n + 1))^2 := by
      intro n
      -- Step 1: Establish integrability
      have incr_sq_int : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
        have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
        have hX_sm' : StronglyMeasurable (X (n + 1)) := (asm.X_adapted (n + 1)).mono (ℱ.le (n + 1))
        have h_X_sm : StronglyMeasurable (fun ω => h (X n ω)) :=
          asm.h_continuous.comp_stronglyMeasurable hX_sm
        have h_sq_int : Integrable (fun ω => ‖h (X n ω)‖^2) μ := by
          have V_int := V'_integrable n
          have bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
            have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
          exact Integrable.mono' ((Integrable.add (integrable_const 1) V_int).const_mul C_growth)
            (h_X_sm.aestronglyMeasurable.norm.pow 2)
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
        have R_sq_int : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n
        have rhs_int : Integrable (fun ω =>
            3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) μ :=
          ((h_sq_int.add DeltaM_sq_int).add R_sq_int).const_mul _
        -- Prove the norm-squared bound
        have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
          intro a b c
          have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
            calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
              _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
              _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
          have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
            have h_nn := norm_nonneg (a + b + c)
            have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
            exact sq_le_sq' (by linarith) h1
          let f : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
          have sum_eq : ∑ i : Fin 3, f i = ‖a‖ + ‖b‖ + ‖c‖ := by simp only [Fin.sum_univ_three]; rfl
          have sum_sq_eq : ∑ i : Fin 3, (f i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by simp only [Fin.sum_univ_three]; rfl
          have h3 : (∑ i : Fin 3, f i)^2 ≤ 3 * ∑ i : Fin 3, (f i)^2 := by
            calc (∑ i : Fin 3, f i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (f i)^2 :=
                sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
              _ = 3 * ∑ i : Fin 3, (f i)^2 := by simp [Fintype.card_fin]
          calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
            _ = (∑ i : Fin 3, f i)^2 := by rw [sum_eq]
            _ ≤ 3 * ∑ i : Fin 3, (f i)^2 := h3
            _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
        have increment_eq : ∀ ω, X (n + 1) ω - X n ω =
            γ (n + 1) • (-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω) := by
          intro ω
          have := proc n ω
          simp only [this, smul_add]
          module
        have increment_bound : ∀ ω, ‖X (n + 1) ω - X n ω‖^2 ≤
            3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
          intro ω
          rw [increment_eq]
          rw [norm_smul, mul_pow, Real.norm_eq_abs]
          have h_tri := norm_sq_sum_le_three (-h (X n ω)) (ΔM (n + 1) ω) (R (n + 1) ω)
          rw [norm_neg] at h_tri
          calc |γ (n + 1)|^2 * ‖-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω‖^2
              ≤ |γ (n + 1)|^2 * (3 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
                apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
            _ = 3 * γ (n + 1)^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
                rw [sq_abs]; ring
        exact Integrable.mono' rhs_int (by
          have : AEStronglyMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact hX_sm'.aestronglyMeasurable.sub hX_sm.aestronglyMeasurable
          exact this) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact increment_bound ω)
      -- Step 2: Integrability of the RHS
      have rhs_int : Integrable (fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω))) μ := by
        have V_int := V'_integrable n
        exact ((integrable_const 1).add V_int).const_mul _
      -- Step 3: Use tower property: ∫ f ∂μ = ∫ μ[f | ℱ n] ∂μ
      have tower : ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ =
          ∫ ω, (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) ω ∂μ := by
        symm
        exact integral_condExp (ℱ.le n)
      rw [tower]
      -- Step 4: Apply integral_mono_ae with the conditional bound
      have int_condExp : Integrable (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) μ :=
        integrable_condExp
      calc ∫ ω, (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) ω ∂μ
          ≤ ∫ ω, C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) ∂μ := by
            apply integral_mono_ae int_condExp rhs_int
            exact cond_increment_bound n
        _ = C_incr * (γ (n + 1))^2 * ∫ ω, (1 + V (X n ω)) ∂μ := by
            have heq : (fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω))) =
                (fun ω => (C_incr * (γ (n + 1))^2) * (1 + V (X n ω))) := rfl
            rw [heq, integral_const_mul]
        _ = C_incr * (γ (n + 1))^2 * (1 + ∫ ω, V (X n ω) ∂μ) := by
            congr 1
            rw [integral_add (integrable_const 1) (V'_integrable n)]
            simp only [integral_const, measure_univ, smul_eq_mul, mul_one, V',
              measureReal_univ_eq_one]
        _ ≤ C_incr * (γ (n + 1))^2 * (1 + M_V) := by
            apply mul_le_mul_of_nonneg_left
            · apply add_le_add_right
              apply hM_V.2
              exact ⟨n, rfl⟩
            · apply mul_nonneg
              · simp only [C_incr]
                apply mul_nonneg (by norm_num : (0:ℝ) ≤ 3)
                linarith
              · exact sq_nonneg _
        _ = C_incr * (1 + M_V) * (γ (n + 1))^2 := by ring

    -- Step 4: Sum of expectations is finite
    have summable_integral : Summable (fun n => ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ) := by
      apply Summable.of_nonneg_of_le
      · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
      · intro n; exact integral_bound n
      · have h_summable_shift : Summable (fun n => (γ (n + 1))^2) :=
          (summable_nat_add_iff 1).mpr asm.gamma_sq_sum_fin
        exact h_summable_shift.mul_left (C_incr * (1 + M_V))

    -- Step 5: Tonelli - a.e. summability of ‖ΔX(ω)‖²
    -- Key lemma: If ∑ E[f_n] < ∞ for nonneg f_n, then ∑ f_n(ω) < ∞ a.e.
    have ae_summable_sq : ∀ᵐ ω ∂μ, Summable (fun n => ‖X (n + 1) ω - X n ω‖^2) := by
      -- By Tonelli/Fubini for nonnegative functions
      -- Define f_n(ω) = ‖X (n + 1) ω - X n ω‖^2 as ENNReal
      let f : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal (‖X (n + 1) ω - X n ω‖^2)
      -- Step 1: Each f_n is measurable
      have hf_meas : ∀ n, AEMeasurable (f n) μ := fun n => by
        have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
        have hX_sm' : StronglyMeasurable (X (n + 1)) := (asm.X_adapted (n + 1)).mono (ℱ.le (n + 1))
        have h_diff_sm : AEStronglyMeasurable (fun ω => X (n + 1) ω - X n ω) μ :=
          hX_sm'.aestronglyMeasurable.sub hX_sm.aestronglyMeasurable
        have h_norm_sq_meas : AEMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ :=
          h_diff_sm.norm.aemeasurable.pow_const 2
        exact h_norm_sq_meas.ennreal_ofReal
      -- Step 2: ∫⁻ ∑ f_n = ∑ ∫⁻ f_n (Tonelli)
      have tonelli : ∫⁻ ω, ∑' n, f n ω ∂μ = ∑' n, ∫⁻ ω, f n ω ∂μ := lintegral_tsum hf_meas
      -- Step 3: Each ∫⁻ f_n = ENNReal.ofReal (∫ f_n) since f_n ≥ 0
      have lintegral_eq : ∀ n, ∫⁻ ω, f n ω ∂μ = ENNReal.ofReal (∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ) := by
        intro n
        have incr_sq_int : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
          have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
          have hX_sm' : StronglyMeasurable (X (n + 1)) := (asm.X_adapted (n + 1)).mono (ℱ.le (n + 1))
          have h_X_sm : StronglyMeasurable (fun ω => h (X n ω)) :=
            asm.h_continuous.comp_stronglyMeasurable hX_sm
          have h_sq_int : Integrable (fun ω => ‖h (X n ω)‖^2) μ := by
            have V_int := V'_integrable n
            have bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
              have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
            exact Integrable.mono' ((Integrable.add (integrable_const 1) V_int).const_mul C_growth)
              (h_X_sm.aestronglyMeasurable.norm.pow 2)
              (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
          have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
          have R_sq_int : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n
          have rhs_int : Integrable (fun ω =>
              3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) μ :=
            ((h_sq_int.add DeltaM_sq_int).add R_sq_int).const_mul _
          have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
            intro a b c
            have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
              calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
                _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
                _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
            have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
              have h_nn := norm_nonneg (a + b + c)
              have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
              exact sq_le_sq' (by linarith) h1
            let g : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
            have sum_eq : ∑ i : Fin 3, g i = ‖a‖ + ‖b‖ + ‖c‖ := by simp only [Fin.sum_univ_three]; rfl
            have sum_sq_eq : ∑ i : Fin 3, (g i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by simp only [Fin.sum_univ_three]; rfl
            have h3 : (∑ i : Fin 3, g i)^2 ≤ 3 * ∑ i : Fin 3, (g i)^2 := by
              calc (∑ i : Fin 3, g i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (g i)^2 :=
                  sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := g)
                _ = 3 * ∑ i : Fin 3, (g i)^2 := by simp [Fintype.card_fin]
            calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
              _ = (∑ i : Fin 3, g i)^2 := by rw [sum_eq]
              _ ≤ 3 * ∑ i : Fin 3, (g i)^2 := h3
              _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
          have increment_eq : ∀ ω, X (n + 1) ω - X n ω =
              γ (n + 1) • (-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω) := by
            intro ω
            have := proc n ω
            simp only [this, smul_add]
            module
          have increment_bound : ∀ ω, ‖X (n + 1) ω - X n ω‖^2 ≤
              3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
            intro ω
            rw [increment_eq]
            rw [norm_smul, mul_pow, Real.norm_eq_abs]
            have h_tri := norm_sq_sum_le_three (-h (X n ω)) (ΔM (n + 1) ω) (R (n + 1) ω)
            rw [norm_neg] at h_tri
            calc |γ (n + 1)|^2 * ‖-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω‖^2
                ≤ |γ (n + 1)|^2 * (3 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
                  apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
              _ = 3 * γ (n + 1)^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
                  rw [sq_abs]; ring
          exact Integrable.mono' rhs_int (by
            have : AEStronglyMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
              apply AEStronglyMeasurable.pow
              apply AEStronglyMeasurable.norm
              exact hX_sm'.aestronglyMeasurable.sub hX_sm.aestronglyMeasurable
            exact this) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact increment_bound ω)
        rw [← ofReal_integral_eq_lintegral_ofReal incr_sq_int (ae_of_all _ (fun ω => sq_nonneg _))]
      -- Step 4: Sum of lintegrals is finite
      have sum_lintegral_lt_top : ∑' n, ∫⁻ ω, f n ω ∂μ < ⊤ := by
        simp_rw [lintegral_eq]
        exact summable_integral.tsum_ofReal_lt_top
      -- Step 5: Therefore ∫⁻ ∑ f_n < ⊤
      have lintegral_tsum_lt_top : ∫⁻ ω, ∑' n, f n ω ∂μ < ⊤ := by
        rw [tonelli]; exact sum_lintegral_lt_top
      -- Step 6: By ae_lt_top, ∑ f_n(ω) < ⊤ a.e.
      have tsum_ae_lt_top : ∀ᵐ ω ∂μ, ∑' n, f n ω < ⊤ := by
        apply ae_lt_top'
        · exact AEMeasurable.ennreal_tsum hf_meas
        · exact lintegral_tsum_lt_top.ne
      -- Step 7: Convert ENNReal tsum < ⊤ to Real Summable
      refine tsum_ae_lt_top.mono fun ω hω => ?_
      -- hω : ∑' n, f n ω < ⊤
      -- Need: Summable (fun n => ‖X (n + 1) ω - X n ω‖^2)
      have h_nonneg : ∀ n, 0 ≤ ‖X (n + 1) ω - X n ω‖^2 := fun n => sq_nonneg _
      have tsum_ne_top : ∑' n, f n ω ≠ ⊤ := hω.ne
      -- f n ω = ENNReal.ofReal (‖...‖^2), and toReal of ofReal of nonneg is identity
      have h_toReal_eq : ∀ n, (f n ω).toReal = ‖X (n + 1) ω - X n ω‖^2 := fun n =>
        ENNReal.toReal_ofReal (h_nonneg n)
      -- Use ENNReal.summable_toReal: if ∑ f < ⊤ then (f ·).toReal is summable
      have h_summable_toReal : Summable (fun n => (f n ω).toReal) :=
        ENNReal.summable_toReal tsum_ne_top
      convert h_summable_toReal using 1
      ext n; exact (h_toReal_eq n).symm

    -- Step 6: Convergent series has terms → 0
    filter_upwards [ae_summable_sq] with ω hω_sum
    have h_sq_tendsto : Tendsto (fun n => ‖X (n + 1) ω - X n ω‖^2) atTop (nhds 0) :=
      hω_sum.tendsto_atTop_zero
    have h_norm_tendsto : Tendsto (fun n => ‖X (n + 1) ω - X n ω‖) atTop (nhds 0) := by
      have h_sqrt : Tendsto (fun n => Real.sqrt (‖X (n + 1) ω - X n ω‖^2)) atTop (nhds (Real.sqrt 0)) :=
        h_sq_tendsto.sqrt
      simp only [Real.sqrt_zero] at h_sqrt
      convert h_sqrt using 1
      ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto

  -- =====================================================
  -- SUBTASK 20: Conclusion (d) part 2 - E[‖X_{n+1} - X_n‖²] → 0
  -- Uses: E[‖X_{n+1} - X_n‖² | F_n] ≤ C γ_{n+1}² (1 + V(X_n))
  -- And: sup E[V(X_n)] < ∞, γ_n → 0
  --
  -- SANITY CHECK PASSED
  -- =====================================================
  /-
  ## Informal Proof of conc_d_L2

  **Goal:** E[‖X_{n+1} - X_n‖²] → 0 as n → ∞

  **Step 1: Conditional increment bound**
  From second_order_bound (proved in condexp_ineq):
    E[‖X_{n+1} - X_n‖² | F_n] ≤ᵐ 3 * γ_{n+1}² * (C_growth + C_mart + C_rem*γ_{n+1}²) * (1 + V(X_n))

  For convenience, let C_incr := 3 * (C_growth + C_mart + C_rem) (absorbing the γ² inside).
  Then: E[‖ΔX‖² | F_n] ≤ C_incr * γ_{n+1}² * (1 + V(X_n))  (for γ² ≤ 1)

  **Step 2: Tower property (taking expectations)**
  E[‖X_{n+1} - X_n‖²] = E[E[‖X_{n+1} - X_n‖² | F_n]]   (tower property)
                       ≤ E[C_incr * γ_{n+1}² * (1 + V(X_n))]  (condExp_integral_mono)
                       = C_incr * γ_{n+1}² * (1 + E[V(X_n)])  (pull out constant)

  **Step 3: Uniform bound on E[V(X_n)]**
  From hV_sup: BddAbove (Set.range (fun n => ∫ ω, V(X n ω) ∂μ))
  So ∃ M, ∀ n, E[V(X_n)] ≤ M.

  **Step 4: Final bound**
  E[‖X_{n+1} - X_n‖²] ≤ C_incr * (1 + M) * γ_{n+1}²

  **Step 5: Convergence to zero**
  From asm.gamma_sq_sum_fin: Summable (fun n => (γ n)²)
  By Summable.tendsto_atTop_zero: γ_n² → 0
  Therefore: C_incr * (1 + M) * γ_{n+1}² → 0

  By Tendsto.const_mul: E[‖X_{n+1} - X_n‖²] → 0  ∎

  **Key Mathlib lemmas:**
  - integral_condExp: E[E[f|G]] = E[f] (for integrable f)
  - condExp_mono: f ≤ᵐ g integrable → E[f|G] ≤ᵐ E[g|G]
  - Summable.tendsto_atTop_zero: Summable f → f → 0
  - Tendsto.const_mul: c * f → c * 0 = 0
  - BddAbove for extracting the bound M
  -/
  case conc_d_L2 =>
    -- Define the increment bound constant
    let C_incr := 3 * (C_growth + C_mart + C_rem)

    -- SUB 20.1: Conditional bound E[‖ΔX‖² | F_n] ≤ C * γ² * (1 + V(X_n))
    have cond_increment_bound : ∀ n,
        μ[fun ω => ‖X (n + 1) ω - X n ω‖^2 | ℱ n]
          ≤ᵐ[μ] fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) := by
      -- From second_order_bound in condexp_ineq proof
      -- Simplify: 3 * γ² * (C_growth + C_mart + C_rem*γ²) ≤ C_incr * γ²  for γ² ≤ 1
      -- Mathlib: condExp_mono, Filter.EventuallyLE.trans
      intro n
      -- Re-prove second_order_bound for arbitrary n (following pattern from condexp_ineq proof)
      -- Step 1: Triangle inequality for squared norms
      have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
        intro a b c
        have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
          calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
            _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
            _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
        have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
          have h_nn := norm_nonneg (a + b + c)
          have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
          exact sq_le_sq' (by linarith) h1
        let f : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
        have sum_eq : ∑ i : Fin 3, f i = ‖a‖ + ‖b‖ + ‖c‖ := by simp only [Fin.sum_univ_three]; rfl
        have sum_sq_eq : ∑ i : Fin 3, (f i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by simp only [Fin.sum_univ_three]; rfl
        have h3 : (∑ i : Fin 3, f i)^2 ≤ 3 * ∑ i : Fin 3, (f i)^2 := by
          calc (∑ i : Fin 3, f i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (f i)^2 :=
              sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
            _ = 3 * ∑ i : Fin 3, (f i)^2 := by simp [Fintype.card_fin]
        calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
          _ = (∑ i : Fin 3, f i)^2 := by rw [sum_eq]
          _ ≤ 3 * ∑ i : Fin 3, (f i)^2 := h3
          _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
      -- Step 2: Increment equality from proc
      have increment_eq : ∀ ω, X (n + 1) ω - X n ω =
          γ (n + 1) • (-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω) := by
        intro ω
        have := proc n ω
        simp only [this, smul_add]
        module
      -- Step 3: Pointwise bound on increment squared
      have increment_bound : ∀ ω, ‖X (n + 1) ω - X n ω‖^2 ≤
          3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
        intro ω
        rw [increment_eq]
        rw [norm_smul, mul_pow, Real.norm_eq_abs]
        have h_tri := norm_sq_sum_le_three (-h (X n ω)) (ΔM (n + 1) ω) (R (n + 1) ω)
        rw [norm_neg] at h_tri
        calc |γ (n + 1)|^2 * ‖-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω‖^2
            ≤ |γ (n + 1)|^2 * (3 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
              apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
          _ = 3 * γ (n + 1)^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
              rw [sq_abs]; ring
      -- Step 4: Integrability for condExp_mono
      have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
      have R_sq_int : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n
      have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
      have h_X_sm : StronglyMeasurable (fun ω => h (X n ω)) :=
        asm.h_continuous.comp_stronglyMeasurable hX_sm
      have h_sq_int : Integrable (fun ω => ‖h (X n ω)‖^2) μ := by
        have V_int := V'_integrable n
        have bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
          have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
        have asm' : AEStronglyMeasurable (fun ω => ‖h (X n ω)‖^2) μ :=
          h_X_sm.aestronglyMeasurable.norm.pow 2
        have bound_int : Integrable (fun ω => C_growth * (1 + V (X n ω))) μ :=
          (Integrable.add (integrable_const 1) V_int).const_mul C_growth
        exact Integrable.mono' bound_int asm'
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
      have rhs_int : Integrable (fun ω =>
          3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) μ := by
        apply Integrable.const_mul
        exact (h_sq_int.add DeltaM_sq_int).add R_sq_int
      have lhs_int : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
        exact Integrable.mono' rhs_int (by
          have : AEStronglyMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact ((asm.X_adapted (n+1)).mono (ℱ.le (n+1))).aestronglyMeasurable.sub
              hX_sm.aestronglyMeasurable
          exact this) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact increment_bound ω)
      -- Step 5: Apply condExp_mono to get condexp of increment ≤ condexp of bound
      have mono_step := condExp_mono (m := ℱ n) lhs_int rhs_int (ae_of_all _ increment_bound)
      -- Step 6: The RHS condexp simplifies using the variance bounds
      -- (Following pattern from condexp_ineq proof - pullout_eq step uses sorry there too)
      have condexp_bound_raw :
          μ[fun ω => 3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n]
            ≤ᵐ[μ] fun ω => 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
        have h_bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
          have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
        have mart_bound := h_mart_var n
        have rem_bound := h_rem_var n
        -- Pulling out constants and measurable terms from condexp is complex
        -- Following the same pattern as pullout_eq in condexp_ineq

        -- Step 1: Establish integrability
        have sum_int : Integrable (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) μ :=
          (h_sq_int.add DeltaM_sq_int).add R_sq_int

        -- Step 2: ‖h(X_n)‖² is ℱ_n-strongly measurable
        have hX_sm_Fn : StronglyMeasurable[ℱ n] (X n) := asm.X_adapted n
        have h_X_sm_Fn : StronglyMeasurable[ℱ n] (fun ω => h (X n ω)) :=
          asm.h_continuous.comp_stronglyMeasurable hX_sm_Fn
        have h_sq_sm : StronglyMeasurable[ℱ n] (fun ω => ‖h (X n ω)‖^2) :=
          h_X_sm_Fn.norm.pow 2

        -- Step 3: Use condExp_add to split the sum
        have h_plus_DeltaM_int : Integrable (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2) μ :=
          h_sq_int.add DeltaM_sq_int

        have add_eq1 : μ[fun ω => (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2) + ‖R (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            (μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 | ℱ n]) +
            (μ[fun ω => ‖R (n + 1) ω‖^2 | ℱ n]) :=
          condExp_add h_plus_DeltaM_int R_sq_int (ℱ n)

        have add_eq2 : μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            (μ[fun ω => ‖h (X n ω)‖^2 | ℱ n]) + (μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n]) :=
          condExp_add h_sq_int DeltaM_sq_int (ℱ n)

        -- Step 4: E[‖h(X_n)‖² | ℱ_n] = ‖h(X_n)‖² since it's ℱ_n-measurable
        have h_sq_condExp : μ[fun ω => ‖h (X n ω)‖^2 | ℱ n] =ᵐ[μ] fun ω => ‖h (X n ω)‖^2 := by
          rw [condExp_of_stronglyMeasurable (ℱ.le n) h_sq_sm h_sq_int]

        -- Step 5: Pull out the constant using condExp_smul
        have smul_eq : μ[fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n] =ᵐ[μ]
            fun ω => 3 * (γ (n + 1))^2 * μ[fun ω' =>
            (‖h (X n ω')‖^2 + ‖ΔM (n + 1) ω'‖^2 + ‖R (n + 1) ω'‖^2) | ℱ n] ω := by
          have key : (fun ω => 3 * (γ (n + 1))^2 *
              (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) =
              (fun ω => (3 * (γ (n + 1))^2) •
              (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
            ext ω; simp [smul_eq_mul]
          rw [key]
          have smul_cond := @condExp_smul Ω _ ℝ _ m0 μ _ _ _ _
            (3 * (γ (n + 1))^2)
            (fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) (ℱ n)
          filter_upwards [smul_cond] with ω hω
          simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
          exact hω

        -- Step 6: Combine: E[sum | ℱ_n] = E[h_sq] + E[ΔM_sq] + E[R_sq] = h_sq + E[ΔM_sq] + E[R_sq]
        have combined_eq : μ[fun ω => ‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2 | ℱ n] =ᵐ[μ]
            fun ω => ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                     μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω := by
          filter_upwards [add_eq1, add_eq2, h_sq_condExp] with ω h1 h2 h3
          simp only [Pi.add_apply] at h1 h2 h3 ⊢
          rw [h1, h2, h3]

        -- Step 7: Establish pullout_eq: condExp of LHS =ᵃᵉ 3γ² * (h_sq + condExp[ΔM_sq] + condExp[R_sq])
        have pullout_eq : μ[fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) | ℱ n] =ᵐ[μ]
            fun ω => 3 * (γ (n + 1))^2 *
            (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
             μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω) := by
          filter_upwards [smul_eq, combined_eq] with ω h_smul h_comb
          rw [h_smul, h_comb]

        -- Step 8: Apply the variance bounds from assumptions
        have apply_bounds :
            ∀ᵐ ω ∂μ, 3 * (γ (n + 1))^2 *
              (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
               μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω) ≤
            3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
          filter_upwards [mart_bound, rem_bound] with ω h_mart h_rem
          have h1 := h_bound ω
          have sum_bound : ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
              μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω ≤
              (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by
            calc ‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                  μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω
                ≤ C_growth * (1 + V (X n ω)) + C_mart * (1 + V (X n ω)) +
                  C_rem * (γ (n + 1))^2 * (1 + V (X n ω)) := by linarith
              _ = (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by ring
          calc 3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + μ[fun ω' => ‖ΔM (n + 1) ω'‖^2 | ℱ n] ω +
                μ[fun ω' => ‖R (n + 1) ω'‖^2 | ℱ n] ω)
              ≤ 3 * (γ (n + 1))^2 * ((C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω))) := by
                apply mul_le_mul_of_nonneg_left sum_bound
                apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _)
            _ = 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) := by ring

        -- Final step: Combine pullout_eq (equality) with apply_bounds (inequality)
        exact pullout_eq.trans_le apply_bounds
      -- Step 7: Simplify to the target bound
      -- Need: 3γ²(C_growth + C_mart + C_rem*γ²) ≤ C_incr * γ² = 3(C_growth + C_mart + C_rem)*γ²
      -- This requires C_rem*γ² ≤ C_rem, i.e., γ² ≤ 1
      have coeff_bound : ∀ᵐ ω ∂μ, 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω)) ≤
          C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) := by
        filter_upwards with ω
        simp only [C_incr]
        have h_sq_nonneg := sq_nonneg (γ (n + 1))
        have h_V_nonneg : 0 ≤ 1 + V (X n ω) := by linarith [hV_lower (X n ω)]
        -- Case split on γ² ≤ 1
        by_cases hγ : (γ (n + 1))^2 ≤ 1
        · have h1 : C_rem * (γ (n + 1))^2 ≤ C_rem := by
            calc C_rem * (γ (n + 1))^2 ≤ C_rem * 1 := mul_le_mul_of_nonneg_left hγ (le_of_lt hC_rem_pos)
              _ = C_rem := mul_one _
          calc 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem * (γ (n + 1))^2) * (1 + V (X n ω))
              ≤ 3 * (γ (n + 1))^2 * (C_growth + C_mart + C_rem) * (1 + V (X n ω)) := by
                apply mul_le_mul_of_nonneg_right _ h_V_nonneg
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) h_sq_nonneg)
                linarith
            _ = 3 * (C_growth + C_mart + C_rem) * (γ (n + 1))^2 * (1 + V (X n ω)) := by ring
        · -- Case γ² > 1: Impossible since γ ≤ 1 by assumption
          exfalso
          have hγ_le_one : γ (n + 1) ≤ 1 := asm.gamma_le_one (n + 1)
          have hγ_nonneg : 0 ≤ γ (n + 1) := le_of_lt (asm.gamma_pos (n + 1))
          have hγ_sq_le : (γ (n + 1))^2 ≤ 1 := by
            have h1 : (γ (n + 1))^2 ≤ (1 : ℝ)^2 := by
              apply sq_le_sq'
              · linarith  -- -1 ≤ γ since 0 ≤ γ
              · exact hγ_le_one
            simp only [one_pow] at h1
            exact h1
          exact hγ hγ_sq_le
      exact mono_step.trans (condexp_bound_raw.trans coeff_bound)

    -- SUB 20.2: Extract uniform bound M from hV_sup
    have exists_M : ∃ M : ℝ, ∀ n, ∫ ω, V (X n ω) ∂μ ≤ M := by
      -- hV_sup : BddAbove (Set.range (fun n => ∫ ω, V (X n ω) ∂μ))
      -- Use BddAbove definition to extract an upper bound
      -- Mathlib: BddAbove.exists_ge, or sSup_le for the sSup
      obtain ⟨M, hM⟩ := hV_sup
      refine ⟨M, fun n => ?_⟩
      apply hM
      exact Set.mem_range_self n

    obtain ⟨M, hM⟩ := exists_M

    -- SUB 20.3: Taking expectations via tower property
    have integral_bound : ∀ n, ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ ≤ C_incr * (1 + M) * (γ (n + 1))^2 := by
      intro n
      -- Step 1: E[‖ΔX‖²] = E[E[‖ΔX‖² | F_n]] by integral_condExp
      -- Step 2: E[E[‖ΔX‖² | F_n]] ≤ E[C_incr * γ² * (1 + V(X_n))] by condExp_mono + integral_mono_ae
      -- Step 3: = C_incr * γ² * (1 + E[V(X_n)])  pull out constants
      -- Step 4: ≤ C_incr * γ² * (1 + M)  using hM
      -- Mathlib: integral_condExp, setIntegral_condExp_eq_integral,
      --          MeasureTheory.integral_mono_ae, integral_mul_left
      -- First establish integrability of ‖X (n + 1) - X n‖²
      have lhs_int : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
        -- From cond_increment_bound proof context
        have hX_sm : StronglyMeasurable (X n) := (asm.X_adapted n).mono (ℱ.le n)
        have h_X_sm : StronglyMeasurable (fun ω => h (X n ω)) :=
          asm.h_continuous.comp_stronglyMeasurable hX_sm
        have DeltaM_sq_int : Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ := asm.martingale_diff_L2 n
        have R_sq_int : Integrable (fun ω => ‖R (n + 1) ω‖^2) μ := asm.remainder_L2 n
        have h_sq_int : Integrable (fun ω => ‖h (X n ω)‖^2) μ := by
          have V_int := V'_integrable n
          have bound : ∀ ω, ‖h (X n ω)‖^2 ≤ C_growth * (1 + V (X n ω)) := fun ω => by
            have := h_growth (X n ω); linarith [sq_nonneg ‖gradV (X n ω)‖]
          have asm' : AEStronglyMeasurable (fun ω => ‖h (X n ω)‖^2) μ :=
            h_X_sm.aestronglyMeasurable.norm.pow 2
          have bound_int : Integrable (fun ω => C_growth * (1 + V (X n ω))) μ :=
            (Integrable.add (integrable_const 1) V_int).const_mul C_growth
          exact Integrable.mono' bound_int asm'
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound ω)
        -- Use the increment bound
        have norm_sq_sum_le_three : ∀ (a b c : E), ‖a + b + c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
          intro a b c
          have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
            calc ‖a + b + c‖ = ‖(a + b) + c‖ := by ring_nf
              _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
              _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]
          have h2 : ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := by
            have h_nn := norm_nonneg (a + b + c)
            have h_rhs_nn : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]
            exact sq_le_sq' (by linarith) h1
          let f : Fin 3 → ℝ := ![‖a‖, ‖b‖, ‖c‖]
          have sum_eq : ∑ i : Fin 3, f i = ‖a‖ + ‖b‖ + ‖c‖ := by simp only [Fin.sum_univ_three]; rfl
          have sum_sq_eq : ∑ i : Fin 3, (f i)^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 := by simp only [Fin.sum_univ_three]; rfl
          have h3 : (∑ i : Fin 3, f i)^2 ≤ 3 * ∑ i : Fin 3, (f i)^2 := by
            calc (∑ i : Fin 3, f i)^2 ≤ Fintype.card (Fin 3) * ∑ i : Fin 3, (f i)^2 :=
                sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
              _ = 3 * ∑ i : Fin 3, (f i)^2 := by simp [Fintype.card_fin]
          calc ‖a + b + c‖^2 ≤ (‖a‖ + ‖b‖ + ‖c‖)^2 := h2
            _ = (∑ i : Fin 3, f i)^2 := by rw [sum_eq]
            _ ≤ 3 * ∑ i : Fin 3, (f i)^2 := h3
            _ = 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by rw [sum_sq_eq]
        have increment_eq : ∀ ω, X (n + 1) ω - X n ω =
            γ (n + 1) • (-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω) := by
          intro ω
          have := proc n ω
          simp only [this, smul_add]
          module
        have increment_bound : ∀ ω, ‖X (n + 1) ω - X n ω‖^2 ≤
            3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
          intro ω
          rw [increment_eq]
          rw [norm_smul, mul_pow, Real.norm_eq_abs]
          have h_tri := norm_sq_sum_le_three (-h (X n ω)) (ΔM (n + 1) ω) (R (n + 1) ω)
          rw [norm_neg] at h_tri
          calc |γ (n + 1)|^2 * ‖-h (X n ω) + ΔM (n + 1) ω + R (n + 1) ω‖^2
              ≤ |γ (n + 1)|^2 * (3 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) := by
                apply mul_le_mul_of_nonneg_left h_tri (sq_nonneg _)
            _ = 3 * γ (n + 1)^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2) := by
                rw [sq_abs]; ring
        have rhs_int : Integrable (fun ω =>
            3 * (γ (n + 1))^2 * (‖h (X n ω)‖^2 + ‖ΔM (n + 1) ω‖^2 + ‖R (n + 1) ω‖^2)) μ := by
          apply Integrable.const_mul
          exact (h_sq_int.add DeltaM_sq_int).add R_sq_int
        exact Integrable.mono' rhs_int (by
          have : AEStronglyMeasurable (fun ω => ‖X (n + 1) ω - X n ω‖^2) μ := by
            apply AEStronglyMeasurable.pow
            apply AEStronglyMeasurable.norm
            exact ((asm.X_adapted (n+1)).mono (ℱ.le (n+1))).aestronglyMeasurable.sub
              hX_sm.aestronglyMeasurable
          exact this) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact increment_bound ω)
      -- Integrability of the RHS
      have rhs_int : Integrable (fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω))) μ := by
        apply Integrable.const_mul
        exact Integrable.add (integrable_const 1) (V'_integrable n)
      -- Step 1: Use tower property E[f] = E[E[f|G]]
      -- For finite measures, trim is sigma-finite
      haveI : SigmaFinite (μ.trim (ℱ.le n)) := by
        haveI : IsFiniteMeasure (μ.trim (ℱ.le n)) := isFiniteMeasure_trim (ℱ.le n)
        exact IsFiniteMeasure.toSigmaFinite _
      -- Step 2: E[‖ΔX‖²] = E[E[‖ΔX‖² | F_n]]
      have tower : ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ =
          ∫ ω, (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) ω ∂μ := by
        rw [integral_condExp (ℱ.le n)]
      -- Step 3: Apply integral_mono_ae with cond_increment_bound
      have step3 : ∫ ω, (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) ω ∂μ ≤
          ∫ ω, C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) ∂μ := by
        apply integral_mono_ae integrable_condExp rhs_int
        exact cond_increment_bound n
      -- Step 4: Pull out constants: ∫ c * f = c * ∫ f
      have step4 : ∫ ω, C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) ∂μ =
          C_incr * (γ (n + 1))^2 * ∫ ω, (1 + V (X n ω)) ∂μ := by
        have h_eq : (fun ω => C_incr * (γ (n + 1))^2 * (1 + V (X n ω))) =
            (fun ω => (C_incr * (γ (n + 1))^2) * (1 + V (X n ω))) := by
          ext ω; ring
        rw [h_eq, integral_const_mul]
      -- Step 5: Expand integral of (1 + V(X_n))
      have step5 : ∫ ω, (1 + V (X n ω)) ∂μ = 1 + ∫ ω, V (X n ω) ∂μ := by
        rw [integral_add (integrable_const 1) (V'_integrable n)]
        simp only [integral_const]
        have h_measure : μ.real Set.univ = 1 := by
          simp only [Measure.real_def, measure_univ, ENNReal.toReal_one]
        simp only [h_measure, one_smul]
        -- V' n = V (X n), so integrals are equal
        rfl
      -- Step 6: Combine and use hM
      calc ∫ ω, ‖X (n + 1) ω - X n ω‖^2 ∂μ
          = ∫ ω, (μ[fun ω' => ‖X (n + 1) ω' - X n ω'‖^2 | ℱ n]) ω ∂μ := tower
        _ ≤ ∫ ω, C_incr * (γ (n + 1))^2 * (1 + V (X n ω)) ∂μ := step3
        _ = C_incr * (γ (n + 1))^2 * ∫ ω, (1 + V (X n ω)) ∂μ := step4
        _ = C_incr * (γ (n + 1))^2 * (1 + ∫ ω, V (X n ω) ∂μ) := by rw [step5]
        _ ≤ C_incr * (γ (n + 1))^2 * (1 + M) := by
            apply mul_le_mul_of_nonneg_left
            · linarith [hM n]
            · apply mul_nonneg
              · simp only [C_incr]
                apply mul_nonneg (by norm_num : (0:ℝ) ≤ 3)
                linarith
              · exact sq_nonneg _
        _ = C_incr * (1 + M) * (γ (n + 1))^2 := by ring

    -- SUB 20.4: Convergence: γ² → 0 implies E[‖ΔX‖²] → 0
    have gamma_sq_tends_zero : Tendsto (fun n => (γ n)^2) atTop (nhds 0) := by
      -- From asm.gamma_sq_sum_fin : Summable (fun n => (γ n)^2)
      -- Use Summable.tendsto_atTop_zero
      exact asm.gamma_sq_sum_fin.tendsto_atTop_zero

    -- SUB 20.5: Final convergence
    -- E[‖X_{n+1} - X_n‖²] ≤ C * γ_{n+1}² → 0
    -- Use squeeze theorem: 0 ≤ E[‖ΔX‖²] ≤ C * γ² → 0
    -- Mathlib: tendsto_of_tendsto_of_tendsto_of_le_of_le (squeeze)
    --          Tendsto.const_mul for C * γ² → C * 0 = 0
    have const_bound_tends_zero : Tendsto (fun n => C_incr * (1 + M) * (γ (n + 1))^2) atTop (nhds 0) := by
      -- C_incr * (1 + M) * γ_{n+1}² → 0 since γ² → 0
      -- Strategy: γ² → 0 implies c * γ² → c * 0 = 0
      -- Use Tendsto.mul_const or rewrite c * x as x * c and use Tendsto.const_mul
      -- Mathlib: Filter.Tendsto.mul_const, Filter.Tendsto.const_mul
      have h1 : Tendsto (fun n => (γ (n + 1))^2) atTop (nhds 0) :=
        (tendsto_add_atTop_iff_nat 1).mpr gamma_sq_tends_zero
      have h2 := h1.const_mul (C_incr * (1 + M))
      simp only [mul_zero] at h2
      convert h2 using 1

    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds const_bound_tends_zero
    · -- Lower bound: 0 ≤ E[‖ΔX‖²]
      intro n
      exact integral_nonneg (fun ω => sq_nonneg _)
    · -- Upper bound: E[‖ΔX‖²] ≤ C * γ²
      intro n
      exact integral_bound n
