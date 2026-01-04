/-

This file formalizes the corollary to the SGD convergence theorem
in the case where the drift condition has a unique zero.
-/

import ArtificialAlgorithms.AI.SGD
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For stdOrthonormalBasis
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Martingale.Convergence  -- For Submartingale.exists_ae_tendsto_of_bdd
import Mathlib.Probability.CondVar  -- For condVar_ae_eq_condExp_sq_sub_sq_condExp

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators

namespace SGDUniqueMin

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- Additional assumptions for Corollary 2.3.1 (Robbins-Monro with unique minimizer).

These assumptions extend SGD_Convergence_Assumptions with:
1. Continuity of h (already in base assumptions)
2. Unique zero of the drift condition: {x : ⟨∇V(x), h(x)⟩ = 0} = {x*}
-/
structure Assumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM R : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (x_star : E) : Prop where
  /-- Base SGD convergence assumptions hold -/
  base_asm : SGD_Convergence_Assumptions μ X γ h ΔM R V gradV ℱ
  /-- x* is the unique point where drift vanishes -/
  drift_zero_unique : {x : E | @inner ℝ _ _ (gradV x) (h x) = 0} = {x_star}

/-!
## Helper Lemmas

### Lemma 1: Coercive continuous functions attain their minimum
-/

/-- A coercive continuous function on a finite-dimensional space attains its minimum. -/
lemma exists_minimizer_of_coercive
    {V : E → ℝ} (hV_cont : Continuous V) (hV_coercive : Tendsto V (cocompact E) atTop) :
    ∃ x_min : E, ∀ y, V x_min ≤ V y := by
  -- In finite dimensions, we have ProperSpace
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Fix a point x₀ and consider sublevel set S = {x : V x ≤ V x₀}
  obtain ⟨x₀⟩ : Nonempty E := inferInstance
  let S := {x : E | V x ≤ V x₀}
  -- S is nonempty since x₀ ∈ S
  have hS_nonempty : S.Nonempty := ⟨x₀, le_refl (V x₀)⟩
  -- S is closed (preimage of closed set under continuous function)
  have hS_closed : IsClosed S := isClosed_Iic.preimage hV_cont
  -- S is bounded: from coercivity
  have hS_bdd : Bornology.IsBounded S := by
    -- From coercivity: there exists K compact such that V x > V x₀ outside K
    have hcoerc : ∀ᶠ x in cocompact E, V x₀ < V x :=
      hV_coercive.eventually (eventually_gt_atTop (V x₀))
    rw [Filter.Eventually, mem_cocompact'] at hcoerc
    obtain ⟨K, hK_compact, hK_sub⟩ := hcoerc
    -- hK_sub : {x | V x₀ < V x}ᶜ ⊆ K
    -- S ⊆ K: if x ∈ S, then V x ≤ V x₀, so x ∈ K (otherwise V x > V x₀)
    have hS_sub_K : S ⊆ K := by
      intro x hx
      -- hx : V x ≤ V x₀
      -- Goal: x ∈ K
      by_contra h_not_in_K
      -- h_not_in_K : x ∉ K.
      -- Since Sᶜ ⊆ K, if x ∉ K then x ∉ Sᶜ, so x ∈ S.
      -- Wait, hK_sub : sᶜ ⊆ K.
      -- So if x ∉ K, then x ∉ sᶜ, so x ∈ s.
      -- s = {y | V x₀ < V y}.
      -- So x ∈ s means V x₀ < V x.
      have h_subset : {y | V x₀ < V y}ᶜ ⊆ K := hK_sub
      have h_in_s : x ∈ {y | V x₀ < V y} := by
        by_contra h_not_in_s
        have h_in_K := h_subset h_not_in_s
        exact h_not_in_K h_in_K
      have h_gt : V x₀ < V x := h_in_s
      exact hx.not_lt h_gt
    exact hK_compact.isBounded.subset hS_sub_K
  -- S is compact (closed + bounded in proper space)
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  -- V is continuous on compact S, hence attains minimum on S
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ := hS_compact.exists_isMinOn hS_nonempty hV_cont.continuousOn
  -- x_min is global minimum
  use x_min
  intro y
  by_cases hy : y ∈ S
  · exact hx_min_le hy
  · -- y ∉ S means V y > V x₀ ≥ V x_min
    have hy' : V x₀ < V y := by
      change ¬ (V y ≤ V x₀) at hy
      linarith
    have h_x0_in_S : x₀ ∈ S := le_refl (V x₀)
    have h1 : V x_min ≤ V x₀ := hx_min_le h_x0_in_S
    linarith

/-- At a minimizer of a differentiable function, the gradient is zero. -/
lemma gradient_zero_at_minimizer
    {V : E → ℝ} {gradV : E → E}
    (hV_diff : ContDiff ℝ 1 V) (hV_grad : ∀ x, gradient V x = gradV x)
    {x_min : E} (h_min : ∀ y, V x_min ≤ V y) :
    gradV x_min = 0 := by
  -- A global minimizer is a local minimizer
  have h_isMinOn : IsMinOn V univ x_min := isMinOn_univ_iff.mpr h_min
  have h_isLocalMin : IsLocalMin V x_min := h_isMinOn.isLocalMin Filter.univ_mem
  -- At a local minimum, fderiv = 0 (Fermat's theorem)
  have h_fderiv_zero : fderiv ℝ V x_min = 0 := h_isLocalMin.fderiv_eq_zero
  -- gradient is the Riesz dual of fderiv, so gradient = 0
  have h_grad_zero : gradient V x_min = 0 := by
    rw [gradient, h_fderiv_zero, map_zero]
  -- Use the hypothesis that gradV = gradient V
  rw [← hV_grad x_min, h_grad_zero]

/-!
### Lemma 2: Bounded sequences with vanishing increments
-/

/-- If a bounded sequence has vanishing increments and a unique accumulation point,
    then it converges to that point. -/
lemma tendsto_of_bounded_unique_accumulation
    {x : ℕ → E} {x_star : E}
    (h_bdd : Bornology.IsBounded (Set.range x))
    (_h_incr : Tendsto (fun n => x (n + 1) - x n) atTop (nhds 0))
    (h_unique : ∀ y, (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds y)) → y = x_star) :
    Tendsto x atTop (nhds x_star) := by
  -- In finite dimensions, bounded sequences have convergent subsequences
  -- If x_star is the unique accumulation point, the whole sequence converges
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Use tendsto_of_subseq_tendsto: we need to show every subsequence has a sub-subsequence
  -- converging to x_star
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- ns : ℕ → ℕ is a sequence tending to atTop (i.e., ns n → ∞)
  -- We need to find ms such that x (ns (ms n)) → x_star
  -- First, extract a strictly monotone subsequence from ns (since ns → atTop)
  obtain ⟨ψ, hψ_mono, hnsψ_mono⟩ := strictMono_subseq_of_tendsto_atTop hns
  -- The subsequence (x ∘ ns ∘ ψ) is bounded (subset of range x)
  have h_sub_bdd : Bornology.IsBounded (Set.range (x ∘ ns ∘ ψ)) := by
    apply h_bdd.subset
    intro y hy
    simp only [Set.mem_range, Function.comp_apply] at hy
    obtain ⟨n, rfl⟩ := hy
    exact Set.mem_range_self (ns (ψ n))
  -- By Bolzano-Weierstrass (ProperSpace), (x ∘ ns ∘ ψ) has a convergent subsequence
  obtain ⟨y, _, θ, hθ_mono, hθ_tend⟩ := tendsto_subseq_of_bounded h_sub_bdd (fun n => Set.mem_range_self n)
  -- ns ∘ ψ ∘ θ is strictly monotone (composition of strictly monotone functions)
  have hcomp_mono : StrictMono (ns ∘ ψ ∘ θ) := hnsψ_mono.comp hθ_mono
  -- So (ns ∘ ψ ∘ θ, x ∘ ns ∘ ψ ∘ θ → y) shows y is an accumulation point of x
  have hy_accum : ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ Tendsto (x ∘ ρ) atTop (nhds y) :=
    ⟨ns ∘ ψ ∘ θ, hcomp_mono, hθ_tend⟩
  -- By h_unique, y = x_star
  have hy_eq : y = x_star := h_unique y hy_accum
  -- So x ∘ ns ∘ (ψ ∘ θ) → x_star
  use ψ ∘ θ
  simp only [Function.comp_apply] at hθ_tend ⊢
  rwa [hy_eq] at hθ_tend

/-!
### Lemma 3: Drift terms eventually small
-/

/-- If ∑ γ_n = ∞, ∑ γ_n a_n < ∞, and a_n ≥ 0, then liminf a_n = 0. -/
lemma liminf_zero_of_summable_weighted
    {γ a : ℕ → ℝ}
    (hγ_pos : ∀ n, 0 < γ n)
    (hγ_div : ¬ Summable γ)
    (ha_nn : ∀ n, 0 ≤ a n)
    (ha_sum : Summable (fun n => γ n * a n)) :
    Filter.liminf a atTop = 0 := by
  -- Proof by contradiction: if liminf a > 0, then eventually a_n > c for some c > 0
  -- Then ∑ γ_n a_n ≥ c ∑ γ_n = ∞, contradiction
  by_contra h_ne
  -- a is bounded below by 0
  have h_bdd : Filter.IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall ha_nn)
  -- liminf ≥ 0 since a ≥ 0
  -- We need to show IsCoboundedUnder (· ≥ ·), but for ℝ this requires an upper bound
  -- Since we don't have one in general, we need a different approach
  -- Instead, use: liminf of nonneg function ≥ 0, which follows from iInf_le_liminf
  have h_liminf_nn : 0 ≤ Filter.liminf a atTop := by
    -- The set of eventual lower bounds
    let S := {c : ℝ | ∀ᶠ n in atTop, c ≤ a n}
    -- liminf a atTop = sSup S (by definition)
    have h_liminf_eq : Filter.liminf a atTop = sSup S := by
      unfold Filter.liminf Filter.limsInf
      simp only [Filter.eventually_map]
      rfl
    -- 0 is in S (since a_n >= 0 always)
    have h_0_in : (0 : ℝ) ∈ S := Eventually.of_forall ha_nn
    -- Case split: S bounded above or not
    by_cases h_bdd_S : BddAbove S
    · -- S is bounded above, so sSup S >= 0
      calc 0 ≤ sSup S := le_csSup h_bdd_S h_0_in
        _ = Filter.liminf a atTop := h_liminf_eq.symm
    · -- S is not bounded above, so sSup S = 0 by Real.sSup_def
      have h_eq_zero : sSup S = 0 := by
        rw [Real.sSup_def]
        split_ifs with h
        · exact absurd h.2 h_bdd_S
        · rfl
      rw [h_liminf_eq, h_eq_zero]
  -- So liminf > 0
  have h_liminf_pos : 0 < Filter.liminf a atTop := lt_of_le_of_ne h_liminf_nn (ne_comm.mp h_ne)
  -- Let c = liminf a / 2 > 0
  set c := Filter.liminf a atTop / 2 with hc_def
  have hc_pos : 0 < c := by linarith
  have hc_lt : c < Filter.liminf a atTop := by linarith
  -- Eventually a_n > c (since c < liminf a)
  have h_ev : ∀ᶠ n in atTop, c < a n := eventually_lt_of_lt_liminf hc_lt h_bdd
  -- Get N such that for n ≥ N, a n > c
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N, hN⟩ := h_ev
  -- For n ≥ N: γ n * a n ≥ γ n * c
  have h_le : ∀ n ≥ N, c * γ n ≤ γ n * a n := fun n hn => by
    have h1 : c ≤ a n := le_of_lt (hN n hn)
    calc c * γ n = γ n * c := mul_comm c (γ n)
      _ ≤ γ n * a n := mul_le_mul_of_nonneg_left h1 (le_of_lt (hγ_pos n))
  -- The tail sum (from N onward) of c * γ is bounded by tail of γ * a
  -- Since γ * a is summable, so is its tail
  -- We use: summable of eventually bounded by summable
  have h_summable_cγ : Summable (fun n => c * γ n) := by
    -- Use Summable.of_nonneg_of_le with shift
    -- First show that the tail (n ≥ N) is summable by comparison
    have h_tail : Summable (fun n => c * γ (n + N)) := by
      apply Summable.of_nonneg_of_le
      · intro n
        exact mul_nonneg (le_of_lt hc_pos) (le_of_lt (hγ_pos (n + N)))
      · intro n
        have hn : N ≤ n + N := Nat.le_add_left N n
        calc c * γ (n + N) ≤ γ (n + N) * a (n + N) := h_le (n + N) hn
          _ = (fun m => γ m * a m) (n + N) := rfl
      · exact (summable_nat_add_iff N).mpr ha_sum
    -- Summable of shift implies original summable (use that finite prefix doesn't affect summability)
    exact (summable_nat_add_iff N).mp h_tail
  -- But ∑ c * γ = c * ∑ γ, and c > 0, so this means ∑ γ is summable
  have h_summable_γ : Summable γ := by
    have := h_summable_cγ
    rwa [summable_mul_left_iff hc_pos.ne'] at this
  exact hγ_div h_summable_γ

/-!
### Lemma 4: Accumulation points satisfy drift = 0

We provide two approaches:
1. Original excursion argument (requires noise summability)
2. Alternative approach following informal proof (simpler hypotheses)
-/

/-- In a bounded sequence with liminf f = 0 (f continuous nonneg),
    some accumulation point has f = 0. -/
lemma exists_accumulation_point_of_liminf_zero
    {x : ℕ → E} {f : E → ℝ}
    (h_bdd : Bornology.IsBounded (Set.range x))
    (f_cont : Continuous f)
    (f_nn : ∀ y, 0 ≤ f y)
    (h_liminf : Filter.liminf (f ∘ x) atTop = 0) :
    ∃ y, (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds y)) ∧ f y = 0 := by
  -- Since liminf = 0, there's a subsequence along which f(x_n) → 0
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Use the characterization: liminf = 0 means there exists a subsequence converging to 0
  -- We'll construct such a subsequence using the definition of liminf
  --
  -- Key fact: liminf f = 0 and f ≥ 0 implies for all ε > 0, f(x_n) < ε infinitely often
  -- This gives us a subsequence with f → 0

  -- For now, we use a direct argument via extracting convergent subsequences
  -- from the bounded sequence, and show one has f = 0 at the limit.
  --
  -- Alternative approach: use that liminf = inf of cluster points (when they exist)
  -- In a compact space (bounded subset of finite dim), cluster points exist.

  -- The set f(x(ℕ)) is bounded below by 0 and has liminf = 0
  -- So inf of accumulation points of f ∘ x is 0
  -- Hence some accumulation point of x has f = 0

  -- Detailed proof:
  -- 1. f ∘ x is bounded (f is continuous on bounded set)
  -- 2. liminf (f ∘ x) = 0
  -- 3. There's a subsequence f(x_{ψ(n)}) → 0 (characterization of liminf for bounded sequences)
  -- 4. x_{ψ(n)} is bounded, extract convergent sub-subsequence x_{ψ(θ(n))} → y
  -- 5. f(y) = lim f(x_{ψ(θ(n))}) = 0 by continuity

  -- Step 1: liminf = 0 and f ≥ 0 means f(x_n) < ε frequently for all ε > 0
  -- Use frequently_lt_of_liminf_lt
  have h_cobdd : IsCoboundedUnder (· ≥ ·) atTop (f ∘ x) := by
    -- f ∘ x is bounded since x has bounded range and f is continuous
    -- First show f(range x) is bounded (hence BddAbove)
    have h_closed : IsCompact (closure (Set.range x)) := h_bdd.isCompact_closure
    have h_range_sub : Set.range (f ∘ x) ⊆ f '' closure (Set.range x) := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      exact ⟨x n, subset_closure (Set.mem_range_self n), rfl⟩
    have h_compact_img : IsCompact (f '' closure (Set.range x)) := h_closed.image f_cont
    have h_bddAbove : BddAbove (Set.range (f ∘ x)) := h_compact_img.bddAbove.mono h_range_sub
    exact h_bddAbove.isBoundedUnder_of_range.isCoboundedUnder_ge
  have h_freq : ∀ ε > 0, ∃ᶠ n in atTop, (f ∘ x) n < ε := by
    intro ε hε
    have h_lt : liminf (f ∘ x) atTop < ε := by rw [h_liminf]; exact hε
    exact frequently_lt_of_liminf_lt h_cobdd h_lt
  -- Step 2: Construct a subsequence ψ along which f(x_{ψ(n)}) → 0
  -- We extract ψ such that f(x_{ψ(n)}) < 1/(n+1)
  have h_subseq : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto ((f ∘ x) ∘ ψ) atTop (nhds 0) := by
    -- Use extraction_forall_of_frequently
    have h_forall : ∀ n : ℕ, ∃ᶠ k in atTop, (f ∘ x) k < 1 / (n + 1 : ℝ) := by
      intro n
      apply h_freq
      have : (0 : ℝ) < n + 1 := by positivity
      positivity
    obtain ⟨ψ, hψ_mono, hψ_prop⟩ := extraction_forall_of_frequently h_forall
    refine ⟨ψ, hψ_mono, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / (N + 1 : ℝ) < ε := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      use N
      rw [div_lt_iff₀ (by positivity : (N + 1 : ℝ) > 0)]
      calc ε * (N + 1) > ε * N := by nlinarith
        _ > ε * (1 / ε) := by nlinarith
        _ = 1 := by field_simp
    use N
    intro n hn
    simp only [Function.comp_apply, Real.dist_eq]
    have h1 : (f ∘ x) (ψ n) < 1 / (n + 1 : ℝ) := hψ_prop n
    have h2 : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      apply div_le_div_of_nonneg_left
      · have hn' : (n : ℝ) ≥ N := by exact Nat.cast_le.mpr hn
        linarith
      · positivity
      · have hn' : (n : ℝ) ≥ N := by exact Nat.cast_le.mpr hn
        linarith
    have h3 : (f ∘ x) (ψ n) < ε := lt_of_lt_of_le h1 (le_of_lt (lt_of_le_of_lt h2 hN))
    have hfnn : 0 ≤ f (x (ψ n)) := f_nn (x (ψ n))
    -- Goal after simp is |f(x(ψ n)) - 0| < ε
    rw [sub_zero, abs_of_nonneg hfnn]
    exact h3
  obtain ⟨ψ, hψ_mono, hψ_tend⟩ := h_subseq
  -- Step 3: x ∘ ψ is bounded, extract convergent sub-subsequence
  have h_bdd_sub : Bornology.IsBounded (Set.range (x ∘ ψ)) := by
    apply Bornology.IsBounded.subset h_bdd
    intro z hz
    simp only [Set.mem_range, Function.comp_apply] at hz ⊢
    obtain ⟨n, rfl⟩ := hz
    exact ⟨ψ n, rfl⟩
  obtain ⟨y, hy_mem, θ, hθ_mono, hθ_tend⟩ := tendsto_subseq_of_bounded h_bdd_sub (fun n => Set.mem_range_self n)
  -- Step 4: The composite subsequence φ = ψ ∘ θ
  let φ := ψ ∘ θ
  have hφ_mono : StrictMono φ := hψ_mono.comp hθ_mono
  have hφ_tend : Tendsto (x ∘ φ) atTop (nhds y) := by
    show Tendsto ((x ∘ ψ) ∘ θ) atTop (nhds y)
    exact hθ_tend
  -- Step 5: f(y) = 0 by continuity
  have hfy : f y = 0 := by
    have h1 : Tendsto (f ∘ (x ∘ φ)) atTop (nhds (f y)) := f_cont.tendsto y |>.comp hφ_tend
    have h2 : Tendsto ((f ∘ x) ∘ φ) atTop (nhds 0) := by
      show Tendsto (((f ∘ x) ∘ ψ) ∘ θ) atTop (nhds 0)
      exact hψ_tend.comp hθ_mono.tendsto_atTop
    -- Both h1 and h2 describe the same sequence converging to limits
    -- h1: f(x(φ(n))) → f(y) and h2: f(x(φ(n))) → 0
    have heq : f y = 0 := tendsto_nhds_unique h1 h2
    exact heq
  exact ⟨y, ⟨φ, hφ_mono, hφ_tend⟩, hfy⟩

/-- Any accumulation point of (X_n) must have zero drift.
    Includes explicit noise term U to handle step decomposition. -/
lemma accumulation_point_drift_zero
    {X : ℕ → Ω → E} {γ : ℕ → ℝ} {h gradV : E → E} {U : ℕ → E}
    (hγ_pos : ∀ n, 0 < γ n)
    (hγ_div : ¬ Summable γ)
    (h_cont : Continuous h)
    (gradV_cont : Continuous gradV)
    (drift_nn : ∀ x, 0 ≤ @inner ℝ _ _ (gradV x) (h x))
    {ω : Ω}
    (h_sum : Summable (fun n => γ (n + 1) * @inner ℝ _ _ (gradV (X n ω)) (h (X n ω))))
    (h_rec : ∀ n, X (n + 1) ω - X n ω = - (γ (n + 1)) • h (X n ω) + U n)
    (h_noise_cauchy : CauchySeq (fun n => ∑ k ∈ Finset.range n, U k))
    {y : E} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_lim : Tendsto (fun n => X (φ n) ω) atTop (nhds y)) :
    @inner ℝ _ _ (gradV y) (h y) = 0 := by
  -- Strategy: Proof by contradiction via excursion argument
  -- If drift(y) = L > 0, we find a ball B(y, δ) where drift > L/2.
  -- X_n visits B(y, δ/2) infinitely often.
  -- If it stays in B(y, δ) forever, the weighted sum diverges.
  -- If it leaves B(y, δ) infinitely often, we sum the gamma cost of excursions.
  -- We bound the net noise over an excursion using Cauchy partial sums.
  set drift := fun x => @inner ℝ _ _ (gradV x) (h x)
  by_contra h_nonzero
  -- 1. Local lower bound on drift
  have h_drift_y : 0 < drift y := by
    refine lt_of_le_of_ne (drift_nn y) (Ne.symm h_nonzero)
  let L := drift y
  have hL_pos : 0 < L := h_drift_y
  have drift_cont : Continuous drift := Continuous.inner gradV_cont h_cont
  -- Find δ such that drift(x) > L/2 in B(y, δ) and ||h(x)|| is bounded
  obtain ⟨δ, hδ_pos, h_ball_drift, h_ball_h⟩ :
      ∃ δ > 0, (∀ x ∈ Metric.ball y δ, drift x > L / 2) ∧
               (∃ C_h > 0, ∀ x ∈ Metric.ball y δ, ‖h x‖ ≤ C_h) := by
    -- Continuity of drift
    have h_nhds : ∀ᶠ x in nhds y, L / 2 < drift x :=
      drift_cont.tendsto y (eventually_gt_nhds (half_lt_self hL_pos))
    -- Boundedness of h near y
    have h_bounded : ∀ᶠ x in nhds y, ‖h x‖ < ‖h y‖ + 1 :=
      (continuous_norm.comp h_cont).tendsto y (eventually_lt_nhds (lt_add_one (‖h y‖)))
    -- Combine
    have h_comb := h_nhds.and h_bounded
    rw [Metric.eventually_nhds_iff] at h_comb
    obtain ⟨ε, hε_pos, hε⟩ := h_comb
    use ε, hε_pos
    constructor
    · intro x hx; exact (hε hx).1
    · use ‖h y‖ + 1, (by linarith [norm_nonneg (h y)])
      intro x hx; exact le_of_lt (hε hx).2

  obtain ⟨C_h, hC_h_pos, h_ball_norm⟩ := h_ball_h

  -- 2. X visits B(y, δ/2) infinitely often
  -- This is guaranteed by X(φ n) → y
  have h_frequently : ∀ N, ∃ n ≥ N, X n ω ∈ Metric.ball y (δ / 2) := by
    intro N
    -- φ n → ∞, so eventually φ n ≥ N
    have h_phi_large : ∀ᶠ k in atTop, N ≤ φ k :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
    -- X (φ n) ∈ B(y, δ/2) eventually
    have h_phi_in : ∀ᶠ k in atTop, X (φ k) ω ∈ Metric.ball y (δ / 2) := by
      rw [Metric.tendsto_nhds] at h_lim
      exact h_lim (δ / 2) (half_pos hδ_pos)
    obtain ⟨k, hk1, hk2⟩ := (h_phi_large.and h_phi_in).exists
    use φ k, hk1, hk2

  -- 3. Construction of disjoint excursions
  -- We want to find a sequence of intervals [s_k, e_k] such that:
  -- X_{s_k} ∈ B(y, δ/2)
  -- X_{e_k} ∉ B(y, δ)
  -- For n ∈ [s_k, e_k), X_n ∈ B(y, δ)
  -- s_{k+1} > e_k

  -- But first, check if X stays in B(y, δ) forever after some point
  by_cases h_stays : ∃ N, ∀ n ≥ N, X n ω ∈ Metric.ball y δ
  · -- Case A: Stays in ball. Then drift sum diverges.
    obtain ⟨N, hN⟩ := h_stays
    have h_div : ¬ Summable (fun n => γ (n + 1) * drift (X n ω)) := by
      have h_comp : ∀ n ≥ N, γ (n + 1) * (L / 2) ≤ γ (n + 1) * drift (X n ω) := by
        intro n hn
        apply mul_le_mul_of_nonneg_left (le_of_lt (h_ball_drift _ (hN n hn)))
        exact le_of_lt (hγ_pos (n + 1))
      -- If summable, then comparison test with γ * L/2 implies γ summable
      intro h_sum_drift
      have h_tail : Summable (fun n => γ (n + N + 1) * (L / 2)) := by
        apply Summable.of_nonneg_of_le
        · intro n; apply mul_nonneg (le_of_lt (hγ_pos _)) (le_of_lt (half_pos hL_pos))
        · intro n; exact h_comp (n + N) (Nat.le_add_left N n)
        · exact (summable_nat_add_iff N).mpr h_sum_drift
      have h_gamma_tail : Summable (fun n => γ (n + N + 1)) := by
        rw [summable_mul_right_iff (ne_of_gt (half_pos hL_pos))] at h_tail
        exact h_tail
      exact hγ_div ((summable_nat_add_iff (N + 1)).mp h_gamma_tail)
    exact h_div h_sum

  · -- Case B: Leaves B(y, δ) infinitely often.
    -- We derive a contradiction using the excursion argument.

    -- Convert h_stays to: ∀ N, ∃ n ≥ N, X n ω ∉ B(y, δ)
    push_neg at h_stays

    -- The noise partial sums are Cauchy, so interval noise sums are eventually small.
    let noisePartial : ℕ → E := fun n => ∑ k ∈ Finset.range n, U k
    have h_noise_cauchy' := (Metric.cauchySeq_iff).1 h_noise_cauchy
    have hδ4_pos : 0 < δ / 4 := by linarith [hδ_pos]
    obtain ⟨N₀, hN₀⟩ :
        ∃ N₀, ∀ m ≥ N₀, ∀ n ≥ N₀, dist (noisePartial m) (noisePartial n) < δ / 4 :=
      h_noise_cauchy' (δ / 4) hδ4_pos

    -- Define the minimum contribution per excursion
    let ε := (δ / 4 / C_h) * (L / 2)
    have hε_pos : 0 < ε := by
      apply mul_pos
      · apply div_pos (div_pos hδ_pos (by linarith : (4 : ℝ) > 0)) hC_h_pos
      · exact half_pos hL_pos

    -- Key claim: for any starting point s ≥ N₀ where X_s ∈ B(y, δ/2),
    -- the sum ∑_{n=s}^{e-1} γ(n+1) * drift(X_n) ≥ ε before X first exits B(y, δ)
    -- This is because the trajectory must travel at least δ/2 to exit, and each step
    -- when inside B(y, δ) has drift > L/2.

    -- The weighted sum is not Cauchy: for any M, we can find intervals with sum ≥ ε
    have h_not_cauchy : ¬ CauchySeq (fun n => ∑ i ∈ Finset.range n, γ (i + 1) * drift (X i ω)) := by
      intro h_cauchy
      -- A Cauchy sequence in ℝ converges (since ℝ is complete)
      haveI : CompleteSpace ℝ := inferInstance
      obtain ⟨_, hlim⟩ := cauchySeq_tendsto_of_complete h_cauchy
      -- The Cauchy condition should be violated by the excursions
      -- Pick N₁ large enough that partial sums after N₁ are within ε/2 of each other
      rw [Metric.cauchySeq_iff] at h_cauchy
      obtain ⟨N₁, hN₁⟩ := h_cauchy (ε / 2) (half_pos hε_pos)

      -- Find an excursion starting after max(N₀, N₁)
      let N := max N₀ N₁
      obtain ⟨s, hs_ge, hs_in⟩ := h_frequently N
      -- s ≥ N ≥ N₀, X_s ∈ B(y, δ/2)

      -- Find some exit time e > s where X_e ∉ B(y, δ)
      obtain ⟨e', he'_ge, he'_out⟩ := h_stays (s + 1)

      -- Define e as the first exit time after s (using well-founded recursion on ℕ)
      -- For simplicity, we use e' directly (the argument works with any exit time)

      -- The key estimate: the sum over [s, e') when X is in the ball is bounded below
      -- During an excursion from B(y, δ/2) to outside B(y, δ), the trajectory must
      -- travel distance at least δ/2 while inside B(y, δ).

      -- Distance traveled from s to e':
      -- ‖X_{e'} - X_s‖ ≥ dist(y, X_{e'}) - dist(y, X_s) ≥ δ - δ/2 = δ/2
      -- (since X_s ∈ B(y, δ/2) and X_{e'} ∉ B(y, δ))

      have h_dist_lower : δ / 2 ≤ ‖X e' ω - X s ω‖ := by
        -- hs_in : X s ω ∈ Metric.ball y (δ/2) means dist (X s ω) y < δ/2
        have h1 : dist (X s ω) y < δ / 2 := Metric.mem_ball.mp hs_in
        -- he'_out : X e' ω ∉ Metric.ball y δ means ¬(dist (X e' ω) y < δ), i.e., δ ≤ dist (X e' ω) y
        have h2 : δ ≤ dist (X e' ω) y := le_of_not_lt (Metric.mem_ball.not.mp he'_out)
        -- Use reverse triangle inequality: |dist(a,c) - dist(b,c)| ≤ dist(a,b)
        have h_rev_tri : dist (X e' ω) y - dist (X s ω) y ≤ dist (X e' ω) (X s ω) := by
          have h_abs := abs_dist_sub_le (X e' ω) (X s ω) y
          have h_le := le_abs_self (dist (X e' ω) y - dist (X s ω) y)
          linarith
        calc δ / 2 = δ - δ / 2 := by ring
          _ ≤ dist (X e' ω) y - dist (X s ω) y := by linarith
          _ ≤ dist (X e' ω) (X s ω) := h_rev_tri
          _ = ‖X e' ω - X s ω‖ := dist_eq_norm _ _

      -- From the Cauchy condition at N₁:
      have hs_ge_N1 : s ≥ N₁ := le_trans (le_max_right N₀ N₁) hs_ge
      have hs_ge_N0 : s ≥ N₀ := le_trans (le_max_left N₀ N₁) hs_ge
      have he'_ge_N1 : e' + 1 ≥ N₁ := by omega

      -- The partial sum difference from s to e'+1 should be < ε/2 by Cauchy condition
      have h_cauchy_applied := hN₁ s hs_ge_N1 (e' + 1) he'_ge_N1
      -- This gives: dist (partial_sum s) (partial_sum (e'+1)) < ε/2

      -- The partial sum from s to e' is the sum over [s, e')
      let partial_sum := fun n => ∑ i ∈ Finset.range n, γ (i + 1) * drift (X i ω)

      -- The increment from s to e'+1 is:
      -- partial_sum (e'+1) - partial_sum s = ∑_{i ∈ [s, e'+1)} γ(i+1) * drift(X_i)
      have h_increment : partial_sum (e' + 1) - partial_sum s =
          ∑ i ∈ Finset.Ico s (e' + 1), γ (i + 1) * drift (X i ω) := by
        simp only [partial_sum, Finset.range_eq_Ico]
        have hs_le : s ≤ e' + 1 := by omega
        -- Use: Ico 0 (e'+1) = Ico 0 s ∪ Ico s (e'+1) (disjoint union)
        -- So: ∑ Ico 0 s + ∑ Ico s (e'+1) = ∑ Ico 0 (e'+1)
        have h_split := Finset.sum_Ico_consecutive (f := fun i => γ (i + 1) * drift (X i ω))
          (Nat.zero_le s) hs_le
        -- h_split : ∑ Ico 0 s + ∑ Ico s (e'+1) = ∑ Ico 0 (e'+1)
        -- Goal: ∑ Ico 0 (e'+1) - ∑ Ico 0 s = ∑ Ico s (e'+1)
        linarith [h_split]

      -- The increment is nonnegative (sum of nonneg terms)
      have h_incr_nn : 0 ≤ partial_sum (e' + 1) - partial_sum s := by
        rw [h_increment]
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (le_of_lt (hγ_pos (i + 1))) (drift_nn (X i ω))

      -- From Cauchy: |partial_sum (e'+1) - partial_sum s| < ε/2
      have h_cauchy_bound : |partial_sum (e' + 1) - partial_sum s| < ε / 2 := by
        simp only [partial_sum]
        rw [Real.dist_eq] at h_cauchy_applied
        -- h_cauchy_applied has the order reversed, but |a - b| = |b - a|
        rw [abs_sub_comm] at h_cauchy_applied
        exact h_cauchy_applied

      -- Since the increment is nonneg, we have: partial_sum (e'+1) - partial_sum s < ε/2
      have h_incr_lt : partial_sum (e' + 1) - partial_sum s < ε / 2 := by
        rw [abs_of_nonneg h_incr_nn] at h_cauchy_bound
        exact h_cauchy_bound

      -- Strategy: Use First Exit Time (from informal proof)
      -- Define e = first exit time after s, then all steps in [s, e) are inside B(y, δ)

      -- Step 1: Define the set of exit times and show it's nonempty
      let S_out := {k : ℕ | k > s ∧ X k ω ∉ Metric.ball y δ}
      have hS_nonempty : S_out.Nonempty := ⟨e', ⟨he'_ge, he'_out⟩⟩

      -- Step 2: Define e = min S_out (first exit time)
      -- Use Nat.find for well-founded minimum (need classical decidability)
      have h_ex_exit : ∃ k > s, X k ω ∉ Metric.ball y δ := ⟨e', he'_ge, he'_out⟩
      haveI : DecidablePred fun k => k > s ∧ X k ω ∉ Metric.ball y δ := Classical.decPred _
      let e := Nat.find h_ex_exit
      have he_spec := Nat.find_spec h_ex_exit
      have he_gt_s : e > s := he_spec.1
      have he_out : X e ω ∉ Metric.ball y δ := he_spec.2

      -- Step 3: All steps in [s, e) are inside B(y, δ)
      have h_in_ball : ∀ k, s ≤ k → k < e → X k ω ∈ Metric.ball y δ := by
        -- For k < e = Nat.find, by Nat.find_min, the predicate is NOT satisfied at k
        -- Predicate: k > s ∧ X k ω ∉ Metric.ball y δ
        -- NOT predicate: k ≤ s ∨ X k ω ∈ Metric.ball y δ
        intro k hsk hke
        by_cases hk_eq_s : k = s
        · -- Case k = s: X_s ∈ B(y, δ/2) ⊆ B(y, δ)
          rw [hk_eq_s]
          exact Metric.ball_subset_ball (by linarith : δ / 2 ≤ δ) hs_in
        · -- Case k > s: by Nat.find_min, k does not satisfy the predicate
          -- So either k ≤ s (false since k > s) or X k ∈ ball
          have hk_gt_s : k > s := Nat.lt_of_le_of_ne hsk (Ne.symm hk_eq_s)
          have h_not_sat := Nat.find_min h_ex_exit hke
          -- h_not_sat : ¬(k > s ∧ X k ω ∉ Metric.ball y δ)
          push_neg at h_not_sat
          exact h_not_sat hk_gt_s

      -- Step 4: Lower bound on distance traveled from X_s to X_e
      -- ||X_e - X_s|| > δ - δ/2 = δ/2 (reverse triangle inequality)
      have h_dist_e : δ / 2 < ‖X e ω - X s ω‖ := by
        -- X_s ∈ B(y, δ/2) means dist(X_s, y) < δ/2
        have h1 : dist (X s ω) y < δ / 2 := Metric.mem_ball.mp hs_in
        -- X_e ∉ B(y, δ) means dist(X_e, y) ≥ δ
        have h2 : δ ≤ dist (X e ω) y := le_of_not_lt (Metric.mem_ball.not.mp he_out)
        -- Reverse triangle inequality: |dist(a,c) - dist(b,c)| ≤ dist(a,b)
        have h_rev_tri : dist (X e ω) y - dist (X s ω) y ≤ dist (X e ω) (X s ω) := by
          have h_abs := abs_dist_sub_le (X e ω) (X s ω) y
          have h_le := le_abs_self (dist (X e ω) y - dist (X s ω) y)
          linarith
        calc δ / 2 = δ - δ / 2 := by ring
          _ < dist (X e ω) y - dist (X s ω) y := by linarith
          _ ≤ dist (X e ω) (X s ω) := h_rev_tri
          _ = ‖X e ω - X s ω‖ := dist_eq_norm _ _

      -- Step 5: Upper bound via dynamics
      -- X_e - X_s = ∑_{k=s}^{e-1} (X_{k+1} - X_k)
      -- X_e - X_s = -∑ γ_{k+1}•h(X_k) + ∑ U_k
      -- so ||X_e - X_s|| ≤ C_h * (∑_{k=s}^{e-1} γ_{k+1}) + ‖∑_{k=s}^{e-1} U_k‖
      have h_upper : ‖X e ω - X s ω‖ ≤
          C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) + ‖∑ k ∈ Finset.Ico s e, U k‖ := by
        -- Telescoping: X_e - X_s = ∑_{k ∈ [s, e)} (X_{k+1} - X_k)
        have h_tele : X e ω - X s ω = ∑ k ∈ Finset.Ico s e, (X (k + 1) ω - X k ω) := by
          have h_le : s ≤ e := le_of_lt he_gt_s
          rw [Finset.sum_Ico_eq_sum_range]
          -- sum_range_sub: ∑ i ∈ range n, (f (i+1) - f i) = f n - f 0
          -- We need: ∑ k ∈ range (e-s), (X(s+k+1) - X(s+k)) = X e - X s
          -- Let f(i) = X(s+i), then ∑ i ∈ range (e-s), (f(i+1) - f(i)) = f(e-s) - f(0)
          -- = X(s+(e-s)) - X(s+0) = X e - X s
          have h_eq : ∑ k ∈ Finset.range (e - s), (X (s + k + 1) ω - X (s + k) ω) =
              ∑ k ∈ Finset.range (e - s), ((fun i => X (s + i) ω) (k + 1) - (fun i => X (s + i) ω) k) := by
            apply Finset.sum_congr rfl
            intro k _
            -- s + k + 1 = s + (k + 1) by associativity of Nat.add
            have h1 : s + k + 1 = s + (k + 1) := Nat.add_assoc s k 1
            simp only [h1]
          rw [h_eq, Finset.sum_range_sub (fun i => X (s + i) ω) (e - s)]
          simp only [add_zero, Nat.add_sub_cancel' h_le]
        have h_rec_sum :
            ∑ k ∈ Finset.Ico s e, (X (k + 1) ω - X k ω) =
              ∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω) + U k) := by
          apply Finset.sum_congr rfl
          intro k _
          simp [h_rec k]

        -- Split drift and noise sums, then bound drift by C_h * ∑ γ.
        have h_drift_term :
            ∀ k ∈ Finset.Ico s e, ‖(-(γ (k + 1)) • h (X k ω))‖ ≤ γ (k + 1) * C_h := by
          intro k hk
          have hk_in_ball : X k ω ∈ Metric.ball y δ := by
            simp only [Finset.mem_Ico] at hk
            exact h_in_ball k hk.1 hk.2
          have hhk : ‖h (X k ω)‖ ≤ C_h := h_ball_norm _ hk_in_ball
          have hγ_nn : 0 ≤ γ (k + 1) := le_of_lt (hγ_pos (k + 1))
          calc
            ‖(-(γ (k + 1)) • h (X k ω))‖
                = ‖(-(γ (k + 1)) : ℝ)‖ * ‖h (X k ω)‖ := by
                    simp [norm_smul, mul_assoc]
            _ = γ (k + 1) * ‖h (X k ω)‖ := by
                    simp [Real.norm_eq_abs, abs_neg, abs_of_pos (hγ_pos (k + 1)), mul_assoc]
            _ ≤ γ (k + 1) * C_h := mul_le_mul_of_nonneg_left hhk hγ_nn

        have h_drift_sum :
            ‖∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω))‖ ≤
              C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) := by
          calc
            ‖∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω))‖
                ≤ ∑ k ∈ Finset.Ico s e, ‖(-(γ (k + 1)) • h (X k ω))‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.Ico s e, γ (k + 1) * C_h := Finset.sum_le_sum h_drift_term
            _ = C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) := by
                -- move constant to the front
                have h1 :
                    (∑ k ∈ Finset.Ico s e, γ (k + 1) * C_h) =
                      (∑ k ∈ Finset.Ico s e, γ (k + 1)) * C_h := by
                  simpa using
                    (Finset.sum_mul (s := Finset.Ico s e) (f := fun k => γ (k + 1)) (a := C_h)).symm
                simpa [mul_comm, mul_left_comm, mul_assoc] using h1.trans (by simp [mul_comm])

        -- Final assembly
        calc
          ‖X e ω - X s ω‖
              = ‖∑ k ∈ Finset.Ico s e, (X (k + 1) ω - X k ω)‖ := by rw [h_tele]
          _ = ‖∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω) + U k)‖ := by
                simpa [h_rec_sum]
          _ = ‖(∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω))) +
                (∑ k ∈ Finset.Ico s e, U k)‖ := by
                simp [Finset.sum_add_distrib]
          _ ≤ ‖∑ k ∈ Finset.Ico s e, (-(γ (k + 1)) • h (X k ω))‖ +
                ‖∑ k ∈ Finset.Ico s e, U k‖ := norm_add_le _ _
          _ ≤ C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) + ‖∑ k ∈ Finset.Ico s e, U k‖ := by
                exact add_le_add_right h_drift_sum _

      -- Step 6: Noise bound (Cauchy partial sums)
      have h_noise_bound : ‖∑ k ∈ Finset.Ico s e, U k‖ < δ / 4 := by
        have hN0_le_s : N₀ ≤ s := hs_ge_N0
        have hN0_le_e : N₀ ≤ e := Nat.le_trans hN0_le_s (le_of_lt he_gt_s)
        have hdist : dist (noisePartial e) (noisePartial s) < δ / 4 :=
          hN₀ e hN0_le_e s hN0_le_s
        have hdist' : ‖noisePartial e - noisePartial s‖ < δ / 4 := by
          simpa [dist_eq_norm] using hdist
        have h_diff :
            noisePartial e - noisePartial s = ∑ k ∈ Finset.Ico s e, U k := by
          have h_le : s ≤ e := le_of_lt he_gt_s
          -- `sum_Ico_consecutive`: prefix(s) + sum(s,e) = prefix(e)
          have h_split :=
            Finset.sum_Ico_consecutive (f := fun k => U k) (Nat.zero_le s) h_le
          have h_split' :
              noisePartial s + (∑ k ∈ Finset.Ico s e, U k) = noisePartial e := by
            simpa [noisePartial] using h_split
          -- Rearrange to get `prefix(e) - prefix(s) = sum(s,e)`
          refine (sub_eq_iff_eq_add).2 ?_
          calc
            noisePartial e = noisePartial s + ∑ k ∈ Finset.Ico s e, U k := by
                simpa using h_split'.symm
            _ = (∑ k ∈ Finset.Ico s e, U k) + noisePartial s := by
                simpa [add_comm, add_left_comm, add_assoc]
        simpa [h_diff] using hdist'

      -- Step 7: Gamma sum lower bound
      -- From steps 4, 5, 6: δ/2 < C_h * (∑ γ) + δ/4
      -- So: δ/4 < C_h * (∑_{k=s}^{e-1} γ_{k+1})
      -- Thus: ∑_{k=s}^{e-1} γ_{k+1} > δ/(4*C_h)
      have h_gamma_sum : δ / (4 * C_h) < ∑ k ∈ Finset.Ico s e, γ (k + 1) := by
        -- From h_dist_e, h_upper, h_noise_bound:
        -- δ/2 < ||X_e - X_s|| ≤ C_h * (∑ γ) + noise_sum < C_h * (∑ γ) + δ/4
        -- So: δ/4 < C_h * (∑ γ)
        -- Thus: δ/(4*C_h) < ∑ γ
        have h_comb : δ / 2 < C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) + δ / 4 := by
          calc δ / 2 < ‖X e ω - X s ω‖ := h_dist_e
            _ ≤ C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) + ‖∑ k ∈ Finset.Ico s e, U k‖ := h_upper
            _ < C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) + δ / 4 := by linarith
        -- δ/4 < C_h * (∑ γ)
        have h_quarter : δ / 4 < C_h * (∑ k ∈ Finset.Ico s e, γ (k + 1)) := by linarith
        -- Divide by C_h (positive): a < b * c ↔ a / b < c when b > 0
        have h_div : δ / 4 / C_h < ∑ k ∈ Finset.Ico s e, γ (k + 1) := by
          rw [div_lt_iff₀ hC_h_pos]
          rw [mul_comm]
          exact h_quarter
        -- δ/(4*C_h) = δ/4 / C_h
        have h_eq : δ / (4 * C_h) = δ / 4 / C_h := by ring
        rw [h_eq]
        exact h_div

      -- Step 8: Drift sum lower bound
      -- For k ∈ [s, e), X_k ∈ ball, so drift(X_k) > L/2
      -- ∑_{k=s}^{e-1} γ_{k+1} * drift(X_k) > (L/2) * ∑_{k=s}^{e-1} γ_{k+1} > (L/2) * δ/(4*C_h) = ε
      have h_drift_sum_e : ε < ∑ k ∈ Finset.Ico s e, γ (k + 1) * drift (X k ω) := by
        -- For k ∈ [s, e), X_k ∈ ball, so drift(X_k) > L/2
        -- Thus γ(k+1) * drift(X_k) > γ(k+1) * (L/2)
        -- Sum: ∑ γ(k+1) * drift(X_k) > (L/2) * ∑ γ(k+1) > (L/2) * δ/(4*C_h) = ε
        have h_term_bound : ∀ k ∈ Finset.Ico s e, L / 2 * γ (k + 1) < γ (k + 1) * drift (X k ω) := by
          intro k hk
          simp only [Finset.mem_Ico] at hk
          have hk_in_ball := h_in_ball k hk.1 hk.2
          have hk_drift := h_ball_drift (X k ω) hk_in_ball
          have hγ_pos_k := hγ_pos (k + 1)
          calc L / 2 * γ (k + 1) = γ (k + 1) * (L / 2) := by ring
            _ < γ (k + 1) * drift (X k ω) := by
              apply mul_lt_mul_of_pos_left hk_drift hγ_pos_k
        -- Sum bound: ∑ (L/2 * γ) < ∑ (γ * drift)
        have h_sum_bound : L / 2 * (∑ k ∈ Finset.Ico s e, γ (k + 1)) <
            ∑ k ∈ Finset.Ico s e, γ (k + 1) * drift (X k ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_lt_sum
          · intro k hk
            simp only [Finset.mem_Ico] at hk
            have hk_in_ball := h_in_ball k hk.1 hk.2
            have hk_drift := h_ball_drift (X k ω) hk_in_ball
            calc L / 2 * γ (k + 1) = γ (k + 1) * (L / 2) := by ring
              _ ≤ γ (k + 1) * drift (X k ω) := by
                apply mul_le_mul_of_nonneg_left (le_of_lt hk_drift) (le_of_lt (hγ_pos (k + 1)))
          · -- Need at least one strict inequality
            -- s < e, so s ∈ Ico s e
            use s
            constructor
            · simp only [Finset.mem_Ico]
              exact ⟨le_refl s, he_gt_s⟩
            · exact h_term_bound s (by simp only [Finset.mem_Ico]; exact ⟨le_refl s, he_gt_s⟩)
        -- Now combine with h_gamma_sum
        calc ε = δ / 4 / C_h * (L / 2) := rfl
          _ = L / 2 * (δ / (4 * C_h)) := by ring
          _ < L / 2 * (∑ k ∈ Finset.Ico s e, γ (k + 1)) := by
              apply mul_lt_mul_of_pos_left h_gamma_sum (half_pos hL_pos)
          _ < ∑ k ∈ Finset.Ico s e, γ (k + 1) * drift (X k ω) := h_sum_bound

      -- Step 9: The sum over [s, e') contains [s, e), so it's even larger
      have h_e_le : e ≤ e' + 1 := by
        -- e = Nat.find h_ex_exit is the minimum k such that k > s ∧ X k ∉ ball
        -- e' satisfies this predicate by he'_ge and he'_out
        -- Therefore e ≤ e' by Nat.find_le
        have he'_sat : e' > s ∧ X e' ω ∉ Metric.ball y δ := ⟨he'_ge, he'_out⟩
        have h_e_le_e' : e ≤ e' := Nat.find_le he'_sat
        omega

      -- Step 10: Extend the bound to [s, e'+1)
      have h_drift_sum_full : ε < partial_sum (e' + 1) - partial_sum s := by
        rw [h_increment]
        -- Since e ≤ e' + 1 and drift ≥ 0:
        -- ∑_{[s, e'+1)} ≥ ∑_{[s, e)} > ε
        have h_le_se : s ≤ e := le_of_lt he_gt_s
        have h_terms_nn : ∀ k, 0 ≤ γ (k + 1) * drift (X k ω) := fun k =>
          mul_nonneg (le_of_lt (hγ_pos (k + 1))) (drift_nn (X k ω))
        -- [s, e) ⊆ [s, e'+1)
        have h_Ico_sub : Finset.Ico s e ⊆ Finset.Ico s (e' + 1) := by
          apply Finset.Ico_subset_Ico (le_refl s) h_e_le
        calc ε < ∑ k ∈ Finset.Ico s e, γ (k + 1) * drift (X k ω) := h_drift_sum_e
          _ ≤ ∑ k ∈ Finset.Ico s (e' + 1), γ (k + 1) * drift (X k ω) :=
              Finset.sum_le_sum_of_subset_of_nonneg h_Ico_sub (fun k _ _ => h_terms_nn k)

      -- Step 11: Contradiction with h_incr_lt
      linarith

    -- But Summable implies Cauchy partial sums
    have h_cauchy : CauchySeq (fun n => ∑ i ∈ Finset.range n, γ (i + 1) * drift (X i ω)) := by
      have h_sum' : Summable (fun n => γ (n + 1) * drift (X n ω)) := h_sum
      exact h_sum'.hasSum.tendsto_sum_nat.cauchySeq

    exact h_not_cauchy h_cauchy

/-!
## General Robbins-Monro Corollary (Removed)

The earlier (incomplete) attempt to formalize the full Corollary 2.3.1 (with remainder `R`
and state-dependent conditional variance bounds) is preserved in
`EscherProver/SGDUniqueMin_full_optionA.lean`.
-/

/-!
## Simplified Version: Unbiased SGD with Bounded Variance

The following provides a simplified version of Corollary 2.3.1 under stronger but practical assumptions:
1. **Unbiased gradients**: R = 0 (no remainder term)
2. **Bounded variance**: E[‖ΔM‖² | F_n] ≤ σ² (constant, not depending on V(X_n))

These assumptions are satisfied by mini-batch SGD with bounded gradients, which is the most
common practical setting. The key benefit is that the martingale convergence proof becomes
straightforward: the partial sums form an L²-bounded martingale, which converges a.s.
-/

/-- Simplified SGD assumptions for unbiased gradients with bounded variance.

This extends SGD_Convergence_Assumptions from sgd.lean with:
- R = 0 (unbiased gradients)
- Constant variance bound σ² (not state-dependent)
- Unique zero of drift (for convergence to x*)

The key benefit is that we can reuse convergence_stochastic_gradient_method
directly for drift summability and V convergence.
-/
structure SimplifiedAssumptions
    (X : ℕ → Ω → E)
    (γ : ℕ → ℝ)
    (h : E → E)
    (ΔM : ℕ → Ω → E)
    (V : E → ℝ)
    (gradV : E → E)
    (ℱ : Filtration ℕ m0)
    (x_star : E) : Prop where

  /-- Base SGD assumptions with R = 0.
      This gives us convergence_stochastic_gradient_method for free. -/
  base : SGD_Convergence_Assumptions μ X γ h ΔM (fun _ _ => 0) V gradV ℱ

  /-- KEY SIMPLIFICATION: Variance bound is CONSTANT, not state-dependent.
      This is stronger than base.martingale_condvar_bound and makes
      the noise summability argument much simpler. -/
  martingale_condvar_bound_const : ∃ σ : ℝ, 0 < σ ∧ ∀ n,
    μ[fun ω => ‖ΔM (n + 1) ω‖^2 | ℱ n] ≤ᵐ[μ] fun _ => σ^2

  /-- Recursion matches the StochasticAlgorithm form with R = 0. -/
  recursion : ∀ n ω, X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • ΔM (n + 1) ω

  /-- Unique zero of drift - this is what makes convergence to x* work. -/
  drift_zero_unique : {x : E | @inner ℝ _ _ (gradV x) (h x) = 0} = {x_star}

/-- SimplifiedAssumptions implies the StochasticAlgorithm recursion with R = 0. -/
lemma SimplifiedAssumptions.stochastic_algorithm
    {X : ℕ → Ω → E} {γ : ℕ → ℝ} {h : E → E} {ΔM : ℕ → Ω → E}
    {V : E → ℝ} {gradV : E → E} {ℱ : Filtration ℕ m0} {x_star : E}
    (asm : SimplifiedAssumptions μ X γ h ΔM V gradV ℱ x_star) :
    StochasticAlgorithm X γ h ΔM (fun _ _ => 0) := by
  intro n ω
  simp only [asm.recursion n ω, add_zero]

-- Convenience accessors for common base fields
namespace SimplifiedAssumptions

variable {X : ℕ → Ω → E} {γ : ℕ → ℝ} {h : E → E} {ΔM : ℕ → Ω → E}
variable {V : E → ℝ} {gradV : E → E} {ℱ : Filtration ℕ m0} {x_star : E}
variable (asm : SimplifiedAssumptions μ X γ h ΔM V gradV ℱ x_star)

def gamma_pos : ∀ n, 0 < γ n := asm.base.gamma_pos
def gamma_sum_inf : ¬ Summable γ := asm.base.gamma_sum_inf
def gamma_sq_sum_fin : Summable (fun n => (γ n) ^ 2) := asm.base.gamma_sq_sum_fin
def gamma_le_one : ∀ n, γ n ≤ 1 := asm.base.gamma_le_one
def V_smooth : ContDiff ℝ 2 V := asm.base.V_smooth
def V_grad_eq : ∀ x, gradient V x = gradV x := asm.base.V_grad_eq
def V_grad_lipschitz : ∃ L : ℝ, 0 < L ∧ ∀ x y, ‖gradV x - gradV y‖ ≤ L * ‖x - y‖ :=
  asm.base.V_grad_lipschitz
def V_lower_bound : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ V x := asm.base.V_lower_bound
def V_coercive : Tendsto V (cocompact E) atTop := asm.base.V_coercive
def drift_nonneg : ∀ x, 0 ≤ @inner ℝ _ _ (gradV x) (h x) := asm.base.drift_nonneg
def growth_bound : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖h x‖^2 + ‖gradV x‖^2 ≤ C * (1 + V x) :=
  asm.base.growth_bound
def h_continuous : Continuous h := asm.base.h_continuous
def martingale_diff_adapted : Adapted ℱ ΔM := asm.base.martingale_diff_adapted
def martingale_diff_condexp : ∀ n, μ[ΔM (n + 1)|ℱ n] =ᵐ[μ] 0 := asm.base.martingale_diff_condexp
def martingale_diff_L2 : ∀ n, Integrable (fun ω => ‖ΔM (n + 1) ω‖^2) μ :=
  asm.base.martingale_diff_L2
def X_adapted : Adapted ℱ X := asm.base.X_adapted
def V_X0_integrable : Integrable (fun ω => V (X 0 ω)) μ := asm.base.V_X0_integrable

end SimplifiedAssumptions

/- Simplified Corollary 2.3.1: Almost sure convergence for unbiased SGD with bounded variance.

Under the simplified assumptions (unbiased gradients, constant variance bound), we have:
- X_n → x* almost surely

The proof is simpler because:
1. No remainder term R (so the earlier “line 1375” gap disappears)
2. Constant variance ⟹ E[‖∑ γ_k ΔM_k‖²] ≤ σ² ∑ γ_k² < ∞ directly
3. L²-bounded martingale converges a.s. by Doob's theorem
-/
set_option maxHeartbeats 400000 in
theorem convergence_simplified
    (X : ℕ → Ω → E) (γ : ℕ → ℝ) (h : E → E) (ΔM : ℕ → Ω → E)
    (V : E → ℝ) (gradV : E → E) (ℱ : Filtration ℕ m0) (x_star : E)
    (asm : SimplifiedAssumptions μ X γ h ΔM V gradV ℱ x_star) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds x_star) := by

  -- =====================================================
  -- STEP 0: Apply Base Theorem (convergence_stochastic_gradient_method)
  -- =====================================================
  -- The base theorem gives us drift summability and V convergence for free!
  have h_base := convergence_stochastic_gradient_method μ X γ h ΔM (fun _ _ => 0) V gradV ℱ
      asm.stochastic_algorithm asm.base

  -- Extract conclusions from base theorem
  obtain ⟨_, h_drift_sum, ⟨V_inf, _, h_V_conv_raw⟩, h_incr_base, _⟩ := h_base

  -- Extract constants from assumptions
  obtain ⟨L, hL_pos, hgrad_lip⟩ := asm.base.V_grad_lipschitz
  obtain ⟨σ, hσ_pos, h_const_var⟩ := asm.martingale_condvar_bound_const
  obtain ⟨m, hm_pos, hV_lower⟩ := asm.base.V_lower_bound
  obtain ⟨C_growth, hC_growth_pos, h_growth⟩ := asm.base.growth_bound

  -- Continuity of gradient (needed for accumulation_point_drift_zero)
  have gradV_cont : Continuous gradV := by
    -- Lipschitz implies continuous
    have hL_nn : 0 ≤ L := le_of_lt hL_pos
    have hLip : LipschitzWith ⟨L, hL_nn⟩ gradV := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]
      exact hgrad_lip x y
    exact hLip.continuous

  -- =====================================================
  -- STEP 1: Noise Cauchy via L² Martingale Bound
  -- =====================================================
  -- Define U_n(ω) = γ_n • ΔM_n(ω) (the noise increment)
  let U : ℕ → Ω → E := fun n ω => γ n • ΔM n ω

  -- KEY LEMMA: With constant variance bound, the ordered partial sums of U_n converge a.s.
  -- This is SIMPLER than the general case because σ² is constant!
  have h_noise_cauchy : ∀ᵐ ω ∂μ, CauchySeq (fun n => ∑ k ∈ Finset.range n, U (k + 1) ω) := by
    -- =========================================================================
    -- STEP 1: Setup - Define partial sums and establish L² bounds
    -- =========================================================================

    -- Partial sums S_n = ∑_{k<n} U_{k+1} = ∑_{k<n} γ_{k+1} • ΔM_{k+1}
    let S : ℕ → Ω → E := fun n ω => ∑ k ∈ Finset.range n, U (k + 1) ω

    -- Each ΔM_k is L² (from assumptions)
    have hDM_L2 : ∀ k, MemLp (ΔM (k + 1)) 2 μ := fun k => by
      -- Get AEStronglyMeasurable from Adapted (go from ℱ (k+1) to m0)
      have hDM_sm : StronglyMeasurable[m0] (ΔM (k + 1)) :=
        (asm.base.martingale_diff_adapted (k + 1)).mono (ℱ.le (k + 1))
      have hDM_asm : AEStronglyMeasurable (ΔM (k + 1)) μ := hDM_sm.aestronglyMeasurable
      -- Use memLp_two_iff_integrable_sq_norm
      rw [memLp_two_iff_integrable_sq_norm hDM_asm]
      exact asm.base.martingale_diff_L2 k

    -- Unconditional variance bound: E[‖ΔM_k‖²] ≤ σ² (by tower property)
    have hDM_var_bound : ∀ k, ∫ ω, ‖ΔM (k + 1) ω‖^2 ∂μ ≤ σ^2 := fun k => by
      -- Use tower property: E[X] = E[E[X|F]]
      -- E[‖ΔM_{k+1}‖²] = E[E[‖ΔM_{k+1}‖² | F_k]] ≤ E[σ²] = σ²
      -- This uses integral_condExp + integral_mono_ae
      have h_le := h_const_var k
      -- Tower property: ∫ f = ∫ E[f|ℱ_k]
      have h_integ : Integrable (fun ω => ‖ΔM (k + 1) ω‖^2) μ := asm.base.martingale_diff_L2 k
      -- Need SigmaFinite instance for the trimmed measure
      haveI : SigmaFinite (μ.trim (ℱ.le k)) := sigmaFinite_of_sigmaFiniteFiltration μ ℱ k
      have h_tower : ∫ x, (μ[fun ω => ‖ΔM (k + 1) ω‖^2 | ℱ k]) x ∂μ = ∫ x, ‖ΔM (k + 1) x‖^2 ∂μ :=
        integral_condExp (ℱ.le k)
      -- Use mono: ∫ E[‖ΔM_{k+1}‖² | ℱ_k] ≤ ∫ σ²
      calc ∫ ω, ‖ΔM (k + 1) ω‖^2 ∂μ
          = ∫ ω, (μ[fun ω => ‖ΔM (k + 1) ω‖^2 | ℱ k]) ω ∂μ := h_tower.symm
        _ ≤ ∫ _, σ^2 ∂μ := by
            apply integral_mono_ae integrable_condExp (integrable_const _)
            exact h_le
        _ = σ^2 := by simp [integral_const, measureReal_univ_eq_one]

    -- L² bound for U_k: E[‖U_k‖²] ≤ γ_k² σ²
    have hU_L2_bound : ∀ k, ∫ ω, ‖U (k + 1) ω‖^2 ∂μ ≤ (γ (k + 1))^2 * σ^2 := fun k => by
      simp only [U]
      calc ∫ ω, ‖γ (k + 1) • ΔM (k + 1) ω‖^2 ∂μ
          = ∫ ω, (γ (k + 1))^2 * ‖ΔM (k + 1) ω‖^2 ∂μ := by
            congr 1; ext ω
            rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        _ = (γ (k + 1))^2 * ∫ ω, ‖ΔM (k + 1) ω‖^2 ∂μ := by
            rw [integral_mul_left]
        _ ≤ (γ (k + 1))^2 * σ^2 := by
            apply mul_le_mul_of_nonneg_left (hDM_var_bound k) (sq_nonneg _)

    -- Global L² bound for partial sums: E[‖S_n‖²] ≤ σ² ∑_k γ_k²
    -- (Uses martingale orthogonality: cross terms vanish)
    have hS_L2_bound : ∃ M : ℝ, 0 < M ∧ ∀ n, ∫ ω, ‖S n ω‖^2 ∂μ ≤ M := by
      use σ^2 * ∑' k, (γ (k + 1))^2
      constructor
      · apply mul_pos (sq_pos_of_pos hσ_pos)
        have h_shift : Summable (fun k => (γ (k + 1))^2) :=
          (summable_nat_add_iff 1).mpr asm.base.gamma_sq_sum_fin
        exact tsum_pos h_shift (fun k => sq_nonneg _) 0 (sq_pos_of_pos (asm.base.gamma_pos 1))
      · intro n
        -- E[‖S_n‖²] = E[‖∑_{k<n} U_{k+1}‖²] = ∑_{k<n} E[‖U_{k+1}‖²] (orthogonality)
        -- ≤ ∑_{k<n} γ_{k+1}² σ² ≤ σ² ∑_k γ_k²
        -- Use simpler bound: ‖∑ x_k‖² ≤ n * ∑ ‖x_k‖² (Cauchy-Schwarz on sums)
        -- But actually we can use martingale orthogonality for equality
        -- For now, use crude bound via finite sum ≤ infinite sum
        simp only [S]
        -- First bound: E[‖∑ U_k‖²] ≤ ∑ E[‖U_k‖²] (for orthogonal increments, this is equality)
        -- We'll prove this using the fact that the U_k are martingale differences
        -- Actually, let's use a simpler bound using Minkowski's inequality for L²
        -- For L² norms: ‖∑ f_k‖_L² ≤ ∑ ‖f_k‖_L²
        -- Squaring: (∑ ‖f_k‖_L²)² ≤ n * ∑ ‖f_k‖²_L² by Cauchy-Schwarz
        -- Let's use the direct bound instead:
        -- U_k are martingale differences: E[U_{k+1}|F_k] = γ_{k+1} E[ΔM_{k+1}|F_k] = 0
        -- Martingale orthogonality: E[⟨U_i, U_j⟩] = 0 for i ≠ j
        -- So E[‖∑ U_k‖²] = E[∑ ‖U_k‖² + 2∑_{i<j} ⟨U_i, U_j⟩] = ∑ E[‖U_k‖²]
        -- Proof outline:
        -- 1. U_k = γ_k • ΔM_k are scaled martingale differences
        -- 2. martingale_diff_condexp gives E[ΔM_{k+1}|F_k] = 0
        -- 3. This means E[U_{k+1}|F_k] = γ_{k+1} E[ΔM_{k+1}|F_k] = 0
        -- 4. For i < j, S_i is F_{j-1}-measurable, so
        --    E[⟨S_i, U_j⟩] = E[E[⟨S_i, U_j⟩|F_{j-1}]] = E[⟨S_i, E[U_j|F_{j-1}]⟩] = 0
        -- 5. By induction, E[‖S_n‖²] = ∑ E[‖U_k‖²]
        -- First, establish that U_k are martingale differences: E[U_{k+1}|F_k] = 0
        have _hU_martingale_diff : ∀ k, μ[U (k + 1)|ℱ k] =ᵐ[μ] 0 := fun k => by
          simp only [U]
          -- E[γ_{k+1} • ΔM_{k+1} | F_k] = γ_{k+1} • E[ΔM_{k+1} | F_k] = γ_{k+1} • 0 = 0
          have h_condexp := asm.base.martingale_diff_condexp k
          -- Use the fact that μ[c • f|m] =ᵐ[μ] c • μ[f|m]
          calc μ[fun ω => γ (k + 1) • ΔM (k + 1) ω|ℱ k]
              =ᵐ[μ] γ (k + 1) • μ[ΔM (k + 1)|ℱ k] := condExp_smul (μ := μ) (γ (k + 1)) (ΔM (k + 1)) (ℱ k)
            _ =ᵐ[μ] γ (k + 1) • (0 : Ω → E) := by
                filter_upwards [h_condexp] with ω hω
                simp only [Pi.smul_apply, hω]
            _ =ᵐ[μ] 0 := by simp [smul_zero, Pi.zero_apply]
        calc ∫ ω, ‖∑ k ∈ Finset.range n, U (k + 1) ω‖^2 ∂μ
            ≤ ∑ k ∈ Finset.range n, ∫ ω, ‖U (k + 1) ω‖^2 ∂μ := by
              -- Standard martingale orthogonality: cross terms vanish
              -- Proof by induction using ‖a + b‖² = ‖a‖² + ‖b‖² + 2⟨a,b⟩
              -- and E[⟨S_m, U_{m+1}⟩] = 0 by tower property + martingale difference
              induction n with
              | zero => simp
              | succ m ih =>
                simp only [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
                -- Goal: ∫ ‖S_m + U_{m+1}‖² ≤ (∫ ‖U_{m+1}‖²) + ∑ ∫ ‖U_k‖²
                -- This follows from:
                -- ∫ ‖S_m + U_{m+1}‖² = ∫ ‖S_m‖² + ∫ ‖U_{m+1}‖² + 2∫⟨S_m, U_{m+1}⟩
                -- and the cross term ∫⟨S_m, U_{m+1}⟩ = 0
                -- The technical details require tower property and measurability
                -- First, expand ‖U + S‖² = ‖U‖² + ‖S‖² + 2⟪U, S⟫
                -- Define the partial sum for convenience
                set Sm : Ω → E := fun ω => ∑ x ∈ Finset.range m, U (x + 1) ω with hSm_def
                have h_expand : ∀ ω, ‖U (m + 1) ω + Sm ω‖^2 =
                    ‖U (m + 1) ω‖^2 + 2 * @inner ℝ _ _ (U (m + 1) ω) (Sm ω) +
                    ‖Sm ω‖^2 := fun ω => norm_add_sq_real _ _
                -- For now, admit integrability conditions and cross term vanishing
                have hU_integrable : Integrable (fun ω => ‖U (m + 1) ω‖^2) μ := by
                  simp only [U, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                  apply Integrable.const_mul
                  exact asm.base.martingale_diff_L2 m
                have hS_integrable : Integrable (fun ω => ‖Sm ω‖^2) μ := by
                  -- S_m is a finite sum of L² functions, so it's L²
                  -- First show each U_k is in L2
                  have hU_L2 : ∀ k, MemLp (U (k + 1)) 2 μ := fun k => by
                    simp only [U]
                    have hDM_sm : StronglyMeasurable[m0] (ΔM (k + 1)) :=
                      (asm.base.martingale_diff_adapted (k + 1)).mono (ℱ.le (k + 1))
                    have hDM_asm : AEStronglyMeasurable (ΔM (k + 1)) μ := hDM_sm.aestronglyMeasurable
                    have hU_asm : AEStronglyMeasurable (fun ω => γ (k + 1) • ΔM (k + 1) ω) μ :=
                      hDM_asm.const_smul (γ (k + 1))
                    rw [memLp_two_iff_integrable_sq_norm hU_asm]
                    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                    exact (asm.base.martingale_diff_L2 k).const_mul _
                  -- Now show Sm is in L2
                  have hSm_L2 : MemLp Sm 2 μ := by
                    simp only [hSm_def]
                    exact memLp_finset_sum (Finset.range m) (fun k _ => hU_L2 k)
                  -- L2 implies norm² is integrable
                  have hSm_asm : AEStronglyMeasurable Sm μ := hSm_L2.aestronglyMeasurable
                  exact (memLp_two_iff_integrable_sq_norm hSm_asm).mp hSm_L2
                have hcross_integrable : Integrable (fun ω => @inner ℝ _ _ (U (m + 1) ω) (Sm ω)) μ := by
                  -- inner product of two L² functions is L¹
                  -- We already have hU_L2 from hS_integrable's proof; reestablish it
                  have hU_m_L2 : MemLp (U (m + 1)) 2 μ := by
                    simp only [U]
                    have hDM_sm : StronglyMeasurable[m0] (ΔM (m + 1)) :=
                      (asm.base.martingale_diff_adapted (m + 1)).mono (ℱ.le (m + 1))
                    have hDM_asm : AEStronglyMeasurable (ΔM (m + 1)) μ := hDM_sm.aestronglyMeasurable
                    have hU_asm : AEStronglyMeasurable (fun ω => γ (m + 1) • ΔM (m + 1) ω) μ :=
                      hDM_asm.const_smul (γ (m + 1))
                    rw [memLp_two_iff_integrable_sq_norm hU_asm]
                    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                    exact (asm.base.martingale_diff_L2 m).const_mul _
                  have hSm_L2 : MemLp Sm 2 μ := by
                    have hU_L2 : ∀ k, MemLp (U (k + 1)) 2 μ := fun k => by
                      simp only [U]
                      have hDM_sm : StronglyMeasurable[m0] (ΔM (k + 1)) :=
                        (asm.base.martingale_diff_adapted (k + 1)).mono (ℱ.le (k + 1))
                      have hDM_asm : AEStronglyMeasurable (ΔM (k + 1)) μ := hDM_sm.aestronglyMeasurable
                      have hU_asm : AEStronglyMeasurable (fun ω => γ (k + 1) • ΔM (k + 1) ω) μ :=
                        hDM_asm.const_smul (γ (k + 1))
                      rw [memLp_two_iff_integrable_sq_norm hU_asm]
                      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                      exact (asm.base.martingale_diff_L2 k).const_mul _
                    simp only [hSm_def]
                    exact memLp_finset_sum (Finset.range m) (fun k _ => hU_L2 k)
                  -- Use MemLp.toLp to create L2 elements, then use integrable_inner
                  let f_Lp : Lp E 2 μ := hU_m_L2.toLp (U (m + 1))
                  let g_Lp : Lp E 2 μ := hSm_L2.toLp Sm
                  have h_integ := L2.integrable_inner (𝕜 := ℝ) f_Lp g_Lp
                  -- The coercion of f_Lp and g_Lp equals U and Sm a.e.
                  have hf_ae : f_Lp =ᵐ[μ] U (m + 1) := hU_m_L2.coeFn_toLp
                  have hg_ae : g_Lp =ᵐ[μ] Sm := hSm_L2.coeFn_toLp
                  -- Transfer integrability
                  refine h_integ.congr ?_
                  filter_upwards [hf_ae, hg_ae] with ω hf hg
                  simp only [hf, hg]
                have hcross_zero : ∫ ω, @inner ℝ _ _ (U (m + 1) ω) (Sm ω) ∂μ = 0 := by
                  -- This is the martingale orthogonality condition
                  -- S_m is F_m-measurable, and E[U_{m+1}|F_m] = 0
                  -- The proof uses:
                  -- ∫ ⟪U_{m+1}, S_m⟫ = ∫ ⟪E[U_{m+1}|F_m], S_m⟫ (by tower property for m-measurable g)
                  --                  = ∫ ⟪0, S_m⟫ = 0
                  -- Need: S_m is F_m-measurable (it's a finite sum of terms, each F_k-measurable for k ≤ m)
                  have hSm_meas : StronglyMeasurable[ℱ m] Sm := by
                    simp only [hSm_def, U]
                    refine Finset.stronglyMeasurable_fun_sum _ (fun k hk => ?_)
                    have hk_lt : k < m := Finset.mem_range.mp hk
                    have h_le : ℱ (k + 1) ≤ ℱ m := ℱ.mono (Nat.succ_le_of_lt hk_lt)
                    exact ((asm.base.martingale_diff_adapted (k + 1)).const_smul (γ (k + 1))).mono h_le
                  -- Use the martingale difference property
                  have hU_cond : μ[U (m + 1)|ℱ m] =ᵐ[μ] 0 := _hU_martingale_diff m
                  haveI : SigmaFinite (μ.trim (ℱ.le m)) := sigmaFinite_of_sigmaFiniteFiltration μ ℱ m
                  -- Key: for F_m-measurable g and integrable f,
                  -- ∫ ⟪f, g⟫ = ∫ ⟪E[f|F_m], g⟫
                  -- Use inner_condExpL2_eq_inner_fun: ⟪condExpL2 f, g⟫_L2 = ⟪f, g⟫_L2 when g is m-meas
                  -- Since E[U_{m+1}|F_m] = 0, we get ⟪f, g⟫_L2 = ⟪0, g⟫_L2 = 0
                  -- Convert to L2 inner product
                  have hU_m_L2' : MemLp (U (m + 1)) 2 μ := by
                    simp only [U]
                    have hDM_sm : StronglyMeasurable[m0] (ΔM (m + 1)) :=
                      (asm.base.martingale_diff_adapted (m + 1)).mono (ℱ.le (m + 1))
                    have hDM_asm : AEStronglyMeasurable (ΔM (m + 1)) μ := hDM_sm.aestronglyMeasurable
                    have hU_asm : AEStronglyMeasurable (fun ω => γ (m + 1) • ΔM (m + 1) ω) μ :=
                      hDM_asm.const_smul (γ (m + 1))
                    rw [memLp_two_iff_integrable_sq_norm hU_asm]
                    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                    exact (asm.base.martingale_diff_L2 m).const_mul _
                  have hSm_L2' : MemLp Sm 2 μ := by
                    have hU_L2 : ∀ k, MemLp (U (k + 1)) 2 μ := fun k => by
                      simp only [U]
                      have hDM_sm : StronglyMeasurable[m0] (ΔM (k + 1)) :=
                        (asm.base.martingale_diff_adapted (k + 1)).mono (ℱ.le (k + 1))
                      have hDM_asm : AEStronglyMeasurable (ΔM (k + 1)) μ := hDM_sm.aestronglyMeasurable
                      have hU_asm : AEStronglyMeasurable (fun ω => γ (k + 1) • ΔM (k + 1) ω) μ :=
                        hDM_asm.const_smul (γ (k + 1))
                      rw [memLp_two_iff_integrable_sq_norm hU_asm]
                      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
                      exact (asm.base.martingale_diff_L2 k).const_mul _
                    simp only [hSm_def]
                    exact memLp_finset_sum (Finset.range m) (fun k _ => hU_L2 k)
                  -- Create L2 functions
                  let f_L2 : Lp E 2 μ := hU_m_L2'.toLp (U (m + 1))
                  let g_L2 : Lp E 2 μ := hSm_L2'.toLp Sm
                  -- The L2 inner product equals the pointwise integral
                  have h_inner_L2 : @inner ℝ _ _ f_L2 g_L2 = ∫ ω, @inner ℝ _ _ (U (m + 1) ω) (Sm ω) ∂μ := by
                    -- L2 inner product is defined as ∫ ⟪f, g⟫
                    simp only [L2.inner_def]
                    apply integral_congr_ae
                    filter_upwards [hU_m_L2'.coeFn_toLp, hSm_L2'.coeFn_toLp] with ω hf hg
                    rw [hf, hg]
                  rw [← h_inner_L2]
                  -- Use inner_condExpL2_eq_inner_fun: since Sm is F_m-measurable
                  -- ⟪f_L2, g_L2⟫ = ⟪condExpL2 f_L2, g_L2⟫
                  have h_Sm_meas_ae : AEStronglyMeasurable[ℱ m] Sm μ := hSm_meas.aestronglyMeasurable
                  have h_g_L2_meas : AEStronglyMeasurable[ℱ m] g_L2 μ := by
                    exact h_Sm_meas_ae.congr hSm_L2'.coeFn_toLp.symm
                  have h_eq := @inner_condExpL2_eq_inner_fun Ω E ℝ _ _ _ _ (ℱ m) m0 μ (ℱ.le m) f_L2 g_L2 h_g_L2_meas
                  rw [← h_eq]
                  -- Now condExpL2 f_L2 = 0 because E[U_{m+1}|F_m] = 0
                  -- The condExpL2 agrees with condExp for L2 functions
                  have h_condExpL2_eq : (condExpL2 E ℝ (ℱ.le m) f_L2 : Ω →₂[μ] E) =ᵐ[μ] μ[U (m + 1)|ℱ m] := by
                    -- condExpL2 and condExp agree for L2 functions
                    exact hU_m_L2'.condExpL2_ae_eq_condExp' (ℱ.le m) (hU_m_L2'.integrable one_le_two)
                  -- So condExpL2 f_L2 =ᵐ[μ] 0
                  have h_condExpL2_zero : (condExpL2 E ℝ (ℱ.le m) f_L2 : Ω →₂[μ] E) =ᵐ[μ] 0 := by
                    exact h_condExpL2_eq.trans hU_cond
                  -- Therefore ⟪condExpL2 f_L2, g_L2⟫ = 0
                  calc @inner ℝ _ _ (condExpL2 E ℝ (ℱ.le m) f_L2 : Ω →₂[μ] E) g_L2
                      = ∫ ω, @inner ℝ _ _ ((condExpL2 E ℝ (ℱ.le m) f_L2 : Ω →₂[μ] E) ω) (g_L2 ω) ∂μ := by
                        simp only [L2.inner_def]
                    _ = ∫ ω, @inner ℝ _ _ (0 : E) (g_L2 ω) ∂μ := by
                        apply integral_congr_ae
                        filter_upwards [h_condExpL2_zero] with ω hω
                        simp only [hω, Pi.zero_apply]
                    _ = 0 := by simp [inner_zero_left]
                -- Now compute the integral using h_expand
                -- First, show the goal has the form ∫ ‖U + Sm‖² ≤ ...
                have hgoal_eq : ∀ ω, ‖U (m + 1) ω + Sm ω‖^2 =
                    ‖U (m + 1) ω‖^2 + 2 * @inner ℝ _ _ (U (m + 1) ω) (Sm ω) + ‖Sm ω‖^2 :=
                  h_expand
                conv_lhs => arg 2; ext ω; rw [hgoal_eq]
                calc ∫ ω, (‖U (m + 1) ω‖^2 + 2 * @inner ℝ _ _ (U (m + 1) ω) (Sm ω) +
                      ‖Sm ω‖^2) ∂μ
                    = ∫ ω, ‖U (m + 1) ω‖^2 ∂μ +
                      2 * ∫ ω, @inner ℝ _ _ (U (m + 1) ω) (Sm ω) ∂μ +
                      ∫ ω, ‖Sm ω‖^2 ∂μ := by
                      rw [integral_add, integral_add hU_integrable (hcross_integrable.const_mul 2),
                          integral_mul_left]
                      · exact hU_integrable.add (hcross_integrable.const_mul 2)
                      · exact hS_integrable
                  _ = ∫ ω, ‖U (m + 1) ω‖^2 ∂μ + 2 * 0 + ∫ ω, ‖Sm ω‖^2 ∂μ := by
                      rw [hcross_zero]
                  _ = ∫ ω, ‖U (m + 1) ω‖^2 ∂μ + ∫ ω, ‖Sm ω‖^2 ∂μ := by ring
                  _ ≤ ∫ ω, ‖U (m + 1) ω‖^2 ∂μ + ∑ x ∈ Finset.range m, ∫ ω, ‖U (x + 1) ω‖^2 ∂μ := by
                      simp only [hSm_def]
                      apply add_le_add_left ih
          _ ≤ ∑ k ∈ Finset.range n, (γ (k + 1))^2 * σ^2 := by
              apply Finset.sum_le_sum
              intro k _
              exact hU_L2_bound k
          _ = σ^2 * ∑ k ∈ Finset.range n, (γ (k + 1))^2 := by
              rw [Finset.mul_sum]; congr 1; ext k; ring
          _ ≤ σ^2 * ∑' k, (γ (k + 1))^2 := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
              have h_shift : Summable (fun k => (γ (k + 1))^2) :=
                (summable_nat_add_iff 1).mpr asm.base.gamma_sq_sum_fin
              exact h_shift.sum_le_tsum (Finset.range n) (fun k _ => sq_nonneg _)

    obtain ⟨M, hM_pos, hS_bound⟩ := hS_L2_bound

    -- =========================================================================
    -- STEP 2: Orthonormal basis and coordinate processes
    -- =========================================================================

    -- Fix orthonormal basis of E
    let d := Module.finrank ℝ E
    let b : OrthonormalBasis (Fin d) ℝ E := stdOrthonormalBasis ℝ E

    -- For each coordinate i, define coordinate process S_n^{(i)} := ⟪b i, S_n⟫
    let coord : Fin d → ℕ → Ω → ℝ := fun i n ω => ⟪b i, S n ω⟫

    -- =========================================================================
    -- STEP 3: Each coordinate is an L¹-bounded martingale
    -- =========================================================================

    -- Key: condexp of inner product with constant equals inner product with condexp
    -- This uses condExpL2_const_inner + condExpL2_ae_eq_condExp
    -- Helper: S n is ℱ n-measurable
    have hS_adapted : ∀ n, StronglyMeasurable[ℱ n] (S n) := fun n => by
      apply Finset.stronglyMeasurable_fun_sum
      intro k hk
      have hk_lt : k < n := Finset.mem_range.mp hk
      have h_le : ℱ (k + 1) ≤ ℱ n := ℱ.mono (Nat.succ_le_of_lt hk_lt)
      exact ((asm.base.martingale_diff_adapted (k + 1)).const_smul (γ (k + 1))).mono h_le

    -- Helper: S n is L² (and hence integrable)
    have hS_L2 : ∀ n, MemLp (S n) 2 μ := fun n => by
      apply memLp_finset_sum
      intro k _
      have hDM_sm : StronglyMeasurable[m0] (ΔM (k + 1)) :=
        (asm.base.martingale_diff_adapted (k + 1)).mono (ℱ.le (k + 1))
      have hDM_asm : AEStronglyMeasurable (ΔM (k + 1)) μ := hDM_sm.aestronglyMeasurable
      have hU_asm : AEStronglyMeasurable (fun ω => γ (k + 1) • ΔM (k + 1) ω) μ :=
        hDM_asm.const_smul (γ (k + 1))
      rw [memLp_two_iff_integrable_sq_norm hU_asm]
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact (asm.base.martingale_diff_L2 k).const_mul _

    -- Helper: coord i n is integrable
    have hcoord_integrable : ∀ i n, Integrable (coord i n) μ := fun i n =>
      Integrable.const_inner (b i) ((hS_L2 n).integrable one_le_two)

    -- Helper: coord i n is ℱ n-measurable
    have hcoord_adapted : ∀ i n, StronglyMeasurable[ℱ n] (coord i n) := fun i n =>
      StronglyMeasurable.inner stronglyMeasurable_const (hS_adapted n)

    have h_coord_martingale : ∀ i, Martingale (coord i) ℱ μ := fun i => by
      -- Martingale requires: (1) Adapted, (2) condExp property
      constructor
      -- (1) Adapted: coord i n is ℱ n-measurable
      · exact fun n => hcoord_adapted i n
      -- (2) Martingale property: μ[coord i j | ℱ i] =ᵐ[μ] coord i i for i ≤ j
      · intro i_idx j_idx hij
        -- Proof by induction on j_idx
        induction j_idx with
        | zero =>
          -- i_idx ≤ 0 means i_idx = 0
          interval_cases i_idx
          -- Case i_idx = 0: μ[coord i 0 | ℱ 0] = coord i 0 (it's ℱ 0-measurable)
          rw [condExp_of_stronglyMeasurable (ℱ.le 0) (hcoord_adapted i 0) (hcoord_integrable i 0)]
        | succ m ih =>
          -- Case j = m + 1
          by_cases h_eq : i_idx = m + 1
          · -- i_idx = m + 1: trivial, condExp of ℱ_{m+1}-measurable function is itself
            subst h_eq
            rw [condExp_of_stronglyMeasurable (ℱ.le (m + 1))
              (hcoord_adapted i (m + 1)) (hcoord_integrable i (m + 1))]
          · -- i_idx ≤ m < m + 1: use tower property and martingale diff
            have hi_le_m : i_idx ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hij h_eq)
            haveI : SigmaFinite (μ.trim (ℱ.le i_idx)) := sigmaFinite_of_sigmaFiniteFiltration μ ℱ i_idx
            haveI : SigmaFinite (μ.trim (ℱ.le m)) := sigmaFinite_of_sigmaFiniteFiltration μ ℱ m

            -- Key: coord i (m+1) = coord i m + ⟪b i, U (m+1)⟫
            have h_split : coord i (m + 1) = fun ω => coord i m ω + ⟪b i, U (m + 1) ω⟫ := by
              funext ω
              -- coord i n ω = ⟪b i, S n ω⟫ and S n ω = ∑ k ∈ range n, U (k+1) ω
              -- Use explicit change to make the let bindings definitionally equal
              change ⟪b i, S (m + 1) ω⟫ = ⟪b i, S m ω⟫ + ⟪b i, U (m + 1) ω⟫
              -- S (m+1) ω = S m ω + U (m+1) ω
              have hS_step : S (m + 1) ω = S m ω + U (m + 1) ω := by
                show ∑ k ∈ Finset.range (m + 1), U (k + 1) ω =
                     ∑ k ∈ Finset.range m, U (k + 1) ω + U (m + 1) ω
                rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self, add_comm]
              rw [hS_step, inner_add_right]

            -- E[U (m+1) | ℱ m] = 0
            have h_U_condExp_zero : μ[U (m + 1)|ℱ m] =ᵐ[μ] 0 := by
              calc μ[fun ω => γ (m + 1) • ΔM (m + 1) ω|ℱ m]
                  =ᵐ[μ] γ (m + 1) • μ[ΔM (m + 1)|ℱ m] :=
                    condExp_smul (μ := μ) (γ (m + 1)) (ΔM (m + 1)) (ℱ m)
                _ =ᵐ[μ] γ (m + 1) • (0 : Ω → E) := by
                    filter_upwards [asm.base.martingale_diff_condexp m] with ω hω
                    simp only [Pi.smul_apply, hω]
                _ =ᵐ[μ] 0 := by
                    filter_upwards with ω
                    simp only [Pi.smul_apply, Pi.zero_apply, smul_zero]

            -- U (m+1) is L² hence integrable
            have hU_m_L2 : MemLp (U (m + 1)) 2 μ := by
              have hDM_sm : StronglyMeasurable[m0] (ΔM (m + 1)) :=
                (asm.base.martingale_diff_adapted (m + 1)).mono (ℱ.le (m + 1))
              have hDM_asm : AEStronglyMeasurable (ΔM (m + 1)) μ := hDM_sm.aestronglyMeasurable
              have hU_asm : AEStronglyMeasurable (fun ω => γ (m + 1) • ΔM (m + 1) ω) μ :=
                hDM_asm.const_smul (γ (m + 1))
              rw [memLp_two_iff_integrable_sq_norm hU_asm]
              simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
              exact (asm.base.martingale_diff_L2 m).const_mul _

            -- E[⟪b i, U (m+1)⟫ | ℱ m] = 0
            -- This follows from linearity of condExp and inner product
            have h_inner_condExp_zero : μ[fun ω => ⟪b i, U (m + 1) ω⟫|ℱ m] =ᵐ[μ] 0 := by
              -- The inner product with a constant is a bounded linear functional
              -- E[⟪c, f⟫ | F] = ⟪c, E[f|F]⟫ for integrable f in finite dimensions
              -- Use condExpL2_const_inner combined with condExpL2_ae_eq_condExp
              -- First, show the result using condExpL2 tools
              let f_Lp : Lp E 2 μ := hU_m_L2.toLp (U (m + 1))
              -- condExpL2 of ⟪c, f⟫ =ᵐ ⟪c, condExpL2 f⟫
              have h_condExpL2_inner := condExpL2_const_inner (𝕜 := ℝ) (ℱ.le m) f_Lp (b i)
              -- condExpL2 f =ᵐ condExp f
              have h_condExpL2_eq := hU_m_L2.condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le m)
              -- condExp (⟪c, f⟫) =ᵐ condExpL2 (⟪c, f⟫)
              have h_inner_L2 : MemLp (fun ω => ⟪b i, U (m + 1) ω⟫) 2 μ := hU_m_L2.const_inner (b i)
              have h_inner_condExpL2_eq := h_inner_L2.condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le m)
              -- Key: the two Lp elements are equal because their underlying functions are ae-equal
              have h_toLp_eq : h_inner_L2.toLp (fun ω => ⟪b i, U (m + 1) ω⟫) =
                  ((Lp.memLp f_Lp).const_inner (b i)).toLp (fun a => ⟪b i, f_Lp a⟫) := by
                rw [MemLp.toLp_eq_toLp_iff]
                have h_coeFn := hU_m_L2.coeFn_toLp
                filter_upwards [h_coeFn] with ω hω
                rw [hω]
              calc μ[fun ω => ⟪b i, U (m + 1) ω⟫|ℱ m]
                  =ᵐ[μ] condExpL2 ℝ ℝ (ℱ.le m) (h_inner_L2.toLp _) := h_inner_condExpL2_eq.symm
                _ =ᵐ[μ] condExpL2 ℝ ℝ (ℱ.le m) (((Lp.memLp f_Lp).const_inner (b i)).toLp _) := by
                    rw [h_toLp_eq]
                _ =ᵐ[μ] fun a => ⟪b i, (condExpL2 E ℝ (ℱ.le m) f_Lp : Ω → E) a⟫ := h_condExpL2_inner
                _ =ᵐ[μ] fun a => ⟪b i, (μ[U (m + 1)|ℱ m]) a⟫ := by
                    filter_upwards [h_condExpL2_eq] with ω hω
                    rw [hω]
                _ =ᵐ[μ] fun a => ⟪b i, (0 : E)⟫ := by
                    filter_upwards [h_U_condExp_zero] with ω hω
                    rw [hω]; rfl
                _ =ᵐ[μ] 0 := by filter_upwards with _; simp only [inner_zero_right, Pi.zero_apply]

            -- μ[coord i (m+1) | ℱ m] = coord i m
            have h_condExp_m : μ[coord i (m + 1)|ℱ m] =ᵐ[μ] coord i m := by
              rw [h_split]
              have h_add := condExp_add (hcoord_integrable i m)
                (Integrable.const_inner (b i) (hU_m_L2.integrable one_le_two)) (ℱ m)
              calc μ[(fun ω => coord i m ω + ⟪b i, U (m + 1) ω⟫)|ℱ m]
                  =ᵐ[μ] μ[coord i m|ℱ m] + μ[fun ω => ⟪b i, U (m + 1) ω⟫|ℱ m] := h_add
                _ =ᵐ[μ] coord i m + μ[fun ω => ⟪b i, U (m + 1) ω⟫|ℱ m] := by
                    have hcm : μ[coord i m|ℱ m] = coord i m :=
                      condExp_of_stronglyMeasurable (ℱ.le m) (hcoord_adapted i m) (hcoord_integrable i m)
                    rw [hcm]
                _ =ᵐ[μ] coord i m + (0 : Ω → ℝ) := by
                    filter_upwards [h_inner_condExp_zero] with ω hω
                    simp only [Pi.add_apply, hω]
                _ =ᵐ[μ] coord i m := by
                    filter_upwards with ω
                    simp only [Pi.add_apply, Pi.zero_apply, add_zero]

            -- Tower property: μ[coord i (m+1) | ℱ i_idx] = μ[μ[coord i (m+1) | ℱ m] | ℱ i_idx]
            calc μ[coord i (m + 1)|ℱ i_idx]
                =ᵐ[μ] μ[μ[coord i (m + 1)|ℱ m]|ℱ i_idx] := by
                  symm
                  exact condExp_condExp_of_le (ℱ.mono hi_le_m) (ℱ.le m)
              _ =ᵐ[μ] μ[coord i m|ℱ i_idx] := condExp_congr_ae h_condExp_m
              _ =ᵐ[μ] coord i i_idx := ih hi_le_m

    -- L¹ bound for coordinates: E[|coord i n|] ≤ √M
    have h_coord_L1_bound : ∀ i n, ∫ ω, |coord i n ω| ∂μ ≤ Real.sqrt M := fun i n => by
      -- |⟪b i, S_n⟫| ≤ ‖b i‖ ‖S_n‖ = ‖S_n‖ (since ‖b i‖ = 1)
      -- E[|coord|] ≤ E[‖S_n‖] ≤ √(E[‖S_n‖²]) ≤ √M (Jensen)
      -- Step 1: |⟪b i, S n ω⟫| ≤ ‖b i‖ * ‖S n ω‖ = ‖S n ω‖ (since ‖b i‖ = 1)
      have h_coord_le_norm : ∀ ω, |coord i n ω| ≤ ‖S n ω‖ := fun ω => by
        have hCS := abs_real_inner_le_norm (b i) (S n ω)
        have h_b_norm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
        simp only [h_b_norm, one_mul] at hCS
        exact hCS
      -- Step 2: ∫ |coord| ≤ ∫ ‖S n‖
      have h_int_le : ∫ ω, |coord i n ω| ∂μ ≤ ∫ ω, ‖S n ω‖ ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all μ (fun ω => abs_nonneg _)
        · exact (hS_L2 n).integrable one_le_two |>.norm
        · exact ae_of_all μ h_coord_le_norm
      -- Step 3: ∫ ‖S n‖ ≤ √(∫ ‖S n‖²) (Jensen for probability measure)
      -- Use eLpNorm_le_eLpNorm_of_exponent_le: for probability measures, eLpNorm p ≤ eLpNorm q when p ≤ q
      have h_S_asm : AEStronglyMeasurable (S n) μ := (hS_L2 n).aestronglyMeasurable
      have h_L1_le_L2 : eLpNorm (S n) 1 μ ≤ eLpNorm (S n) 2 μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_S_asm
      -- Convert eLpNorm to integrals
      have h_eLpNorm_1 : eLpNorm (S n) 1 μ = ENNReal.ofReal (∫ ω, ‖S n ω‖ ∂μ) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have h_eq : ∫⁻ x, ‖S n x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal ‖S n x‖ ∂μ := by
          apply lintegral_congr
          intro x
          exact (ofReal_norm_eq_enorm (S n x)).symm
        rw [h_eq, ← ofReal_integral_eq_lintegral_ofReal
            ((hS_L2 n).integrable one_le_two).norm (ae_of_all μ (fun ω => norm_nonneg _))]
      have h_eLpNorm_2 : eLpNorm (S n) 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, ‖S n ω‖^2 ∂μ)) := by
        rw [(hS_L2 n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
        simp only [ENNReal.toReal_ofNat]
        congr 1
        have h_nonneg : 0 ≤ ∫ ω, ‖S n ω‖^2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
        have h_eq_int : ∫ ω, ‖S n ω‖^(2:ℝ) ∂μ = ∫ ω, ‖S n ω‖^2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          exact Real.rpow_natCast _ _
        rw [h_eq_int, Real.sqrt_eq_rpow, show (2:ℝ)⁻¹ = (1/2:ℝ) by norm_num]
      -- Combine: ∫ ‖S n‖ ≤ √(∫ ‖S n‖²)
      have h_int_norm_le_sqrt : ∫ ω, ‖S n ω‖ ∂μ ≤ Real.sqrt (∫ ω, ‖S n ω‖^2 ∂μ) := by
        have h_le := h_L1_le_L2
        rw [h_eLpNorm_1, h_eLpNorm_2] at h_le
        have h_nonneg1 : 0 ≤ ∫ ω, ‖S n ω‖ ∂μ := integral_nonneg (fun ω => norm_nonneg _)
        have h_nonneg2 : 0 ≤ Real.sqrt (∫ ω, ‖S n ω‖^2 ∂μ) := Real.sqrt_nonneg _
        exact ENNReal.ofReal_le_ofReal_iff h_nonneg2 |>.mp h_le
      -- Step 4: √(∫ ‖S n‖²) ≤ √M
      have h_sqrt_le : Real.sqrt (∫ ω, ‖S n ω‖^2 ∂μ) ≤ Real.sqrt M := by
        apply Real.sqrt_le_sqrt
        exact hS_bound n
      -- Combine all
      calc ∫ ω, |coord i n ω| ∂μ
          ≤ ∫ ω, ‖S n ω‖ ∂μ := h_int_le
        _ ≤ Real.sqrt (∫ ω, ‖S n ω‖^2 ∂μ) := h_int_norm_le_sqrt
        _ ≤ Real.sqrt M := h_sqrt_le

    -- =========================================================================
    -- STEP 4: Apply Doob's martingale convergence to each coordinate
    -- =========================================================================

    -- Each coordinate converges a.s.
    have h_coord_conv : ∀ i, ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun n => coord i n ω) atTop (nhds L) := by
      intro i
      -- The squared process (coord i)² is a submartingale
      -- It's L¹-bounded since E[(coord i n)²] ≤ E[‖S_n‖²] ≤ M
      -- Apply Submartingale.exists_ae_tendsto_of_bdd
      have h_subm : Submartingale (fun n ω => (coord i n ω)^2) ℱ μ := by
        -- Use submartingale_nat: need to show (coord i n)² ≤ᵐ[μ] μ[(coord i (n+1))² | ℱ n]
        have h_mart := h_coord_martingale i
        -- The squared process is adapted (coord i n is ℱ n-measurable, so is its square)
        have hadp_sq : Adapted ℱ (fun n ω => (coord i n ω)^2) := fun n =>
          (hcoord_adapted i n).pow 2
        -- Each (coord i n)² is integrable (follows from L² bounds)
        -- coord i n = ⟪b i, S n⟫ and S n is L², so coord i n is L² by MemLp.const_inner
        have hcoord_L2 : ∀ n, MemLp (coord i n) 2 μ := fun n => (hS_L2 n).const_inner (b i)
        have hint_sq : ∀ n, Integrable (fun ω => (coord i n ω)^2) μ := fun n =>
          (hcoord_L2 n).integrable_sq
        -- Apply submartingale_nat
        apply submartingale_nat hadp_sq hint_sq
        intro n
        -- Need: (coord i n)² ≤ᵐ[μ] μ[(coord i (n+1))² | ℱ n]
        -- From martingale: μ[coord i (n+1) | ℱ n] =ᵐ[μ] coord i n
        have h_mart_eq : μ[coord i (n + 1)|ℱ n] =ᵐ[μ] coord i n := h_mart.condExp_ae_eq (Nat.le_succ n)
        -- From conditional Jensen (variance is non-negative):
        -- μ[(coord i (n+1))² | ℱ n] ≥ μ[coord i (n+1) | ℱ n]² = (coord i n)²
        have h_L2_np1 : MemLp (coord i (n + 1)) 2 μ := hcoord_L2 (n + 1)
        haveI : SigmaFinite (μ.trim (ℱ.le n)) := sigmaFinite_of_sigmaFiniteFiltration μ ℱ n
        -- condVar is non-negative (it's conditional expectation of a square)
        have h_condVar_nonneg : 0 ≤ᵐ[μ] ProbabilityTheory.condVar (ℱ n) (coord i (n + 1)) μ := by
          unfold ProbabilityTheory.condVar
          apply condExp_nonneg
          filter_upwards with ω
          exact sq_nonneg _
        -- condVar =ᵐ μ[X² | m] - μ[X | m]²
        have h_condVar_eq := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le n) h_L2_np1
        -- Combine: μ[X | m]² ≤ μ[X² | m]
        have h_jensen : μ[coord i (n + 1)|ℱ n] ^ 2 ≤ᵐ[μ] μ[(coord i (n + 1)) ^ 2|ℱ n] := by
          filter_upwards [h_condVar_nonneg, h_condVar_eq] with ω h_nonneg h_eq
          simp only [Pi.sub_apply, Pi.pow_apply] at h_eq
          simp only [Pi.zero_apply] at h_nonneg
          simp only [Pi.pow_apply]
          linarith
        -- Use martingale property: μ[coord i (n+1) | ℱ n] =ᵐ coord i n
        filter_upwards [h_jensen, h_mart_eq] with ω hj hm
        simp only [sq] at hj ⊢
        rw [← hm]
        exact hj
      have h_L1_bdd : ∀ n, eLpNorm (fun ω => (coord i n ω)^2) 1 μ ≤ ENNReal.ofReal M := by
        intro n
        -- E[(coord i n)²] ≤ E[‖S_n‖²] ≤ M
        -- Step 1: (coord i n ω)² ≤ ‖S n ω‖² pointwise
        have h_sq_le : ∀ ω, (coord i n ω)^2 ≤ ‖S n ω‖^2 := fun ω => by
          have hCS := abs_real_inner_le_norm (b i) (S n ω)
          have h_b_norm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
          simp only [h_b_norm, one_mul] at hCS
          exact sq_le_sq' (neg_le_of_abs_le hCS) (le_of_abs_le hCS)
        -- Step 2: eLpNorm of (coord i n)² at 1 = ∫⁻ |(coord i n)²| = ∫⁻ (coord i n)² (nonneg)
        rw [eLpNorm_one_eq_lintegral_enorm]
        -- Step 3: Convert to ofReal of integral
        have h_sq_nonneg : ∀ ω, 0 ≤ (coord i n ω)^2 := fun ω => sq_nonneg _
        -- coord i n = ⟪b i, S n⟫ is L² (since S n is L²), so (coord i n)² is integrable
        have hcoord_L2' : MemLp (coord i n) 2 μ := (hS_L2 n).const_inner (b i)
        have h_int_sq : Integrable (fun ω => (coord i n ω)^2) μ := hcoord_L2'.integrable_sq
        have h_eq_ofReal : ∫⁻ ω, ‖(coord i n ω)^2‖ₑ ∂μ = ENNReal.ofReal (∫ ω, (coord i n ω)^2 ∂μ) := by
          have h_eq : ∫⁻ ω, ‖(coord i n ω)^2‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal ((coord i n ω)^2) ∂μ := by
            apply lintegral_congr
            intro ω
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (h_sq_nonneg ω)]
          rw [h_eq, ← ofReal_integral_eq_lintegral_ofReal h_int_sq (ae_of_all μ h_sq_nonneg)]
        rw [h_eq_ofReal]
        -- Step 4: ∫ (coord i n)² ≤ ∫ ‖S n‖² ≤ M
        -- S n is L², so ‖S n‖² is integrable
        have h_S_norm_sq_int : Integrable (fun ω => ‖S n ω‖^2) μ :=
          (hS_L2 n).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
        apply ENNReal.ofReal_le_ofReal
        calc ∫ ω, (coord i n ω)^2 ∂μ
            ≤ ∫ ω, ‖S n ω‖^2 ∂μ := by
              apply integral_mono_of_nonneg
              · exact ae_of_all μ h_sq_nonneg
              · exact h_S_norm_sq_int
              · exact ae_of_all μ h_sq_le
          _ ≤ M := hS_bound n
      -- Get convergence of squared process, then of original
      -- Simpler approach: coord i is a martingale, hence submartingale
      -- Apply Submartingale.exists_ae_tendsto_of_bdd directly to coord i
      have h_subm_coord : Submartingale (coord i) ℱ μ := (h_coord_martingale i).submartingale
      -- Convert L¹ bound: ∫ |coord i n| ≤ √M to eLpNorm bound
      have h_eLpNorm_bdd : ∀ n, eLpNorm (coord i n) 1 μ ≤ ENNReal.ofReal (Real.sqrt M) := fun n => by
        rw [eLpNorm_one_eq_lintegral_enorm]
        -- ∫⁻ ‖coord i n‖ₑ = ∫⁻ |coord i n| = ofReal (∫ |coord i n|)
        have h_coord_int : Integrable (coord i n) μ := by
          have hcoord_L2 : MemLp (coord i n) 2 μ := (hS_L2 n).const_inner (b i)
          exact hcoord_L2.integrable one_le_two
        have h_eq : ∫⁻ ω, ‖coord i n ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, |coord i n ω| ∂μ) := by
          have h_eq' : ∫⁻ ω, ‖coord i n ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal |coord i n ω| ∂μ := by
            apply lintegral_congr
            intro ω
            rw [Real.enorm_eq_ofReal_abs]
          rw [h_eq', ← ofReal_integral_eq_lintegral_ofReal h_coord_int.abs (ae_of_all μ (fun _ => abs_nonneg _))]
        rw [h_eq]
        exact ENNReal.ofReal_le_ofReal (h_coord_L1_bound i n)
      exact h_subm_coord.exists_ae_tendsto_of_bdd h_eLpNorm_bdd

    -- =========================================================================
    -- STEP 5: Combine coordinates - finite intersection gives S_n → S_∞
    -- =========================================================================

    -- All coordinates converge a.s. (finite intersection of a.e. events)
    have h_all_coord_conv : ∀ᵐ ω ∂μ, ∀ i, ∃ L, Tendsto (fun n => coord i n ω) atTop (nhds L) := by
      -- Finite intersection over Fin d
      rw [ae_all_iff]
      exact h_coord_conv

    -- S_n converges iff all coordinates converge (finite-dimensional)
    have h_S_conv : ∀ᵐ ω ∂μ, ∃ S_lim, Tendsto (fun n => S n ω) atTop (nhds S_lim) := by
      filter_upwards [h_all_coord_conv] with ω h_coord
      -- In finite dimensions, coordinatewise convergence ⟹ convergence
      -- S_n = ∑_i ⟪b i, S_n⟫ • b i, and each coordinate converges
      -- For each coordinate i, extract the limit L_i
      choose L hL using h_coord
      -- Set S_lim = ∑ i, L_i • b i
      use ∑ i, L i • b i
      -- S n ω = ∑ i, ⟪b i, S n ω⟫ • b i by OrthonormalBasis.sum_repr'
      have h_S_eq : ∀ n, S n ω = ∑ i, coord i n ω • b i := fun n => (b.sum_repr' (S n ω)).symm
      simp_rw [h_S_eq]
      -- Each summand converges: coord i n ω • b i → L i • b i
      -- Use tendsto_finset_sum for finite sums
      apply tendsto_finset_sum
      intro i _
      exact (hL i).smul_const (b i)

    -- =========================================================================
    -- STEP 6: Convergence ⇒ Cauchy partial sums
    -- =========================================================================

    filter_upwards [h_S_conv] with ω ⟨S_lim, hSLim⟩
    have : CauchySeq (fun n => S n ω) := (Filter.Tendsto.cauchySeq hSLim)
    simpa [S] using this

  -- =====================================================
  -- STEP 2: V(X_n) Converges (from base theorem)
  -- =====================================================
  have h_V_conv : ∀ᵐ ω ∂μ, ∃ V_lim, Tendsto (fun n => V (X n ω)) atTop (nhds V_lim) := by
    filter_upwards [h_V_conv_raw] with ω hω
    exact ⟨V_inf ω, hω⟩

  have h_X_bdd : ∀ᵐ ω ∂μ, Bornology.IsBounded (Set.range fun n => X n ω) := by
    -- V coercive + V(X_n) converges → X_n is bounded
    -- Standard argument: V(X_n) bounded ⟹ X_n in sublevel set ⟹ X_n bounded (coercivity)
    filter_upwards [h_V_conv] with ω ⟨V_lim, hV_lim⟩
    have h_V_bdd : BddAbove (Set.range fun n => V (X n ω)) :=
      hV_lim.isBoundedUnder_le.bddAbove_range
    obtain ⟨M, hM⟩ := h_V_bdd
    rw [mem_upperBounds] at hM
    haveI : ProperSpace E := FiniteDimensional.proper ℝ E
    -- X_n lies in sublevel set {x | V x ≤ M}
    have h_range_sub : Set.range (fun n => X n ω) ⊆ {x : E | V x ≤ M} := fun x ⟨n, hn⟩ =>
      hn ▸ hM (V (X n ω)) (Set.mem_range_self n)
    -- Sublevel set is bounded (coercivity)
    -- MATH: V coercive means V → ∞ as ‖x‖ → ∞
    -- So sublevel set {V ≤ M} is contained in some ball, hence bounded
    have h_sublevel_bdd : Bornology.IsBounded {x : E | V x ≤ M} := by
      -- From coercivity: Tendsto V (cocompact E) atTop
      -- This means for any level, the superlevel set is in cocompact
      -- So there exists a compact set containing the sublevel set
      have h_mem : V ⁻¹' (Set.Ici (M + 1)) ∈ Filter.cocompact E :=
        asm.base.V_coercive (Filter.mem_atTop (M + 1))
      rw [Filter.mem_cocompact] at h_mem
      obtain ⟨K, hK_compact, hK_sub⟩ := h_mem
      -- {V ≤ M} ⊆ {V < M+1} ⊆ K
      have h_sub : {x : E | V x ≤ M} ⊆ K := fun x hx => by
        by_contra h_not_in_K
        have h_in_compl : x ∈ Kᶜ := h_not_in_K
        have h_in_superlevel : x ∈ V ⁻¹' (Set.Ici (M + 1)) := hK_sub h_in_compl
        simp only [Set.mem_preimage, Set.mem_Ici] at h_in_superlevel
        simp only [Set.mem_setOf_eq] at hx
        linarith
      exact hK_compact.isBounded.subset h_sub
    exact h_sublevel_bdd.subset h_range_sub

  -- =====================================================
  -- STEP 3: Vanishing Increments (from base theorem)
  -- =====================================================
  -- The base theorem already proves this!
  have h_incr : ∀ᵐ ω ∂μ, Tendsto (fun n => X (n + 1) ω - X n ω) atTop (nhds 0) := h_incr_base

  -- =====================================================
  -- STEP 5: Apply Excursion Argument
  -- =====================================================
  -- Every accumulation point y has ⟨∇V(y), h(y)⟩ = 0

  -- Combine all a.s. properties
  filter_upwards [h_noise_cauchy, h_drift_sum, h_X_bdd, h_incr] with ω h_noise h_drift h_bdd h_vanish

  -- Define U shifted for accumulation_point_drift_zero
  let U' : ℕ → E := fun n => U (n + 1) ω
  have h_noise' : CauchySeq (fun n => ∑ k ∈ Finset.range n, U' k) := by
    simpa [U'] using h_noise

  -- Verify recursion matches the form needed
  have h_rec : ∀ n, X (n + 1) ω - X n ω = -(γ (n + 1)) • h (X n ω) + U' n := by
    intro n
    -- From recursion: X (n+1) = X n - γ (n+1) • h(X n) + γ (n+1) • ΔM (n+1)
    -- So X (n+1) - X n = -γ (n+1) • h(X n) + γ (n+1) • ΔM (n+1) = -γ • h + U'
    have h1 : X (n + 1) ω = X n ω - (γ (n + 1)) • h (X n ω) + (γ (n + 1)) • ΔM (n + 1) ω :=
      asm.recursion n ω
    simp only [h1, U', U, neg_smul]
    -- Goal: X n ω - γ (n+1) • h (X n ω) + γ (n+1) • ΔM (n+1) ω - X n ω =
    --       -γ (n+1) • h (X n ω) + γ (n+1) • ΔM (n+1) ω
    -- Rewrite using vector subtraction: (a - b + c) - a = -b + c
    abel

  -- Apply accumulation_point_drift_zero to show all accum. points have zero drift
  -- Uses the excursion argument: if drift(y) > 0, trajectory visits ball infinitely often,
  -- contradiction with drift summability
  have h_accum_zero : ∀ (y : E) (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (fun (n : ℕ) => X (φ n) ω) atTop (nhds y) →
      y ∈ {x : E | @inner ℝ _ _ (gradV x) (h x) = 0} := by
    intro y φ hφ hy_lim
    simp only [Set.mem_setOf_eq]
    exact accumulation_point_drift_zero
      asm.base.gamma_pos asm.base.gamma_sum_inf asm.base.h_continuous gradV_cont asm.base.drift_nonneg
      h_drift h_rec h_noise' hφ hy_lim

  -- =====================================================
  -- STEP 6: Unique Accumulation Point → Convergence
  -- =====================================================
  -- By drift_zero_unique, all accumulation points equal x_star
  have h_unique_accum : ∀ y, (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => X (φ n) ω) atTop (nhds y))
      → y = x_star := by
    intro y ⟨φ, hφ, hy_lim⟩
    have h_drift_zero := h_accum_zero y φ hφ hy_lim
    rw [asm.drift_zero_unique] at h_drift_zero
    exact h_drift_zero

  -- Bounded sequence with unique accumulation point converges
  exact tendsto_of_bounded_unique_accumulation h_bdd h_vanish h_unique_accum

end SGDUniqueMin
