/-
# Integer-rounded value iteration
## Goals
- Define an integer-rounded Bellman operator for finite MDPs that computes the 
  rational Bellman operator and then rounds each state’s value to the nearest integer.
- Prove an approximate convergence theorem analogous to the standard value iteration result:
  - Convergence of the iterates (after casting to reals) to the true fixed point of the real Bellman operator up to a radius induced by rounding.
  - An explicit geometric error bound: for discount `0 ≤ γ < 1`, the iterate error is bounded by `(γ^n) * initial_error + (1/2) / (1-γ)` in sup-norm (after casting to `ℝ`).
  - Eventual inclusion in any ball of radius `ε > (1/2)/(1-γ)`.

## Process
- Mainly done by GPT-5 on Codex CLI, with compiler feedback (`lake build`)
- Two lemmas were solved by Sonnet 4; one on Claude Desktop + LeanTool, another on Cursor + LeanTool

-/

import Mathlib
import ArtificialAlgorithms.AI.ValueIterationComplete

set_option maxHeartbeats 0

open Metric Filter Topology

namespace ApproxValueIterationInt

variable {S A : Type} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq A]

open scoped BigOperators

-- Cast helpers
def castZtoQ (v : S → ℤ) : S → ℚ := fun s => (v s : ℚ)
noncomputable def castQtoR (v : S → ℚ) : S → ℝ := fun s => (v s : ℝ)
noncomputable def castZtoR (v : S → ℤ) : S → ℝ := fun s => ((v s : ℚ) : ℝ)

-- Nearest-integer rounding on ℚ (we adopt Mathlib's `round`, halves toward +∞)
def roundNearestRat (q : ℚ) : ℤ := round q

-- Integer-rounded Bellman operator
def bellmanOperatorInt (mdp : MDP S A) (γ : ℚ) (v : S → ℤ) : S → ℤ :=
  fun s =>
    let qVal : A → ℚ := fun a =>
      mdp.R s a + γ * Finset.univ.sum (fun s' => mdp.P s a s' * (v s' : ℚ))
    roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal)

-- Rounding error bound (placeholder)
lemma roundNearestRat_error_le_half (q : ℚ) :
    |(roundNearestRat q : ℚ) - q| ≤ (1 : ℚ) / 2 := by
  -- This is Mathlib's standard bound for `round`
  simpa [roundNearestRat, abs_sub_comm] using (abs_sub_round (x := q))

-- Supremum over finite set commutes with casting (auxiliary lemma)
lemma sup_cast_commute (f : A → ℚ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => (f a : ℝ))
      = ((Finset.univ.sup' Finset.univ_nonempty f : ℚ) : ℝ) := by
  classical
  -- Notation
  set s : Finset A := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have h_le : s.sup' hs (fun a => (f a : ℝ)) ≤ ((s.sup' hs f : ℚ) : ℝ) := by
    -- Use sup'_le_iff: show (f a : ℝ) ≤ ((sup' f) : ℝ) for all a ∈ s
    refine (Finset.sup'_le_iff (s := s) (H := hs) (f := fun a => (f a : ℝ))).2 ?_
    intro a ha
    -- f a ≤ sup'⟨a,ha⟩ f ≤ sup' hs f, then cast to ℝ
    have h1 : f a ≤ s.sup' ⟨a, by simpa [s] using ha⟩ f :=
      Finset.le_sup' (s := s) (f := f) (by simpa [s] using ha)
    have h2 : s.sup' ⟨a, by simpa [s] using ha⟩ f ≤ s.sup' hs f := by
      -- By sup'_le_iff with upper bound s.sup' hs f
      refine (Finset.sup'_le_iff (s := s) (H := ⟨a, by simpa [s] using ha⟩) (f := f)).2 ?_
      intro b hb
      exact Finset.le_sup' (s := s) (f := f) hb
    have : f a ≤ s.sup' hs f := le_trans h1 h2
    exact (Rat.cast_le (K := ℝ)).mpr this
  have h_ge : ((s.sup' hs f : ℚ) : ℝ) ≤ s.sup' hs (fun a => (f a : ℝ)) := by
    -- Pick argmax a₀ with sup' hs f = f a₀
    obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_mem_eq_sup' (s := s) (H := hs) (f := f)
    -- Show (f a₀ : ℝ) ≤ sup' hs (cast ∘ f), then rewrite LHS by hmax
    have h1 : (f a₀ : ℝ) ≤ s.sup' ⟨a₀, by simpa [s] using ha₀⟩ (fun a => (f a : ℝ)) :=
      Finset.le_sup' (s := s) (f := fun a => (f a : ℝ)) (by simpa [s] using ha₀)
    have h2 : s.sup' ⟨a₀, by simpa [s] using ha₀⟩ (fun a => (f a : ℝ))
                ≤ s.sup' hs (fun a => (f a : ℝ)) := by
      -- As before, using sup'_le_iff for the casted function
      refine (Finset.sup'_le_iff (s := s) (H := ⟨a₀, by simpa [s] using ha₀⟩)
        (f := fun a => (f a : ℝ))).2 ?_
      intro b hb
      exact Finset.le_sup' (s := s) (f := fun a => (f a : ℝ)) hb
    have : (f a₀ : ℝ) ≤ s.sup' hs (fun a => (f a : ℝ)) := le_trans h1 h2
    simpa [hmax] using this
  exact le_antisymm h_le h_ge

-- One-step error in sup-norm after casting (to be proved)
lemma T_int_one_step_error_le (mdp : MDP S A) (γ : ℚ) (v : S → ℤ) :
    dist (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v))
         (bellmanOperatorReal (S:=S) (A:=A) mdp (γ : ℝ) (castZtoR v))
      ≤ (1 : ℝ) / 2 := by
  -- Reduce to pointwise bound using Pi metric and the sup-cast lemma
  refine (dist_pi_le_iff (by norm_num)).2 ?hpoint
  intro s
  simp [bellmanOperatorInt, bellmanOperatorReal]
  -- Define action-value functions
  set qVal : A → ℚ := fun a => mdp.R s a + γ * Finset.univ.sum (fun s' => mdp.P s a s' * (v s' : ℚ))
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun a => (qVal a : ℝ))
              = ((Finset.univ.sup' Finset.univ_nonempty qVal : ℚ) : ℝ) :=
    sup_cast_commute qVal
  -- It suffices to bound the absolute value after rewriting via hsup
  have hleft : castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v) s
        = ((roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal) : ℚ) : ℝ) := by
    simp [bellmanOperatorInt, qVal, castZtoR]
  have hright : Finset.univ.sup' Finset.univ_nonempty
        (fun a => (mdp.R s a : ℝ) + (γ : ℝ) *
          Finset.univ.sum (fun s' => (mdp.P s a s' : ℝ) * castZtoR v s'))
        = ((Finset.univ.sup' Finset.univ_nonempty qVal : ℚ) : ℝ) := by
    -- This is exactly hsup after unfolding the cast
    simpa [qVal, castZtoR, Rat.cast_mul, Rat.cast_add, Rat.cast_sum]
      using hsup
  suffices
    |((roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal) : ℚ) : ℝ)
        - ((Finset.univ.sup' Finset.univ_nonempty qVal : ℚ) : ℝ)| ≤ (1 : ℝ) / 2 by
    simpa [Real.dist_eq, hleft, hright]
  -- Transfer the rounding bound from ℚ to ℝ by casting
  have hq : |(roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal) : ℚ)
                - (Finset.univ.sup' Finset.univ_nonempty qVal)| ≤ (1 : ℚ) / 2 :=
    roundNearestRat_error_le_half _
  -- Cast inequality to ℝ
  have : |((roundNearestRat (Finset.univ.sup' Finset.univ_nonempty qVal) : ℚ) : ℝ)
             - ((Finset.univ.sup' Finset.univ_nonempty qVal : ℚ) : ℝ)|
          ≤ ((1 : ℚ) / 2 : ℝ) := by
    simpa [Rat.cast_sub, Rat.cast_abs, Rat.cast_div, Rat.cast_one]
      using (Rat.cast_le (K := ℝ)).mpr hq
  exact (le_trans this (by norm_num))

-- Affine contraction: γ-contraction plus additive 1 (to be proved)
lemma T_int_affine_contraction (mdp : MDP S A) (γ : ℚ) (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1)
    (v₁ v₂ : S → ℤ) :
    dist (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v₁))
         (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v₂))
      ≤ (γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) := by
  -- Triangle inequality via the real Bellman operator, plus two rounding errors
  have hγ_real_nonneg : (0 : ℝ) ≤ (γ : ℝ) := Rat.cast_nonneg.mpr hγ_nonneg
  have hγ_real_lt : (γ : ℝ) < 1 := by
    rw [← Rat.cast_one]
    exact Rat.cast_lt.mpr hγ_lt
  -- Shorthands
  set a := castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v₁)
  set c := castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v₂)
  set b := bellmanOperatorReal (S:=S) (A:=A) mdp (γ : ℝ) (castZtoR v₁)
  set d := bellmanOperatorReal (S:=S) (A:=A) mdp (γ : ℝ) (castZtoR v₂)
  have h1 : dist a b ≤ (1 : ℝ) / 2 := by
    -- one-step rounding error at v₁
    simpa [a, b] using
      (T_int_one_step_error_le (S:=S) (A:=A) (mdp:=mdp) (γ:=γ) (v:=v₁))
  have h3 : dist d c ≤ (1 : ℝ) / 2 := by
    -- one-step rounding error at v₂ (note the order in dist)
    have := T_int_one_step_error_le (S:=S) (A:=A) (mdp:=mdp) (γ:=γ) (v:=v₂)
    -- dist is symmetric
    simpa [d, c, dist_comm] using this
  -- Lipschitz (γ) for the real Bellman operator
  have hLip := bellmanReal_isLipschitz (S:=S) (A:=A) mdp (γ : ℝ) hγ_real_nonneg hγ_real_lt
  have h2 : dist b d ≤ (γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) := by
    -- Extract the dist inequality from LipschitzWith
    have := (lipschitzWith_iff_dist_le_mul).1 hLip (castZtoR v₁) (castZtoR v₂)
    simpa [NNReal.coe_mk, b, d]
      using this
  -- Now combine: dist a c ≤ dist a b + dist b d + dist d c
  have htriangle :
      dist a c ≤ dist a b + (dist b d + dist d c) := by
    have hbdc : dist b c ≤ dist b d + dist d c := by
      simpa [dist_comm] using dist_triangle_right (b) (c) (d)
    have habc : dist a c ≤ dist a b + dist b c := by
      simpa [dist_comm] using dist_triangle_right (a) (c) (b)
    exact le_trans habc (by exact add_le_add_right hbdc (dist a b))
  -- Plug the bounds and simplify
  refine le_trans htriangle ?_
  -- Bound each term
  have : dist a b + (dist b d + dist d c)
      ≤ (1 : ℝ) / 2 + ((γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) / 2) := by
    apply add_le_add
    · exact h1
    · exact add_le_add h2 h3
  -- Reassociate and simplify 1/2 + (γ⋅dist + 1/2) = γ⋅dist + 1
  have hsum :
      (1 : ℝ) / 2 + ((γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) / 2)
        = (γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) := by
    ring
  -- Finish by rewriting with the identity
  have hsum_le :
      (1 : ℝ) / 2 + ((γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) / 2)
        ≤ (γ : ℝ) * dist (castZtoR v₁) (castZtoR v₂) + (1 : ℝ) := by
    simpa [hsum]
      using (le_of_eq hsum)
  exact le_trans this hsum_le

-- Generic affine recurrence unrolling helper.
-- If a sequence `e : ℕ → ℝ` satisfies `e (n+1) ≤ γ * e n + c` for all `n`,
-- then `e n ≤ γ^n * e 0 + c * ∑_{i < n} γ^i`.
lemma unroll_affine_recur
    (γr c : ℝ) (e : ℕ → ℝ) (hγr_nonneg : 0 ≤ γr)
    (Hrec : ∀ n, e (n+1) ≤ γr * e n + c) :
    ∀ n, e n ≤ γr^n * e 0 + c * ((Finset.range n).sum (fun i => γr^i)) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have rec_step : e (k + 1) ≤ γr * e k + c := Hrec k
    have ih_bound : γr * e k ≤ γr * (γr^k * e 0 + c * ∑ i ∈ Finset.range k, γr^i) :=
      mul_le_mul_of_nonneg_left ih hγr_nonneg

    -- Combine the recurrence and inductive hypothesis
    have combined : e (k + 1) ≤ γr * (γr^k * e 0 + c * ∑ i ∈ Finset.range k, γr^i) + c :=
      le_trans rec_step (add_le_add ih_bound (le_refl c))

    -- Now we need to show that the RHS equals γr^(k+1) * e 0 + c * ∑ i ∈ Finset.range (k+1), γr^i
    have key_eq : γr * (γr^k * e 0 + c * ∑ i ∈ Finset.range k, γr^i) + c =
                  γr^(k+1) * e 0 + c * ∑ i ∈ Finset.range (k+1), γr^i := by
      -- Expand the left side
      have expand_lhs : γr * (γr^k * e 0 + c * ∑ i ∈ Finset.range k, γr^i) + c =
                        γr * γr^k * e 0 + c * γr * ∑ i ∈ Finset.range k, γr^i + c := by
        rw [mul_add, ← mul_assoc]
        grind [mul_comm, mul_assoc]

      -- Simplify γr * γr^k = γr^(k+1)
      have pow_simp : γr * γr^k = γr^(k+1) := by grind [pow_succ]

      -- The key identity: c * γr * ∑_{i<k} γr^i + c = c * ∑_{i<k+1} γr^i
      have sum_identity : c * γr * ∑ i ∈ Finset.range k, γr^i + c = c * ∑ i ∈ Finset.range (k+1), γr^i := by
        -- Use the sum range expansion directly
        rw [Finset.sum_range_succ, mul_add]
        -- Now: c * γr * ∑ i ∈ Finset.range k, γr^i + c = c * ∑ i ∈ Finset.range k, γr^i + c * γr^k

        -- Sum transformation helper
        have sum_transform : ∑ i ∈ Finset.range k, γr * γr^i = ∑ i ∈ Finset.range k, γr^(i+1) := by
          congr 1
          ext i
          rw [pow_succ, mul_comm]

        -- Use calculation approach
        calc c * γr * ∑ i ∈ Finset.range k, γr^i + c
          = c * (γr * ∑ i ∈ Finset.range k, γr^i) + c := by rw [mul_assoc]
          _ = c * (∑ i ∈ Finset.range k, γr * γr^i) + c := by rw [← Finset.mul_sum]
          _ = c * (∑ i ∈ Finset.range k, γr^(i+1)) + c := by rw [sum_transform]
          _ = c * (∑ i ∈ Finset.range k, γr^(i+1)) + c * 1 := by rw [mul_one]
          _ = c * (∑ i ∈ Finset.range k, γr^(i+1)) + c * γr^0 := by rw [pow_zero]
          _ = c * (∑ i ∈ Finset.range k, γr^(i+1) + γr^0) := by rw [← mul_add]
          _ = c * (∑ i ∈ Finset.range (k+1), γr^i) := by
              congr 1
              rw [← Finset.sum_range_succ']
          _ = c * ∑ i ∈ Finset.range k, γr^i + c * γr^k := by rw [Finset.sum_range_succ, mul_add]


      grind

    grind


lemma geom_sum_le_inv_one_sub
    (γr : ℝ) (n : ℕ) (hγr_nonneg : 0 ≤ γr) (hγr_lt : γr < 1) :
    ((Finset.range n).sum (fun i => γr^i)) ≤ 1 / (1 - γr) := by
  have h_pos : 0 < 1 - γr := by linarith
  have h_ne_one : γr ≠ 1 := ne_of_lt hγr_lt
  
  -- Use geometric series formula
  rw [geom_sum_eq h_ne_one n]
  
  -- We have: (γr^n - 1) / (γr - 1) ≤ 1 / (1 - γr)
  -- Since γr - 1 = -(1 - γr), we have:
  -- (γr^n - 1) / (-(1 - γr)) ≤ 1 / (1 - γr)
  -- Multiply by (1 - γr) > 0: -(γr^n - 1) ≤ 1
  -- So: 1 - γr^n ≤ 1, which is true since γr^n ≥ 0
  
  have h_pow_nonneg : 0 ≤ γr ^ n := pow_nonneg hγr_nonneg n
  have h_eq : (γr ^ n - 1) / (γr - 1) = (1 - γr ^ n) / (1 - γr) := by
    have h_ne_zero : γr - 1 ≠ 0 := ne_of_lt (by linarith : γr - 1 < 0)
    have h_pos_ne_zero : 1 - γr ≠ 0 := ne_of_gt h_pos
    field_simp [h_ne_zero, h_pos_ne_zero]
    ring
  
  rw [h_eq]
  
  -- Now we need: (1 - γr^n) / (1 - γr) ≤ 1 / (1 - γr)
  -- Since 1 - γr > 0, this is equivalent to: 1 - γr^n ≤ 1
  have h_le : 1 - γr ^ n ≤ 1 := by linarith [h_pow_nonneg]
  
  exact div_le_div_of_nonneg_right h_le (le_of_lt h_pos)


-- Main approximate convergence inequality (to be proved)
theorem INT_VALUE_ITERATION_APPROX
    (mdp : MDP S A) (γ : ℚ) (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1) :
    ∃ v_star : S → ℝ,
      bellmanOperatorReal (S:=S) (A:=A) mdp (γ : ℝ) v_star = v_star ∧
      ∀ (v₀ : S → ℤ) (n : ℕ),
        dist (castZtoR ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[n] v₀)) v_star
          ≤ (γ : ℝ)^n * dist (castZtoR v₀) v_star +
            ((1 : ℝ) / 2) / (1 - (γ : ℝ)) := by
  classical
  -- Real parameters and fixed point
  set γr : ℝ := (γ : ℝ)
  have hγr_nonneg : (0 : ℝ) ≤ γr := Rat.cast_nonneg.mpr hγ_nonneg
  have hγr_lt : γr < 1 := by
    rw [← Rat.cast_one, show γr = (γ : ℝ) by rfl]; exact Rat.cast_lt.mpr hγ_lt
  obtain ⟨_, _, hexists⟩ :=
    value_iteration_banach_success (S:=S) (A:=A) mdp γr hγr_nonneg hγr_lt
  obtain ⟨v_star, h_fixed, _⟩ := hexists
  have h_fix : bellmanOperatorReal (S:=S) (A:=A) mdp γr v_star = v_star := h_fixed.1
  refine ⟨v_star, h_fix, ?_⟩
  intro v₀ n
  -- Error sequence and Lipschitz of the real operator
  let e : ℕ → ℝ := fun k =>
    dist (castZtoR ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[k] v₀)) v_star
  have hLip := bellmanReal_isLipschitz (S:=S) (A:=A) mdp γr hγr_nonneg hγr_lt
  -- One-step recurrence: e (k+1) ≤ γr * e k + 1/2
  have Hrec : ∀ k, e (k+1) ≤ γr * e k + (1 : ℝ) / 2 := by
    intro k
    set v_k : S → ℤ := ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[k] v₀) with hvk
    have h_round :
        dist (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v_k))
             (bellmanOperatorReal (S:=S) (A:=A) mdp γr (castZtoR v_k))
          ≤ (1 : ℝ) / 2 :=
      T_int_one_step_error_le (S:=S) (A:=A) (mdp:=mdp) (γ:=γ) (v:=v_k)
    have h_lip_step :
        dist (bellmanOperatorReal (S:=S) (A:=A) mdp γr (castZtoR v_k)) v_star
          ≤ γr * dist (castZtoR v_k) v_star := by
      have := (lipschitzWith_iff_dist_le_mul).1 hLip (castZtoR v_k) v_star
      simpa [h_fix, NNReal.coe_mk]
        using this
    have htri :
        dist (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v_k)) v_star
          ≤ dist (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v_k))
                (bellmanOperatorReal (S:=S) (A:=A) mdp γr (castZtoR v_k))
            + dist (bellmanOperatorReal (S:=S) (A:=A) mdp γr (castZtoR v_k)) v_star := by
      simpa [dist_comm] using dist_triangle_right
        (castZtoR (bellmanOperatorInt (S:=S) (A:=A) mdp γ v_k))
        v_star
        (bellmanOperatorReal (S:=S) (A:=A) mdp γr (castZtoR v_k))
    have := le_trans htri (add_le_add h_round h_lip_step)
    simpa [e, hvk, Function.iterate_succ_apply', add_comm]
      using this
  -- Unroll the recurrence using the helper lemma
  have Hunroll :=
    unroll_affine_recur (γr:=γr) (c:=(1 : ℝ) / 2) (e:=e) hγr_nonneg Hrec n
  -- Bound the geometric sum using the proved bound
  have Hsum := geom_sum_le_inv_one_sub γr n hγr_nonneg hγr_lt
  have hhalf_nonneg : (0 : ℝ) ≤ (1 : ℝ) / 2 := by norm_num
  have Hscaled : (1 : ℝ) / 2 * (∑ i ∈ Finset.range n, γr^i)
      ≤ (1 : ℝ) / 2 * (1 / (1 - γr)) :=
    mul_le_mul_of_nonneg_left Hsum hhalf_nonneg
  calc
    e n
        ≤ γr^n * e 0 + (1 : ℝ) / 2 * (∑ i ∈ Finset.range n, γr^i) := Hunroll
    _ ≤ γr^n * e 0 + (1 : ℝ) / 2 * (1 / (1 - γr)) := by
      have h := Hscaled
      exact add_le_add_right h (γr^n * e 0)
    _ = γr^n * dist (castZtoR v₀) v_star + ((1 : ℝ) / 2) / (1 - γr) := by
      simp [e, div_eq_mul_inv]

-- Eventual ball corollary (to be proved)
theorem INT_VALUE_ITERATION_EVENTUAL_BALL
    (mdp : MDP S A) (γ : ℚ) (hγ_nonneg : 0 ≤ γ) (hγ_lt : γ < 1)
    (ε : ℝ) (hε : ((1 : ℝ) / 2) / (1 - (γ : ℝ)) < ε) :
    ∀ v₀ : S → ℤ, ∀ᶠ n in atTop,
      let v_starWitness := Classical.choose
        (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)
      have hfix := (Classical.choose_spec
        (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)).1
      let v_star : S → ℝ := v_starWitness
      dist (castZtoR ((bellmanOperatorInt (S:=S) (A:=A) mdp γ)^[n] v₀)) v_star ≤ ε := by
  classical
  intro v₀
  -- Real parameters
  set γr : ℝ := (γ : ℝ)
  have hγr_nonneg : (0 : ℝ) ≤ γr := Rat.cast_nonneg.mpr hγ_nonneg
  have hγr_lt : γr < 1 := by
    rw [← Rat.cast_one, show γr = (γ : ℝ) by rfl]; exact Rat.cast_lt.mpr hγ_lt
  -- Extract the fixed point and quantitative inequality
  set v_starWitness := Classical.choose
    (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)
  have hpair := Classical.choose_spec
    (INT_VALUE_ITERATION_APPROX (S:=S) (A:=A) mdp γ hγ_nonneg hγ_lt)
  have hfix := hpair.1
  let v_star : S → ℝ := v_starWitness
  have Hbound := hpair.2 v₀
  -- Noise floor and margin
  let M : ℝ := ((1 : ℝ) / 2) / (1 - γr)
  have hMlt : M < ε := hε
  -- Suffices: geometric term is eventually ≤ ε - M
  suffices h_event : ∀ᶠ n in atTop, γr^n * dist (castZtoR v₀) v_star ≤ ε - M by
    -- From the quantitative bound and h_event, conclude the claim pointwise
    refine h_event.mono ?_
    intro n hgeom
    have hbound := Hbound n
    have hsum : γr^n * dist (castZtoR v₀) v_star + M ≤ (ε - M) + M :=
      add_le_add hgeom (le_refl M)
    have : γr^n * dist (castZtoR v₀) v_star + M ≤ ε := by
      simpa [sub_add_cancel] using hsum
    exact le_trans hbound this
  -- Show γ^n → 0 hence eventually ≤ ε - M
  -- Handle the two cases depending on the initial distance
  by_cases hC0 : dist (castZtoR v₀) v_star = 0
  · -- Trivial: geometric term is identically 0
    have hpos : 0 ≤ ε - M := sub_nonneg.mpr (le_of_lt hMlt)
    refine Eventually.of_forall ?_
    intro n
    simp [hC0, hpos]
  · -- Nontrivial: use convergence (γr^n → 0) and scale by the positive constant
    have hneC : 0 ≠ dist (castZtoR v₀) v_star := by simpa [eq_comm] using hC0
    have hCpos : 0 < dist (castZtoR v₀) v_star :=
      lt_of_le_of_ne (by simpa using dist_nonneg) hneC
    have habs : |γr| < 1 := by
      have := hγr_lt
      have hnonneg : 0 ≤ γr := hγr_nonneg
      simpa [abs_of_nonneg hnonneg]
        using this
    have hpow0 : Tendsto (fun n => γr^n) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
    -- Choose δ := (ε - M) / dist ... > 0
    have hδpos : 0 < (ε - M) / dist (castZtoR v₀) v_star := by
      have hpos : 0 < ε - M := sub_pos.mpr hMlt
      exact div_pos hpos hCpos
    have h_ev_small : ∀ᶠ n in atTop, |γr^n| < (ε - M) / dist (castZtoR v₀) v_star := by
      have : (Metric.ball (0 : ℝ) ((ε - M) / dist (castZtoR v₀) v_star)) ∈ 𝓝 (0 : ℝ) :=
        Metric.ball_mem_nhds (0 : ℝ) hδpos
      refine (hpow0.eventually this).mono ?_
      intro n hn
      -- In ℝ, membership in the ball is |x - 0| < radius
      simpa [Metric.mem_ball, Real.dist_eq, sub_self] using hn
    -- Since γr^n ≥ 0, we can drop absolute values and multiply by the positive constant
    have h_ev_le : ∀ᶠ n in atTop, γr^n ≤ (ε - M) / dist (castZtoR v₀) v_star := by
      refine h_ev_small.mono ?_
      intro n hlt
      have hnn : 0 ≤ γr^n := pow_nonneg hγr_nonneg n
      have hlt' : γr^n < (ε - M) / dist (castZtoR v₀) v_star := by
        simpa [abs_of_nonneg hnn] using hlt
      exact le_of_lt hlt'
    -- Multiply both sides by the positive constant to obtain the desired inequality
    refine h_ev_le.mono ?_
    intro n hle
    have hCnonneg : 0 ≤ dist (castZtoR v₀) v_star := by simpa using dist_nonneg
    have hCne : dist (castZtoR v₀) v_star ≠ 0 := ne_of_gt hCpos
    have := mul_le_mul_of_nonneg_right hle hCnonneg
    -- (ε - M) / C * C = ε - M since C ≠ 0
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hCne]
      using this


end ApproxValueIterationInt
