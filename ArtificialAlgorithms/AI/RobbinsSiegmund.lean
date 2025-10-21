import Mathlib

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

open MeasureTheory
open scoped ProbabilityTheory BigOperators

namespace QLS
namespace Stoch

section Classical

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable (ℱ : Filtration ℕ m0)

variable (X Y Z W : ℕ → Ω → ℝ)

/-- Cumulative product `∏_{k < t} (1 + Y_{k+1})`. -/
noncomputable def prodY (Y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range t).prod fun k => 1 + Y (k + 1) ω

/-- Cumulative sum of `W`. -/
def cumW (W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (t + 1)).sum fun k => W k ω

/-- Recurrence for the cumulative sum. -/
lemma cumW_succ (W : ℕ → Ω → ℝ) (n : ℕ) :
    cumW W (n + 1) = fun ω => cumW W n ω + W (n + 1) ω := by
  funext ω
  classical
  simp [cumW, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

/-- Non-negativity of the cumulative sum under non-negativity of each increment. -/
lemma cumW_nonneg (hW : ∀ t ω, 0 ≤ W t ω) : ∀ t ω, 0 ≤ cumW W t ω := by
  intro t ω
  classical
  induction' t with n ih
  · simpa [cumW] using hW 0 ω
  · have ih' : 0 ≤ cumW W n ω := ih
    have hW' : 0 ≤ W (n + 1) ω := hW _ _
    have := add_nonneg ih' hW'
    simpa [cumW_succ, add_comm, add_left_comm, add_assoc] using this

/-- Integrability of the cumulative sum given integrability of each increment. -/
lemma integrable_cumW (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ t, Integrable (cumW W t) μ := by
  intro t
  classical
  induction' t with n ih
  · -- base: cumW W 0 = W 0
    have : (cumW W 0) = fun ω => W 0 ω := by
      funext ω; simp [cumW]
    simpa [this] using integrable_W 0
  · have ih' := ih
    have hW' := integrable_W (n + 1)
    have hsum : Integrable (fun ω => cumW W n ω + W (n + 1) ω) μ := ih'.add hW'
    simpa [cumW_succ, add_comm, add_left_comm, add_assoc] using hsum

/-- Scaled `Z` term. -/
noncomputable def scaledZ (Y Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => Z (t + 1) ω / prodY Y t ω

/-- Alternative scaled Z using the next-step denominator `P_{t+1}`. -/
noncomputable def scaledZ_next (Y Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => Z (t + 1) ω / prodY Y (t + 1) ω

/-- Partial sums of `scaledZ_next`, i.e. `∑_{k=0}^{t-1} Z_{k+1}/P_{k+1}`. -/
noncomputable def Csum (Y Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range t).sum (fun k => scaledZ_next Y Z k ω)

/-- Partial sums of the `scaledZ` with denominator `P_t`: `∑_{k=0}^{t-1} Z_{k+1}/P_k`. -/
noncomputable def Zsum (Y Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range t).sum (fun k => scaledZ Y Z k ω)

/-- Partial sums of the scaled `Z`.  With our indexing convention this corresponds to the classical quantity
`∑_{k = 0}^{t} Z_{k+1} / prodY Y k`. -/
noncomputable def B_part (Y Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (t + 1)).sum fun k => scaledZ Y Z k ω

/-- Recurrence for the partial sums of the scaled `Z`. -/
lemma B_part_succ (Y Z : ℕ → Ω → ℝ) (n : ℕ) :
    B_part Y Z (n + 1) = fun ω => B_part Y Z n ω + scaledZ Y Z (n + 1) ω := by
  funext ω
  classical
  simp [B_part, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

/-- Scaled version of `X` plus the cumulative `W`. -/
noncomputable def scaledS (X Y W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (X t ω + cumW W t ω) / prodY Y t ω

/-- Compensated normalized process used in approach (1): `M_t = S_t - ∑_{k<t} Z_{k+1}/P_{k+1}`. -/
noncomputable def Mproc (X Y Z W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => scaledS X Y W t ω - Csum Y Z t ω

/-- Compensated normalized process using `Zsum`: `Mpred_t = S_t - ∑_{k<t} Z_{k+1}/P_k`. -/
noncomputable def Mpred (X Y Z W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => scaledS X Y W t ω - Zsum Y Z t ω

/-- Truncated partial sums of the scaled `Z`.  This realises the truncation
`B_{min(t,N)}` from the textbook proof. -/
noncomputable def B_trunc (Y Z : ℕ → Ω → ℝ) (N t : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range (Nat.min t N)).sum fun k => scaledZ Y Z k ω

-- Convenience rewrites for B_trunc in the two branches `t ≤ N` and `N ≤ t`.
lemma B_trunc_of_le_left (Y Z : ℕ → Ω → ℝ) {N t : ℕ} (htN : t ≤ N) :
    B_trunc Y Z N t =
      (Finset.range t).sum (fun k => scaledZ Y Z k) := by
  funext ω; simp [B_trunc, Nat.min_eq_left htN]

lemma B_trunc_of_le_right (Y Z : ℕ → Ω → ℝ) {N t : ℕ} (hNt : N ≤ t) :
    B_trunc Y Z N t =
      (Finset.range N).sum (fun k => scaledZ Y Z k) := by
  funext ω; simp [B_trunc, Nat.min_eq_right hNt]

lemma B_trunc_succ
    (Y Z : ℕ → Ω → ℝ) (N t : ℕ) :
    B_trunc Y Z N (t + 1) =
      fun ω => B_trunc Y Z N t ω + (if t + 1 ≤ N then scaledZ Y Z t ω else 0) := by
  classical
  by_cases h : t + 1 ≤ N
  · have htN : t ≤ N := Nat.le_trans (Nat.le_succ t) h
    funext ω
    -- Identify both sides as numeric sums and apply the range-succ identity
    have hL : B_trunc Y Z N (t + 1) ω
        = (Finset.range (t + 1)).sum (fun k => scaledZ Y Z k ω) := by
      simp [B_trunc, Nat.min_eq_left h]
    have hR : B_trunc Y Z N t ω
        = (Finset.range t).sum (fun k => scaledZ Y Z k ω) := by
      simp [B_trunc, Nat.min_eq_left htN]
    have hsω : (Finset.range (t + 1)).sum (fun k => scaledZ Y Z k ω)
        = (Finset.range t).sum (fun k => scaledZ Y Z k ω) + scaledZ Y Z t ω := by
      simpa using Finset.sum_range_succ (fun k => scaledZ Y Z k ω) t
    calc
      B_trunc Y Z N (t + 1) ω
          = (Finset.range (t + 1)).sum (fun k => scaledZ Y Z k ω) := hL
      _ = (Finset.range t).sum (fun k => scaledZ Y Z k ω) + scaledZ Y Z t ω := hsω
      _ = B_trunc Y Z N t ω + scaledZ Y Z t ω := by simpa [hR]
      _ = B_trunc Y Z N t ω + (if t + 1 ≤ N then scaledZ Y Z t ω else 0) := by
            simp [h]
  · have hNt : N ≤ t := by
      have : ¬ t < N := by simpa [Nat.succ_le] using h
      exact le_of_not_gt this
    have h1 : B_trunc Y Z N (t + 1)
        = (Finset.range N).sum (fun k => scaledZ Y Z k) := by
      simpa [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := t + 1)
        (Nat.le_trans hNt (Nat.le_succ t))]
    have h2 : B_trunc Y Z N t
        = (Finset.range N).sum (fun k => scaledZ Y Z k) := by
      simpa [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := t) hNt]
    funext ω
    simp [h1, h2, h]

/-- Truncated compensated process used in the Doob argument. -/
noncomputable def Scomp_trunc (N t : ℕ) : Ω → ℝ :=
  fun ω =>
    scaledS X Y W t ω
      + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
      - B_trunc Y Z N t ω

/-- Stopped version: keep the scaled part constant after time `N`. -/
noncomputable def Scomp_trunc_stop (N t : ℕ) : Ω → ℝ :=
  fun ω =>
    scaledS X Y W (Nat.min t N) ω
      + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
      - B_trunc Y Z N t ω

/-- Placeholder: positivity of the cumulative product. -/
lemma prodY_pos (hY : ∀ t ω, 0 ≤ Y t ω) : ∀ t ω, 0 < prodY Y t ω := by
  intro t ω
  classical
  induction' t with n ih
  · simpa [prodY] using (show (0 : ℝ) < 1 by norm_num)
  · have h₁ : 0 < prodY Y n ω := ih
    have h₂ : 0 ≤ Y (n + 1) ω := hY _ _
    have h₂'' : (1 : ℝ) ≤ 1 + Y (n + 1) ω := by
      simpa using add_le_add_left h₂ (1 : ℝ)
    have h₂' : 0 < 1 + Y (n + 1) ω :=
      lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) h₂''
    have hprod : prodY Y (n + 1) ω = prodY Y n ω * (1 + Y (n + 1) ω) := by
      simp [prodY, Finset.prod_range_succ]
    simpa [hprod] using mul_pos h₁ h₂'

/-- Lower bound by one for the cumulative product. -/
lemma prodY_ge_one (hY : ∀ t ω, 0 ≤ Y t ω) : ∀ t ω, 1 ≤ prodY Y t ω := by
  intro t ω
  classical
  induction' t with n ih
  · simp [prodY]
  · have hprod : prodY Y (n + 1) ω = prodY Y n ω * (1 + Y (n + 1) ω) := by
      simp [prodY, Finset.prod_range_succ]
    have h₁ : 1 ≤ prodY Y n ω := ih
    have hy : 0 ≤ Y (n + 1) ω := hY _ _
    have h₂ : 1 ≤ 1 + Y (n + 1) ω := by
      simpa using add_le_add_left hy (1 : ℝ)
    have hpos : 0 ≤ prodY Y n ω := (prodY_pos (Y := Y) hY n ω).le
    have : 1 ≤ prodY Y n ω * (1 + Y (n + 1) ω) := by
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have := mul_le_mul h₁ h₂ h01 hpos
      simpa using this
    simpa [hprod] using this


/-- Measurability of the scaled process. -/
lemma scaledS_measurable
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_W : Adapted ℱ W) :
    ∀ t, StronglyMeasurable[ℱ t] (scaledS X Y W t) := by
  intro t
  -- Strategy: StronglyMeasurable → Measurable → Measurable.div → StronglyMeasurable
  apply Measurable.stronglyMeasurable
  -- Show numerator is measurable
  have h_num : Measurable[ℱ t] fun ω => X t ω + cumW W t ω := by
    apply Measurable.add
    · exact (adapted_X t).measurable
    · -- cumW W t is a finite sum of adapted processes
      unfold cumW
      apply Finset.measurable_sum
      intro k hk
      have hk_le : k ≤ t := by simp at hk; omega
      exact ((adapted_W k).mono (ℱ.mono hk_le)).measurable
  -- Show denominator is measurable
  have h_denom : Measurable[ℱ t] (prodY Y t) := by
    unfold prodY
    apply Finset.measurable_prod
    intro k hk
    have : k + 1 ≤ t := by simp at hk; omega
    exact ((adapted_Y (k + 1)).mono (ℱ.mono this)).measurable.const_add 1
  -- Apply division measurability
  exact h_num.div h_denom

/-- Strong measurability of the scaled `Z` term using predictability. -/
lemma scaledZ_measurable
    (adapted_Y : Adapted ℱ Y) (predictable_Z : Adapted ℱ fun t => Z (t + 1)) :
    ∀ t, StronglyMeasurable[ℱ t] (scaledZ Y Z t) := by
  intro t
  classical
  unfold scaledZ
  apply Measurable.stronglyMeasurable
  have h_num : Measurable[ℱ t] fun ω => Z (t + 1) ω := (predictable_Z t).measurable
  have h_denom : Measurable[ℱ t] (prodY Y t) := by
    unfold prodY
    apply Finset.measurable_prod
    intro k hk
    have : k + 1 ≤ t := by simp at hk; omega
    exact ((adapted_Y (k + 1)).mono (ℱ.mono this)).measurable.const_add 1
  exact h_num.div h_denom

/-- A pointwise bound comparing `scaledZ` with the original `Z`. -/
lemma abs_scaledZ_le
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) :
    ∀ t ω, |scaledZ Y Z t ω| ≤ Z (t + 1) ω := by
  intro t ω
  have hden_pos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
  have hden_ge : 1 ≤ prodY Y t ω := prodY_ge_one (Y := Y) hY_nonneg t ω
  have hZ : 0 ≤ Z (t + 1) ω := hZ_nonneg _ _
  have h_nonneg : 0 ≤ scaledZ Y Z t ω := by
    unfold scaledZ
    exact div_nonneg hZ hden_pos.le
  have h_le : scaledZ Y Z t ω ≤ Z (t + 1) ω := by
    unfold scaledZ
    exact div_le_self hZ hden_ge
  simpa [abs_of_nonneg h_nonneg] using h_le

/-- Integrability of the scaled `Z` term via domination by `Z`. -/
lemma integrable_scaledZ
    (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ) :
    ∀ t, Integrable (scaledZ Y Z t) μ := by
  intro t
  classical
  have h_meas : AEStronglyMeasurable (scaledZ Y Z t) μ :=
    ((scaledZ_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y predictable_Z t).mono (ℱ.le t)).aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ‖scaledZ Y Z t ω‖ ≤ ‖Z (t + 1) ω‖ := by
    refine ae_of_all μ fun ω => ?_
    have h := abs_scaledZ_le (Y := Y) (Z := Z) hY_nonneg hZ_nonneg t ω
    have hZnon : 0 ≤ Z (t + 1) ω := hZ_nonneg _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg hZnon] using h
  have hZ_int : Integrable (fun ω => Z (t + 1) ω) μ := integrable_Z (t + 1)
  exact Integrable.mono hZ_int h_meas h_bound

/-- Integrability of the partial sums of the scaled `Z`. -/
lemma integrable_B_part
    (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ) :
    ∀ t, Integrable (B_part Y Z t) μ := by
  intro t
  classical
  induction' t with n ih
  · have h0 : B_part Y Z 0 = scaledZ Y Z 0 := by
      funext ω; simp [B_part, Finset.range_one]
    simpa [h0] using
      (integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y adapted_Z
        predictable_Z hY_nonneg hZ_nonneg integrable_Z 0)
  · have ih' := ih
    have hscaled := integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z (n + 1)
    have hsum : Integrable
        (fun ω => B_part Y Z n ω + scaledZ Y Z (n + 1) ω) μ := ih'.add hscaled
    simpa [B_part_succ, add_comm, add_left_comm, add_assoc] using hsum

/-- Integrability of the truncated partial sums. -/
lemma integrable_B_trunc
    (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ) :
    ∀ N t, Integrable (B_trunc Y Z N t) μ := by
  intro N t
  classical
  -- Let n = min t N. If n=0, the sum is empty; otherwise it equals B_part at (n-1).
  set n := Nat.min t N with hn
  by_cases h0 : n = 0
  · -- Empty sum case: integrable constant zero
    have hmin0 : t.min N = 0 := by simpa [hn] using h0
    have hfun : B_trunc Y Z N t = (fun _ : Ω => 0) := by
      funext ω; simp [B_trunc, hmin0]
    simpa [hfun] using (integrable_const (μ := μ) (c := (0 : ℝ)))
  · -- Nonempty sum: n = m + 1, rewrite as B_part at index m and reuse its integrability
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hmin : t.min N = m + 1 := by simpa [hn] using hm
    have hfun : B_trunc Y Z N t = B_part Y Z m := by
      funext ω; simp [B_trunc, B_part, hmin]
    simpa [hfun] using
      (integrable_B_part (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z m)

/-- Bounding the scaled `S` process by integrable terms. -/
lemma abs_scaledS_le
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω) :
    ∀ t ω, |scaledS X Y W t ω| ≤ |X t ω| + cumW W t ω := by
  intro t ω
  have hden_pos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
  have hden_ge : 1 ≤ prodY Y t ω := prodY_ge_one (Y := Y) hY_nonneg t ω
  have hnonneg_cum : 0 ≤ cumW W t ω := cumW_nonneg (W := W) hW_nonneg t ω
  have h1 : |scaledS X Y W t ω| ≤ |X t ω + cumW W t ω| := by
    have h_abs : |scaledS X Y W t ω| = |X t ω + cumW W t ω| / prodY Y t ω := by
      simp [scaledS, abs_div, abs_of_pos hden_pos]
    have hdiv : |X t ω + cumW W t ω| / prodY Y t ω ≤ |X t ω + cumW W t ω| := by
      have hnn : 0 ≤ |X t ω + cumW W t ω| := abs_nonneg _
      exact div_le_self hnn hden_ge
    simpa [h_abs] using hdiv
  have h2 : |X t ω + cumW W t ω| ≤ |X t ω| + cumW W t ω := by
    have htriangle : |X t ω + cumW W t ω| ≤ |X t ω| + |cumW W t ω| := by
      simpa using abs_add_le (X t ω) (cumW W t ω)
    simpa [abs_of_nonneg hnonneg_cum] using htriangle
  exact le_trans h1 h2

/-- Integrability of the scaled `S` process. -/
lemma integrable_scaledS
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_W : Adapted ℱ W)
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ t, Integrable (scaledS X Y W t) μ := by
  intro t
  classical
  have h_meas : AEStronglyMeasurable (scaledS X Y W t) μ :=
    ((scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
        adapted_X adapted_Y adapted_W t).mono (ℱ.le t)).aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂μ, ‖scaledS X Y W t ω‖ ≤ ‖|X t ω| + cumW W t ω‖ := by
    refine ae_of_all μ fun ω => ?_
    have hle := abs_scaledS_le (X := X) (Y := Y) (W := W)
      hY_nonneg hW_nonneg t ω
    have hx := abs_nonneg (X t ω)
    have hcw := cumW_nonneg (W := W) hW_nonneg t ω
    have hnonneg : 0 ≤ |X t ω| + cumW W t ω := add_nonneg hx hcw
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_abs] using hle
  have hX_abs : Integrable (fun ω => |X t ω|) μ := (integrable_X t).abs
  have hcum : Integrable (cumW W t) μ := integrable_cumW (μ := μ) (W := W) integrable_W t
  have h_sum : Integrable (fun ω => |X t ω| + cumW W t ω) μ := hX_abs.add hcum
  exact Integrable.mono h_sum h_meas h_bound

/-- Integrability of the compensated truncated process. -/
lemma integrable_Scomp_trunc
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ) (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ N t, Integrable (Scomp_trunc μ ℱ X Y Z W N t) μ := by
  intro N t
  classical
  have h_scaled := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
  have h_condexp : Integrable (μ[fun ω' => B_trunc Y Z N N ω' | ℱ t]) μ :=
    integrable_condExp (μ := μ) (m := ℱ t) (f := fun ω => B_trunc Y Z N N ω)
  have h_trunc := integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N t
  have h_sum : Integrable
      (fun ω => scaledS X Y W t ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω) μ :=
    h_scaled.add h_condexp
  have h_all := h_sum.sub h_trunc
  simpa [Scomp_trunc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_all


/-- Measurability of the truncated `B`. Predictability of `Z` is essential here because
the summand with index `k = t` involves `Z (t + 1)` while we require ℱₜ-measurability. -/
lemma B_trunc_measurable
    (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1)) :
    ∀ N t, StronglyMeasurable[ℱ t] (B_trunc Y Z N t) := by
  intro N t
  -- B_trunc is a finite sum of scaledZ terms
  unfold B_trunc scaledZ
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro k hk
  -- Each scaledZ term is Z(k+1) / prodY Y k
  have hk_lt : k < Nat.min t N := by simpa using hk
  have hk_le_min : k ≤ Nat.min t N := Nat.le_of_lt hk_lt
  have hk_le_t : k ≤ t := hk_le_min.trans (Nat.min_le_left t N)
  have h_num_k : StronglyMeasurable[ℱ k] fun ω => Z (k + 1) ω :=
    (predictable_Z k)
  have h_num : Measurable[ℱ t] fun ω => Z (k + 1) ω := by
    have h_le : ℱ k ≤ ℱ t := ℱ.mono hk_le_t
    exact (h_num_k.mono h_le).measurable
  have h_denom : Measurable[ℱ t] (prodY Y k) := by
    unfold prodY
    apply Finset.measurable_prod
    intro j hj
    have hj' : j < k := by simp at hj; exact hj
    have hj1 : j + 1 ≤ k := Nat.succ_le_of_lt hj'
    have hj2 : j + 1 ≤ t := Nat.le_trans hj1 hk_le_t
    exact ((adapted_Y (j + 1)).mono (ℱ.mono hj2)).measurable.const_add 1
  exact h_num.div h_denom

/-- Pull-out lemma for conditional expectation with an ℱ_t-measurable factor.
If `c` is `ℱ t`-measurable (strongly measurable) and `f` is integrable, then
`μ[c * f | ℱ t] = c * μ[f | ℱ t]` almost everywhere. -/
lemma condexp_mul_left
    (t : ℕ) (c f : Ω → ℝ)
    (hc : StronglyMeasurable[ℱ t] c)
    (hcf_int : Integrable (fun ω => c ω * f ω) μ)
    (hf_int : Integrable f μ) :
    μ[fun ω => c ω * f ω | ℱ t] =ᵐ[μ] fun ω => c ω * μ[f | ℱ t] ω := by
  -- Use mathlib's pull-out property for real-valued conditional expectations
  simpa using
    (MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ t) (μ := μ)
      (f := c) (g := f) hc hcf_int hf_int)

/-- Placeholder: adaptedness of the compensated process. -/
lemma Scomp_trunc_adapted
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    : ∀ N, Adapted ℱ (Scomp_trunc μ ℱ X Y Z W N) := by
  intro N t
  classical
  have h_scaled : StronglyMeasurable[ℱ t] (scaledS X Y W t) :=
    scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W t
  have h_condexp : StronglyMeasurable[ℱ t]
      (μ[fun ω' => B_trunc Y Z N N ω' | ℱ t]) :=
    MeasureTheory.stronglyMeasurable_condExp
  have h_trunc : StronglyMeasurable[ℱ t] (B_trunc Y Z N t) :=
    (B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z) N t
  have h_add : StronglyMeasurable[ℱ t]
      (fun ω => scaledS X Y W t ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω) :=
    h_scaled.add h_condexp
  have h_all : StronglyMeasurable[ℱ t]
      (fun ω => (scaledS X Y W t ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω)
        - B_trunc Y Z N t ω) := h_add.sub h_trunc
  simpa [Scomp_trunc] using h_all
/-- One-step drift for the normalized process: conditional expectation inequality for `scaledS`.
This encodes
  μ[scaledS(t+1) | ℱ_t] ≤ scaledS(t) + Z_{t+1} / P_{t+1}
under the hypotheses (predictability, nonnegativity and integrability).
-/
lemma condexp_scaledS_step
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (adapted_W : Adapted ℱ W) (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    : ∀ t,
      μ[fun ω => scaledS X Y W (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => scaledS X Y W t ω + Z (t + 1) ω / prodY Y (t + 1) ω := by
  intro t
  classical
  -- Reduce to an inequality stated directly on numerators/denominators.
  suffices h :
      μ[fun ω =>
          (X (t + 1) ω + cumW W (t + 1) ω) / prodY Y (t + 1) ω | ℱ t]
        ≤ᵐ[μ]
        fun ω =>
          (X t ω + cumW W t ω) / prodY Y t ω
            + Z (t + 1) ω / prodY Y (t + 1) ω by
    simpa [scaledS] using h
  -- Proof of the reduced inequality (to be filled next).
  -- Introduce the predictable factor c := 1 / prodY Y (t+1) and expand numerators.
  let c : Ω → ℝ := fun ω => 1 / prodY Y (t + 1) ω
  let f1 : Ω → ℝ := fun ω => X (t + 1) ω + cumW W (t + 1) ω
  -- It suffices to prove an inequality after pulling out c and linearizing:
  suffices h2 :
      μ[fun ω => c ω * f1 ω | ℱ t]
        ≤ᵐ[μ]
        fun ω =>
          c ω * ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω) by
    -- Algebraic rewrite to the target normalized inequality
    -- Using P_{t+1} = P_t (1 + Y_{t+1}) and dropping the positive cumW term as needed
    -- We compare the right-hand side with the desired normalized form
    -- using P_{t+1} = P_t (1 + Y_{t+1}) and that P_{t+1} ≥ P_t.
    -- Notation shorthands
    let Pt : Ω → ℝ := prodY Y t
    let Pt1 : Ω → ℝ := prodY Y (t + 1)
    have hprod : ∀ ω, Pt1 ω = Pt ω * (1 + Y (t + 1) ω) := by
      intro ω; simp [Pt, Pt1, prodY, Finset.prod_range_succ]
    have hY_ge_one : ∀ ω, (1 : ℝ) ≤ 1 + Y (t + 1) ω := by
      intro ω; simpa using add_le_add_left (hY_nonneg (t + 1) ω) (1 : ℝ)
    have hPt_nonneg : ∀ ω, 0 ≤ Pt ω := by
      intro ω; exact (prodY_pos (Y := Y) hY_nonneg t ω).le
    have hPt_le_Pt1 : ∀ ω, Pt ω ≤ Pt1 ω := by
      intro ω
      have := mul_le_mul_of_nonneg_left (hY_ge_one ω) (hPt_nonneg ω)
      simpa [hprod ω] using this
    have hcumW_nonneg : ∀ ω, 0 ≤ cumW W t ω := by
      intro ω; exact cumW_nonneg (W := W) hW_nonneg t ω
    -- Pointwise comparison for the RHS of h2 to the normalized RHS
    have hrhs_bound : ∀ ω,
        c ω * ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω)
          ≤ (X t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω + (cumW W t ω) / Pt ω := by
      intro ω
      -- Expand and simplify the first two terms using Pt1 = Pt * (1+Y_{t+1}).
      have hY_pos : 0 < 1 + Y (t + 1) ω :=
        lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (hY_ge_one ω)
      have hY_ne : (1 + Y (t + 1) ω) ≠ 0 := ne_of_gt hY_pos
      have h1 : c ω * ((1 + Y (t + 1) ω) * X t ω)
          = (X t ω) / Pt ω := by
        -- Use Pt1 = Pt * (1+Y_{t+1}) and cancel the (1+Y_{t+1}) factor via mul_div_mul_left
        have hPt1 : Pt1 ω = Pt ω * (1 + Y (t + 1) ω) := hprod ω
        have hY_ne' : (1 + Y (t + 1) ω) ≠ 0 := hY_ne
        have hfrac : ((1 + Y (t + 1) ω) * X t ω) / Pt1 ω
            = (X t ω * (1 + Y (t + 1) ω)) / (Pt ω * (1 + Y (t + 1) ω)) := by
          simpa [hPt1, mul_comm, mul_left_comm, mul_assoc]
        have hcancel : (X t ω * (1 + Y (t + 1) ω)) / (Pt ω * (1 + Y (t + 1) ω))
            = (X t ω) / Pt ω := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_div_mul_left (a := X t ω) (b := Pt ω)
              (c := 1 + Y (t + 1) ω) (hc := hY_ne'))
        have := hfrac.trans hcancel
        simpa [c, div_eq_mul_inv, mul_comm] using this
      have h2' : c ω * (Z (t + 1) ω) = (Z (t + 1) ω) / Pt1 ω := by
        have : c ω = 1 / Pt1 ω := rfl
        simpa [this, div_eq_mul_inv, mul_comm]
      -- For the cumW term, use monotonicity Pt ≤ Pt1 and cumW ≥ 0
      have h3 : c ω * (cumW W t ω) ≤ (cumW W t ω) / Pt ω := by
        -- c ω = 1 / Pt1 ω and Pt ω ≤ Pt1 ω ⇒ (cumW)/Pt1 ≤ (cumW)/Pt
        have hPt_le : Pt ω ≤ Pt1 ω := hPt_le_Pt1 ω
        have hPt_pos : 0 < Pt ω := prodY_pos (Y := Y) hY_nonneg t ω
        have hcum : 0 ≤ cumW W t ω := hcumW_nonneg ω
        have h_inv : (1 / Pt1 ω) ≤ (1 / Pt ω) :=
          one_div_le_one_div_of_le hPt_pos hPt_le
        have := mul_le_mul_of_nonneg_left h_inv hcum
        simpa [c, div_eq_mul_inv, mul_comm] using this
      -- Assemble the three components
      calc
        c ω * ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω)
            = c ω * ((1 + Y (t + 1) ω) * X t ω)
                + c ω * (Z (t + 1) ω)
                + c ω * (cumW W t ω) := by ring
        _ ≤ (X t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω + (cumW W t ω) / Pt ω := by
          -- Replace the first two terms by equalities `h1` and `h2'`, then use `h3`.
          have := add_le_add (le_of_eq h1) (le_of_eq h2')
          exact add_le_add this h3
    -- First, rewrite the left-hand side to the normalized integrand.
    have hfg : (fun ω => c ω * f1 ω)
        = (fun ω =>
            (X (t + 1) ω + cumW W (t + 1) ω) / prodY Y (t + 1) ω) := by
      funext ω; simp [c, f1, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have h2' :
        μ[fun ω =>
            (X (t + 1) ω + cumW W (t + 1) ω) / prodY Y (t + 1) ω | ℱ t]
          ≤ᵐ[μ]
        (fun ω =>
          c ω * ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω)) := by
      simpa [hfg]
        using h2
    -- Combine h2' with the deterministic pointwise bound `hrhs_bound`.
    refine (h2'.trans ?_)
    refine ae_of_all μ ?_
    intro ω
    -- Rearrange the right-hand side into the target shape.
    have hrearr :
        (X t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω + (cumW W t ω) / Pt ω
          = (X t ω + cumW W t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω := by
      have hsum_eq :
          (X t ω + cumW W t ω) / Pt ω
            = (X t ω) / Pt ω + (cumW W t ω) / Pt ω := by
        simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc]
          using (add_div (X t ω) (cumW W t ω) (Pt ω))
      calc
        (X t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω + (cumW W t ω) / Pt ω
            = (X t ω) / Pt ω + ((Z (t + 1) ω) / Pt1 ω + (cumW W t ω) / Pt ω) := by
              simp [add_assoc]
        _ = (X t ω) / Pt ω + ((cumW W t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω) := by
              simp [add_comm]
        _ = ((X t ω) / Pt ω + (cumW W t ω) / Pt ω) + (Z (t + 1) ω) / Pt1 ω := by
              simp [add_assoc]
        _ = (X t ω + cumW W t ω) / Pt ω + (Z (t + 1) ω) / Pt1 ω := by
              simpa [hsum_eq]
    -- Now conclude
    simpa [Pt, Pt1, hrearr] using hrhs_bound ω
  -- Further reduction: It suffices to show a drift bound for μ[f1 | ℱ t];
  -- from that, h2 follows via pull-out and c ≥ 0 (details to be filled).
  suffices h3 :
      μ[f1 | ℱ t]
        ≤ᵐ[μ]
        fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω by
    -- Derive h2 from h3 by pulling out the ℱ_t-measurable nonnegative factor c
    -- Show c is ℱ_t-strongly measurable
    have h_denom_meas : Measurable[ℱ t] (prodY Y (t + 1)) := by
      unfold prodY
      apply Finset.measurable_prod
      intro k hk
      have hk' : k < t + 1 := by simpa using hk
      have hk1 : k ≤ t := Nat.le_of_lt_succ hk'
      -- Y (k+1) is ℱ k-measurable via predictability; lift to ℱ t
      have hYk : StronglyMeasurable[ℱ k] fun ω => Y (k + 1) ω :=
        (predictable_Y k)
      have : Measurable[ℱ t] fun ω => Y (k + 1) ω := (hYk.mono (ℱ.mono hk1)).measurable
      simpa using this.const_add 1
    have hc_meas : StronglyMeasurable[ℱ t] c :=
      (Measurable.stronglyMeasurable ((measurable_const).div h_denom_meas))
    -- Integrability of f1 and c * f1
    have hf1_int : Integrable f1 μ := by
      have hX1 : Integrable (X (t + 1)) μ := integrable_X (t + 1)
      have hcum1 : Integrable (cumW W (t + 1)) μ := integrable_cumW (μ := μ) (W := W) integrable_W (t + 1)
      simpa [f1, add_comm, add_left_comm, add_assoc] using hX1.add hcum1
    -- Bound |c * f1| ≤ |f1| using 0 ≤ c ≤ 1
    have hc_nonneg : ∀ ω, 0 ≤ c ω := by
      intro ω
      have hpos : 0 < prodY Y (t + 1) ω := prodY_pos (Y := Y) hY_nonneg (t + 1) ω
      have : 0 < 1 / prodY Y (t + 1) ω := one_div_pos.mpr hpos
      exact this.le
    have hc_le_one : ∀ ω, c ω ≤ 1 := by
      intro ω
      have hge : 1 ≤ prodY Y (t + 1) ω := prodY_ge_one (Y := Y) hY_nonneg (t + 1) ω
      -- 1 / P ≤ 1 when 1 ≤ P and P > 0, via anti-monotonicity of inversion
      have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hge
      simpa [c] using this
    have h_meas_cmulf : AEStronglyMeasurable (fun ω => c ω * f1 ω) μ :=
      ((hc_meas.mono (ℱ.le t)).aestronglyMeasurable.mul hf1_int.aestronglyMeasurable)
    have h_bound_norm : ∀ᵐ ω ∂μ, ‖c ω * f1 ω‖ ≤ ‖‖f1 ω‖‖ := by
      refine ae_of_all μ ?_
      intro ω
      have h1 := hc_nonneg ω
      have h2 := hc_le_one ω
      have hn : 0 ≤ ‖f1 ω‖ := norm_nonneg _
      have := mul_le_mul_of_nonneg_right h2 hn
      simpa [norm_mul, Real.norm_of_nonneg h1, one_mul] using this
    have hcf_int : Integrable (fun ω => c ω * f1 ω) μ :=
      Integrable.mono (hf1_int.norm) h_meas_cmulf h_bound_norm
    -- Pull out c from the conditional expectation (exact equality a.e.)
    have h_pull : μ[fun ω => c ω * f1 ω | ℱ t]
        =ᵐ[μ] fun ω => c ω * μ[f1 | ℱ t] ω :=
      condexp_mul_left (μ := μ) (ℱ := ℱ) (t := t) (c := c) (f := f1)
        hc_meas hcf_int hf1_int
    -- Multiply the drift inequality by nonnegative c to obtain h2
    have h2' :
        μ[fun ω => c ω * f1 ω | ℱ t]
          ≤ᵐ[μ]
        fun ω => c ω * ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω) := by
      filter_upwards [h_pull, h3] with ω h_eq h_le
      have := mul_le_mul_of_nonneg_left h_le (hc_nonneg ω)
      simpa [h_eq]
        using this
    exact h2'
  -- Prove the drift bound h3
  ·
    classical
    -- Split μ[f1 | ℱ t] into μ[X_{t+1}|ℱ t] and μ[cumW_{t+1}|ℱ t]
    have h_add1 :
        μ[f1 | ℱ t]
          =ᵐ[μ]
        fun ω => μ[fun ω => X (t + 1) ω | ℱ t] ω
                + μ[fun ω => cumW W (t + 1) ω | ℱ t] ω := by
      have hx := integrable_X (t + 1)
      have hcum1 := integrable_cumW (μ := μ) (W := W) integrable_W (t + 1)
      have := condExp_add (μ := μ) (m := ℱ t) (hf := hx) (hg := hcum1)
      simpa [f1, add_comm, add_left_comm, add_assoc] using this
    -- Rewrite μ[cumW_{t+1}|ℱ t] using cumW_succ and split
    have h_split2 :
        μ[fun ω => cumW W (t + 1) ω | ℱ t]
          =ᵐ[μ]
        fun ω => μ[fun ω => cumW W t ω | ℱ t] ω
              + μ[fun ω => W (t + 1) ω | ℱ t] ω := by
      have hcumt := integrable_cumW (μ := μ) (W := W) integrable_W t
      have hW1 := integrable_W (t + 1)
      have hadd := condExp_add (μ := μ) (m := ℱ t) (hf := hcumt) (hg := hW1)
      have hrewrite : μ[fun ω => cumW W (t + 1) ω | ℱ t]
          = μ[fun ω => cumW W t ω + W (t + 1) ω | ℱ t] := by
        have : (fun ω => cumW W (t + 1) ω)
            = (fun ω => cumW W t ω + W (t + 1) ω) := by
          funext ω; simpa [cumW_succ, add_comm, add_left_comm, add_assoc]
        simpa [this]
      exact ((Filter.EventuallyEq.of_eq hrewrite).trans hadd)
    -- Identify predictable pieces under conditional expectation
    have h_cumW_meas : StronglyMeasurable[ℱ t] (cumW W t) := by
      unfold cumW
      apply Measurable.stronglyMeasurable
      apply Finset.measurable_sum
      intro k hk
      have hk_le : k ≤ t := by
        have : k < t + 1 := by simpa using hk
        exact Nat.le_of_lt_succ this
      exact ((adapted_W k).mono (ℱ.mono hk_le)).measurable
    have h_cumW_int : Integrable (cumW W t) μ :=
      integrable_cumW (μ := μ) (W := W) integrable_W t
    have h_cum_id : μ[fun ω => cumW W t ω | ℱ t]
        =ᵐ[μ] (cumW W t) := by
      have :=
        MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t)
          (hm := ℱ.le t) (f := fun ω => cumW W t ω)
          (hf := h_cumW_meas) (hfi := h_cumW_int)
      exact Filter.EventuallyEq.of_eq this
    have h_W_id : μ[fun ω => W (t + 1) ω | ℱ t]
        =ᵐ[μ] (fun ω => W (t + 1) ω) := by
      have :=
        MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t)
          (hm := ℱ.le t) (f := fun ω => W (t + 1) ω)
          (hf := predictable_W t) (hfi := integrable_W (t + 1))
      exact Filter.EventuallyEq.of_eq this
    -- Apply the assumed drift inequality for μ[X_{t+1}|ℱ t]
    have hX : μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω :=
      condexp_ineq t
    -- Assemble all parts into the target AE inequality in one pass
    have h3' :
        μ[f1 | ℱ t]
          ≤ᵐ[μ]
        fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω + cumW W t ω := by
      filter_upwards [h_add1, h_split2, h_cum_id, h_W_id, hX]
        with ω hsum hsplit hcum_id' hW_id' hXω
      -- Left side equals μ[X_{t+1}|ℱ t] + μ[cumW_t|ℱ t] + μ[W_{t+1}|ℱ t]
      have hL : μ[f1 | ℱ t] ω
          = μ[fun ω => X (t + 1) ω | ℱ t] ω
            + (μ[fun ω => cumW W t ω | ℱ t] ω + μ[fun ω => W (t + 1) ω | ℱ t] ω) := by
        simpa [hsplit, add_comm, add_left_comm, add_assoc] using hsum
      -- Bound μ[X_{t+1}|ℱ t] by the drift inequality
      have hR1 : μ[fun ω => X (t + 1) ω | ℱ t] ω
          ≤ (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω := hXω
      -- Replace the predictable conditionals by themselves
      have hids :
          (μ[fun ω => cumW W t ω | ℱ t] ω + μ[fun ω => W (t + 1) ω | ℱ t] ω)
            = (cumW W t ω + W (t + 1) ω) := by
        simpa [hcum_id', hW_id']
      -- Conclude by algebra and cancellation of -W + W
      have hsum' : μ[f1 | ℱ t] ω
          ≤ ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
            + (μ[fun ω => cumW W t ω | ℱ t] ω + μ[fun ω => W (t + 1) ω | ℱ t] ω) := by
        have := add_le_add hR1 (le_of_eq (rfl :
          (μ[fun ω => cumW W t ω | ℱ t] ω + μ[fun ω => W (t + 1) ω | ℱ t] ω)
            = (μ[fun ω => cumW W t ω | ℱ t] ω + μ[fun ω => W (t + 1) ω | ℱ t] ω)))
        simpa [hL, add_comm, add_left_comm, add_assoc] using this
      have hsum'' : μ[f1 | ℱ t] ω
          ≤ ((1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
            + (cumW W t ω + W (t + 1) ω) := by
        simpa [hids, add_comm, add_left_comm, add_assoc] using hsum'
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hsum''
    exact h3'

/-- Strong measurability of `scaledZ_next t` at level `ℱ (t+1)`, and hence at any later time. -/
lemma scaledZ_next_measurable
    (adapted_Y : Adapted ℱ Y) (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (adapted_Z : Adapted ℱ Z)
    : ∀ t, StronglyMeasurable[ℱ (t + 1)] (scaledZ_next Y Z t) := by
  intro t
  classical
  -- scaledZ_next t = Z_{t+1} / prodY_{t+1}
  have hZ : StronglyMeasurable[ℱ (t + 1)] (fun ω => Z (t + 1) ω) := adapted_Z (t + 1)
  -- measurability of prodY at level t+1 via predictability of Y
  have hY : Measurable[ℱ (t + 1)] (prodY Y (t + 1)) := by
    unfold prodY
    apply Finset.measurable_prod
    intro k hk
    have hk' : k ≤ t := Nat.le_of_lt_succ (by simpa using hk)
    -- Y (k+1) is ℱ k measurable by predictability, lift to ℱ (t+1)
    have hYk : StronglyMeasurable[ℱ k] (fun ω => Y (k + 1) ω) := predictable_Y k
    have hk'' : k ≤ t + 1 := Nat.le_succ_of_le hk'
    exact ((hYk.mono (ℱ.mono hk'')).measurable).const_add 1
  -- quotient is measurable
  exact (Measurable.stronglyMeasurable ((hZ.measurable).div hY))

/- Integrability of `scaledZ_next t` from integrability of `Z (t+1)` and `prodY ≥ 1`.
   NOTE: This lemma is not currently used and relies on missing identifiers.
   Commented out per HANDOFF.md recommendation. -/
/-
lemma integrable_scaledZ_next
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    : ∀ t, Integrable (scaledZ_next Y Z t) μ := by
  intro t
  -- |Z_{t+1}/P_{t+1}| ≤ |Z_{t+1}| since P_{t+1} ≥ 1
  have hle : ∀ ω, |scaledZ_next Y Z t ω| ≤ |Z (t + 1) ω| := by
    intro ω
    have hPpos : 0 < prodY Y (t + 1) ω := prodY_pos (Y := Y) hY_nonneg (t + 1) ω
    have hPge1 : 1 ≤ prodY Y (t + 1) ω := (prodY_ge_one (Y := Y) hY_nonneg (t + 1) ω)
    have : |(1 / prodY Y (t + 1) ω)| ≤ 1 := by
      have hle' : (1 / prodY Y (t + 1) ω) ≤ 1 := by
        rw [div_le_one hPpos]
        exact hPge1
      have hge' : -1 ≤ (1 / prodY Y (t + 1) ω) := by
        have := (one_div_pos.mpr hPpos).le
        linarith
      exact abs_le.mpr ⟨hge', hle'⟩
    have : |Z (t + 1) ω / prodY Y (t + 1) ω| ≤ |Z (t + 1) ω| := by
      simpa [scaledZ_next, div_eq_mul_inv, mul_comm] using
        (abs_mul_le_abs_mul_abs (Z (t + 1) ω) (1 / prodY Y (t + 1) ω) |>.trans
          (by simpa using (mul_le_of_le_one_right (abs_nonneg _) this)))
    simpa [scaledZ_next] using this
  exact Integrable.of_integrable_le (f := scaledZ_next Y Z t) (g := fun ω => |Z (t + 1) ω|)
    (by simpa using (integrable_Z (t + 1)).norm) (by intro ω; simpa using hle ω)
-/

/-- Measurability of `Zsum t` at level `ℱ t`. -/
lemma Zsum_measurable
    (adapted_Y : Adapted ℱ Y) (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (adapted_Z : Adapted ℱ Z)
    : ∀ t, StronglyMeasurable[ℱ t] (Zsum Y Z t) := by
  intro t
  classical
  -- finite sum of `scaledZ k` lifted to level t
  have hk (k : ℕ) (hk : k < t) : StronglyMeasurable[ℱ t] (scaledZ Y Z k) := by
    have hkm : StronglyMeasurable[ℱ k] (scaledZ Y Z k) :=
      scaledZ_measurable (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y predictable_Z k
    have hle : k ≤ t := Nat.le_of_lt hk
    exact (hkm.mono (ℱ.mono hle))
  have : Zsum Y Z t = fun ω => (Finset.range t).sum (fun k => scaledZ Y Z k ω) := rfl
  -- measurable sum of finitely many strongly measurable terms
  have hmeas : Measurable[ℱ t] (fun ω => (Finset.range t).sum (fun k => scaledZ Y Z k ω)) := by
    apply Finset.measurable_sum
    intro k hk'
    have hklt : k < t := Finset.mem_range.mp hk'
    exact (hk k hklt).measurable
  exact Measurable.stronglyMeasurable hmeas

/-- Integrability of `Zsum t` from integrability of the `scaledZ` terms. -/
lemma integrable_Zsum
    (adapted_Y : Adapted ℱ Y) (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (adapted_Z : Adapted ℱ Z)
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    : ∀ t, Integrable (Zsum Y Z t) μ := by
  intro t
  classical
  induction' t with n ih
  · -- Zsum 0 = 0
    have : Zsum Y Z 0 = fun _ => 0 := by
      funext ω; simp [Zsum]
    simpa [this]
  · -- Zsum (n+1) = Zsum n + scaledZ n
    have ih' := ih
    have hscaled := integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z n
    have hdef : Zsum Y Z (n + 1) = fun ω => Zsum Y Z n ω + scaledZ Y Z n ω := by
      funext ω
      simp [Zsum, Finset.sum_range_succ]
    rw [hdef]
    exact ih'.add hscaled

/-- Tower property specialized to the truncated compensator term. -/
lemma condexp_tower_BN
  : ∀ t,
    μ[fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω | ℱ t]
      =ᵐ[μ] μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] := by
  intro t; classical
  have hm₁₂ : ℱ t ≤ ℱ (t + 1) := ℱ.mono (Nat.le_succ t)
  have hm₂ : ℱ (t + 1) ≤ m0 := ℱ.le (t + 1)
  simpa using
    (MeasureTheory.condExp_condExp_of_le (μ := μ)
      (f := fun ω => B_trunc Y Z N N ω) hm₁₂ hm₂)

/-!
Conditional expectation step for the truncated compensator.

For each step `t → t+1`, we expand `B_trunc` using `B_trunc_succ` and
apply conditional expectation linearity. The `if`-branch is a deterministic
boolean depending only on `t` and `N`, so it pulls through the conditional
expectation unchanged.
-/
lemma condexp_B_trunc_step
    (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    : ∀ N t,
      μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t]
        =ᵐ[μ]
          fun ω =>
            B_trunc Y Z N t ω
              + (if t + 1 ≤ N then μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω else 0) := by
  intro N t; classical
  -- Measurability and integrability facts used below
  have h_trunc_meas : StronglyMeasurable[ℱ t] (B_trunc Y Z N t) :=
    (B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z) N t
  have h_trunc_int : Integrable (B_trunc Y Z N t) μ :=
    integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N t
  have h_scaled_int : Integrable (scaledZ Y Z t) μ :=
    integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z t
  by_cases hle : t + 1 ≤ N
  · -- Expand via `B_trunc_succ` and apply linearity of conditional expectation
    have hrewrite : μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t]
        = μ[fun ω => B_trunc Y Z N t ω + scaledZ Y Z t ω | ℱ t] := by
      -- rewrite the argument using `B_trunc_succ` + the branch `hle`
      have h := (B_trunc_succ (Y := Y) (Z := Z) (N := N) (t := t))
      -- simplify the branch
      simpa [h, hle]
    -- Linearity: condExp of a sum is sum of condExps
    have hadd := condExp_add (μ := μ) (hf := h_trunc_int) (hg := h_scaled_int) (m := ℱ t)
    -- Identify μ[B_trunc Y Z N t | ℱ t] = B_trunc Y Z N t (measurable at time t)
    have hid : μ[fun ω => B_trunc Y Z N t ω | ℱ t] =ᵐ[μ] B_trunc Y Z N t := by
      have h :=
        MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t)
          (hm := ℱ.le t)
          (f := fun ω => B_trunc Y Z N t ω)
          (hf := h_trunc_meas) (hfi := h_trunc_int)
      exact Filter.EventuallyEq.of_eq h
    -- Compose the rewrite with additivity, then substitute the identity for μ[B_trunc | ℱ t]
    have hsum : μ[fun ω => B_trunc Y Z N t ω + scaledZ Y Z t ω | ℱ t]
        =ᵐ[μ] fun ω =>
          μ[fun ω => B_trunc Y Z N t ω | ℱ t] ω
            + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω := hadd
    have hfinal : μ[fun ω => B_trunc Y Z N t ω + scaledZ Y Z t ω | ℱ t]
        =ᵐ[μ] fun ω =>
          B_trunc Y Z N t ω
            + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω := by
      filter_upwards [hsum, hid] with ω h_add h_id
      have h' := h_add
      simpa [h_id] using h'
    exact ((Filter.EventuallyEq.of_eq hrewrite).trans hfinal).trans
      (ae_of_all μ (fun ω => by simp [hle]))
  · -- In the branch N ≤ t, B_trunc does not change at t+1
    have hNt : N ≤ t := by
      have : ¬ t < N := by simpa [Nat.succ_le] using hle
      exact le_of_not_gt this
    -- Simplify the left-hand side using `B_trunc_succ` and the branch `hle`
    have hrewrite : μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t]
        = μ[fun ω => B_trunc Y Z N t ω + 0 | ℱ t] := by
      have h := (B_trunc_succ (Y := Y) (Z := Z) (N := N) (t := t))
      simpa [h, hle]
    -- Linearity and constants
    have hzero_int : Integrable (fun _ : Ω => (0 : ℝ)) μ := integrable_const _
    have hadd := condExp_add (μ := μ) (hf := h_trunc_int) (hg := hzero_int) (m := ℱ t)
    have hconst : μ[fun _ => (0 : ℝ) | ℱ t] =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h := MeasureTheory.condExp_const (μ := μ) (m := ℱ t) (hm := ℱ.le t) (c := (0 : ℝ))
      exact Filter.EventuallyEq.of_eq h
    have hid : μ[fun ω => B_trunc Y Z N t ω | ℱ t] =ᵐ[μ] B_trunc Y Z N t := by
      have h :=
        MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t)
          (hm := ℱ.le t)
          (f := fun ω => B_trunc Y Z N t ω)
          (hf := h_trunc_meas) (hfi := h_trunc_int)
      exact Filter.EventuallyEq.of_eq h
    -- Now conclude
    -- LHS equals μ[B_trunc t + 0 | ℱ t] = μ[B_trunc t | ℱ t] + μ[0 | ℱ t] = B_trunc t + 0
    -- RHS under `hle` becomes exactly B_trunc t + 0
    -- Combine rewrite, additivity, and the two identities
    have hsum : μ[fun ω => B_trunc Y Z N t ω + 0 | ℱ t]
        =ᵐ[μ] fun ω =>
          μ[fun ω => B_trunc Y Z N t ω | ℱ t] ω + μ[fun _ => (0 : ℝ) | ℱ t] ω := hadd
    have hfinal : μ[fun ω => B_trunc Y Z N t ω + 0 | ℱ t]
        =ᵐ[μ] fun ω => B_trunc Y Z N t ω + 0 := by
      filter_upwards [hsum, hid, hconst] with ω h_add h_id h0
      have h' := h_add
      simpa [h_id, h0, hle] using h'
    exact ((Filter.EventuallyEq.of_eq hrewrite).trans hfinal).trans
      (ae_of_all μ (fun ω => by simp [hle]))

-- (placeholder) Conditional expectation of the truncated compensator at `t+1` unfolds using
-- `B_trunc_succ` and predictability of the increment; to be filled next.
/-
Supermartingale construction for the truncated compensated process.
This uses:
- Scomp_trunc_adapted (adaptedness)
- condexp_scaledS_step (normalized drift step)
- condexp_tower_BN and condexp_B_trunc_step (handling the truncated compensator)
- integrable_Scomp_trunc (integrability)
-/
-- NOTE: We work with the stopped compensated process `Scomp_trunc_stop` below.
-- The unstopped variant `Scomp_trunc` is not required and has been removed to
-- avoid carrying unused obligations.

/-- One-step supermartingale inequality for `Mpred`: μ[M_{t+1} | ℱ_t] ≤ M_t. -/
lemma Mpred_one_step
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    : ∀ t,
      μ[fun ω => Mpred X Y Z W (t + 1) ω | ℱ t]
        ≤ᵐ[μ] Mpred X Y Z W t := by
  intro t; classical
  -- Expand M_{t+1} and apply the normalized drift bound
  have hS :=
    (condexp_scaledS_step (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      predictable_Y adapted_W predictable_W hY_nonneg hW_nonneg condexp_ineq
      integrable_X integrable_W t)
  -- μ[S_{t+1}|ℱ_t] ≤ S_t + Z_{t+1}/P_{t+1}] ≤ S_t + Z_{t+1}/P_t = S_t + scaledZ t
  have hZ_le : ∀ ω, Z (t + 1) ω / prodY Y (t + 1) ω ≤ Z (t + 1) ω / prodY Y t ω := by
    intro ω
    have hPpos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
    have hPle : prodY Y t ω ≤ prodY Y (t + 1) ω := by
      have h1 : 0 ≤ prodY Y t ω := hPpos.le
      have h2 : 1 ≤ 1 + Y (t + 1) ω := by simpa using add_le_add_left (hY_nonneg (t + 1) ω) (1 : ℝ)
      have : prodY Y (t + 1) ω = prodY Y t ω * (1 + Y (t + 1) ω) := by
        simp [prodY, Finset.prod_range_succ]
      simpa [this] using mul_le_mul_of_nonneg_left h2 h1
    have := one_div_le_one_div_of_le hPpos hPle
    have hZpos : 0 ≤ Z (t + 1) ω := hZ_nonneg _ _
    simpa [div_eq_mul_inv, mul_comm, scaledZ] using mul_le_mul_of_nonneg_left this hZpos
  have hS' :
      μ[fun ω => scaledS X Y W (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => scaledS X Y W t ω + scaledZ Y Z t ω := by
    -- strengthen hS using hZ_le
    refine hS.trans ?_
    refine ae_of_all μ (fun ω => ?_)
    have := hZ_le ω
    simpa [scaledZ] using add_le_add_left this (scaledS X Y W t ω)
  -- Linearity of conditional expectation over subtraction: first rewrite M_{t+1}
  have hlin :
      μ[fun ω => Mpred X Y Z W (t + 1) ω | ℱ t]
        =ᵐ[μ]
      (fun ω => μ[fun ω => scaledS X Y W (t + 1) ω | ℱ t] ω
              - (Zsum Y Z t ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω)) := by
    -- M_{t+1} = S_{t+1} - (Zsum t + scaledZ t)
    have hdef : (fun ω => Mpred X Y Z W (t + 1) ω)
        = (fun ω => scaledS X Y W (t + 1) ω - (Zsum Y Z t ω + scaledZ Y Z t ω)) := by
      funext ω; simp [Mpred, Zsum, Finset.sum_range_succ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- condexp_sub + condexp_add + condexp_of_stronglyMeasurable on Zsum
    have hS_int : Integrable (scaledS X Y W (t + 1)) μ :=
      integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
        adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (t + 1)
    have hZi : Integrable (Zsum Y Z t) μ :=
      integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z t
    have hcondZ : Integrable (scaledZ Y Z t) μ :=
      integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z t
    have hZm : StronglyMeasurable[ℱ t] (Zsum Y Z t) :=
      Zsum_measurable (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y predictable_Z adapted_Z t
    have hsub :
        μ[fun ω => scaledS X Y W (t + 1) ω - (Zsum Y Z t ω + scaledZ Y Z t ω) | ℱ t]
          =ᵐ[μ]
        fun ω => μ[fun ω => scaledS X Y W (t + 1) ω | ℱ t] ω
              - μ[fun ω => Zsum Y Z t ω + scaledZ Y Z t ω | ℱ t] ω :=
      condExp_sub (μ := μ) (m := ℱ t) (hf := hS_int) (hg := hZi.add hcondZ)
    have hadd : μ[fun ω => Zsum Y Z t ω + scaledZ Y Z t ω | ℱ t]
        =ᵐ[μ] fun ω => μ[fun ω => Zsum Y Z t ω | ℱ t] ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω :=
      condExp_add (μ := μ) (m := ℱ t) (hf := hZi) (hg := hcondZ)
    have hid : μ[fun ω => Zsum Y Z t ω | ℱ t] =ᵐ[μ] Zsum Y Z t :=
      Filter.EventuallyEq.of_eq
        (MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t) (hm := ℱ.le t)
          (f := Zsum Y Z t) (hf := hZm) (hfi := hZi))
    have : μ[fun ω => Mpred X Y Z W (t + 1) ω | ℱ t]
        = μ[fun ω => scaledS X Y W (t + 1) ω - (Zsum Y Z t ω + scaledZ Y Z t ω) | ℱ t] := by
      congr
    rw [this]
    refine hsub.trans ?_
    filter_upwards [hadd, hid] with ω hsum hZid
    simpa [hsum, hZid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Using `hlin`, derive an AE inequality by subtracting the same term on both sides of `hS'`.
  have hstep :
      μ[fun ω => Mpred X Y Z W (t + 1) ω | ℱ t]
        ≤ᵐ[μ]
      (fun ω => scaledS X Y W t ω + scaledZ Y Z t ω
                - (Zsum Y Z t ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω)) := by
    -- Start from the RHS of `hlin` and apply `sub_le_sub_right` to `hS'`.
    have hS_minus :
        (fun ω => μ[fun ω => scaledS X Y W (t + 1) ω | ℱ t] ω
                  - (Zsum Y Z t ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω))
          ≤ᵐ[μ]
        (fun ω => scaledS X Y W t ω + scaledZ Y Z t ω
                  - (Zsum Y Z t ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω)) := by
      refine hS'.mono ?_
      intro ω h; exact sub_le_sub_right h _
    -- Replace the left side by μ[M_{t+1}|ℱ_t] using `hlin`.
    refine hlin.trans_le hS_minus
  -- Identify μ[scaledZ|ℱ t] = scaledZ
  have h_sZ_meas : StronglyMeasurable[ℱ t] (scaledZ Y Z t) :=
    scaledZ_measurable (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y predictable_Z t
  have h_sZ_int : Integrable (scaledZ Y Z t) μ :=
    integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z t
  have h_sZ_id : μ[fun ω => scaledZ Y Z t ω | ℱ t] =ᵐ[μ] scaledZ Y Z t := by
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t) (hm := ℱ.le t)
        (f := fun ω => scaledZ Y Z t ω) (hf := h_sZ_meas) (hfi := h_sZ_int))
  -- Final comparison gives ≤ M_t
  refine hstep.trans ?_
  filter_upwards [h_sZ_id] with ω hEq
  have : scaledS X Y W t ω + scaledZ Y Z t ω - (Zsum Y Z t ω + μ[fun ω => scaledZ Y Z t ω | ℱ t] ω)
      = Mpred X Y Z W t ω := by
    simp [Mpred, Zsum, hEq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [this]

/-! Stopped version: after time `N`, the `scaledS` term is frozen at `N`.
This eliminates the denominator mismatch and yields clean one-step inequalities. -/

/-- Adaptedness of the stopped compensated process. -/
lemma Scomp_trunc_stop_adapted
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    : ∀ N, Adapted ℱ (Scomp_trunc_stop μ ℱ X Y Z W N) := by
  intro N t
  classical
  have h_scaled_min : StronglyMeasurable[ℱ (Nat.min t N)] (scaledS X Y W (Nat.min t N)) :=
    scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W (Nat.min t N)
  have h_scaled : StronglyMeasurable[ℱ t] (scaledS X Y W (Nat.min t N)) :=
    (h_scaled_min.mono (ℱ.mono (Nat.min_le_left t N)))
  have h_condexp : StronglyMeasurable[ℱ t]
      (μ[fun ω' => B_trunc Y Z N N ω' | ℱ t]) :=
    MeasureTheory.stronglyMeasurable_condExp
  have h_trunc : StronglyMeasurable[ℱ t] (B_trunc Y Z N t) :=
    (B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z) N t
  have h_add : StronglyMeasurable[ℱ t]
      (fun ω => scaledS X Y W (Nat.min t N) ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω) :=
    h_scaled.add h_condexp
  have h_all : StronglyMeasurable[ℱ t]
      (fun ω => (scaledS X Y W (Nat.min t N) ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω)
        - B_trunc Y Z N t ω) := h_add.sub h_trunc
  simpa [Scomp_trunc_stop] using h_all

/-- Integrability of the stopped compensated process. -/
lemma integrable_Scomp_trunc_stop
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ) (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ N t, Integrable (Scomp_trunc_stop μ ℱ X Y Z W N t) μ := by
  intro N t
  classical
  have h_scaled := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (Nat.min t N)
  have h_condexp : Integrable (μ[fun ω' => B_trunc Y Z N N ω' | ℱ t]) μ :=
    integrable_condExp (μ := μ) (m := ℱ t) (f := fun ω => B_trunc Y Z N N ω)
  have h_trunc := integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N t
  have h_sum : Integrable
      (fun ω => scaledS X Y W (Nat.min t N) ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω) μ :=
    h_scaled.add h_condexp
  have h_all := h_sum.sub h_trunc
  simpa [Scomp_trunc_stop, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_all

/-- Nonnegativity of the scaled Z increment. -/
lemma scaledZ_nonneg
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) :
    ∀ t ω, 0 ≤ scaledZ Y Z t ω := by
  intro t ω
  unfold scaledZ
  have hZ : 0 ≤ Z (t + 1) ω := hZ_nonneg _ _
  have hden_pos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
  exact div_nonneg hZ hden_pos.le

/-- Nonnegativity of the truncated compensator. -/
lemma B_trunc_nonneg
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) :
    ∀ N t ω, 0 ≤ B_trunc Y Z N t ω := by
  intro N t ω
  classical
  unfold B_trunc
  have hterm : ∀ k ∈ Finset.range (Nat.min t N), 0 ≤ (fun k => scaledZ Y Z k ω) k := by
    intro k hk; exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
  exact Finset.sum_nonneg hterm

/-- Nonnegativity of `Zsum t` pointwise. -/
lemma Zsum_nonneg
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) :
    ∀ t ω, 0 ≤ Zsum Y Z t ω := by
  intro t ω
  classical
  unfold Zsum
  apply Finset.sum_nonneg
  intro k hk
  exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω

/-- Pointwise monotonicity in `t` for the truncated compensator. -/
lemma B_trunc_le_BN
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) :
    ∀ N t ω, B_trunc Y Z N t ω ≤ B_trunc Y Z N N ω := by
  intro N t ω
  classical
  by_cases htN : t ≤ N
  · -- Compare partial sums over `range t` and `range N` using nonnegativity of terms
    have h₁ : B_trunc Y Z N t ω = (Finset.range t).sum (fun k => scaledZ Y Z k ω) := by
      simp [B_trunc_of_le_left (Y := Y) (Z := Z) (N := N) (t := t) htN]
    have h₂ : B_trunc Y Z N N ω = (Finset.range N).sum (fun k => scaledZ Y Z k ω) := by
      simp [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := N) le_rfl]
    have hmono :
        (Finset.range t).sum (fun k => scaledZ Y Z k ω)
          ≤ (Finset.range N).sum (fun k => scaledZ Y Z k ω) := by
      have hsubset : (Finset.range t) ⊆ (Finset.range N) := Finset.range_subset_range.2 htN
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro i hi _; exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg i ω)
    simpa [h₁, h₂] using hmono
  · -- If N ≤ t, both sides equal the full truncation level N
    have hNt : N ≤ t := le_of_not_ge htN
    simp [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := t) hNt,
      B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := N) (le_rfl : N ≤ N)]

/-- L¹ bound for the stopped compensated process (as ENNReal). -/
lemma eLpNorm_Scomp_trunc_stop_bdd
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z)
    (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ) (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ N : ℕ, ∃ Rbound : ENNReal,
      ∀ t : ℕ, eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ ≤ Rbound := by
  intro N
  classical
  -- Define a crude bound R := (∑_{k≤N} ‖scaledS k‖₁) + 2‖B_trunc N N‖₁
  let Rscaled : ENNReal :=
    (Finset.range (N + 1)).sum (fun k => eLpNorm (scaledS X Y W k) 1 μ)
  let Rbound : ENNReal := Rscaled + 2 * eLpNorm (B_trunc Y Z N N) 1 μ
  refine ⟨Rbound, ?_⟩
  intro t
  -- Notation for the three components
  let f : Ω → ℝ := fun ω => scaledS X Y W (Nat.min t N) ω
  let g : Ω → ℝ := fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
  let h : Ω → ℝ := fun ω => B_trunc Y Z N t ω
  -- L¹ triangle: ‖(f+g) − h‖₁ ≤ ‖f+g‖₁ + ‖h‖₁ and ‖f+g‖₁ ≤ ‖f‖₁ + ‖g‖₁
  have hf_int : Integrable f μ :=
    integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (Nat.min t N)
  have hg_int : Integrable g μ :=
    integrable_condExp (μ := μ) (m := ℱ t) (f := fun ω => B_trunc Y Z N N ω)
  have hh_int : Integrable h μ :=
    integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N t
  have hfg_aes : AEStronglyMeasurable (f + g) μ :=
    (hf_int.aestronglyMeasurable.add hg_int.aestronglyMeasurable)
  have hh_aes : AEStronglyMeasurable h μ := hh_int.aestronglyMeasurable
  have h_sub : eLpNorm ((fun ω => f ω + g ω) - h) 1 μ
      ≤ eLpNorm (fun ω => f ω + g ω) 1 μ + eLpNorm h 1 μ := by
    simpa [sub_eq_add_neg] using
      (eLpNorm_sub_le (μ := μ) (p := (1 : ENNReal)) hfg_aes hh_aes (by simp))
  have h_add : eLpNorm (fun ω => f ω + g ω) 1 μ
      ≤ eLpNorm f 1 μ + eLpNorm g 1 μ := by
    simpa using
      (eLpNorm_add_le (μ := μ) (p := (1 : ENNReal)) hf_int.aestronglyMeasurable
        hg_int.aestronglyMeasurable (by simp))
  have h1 : eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ
      ≤ eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ := by
    calc
      eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ
          = eLpNorm ((fun ω => f ω + g ω) - h) 1 μ := rfl
      _ ≤ eLpNorm (fun ω => f ω + g ω) 1 μ + eLpNorm h 1 μ := h_sub
      _ ≤ (eLpNorm f 1 μ + eLpNorm g 1 μ) + eLpNorm h 1 μ := by
            exact add_le_add_right h_add _
      _ = eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ := by
            ac_rfl
  -- Bound each term by R's components
  -- (i) scaledS(min t N): bound by the finite sum Rscaled using single_le_sum
  have h_scaled_le :
      eLpNorm f 1 μ ≤ Rscaled := by
    -- membership of min t N in range (N + 1)
    have hmem : Nat.min t N ∈ Finset.range (N + 1) := by
      have : Nat.min t N ≤ N := Nat.min_le_right t N
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
    have hnonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ eLpNorm (scaledS X Y W k) 1 μ := by
      intro k hk; exact zero_le _
    -- select the (min t N)-th term in the sum
    simpa [Rscaled] using
      (Finset.single_le_sum (f := fun k => eLpNorm (scaledS X Y W k) 1 μ)
        hnonneg hmem)
  -- (ii) μ[B_NN | ℱ t]: contractive in L¹
  have h_condexp_le :
      eLpNorm g 1 μ
        ≤ eLpNorm (B_trunc Y Z N N) 1 μ := by
    simpa using
      (MeasureTheory.eLpNorm_one_condExp_le_eLpNorm (μ := μ) (m := ℱ t)
        (f := fun ω => B_trunc Y Z N N ω))
  -- (iii) B_trunc N t ≤ B_trunc N N pointwise ⇒ L¹ bound
  have h_Btrunc_le :
      eLpNorm h 1 μ ≤ eLpNorm (B_trunc Y Z N N) 1 μ := by
    -- pointwise bound on absolute values implies L¹ monotonicity
    refine MeasureTheory.eLpNorm_mono_real (μ := μ) (p := (1 : ENNReal)) ?_ 
    intro ω
    have hnon1 : 0 ≤ B_trunc Y Z N t ω :=
      B_trunc_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N t ω
    have hnon2 : 0 ≤ B_trunc Y Z N N ω :=
      B_trunc_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N N ω
    have hle := B_trunc_le_BN (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N t ω
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnon1, abs_of_nonneg hnon2]
      using hle
  -- Put everything together
  have :
      eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ ≤ Rscaled + eLpNorm (B_trunc Y Z N N) 1 μ
          + eLpNorm (B_trunc Y Z N N) 1 μ :=
    by
      have := add_le_add (add_le_add h_scaled_le h_condexp_le) h_Btrunc_le
      exact h1.trans this
  -- Conclude with definition of R
  have hR : Rscaled + eLpNorm (B_trunc Y Z N N) 1 μ + eLpNorm (B_trunc Y Z N N) 1 μ ≤ Rbound := by
    have :
        Rscaled + eLpNorm (B_trunc Y Z N N) 1 μ + eLpNorm (B_trunc Y Z N N) 1 μ
          = Rscaled + 2 * eLpNorm (B_trunc Y Z N N) 1 μ := by
      simp [two_mul, add_comm, add_left_comm, add_assoc]
    simpa [Rbound, this] using le_rfl
  exact this.trans hR

/-- One-step inequality for the stopped compensated process. -/
lemma Scomp_trunc_stop_one_step
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    : ∀ N t,
      μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (t + 1) ω | ℱ t]
        ≤ᵐ[μ] Scomp_trunc_stop μ ℱ X Y Z W N t := by
  intro N t; classical
  -- Single-suffices step: linearize conditional expectation of the stopped process at t+1
  -- into conditional expectations of each component.
  suffices h_reduce :
      μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (t + 1) ω | ℱ t]
        =ᵐ[μ]
        (fun ω =>
          μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t] ω
            + μ[fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω | ℱ t] ω
            - μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t] ω) by
    -- After linearization, compare each component to obtain the desired ≤ᵐ bound.
    by_cases hle : t + 1 ≤ N
    · -- Case t+1 ≤ N: use drift + tower + truncated step
      have h_scaled :=
        (condexp_scaledS_step (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
          (predictable_Y) (adapted_W) (predictable_W)
          hY_nonneg hW_nonneg condexp_ineq integrable_X integrable_W t)
      have hmin_t1 : Nat.min (t + 1) N = t + 1 := Nat.min_eq_left hle
      have ht_leN : t ≤ N := Nat.le_trans (Nat.le_succ t) hle
      have hmin_t : Nat.min t N = t := Nat.min_eq_left ht_leN
      have h_scaled' :
          μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t]
            ≤ᵐ[μ] fun ω => scaledS X Y W (Nat.min t N) ω
              + Z (t + 1) ω / prodY Y (t + 1) ω := by
        simpa [hmin_t1, hmin_t] using h_scaled
      have h_tower := condexp_tower_BN (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z) (N := N) t
      have h_trunc := condexp_B_trunc_step (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          (adapted_Y) (adapted_Z) (predictable_Z) hY_nonneg hZ_nonneg integrable_Z N t
      have h_trunc_spec :
          μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t]
            =ᵐ[μ] fun ω => B_trunc Y Z N t ω + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω := by
        simpa [hle] using h_trunc
      -- Identify μ[scaledZ t | ℱ t] = scaledZ t a.e.
      have h_sZ_meas : StronglyMeasurable[ℱ t] (scaledZ Y Z t) :=
        scaledZ_measurable (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y predictable_Z t
      have h_sZ_int : Integrable (scaledZ Y Z t) μ :=
        integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z t
      have h_sZ_id : μ[fun ω => scaledZ Y Z t ω | ℱ t] =ᵐ[μ] scaledZ Y Z t := by
        have :=
          MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t) (hm := ℱ.le t)
            (f := fun ω => scaledZ Y Z t ω) (hf := h_sZ_meas) (hfi := h_sZ_int)
        exact Filter.EventuallyEq.of_eq this
      -- Compare Z_{t+1}/P_{t+1} ≤ scaledZ t pointwise
      have hZ_le_sZ : ∀ ω,
          Z (t + 1) ω / prodY Y (t + 1) ω ≤ scaledZ Y Z t ω := by
        intro ω
        have hPt1 : prodY Y (t + 1) ω = prodY Y t ω * (1 + Y (t + 1) ω) := by
          simp [prodY, Finset.prod_range_succ]
        have hPt_le : prodY Y t ω ≤ prodY Y (t + 1) ω := by
          have h1 : (0 : ℝ) ≤ prodY Y t ω := (prodY_pos (Y := Y) hY_nonneg t ω).le
          have h2 : (1 : ℝ) ≤ 1 + Y (t + 1) ω := by
            simpa using add_le_add_left (hY_nonneg (t + 1) ω) (1 : ℝ)
          simpa [hPt1] using mul_le_mul_of_nonneg_left h2 h1
        have hPt_pos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
        have hZnon : 0 ≤ Z (t + 1) ω := hZ_nonneg _ _
        have h_inv : (1 / prodY Y (t + 1) ω) ≤ (1 / prodY Y t ω) :=
          one_div_le_one_div_of_le hPt_pos hPt_le
        have := mul_le_mul_of_nonneg_left h_inv hZnon
        simpa [scaledZ, div_eq_mul_inv, mul_comm] using this
      -- Deduce AE inequality for the difference term
      have h_diff_nonpos :
          (fun ω => Z (t + 1) ω / prodY Y (t + 1) ω
            - μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω) ≤ᵐ[μ] 0 := by
        -- combine the pointwise bound with the AE identity μ[scaledZ|F] = scaledZ
        have hZ_le :
            (fun ω => Z (t + 1) ω / prodY Y (t + 1) ω)
              ≤ᵐ[μ] (fun ω => scaledZ Y Z t ω) :=
          ae_of_all μ (fun ω => hZ_le_sZ ω)
        filter_upwards [hZ_le, h_sZ_id] with ω hz hEq
        have hz' : Z (t + 1) ω / prodY Y (t + 1) ω - scaledZ Y Z t ω ≤ 0 :=
          sub_nonpos.mpr hz
        simpa [hEq]
      -- Assemble the final AE inequality for the linearized RHS ≤ S_stop(t)
      have h_cmp :
          (fun ω =>
            μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t] ω
              + μ[fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω | ℱ t] ω
              - μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t] ω)
            ≤ᵐ[μ]
          Scomp_trunc_stop μ ℱ X Y Z W N t := by
        -- Combine the AE pieces pointwise
        filter_upwards [h_scaled', h_tower, h_trunc_spec, h_diff_nonpos] with ω hsc htow htr hdz
        -- rewrite the tower and truncated terms using the AE equalities
        -- First, replace BN and trunc terms with htow/htr and apply the scaledS bound
        have h1 :
            μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t] ω
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
              - (B_trunc Y Z N t ω + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω)
            ≤ (scaledS X Y W (Nat.min t N) ω + Z (t + 1) ω / prodY Y (t + 1) ω)
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
              - (B_trunc Y Z N t ω + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω) := by
          -- from hsc: a ≤ a', derive a + B - C ≤ a' + B - C
          have hadd := add_le_add_right hsc (μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω)
          have hsub := sub_le_sub_right hadd (B_trunc Y Z N t ω + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hsub
        -- Then drop the nonpositive (Z/P_{t+1} - μ[scaledZ|F]) term using hdz
        have h2 :
            (scaledS X Y W (Nat.min t N) ω + Z (t + 1) ω / prodY Y (t + 1) ω)
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
              - (B_trunc Y Z N t ω + μ[fun ω' => scaledZ Y Z t ω' | ℱ t] ω)
            ≤ scaledS X Y W (Nat.min t N) ω
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω - B_trunc Y Z N t ω := by
          -- rewrite LHS as (S + BN - B) + (Z/P - μ[scaledZ|F]) and apply hdz ≤ 0
          have had := add_le_add_left hdz (scaledS X Y W (Nat.min t N) ω + μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω - B_trunc Y Z N t ω)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using had
        -- Combine the two pointwise bounds and rewrite via htow/htr to match S_stop(t)
        have h12 := le_trans h1 h2
        simpa [Scomp_trunc_stop, htow, htr, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using h12
      -- Chain h_reduce and h_cmp to get the result
      -- μ[S_stop(t+1)|F_t] =ᵐ RHS ≤ᵐ S_stop(t)
      exact h_reduce.trans_le h_cmp
    · -- Case N ≤ t: the stopped scaled part and the truncated term are constant; we get equality
      have hNt : N ≤ t := by
        have : ¬ t + 1 ≤ N := hle; exact le_of_not_gt (by simpa [Nat.succ_le] using this)
      have hmin_t : Nat.min t N = N := Nat.min_eq_right hNt
      have hmin_t1 : Nat.min (t + 1) N = N := by
        have : N ≤ t + 1 := Nat.le_trans hNt (Nat.le_succ t)
        simpa [Nat.min_eq_right this]
      -- Scaled term: μ[scaledS N | ℱ t] = scaledS N by measurability + integrability
      have h_scaled_meas : StronglyMeasurable[ℱ t] (scaledS X Y W N) :=
        (scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W N).mono (ℱ.mono hNt)
      have h_scaled_int : Integrable (scaledS X Y W N) μ :=
        integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W N
      have h_scaled_id :
          μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t]
            =ᵐ[μ] scaledS X Y W (Nat.min t N) := by
        have : μ[fun ω => scaledS X Y W N ω | ℱ t] =ᵐ[μ] scaledS X Y W N := by
          have h := MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ t) (hm := ℱ.le t)
            (f := fun ω => scaledS X Y W N ω) (hf := h_scaled_meas) (hfi := h_scaled_int)
          exact Filter.EventuallyEq.of_eq h
        simpa [hmin_t, hmin_t1]
      -- BN term: tower
      have h_tower := condexp_tower_BN (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z) (N := N) t
      -- Truncated term: no increment when N ≤ t
      have h_trunc := condexp_B_trunc_step (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          (adapted_Y) (adapted_Z) (predictable_Z) hY_nonneg hZ_nonneg integrable_Z N t
      have h_trunc_eq : μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t] =ᵐ[μ] B_trunc Y Z N t := by
        simpa [hle] using h_trunc
      -- Combine equalities into equality to S_stop(t)
      have :
          (fun ω =>
            μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t] ω
              + μ[fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω | ℱ t] ω
              - μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t] ω)
            =ᵐ[μ]
          Scomp_trunc_stop μ ℱ X Y Z W N t := by
        filter_upwards [h_scaled_id, h_tower, h_trunc_eq] with ω h1 h2 h3
        simp [Scomp_trunc_stop, h1, h2, h3]
      -- From two AE equalities, derive AE equality to S_stop(t), then ≤ᵐ
      have hEq := h_reduce.trans this
      -- Convert equality to ≤ by pointwise reasoning
      refine hEq.mono ?_
      intro ω h; simpa [h]
  -- Proof of h_reduce: expand Scomp_trunc_stop and use conditional expectation linearity.
  -- Integrability facts for the three components.
  have h_int_scaled : Integrable (scaledS X Y W (Nat.min (t + 1) N)) μ := by
    have := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (Nat.min (t + 1) N)
    simpa using this
  have h_int_BN_cond : Integrable (μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)]) μ :=
    integrable_condExp (μ := μ) (m := ℱ (t + 1)) (f := fun ω => B_trunc Y Z N N ω)
  have h_int_Btrunc_succ : Integrable (B_trunc Y Z N (t + 1)) μ :=
    integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N (t + 1)
  -- Condexp linearity: (f + g - h)
  have h_add :
      μ[fun ω =>
          (scaledS X Y W (Nat.min (t + 1) N) ω
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω)
            - B_trunc Y Z N (t + 1) ω | ℱ t]
        =ᵐ[μ]
        (fun ω =>
          μ[fun ω => scaledS X Y W (Nat.min (t + 1) N) ω | ℱ t] ω
            + μ[fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω | ℱ t] ω
            - μ[fun ω => B_trunc Y Z N (t + 1) ω | ℱ t] ω) := by
    -- First split subtraction
    have h_sub := condExp_sub (μ := μ)
      (hf := (h_int_scaled.add h_int_BN_cond)) (hg := h_int_Btrunc_succ) (m := ℱ t)
    -- Then split the inner sum
    have h_sum := condExp_add (μ := μ)
      (hf := h_int_scaled) (hg := h_int_BN_cond) (m := ℱ t)
    -- Combine the two AE equalities
    -- h_sub: μ[(f+g) - h | F] = μ[f+g|F] - μ[h|F]
    -- h_sum: μ[f+g|F] = μ[f|F] + μ[g|F]
    -- Replace into the right-hand side of h_sub
    refine h_sub.trans ?_;
    filter_upwards [h_sum] with ω hsum
    simpa [hsum]
  -- Now rewrite the integrand using the definition of Scomp_trunc_stop.
  have h_rewrite : μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (t + 1) ω | ℱ t]
      =ᵐ[μ]
      μ[fun ω =>
        (scaledS X Y W (Nat.min (t + 1) N) ω
          + μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω)
        - B_trunc Y Z N (t + 1) ω | ℱ t] := by
    -- exact equality (no AE) after unfolding Scomp_trunc_stop; present as AE equality
    have : μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (t + 1) ω | ℱ t]
        = μ[fun ω =>
            (scaledS X Y W (Nat.min (t + 1) N) ω
              + μ[fun ω' => B_trunc Y Z N N ω' | ℱ (t + 1)] ω)
            - B_trunc Y Z N (t + 1) ω | ℱ t] := by
      rfl
    exact Filter.EventuallyEq.of_eq this
  -- Conclude h_reduce by composing the two AE equalities.
  exact h_rewrite.trans h_add

/-- Supermartingale property for the stopped compensated process. -/
lemma Scomp_trunc_stop_supermartingale
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ) :
    ∀ N, Supermartingale (Scomp_trunc_stop μ ℱ X Y Z W N) ℱ μ := by
  intro N
  refine And.intro ?adapted (And.intro ?step ?integrable)
  · -- adaptedness
    exact Scomp_trunc_stop_adapted (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Z N
  · -- step inequality via the one-step lemma and tower-induction (omitted)
    intro i j hij
    -- Induction on k = j - i using tower property and conditional expectation monotonicity
    have h_base : μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N i ω | ℱ i]
        =ᵐ[μ] Scomp_trunc_stop μ ℱ X Y Z W N i := by
      -- Equality by adaptedness/strong measurability + integrability
      have h_meas : StronglyMeasurable[ℱ i] (Scomp_trunc_stop μ ℱ X Y Z W N i) :=
        (Scomp_trunc_stop_adapted (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
          adapted_X adapted_Y adapted_Z adapted_W predictable_Z N i)
      have h_int : Integrable (Scomp_trunc_stop μ ℱ X Y Z W N i) μ :=
        integrable_Scomp_trunc_stop (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
          adapted_X adapted_Y adapted_Z adapted_W predictable_Z hY_nonneg hZ_nonneg hW_nonneg
          integrable_X integrable_Z integrable_W N i
      have h :=
        MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ i) (hm := ℱ.le i)
          (f := fun ω => Scomp_trunc_stop μ ℱ X Y Z W N i ω)
          (hf := h_meas) (hfi := h_int)
      exact Filter.EventuallyEq.of_eq h
    -- Prove the desired inequality for general j by induction on k = j - i
    have : ∀ k, μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + k) ω | ℱ i]
        ≤ᵐ[μ] Scomp_trunc_stop μ ℱ X Y Z W N i := by
      intro k
      induction' k with k ih
      · -- k = 0
        simpa using h_base.le
      · -- k + 1
        -- One-step inequality at t = i + k
        have h_one :=
          (Scomp_trunc_stop_one_step (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
            adapted_X adapted_Y adapted_Z adapted_W predictable_Y predictable_Z predictable_W
            hY_nonneg hZ_nonneg hW_nonneg condexp_ineq integrable_X integrable_Z integrable_W N (i + k))
        -- Tower property: μ[ μ[S_{i+k+1}|ℱ_{i+k}] | ℱ_i ] = μ[S_{i+k+1}|ℱ_i]
        have h_tower :
            μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω | ℱ i]
              =ᵐ[μ]
            μ[fun ω => μ[fun ω' => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω' | ℱ (i + k)] ω | ℱ i] := by
          have hm₁₂ : ℱ i ≤ ℱ (i + k) := by exact ℱ.mono (Nat.le_add_right _ _)
          have hm₂ : ℱ (i + k) ≤ m0 := ℱ.le (i + k)
          -- Rewriting the condExp_condExp_of_le equality to the desired direction
          have :=
            MeasureTheory.condExp_condExp_of_le (μ := μ)
              (f := fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω) hm₁₂ hm₂
          -- It gives μ[ μ[f|ℱ(i+k)] | ℱ i ] =ᵐ μ[f|ℱ i]
          -- Flip sides to match our target
          exact this.symm
        -- Monotonicity: apply condExp_mono with m = ℱ i to h_one
        have h_int_left : Integrable (μ[fun ω' => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω' | ℱ (i + k)]) μ :=
          integrable_condExp (μ := μ) (m := ℱ (i + k))
            (f := fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω)
        have h_int_right : Integrable (Scomp_trunc_stop μ ℱ X Y Z W N (i + k)) μ :=
          integrable_Scomp_trunc_stop (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
            adapted_X adapted_Y adapted_Z adapted_W predictable_Z
            hY_nonneg hZ_nonneg hW_nonneg integrable_X integrable_Z integrable_W N (i + k)
        have h_mono :=
          (MeasureTheory.condExp_mono (m := ℱ i) (μ := μ)
            (hf := h_int_left) (hg := h_int_right) (hfg := h_one))
        -- Chain: μ[S_{i+k+1}|ℱ i] =ᵐ μ[ μ[S_{i+k+1}|ℱ_{i+k}] | ℱ i ] ≤ᵐ μ[S_{i+k}|ℱ i] ≤ᵐ S_i
        have h_step :
            μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + (k + 1)) ω | ℱ i]
              ≤ᵐ[μ]
            μ[fun ω => Scomp_trunc_stop μ ℱ X Y Z W N (i + k) ω | ℱ i] :=
          h_tower.trans_le h_mono
        exact h_step.trans ih
    -- Apply the result to k = j - i
    have h_final := this (j - i)
    -- Rewrite i + (j - i) = j
    have hij' : i + (j - i) = j := Nat.add_sub_of_le hij
    simpa [hij'] using h_final
  · -- integrability
    intro t
    simpa using
      integrable_Scomp_trunc_stop (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
        adapted_X adapted_Y adapted_Z adapted_W predictable_Z
        hY_nonneg hZ_nonneg hW_nonneg integrable_X integrable_Z integrable_W N t

/-- Adaptedness of `Mpred`. -/
lemma Mpred_adapted
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    : Adapted ℱ (Mpred X Y Z W) := by
  intro t
  classical
  have hS : StronglyMeasurable[ℱ t] (scaledS X Y W t) :=
    scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W t
  have hZs : StronglyMeasurable[ℱ t] (Zsum Y Z t) :=
    Zsum_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y predictable_Z adapted_Z t
  simpa [Mpred, sub_eq_add_neg] using hS.sub hZs

/-- Integrability of `Mpred t`. -/
lemma integrable_Mpred
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    : ∀ t, Integrable (Mpred X Y Z W t) μ := by
  intro t
  have hS := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
    adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
  have hZs := integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
    adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z t
  simpa [Mpred, sub_eq_add_neg] using hS.sub hZs

/-- L¹ triangle for `Mpred t = scaledS t − Zsum t`. This is useful when attempting
to bound `Mpred` uniformly in `L¹` via separate bounds on `scaledS` and `Zsum`. -/
lemma eLpNorm_Mpred_le
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y) (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω) (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    : ∀ t,
      eLpNorm (Mpred X Y Z W t) 1 μ
        ≤ eLpNorm (scaledS X Y W t) 1 μ + eLpNorm (Zsum Y Z t) 1 μ := by
  intro t
  classical
  have hS_meas : AEStronglyMeasurable (scaledS X Y W t) μ :=
    ((scaledS_measurable (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W t).mono (ℱ.le t)).aestronglyMeasurable
  have hZs_meas : AEStronglyMeasurable (Zsum Y Z t) μ :=
    ((Zsum_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y predictable_Z adapted_Z t).mono (ℱ.le t)).aestronglyMeasurable
  have hsum : eLpNorm (Mpred X Y Z W t) 1 μ
      ≤ eLpNorm (scaledS X Y W t) 1 μ + eLpNorm (fun ω => - Zsum Y Z t ω) 1 μ := by
    -- triangle on scaledS + (−Zsum)
    have hZs_meas_neg : AEStronglyMeasurable (fun ω => - Zsum Y Z t ω) μ := hZs_meas.neg
    simpa [Mpred, sub_eq_add_neg] using
      (eLpNorm_add_le (μ := μ) (p := (1 : ENNReal)) hS_meas hZs_meas_neg (by simp))
  -- eLpNorm(−f) ≤ eLpNorm(f)
  have hneg_le : eLpNorm (fun ω => - Zsum Y Z t ω) 1 μ ≤ eLpNorm (Zsum Y Z t) 1 μ := by
    refine MeasureTheory.eLpNorm_mono_ae (μ := μ) (p := (1 : ENNReal)) ?_
    filter_upwards with ω; simp
  exact hsum.trans (add_le_add le_rfl hneg_le)

/-- Supermartingale property for `Mpred`. -/
lemma Mpred_supermartingale
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    : Supermartingale (Mpred X Y Z W) ℱ μ := by
  -- Structure: adapted + step + integrable
  refine And.intro ?adapted (And.intro ?step ?integrable)
  · exact Mpred_adapted (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Z
  · intro i j hij
    -- Induct on k = j - i using tower and monotonicity
    have h_base : μ[fun ω => Mpred X Y Z W i ω | ℱ i] =ᵐ[μ] Mpred X Y Z W i := by
      -- meas + integrable at level i
      have hmeas : StronglyMeasurable[ℱ i] (Mpred X Y Z W i) :=
        (Mpred_adapted (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
          adapted_X adapted_Y adapted_Z adapted_W predictable_Z i)
      have hint : Integrable (Mpred X Y Z W i) μ := by
        -- reuse integrability lemma
        have hS := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W i
        have hZs := integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z i
        simpa [Mpred, sub_eq_add_neg] using hS.sub hZs
      exact Filter.EventuallyEq.of_eq
        (MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := ℱ i) (hm := ℱ.le i)
          (f := Mpred X Y Z W i) (hf := hmeas) (hfi := hint))
    have : ∀ k, μ[fun ω => Mpred X Y Z W (i + k) ω | ℱ i] ≤ᵐ[μ] Mpred X Y Z W i := by
      intro k
      induction' k with k ih
      · simpa using h_base.le
      · -- one-step at time i+k
        have h_one := Mpred_one_step (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
          adapted_X adapted_Y adapted_Z adapted_W predictable_Y predictable_Z predictable_W
          hY_nonneg hZ_nonneg hW_nonneg condexp_ineq integrable_X integrable_Z integrable_W (i + k)
        -- tower: μ[μ[M_{i+k+1}|ℱ_{i+k}]|ℱ_i] = μ[M_{i+k+1}|ℱ_i]
        have h_tower :
            μ[fun ω => Mpred X Y Z W (i + (k + 1)) ω | ℱ i]
              =ᵐ[μ]
            μ[fun ω => μ[fun ω' => Mpred X Y Z W (i + (k + 1)) ω' | ℱ (i + k)] ω | ℱ i] := by
          have hm₁₂ : ℱ i ≤ ℱ (i + k) := ℱ.mono (Nat.le_add_right _ _)
          have hm₂ : ℱ (i + k) ≤ m0 := ℱ.le (i + k)
          exact (MeasureTheory.condExp_condExp_of_le (μ := μ)
            (f := fun ω => Mpred X Y Z W (i + (k + 1)) ω) hm₁₂ hm₂).symm
        -- monotonicity through conditional expectation at level i
        have h_int_left : Integrable (μ[fun ω' => Mpred X Y Z W (i + (k + 1)) ω' | ℱ (i + k)]) μ :=
          integrable_condExp (μ := μ) (m := ℱ (i + k))
            (f := fun ω => Mpred X Y Z W (i + (k + 1)) ω)
        have h_int_right : Integrable (Mpred X Y Z W (i + k)) μ := by
          have hS := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
            adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (i + k)
          have hZs := integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
            adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z (i + k)
          simpa [Mpred, sub_eq_add_neg] using hS.sub hZs
        have h_mono :=
          (MeasureTheory.condExp_mono (μ := μ) (m := ℱ i)
            (hf := h_int_left) (hg := h_int_right) (hfg := h_one))
        -- chain: μ[M_{i+k+1}|ℱ i] ≤ μ[M_{i+k}|ℱ i] ≤ M_i
        exact (h_tower.trans_le h_mono).trans ih
    -- apply to k = j - i
    have h := this (j - i)
    simpa [Nat.add_sub_of_le hij] using h
  · intro t
    -- integrable at each time
    have hS := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
      adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
    have hZs := integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z t
    simpa [Mpred, sub_eq_add_neg] using hS.sub hZs

/-- For fixed `N`, the stopped compensated process converges a.e. to `scaledS · N` as `t → ∞`.
This follows since the two compensator terms converge (one stabilizes and one is a Doob
approximation `μ[g | ℱ t] → g`) and `scaledS (min t N)` stabilizes to `scaledS N`. -/
lemma Scomp_trunc_stop_tendsto_scaledS
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    : ∀ N, ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun t => Scomp_trunc_stop μ ℱ X Y Z W N t ω)
          Filter.atTop (nhds (scaledS X Y W N ω)) := by
  intro N
  classical
  -- Convergence of the conditional expectation term to the integrable, ℱ∞-measurable limit
  have hB_int : Integrable (fun ω => B_trunc Y Z N N ω) μ :=
    integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
      adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N N
  have hB_meas_sSup : StronglyMeasurable[⨆ n, ℱ n] (fun ω => B_trunc Y Z N N ω) := by
    -- Strong measurability at level N, then lift to ⨆ n ℱ n
    have hN :=
      (B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
        adapted_Y adapted_Z predictable_Z) N N
    exact hN.mono (le_sSup ⟨N, rfl⟩)
  have h_condexp_tend : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun t => μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω)
        Filter.atTop (nhds (B_trunc Y Z N N ω)) := by
    -- Doob convergence for conditional expectations of a fixed integrable function
    simpa using
      (MeasureTheory.Integrable.tendsto_ae_condExp (μ := μ) (ℱ := ℱ)
        (g := fun ω => B_trunc Y Z N N ω) hB_int hB_meas_sSup)
  -- Stabilization of the two eventually-constant components
  have h_scaled_stab : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun t => scaledS X Y W (Nat.min t N) ω)
        Filter.atTop (nhds (scaledS X Y W N ω)) := by
    refine ae_of_all μ (fun ω => ?_)
    refine tendsto_atTop_of_eventually_const (ι := ℕ) (u := fun t => scaledS X Y W (Nat.min t N) ω)
      (i₀ := N) ?_
    intro t ht; simp [Nat.min_eq_right ht]
  have h_B_stab : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun t => B_trunc Y Z N t ω)
        Filter.atTop (nhds (B_trunc Y Z N N ω)) := by
    refine ae_of_all μ (fun ω => ?_)
    refine tendsto_atTop_of_eventually_const (ι := ℕ) (u := fun t => B_trunc Y Z N t ω)
      (i₀ := N) ?_
    intro t ht
    -- For t ≥ N, B_trunc freezes at the full truncation level N (pointwise).
    have hNt : N ≤ t := ht
    have h1 : B_trunc Y Z N t ω = (Finset.range N).sum (fun k => scaledZ Y Z k ω) := by
      simp [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := t) hNt]
    have h2 : B_trunc Y Z N N ω = (Finset.range N).sum (fun k => scaledZ Y Z k ω) := by
      have : N ≤ N := le_rfl
      simp [B_trunc_of_le_right (Y := Y) (Z := Z) (N := N) (t := N) this]
    simpa [h1, h2]
  -- Combine the three convergences using algebra of limits
  filter_upwards [h_scaled_stab, h_condexp_tend, h_B_stab] with ω hS hC hB
  -- Scomp_trunc_stop = scaledS(min t N) + μ[B_trunc N N | ℱ t] − B_trunc N t
  have h_add := hS.add hC
  have h_sub := h_add.sub hB
  simpa [Scomp_trunc_stop, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_sub

/-!
A Lean formulation of the classical Robbins–Siegmund lemma.

See paper/RobbinsSiegmundLemma.md for the statement and proof sketch we follow.
We adopt the predictable-form drift inequality with 0-based products/sums and
the stopped, truncated compensated process to construct a supermartingale.
-/

/-- Robbins–Siegmund lemma (predictable form, real-valued processes).

Assumptions:
- Adaptedness: `X t, Y t, Z t, W t` are `ℱ t`-measurable.
- Predictability: `Y (t+1), Z (t+1), W (t+1)` are `ℱ t`-measurable.
- Nonnegativity: `0 ≤ X t ω, 0 ≤ Y t ω, 0 ≤ Z t ω, 0 ≤ W t ω`.
- Integrability: each `X t, Z t, W t` is integrable; used in the conditional expectations below.
- Drift inequality (a.e.):
    `μ[fun ω => X (t + 1) ω | ℱ t] ≤ᵐ[μ]
       fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω`.
- Summability a.e.: `Summable (fun t => Y t ω)` and `Summable (fun t => Z t ω)` for a.e. `ω`.

Conclusions:
- There exists a measurable `X∞ : Ω → ℝ` such that `X t ⟶ X∞` almost surely.
- `∑ t, W t ω` converges (is finite) for almost every `ω`.
-/
theorem robbinsSiegmund
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hX_nonneg : ∀ t ω, 0 ≤ X t ω)
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    (summable_Y : ∀ᵐ ω ∂μ, Summable (fun t => Y t ω))
    (summable_Z : ∀ᵐ ω ∂μ, Summable (fun t => Z t ω))
  : ∃ Xlim : Ω → ℝ,
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => X t ω) Filter.atTop (nhds (Xlim ω)))
        ∧ (∀ᵐ ω ∂μ, Summable (fun t => W t ω)) := by
  -- Single-suffices reduction: normalize and compensate, then use the stopped supermartingale.
  suffices hS : ∃ Slim : Ω → ℝ,
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => scaledS X Y W t ω) Filter.atTop (nhds (Slim ω))) ∧
      (∀ᵐ ω ∂μ, Summable (fun t => W t ω)) by
    -- From convergence of scaledS and finiteness of ∑ W, it suffices to have a.e. limits
    -- for the product P_t := prodY Y t and the cumulative sum cumW.
    rcases hS with ⟨Slim, h_scaledS_tendsto_ae, h_summW_ae⟩
    -- Suffices: existence of pointwise limits Plim, Wlim with a.e. convergence
    suffices hPW : ∃ (Plim Wlim : Ω → ℝ),
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => prodY Y t ω) Filter.atTop (nhds (Plim ω))) ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => cumW W t ω) Filter.atTop (nhds (Wlim ω))) by
      rcases hPW with ⟨Plim, Wlim, hP_tendsto_ae, hW_tendsto_ae⟩
      refine ⟨(fun ω => Plim ω * Slim ω - Wlim ω), ?_, h_summW_ae⟩
      -- On the a.e. set where all components converge, use algebra of limits
      filter_upwards [hP_tendsto_ae, h_scaledS_tendsto_ae, hW_tendsto_ae] with ω hP hS hW
      -- Reduce to the algebraic identity `X t = prodY * scaledS - cumW`.
      -- We can finish the limit via `mul` and `sub` continuity once this identity is available.
      suffices hX_eq : ∀ t, X t ω = prodY Y t ω * scaledS X Y W t ω - cumW W t ω by
        have h_mul :
            Filter.Tendsto (fun t => prodY Y t ω * scaledS X Y W t ω)
              Filter.atTop (nhds (Plim ω * Slim ω)) := hP.mul hS
        have h_sub :
            Filter.Tendsto (fun t => prodY Y t ω * scaledS X Y W t ω - cumW W t ω)
              Filter.atTop (nhds (Plim ω * Slim ω - Wlim ω)) := h_mul.sub hW
        simpa [hX_eq] using h_sub
      -- TODO: algebraic identity for X in terms of scaledS and cumW.
      -- Hint: unfold `scaledS`, clear the denominator using `mul_div_cancel` with
      -- `prodY_pos hY_nonneg t ω`. Then `ring`.
      have hX_eq : ∀ t, X t ω = prodY Y t ω * scaledS X Y W t ω - cumW W t ω := by
        intro t
        have hpos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
        have hne : prodY Y t ω ≠ 0 := ne_of_gt hpos
        -- Start from the left-hand side and build up to the required expression
        calc
          X t ω
              = (X t ω + cumW W t ω) - cumW W t ω := by
                simp
          _ = prodY Y t ω * ((X t ω + cumW W t ω) / prodY Y t ω) - cumW W t ω := by
                -- Show X + cumW = prodY * ((X + cumW) / prodY)
                have hcancel :
                    prodY Y t ω * ((X t ω + cumW W t ω) / prodY Y t ω)
                      = X t ω + cumW W t ω := by
                  calc
                    prodY Y t ω * ((X t ω + cumW W t ω) / prodY Y t ω)
                        = ((X t ω + cumW W t ω) / prodY Y t ω) * prodY Y t ω := by
                          simpa [mul_comm]
                    _ = (X t ω + cumW W t ω) * prodY Y t ω / prodY Y t ω := by
                          simpa using
                            (div_mul_eq_mul_div (X t ω + cumW W t ω)
                              (prodY Y t ω) (prodY Y t ω))
                    _ = X t ω + cumW W t ω := by
                          -- simplify ((X+cumW) * P) / P to (X+cumW)
                          simpa [div_eq_mul_inv, hne, mul_comm, mul_left_comm, mul_assoc]
                exact congrArg (· - cumW W t ω) hcancel.symm
          _ = prodY Y t ω * scaledS X Y W t ω - cumW W t ω := by
                simp [scaledS]
      exact hX_eq
    -- It remains to construct Plim and Wlim. We split the two constructions.
    -- Wlim: a.e. limit of cumW from a.e. summability and nonnegativity
    have hWlim : ∃ Wlim : Ω → ℝ,
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => cumW W t ω) Filter.atTop (nhds (Wlim ω))) := by
      classical
      -- Choose the natural candidate Wlim = tsum W pointwise.
      let Wlim : Ω → ℝ := fun ω => ∑' t, W t ω
      refine ⟨Wlim, ?_⟩
      -- It suffices to show pointwise: if (W · ω) is summable then cumW W · ω tends to tsum.
      suffices hpt : ∀ᵐ ω ∂μ,
          (Summable (fun t => W t ω)) →
          Filter.Tendsto (fun t => cumW W t ω) Filter.atTop (nhds (Wlim ω)) by
        have hsumW := h_summW_ae
        filter_upwards [hpt, hsumW] with ω hω hsum; exact hω hsum
      -- pointwise: from Summable (W · ω) derive Tendsto of cumW to tsum.
      have hpt : ∀ᵐ ω ∂μ,
          (Summable (fun t => W t ω)) →
          Filter.Tendsto (fun t => cumW W t ω) Filter.atTop (nhds (Wlim ω)) := by
        refine ae_of_all μ (fun ω => ?_)
        intro hsum
        classical
        -- It suffices to show the partial sums with index (t+1) converge to the same limit.
        suffices hshift :
            Filter.Tendsto
              (fun t => (Finset.range (t + 1)).sum (fun k => W k ω))
              Filter.atTop (nhds (∑' k, W k ω)) by
          simpa [cumW] using hshift
        -- obtain hshift from (hsum.hasSum.tendsto_sum_nat) by composing with (Nat.succ)
        -- TODO: partial-sum convergence and cofinality composition
        -- (1) hsum_tend: Tendsto (fun n => ∑_{k < n} W k ω) atTop → nhds (∑' W · ω)
        -- (2) hsucc: Tendsto (fun t => t+1) atTop → atTop
        -- Then compose to get hshift.
        have hsum_tend :
            Filter.Tendsto (fun n => (Finset.range n).sum (fun k => W k ω))
              Filter.atTop (nhds (∑' k, W k ω)) := by
          -- from hasSum.tendsto_sum_nat
          exact hsum.hasSum.tendsto_sum_nat
        have hsucc : Filter.Tendsto (fun t : ℕ => t + 1) Filter.atTop Filter.atTop := by
          -- cofinality of Nat.succ on atTop
          -- For any n, eventually t ≥ n so t+1 ≥ n
          exact Filter.tendsto_atTop_atTop.mpr (fun n => ⟨n, fun t h => Nat.le_trans h (Nat.le_succ t)⟩)
        simpa using hsum_tend.comp hsucc
      exact hpt
    -- Plim: a.e. limit of prodY from a.e. summability and nonnegativity
    have hPlim : ∃ Plim : Ω → ℝ,
        (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => prodY Y t ω) Filter.atTop (nhds (Plim ω))) := by
      classical
      -- Candidate limit via logs: prodY t = exp (∑_{k<t} log (1 + Y (k+1))).
      let Plim : Ω → ℝ :=
        fun ω => Real.exp (∑' k, Real.log (1 + Y (k + 1) ω))
      refine ⟨Plim, ?_⟩
      -- Reduce to the pointwise statement on the a.e. set where Y · ω is summable.
      suffices hpt : ∀ᵐ ω ∂μ,
          (Summable (fun t => Y t ω)) →
          Filter.Tendsto (fun t => prodY Y t ω) Filter.atTop (nhds (Plim ω)) by
        filter_upwards [hpt, summable_Y] with ω hω hsum; exact hω hsum
      -- Pointwise proof under `Summable (Y · ω)`.
      refine ae_of_all μ (fun ω => ?_)
      intro hsumY
      -- Step 1: Summability of the log-increments by comparison 0 ≤ log(1+y) ≤ y.
      suffices hlog_sum : Summable (fun t => Real.log (1 + Y (t + 1) ω)) by
        -- Step 2: Identify finite products with exp of partial sums of logs.
        have hprod_exp : ∀ t,
            prodY Y t ω
              = Real.exp ((Finset.range t).sum (fun k => Real.log (1 + Y (k + 1) ω))) := by
          intro t
          classical
          induction' t with n ih
          · -- t = 0
            simp [prodY]
          · -- step
            -- positivity of the new factor to use exp_log
            have hpos : 0 < 1 + Y (n + 1) ω := by
              have : (0 : ℝ) < 1 := by norm_num
              have hy : 1 ≤ 1 + Y (n + 1) ω := by
                simpa using add_le_add_left (hY_nonneg (n + 1) ω) (1 : ℝ)
              exact lt_of_lt_of_le this hy
            -- use the inductive identity and exp_add/exp_log
            have :
                Real.exp ((Finset.range (n + 1)).sum (fun k => Real.log (1 + Y (k + 1) ω)))
                  = Real.exp ((Finset.range n).sum (fun k => Real.log (1 + Y (k + 1) ω))
                      + Real.log (1 + Y (n + 1) ω)) := by
              simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
            calc
              prodY Y (n + 1) ω
                  = prodY Y n ω * (1 + Y (n + 1) ω) := by
                    simp [prodY, Finset.prod_range_succ, mul_comm, mul_left_comm, mul_assoc]
              _ = Real.exp ((Finset.range n).sum (fun k => Real.log (1 + Y (k + 1) ω)))
                    * (1 + Y (n + 1) ω) := by simpa [ih]
              _ = Real.exp ((Finset.range n).sum (fun k => Real.log (1 + Y (k + 1) ω)))
                    * Real.exp (Real.log (1 + Y (n + 1) ω)) := by
                    simp [Real.exp_log hpos]
              _ = Real.exp (((Finset.range n).sum (fun k => Real.log (1 + Y (k + 1) ω)))
                    + Real.log (1 + Y (n + 1) ω)) := by
                    simpa [Real.exp_add, mul_comm, mul_left_comm, mul_assoc]
              _ = Real.exp ((Finset.range (n + 1)).sum (fun k => Real.log (1 + Y (k + 1) ω))) := by
                    simpa [this]
        -- Step 3: Tendsto of partial sums of logs to the tsum of logs.
        have h_hasSum := hlog_sum.hasSum
        have hsum_tend :
            Filter.Tendsto
              (fun t => (Finset.range t).sum (fun k => Real.log (1 + Y (k + 1) ω)))
              Filter.atTop (nhds (∑' k, Real.log (1 + Y (k + 1) ω))) := by
          simpa using h_hasSum.tendsto_sum_nat
        -- Step 4: Continuity of exp transports the convergence.
        have h_exp_tend :
            Filter.Tendsto
              (fun t => Real.exp ((Finset.range t).sum (fun k => Real.log (1 + Y (k + 1) ω))))
              Filter.atTop (nhds (Real.exp (∑' k, Real.log (1 + Y (k + 1) ω)))) := by
          exact (Real.continuous_exp.tendsto _).comp hsum_tend
        -- Step 5: Replace the finite exponentials with prodY via hprod_exp.
        have := h_exp_tend
        simpa [hprod_exp, Plim] using this
      -- Remaining task: summability of logs from summability of Y (shifted by 1).
      -- This follows from `Real.summable_log_one_add_of_summable` and `summable_nat_add_iff`.
      have hsumY_shift : Summable (fun t => Y (t + 1) ω) :=
        ((summable_nat_add_iff (f := fun t => Y t ω) 1).mpr hsumY)
      exact Real.summable_log_one_add_of_summable hsumY_shift
    rcases hPlim with ⟨Plim, hP_tendsto_ae⟩
    rcases hWlim with ⟨Wlim, hW_tendsto_ae⟩
    exact ⟨Plim, Wlim, hP_tendsto_ae, hW_tendsto_ae⟩
  -- Existence of a stopped compensated supermartingale; will be used to construct Slim and ∑ W.
  have h_super :=
    Scomp_trunc_stop_supermartingale (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Y predictable_Z predictable_W
      hY_nonneg hZ_nonneg hW_nonneg condexp_ineq integrable_X integrable_Z integrable_W
  -- For each N, the stopped compensated process tends a.e. to scaledS · N as t → ∞
  have h_stop_lim :=
    (Scomp_trunc_stop_tendsto_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Z hY_nonneg hZ_nonneg hW_nonneg
      integrable_Z)
  -- Next: from h_super and summable_Y/summable_Z, extract a.e. convergence of scaledS and
  -- a.e. summability of W via the stopped process and a limiting argument in N.
  -- TODO: implement the N → ∞ passage using monotone convergence for the truncated compensator
  -- and submartingale convergence for −Scomp_trunc_stop.
  -- L¹-boundedness for each fixed N (uniform in t): needed for submartingale convergence
  have h_L1_bdd :=
    (eLpNorm_Scomp_trunc_stop_bdd (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Z
      hY_nonneg hZ_nonneg hW_nonneg integrable_X integrable_Z integrable_W)
  -- Single-suffices: submartingale convergence for −Scomp_trunc_stop N with L¹ bound
  suffices h_subconv : ∀ N, ∃ L_N : Ω → ℝ,
      (∀ᵐ ω ∂μ,
        Filter.Tendsto (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t ω)
          Filter.atTop (nhds (L_N ω))) from
    by
      -- Using h_subconv together with h_stop_lim, identify L_N = -scaledS · N a.e.
      -- This reduces the passage N → ∞ to understanding scaledS N.
      have h_ident : ∀ N, ∃ L_N : Ω → ℝ,
          (∀ᵐ ω ∂μ,
            Filter.Tendsto (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t ω)
              Filter.atTop (nhds (L_N ω))) ∧
          (∀ᵐ ω ∂μ, L_N ω = - scaledS X Y W N ω) := by
        intro N
        rcases h_subconv N with ⟨L_N, hL⟩
        -- Negate the stopped-limit convergence: Scomp_trunc_stop → scaledS ⇒ −Scomp_trunc_stop → −scaledS
        have h_neg_stop : ∀ᵐ ω ∂μ,
            Filter.Tendsto (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t ω)
              Filter.atTop (nhds (- scaledS X Y W N ω)) := by
          filter_upwards [h_stop_lim N] with ω hS
          exact (continuous_neg.tendsto _).comp hS
        -- Uniqueness of limits in ℝ: if −Scomp tends to L_N and to −scaledS, then L_N = −scaledS a.e.
        have h_eq : ∀ᵐ ω ∂μ, L_N ω = - scaledS X Y W N ω := by
          classical
          haveI : (Filter.atTop : Filter ℕ).NeBot := Filter.atTop_neBot
          filter_upwards [hL, h_neg_stop] with ω h1 h2
          exact tendsto_nhds_unique h1 h2
        exact ⟨L_N, hL, h_eq⟩
      -- TODO: pass to N → ∞ using summability of Y and Z to construct Slim and Summable W.
      -- The identification above reduces the problem to the behavior of scaledS N.
      have hSlim : ∃ Slim : Ω → ℝ,
          (∀ᵐ ω ∂μ,
            Filter.Tendsto (fun t => scaledS X Y W t ω)
              Filter.atTop (nhds (Slim ω))) ∧
          (∀ᵐ ω ∂μ, Summable (fun t => W t ω)) := by
        classical
        /- Strategy: it suffices to show that for almost every ω there exists a real limit
           c(ω) with Tendsto scaledS · ω → c(ω) and Summable (W · ω). Then select Slim(ω)
           as that limit via a choice-on-ae set construction. -/
        -- Existence of pointwise limits and W-summability on an a.e. set
        suffices hlim_exists : ∀ᵐ ω ∂μ,
            ∃ c : ℝ,
              (Filter.Tendsto (fun t => scaledS X Y W t ω)
                 Filter.atTop (nhds c)) ∧ Summable (fun t => W t ω) by
          -- Define Slim by choosing the limit on the a.e. set where it exists
          let Slim : Ω → ℝ := fun ω =>
            let HH : Prop := ∃ c : ℝ,
              Filter.Tendsto (fun t => scaledS X Y W t ω) Filter.atTop (nhds c)
            if h : HH ∧ Summable (fun t => W t ω)
            then (Classical.choose h.1) else 0
          have h_tend : ∀ᵐ ω ∂μ,
              Filter.Tendsto (fun t => scaledS X Y W t ω)
                Filter.atTop (nhds (Slim ω)) := by
            filter_upwards [hlim_exists] with ω hω
            -- On this ω, the if-branch is taken and Slim ω = chosen limit
            rcases hω with ⟨c, hc, _hW⟩
            have hH : (∃ c : ℝ,
                Filter.Tendsto (fun t => scaledS X Y W t ω) Filter.atTop (nhds c)) ∧
                Summable (fun t => W t ω) := ⟨⟨c, hc⟩, _hW⟩
            -- Tendsto to the (Classical.choose hH.1); by definition Slim ω equals this choose
            have h_choose :
                Filter.Tendsto (fun t => scaledS X Y W t ω)
                  Filter.atTop (nhds (Classical.choose hH.1)) := Classical.choose_spec hH.1
            have hSlim_eq : Slim ω = Classical.choose hH.1 := by simp [Slim, hH]
            simpa [hSlim_eq] using h_choose
          have h_sumW : ∀ᵐ ω ∂μ, Summable (fun t => W t ω) := by
            filter_upwards [hlim_exists] with ω hω
            rcases hω with ⟨c, _hc, hW⟩; exact hW
          exact ⟨Slim, And.intro h_tend h_sumW⟩
        -- Pointwise existence under the RS hypotheses (to be refined):
        -- Step 1: From summable_Z and prodY ≥ 1, deduce a.e. summability of scaledZ Y Z.
        have hsum_scaledZ_ae : ∀ᵐ ω ∂μ, Summable (fun k => scaledZ Y Z k ω) := by
          -- comparison: 0 ≤ scaledZ k ω ≤ Z (k+1) ω, and Summable (Z (·+1) ω)
          have hcmp : ∀ ω, ∀ k, 0 ≤ scaledZ Y Z k ω ∧ scaledZ Y Z k ω ≤ Z (k + 1) ω := by
            intro ω k
            have hZpos : 0 ≤ Z (k + 1) ω := hZ_nonneg (k + 1) ω
            have hden_ge1 : 1 ≤ prodY Y k ω := prodY_ge_one (Y := Y) hY_nonneg k ω
            have hden_pos : 0 < prodY Y k ω := prodY_pos (Y := Y) hY_nonneg k ω
            have hnonneg : 0 ≤ scaledZ Y Z k ω :=
              scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
            -- scaledZ ≤ Z_{k+1} via multiplication by the denominator ≥ 1
            have hmul : Z (k + 1) ω ≤ Z (k + 1) ω * prodY Y k ω := by
              simpa [one_mul] using (mul_le_mul_of_nonneg_left hden_ge1 hZpos)
            have hle : scaledZ Y Z k ω ≤ Z (k + 1) ω := by
              -- use div_le_iff₀ for positive denominators
              have := (div_le_iff₀ hden_pos).mpr hmul
              simpa [scaledZ] using this
            exact ⟨hnonneg, hle⟩
          -- Lift summable_Z (pointwise) to obtain summability of the comparison series
          filter_upwards [summable_Z] with ω hsumZ
          have hsumZ_shift : Summable (fun k => Z (k + 1) ω) :=
            (summable_nat_add_iff (f := fun k => Z k ω) 1).mpr hsumZ
          -- Apply comparison test to get Summable (scaledZ · ω)
          refine Summable.of_nonneg_of_le (fun k => (hcmp ω k).1) (fun k => (hcmp ω k).2) hsumZ_shift
        -- Step 2: Reduce the pointwise existence to a dedicated pointwise lemma,
        -- parameterized by ω and the summability assumptions.
        have robbinsSiegmund_pointwise :
            ∀ ω,
              (Summable (fun t => Y t ω)) → (Summable (fun t => Z t ω)) →
              ∃ c : ℝ,
                (Filter.Tendsto (fun t => scaledS X Y W t ω)
                  Filter.atTop (nhds c)) ∧ Summable (fun t => W t ω) := by
          intro ω hYsum hZsum
          -- Comparison: 0 ≤ scaledZ ≤ Z_{k+1} and Summable (Z (·+1) ω)
          have hsum_scaledZ : Summable (fun k => scaledZ Y Z k ω) := by
            have hZshift : Summable (fun k => Z (k + 1) ω) :=
              (summable_nat_add_iff (f := fun k => Z k ω) 1).mpr hZsum
            have hcmp : ∀ k, 0 ≤ scaledZ Y Z k ω ∧ scaledZ Y Z k ω ≤ Z (k + 1) ω := by
              intro k
              have hZpos : 0 ≤ Z (k + 1) ω := hZ_nonneg (k + 1) ω
              have hden_ge1 : 1 ≤ prodY Y k ω := prodY_ge_one (Y := Y) hY_nonneg k ω
              have hden_pos : 0 < prodY Y k ω := prodY_pos (Y := Y) hY_nonneg k ω
              have hnonneg : 0 ≤ scaledZ Y Z k ω :=
                scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
              have hmul : Z (k + 1) ω ≤ Z (k + 1) ω * prodY Y k ω := by
                simpa [one_mul] using (mul_le_mul_of_nonneg_left hden_ge1 hZpos)
              have hle : scaledZ Y Z k ω ≤ Z (k + 1) ω := by
                have := (div_le_iff₀ hden_pos).mpr hmul
                simpa [scaledZ] using this
              exact ⟨hnonneg, hle⟩
            exact Summable.of_nonneg_of_le (fun k => (hcmp k).1) (fun k => (hcmp k).2) hZshift
          -- Reduce to two concrete subgoals: existence of the limit and W-summability.
          -- (A) Existence of pointwise limit for scaledS · ω
          suffices hScaled_lim : ∃ c : ℝ,
              Filter.Tendsto (fun t => scaledS X Y W t ω)
                Filter.atTop (nhds c) from
            by
              -- (B) Summability of W · ω
              suffices hWsum : Summable (fun t => W t ω) by
                exact ⟨hScaled_lim.choose, hScaled_lim.choose_spec, hWsum⟩
              -- Pointwise summability of W from bounded partial sums.
              -- Notation shorthands
              classical
              set Pt : ℕ → ℝ := fun t => prodY Y t ω
              set St : ℕ → ℝ := fun t => scaledS X Y W t ω
              set Wsum : ℕ → ℝ := fun t => cumW W t ω
              -- From convergence St → c, obtain an eventual bound St ≤ c + 1.
              have hSt_tend : Filter.Tendsto St Filter.atTop (nhds hScaled_lim.choose) :=
                hScaled_lim.choose_spec
              have hSt_bd : ∀ᶠ t in Filter.atTop, St t ≤ hScaled_lim.choose + 1 := by
                have h := hSt_tend.eventually (by
                  have hε : 0 < (1 : ℝ) := by norm_num
                  exact Metric.ball_mem_nhds _ hε)
                refine h.mono ?_
                intro t ht
                -- |St t − c| < 1 ⇒ St t ≤ c + 1
                have hlt : |St t - hScaled_lim.choose| < 1 := by
                  simpa [Metric.mem_ball, Real.dist_eq] using ht
                have : St t - hScaled_lim.choose ≤ |St t - hScaled_lim.choose| := by
                  exact le_abs_self _
                have : St t - hScaled_lim.choose < 1 := lt_of_le_of_lt this hlt
                linarith
              -- Uniform bound on Pt using 1 + y ≤ exp y and partial sums ≤ tsum.
              have hprod_le_exp : ∀ t,
                  Pt t ≤ Real.exp ((Finset.range t).sum (fun k => Y (k + 1) ω)) := by
                intro t
                classical
                -- Compare each factor: 1 + Y ≤ exp Y
                have h0 : ∀ k ∈ Finset.range t, (0 : ℝ) ≤ 1 + Y (k + 1) ω := by
                  intro k hk; have := hY_nonneg (k + 1) ω; linarith
                have hle : ∀ k ∈ Finset.range t, (1 + Y (k + 1) ω)
                    ≤ Real.exp (Y (k + 1) ω) := by
                  intro k hk; simpa [add_comm] using Real.add_one_le_exp (Y (k + 1) ω)
                have hprod :=
                  Finset.prod_le_prod (s := Finset.range t) (f := fun k => 1 + Y (k + 1) ω)
                    (g := fun k => Real.exp (Y (k + 1) ω)) h0 hle
                -- Rewrite RHS product as exp of the sum via an auxiliary identity
                have hprod_exp' : ∀ t,
                    (Finset.range t).prod (fun k => Real.exp (Y (k + 1) ω))
                      = Real.exp ((Finset.range t).sum (fun k => Y (k + 1) ω)) := by
                  intro t; classical
                  induction' t with n ih
                  · simp
                  · simp [Finset.prod_range_succ, Finset.sum_range_succ, ih, Real.exp_add,
                      mul_comm, mul_left_comm, mul_assoc]
                simpa [Pt, prodY, hprod_exp' t] using hprod
              -- Bound the partial sums (shifted) of Y by the (finite) tsum since Y ≥ 0
              have hYsum_shift : Summable (fun k => Y (k + 1) ω) :=
                (summable_nat_add_iff (f := fun k => Y k ω) 1).mpr hYsum
              have hsum_le_tsum : ∀ t,
                  (Finset.range t).sum (fun k => Y (k + 1) ω)
                    ≤ ∑' k, Y (k + 1) ω := by
                intro t
                exact hYsum_shift.sum_le_tsum (Finset.range t)
                  (by intro k hk; exact hY_nonneg (k + 1) ω)
              -- Global product bound M
              set M : ℝ := Real.exp (∑' k, Y (k + 1) ω)
              have hPt_bd : ∀ t, Pt t ≤ M := by
                intro t
                have := hprod_le_exp t
                have hmono := (Real.exp_le_exp.mpr (hsum_le_tsum t))
                exact this.trans hmono
              -- Partial sums of W bounded: Wsum t ≤ Pt t * St t since X ≥ 0
              have hWsum_le : ∀ t, Wsum t ≤ Pt t * St t := by
                intro t
                -- Pt t * St t = X t ω + Wsum t
                have hpos : 0 < Pt t := prodY_pos (Y := Y) hY_nonneg t ω
                have hne : Pt t ≠ 0 := ne_of_gt hpos
                have hEq : Pt t * St t = X t ω + Wsum t := by
                  simpa [Pt, St, Wsum, scaledS, mul_comm, mul_left_comm, mul_assoc,
                    div_eq_mul_inv, hne]
                have : Wsum t ≤ X t ω + Wsum t := by
                  have h := hX_nonneg t ω
                  linarith
                simpa [hEq] using this
              -- Choose t₀ with the eventual bound on St
              rcases (Filter.eventually_atTop.1 hSt_bd) with ⟨t0, ht0⟩
              -- Define a uniform bound B for all partial sums (Finset ranges)
              set B : ℝ := max (Wsum t0) (M * (hScaled_lim.choose + 1))
              -- For every n, the partial sum over range n is ≤ B
              have hsum_bd : ∀ n, (Finset.range n).sum (fun k => W k ω) ≤ B := by
                intro n
                by_cases hle : n ≤ t0 + 1
                · -- For small n, compare with Wsum t0 using subset of ranges and nonnegativity
                  have hsubset : (Finset.range n) ⊆ (Finset.range (t0 + 1)) :=
                    Finset.range_subset_range.2 hle
                  have hsmall :
                      (Finset.range n).sum (fun k => W k ω)
                        ≤ (Finset.range (t0 + 1)).sum (fun k => W k ω) := by
                    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                      (by intro i hi _; exact hW_nonneg i ω)
                  have hWsum_t0 :
                      (Finset.range (t0 + 1)).sum (fun k => W k ω) = Wsum t0 := by
                    simp [Wsum, cumW]
                  exact (hsmall.trans (by simpa [hWsum_t0])).trans (le_max_left _ _)
                · -- For large n, write the range-sum as Wsum (n-1) and use the St-bound
                  have hge : t0 + 1 ≤ n := by exact le_of_not_ge hle
                  -- Split n as succ m since n ≥ 1 in this branch
                  by_cases hzero : n = 0
                  · -- n = 0 ⇒ partial sum is 0, trivially ≤ B since B ≥ 0
                    have hB_nonneg : 0 ≤ B := by
                      have h0 : 0 ≤ Wsum t0 := cumW_nonneg (W := W) hW_nonneg t0 ω
                      have : 0 ≤ max (Wsum t0) (M * (hScaled_lim.choose + 1)) :=
                        (le_trans h0 (le_max_left _ _))
                      simpa [B] using this
                    simpa [hzero] using hB_nonneg
                  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
                    -- Now n = m + 1 so the range-sum equals Wsum m
                    have hsum_eq :
                        (Finset.range n).sum (fun k => W k ω) = Wsum m := by
                      subst hm; simp [Wsum, cumW]
                    -- Bound Wsum m by Pt m * St m and then by M * (c + 1)
                    have hSt_le : St m ≤ hScaled_lim.choose + 1 := by
                      have hle' : t0 + 1 ≤ m + 1 := by simpa [hm] using hge
                      have : t0 ≤ m := (Nat.succ_le_succ_iff.mp hle')
                      exact ht0 m this
                    have hM_nonneg : 0 ≤ M := (Real.exp_pos _).le
                    have hSt_nonneg : 0 ≤ St m := by
                      -- St m = (X m + Wsum m) / Pt m with nonnegative numerator and positive denom
                      have hnum : 0 ≤ X m ω + Wsum m :=
                        add_nonneg (hX_nonneg m ω) (cumW_nonneg (W := W) hW_nonneg m ω)
                      have hden : 0 < Pt m := prodY_pos (Y := Y) hY_nonneg m ω
                      simpa [Pt, St, scaledS] using (div_nonneg hnum hden.le)
                    have hmul_bd : Pt m * St m ≤ M * (hScaled_lim.choose + 1) := by
                      exact mul_le_mul (hPt_bd m) hSt_le hSt_nonneg hM_nonneg
                    have hW_bd : Wsum m ≤ M * (hScaled_lim.choose + 1) :=
                      (hWsum_le m).trans hmul_bd
                    have hlarge :
                        (Finset.range n).sum (fun k => W k ω)
                          ≤ M * (hScaled_lim.choose + 1) := by
                      simpa [hsum_eq] using hW_bd
                    exact hlarge.trans (le_max_right _ _)
              -- Apply the real-series criterion: nonnegative terms with bounded partial sums are summable
              exact summable_of_sum_range_le (hf := fun n => hW_nonneg n ω) (h := hsum_bd)
          -- TODO (A): derive existence of the limit for `scaledS` from compensator tail control
          -- and the per‑N identification of stopped limits.
          -- Strategy: first reduce to showing that `scaledS · ω` is a Cauchy sequence, then
          -- appeal to completeness of `ℝ` to obtain a limit.
          suffices hCauchy : CauchySeq (fun t => scaledS X Y W t ω) by
            -- ℝ is complete, so a Cauchy sequence converges to some limit.
            exact cauchySeq_tendsto_of_complete hCauchy
          -- It remains to prove the Cauchy property. Outline: bound the telescoping differences
          -- using the truncated compensator and the summable scaledZ-tail obtained above
          -- (`hsum_scaledZ`), then apply a Cauchy criterion for real sequences.
          -- We will prove the Cauchy property via an ε–N–T construction in the next step.
          classical
          refine Metric.cauchy_iff.2 ?_
          refine ⟨?_, ?_⟩
          · -- The image filter of `atTop` is nontrivial.
            simpa using (Filter.atTop_neBot.map (fun t => scaledS X Y W t ω))
          · intro ε hε
            -- Choose truncation levels and stopping times so that every tail of the process is
            -- ε-close; this is carried out in the next refinement step.
            suffices hCenter :
                ∃ T, ∀ t ≥ T, |scaledS X Y W t ω - scaledS X Y W T ω| < ε / 2 by
              rcases hCenter with ⟨T, hT⟩
              -- Work with the tail set consisting of values attained after time `T`.
              set tailSet :
                  Set ℝ := {x | ∃ n ≥ T, x = scaledS X Y W n ω}
              have ht_mem :
                  tailSet ∈ Filter.map (fun t => scaledS X Y W t ω) Filter.atTop := by
                refine Filter.mem_map.2 ?_
                refine Filter.mem_of_superset (Filter.eventually_ge_atTop T) ?_
                intro n hn
                exact ⟨n, hn, rfl⟩
              refine ⟨tailSet, ht_mem, ?_⟩
              intro x hx
              rcases hx with ⟨sx, hsx, rfl⟩
              intro y hy
              rcases hy with ⟨sy, hsy, rfl⟩
              have hs_bound : |scaledS X Y W sx ω - scaledS X Y W T ω| < ε / 2 :=
                hT sx hsx
              have ht_bound : |scaledS X Y W sy ω - scaledS X Y W T ω| < ε / 2 :=
                hT sy hsy
              -- Triangle inequality via the intermediate index `T`.
              have htriangle :
                  |scaledS X Y W sx ω - scaledS X Y W sy ω|
                      ≤ |scaledS X Y W sx ω - scaledS X Y W T ω|
                        + |scaledS X Y W sy ω - scaledS X Y W T ω| := by
                have hineq :=
                  abs_sub_le (scaledS X Y W sx ω) (scaledS X Y W T ω)
                    (scaledS X Y W sy ω)
                have hrewrite :
                    |scaledS X Y W T ω - scaledS X Y W sy ω|
                      = |scaledS X Y W sy ω - scaledS X Y W T ω| := by
                  simpa [abs_sub_comm]
                simpa [hrewrite] using hineq
              have hsum_lt :
                  |scaledS X Y W sx ω - scaledS X Y W T ω|
                      + |scaledS X Y W sy ω - scaledS X Y W T ω|
                      < ε := by
                have hhalf : ε / 2 + ε / 2 = ε := by ring
                have hsum := add_lt_add hs_bound ht_bound
                simpa [hhalf] using hsum
              exact lt_of_le_of_lt htriangle hsum_lt
            -- Remaining task: build the eventual closeness to the fixed index `T`.
            classical
            suffices h_tail_bound :
                ∃ T₀,
                  (∀ t ≥ T₀,
                      ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω) ≤ ε / 4) ∧
                  (∀ t ≥ T₀,
                      |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                          - B_trunc Y Z T₀ T₀ ω| < ε / 4) ∧
                  (∀ t ≥ T₀,
                      |scaledS X Y W t ω - scaledS X Y W T₀ ω|
                        ≤ ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω)
                          + |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                              - B_trunc Y Z T₀ T₀ ω|) by
              obtain ⟨T₀, hZ, hcond, hbound⟩ := h_tail_bound
              refine ⟨T₀, ?_⟩
              intro t ht
              have hZ_le : ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω) ≤ ε / 4 :=
                hZ t ht
              have hcond_lt :
                  |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                      - B_trunc Y Z T₀ T₀ ω| < ε / 4 :=
                hcond t ht
              have hineq :=
                hbound t ht
              have hcond_le :
                  |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                      - B_trunc Y Z T₀ T₀ ω| ≤ ε / 4 :=
                le_of_lt hcond_lt
              have hsum_le :
                  ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω)
                    + |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                        - B_trunc Y Z T₀ T₀ ω|
                    ≤ ε / 2 := by
                have hadd := add_le_add hZ_le hcond_le
                have : ε / 4 + ε / 4 = ε / 2 := by ring
                simpa [this] using hadd
              have hsum_lt_half :
                  ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω)
                    + |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                        - B_trunc Y Z T₀ T₀ ω|
                    < ε / 2 := by
                have := add_lt_add_of_le_of_lt hZ_le hcond_lt
                have hhalf : ε / 4 + ε / 4 = ε / 2 := by ring
                simpa [hhalf] using this
              exact lt_of_le_of_lt hineq hsum_lt_half
            -- First obtain a single index controlling the two quantitative bounds;
            -- the structural inequality will then complete the goal.
            suffices h_exists_core :
                ∃ T₀,
                  (∀ t ≥ T₀,
                      ((Finset.Icc T₀ t).sum fun k => scaledZ Y Z k ω) ≤ ε / 4) ∧
                  (∀ t ≥ T₀,
                      |μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                          - B_trunc Y Z T₀ T₀ ω| < ε / 4) by
              obtain ⟨T₀, hZ, hcond⟩ := h_exists_core
              refine ⟨T₀, hZ, hcond, ?_⟩
              intro t ht
              -- Quantitative comparison between `scaledS` and its truncated version.
              -- Strategy: use the relationship between scaledS, B_trunc, and scaledZ.
              -- When t ≥ T₀, we have B_trunc T₀ t = B_trunc T₀ T₀ (both freeze at T₀).
              have hB_eq : B_trunc Y Z T₀ t ω = B_trunc Y Z T₀ T₀ ω := by
                have hle : T₀ ≤ t := ht
                have h1 : B_trunc Y Z T₀ t = (Finset.range T₀).sum (fun k => scaledZ Y Z k) := by
                  exact B_trunc_of_le_right (Y := Y) (Z := Z) hle
                have h2 : B_trunc Y Z T₀ T₀ = (Finset.range T₀).sum (fun k => scaledZ Y Z k) := by
                  exact B_trunc_of_le_right (Y := Y) (Z := Z) le_rfl
                simp [h1, h2]
              -- Also μ[B_trunc T₀ T₀ | ℱ T₀] = B_trunc T₀ T₀ by measurability
              have hcondexp_eq : μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ T₀] = B_trunc Y Z T₀ T₀ := by
                have hmeas : StronglyMeasurable[ℱ T₀] (B_trunc Y Z T₀ T₀) := by
                  exact (B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
                    adapted_Y adapted_Z predictable_Z) T₀ T₀
                have hint : Integrable (B_trunc Y Z T₀ T₀) μ := by
                  exact integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
                    adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z T₀ T₀
                exact MeasureTheory.condExp_of_stronglyMeasurable
                  (μ := μ) (m := ℱ T₀) (hm := ℱ.le T₀) (f := B_trunc Y Z T₀ T₀) hmeas hint
              -- Now use Scomp_trunc definition to relate scaledS values
              -- scaledS t ω = Scomp_trunc T₀ t ω - μ[B_trunc T₀ T₀ | ℱ t] ω + B_trunc T₀ t ω
              have hS_t : scaledS X Y W t ω
                  = Scomp_trunc μ ℱ X Y Z W T₀ t ω
                    - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                    + B_trunc Y Z T₀ t ω := by
                simp [Scomp_trunc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              -- scaledS T₀ ω = Scomp_trunc T₀ T₀ ω - μ[B_trunc T₀ T₀ | ℱ T₀] ω + B_trunc T₀ T₀ ω
              have hS_T₀ : scaledS X Y W T₀ ω
                  = Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω
                    - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ T₀] ω
                    + B_trunc Y Z T₀ T₀ ω := by
                simp [Scomp_trunc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              -- Substitute using the equalities
              rw [hS_t, hS_T₀, hB_eq, hcondexp_eq]
              -- After substitution, the LHS simplifies algebraically
              ring_nf
              -- Goal: |Scomp_trunc T₀ t - μ[...| ℱ t] + (B_trunc T₀ T₀ - Scomp_trunc T₀ T₀)|
              --       ≤ sum + |μ[...| ℱ t] - B_trunc T₀ T₀|
              -- Rearrange: |A - B + C| where A = Scomp_trunc t, B = μ[...], C = B_trunc - Scomp_trunc T₀
              -- Use triangle inequality: |A - B + C| ≤ |A + C| + |B|
              have hterm_rewrite : Scomp_trunc μ ℱ X Y Z W T₀ t ω - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω
                  + (B_trunc Y Z T₀ T₀ ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω)
                = (Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω + B_trunc Y Z T₀ T₀ ω)
                  - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω := by ring
              rw [hterm_rewrite]
              -- Now use |X - Y| ≤ |X - C| + |C - Y| with C = B_trunc T₀ T₀
              have htriang : |(Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω + B_trunc Y Z T₀ T₀ ω)
                  - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω|
                ≤ |(Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω + B_trunc Y Z T₀ T₀ ω)
                      - B_trunc Y Z T₀ T₀ ω|
                  + |B_trunc Y Z T₀ T₀ ω - μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω| := by
                have := abs_sub_le
                  (Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω + B_trunc Y Z T₀ T₀ ω)
                  (B_trunc Y Z T₀ T₀ ω)
                  (μ[fun ω' => B_trunc Y Z T₀ T₀ ω' | ℱ t] ω)
                simpa [abs_sub_comm] using this
              refine htriang.trans ?_
              -- Simplify LHS term and use that Scomp_trunc difference relates to scaledZ sum
              have hsimp : |(Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω + B_trunc Y Z T₀ T₀ ω)
                      - B_trunc Y Z T₀ T₀ ω|
                  = |Scomp_trunc μ ℱ X Y Z W T₀ t ω - Scomp_trunc μ ℱ X Y Z W T₀ T₀ ω| := by ring_nf
              rw [hsimp, abs_sub_comm (B_trunc Y Z T₀ T₀ ω)]
              -- Now need to bound |Scomp_trunc T₀ t - Scomp_trunc T₀ T₀| by the scaledZ sum
              -- This requires showing the Scomp_trunc telescopes correctly
              sorry
            -- It remains to build the index `T₀` satisfying the two smallness conditions.
            -- First obtain tail control via summability of `scaledZ`.
            have hsum := hsum_scaledZ.hasSum
            have hconv := hsum.tendsto_sum_nat
            have hquarter_pos : 0 < ε / 8 := by
              have : (0 : ℝ) < 8 := by norm_num
              exact div_pos hε this
            obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hconv) (ε / 8) hquarter_pos
            let S : ℕ → ℝ :=
              fun n => (Finset.range n).sum fun k => scaledZ Y Z k ω
            have h_tail_bound :
                ∀ t ≥ N,
                  ((Finset.Icc N t).sum fun k => scaledZ Y Z k ω) ≤ ε / 4 := by
              intro t ht
              classical
              -- Control the partial sums at indices `t + 1` and `N`.
              have ht_le : N ≤ t + 1 := Nat.le_trans ht (Nat.le_succ t)
              have hdist_t :
                  |S (t + 1) - ∑' k, scaledZ Y Z k ω| < ε / 8 := by
                have := hN (t + 1) ht_le
                simpa [S, Real.dist_eq, Metric.mem_ball] using this
              have hdist_N :
                  |S N - ∑' k, scaledZ Y Z k ω| < ε / 8 := by
                have := hN N le_rfl
                simpa [S, Real.dist_eq, Metric.mem_ball] using this
              -- Tail expression in terms of partial sums.
              have hsplit :
                  S (t + 1)
                    = S N + (Finset.Icc N t).sum (fun k => scaledZ Y Z k ω) := by
                have hsplit' :
                    (Finset.range (t + 1)).sum (fun k => scaledZ Y Z k ω)
                      = (Finset.range N).sum (fun k => scaledZ Y Z k ω)
                        + (Finset.Ico N (t + 1)).sum (fun k => scaledZ Y Z k ω) := by
                  simpa [S] using
                    (Finset.sum_range_add_sum_Ico
                      (fun k => scaledZ Y Z k ω) ht_le).symm
                have hset :
                    Finset.Ico N (t + 1) = Finset.Icc N t := by
                  ext k; constructor
                  · intro hk
                    rcases Finset.mem_Ico.1 hk with ⟨hk_le, hk_lt⟩
                    have hk_le_t : k ≤ t := Nat.le_of_lt_succ hk_lt
                    exact Finset.mem_Icc.2 ⟨hk_le, hk_le_t⟩
                  · intro hk
                    rcases Finset.mem_Icc.1 hk with ⟨hk_le, hk_ge⟩
                    have hk_lt : k < t + 1 := Nat.lt_succ_of_le hk_ge
                    exact Finset.mem_Ico.2 ⟨hk_le, hk_lt⟩
                simpa [S, hset, add_comm, add_left_comm, add_assoc] using hsplit'
              -- Bound the tail by comparing to the limit.
              have htail_eq :
                  (Finset.Icc N t).sum (fun k => scaledZ Y Z k ω)
                    = S (t + 1) - S N := by
                calc
                  (Finset.Icc N t).sum (fun k => scaledZ Y Z k ω)
                      = (S N + (Finset.Icc N t).sum (fun k => scaledZ Y Z k ω)) - S N := by
                        ring
                  _ = S (t + 1) - S N := by
                        simpa [S, hsplit, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
              have htail_nonneg :
                  0 ≤ (Finset.Icc N t).sum (fun k => scaledZ Y Z k ω) :=
                Finset.sum_nonneg (by
                  intro k hk
                  exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω)
              have htriangle :
                  |S (t + 1) - S N|
                      ≤ |S (t + 1) - ∑' k, scaledZ Y Z k ω|
                        + |∑' k, scaledZ Y Z k ω - S N| := by
                simpa [abs_sub_comm] using
                  (abs_sub_le (S (t + 1)) (∑' k, scaledZ Y Z k ω) (S N))
              have hsum_lt :
                  |S (t + 1) - ∑' k, scaledZ Y Z k ω|
                      + |∑' k, scaledZ Y Z k ω - S N| < ε / 4 := by
                have hhalf : ε / 8 + ε / 8 = ε / 4 := by ring
                have :=
                  add_lt_add hdist_t (by simpa [abs_sub_comm] using hdist_N)
                simpa [hhalf] using this
              have habs_tail :
                  |(Finset.Icc N t).sum (fun k => scaledZ Y Z k ω)| ≤ ε / 4 := by
                have habs :=
                  htriangle.trans (le_of_lt hsum_lt)
                simpa [htail_eq] using habs
              simpa [abs_of_nonneg htail_nonneg] using habs_tail
            -- Use this `T₀` to control both the tail and the compensator error.
            -- Conditional expectation convergence bound.
            have hcond_bound :
                ∀ t ≥ N,
                  |μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
                      - B_trunc Y Z N N ω| < ε / 4 := by
              intro t ht
              -- For `t ≥ N`, the conditional expectation is constant.
              have hmeas :
                  StronglyMeasurable[ℱ t] (B_trunc Y Z N N) :=
                ((B_trunc_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
                  adapted_Y adapted_Z predictable_Z) N N).mono (ℱ.mono ht)
              have hint :
                  Integrable (B_trunc Y Z N N) μ :=
                integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
                  adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N N
              have hcond_eq :
                  μ[fun ω' => B_trunc Y Z N N ω' | ℱ t]
                    = B_trunc Y Z N N := by
                refine MeasureTheory.condExp_of_stronglyMeasurable
                  (μ := μ) (m := ℱ t) (hm := ℱ.le t)
                  (f := fun ω' => B_trunc Y Z N N ω') hmeas hint
              have hpos : 0 < ε / 4 := by
                have : (0 : ℝ) < 4 := by norm_num
                exact div_pos hε this
              simpa [hcond_eq, abs_zero] using hpos
            exact ⟨N, h_tail_bound, hcond_bound⟩
        -- Assemble the a.e. statement hlim_exists from the pointwise lemma and the a.e. inputs.
        have hlim_exists : ∀ᵐ ω ∂μ,
            ∃ c : ℝ,
              (Filter.Tendsto (fun t => scaledS X Y W t ω)
                 Filter.atTop (nhds c)) ∧ Summable (fun t => W t ω) := by
          filter_upwards [summable_Y, summable_Z] with ω hYsum hZsum
          exact robbinsSiegmund_pointwise ω hYsum hZsum
        exact hlim_exists
      exact hSlim
  -- Idea for h_subconv: from h_super we know Scomp_trunc_stop N is a supermartingale; negate
  -- to get a submartingale and apply Submartingale.ae_tendsto_limitProcess with an explicit L¹ bound.
  -- Implemented next.
  -- Construct the submartingale for the negated stopped compensated process and
  -- apply the a.s. convergence theorem under an L¹ bound.
  have h_subconv : ∀ N, ∃ L_N : Ω → ℝ,
      (∀ᵐ ω ∂μ,
        Filter.Tendsto (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t ω)
          Filter.atTop (nhds (L_N ω))) := by
    intro N
    classical
    -- From supermartingale to submartingale via negation
    have h_subm : Submartingale (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t) ℱ μ := by
      simpa using (h_super N).neg
    -- Build an explicit uniform L¹ bound as an NNReal using the same decomposition
    -- as in eLpNorm_Scomp_trunc_stop_bdd, then apply the submartingale convergence theorem.
    -- Define the ENNReal bound from the decomposition
    let Rscaled : ENNReal :=
      (Finset.range (N + 1)).sum (fun k => eLpNorm (scaledS X Y W k) 1 μ)
    let RboundE : ENNReal := Rscaled + 2 * eLpNorm (B_trunc Y Z N N) 1 μ
    -- Show the basic L¹ bound for Scomp_trunc_stop as in the lemma
    have h_bound_E : ∀ t : ℕ,
        eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ ≤ RboundE := by
      intro t
      -- Notation for the three components
      let f : Ω → ℝ := fun ω => scaledS X Y W (Nat.min t N) ω
      let g : Ω → ℝ := fun ω => μ[fun ω' => B_trunc Y Z N N ω' | ℱ t] ω
      let h : Ω → ℝ := fun ω => B_trunc Y Z N t ω
      -- Integrability and measurability of pieces
      have hf_int : Integrable f μ :=
        integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W (Nat.min t N)
      have hg_int : Integrable g μ :=
        integrable_condExp (μ := μ) (m := ℱ t) (f := fun ω => B_trunc Y Z N N ω)
      have hh_int : Integrable h μ :=
        integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N t
      have hfg_aes : AEStronglyMeasurable (f + g) μ :=
        (hf_int.aestronglyMeasurable.add hg_int.aestronglyMeasurable)
      have hh_aes : AEStronglyMeasurable h μ := hh_int.aestronglyMeasurable
      have h_sub : eLpNorm ((fun ω => f ω + g ω) - h) 1 μ
          ≤ eLpNorm (fun ω => f ω + g ω) 1 μ + eLpNorm h 1 μ := by
        simpa [sub_eq_add_neg] using
          (eLpNorm_sub_le (μ := μ) (p := (1 : ENNReal)) hfg_aes hh_aes (by simp))
      have h_add : eLpNorm (fun ω => f ω + g ω) 1 μ
          ≤ eLpNorm f 1 μ + eLpNorm g 1 μ := by
        simpa using
          (eLpNorm_add_le (μ := μ) (p := (1 : ENNReal)) hf_int.aestronglyMeasurable
            hg_int.aestronglyMeasurable (by simp))
      have h1 : eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ
          ≤ eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ := by
        calc
          eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ
              = eLpNorm ((fun ω => f ω + g ω) - h) 1 μ := rfl
          _ ≤ eLpNorm (fun ω => f ω + g ω) 1 μ + eLpNorm h 1 μ := h_sub
          _ ≤ (eLpNorm f 1 μ + eLpNorm g 1 μ) + eLpNorm h 1 μ := by
                exact add_le_add_right h_add _
          _ = eLpNorm f 1 μ + eLpNorm g 1 μ + eLpNorm h 1 μ := by
                ac_rfl
      -- Bound each term by RboundE components
      -- (i) scaledS(min t N) ≤ sum_{k≤N} eLpNorm (scaledS k)
      have h_scaled_le : eLpNorm f 1 μ ≤ Rscaled := by
        have hmem : Nat.min t N ∈ Finset.range (N + 1) := by
          have : Nat.min t N ≤ N := Nat.min_le_right t N
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
        have hnonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ eLpNorm (scaledS X Y W k) 1 μ := by
          intro k hk; exact zero_le _
        simpa [Rscaled] using
          (Finset.single_le_sum (f := fun k => eLpNorm (scaledS X Y W k) 1 μ) hnonneg hmem)
      -- (ii) contraction for conditional expectation
      have h_condexp_le : eLpNorm g 1 μ ≤ eLpNorm (B_trunc Y Z N N) 1 μ := by
        simpa using
          (MeasureTheory.eLpNorm_one_condExp_le_eLpNorm (μ := μ) (m := ℱ t)
            (f := fun ω => B_trunc Y Z N N ω))
      -- (iii) monotonicity B_trunc N t ≤ B_trunc N N pointwise ⇒ L¹ monotonicity
      have h_Btrunc_le : eLpNorm h 1 μ ≤ eLpNorm (B_trunc Y Z N N) 1 μ := by
        refine MeasureTheory.eLpNorm_mono_real (μ := μ) (p := (1 : ENNReal)) ?_
        intro ω
        have hnon1 : 0 ≤ B_trunc Y Z N t ω :=
          B_trunc_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N t ω
        have hnon2 : 0 ≤ B_trunc Y Z N N ω :=
          B_trunc_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N N ω
        have hle := B_trunc_le_BN (Y := Y) (Z := Z) hY_nonneg hZ_nonneg N t ω
        simpa [h, Real.norm_eq_abs, abs_of_nonneg hnon1, abs_of_nonneg hnon2] using hle
      -- Collect
      have : eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ
            ≤ Rscaled + eLpNorm (B_trunc Y Z N N) 1 μ + eLpNorm (B_trunc Y Z N N) 1 μ := by
        have := add_le_add (add_le_add h_scaled_le h_condexp_le) h_Btrunc_le
        exact h1.trans this
      -- Finalize with the definition of RboundE
      have hRdef : Rscaled + eLpNorm (B_trunc Y Z N N) 1 μ + eLpNorm (B_trunc Y Z N N) 1 μ
            = RboundE := by
        simp [RboundE, two_mul, add_comm, add_left_comm, add_assoc]
      simpa [hRdef]
    -- RboundE is finite; promote to an NNReal bound R
    have h_fin_scaled : Rscaled ≠ ⊤ := by
      classical
      -- show each term has finite eLpNorm, then use `sum_ne_top`
      have hterm : ∀ k ∈ Finset.range (N + 1), eLpNorm (scaledS X Y W k) 1 μ ≠ ⊤ := by
        intro k hk
        have hint : Integrable (scaledS X Y W k) μ :=
          integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
            adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W k
        -- Integrable f means HasFiniteIntegral f, which gives eLpNorm f 1 μ < ⊤
        have hfin : HasFiniteIntegral (scaledS X Y W k) μ := hint.2
        simp only [eLpNorm, one_ne_zero, ENNReal.one_ne_top, ite_false, eLpNorm',
          ENNReal.toReal_one, one_div, inv_one, ENNReal.rpow_one]
        exact hfin.ne
      simpa [Rscaled] using (ENNReal.sum_ne_top.2 hterm)
    have h_fin_B : eLpNorm (B_trunc Y Z N N) 1 μ ≠ ⊤ := by
      have hint : Integrable (B_trunc Y Z N N) μ :=
        integrable_B_trunc (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z N N
      -- Integrable f means HasFiniteIntegral f, which gives eLpNorm f 1 μ < ⊤
      have hfin : HasFiniteIntegral (B_trunc Y Z N N) μ := hint.2
      simp only [eLpNorm, one_ne_zero, ENNReal.one_ne_top, ite_false, eLpNorm',
        ENNReal.toReal_one, one_div, inv_one, ENNReal.rpow_one]
      exact hfin.ne
    have h_fin_R : RboundE ≠ ⊤ := by
      -- sum of finite ENNReal values is finite
      have : (2 : ENNReal) * eLpNorm (B_trunc Y Z N N) 1 μ ≠ ⊤ := by
        have h2fin : (2 : ENNReal) ≠ ⊤ := by simp
        exact ENNReal.mul_ne_top h2fin h_fin_B
      exact ENNReal.add_ne_top.mpr ⟨h_fin_scaled, this⟩
    -- Define an NNReal bound above RboundE
    let R : NNReal := ⟨RboundE.toReal + 1, by
      have : 0 ≤ RboundE.toReal := ENNReal.toReal_nonneg
      have : 0 ≤ RboundE.toReal + 1 := add_nonneg this (by norm_num)
      exact this⟩
    have hR_coe : (RboundE ≤ (R : ENNReal)) := by
      -- since RboundE is finite, coe_toReal
      have hrepr : (ENNReal.ofReal RboundE.toReal) = RboundE := by
        simpa [ENNReal.ofReal_toReal, h_fin_R] using rfl
      have : ENNReal.ofReal RboundE.toReal ≤ ENNReal.ofReal (RboundE.toReal + 1) := by
        apply ENNReal.ofReal_le_ofReal
        linarith
      calc RboundE = ENNReal.ofReal RboundE.toReal := hrepr.symm
        _ ≤ ENNReal.ofReal (RboundE.toReal + 1) := this
        _ = ↑R := by
          dsimp only [R]
          -- Goal: ENNReal.ofReal (RboundE.toReal + 1) = ↑⟨RboundE.toReal + 1, _⟩
          -- Use ENNReal.coe_nnreal_eq: ↑r = ENNReal.ofReal ↑r
          rw [ENNReal.coe_nnreal_eq]
          -- Now need: ENNReal.ofReal (RboundE.toReal + 1) = ENNReal.ofReal ↑⟨RboundE.toReal + 1, _⟩
          -- Since (⟨x, h⟩ : ℝ) = x for NNReal
          congr
    -- Now bound the negated process uniformly in L¹ by ↑R
    have hR_neg : ∀ t, eLpNorm (fun ω => - Scomp_trunc_stop μ ℱ X Y Z W N t ω) 1 μ ≤ (R : ENNReal) := by
      intro t
      have hmono :
          MeasureTheory.eLpNorm (fun ω => - Scomp_trunc_stop μ ℱ X Y Z W N t ω) 1 μ
            ≤ MeasureTheory.eLpNorm (Scomp_trunc_stop μ ℱ X Y Z W N t) 1 μ := by
        refine MeasureTheory.eLpNorm_mono_ae (μ := μ) (p := (1 : ENNReal)) ?_
        filter_upwards with ω
        rw [norm_neg]
      exact (hmono.trans (h_bound_E t)).trans hR_coe
    -- Apply the submartingale convergence theorem to obtain the a.e. limit
    have h_tend : ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun t => - Scomp_trunc_stop μ ℱ X Y Z W N t ω)
          Filter.atTop (nhds (Filtration.limitProcess (fun t ω => - Scomp_trunc_stop μ ℱ X Y Z W N t ω) ℱ μ ω)) := by
      -- `Submartingale.ae_tendsto_limitProcess` requires an NNReal bound
      simpa using (Submartingale.ae_tendsto_limitProcess (μ := μ) (ℱ := ℱ)
        (f := fun t ω => - Scomp_trunc_stop μ ℱ X Y Z W N t ω) (R := R) h_subm hR_neg)
    -- Package the limit function
    refine ⟨(fun ω => Filtration.limitProcess (fun t ω => - Scomp_trunc_stop μ ℱ X Y Z W N t ω) ℱ μ ω), h_tend⟩
  exact h_subconv

end Classical

end Stoch
end QLS

namespace QLS
namespace Stoch
namespace Classical

open MeasureTheory Filter

/-- Robbins–Siegmund variant under expectation-level summability and a uniform product bound.

Assumptions:
- Adaptedness/predictability for `X,Y,Z,W` as in the main theorem
- Nonnegativity: `0 ≤ X t ω, 0 ≤ Y t ω, 0 ≤ Z t ω, 0 ≤ W t ω`
- Integrability: `X t, Z t, W t` integrable for all `t`
- Drift: `μ[X_{t+1} | ℱ_t] ≤ (1+Y_{t+1}) X_t + Z_{t+1} - W_{t+1}` a.e.
- Expectation summability: `Summable (fun t => ∫ ω, Z t ω ∂μ)`
- Product bound: `∃ C > 0, ∀ t ω, prodY Y t ω ≤ C`

Conclusions:
- `X t` converges almost surely to a finite limit
- `∑ W t` is finite almost surely
-/
theorem robbinsSiegmund_expBound
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m0)
    (X Y Z W : ℕ → Ω → ℝ)
    (adapted_X : Adapted ℱ X) (adapted_Y : Adapted ℱ Y)
    (adapted_Z : Adapted ℱ Z) (adapted_W : Adapted ℱ W)
    (predictable_Y : Adapted ℱ fun t => Y (t + 1))
    (predictable_Z : Adapted ℱ fun t => Z (t + 1))
    (predictable_W : Adapted ℱ fun t => W (t + 1))
    (hX_nonneg : ∀ t ω, 0 ≤ X t ω)
    (hY_nonneg : ∀ t ω, 0 ≤ Y t ω)
    (hZ_nonneg : ∀ t ω, 0 ≤ Z t ω)
    (hW_nonneg : ∀ t ω, 0 ≤ W t ω)
    (condexp_ineq : ∀ t,
      μ[fun ω => X (t + 1) ω | ℱ t]
        ≤ᵐ[μ] fun ω => (1 + Y (t + 1) ω) * X t ω + Z (t + 1) ω - W (t + 1) ω)
    (integrable_X : ∀ t, Integrable (X t) μ)
    (integrable_Z : ∀ t, Integrable (Z t) μ)
    (integrable_W : ∀ t, Integrable (W t) μ)
    (sumEZ : Summable (fun t => ∫ ω, Z t ω ∂μ))
    (prod_bound : ∃ C : ℝ, 0 < C ∧ ∀ t ω, prodY Y t ω ≤ C)
  : ∃ Xlim : Ω → ℝ,
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun t => X t ω) Filter.atTop (nhds (Xlim ω))) ∧
      (∀ᵐ ω ∂μ, Summable (fun t => W t ω)) := by
  classical
  -- Plan A skeleton: Mpred convergence via L¹ bound and Zsum convergence a.e.,
  -- then summability of W from product bound and S convergence.
  -- This is a high-level variant to accompany the paper's expectation-summability statement.
  -- Full formal details reuse `Mpred_supermartingale` and `eLpNorm_Mpred_le` from above.
  -- Step 1: Integrate the normalized drift inequality to get an expectation recursion.
  have h_step_int : ∀ t,
      (∫ ω, scaledS X Y W (t + 1) ω ∂μ)
        ≤ (∫ ω, scaledS X Y W t ω ∂μ)
            + (∫ ω, Z (t + 1) ω ∂μ) := by
    intro t
    classical
    -- condexp inequality for scaledS
    have h :=
      (condexp_scaledS_step (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
        (predictable_Y) (adapted_W) (predictable_W)
        hY_nonneg hW_nonneg condexp_ineq integrable_X integrable_W t)
    -- Both sides integrable
    have hL_int : Integrable (μ[fun ω' => scaledS X Y W (t + 1) ω' | ℱ t]) μ :=
      integrable_condExp (μ := μ) (m := ℱ t)
        (f := fun ω => scaledS X Y W (t + 1) ω)
    -- Integrable RHS via integrable of scaledS and domination for Z/(P_{t+1})
    have hZnext_meas : AEStronglyMeasurable (fun ω => Z (t + 1) ω / prodY Y (t + 1) ω) μ := by
      have hsm : StronglyMeasurable[ℱ (t + 1)] (scaledZ_next Y Z t) :=
        scaledZ_next_measurable (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y (predictable_Y) adapted_Z t
      exact (hsm.mono (ℱ.le (t + 1))).aestronglyMeasurable
    have hZnext_int : Integrable (fun ω => Z (t + 1) ω / prodY Y (t + 1) ω) μ := by
      have hdom : Integrable (fun ω => |Z (t + 1) ω|) μ := (integrable_Z (t + 1)).abs
      have hbound : ∀ᵐ ω ∂μ,
          ‖Z (t + 1) ω / prodY Y (t + 1) ω‖ ≤ ‖|Z (t + 1) ω|‖ := by
        refine ae_of_all μ (fun ω => ?_)
        have hge1 : 1 ≤ prodY Y (t + 1) ω := prodY_ge_one (Y := Y) hY_nonneg (t + 1) ω
        have hpos : 0 < prodY Y (t + 1) ω := prodY_pos (Y := Y) hY_nonneg (t + 1) ω
        have : |Z (t + 1) ω| / |prodY Y (t + 1) ω| ≤ |Z (t + 1) ω| := by
          rw [abs_of_pos hpos]
          have : |Z (t + 1) ω| ≤ |Z (t + 1) ω| * prodY Y (t + 1) ω := by
            have hZnn : 0 ≤ |Z (t + 1) ω| := abs_nonneg _
            simpa [one_mul] using (mul_le_mul_of_nonneg_left hge1 hZnn)
          exact (div_le_iff₀ hpos).mpr this
        simpa [Real.norm_eq_abs, abs_abs] using this
      exact Integrable.mono hdom hZnext_meas hbound
    have hR_int : Integrable
        (fun ω => scaledS X Y W t ω + Z (t + 1) ω / prodY Y (t + 1) ω) μ := by
      have h1 :=
        integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
      exact h1.add hZnext_int
    -- Integrate both sides: ∫ condExp ≤ ∫ (...)
    have hint :=
      (MeasureTheory.integral_mono_ae (μ := μ)
        (f := fun ω => μ[fun ω' => scaledS X Y W (t + 1) ω' | ℱ t] ω)
        (g := fun ω => scaledS X Y W t ω + Z (t + 1) ω / prodY Y (t + 1) ω)
        (hf := hL_int) (hg := hR_int) (h := h))
    -- Rewrite ∫ condExp = ∫ original and bound Z/(P_{t+1}) by Z
    have hcond :
        ∫ ω, μ[fun ω' => scaledS X Y W (t + 1) ω' | ℱ t] ω ∂μ
          = ∫ ω, scaledS X Y W (t + 1) ω ∂μ := by
      simpa using
        (MeasureTheory.integral_condExp (μ := μ) (m := ℱ t) (hm := ℱ.le t)
          (f := fun ω => scaledS X Y W (t + 1) ω))
    -- Pointwise bound: Z/(P_{t+1}) ≤ Z since P_{t+1} ≥ 1
    have hpt : ∀ ω, Z (t + 1) ω / prodY Y (t + 1) ω ≤ Z (t + 1) ω := by
      intro ω
      have hge1 : 1 ≤ prodY Y (t + 1) ω := prodY_ge_one (Y := Y) hY_nonneg (t + 1) ω
      have hpos : 0 < prodY Y (t + 1) ω := prodY_pos (Y := Y) hY_nonneg (t + 1) ω
      have hmul : Z (t + 1) ω / prodY Y (t + 1) ω ≤ Z (t + 1) ω := by
        have hZnn : 0 ≤ Z (t + 1) ω := hZ_nonneg (t + 1) ω
        -- z/p ≤ z for z ≥ 0 and p ≥ 1
        have : Z (t + 1) ω ≤ Z (t + 1) ω * prodY Y (t + 1) ω := by
          simpa [one_mul] using (mul_le_mul_of_nonneg_left hge1 hZnn)
        simpa [div_eq_mul_inv] using ( (div_le_iff₀ hpos).mpr this )
      simpa using hmul
    have hZint :
        ∫ ω, Z (t + 1) ω / prodY Y (t + 1) ω ∂μ ≤ ∫ ω, Z (t + 1) ω ∂μ := by
      exact (MeasureTheory.integral_mono_ae (μ := μ)
        (f := fun ω => Z (t + 1) ω / prodY Y (t + 1) ω)
        (g := fun ω => Z (t + 1) ω)
        (hf := hZnext_int) (hg := integrable_Z (t + 1)) (h := ae_of_all μ hpt))
    -- Conclude the step inequality
    have hsplit : ∫ ω, scaledS X Y W t ω + Z (t + 1) ω / prodY Y (t + 1) ω ∂μ
        = (∫ ω, scaledS X Y W t ω ∂μ) + (∫ ω, Z (t + 1) ω / prodY Y (t + 1) ω ∂μ) := by
      have h1 := integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
        adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
      exact MeasureTheory.integral_add h1 hZnext_int
    have := calc
      ∫ ω, scaledS X Y W (t + 1) ω ∂μ
          = ∫ ω, μ[fun ω' => scaledS X Y W (t + 1) ω' | ℱ t] ω ∂μ := by rw [← hcond]
      _ ≤ ∫ ω, scaledS X Y W t ω + Z (t + 1) ω / prodY Y (t + 1) ω ∂μ := hint
      _ = (∫ ω, scaledS X Y W t ω ∂μ) + (∫ ω, Z (t + 1) ω / prodY Y (t + 1) ω ∂μ) := hsplit
      _ ≤ (∫ ω, scaledS X Y W t ω ∂μ) + (∫ ω, Z (t + 1) ω ∂μ) := add_le_add le_rfl hZint
    exact this
  -- Step 2: bound E[scaledS t] by the initial value + partial sums of E[Z]
  have h_scaledS_bound : ∀ t,
      (∫ ω, scaledS X Y W t ω ∂μ)
        ≤ (∫ ω, scaledS X Y W 0 ω ∂μ) + Finset.sum (Finset.range t) (fun k => ∫ ω, Z (k + 1) ω ∂μ) := by
    intro t; classical
    induction' t with n ih
    · simp
    · have := h_step_int n
      have :=
        calc
          (∫ ω, scaledS X Y W (n + 1) ω ∂μ)
              ≤ (∫ ω, scaledS X Y W n ω ∂μ) + (∫ ω, Z (n + 1) ω ∂μ) := this
          _ ≤ (∫ ω, scaledS X Y W 0 ω ∂μ)
                + Finset.sum (Finset.range n) (fun k => ∫ ω, Z (k + 1) ω ∂μ)
                + (∫ ω, Z (n + 1) ω ∂μ) := by exact add_le_add_right ih _
          _ = (∫ ω, scaledS X Y W 0 ω ∂μ)
                + Finset.sum (Finset.range (n + 1)) (fun k => ∫ ω, Z (k + 1) ω ∂μ) := by
                simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      simpa using this
  -- Step 3: bound E[Zsum t] by partial sums of E[Z]
  have h_Zsum_bound : ∀ t,
      (∫ ω, Zsum Y Z t ω ∂μ)
        ≤ Finset.sum (Finset.range t) (fun k => ∫ ω, Z (k + 1) ω ∂μ) := by
    intro t; classical
    -- ∫ Zsum = sum of ∫ scaledZ and termwise compare
    have hsplit : ∫ ω, Zsum Y Z t ω ∂μ
        = Finset.sum (Finset.range t) (fun k => ∫ ω, scaledZ Y Z k ω ∂μ) := by
      have hint : ∀ i ∈ Finset.range t, Integrable (fun ω => scaledZ Y Z i ω) μ := by
        intro i hi
        exact integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z i
      simpa [Zsum] using MeasureTheory.integral_finset_sum (Finset.range t) hint
    have hterm : ∀ k ∈ Finset.range t,
        (∫ ω, scaledZ Y Z k ω ∂μ) ≤ (∫ ω, Z (k + 1) ω ∂μ) := by
      intro k hk
      -- pointwise scaledZ ≤ Z_{k+1}
      have hpt : ∀ ω, scaledZ Y Z k ω ≤ Z (k + 1) ω := by
        intro ω
        have hge1 : 1 ≤ prodY Y k ω := prodY_ge_one (Y := Y) hY_nonneg k ω
        have hpos : 0 < prodY Y k ω := prodY_pos (Y := Y) hY_nonneg k ω
        have hmul : Z (k + 1) ω ≤ Z (k + 1) ω * prodY Y k ω := by
          simpa [one_mul] using (mul_le_mul_of_nonneg_left hge1 (hZ_nonneg (k + 1) ω))
        simpa [scaledZ] using ( (div_le_iff₀ hpos).mpr hmul )
      have hf : Integrable (scaledZ Y Z k) μ :=
        integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z k
      have hg : Integrable (Z (k + 1)) μ := integrable_Z (k + 1)
      exact (MeasureTheory.integral_mono_ae (μ := μ)
        (f := fun ω => scaledZ Y Z k ω) (g := fun ω => Z (k + 1) ω)
        (hf := hf) (hg := hg) (h := ae_of_all μ hpt))
    have := Finset.sum_le_sum hterm
    simpa [hsplit] using this
  -- Step 4: build a uniform L¹ bound for `-Mpred` and conclude submartingale convergence
  let E0 : ℝ := (∫ ω, scaledS X Y W 0 ω ∂μ)
  let EZsum : ℝ := (∑' k, ∫ ω, Z k ω ∂μ)
  -- Nonnegativity of these real bounds
  have hE0_nn : 0 ≤ E0 := by
    -- scaledS ≥ 0 by assumptions, hence its integral is ≥ 0
    have hpt : ∀ ω, 0 ≤ scaledS X Y W 0 ω := by
      intro ω
      have hx := hX_nonneg 0 ω
      have hw := cumW_nonneg (W := W) hW_nonneg 0 ω
      have hden := (prodY_pos (Y := Y) hY_nonneg 0 ω).le
      have hnum : 0 ≤ X 0 ω + cumW W 0 ω := add_nonneg hx hw
      -- scaledS 0 = (X 0 + cumW 0)/prodY 0
      simpa [scaledS] using (div_nonneg hnum hden)
    have : 0 ≤ᵐ[μ] scaledS X Y W 0 := ae_of_all μ hpt
    simpa [E0] using MeasureTheory.integral_nonneg_of_ae this
  have hEZsum_nn : 0 ≤ EZsum := by
    -- Each term is ≥ 0, so the tsum is ≥ 0
    have hnn : ∀ k, 0 ≤ (∫ ω, Z k ω ∂μ) := by
      intro k; exact MeasureTheory.integral_nonneg_of_ae (ae_of_all μ (by intro ω; exact hZ_nonneg k ω))
    exact tsum_nonneg hnn
  -- Partial sums are bounded by the (finite) total sum of expectations
  have hsum_le_tsum : ∀ t,
      Finset.sum (Finset.range t) (fun k => ∫ ω, Z (k + 1) ω ∂μ) ≤ EZsum := by
    intro t
    classical
    -- Define aₖ := ∫ Z k
    let a : ℕ → ℝ := fun k => ∫ ω, Z k ω ∂μ
    have h_nonneg : ∀ k, 0 ≤ a k := by
      intro k; exact MeasureTheory.integral_nonneg_of_ae (ae_of_all μ (by intro ω; exact hZ_nonneg k ω))
    have hsum_full : (Finset.range (t + 1)).sum a ≤ EZsum := by
      -- by nonnegativity and summability of a
      have ha_sum : Summable a := sumEZ
      simpa using ha_sum.sum_le_tsum (Finset.range (t + 1)) (by intro k hk; exact h_nonneg k)
    -- S_shift = ∑_{k<t} a(k+1) ≤ a 0 + ∑_{k<t} a(k+1) = ∑_{u≤t} a u
    have hsplit_n : ∀ n, (Finset.range (n + 1)).sum a
        = a 0 + (Finset.range n).sum (fun k => a (k + 1)) := by
      intro n; classical
      induction' n with n ih
      · simp [a]
      · calc
          (Finset.range (n + 2)).sum a
              = (Finset.range (n + 1)).sum a + a (n + 1) := by
                    simp [Finset.sum_range_succ]
          _ = (a 0 + (Finset.range n).sum (fun k => a (k + 1))) + a (n + 1) := by
                    simpa [ih]
          _ = a 0 + ((Finset.range n).sum (fun k => a (k + 1)) + a (n + 1)) := by
                    ring
          _ = a 0 + (Finset.range (n + 1)).sum (fun k => a (k + 1)) := by
                    simp [Finset.sum_range_succ]
    have hsplit := hsplit_n t
    have h_le_prefix : (Finset.range t).sum (fun k => a (k + 1)) ≤ (Finset.range (t + 1)).sum a := by
      have h0 : 0 ≤ a 0 := h_nonneg 0
      have : (Finset.range t).sum (fun k => a (k + 1))
          ≤ a 0 + (Finset.range t).sum (fun k => a (k + 1)) := by exact le_add_of_nonneg_left h0
      simpa [hsplit] using this
    exact h_le_prefix.trans hsum_full
  -- L¹ bound for `Mpred t`
  have h_eLpMpred : ∀ t,
      eLpNorm (Mpred X Y Z W t) 1 μ ≤ ENNReal.ofReal (E0 + 2 * EZsum) := by
    intro t
    classical
    have htri := eLpNorm_Mpred_le (μ := μ) (ℱ := ℱ)
      (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Z hY_nonneg hW_nonneg t
    -- bound eLpNorm(scaledS t)
    have hS_int_le : (∫ ω, scaledS X Y W t ω ∂μ) ≤ E0 + EZsum := by
      have := h_scaledS_bound t
      exact le_trans this (add_le_add_left (hsum_le_tsum t) E0)
    have hZs_int_le : (∫ ω, Zsum Y Z t ω ∂μ) ≤ EZsum := by
      exact le_trans (h_Zsum_bound t) (hsum_le_tsum t)
    have hS_eLp : eLpNorm (scaledS X Y W t) 1 μ ≤ ENNReal.ofReal (E0 + EZsum) := by
      -- for nonnegative functions, L¹ norm equals integral (use hS_int_le)
      have hS_nonneg : 0 ≤ᵐ[μ] scaledS X Y W t := by
        apply ae_of_all
        intro ω
        have hx := hX_nonneg t ω
        have hw := cumW_nonneg (W := W) hW_nonneg t ω
        have hden := (prodY_pos (Y := Y) hY_nonneg t ω).le
        have hnum : 0 ≤ X t ω + cumW W t ω := add_nonneg hx hw
        simpa [scaledS] using (div_nonneg hnum hden)
      have hS_int : Integrable (scaledS X Y W t) μ :=
        integrable_scaledS (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (W := W)
          adapted_X adapted_Y adapted_W hY_nonneg hW_nonneg integrable_X integrable_W t
      -- Convert eLpNorm to lintegral, then to ofReal integral
      rw [eLpNorm_one_eq_lintegral_enorm]
      have h_enorm : (∫⁻ x, ‖scaledS X Y W t x‖ₑ ∂μ) = ∫⁻ x, ENNReal.ofReal (scaledS X Y W t x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hS_nonneg] with ω hω
        exact Real.enorm_of_nonneg hω
      rw [h_enorm, ← ofReal_integral_eq_lintegral_ofReal hS_int hS_nonneg]
      exact ENNReal.ofReal_le_ofReal hS_int_le
    have hZs_eLp : eLpNorm (Zsum Y Z t) 1 μ ≤ ENNReal.ofReal EZsum := by
      -- nonnegativity of Zsum and hZs_int_le
      have hZs_nonneg : 0 ≤ᵐ[μ] Zsum Y Z t := by
        apply ae_of_all
        intro ω
        simp [Zsum]
        apply Finset.sum_nonneg
        intro k _
        have := hZ_nonneg (k + 1) ω
        have hden := (prodY_pos (Y := Y) hY_nonneg k ω).le
        simpa [scaledZ] using (div_nonneg this hden)
      have hZs_int : Integrable (Zsum Y Z t) μ :=
        integrable_Zsum (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
          adapted_Y predictable_Z adapted_Z hY_nonneg hZ_nonneg integrable_Z t
      -- Convert eLpNorm to lintegral, then to ofReal integral
      rw [eLpNorm_one_eq_lintegral_enorm]
      have h_enorm : (∫⁻ x, ‖Zsum Y Z t x‖ₑ ∂μ) = ∫⁻ x, ENNReal.ofReal (Zsum Y Z t x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hZs_nonneg] with ω hω
        exact Real.enorm_of_nonneg hω
      rw [h_enorm, ← ofReal_integral_eq_lintegral_ofReal hZs_int hZs_nonneg]
      exact ENNReal.ofReal_le_ofReal hZs_int_le
    -- Algebra in ℝ≥0∞ via `ofReal_add` and `two_mul`
    have hsum_eq : ENNReal.ofReal (E0 + EZsum) + ENNReal.ofReal EZsum
        = ENNReal.ofReal (E0 + 2 * EZsum) := by
      simp [ENNReal.ofReal_add, hE0_nn, hEZsum_nn, two_mul, add_comm, add_left_comm, add_assoc]
    have hsum_bd : ENNReal.ofReal (E0 + EZsum) + ENNReal.ofReal EZsum
        ≤ ENNReal.ofReal (E0 + 2 * EZsum) := by
      simpa [hsum_eq]
    have : eLpNorm (Mpred X Y Z W t) 1 μ
        ≤ ENNReal.ofReal (E0 + EZsum) + ENNReal.ofReal EZsum :=
      htri.trans (add_le_add hS_eLp hZs_eLp)
    exact this.trans hsum_bd
  -- Convert to a uniform NNReal bound for `-Mpred`
  let R : NNReal := ⟨(E0 + 2 * EZsum) + 1, by linarith⟩
  have h_eLp_bound : ∀ t, eLpNorm (fun ω => - Mpred X Y Z W t ω) 1 μ ≤ (R : ENNReal) := by
    intro t
    -- use monotonicity under negation and the previous bound
    have hneg : eLpNorm (fun ω => - Mpred X Y Z W t ω) 1 μ
        ≤ eLpNorm (Mpred X Y Z W t) 1 μ := by
      refine MeasureTheory.eLpNorm_mono_ae (μ := μ) (p := (1 : ENNReal)) ?_
      filter_upwards with ω; simp
    exact (hneg.trans (h_eLpMpred t)).trans (by
      -- simple monotonicity: ofReal (E0 + 2*EZsum) ≤ R = E0 + 2*EZsum + 1
      simp only [R]
      have h_le : E0 + 2 * EZsum ≤ (E0 + 2 * EZsum) + 1 := by linarith
      have h_nn : 0 ≤ (E0 + 2 * EZsum) + 1 := by linarith
      rw [show (⟨(E0 + 2 * EZsum) + 1, h_nn⟩ : NNReal) = ⟨(E0 + 2 * EZsum) + 1, h_nn⟩ from rfl]
      simp [ENNReal.coe_nnreal_eq, ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal h_le)
  -- Submartingale convergence for `-Mpred`
  have h_subm : Submartingale (fun t => - Mpred X Y Z W t) ℱ μ := by
    have hsup := Mpred_supermartingale (μ := μ) (ℱ := ℱ) (X := X) (Y := Y) (Z := Z) (W := W)
      adapted_X adapted_Y adapted_Z adapted_W predictable_Y predictable_Z predictable_W
      hY_nonneg hZ_nonneg hW_nonneg condexp_ineq integrable_X integrable_Z integrable_W
    simpa using hsup.neg
  have hM_tend : ∀ᵐ ω ∂μ,
      Tendsto (fun t => - Mpred X Y Z W t ω) atTop
        (nhds (Filtration.limitProcess (fun t ω => - Mpred X Y Z W t ω) ℱ μ ω)) := by
    simpa using (Submartingale.ae_tendsto_limitProcess (μ := μ) (ℱ := ℱ)
      (f := fun t ω => - Mpred X Y Z W t ω) (R := R) h_subm h_eLp_bound)
  -- Monotonicity and nonnegativity for `Zsum` (partial sums of nonnegative increments)
  have hZsum_mono : ∀ ω, Monotone (fun t => Zsum Y Z t ω) := by
    intro ω t s hts
    classical
    -- split the larger range into the smaller range plus a nonnegative tail
    have hsplit :
        (Finset.range s).sum (fun k => scaledZ Y Z k ω)
          = (Finset.range t).sum (fun k => scaledZ Y Z k ω)
            + (Finset.Ico t s).sum (fun k => scaledZ Y Z k ω) := by
      simpa using
        (Finset.sum_range_add_sum_Ico (fun k => scaledZ Y Z k ω) hts).symm
    have htail_nonneg : 0 ≤ (Finset.Ico t s).sum (fun k => scaledZ Y Z k ω) := by
      apply Finset.sum_nonneg
      intro k hk
      exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
    -- conclude monotonicity
    have := add_le_add_left htail_nonneg ((Finset.range t).sum (fun k => scaledZ Y Z k ω))
    simpa [Zsum, hsplit, add_comm, add_left_comm, add_assoc] using this
  -- Proof sketch continuation: a.e. convergence of Zsum, then scaledS, then W and X.
  have hZsum_ae_conv : ∀ᵐ ω ∂μ, ∃ LZ : ℝ,
      Tendsto (fun t => Zsum Y Z t ω) atTop (nhds LZ) := by
    -- Reduce to a.e. summability of the nonnegative increments `scaledZ`.
    -- Once `Summable (scaledZ · ω)` holds, partial sums `Zsum · ω` tend to the `tsum`.
    suffices hZsum_ae_sum : ∀ᵐ ω ∂μ, Summable (fun k => scaledZ Y Z k ω) by
      refine hZsum_ae_sum.mono ?_
      intro ω hsum
      classical
      -- Partial sums of a summable series tend to its sum.
      have h_tend :
          Tendsto (fun t => (Finset.range t).sum (fun k => scaledZ Y Z k ω))
            atTop (nhds (∑' k, scaledZ Y Z k ω)) := by
        simpa using hsum.hasSum.tendsto_sum_nat
      refine ⟨(∑' k, scaledZ Y Z k ω), ?_⟩
      simpa [Zsum] using h_tend
    -- A.E. summability of `scaledZ` from expectation-level summability (Plan A hypothesis).
    -- We reduce to a.e. finiteness of the ENNReal-valued series and defer the
    -- final conversion to a real-valued Summable.
    -- We now apply Tonelli/monotone convergence to prove a.e. boundedness of
    -- the partial sums of `scaledZ`, which yields the desired a.e. summability.
    -- Proof sketch with structured sub-goals; some are deferred with `sorry`.
    classical
    -- Define F_k := ofReal (scaledZ_k) in ENNReal and partial sums S_t := ∑_{k<t} F_k
    let F : ℕ → Ω → ENNReal := fun k ω => ENNReal.ofReal (scaledZ Y Z k ω)
    have hF_meas : ∀ k, Measurable (F k) := by
      -- From strong measurability of scaledZ at level ℱ k and `ennreal_ofReal`
      intro k
      have hsm : StronglyMeasurable[ℱ k] (scaledZ Y Z k) :=
        scaledZ_measurable (ℱ := ℱ) (Y := Y) (Z := Z) adapted_Y predictable_Z k
      have hm : Measurable (scaledZ Y Z k) := (hsm.mono (ℱ.le k)).measurable
      simpa [F] using hm.ennreal_ofReal
    have hF_nonneg : ∀ k ω, (0 : ENNReal) ≤ F k ω := by
      intro k ω; simpa [F]
    let S : ℕ → Ω → ENNReal := fun t ω => (Finset.range t).sum (fun k => F k ω)
    have hS_meas : ∀ t, Measurable (S t) := by
      -- Finite sum of measurable functions
      intro t
      simpa [S] using
        (Finset.measurable_sum (s := Finset.range t) (f := fun k => F k)
          (by intro k hk; exact hF_meas k))
    have hS_mono : ∀ ω, Monotone (fun t => S t ω) := by
      -- Partial sums of nonnegative terms are pointwise monotone in t
      intro ω t s hts
      classical
      have hsplit :
          (Finset.range s).sum (fun k => F k ω)
            = (Finset.range t).sum (fun k => F k ω)
              + (Finset.Ico t s).sum (fun k => F k ω) := by
        simpa using
          (Finset.sum_range_add_sum_Ico (fun k => F k ω) hts).symm
      have htail_nonneg : (0 : ENNReal) ≤ (Finset.Ico t s).sum (fun k => F k ω) := by
        -- In ENNReal, 0 ≤ x holds for all x
        simpa using (bot_le : (⊥ : ENNReal) ≤ (Finset.Ico t s).sum (fun k => F k ω))
      have := add_le_add_left htail_nonneg ((Finset.range t).sum (fun k => F k ω))
      simpa [S, hsplit, add_comm, add_left_comm, add_assoc] using this
    -- Bound the lintegral of partial sums by finite sums of expectations of Z
    have hS_lint_le : ∀ t,
        (∫⁻ ω, S t ω ∂μ)
          ≤ ENNReal.ofReal (Finset.sum (Finset.range t) (fun k => ∫ ω, Z (k + 1) ω ∂μ)) := by
      -- Expand lintegral over finite sum and bound each term using scaledZ ≤ Z_{k+1}`
      intro t
      classical
      have hsplit : (∫⁻ ω, S t ω ∂μ)
          = Finset.sum (Finset.range t) (fun k => ∫⁻ ω, F k ω ∂μ) := by
        simpa [S] using
          (MeasureTheory.lintegral_finset_sum (f := fun k ω => F k ω)
            (s := Finset.range t) (hf := by intro k hk; exact hF_meas k))
      -- For each k, relate ∫⁻ ofReal(scaledZ k) to ofReal(∫ scaledZ k), then dominate by ∫ Z(k+1)
      have hterm : ∀ k ∈ Finset.range t,
          (∫⁻ ω, F k ω ∂μ) ≤ ENNReal.ofReal (∫ ω, Z (k + 1) ω ∂μ) := by
        intro k hk
        have h_nonneg : 0 ≤ᵐ[μ] scaledZ Y Z k := by
          refine ae_of_all μ (fun ω => ?_)
          have hz := hZ_nonneg (k + 1)
          have hden := (prodY_pos (Y := Y) hY_nonneg k ω).le
          have hnum : 0 ≤ Z (k + 1) ω := hz ω
          simpa [scaledZ] using (div_nonneg hnum hden)
        have h_int_sZ : Integrable (scaledZ Y Z k) μ :=
          integrable_scaledZ (μ := μ) (ℱ := ℱ) (Y := Y) (Z := Z)
            adapted_Y adapted_Z predictable_Z hY_nonneg hZ_nonneg integrable_Z k
        have h_eq : (∫⁻ ω, F k ω ∂μ) = ENNReal.ofReal (∫ ω, scaledZ Y Z k ω ∂μ) := by
          -- equality for nonnegative integrable real functions under ofReal
          simpa [F] using
            (ofReal_integral_eq_lintegral_ofReal (μ := μ) (f := scaledZ Y Z k)
              h_int_sZ h_nonneg).symm
        -- Pointwise domination: scaledZ ≤ Z_{k+1}
        have hpt : ∀ ω, scaledZ Y Z k ω ≤ Z (k + 1) ω := by
          intro ω
          have hge1 : 1 ≤ prodY Y k ω := prodY_ge_one (Y := Y) hY_nonneg k ω
          have hpos : 0 < prodY Y k ω := prodY_pos (Y := Y) hY_nonneg k ω
          have hz : 0 ≤ Z (k + 1) ω := hZ_nonneg (k + 1) ω
          have hmul : Z (k + 1) ω ≤ Z (k + 1) ω * prodY Y k ω := by
            simpa [one_mul] using (mul_le_mul_of_nonneg_left hge1 hz)
          simpa [scaledZ] using ((div_le_iff₀ hpos).mpr hmul)
        have h_int_Z : Integrable (Z (k + 1)) μ := integrable_Z (k + 1)
        have h_le_int : (∫ ω, scaledZ Y Z k ω ∂μ) ≤ (∫ ω, Z (k + 1) ω ∂μ) := by
          exact (MeasureTheory.integral_mono_ae (μ := μ)
            (f := scaledZ Y Z k) (g := Z (k + 1))
            (hf := h_int_sZ) (hg := h_int_Z) (h := ae_of_all μ hpt))
        -- Conclude ENNReal inequality by monotonicity of ofReal
        simpa [h_eq] using ENNReal.ofReal_le_ofReal h_le_int
      -- Summation inequality + identify RHS as ofReal of finite sum
      have hsum_le :
          Finset.sum (Finset.range t) (fun k => ∫⁻ ω, F k ω ∂μ)
            ≤ Finset.sum (Finset.range t) (fun k => ENNReal.ofReal (∫ ω, Z (k + 1) ω ∂μ)) :=
        Finset.sum_le_sum hterm
      -- For nonnegative terms, we also have
      --   ∑ ofReal(∫ Z_{k+1}) ≤ ofReal(∑ ∫ Z_{k+1})
      -- proved by induction using ENNReal.ofReal_add (details omitted here).
      have hsum_ofReal_le :
          Finset.sum (Finset.range t) (fun k => ENNReal.ofReal (∫ ω, Z (k + 1) ω ∂μ))
            ≤ ENNReal.ofReal (Finset.sum (Finset.range t) (fun k => ∫ ω, Z (k + 1) ω ∂μ)) := by
        classical
        -- Define the sequence a k := ∫ Z (k+1) and use simple induction on t.
        let a : ℕ → ℝ := fun k => ∫ ω, Z (k + 1) ω ∂μ
        have ha_nonneg : ∀ k, 0 ≤ a k := by
          intro k; exact MeasureTheory.integral_nonneg_of_ae (ae_of_all μ (by intro ω; exact hZ_nonneg (k + 1) ω))
        refine Nat.rec (by simp) ?step t
        intro n ih
        have hsum_nn : 0 ≤ Finset.sum (Finset.range n) a :=
          Finset.sum_nonneg (by intro k hk; exact ha_nonneg k)
        have hlast_nn : 0 ≤ a n := ha_nonneg n
        have step₁ :
            Finset.sum (Finset.range n) (fun k => ENNReal.ofReal (a k)) + ENNReal.ofReal (a n)
              ≤ ENNReal.ofReal (Finset.sum (Finset.range n) a) + ENNReal.ofReal (a n) :=
          add_le_add_right ih _
        have step₂ :
            ENNReal.ofReal (Finset.sum (Finset.range n) a) + ENNReal.ofReal (a n)
              = ENNReal.ofReal (Finset.sum (Finset.range n) a + a n) := by
          simpa [ENNReal.ofReal_add, hsum_nn, hlast_nn]
        have step' := step₁.trans (le_of_eq step₂)
        simpa [a, Finset.sum_range_succ] using step'
      have hsum_le_ofReal := hsum_le.trans hsum_ofReal_le
      simpa [hsplit] using hsum_le_ofReal
    -- Pass to the supremum over t using `lintegral_iSup'` and the partial-sum bound ≤ tsum
    have h_lint_series :
        (∫⁻ ω, (⨆ t, S t ω) ∂μ)
          ≤ ENNReal.ofReal EZsum := by
      -- Combine partial-sum lintegral bound with `hsum_le_tsum` via `lintegral_iSup'`
      have hmono_ae : ∀ᵐ ω ∂μ, Monotone (fun t => S t ω) := ae_of_all μ hS_mono
      have h_eq : (∫⁻ ω, (⨆ t, S t ω) ∂μ) = ⨆ t, (∫⁻ ω, S t ω ∂μ) := by
        simpa using (MeasureTheory.lintegral_iSup' (μ := μ) (f := S)
          (hf := fun t => (hS_meas t).aemeasurable) (h_mono := hmono_ae))
      have hbound : (⨆ t, (∫⁻ ω, S t ω ∂μ)) ≤ ENNReal.ofReal EZsum := by
        refine iSup_le (fun t => ?_)
        exact (hS_lint_le t).trans (by exact ENNReal.ofReal_le_ofReal (hsum_le_tsum t))
      simpa [h_eq] using hbound
    -- Conclude finiteness a.e. from the integral bound
    have h_fin_ae : ∀ᵐ ω ∂μ, (⨆ t, S t ω) < ⊤ := by
      -- Since ∫⁻ iSup S ≤ ofReal EZsum < ⊤, the iSup is finite a.e.
      have h_meas_S : AEMeasurable (fun ω => (⨆ t, S t ω)) μ := by
        have : ∀ t, AEMeasurable (S t) μ := fun t => (hS_meas t).aemeasurable
        exact AEMeasurable.iSup this
      have hlt : (∫⁻ ω, (⨆ t, S t ω) ∂μ) < ⊤ := lt_of_le_of_lt h_lint_series (by simp)
      exact MeasureTheory.ae_lt_top' (μ := μ) (f := fun ω => (⨆ t, S t ω)) h_meas_S (ne_of_lt hlt)
    -- Convert bounded ENNReal partial sums to real-valued Summable of scaledZ
    have h_sum_scaledZ : ∀ᵐ ω ∂μ, Summable (fun k => scaledZ Y Z k ω) := by
      -- Step 1: obtain a real upper bound B(ω) for the real partial sums from ENNReal finiteness
      suffices h_bound_real : ∀ᵐ ω ∂μ, ∃ B : ℝ,
          ∀ t, (Finset.range t).sum (fun k => scaledZ Y Z k ω) ≤ B by
        -- Step 2: partial sums are monotone and bounded, hence converge a.e.; conclude Summable a.e.
        suffices hconv : ∀ᵐ ω ∂μ, ∃ L : ℝ,
            Filter.Tendsto (fun t => (Finset.range t).sum (fun k => scaledZ Y Z k ω))
              Filter.atTop (nhds L) by
          -- From convergence of partial sums, obtain Summable
          refine hconv.mono ?_
          intro ω hω
          rcases hω with ⟨L, hL⟩
          -- TODO: convert Tendsto of partial sums to Summable using HasSum equivalence
          -- in a topological additive group (ℝ).
          -- This is standard: HasSum ↔ Tendsto of partial sums.
          -- For nonnegative sequences, HasSum is exactly the Tendsto of partial sums
          have hsum : HasSum (fun k => scaledZ Y Z k ω) L := by
            rw [hasSum_iff_tendsto_nat_of_nonneg]
            · exact hL
            · intro i
              exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg i ω
          exact hsum.summable
        -- Build convergence from monotone + bounded
        refine h_bound_real.mono ?_
        intro ω hB
        rcases hB with ⟨B, hBω⟩
        -- Monotonicity of real partial sums
        have hmono : Monotone (fun t => (Finset.range t).sum (fun k => scaledZ Y Z k ω)) := by
          intro t s hts
          classical
          have hsplit :
              (Finset.range s).sum (fun k => scaledZ Y Z k ω)
                = (Finset.range t).sum (fun k => scaledZ Y Z k ω)
                  + (Finset.Ico t s).sum (fun k => scaledZ Y Z k ω) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun k => scaledZ Y Z k ω) hts).symm
          have htail_nonneg : 0 ≤ (Finset.Ico t s).sum (fun k => scaledZ Y Z k ω) := by
            apply Finset.sum_nonneg
            intro k hk
            exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
          have := add_le_add_left htail_nonneg ((Finset.range t).sum (fun k => scaledZ Y Z k ω))
          simpa [hsplit, add_comm, add_left_comm, add_assoc]
            using this
        -- Deduce existence of limit for a monotone bounded sequence in ℝ
        classical
        -- Define the candidate limit as the supremum of the range of partial sums
        let L : ℝ := sSup (Set.range (fun t => (Finset.range t).sum (fun k => scaledZ Y Z k ω)))
        -- TODO: show `Tendsto ... (nhds L)` by applying the monotone convergence to supremum
        -- using completeness of ℝ and boundedness above by `B`.
        exact ⟨L, by
          -- standard: monotone bounded ⇒ convergence to sSup of range
          -- Use tendsto_atTop_ciSup for monotone bounded sequences
          have hbdd : BddAbove (Set.range (fun t => (Finset.range t).sum (fun k => scaledZ Y Z k ω))) := by
            use B
            intro x ⟨t, ht⟩
            rw [← ht]
            exact hBω t
          exact tendsto_atTop_ciSup hmono hbdd⟩
      -- Construct the bound B from `h_fin_ae` (finiteness of the ENNReal supremum)
      refine h_fin_ae.mono ?_
      intro ω hfin
      -- Let B be the real value of the ENNReal supremum of partial sums
      let B : ℝ := (⨆ t, S t ω).toReal
      -- For each t, show the real partial sum is ≤ B
      have hsum_le : ∀ t,
          (Finset.range t).sum (fun k => scaledZ Y Z k ω) ≤ B := by
        intro t
        -- ofReal (real partial sum) ≤ S t ω by construction, and S t ω ≤ iSup ≤ ⊤ (finite by hfin)
        have h1 : ENNReal.ofReal ((Finset.range t).sum (fun k => scaledZ Y Z k ω)) ≤ S t ω := by
          -- Induction: ofReal(real partial sum) ≤ ENNReal partial sum S t ω
          classical
          induction' t with n ih
          · simp [S, F]
          · have hsum_nn : 0 ≤ (Finset.range n).sum (fun k => scaledZ Y Z k ω) := by
              apply Finset.sum_nonneg; intro k hk
              exact scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg k ω
            have hlast_nn : 0 ≤ scaledZ Y Z n ω :=
              scaledZ_nonneg (Y := Y) (Z := Z) hY_nonneg hZ_nonneg n ω
            calc
              ENNReal.ofReal ((Finset.range (n + 1)).sum (fun k => scaledZ Y Z k ω))
                  = ENNReal.ofReal ((Finset.range n).sum (fun k => scaledZ Y Z k ω)
                      + scaledZ Y Z n ω) := by
                    simp [Finset.sum_range_succ]
              _ = ENNReal.ofReal ((Finset.range n).sum (fun k => scaledZ Y Z k ω))
                      + ENNReal.ofReal (scaledZ Y Z n ω) := by
                    simpa [ENNReal.ofReal_add, hsum_nn, hlast_nn]
              _ ≤ S n ω + ENNReal.ofReal (scaledZ Y Z n ω) := by
                    exact add_le_add_right ih _
              _ = S (n + 1) ω := by
                    simp [S, F, Finset.sum_range_succ]
        have h2 : S t ω ≤ (⨆ t, S t ω) := by
          -- pointwise bound to the supremum
          exact le_iSup (fun t => S t ω) t
        -- Conclude via `ofReal_le_iff_le_toReal` using finiteness of the supremum
        have hsup_ne : (⨆ t, S t ω) ≠ ⊤ := (ne_of_lt hfin)
        -- ENNReal.ofReal (sum) ≤ iSup ⇒ real sum ≤ (iSup).toReal
        have :
            (Finset.range t).sum (fun k => scaledZ Y Z k ω)
              ≤ (⨆ t, S t ω).toReal := by
          -- From `ofReal (sum) ≤ iSup` and finiteness, switch to real via toReal.
          have h_ofReal_le :
              ENNReal.ofReal ((Finset.range t).sum (fun k => scaledZ Y Z k ω))
                ≤ (⨆ t, S t ω) := h1.trans h2
          -- Use `ofReal_le_iff_le_toReal` (requires the RHS is finite) to conclude.
          exact (ENNReal.ofReal_le_iff_le_toReal hsup_ne).1 h_ofReal_le
        simpa [B] using this
      exact ⟨B, hsum_le⟩
    -- Use the reduction at the top of this block
    exact h_sum_scaledZ
  have hS_ae_conv : ∀ᵐ ω ∂μ, ∃ Sinf : ℝ,
      Tendsto (fun t => scaledS X Y W t ω) atTop (nhds Sinf) := by
    -- From `hM_tend` (limit for −Mpred) deduce a limit for `Mpred`.
    have hMpred_lim : ∀ᵐ ω ∂μ,
        Tendsto (fun t => Mpred X Y Z W t ω) atTop
          (nhds (- Filtration.limitProcess (fun t ω => - Mpred X Y Z W t ω) ℱ μ ω)) := by
      -- Use `Filter.Tendsto.neg` on the limit of −Mpred and simplify double negation
      filter_upwards [hM_tend] with ω hω
      have := hω.neg
      simpa [neg_neg] using this
    -- Combine the limits of `Mpred` and `Zsum` to obtain a limit for `scaledS = Mpred + Zsum`.
    filter_upwards [hMpred_lim, hZsum_ae_conv] with ω hM hZ
    rcases hZ with ⟨LZ, hZtend⟩
    -- Define the limit pointwise as the sum of the two limits
    refine ⟨- Filtration.limitProcess (fun t ω => - Mpred X Y Z W t ω) ℱ μ ω + LZ, ?_⟩
    -- Algebra of limits for addition
    have h_add := hM.add hZtend
    -- Rewrite `scaledS` as `Mpred + Zsum`
    simpa [Mpred, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_add
  have hW_ae_sum : ∀ᵐ ω ∂μ, Summable (fun t => W t ω) := by
    -- Reduce to a.e. boundedness of partial sums via a single suffices.
    -- With W ≥ 0, partial sums `cumW W t ω` are monotone; bounded + monotone ⇒ convergence;
    -- then HasSum ↔ Tendsto of partial sums (nonnegative ℝ) gives Summable (W · ω).
    suffices h_bound : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ t, cumW W t ω ≤ B by
      refine h_bound.mono ?_
      intro ω hB
      rcases hB with ⟨B, hBω⟩
      -- Monotone bounded ⇒ convergence, then HasSum equivalence ⇒ Summable.
      -- cumW is monotone in t because W ≥ 0
      have hmono : Monotone (fun t => cumW W t ω) := by
        intro t s hts
        simp [cumW]
        have hsplit : (Finset.range (s + 1)).sum (fun k => W k ω)
            = (Finset.range (t + 1)).sum (fun k => W k ω)
              + (Finset.Ico (t + 1) (s + 1)).sum (fun k => W k ω) := by
          exact (Finset.sum_range_add_sum_Ico (fun k => W k ω) (Nat.add_le_add_right hts 1)).symm
        have htail_nn : 0 ≤ (Finset.Ico (t + 1) (s + 1)).sum (fun k => W k ω) := by
          apply Finset.sum_nonneg
          intro k hk
          exact hW_nonneg k ω
        linarith
      -- Monotone bounded sequences converge
      have hconv : ∃ L, Tendsto (fun t => cumW W t ω) atTop (nhds L) := by
        use sSup (Set.range (fun t => cumW W t ω))
        have hbdd : BddAbove (Set.range (fun t => cumW W t ω)) := by
          use B
          intro x ⟨t, ht⟩
          rw [← ht]
          exact hBω t
        exact tendsto_atTop_ciSup hmono hbdd
      rcases hconv with ⟨L, hL⟩
      -- Now use HasSum equivalence for nonnegative series
      -- cumW W t = ∑ k ∈ range (t+1), W k ω
      -- hasSum needs ∑ k ∈ range n, W k ω
      -- Standard fact: these limits are the same (just shifted by 1)
      have hL' : Tendsto (fun n => (Finset.range n).sum (fun k => W k ω)) atTop (nhds L) := by
        -- cumW W t = ∑ k ∈ range (t+1), so hL is tendsto of f(t+1) where f(n) = ∑ k ∈ range n
        -- Use tendsto_add_atTop_iff_nat to shift index
        have : (fun t => cumW W t ω) = (fun t => (Finset.range (t+1)).sum (fun k => W k ω)) := by
          ext t
          rfl
        rw [this] at hL
        exact (tendsto_add_atTop_iff_nat 1).mp hL
      have hsum : HasSum (fun t => W t ω) L := by
        rw [hasSum_iff_tendsto_nat_of_nonneg]
        · exact hL'
        · intro i
          exact hW_nonneg i ω
      exact hsum.summable
    -- Build h_bound from product bound and convergence of scaledS
    -- Convergent sequences are bounded, and cumW ≤ C · scaledS
    rcases prod_bound with ⟨C, hC_pos, hCbd⟩
    filter_upwards [hS_ae_conv] with ω hS
    rcases hS with ⟨Sinf, hStend⟩
    -- Convergent sequences are bounded - use simple eventual bound + initial segment
    have hS_bdd : ∃ M : ℝ, ∀ t, scaledS X Y W t ω ≤ M := by
      -- Tendsto implies BddAbove on the range
      have hbdd := hStend.bddAbove_range
      -- Unwrap BddAbove to get explicit bound
      rcases hbdd with ⟨M, hM⟩
      use M
      intro t
      exact hM (Set.mem_range_self t)
    rcases hS_bdd with ⟨M, hM⟩
    -- Now use cumW ≤ prodY · scaledS ≤ C · M
    use C * M
    intro t
    -- From X = prodY · scaledS - cumW and X ≥ 0, we get cumW ≤ prodY · scaledS
    have hX_identity : X t ω = prodY Y t ω * scaledS X Y W t ω - cumW W t ω := by
      -- This identity follows from scaledS = (X + cumW) / prodY
      have hpos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
      simp only [scaledS]
      rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
      ring
    have hX_nn := hX_nonneg t ω
    have : cumW W t ω ≤ prodY Y t ω * scaledS X Y W t ω := by
      linarith [hX_identity]
    have hS_nn : 0 ≤ scaledS X Y W t ω := by
      -- scaledS = (X + cumW) / prodY, all parts nonnegative
      have hnum : 0 ≤ X t ω + cumW W t ω := by
        apply add_nonneg (hX_nonneg t ω)
        simp [cumW]
        apply Finset.sum_nonneg
        intro k hk
        exact hW_nonneg k ω
      have hden := (prodY_pos (Y := Y) hY_nonneg t ω).le
      simpa [scaledS] using (div_nonneg hnum hden)
    calc cumW W t ω
      _ ≤ prodY Y t ω * scaledS X Y W t ω := this
      _ ≤ C * scaledS X Y W t ω := by
          apply mul_le_mul_of_nonneg_right (hCbd t ω) hS_nn
      _ ≤ C * M := by
          apply mul_le_mul_of_nonneg_left (hM t)
          exact hC_pos.le
  -- Choose Xlim from the a.e. convergence of X using the identity X_t = P_t*S_t − cumW_t
  -- together with the product bound and convergence of scaledS and cumW.
  -- Define Xlim via choice on the a.e. set where all limits exist
  rcases prod_bound with ⟨C, hC_pos, hCbd⟩
  have hX_conv_ae : ∀ᵐ ω ∂μ, ∃ Xlim_ω, Tendsto (fun t => X t ω) atTop (nhds Xlim_ω) := by
    filter_upwards [hS_ae_conv, hW_ae_sum] with ω hS hW
    rcases hS with ⟨Sinf, hStend⟩
    -- prodY is monotone and bounded, hence converges
    have hP_conv : ∃ Pinf, Tendsto (fun t => prodY Y t ω) atTop (nhds Pinf) := by
      have hmono : Monotone (fun t => prodY Y t ω) := by
        intro t s hts
        -- prodY Y s ω = prodY Y t ω * ∏ k ∈ Ico t s, (1 + Y (k+1) ω)
        -- Since Y ≥ 0, each factor (1 + Y (k+1) ω) ≥ 1, so the product ≥ 1
        simp only [prodY]
        rw [← Finset.prod_range_mul_prod_Ico _ hts]
        -- Each product is nonnegative
        have h_prod_t_nn : 0 ≤ ∏ k ∈ Finset.range t, (1 + Y (k + 1) ω) := by
          apply Finset.prod_nonneg
          intro k hk
          have := hY_nonneg (k + 1) ω
          linarith
        have h_prod_Ico_nn : 0 ≤ ∏ k ∈ Finset.Ico t s, (1 + Y (k + 1) ω) := by
          apply Finset.prod_nonneg
          intro k hk
          have := hY_nonneg (k + 1) ω
          linarith
        -- The key: prodY Y t ω * 1 ≤ prodY Y t ω * (product over Ico)
        suffices (Finset.range t).prod (fun k => 1 + Y (k + 1) ω) * 1 ≤
                 (Finset.range t).prod (fun k => 1 + Y (k + 1) ω) *
                 (Finset.Ico t s).prod (fun k => 1 + Y (k + 1) ω) by
          simpa [mul_one] using this
        -- This follows from 1 ≤ Ico-product and prod_t_nn ≥ 0
        apply mul_le_mul_of_nonneg_left _ h_prod_t_nn
        -- Prove 1 ≤ Ico-product directly: compare ∏ 1 with ∏ (1 + Y)
        calc 1
          _ = ∏ k ∈ Finset.Ico t s, (1 : ℝ) := by rw [Finset.prod_const_one]
          _ ≤ ∏ k ∈ Finset.Ico t s, (1 + Y (k + 1) ω) := by
              apply Finset.prod_le_prod
              · intro k hk; norm_num
              · intro k hk
                have : 0 ≤ Y (k + 1) ω := hY_nonneg (k + 1) ω
                linarith
      have hbdd : BddAbove (Set.range (fun t => prodY Y t ω)) := by
        use C
        intro x ⟨t, ht⟩
        rw [← ht]
        exact hCbd t ω
      use sSup (Set.range (fun t => prodY Y t ω))
      exact tendsto_atTop_ciSup hmono hbdd
    rcases hP_conv with ⟨Pinf, hPtend⟩
    -- cumW converges since W is summable
    have hCW_conv : ∃ CWinf, Tendsto (fun t => cumW W t ω) atTop (nhds CWinf) := by
      use ∑' k, W k ω
      simp only [cumW]
      -- Summable.hasSum.tendsto_sum_nat gives: Tendsto (fun n => ∑ k < n, W k ω) atTop (nhds (∑' k, W k ω))
      -- We want: Tendsto (fun t => ∑ k < t+1, W k ω) atTop (nhds (∑' k, W k ω))
      exact (tendsto_add_atTop_iff_nat 1).mpr hW.hasSum.tendsto_sum_nat
    rcases hCW_conv with ⟨CWinf, hCWtend⟩
    -- Now X = prodY * scaledS - cumW, so it converges to Pinf * Sinf - CWinf
    use Pinf * Sinf - CWinf
    have hX_eq : ∀ t, X t ω = prodY Y t ω * scaledS X Y W t ω - cumW W t ω := by
      intro t
      have hpos : 0 < prodY Y t ω := prodY_pos (Y := Y) hY_nonneg t ω
      simp only [scaledS]
      rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
      ring
    have : (fun t => X t ω) = (fun t => prodY Y t ω * scaledS X Y W t ω - cumW W t ω) := by
      ext t
      exact hX_eq t
    rw [this]
    exact (hPtend.mul hStend).sub hCWtend
  -- Define Xlim pointwise using choice
  let Xlim : Ω → ℝ := fun ω => if h : ∃ x, Tendsto (fun t => X t ω) atTop (nhds x) then h.choose else 0
  have hX_tend : ∀ᵐ ω ∂μ, Tendsto (fun t => X t ω) atTop (nhds (Xlim ω)) := by
    filter_upwards [hX_conv_ae] with ω h
    simp only [Xlim]
    have : ∃ x, Tendsto (fun t => X t ω) atTop (nhds x) := h
    simp [dif_pos this]
    exact this.choose_spec
  exact ⟨Xlim, hX_tend, hW_ae_sum⟩

end Classical
end Stoch
end QLS
