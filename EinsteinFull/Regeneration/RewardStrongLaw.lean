import Mathlib.Probability.StrongLaw

/-!
# Ratios of independent cycle rewards and durations

The strong law for rewards and durations gives convergence of their cumulative ratio when the
mean duration is positive. A cycle count and a sublinear remainder then transfer the strong law
to continuous time.
-/

open MeasureTheory Filter Finset ProbabilityTheory
open scoped Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Inverting an asymptotically linear cycle clock gives the reciprocal cycle rate. -/
theorem cycle_count_rate_of_clock (clock : ℕ → ℝ) (count : ℝ → ℕ) (m : ℝ)
    (hm : 0 < m)
    (hclock : Tendsto (fun n : ℕ => clock n / (n : ℝ)) atTop (𝓝 m))
    (hcount : Tendsto count atTop atTop)
    (hbracket : ∀ᶠ t in atTop, clock (count t) ≤ t ∧ t ≤ clock (count t + 1)) :
    Tendsto (fun t : ℝ => (count t : ℝ) / t) atTop (𝓝 m⁻¹) := by
  have hlow := hclock.comp hcount
  have hcast : Tendsto (fun t : ℝ => (count t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have hinv : Tendsto (fun t : ℝ => (count t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hsucc := hclock.comp ((tendsto_add_atTop_nat 1).comp hcount)
  have hu : Tendsto (fun t : ℝ => clock (count t + 1) / (count t : ℝ)) atTop (𝓝 m) := by
    have h := hsucc.mul ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hinv)
    have h' : Tendsto (fun t : ℝ =>
        (clock (count t + 1) / ((count t : ℝ) + 1)) *
          (1 + (count t : ℝ)⁻¹)) atTop (𝓝 m) := by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_zero, mul_one] using h
    apply h'.congr'
    filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with t ht
    have hn : (count t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht)
    have hn' : (count t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hmiddle : Tendsto (fun t : ℝ => t / (count t : ℝ)) atTop (𝓝 m) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hu
    · filter_upwards [hbracket, hcount.eventually (eventually_gt_atTop 0)] with t hb ht
      exact div_le_div_of_nonneg_right hb.1 (by positivity)
    · filter_upwards [hbracket, hcount.eventually (eventually_gt_atTop 0)] with t hb ht
      exact div_le_div_of_nonneg_right hb.2 (by positivity)
  convert hmiddle.inv₀ (ne_of_gt hm) using 1; simp [div_eq_mul_inv, mul_comm]

/-- The ratio of cumulative rewards to cumulative durations tends almost surely to the ratio
of their means when each sequence is pairwise independent and identically distributed. -/
theorem reward_sum_div_duration_sum_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward duration : ℕ → Ω → ℝ)
    (hr : Integrable (reward 0) μ) (ht : Integrable (duration 0) μ)
    (hir : Pairwise ((· ⟂ᵢ[μ] ·) on reward))
    (hit : Pairwise ((· ⟂ᵢ[μ] ·) on duration))
    (hdr : ∀ n, IdentDistrib (reward n) (reward 0) μ μ)
    (hdt : ∀ n, IdentDistrib (duration n) (duration 0) μ μ)
    (hmean : 0 < ∫ ω, duration 0 ω ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ range n, reward i ω) / ∑ i ∈ range n, duration i ω)
      atTop (𝓝 ((∫ ω, reward 0 ω ∂μ) / ∫ ω, duration 0 ω ∂μ)) := by
  filter_upwards [strong_law_ae reward hr hir hdr, strong_law_ae duration ht hit hdt] with ω hR hT
  have h := hR.div hT (ne_of_gt hmean)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hn)))

/-- For an integrable sequence of pairwise independent identically distributed variables, the
individual value divided by its index tends to zero almost surely. -/
theorem reward_div_index_tendsto_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward : ℕ → Ω → ℝ)
    (hr : Integrable (reward 0) μ)
    (hir : Pairwise ((· ⟂ᵢ[μ] ·) on reward))
    (hdr : ∀ n, IdentDistrib (reward n) (reward 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => reward n ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  filter_upwards [strong_law_ae reward hr hir hdr] with ω hR
  have hs : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, reward i ω)
      atTop (𝓝 (∫ ω, reward 0 ω ∂μ)) := by
    simpa only [smul_eq_mul] using hR
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  have hf : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hdiff : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ range (n + 1), reward i ω) -
        ((n : ℝ) / ((n : ℝ) + 1)) * ((n : ℝ)⁻¹ * ∑ i ∈ range n, reward i ω))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, one_mul, sub_self] using hs'.sub (hf.mul hs)
  apply hdiff.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one, sum_range_succ]
  field_simp; ring

/-- A cycle strong law transfers to continuous time when the cycle count has an asymptotic
rate and the displacement remaining after the last completed cycle is sublinear. -/
theorem reward_rate_of_cycle_count_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward : ℕ → Ω → ℝ) (count : Ω → ℝ → ℕ)
    (position : Ω → ℝ → ℝ) (ν : ℝ)
    (hr : Integrable (reward 0) μ)
    (hir : Pairwise ((· ⟂ᵢ[μ] ·) on reward))
    (hdr : ∀ n, IdentDistrib (reward n) (reward 0) μ μ)
    (hcount : ∀ᵐ ω ∂μ, Tendsto (count ω) atTop atTop)
    (hrate : ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => (count ω t : ℝ) / t) atTop (𝓝 ν))
    (hrem : ∀ᵐ ω ∂μ, Tendsto
      (fun t : ℝ => (position ω t - ∑ i ∈ range (count ω t), reward i ω) / t)
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => position ω t / t)
      atTop (𝓝 ((∫ ω, reward 0 ω ∂μ) * ν)) := by
  filter_upwards [strong_law_ae reward hr hir hdr, hcount, hrate, hrem] with ω hs hc ht hleft
  have hs' : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, reward i ω)
      atTop (𝓝 (∫ ω, reward 0 ω ∂μ)) := by
    simpa only [smul_eq_mul] using hs
  have hsum := ((hs'.comp hc).mul ht).add hleft
  have hsum' : Tendsto
      (fun t : ℝ => ((count ω t : ℝ)⁻¹ * ∑ i ∈ range (count ω t), reward i ω) *
        ((count ω t : ℝ) / t) +
        (position ω t - ∑ i ∈ range (count ω t), reward i ω) / t)
      atTop (𝓝 ((∫ ω, reward 0 ω ∂μ) * ν)) := by
    simpa only [Function.comp_apply, add_zero] using hsum
  apply hsum'.congr'
  filter_upwards [hc.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with t hn ht0
  have hn0 : (count ω t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have ht0' : t ≠ 0 := ne_of_gt ht0
  field_simp; ring

/-- A renewal reward law in continuous time, given the clock bracket and a sublinear
incomplete-cycle remainder. -/
theorem reward_rate_of_cycle_clock_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reward duration : ℕ → Ω → ℝ) (count : Ω → ℝ → ℕ)
    (position : Ω → ℝ → ℝ)
    (hr : Integrable (reward 0) μ) (ht : Integrable (duration 0) μ)
    (hir : Pairwise ((· ⟂ᵢ[μ] ·) on reward))
    (hit : Pairwise ((· ⟂ᵢ[μ] ·) on duration))
    (hdr : ∀ n, IdentDistrib (reward n) (reward 0) μ μ)
    (hdt : ∀ n, IdentDistrib (duration n) (duration 0) μ μ)
    (hmean : 0 < ∫ ω, duration 0 ω ∂μ)
    (hcount : ∀ᵐ ω ∂μ, Tendsto (count ω) atTop atTop)
    (hbracket : ∀ᵐ ω ∂μ, ∀ᶠ t in atTop,
      (∑ i ∈ range (count ω t), duration i ω) ≤ t ∧
        t ≤ ∑ i ∈ range (count ω t + 1), duration i ω)
    (hrem : ∀ᵐ ω ∂μ, Tendsto
      (fun t : ℝ => (position ω t - ∑ i ∈ range (count ω t), reward i ω) / t)
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => position ω t / t)
      atTop (𝓝 ((∫ ω, reward 0 ω ∂μ) / ∫ ω, duration 0 ω ∂μ)) := by
  have hrate : ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => (count ω t : ℝ) / t) atTop
      (𝓝 (∫ ω, duration 0 ω ∂μ)⁻¹) := by
    filter_upwards [strong_law_ae duration ht hit hdt, hcount, hbracket] with ω hs hc hb
    have hclock : Tendsto (fun n : ℕ => (∑ i ∈ range n, duration i ω) / (n : ℝ))
        atTop (𝓝 (∫ ω, duration 0 ω ∂μ)) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
    exact cycle_count_rate_of_clock (fun n => ∑ i ∈ range n, duration i ω)
      (count ω) _ hmean hclock hc hb
  simpa only [div_eq_mul_inv] using
    reward_rate_of_cycle_count_ae μ reward count position _ hr hir hdr hcount hrate hrem

end EinsteinFull.Regeneration
