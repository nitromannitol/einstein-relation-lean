import Mathlib.Probability.StrongLaw

/-!
# Ratios of independent cycle rewards and durations

The strong law for rewards and durations gives convergence of their cumulative ratio when the
mean duration is positive. This is the discrete-time component of the regeneration velocity law.
-/

open MeasureTheory Filter Finset ProbabilityTheory
open scoped Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

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

end EinsteinFull.Regeneration
