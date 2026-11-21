import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Large-time limit of triangular averages

Triangular cutoffs tend to one under an integrable correlation by dominated convergence.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace EinsteinFull.External.DFGW

/-- An integrable correlation is recovered as the limit of its triangular cutoffs. -/
theorem tendsto_triangular_cutoff_integral (r : ℝ → ℝ) (hr : Continuous r)
    (hint : IntegrableOn r (Ioi 0)) :
    Tendsto (fun t : ℝ => ∫ s in Ioi (0 : ℝ),
      (Iic t).indicator (fun s => (1 - s / t) * r s) s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), r s)) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun t => (Iic t).indicator (fun s => (1 - s / t) * r s)
  have hF : ∀ t, AEStronglyMeasurable (F t) ν := by
    intro t
    exact (((continuous_const.sub (continuous_id.div_const t)).mul hr).measurable.indicator
      measurableSet_Iic).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ s ∂ν, ‖F t s‖ ≤ ‖r s‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    by_cases hst : s ≤ t
    · have htpos : 0 < t := by linarith
      have hd0 : 0 ≤ s / t := div_nonneg hs.le htpos.le
      have hd1 : s / t ≤ 1 := (div_le_one htpos).2 hst
      have hw0 : 0 ≤ 1 - s / t := by linarith
      have hw1 : 1 - s / t ≤ 1 := by linarith
      simp only [F, indicator_of_mem (mem_Iic.mpr hst), Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hw0]
      nlinarith [abs_nonneg (r s)]
    · simp only [F, indicator_of_notMem (show s ∉ Iic t from hst), norm_zero, norm_nonneg]
  have hlim : ∀ᵐ s ∂ν, Tendsto (fun t => F t s) atTop (𝓝 (r s)) := by
    filter_upwards with s
    have hinv : Tendsto (fun t : ℝ => s * t⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul s
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).mul_const (r s)
    have h' : Tendsto (fun t : ℝ => (1 - s / t) * r s) atTop (𝓝 (r s)) := by
      simpa only [div_eq_mul_inv, sub_zero, one_mul] using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop s] with t ht
    simp only [F, indicator_of_mem (mem_Iic.mpr ht)]
  exact tendsto_integral_filter_of_dominated_convergence (fun s => ‖r s‖)
    (Filter.Eventually.of_forall hF) hbound hint.norm hlim

end EinsteinFull.External.DFGW
