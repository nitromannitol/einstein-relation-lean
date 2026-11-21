import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Limit of Laplace transforms

The Laplace transform of an integrable correlation converges to its time integral as the
positive Laplace parameter tends to zero.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace EinsteinFull.External.DFGW

/-- The positive-parameter Laplace transforms of an integrable continuous function converge
to its integral. -/
theorem tendsto_laplace_integral_zero (r : ℝ → ℝ) (hr : Continuous r)
    (hint : IntegrableOn r (Ioi 0)) :
    Tendsto (fun lam : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * r t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioi (0 : ℝ), r t)) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun lam t => Real.exp (-lam * t) * r t
  have hF : ∀ lam, AEStronglyMeasurable (F lam) ν := by
    intro lam
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hr).aestronglyMeasurable
  have hbound : ∀ᶠ lam : ℝ in 𝓝[>] 0, ∀ᵐ t ∂ν, ‖F lam t‖ ≤ ‖r t‖ := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlam0 : 0 ≤ lam := le_of_lt hlam
    have ht0 : 0 ≤ t := le_of_lt ht
    have hle : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hlam0 ht0])
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [Real.exp_pos (-lam * t), abs_nonneg (r t)]
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun lam => F lam t) (𝓝[>] 0) (𝓝 (r t)) := by
    filter_upwards with t
    have hlam : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hz : Tendsto (fun lam : ℝ => -lam * t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [neg_zero, zero_mul] using hlam.neg.mul_const t
    have he := (Real.continuous_exp.tendsto 0).comp hz
    simpa only [F, Function.comp_def, Real.exp_zero, one_mul] using he.mul_const (r t)
  exact tendsto_integral_filter_of_dominated_convergence (fun t => ‖r t‖)
    (Filter.Eventually.of_forall hF) hbound hint.norm hlim

end EinsteinFull.External.DFGW
