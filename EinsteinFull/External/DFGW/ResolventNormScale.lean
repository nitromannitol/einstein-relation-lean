import EinsteinFull.External.DFGW.ResolventVanishing
import Mathlib.Analysis.SpecificLimits.Basic
import EinsteinFull.External.DFGW.GridScale
import EinsteinFull.External.DFGW.ResolventEnergyCauchy

/-! # Diffusively normalized resolvent norms

The normalized resolvent norm tends to zero as the reciprocal parameter vanishes.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Reciprocal resolvent norms grow more slowly than the square root of the reciprocal scale. -/
theorem tendsto_normalized_resolvent_norm
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) :
    Tendsto (fun n : ℕ => (Real.sqrt (n + 1))⁻¹ *
      ‖transitionResolvent hP (reciprocalShift n) f‖) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_reciprocalShift_mul_resolvent_norm_sq hP f hint)
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro n
  change Real.sqrt ((1 / (n + 1 : ℝ)) * ‖transitionResolvent hP (reciprocalShift n) f‖ ^ 2) = _
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [one_div, Real.sqrt_inv]

/-- A reciprocal resolvent minus a fixed resolvent has negligible normalized `L²` norm. -/
theorem tendsto_normalized_resolvent_difference_norm
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0)) (m : ℕ) :
    Tendsto (fun n : ℕ => (Real.sqrt (n + 1))⁻¹ *
      ‖transitionResolvent hP (reciprocalShift n) f -
        transitionResolvent hP (reciprocalShift m) f‖) atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (Real.sqrt (n + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_gridScale.mono_right nhdsWithin_le_nhds
  have hmajor := (tendsto_normalized_resolvent_norm hP f hint).add
    (hden.mul_const ‖transitionResolvent hP (reciprocalShift m) f‖)
  simp only [zero_mul, add_zero] at hmajor
  apply squeeze_zero (g := fun n : ℕ => (Real.sqrt (n + 1))⁻¹ *
    ‖transitionResolvent hP (reciprocalShift n) f‖ +
      (Real.sqrt (n + 1))⁻¹ * ‖transitionResolvent hP (reciprocalShift m) f‖)
  · intro n
    positivity
  · intro n
    have h := mul_le_mul_of_nonneg_left (norm_sub_le
      (transitionResolvent hP (reciprocalShift n) f)
      (transitionResolvent hP (reciprocalShift m) f))
      (show 0 ≤ (Real.sqrt (n + 1 : ℝ))⁻¹ by positivity)
    simpa only [mul_add] using h
  · exact hmajor

end EinsteinFull.External.DFGW
