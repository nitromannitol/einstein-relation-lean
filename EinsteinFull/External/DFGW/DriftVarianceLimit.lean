import EinsteinFull.External.DFGW.TriangularVariance
import EinsteinFull.External.DFGW.WeightedCorrelationLimit

/-! # Long-time variance of integrated observables

Integrable semigroup autocorrelations determine the asymptotic variance of time-integrated
stationary observables.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The normalized second moment of an integrated observable tends to twice the integral of
its autocorrelation. -/
theorem tendsto_normalized_time_integral_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    (hint : IntegrableOn (fun t : ℝ => inner ℝ (hg.toLp g)
      (transitionOperator hP t.toNNReal (hg.toLp g))) (Set.Ioi 0)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ η : C(ℝ, S),
      (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) atTop
      (𝓝 (2 * ∫ t in Set.Ioi (0 : ℝ), inner ℝ (hg.toLp g)
        (transitionOperator hP t.toNNReal (hg.toLp g)))) := by
  let f := hg.toLp g
  let r : ℝ → ℝ := fun t => inner ℝ f (transitionOperator hP t.toNNReal f)
  have hr : Continuous r := by
    change Continuous (fun t : ℝ => inner ℝ f (transitionSemigroup hP t.toNNReal f))
    exact continuous_const.inner (((transitionSemigroup hP).continuous_orbit f).comp
      continuous_real_toNNReal)
  have hlim := (tendsto_normalized_weighted_integral r hr hint).const_mul 2
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h := integral_time_integral_sq_eq_weighted_autocorrelation hP g hg ht.le
  change 2 * (t⁻¹ * ∫ s in (0 : ℝ)..t, (t - s) * r s) =
    t⁻¹ * ∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P
  rw [h]
  ring

end EinsteinFull.External.DFGW
