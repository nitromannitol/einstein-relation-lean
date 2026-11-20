import EinsteinFull.External.DFGW.TimeIntegralSemigroup
import EinsteinFull.External.DFGW.TriangularIntegral

/-! # Triangular formula for integrated drift variance

The second moment of a time-integrated stationary observable is a triangularly weighted
integral of its semigroup autocorrelation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The integrated observable variance equals twice its triangularly weighted autocorrelation. -/
theorem integral_time_integral_sq_eq_weighted_autocorrelation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) =
      2 * ∫ v in (0 : ℝ)..t, (t - v) *
        inner ℝ (hg.toLp g) (transitionOperator hP v.toNNReal (hg.toLp g)) := by
  let f := hg.toLp g
  let r : ℝ → ℝ := fun v => inner ℝ f (transitionOperator hP v.toNNReal f)
  have hr : Continuous r := by
    change Continuous (fun v : ℝ => inner ℝ f (transitionSemigroup hP v.toNNReal f))
    exact continuous_const.inner (((transitionSemigroup hP).continuous_orbit f).comp
      continuous_real_toNNReal)
  rw [integral_time_integral_sq_eq_double_autocorrelation hP g hg ht]
  exact integral_abs_difference_eq_weighted r hr ht

end EinsteinFull.External.DFGW
