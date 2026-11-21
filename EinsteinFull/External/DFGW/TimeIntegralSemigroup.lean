import EinsteinFull.External.DFGW.DoubleTimeCorrelation
import EinsteinFull.External.DFGW.AutocorrelationDistance

/-! # Semigroup formula for the integrated drift variance

The variance of a time-integrated state observable is a double integral of its semigroup
autocorrelation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The variance of a time-integrated state observable is its double semigroup correlation. -/
theorem integral_time_integral_sq_eq_double_autocorrelation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ η : C(ℝ, S), (∫ u in (0 : ℝ)..t, g (η u)) ^ 2 ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
        inner ℝ (hg.toLp g) (transitionOperator hP (|v - u|).toNNReal (hg.toLp g)) := by
  rw [integral_time_integral_sq_eq_double_correlation hP g hg ht]
  simp_rw [integral_eval_mul_eval_eq_autocorrelation hP g hg]

end EinsteinFull.External.DFGW
