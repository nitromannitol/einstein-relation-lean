import EinsteinFull.External.DFGW.TwoTimeCorrelation

/-! # Stationary autocorrelation at arbitrary times

A stationary process has autocorrelation depending only on the absolute time difference.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The autocorrelation of a square-integrable observable is a semigroup pairing at the
absolute difference of the observation times. -/
theorem integral_eval_mul_eval_eq_autocorrelation
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (g : S → ℝ) (hg : MemLp g 2 μ)
    (u v : ℝ) :
    (∫ η : C(ℝ, S), g (η u) * g (η v) ∂P) =
      inner ℝ (hg.toLp g) (transitionOperator hP (|v - u|).toNNReal (hg.toLp g)) := by
  rcases le_total u v with huv | hvu
  · have hdiff : 0 ≤ v - u := sub_nonneg.mpr huv
    have ht : ((v - u).toNNReal : ℝ) + u = v := by
      rw [Real.coe_toNNReal _ hdiff]
      ring
    have h := integral_eval_mul_eval_add hP g g hg hg u (v - u).toNNReal
    rw [ht] at h
    simpa only [abs_of_nonneg hdiff] using h
  · have hdiff : 0 ≤ u - v := sub_nonneg.mpr hvu
    have ht : ((u - v).toNNReal : ℝ) + v = u := by
      rw [Real.coe_toNNReal _ hdiff]
      ring
    have h := integral_eval_mul_eval_add hP g g hg hg v (u - v).toNNReal
    rw [ht] at h
    have habs : |v - u| = u - v := by rw [abs_of_nonpos (sub_nonpos.mpr hvu)]; ring
    rw [habs]
    simpa only [mul_comm] using h

end EinsteinFull.External.DFGW
