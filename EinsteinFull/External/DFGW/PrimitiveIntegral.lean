import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Integral of a primitive

The integral of a primitive equals a triangularly weighted integral of its derivative.
-/

open MeasureTheory

namespace EinsteinFull.External.DFGW

/-- The integral of a primitive is the triangularly weighted integral of its derivative. -/
theorem integral_primitive_eq_weighted (r : ℝ → ℝ) (hr : Continuous r) (t : ℝ) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..u, r v) =
      ∫ v in (0 : ℝ)..t, (t - v) * r v := by
  let R : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, r v
  have hder (u : ℝ) : HasDerivAt R (r u) u :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable _ _)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := R) (u' := r) (v := fun u : ℝ => u - t) (v' := fun _ => (1 : ℝ))
    (a := 0) (b := t)
    (fun u _ => hder u) (fun u _ => by simpa using (hasDerivAt_id u).sub_const t)
    (hr.intervalIntegrable _ _) (intervalIntegrable_const)
  have hneg : (∫ u in (0 : ℝ)..t, r u * (u - t)) =
      -(∫ u in (0 : ℝ)..t, (t - u) * r u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  simp only [R, mul_one, sub_self, mul_zero, intervalIntegral.integral_same, zero_mul,
    zero_sub] at hparts
  rw [hneg] at hparts
  simpa only [neg_neg, R] using hparts

end EinsteinFull.External.DFGW
