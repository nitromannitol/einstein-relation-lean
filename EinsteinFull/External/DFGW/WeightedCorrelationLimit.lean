import EinsteinFull.External.DFGW.TriangularLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Limit of normalized triangular correlation integrals

Normalized triangularly weighted integrals converge to the integral of an absolutely
integrable correlation.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace EinsteinFull.External.DFGW

/-- A normalized triangular integral equals the corresponding cutoff integral. -/
theorem normalized_weighted_integral_eq_cutoff (r : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    t⁻¹ * (∫ s in (0 : ℝ)..t, (t - s) * r s) =
      ∫ s in Ioi (0 : ℝ), (Iic t).indicator (fun s => (1 - s / t) * r s) s := by
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, ← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  change t⁻¹ * ((t - s) * r s) = (1 - s / t) * r s
  field_simp

/-- Normalized triangular correlation integrals converge to the full correlation integral. -/
theorem tendsto_normalized_weighted_integral (r : ℝ → ℝ) (hr : Continuous r)
    (hint : IntegrableOn r (Ioi 0)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0 : ℝ)..t, (t - s) * r s) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), r s)) := by
  apply (tendsto_triangular_cutoff_integral r hr hint).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (normalized_weighted_integral_eq_cutoff r ht).symm

end EinsteinFull.External.DFGW
