import EinsteinFull.External.DFGW.PrimitiveIntegral

/-! # Triangular integration of stationary correlations

A double integral of a function of the absolute time difference reduces to an integral with
triangular weight.
-/

open MeasureTheory

namespace EinsteinFull.External.DFGW

/-- A double integral of an even time-difference kernel has triangular weight. -/
theorem integral_abs_difference_eq_weighted (r : ℝ → ℝ) (hr : Continuous r)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t, r |v - u|) =
      2 * ∫ v in (0 : ℝ)..t, (t - v) * r v := by
  let R : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, r v
  have hR : Continuous R := (intervalIntegral.differentiable_integral_of_continuous hr).continuous
  have hinner (u : ℝ) (hu : u ∈ Set.Icc 0 t) :
      (∫ v in (0 : ℝ)..t, r |v - u|) = R u + R (t - u) := by
    have hc : Continuous (fun v : ℝ => r |v - u|) := hr.comp ((continuous_id.sub continuous_const).abs)
    have hI1 : IntervalIntegrable (fun v : ℝ => r |v - u|) volume 0 u :=
      hc.intervalIntegrable 0 u
    have hI2 : IntervalIntegrable (fun v : ℝ => r |v - u|) volume u t :=
      hc.intervalIntegrable u t
    have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hleft : (∫ v in (0 : ℝ)..u, r |v - u|) = R u := by
      calc
        _ = ∫ v in (0 : ℝ)..u, r (u - v) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [Set.uIcc_of_le hu.1] at hv
          change r |v - u| = r (u - v)
          rw [abs_of_nonpos (sub_nonpos.mpr hv.2)]
          congr 1
          ring
        _ = R u := by
          have hh := intervalIntegral.integral_comp_sub_left r (a := 0) (b := u) u
          simpa only [R, sub_self, sub_zero] using hh
    have hright : (∫ v in u..t, r |v - u|) = R (t - u) := by
      calc
        _ = ∫ v in u..t, r (v - u) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [Set.uIcc_of_le hu.2] at hv
          change r |v - u| = r (v - u)
          rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]
        _ = R (t - u) := by
          have hh := intervalIntegral.integral_comp_sub_right r (a := u) (b := t) u
          simpa only [R, sub_self] using hh
    linarith
  have hsym : (∫ u in (0 : ℝ)..t, R (t - u)) = ∫ u in (0 : ℝ)..t, R u := by
    have h := intervalIntegral.integral_comp_sub_left R (a := 0) (b := t) t
    simpa only [sub_self, sub_zero] using h
  calc
    _ = ∫ u in (0 : ℝ)..t, (R u + R (t - u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le ht] at hu
      exact hinner u hu
    _ = (∫ u in (0 : ℝ)..t, R u) + ∫ u in (0 : ℝ)..t, R (t - u) := by
      apply intervalIntegral.integral_add (hR.intervalIntegrable 0 t)
      exact (hR.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 t
    _ = 2 * ∫ u in (0 : ℝ)..t, R u := by rw [hsym]; ring
    _ = _ := by rw [integral_primitive_eq_weighted r hr t]

end EinsteinFull.External.DFGW
