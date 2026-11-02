import EinsteinFull.Calculus.SqrtVolterraSupport

/-!
# An elementary integrable majorant for the double square-root kernel

The inequality `sqrt t ≤ sqrt s + sqrt (t-s)` splits the two endpoint
singularities into inverse square roots whose integrals are already known.
-/

open MeasureTheory Set

noncomputable section
namespace EinsteinFull

/-- Splitting the square-root kernel separates its two endpoint singularities. -/
theorem inv_sqrt_mul_inv_sqrt_sub_le {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    (Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹ ≤
      (Real.sqrt t)⁻¹ * ((Real.sqrt s)⁻¹ + (Real.sqrt (t-s))⁻¹) := by
  have ht : 0 < t := hs.trans hst
  have hx : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hy : 0 < Real.sqrt (t-s) := Real.sqrt_pos.2 (sub_pos.2 hst)
  have hz : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hadd : Real.sqrt t ≤ Real.sqrt s + Real.sqrt (t-s) := by
    nlinarith only [Real.sq_sqrt hs.le, Real.sq_sqrt (sub_nonneg.2 hst.le),
      Real.sq_sqrt ht.le, mul_nonneg hx.le hy.le, hx, hy, hz]
  field_simp
  simpa only [add_comm] using hadd

/-- The double square-root kernel is integrable despite both endpoint singularities. -/
theorem intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ => (Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) volume 0 t := by
  have hi := intervalIntegrable_inv_sqrt ht.le
  have hj : IntervalIntegrable (fun s : ℝ => (Real.sqrt (t-s))⁻¹) volume 0 t := by
    simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm
  have hm : Measurable (fun s : ℝ => (Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) :=
    Real.continuous_sqrt.measurable.inv.mul
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).measurable.inv)
  apply ((hi.add hj).const_mul (Real.sqrt t)⁻¹).mono_fun' hm.aestronglyMeasurable
  rw [uIoc_of_le ht.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne t)] with s hs hst
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_sqrt_mul_inv_sqrt_sub_le hs.1 (lt_of_le_of_ne hs.2 hst)

/-- Its integral has a universal bound, independent of the time horizon. -/
theorem integral_inv_sqrt_mul_inv_sqrt_sub_le {t : ℝ} (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, (Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) ≤ 4 := by
  have hi := intervalIntegrable_inv_sqrt ht.le
  have hj : IntervalIntegrable (fun s : ℝ => (Real.sqrt (t-s))⁻¹) volume 0 t := by
    simpa only [sub_zero, sub_self] using (hi.comp_sub_left t).symm
  have he : (∫ s in (0 : ℝ)..t, (Real.sqrt (t-s))⁻¹) = 2 * Real.sqrt t := by
    change (∫ s in (0 : ℝ)..t, (fun x => (Real.sqrt x)⁻¹) (t-s)) = _
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (Real.sqrt x)⁻¹) t]
    simpa only [sub_self, sub_zero] using integral_inv_sqrt ht.le
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (Real.sqrt t)⁻¹ *
        ((Real.sqrt s)⁻¹ + (Real.sqrt (t-s))⁻¹) :=
      intervalIntegral.integral_mono_on_of_le_Ioo ht.le
        (intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub ht)
        ((hi.add hj).const_mul _) (fun _ hs => inv_sqrt_mul_inv_sqrt_sub_le hs.1 hs.2)
    _ = 4 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hj,
        integral_inv_sqrt ht.le, he]
      field_simp
      ring

end EinsteinFull
