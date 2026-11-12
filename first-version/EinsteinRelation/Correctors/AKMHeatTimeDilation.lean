import EinsteinRelation.Correctors.AKMHeatSpatialDilation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-time dilation of the AKM heat formula

Source: `paper/main.tex:722,756`. Positive time windows are transported
exactly. The inverse square from the spatial derivatives cancels the
time Jacobian; the remaining multiplier is the source amplitude.
-/
open MeasureTheory
open Set
noncomputable section
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Spatial dilation preserves genuine integrability of the inner heat
integral, rather than only its totalized value. -/
theorem integrable_akmHeatGradientDensity_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (j k l : Fin d) (x : Vec d)
    (hi : Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume) :
    Integrable (fun y => akmHeatGradientDensity (fun z => b • g (c⁻¹ • z))
      (c ^ 2 * t) j k l (c • x) y) volume := by
  apply (integrable_comp_smul_iff volume _ hc.ne').mp
  simpa only [akmHeatGradientDensity_dilation g c b t hc ht] using
    hi.const_mul ((c ^ d)⁻¹ * (b * (c⁻¹) ^ 2))

/-- Dilation of the actual spatial-then-temporal heat integral on a
positive closed time window. This does not assume a limiting formula. -/
theorem akmHeatGradientTimeIntegral_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b a h : ℝ) (hc : 0 < c)
    (ha : 0 < a) (hah : a ≤ h) (j k l : Fin d) (x : Vec d) :
    (∫ t in Icc (c ^ 2 * a) (c ^ 2 * h),
      akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z)) t j k l (c • x)) =
        b * ∫ t in Icc a h, akmHeatGradientSpaceIntegral g t j k l x := by
  have hscaled : c ^ 2 * a ≤ c ^ 2 * h := mul_le_mul_of_nonneg_left hah (sq_nonneg c)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hscaled,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hah]
  have hcomp : (∫ t in a..h,
      akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
        (c ^ 2 * t) j k l (c • x)) =
      (b * (c⁻¹) ^ 2) * ∫ t in a..h,
        akmHeatGradientSpaceIntegral g t j k l x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Ioc a h := by simpa only [uIoc_of_le hah] using ht
    exact akmHeatGradientSpaceIntegral_dilation g c b t hc
      (lt_of_lt_of_le ha ht'.1.le) j k l x
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (a := a) (b := h)
    (fun t => akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
      t j k l (c • x)) (c ^ 2)
  rw [hcomp, smul_eq_mul] at hchange
  rw [← hchange]
  field_simp

/-- Genuine time integrability is transported together with the finite
heat integral. No assertion about convergence at either endpoint is used. -/
theorem integrableOn_akmHeatGradientSpaceIntegral_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b a h : ℝ) (hc : 0 < c)
    (ha : 0 < a) (hah : a ≤ h) (j k l : Fin d) (x : Vec d)
    (hi : IntegrableOn (fun t => akmHeatGradientSpaceIntegral g t j k l x)
      (Icc a h) volume) :
    IntegrableOn (fun t => akmHeatGradientSpaceIntegral (fun z => b • g (c⁻¹ • z))
      t j k l (c • x)) (Icc (c ^ 2 * a) (c ^ 2 * h)) volume := by
  have hscaled : c ^ 2 * a ≤ c ^ 2 * h := mul_le_mul_of_nonneg_left hah (sq_nonneg c)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hscaled).mp
  apply (IntervalIntegrable.comp_mul_left_iff (c := c ^ 2)
    (pow_ne_zero 2 hc.ne')).mp
  have hdiva : c ^ 2 * a / c ^ 2 = a := mul_div_cancel_left₀ a (pow_ne_zero 2 hc.ne')
  have hdivh : c ^ 2 * h / c ^ 2 = h := mul_div_cancel_left₀ h (pow_ne_zero 2 hc.ne')
  rw [hdiva, hdivh]
  have hi' := ((intervalIntegrable_iff_integrableOn_Icc_of_le hah).mpr hi).const_mul
    (b * (c⁻¹) ^ 2)
  apply hi'.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Ioc a h := by simpa only [uIoc_of_le hah] using ht
  exact (akmHeatGradientSpaceIntegral_dilation g c b t hc
    (lt_of_lt_of_le ha ht'.1.le) j k l x).symm

/-- The exact time window required after physical dilation. Its endpoints
are positive real numbers; they need not be natural-number cutoffs. -/
theorem iteratedAKMHeatGradientTruncation_dilation {d : ℕ}
    (g : Vec d → Vec d) (c b : ℝ) (hc : 0 < c)
    (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation (fun z => b • g (c⁻¹ • z))
        m n j k l (c • x) =
      b * ∫ t in Icc ((c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹)
        ((c ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ)),
          akmHeatGradientSpaceIntegral g t j k l x := by
  have hca : 0 < (c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hlow : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_cast
    omega
  have hhigh : 1 ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hah := mul_le_mul_of_nonneg_left (hlow.trans hhigh)
    (inv_nonneg.mpr (sq_nonneg c))
  have h := akmHeatGradientTimeIntegral_dilation g c b
    ((c ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹)
    ((c ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ)) hc hca hah j k l x
  simpa only [mul_inv_cancel_left₀ (pow_ne_zero 2 hc.ne')] using h

end EinsteinRelation.Correctors
