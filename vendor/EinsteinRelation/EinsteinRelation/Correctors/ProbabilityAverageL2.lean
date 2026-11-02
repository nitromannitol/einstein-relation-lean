import EinsteinRelation.Correctors.KernelLpContraction
import Mathlib.MeasureTheory.Integral.Prod

/-! # Strong L² bounds for probability averages

Source: `paper/main.tex:822–830`. Jensen and Tonelli bound an actual
probability average by its slice energies. Integrals retain their Bochner
meaning even when no integrability has yet been established.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The squared L² seminorm is the integral of the squared extended norm.
Source: `paper/main.tex:822–830`. -/
theorem eLpNorm_two_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (f : X → E) (μ : Measure X) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  norm_num only [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]

/-- Probability averaging is bounded by a uniform bound on actual slice
L² seminorms. Source: `paper/main.tex:822–830`. -/
theorem eLpNorm_probability_integral_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [SFinite ν]
    {F : Y × X → ℝ} (hF : AEStronglyMeasurable F (ν.prod μ))
    {B : ℝ≥0∞} (hB : ∀ᵐ x ∂μ, eLpNorm (fun y => F (y, x)) 2 ν ≤ B) :
    eLpNorm (fun y => ∫ x, F (y, x) ∂μ) 2 ν ≤ B := by
  have hj : ∀ᵐ y ∂ν, ‖∫ x, F (y, x) ∂μ‖ₑ ^ 2 ≤ ∫⁻ x, ‖F (y, x)‖ₑ ^ 2 ∂μ := by
    filter_upwards [hF.prodMk_left] with y hy
    exact (pow_le_pow_left' (enorm_integral_le_eLpNorm (by norm_num) hy) 2).trans_eq
      (eLpNorm_two_sq _ _ hy)
  have hs : eLpNorm (fun y => ∫ x, F (y, x) ∂μ) 2 ν ^ 2 ≤ B ^ 2 := by
    rw [eLpNorm_two_sq _ _ hF.integral_prod_right']
    calc
      _ ≤ ∫⁻ y, ∫⁻ x, ‖F (y, x)‖ₑ ^ 2 ∂μ ∂ν := lintegral_mono_ae hj
      _ = ∫⁻ x, eLpNorm (fun y => F (y, x)) 2 ν ^ 2 ∂μ := by
        rw [lintegral_lintegral_swap (hF.enorm.pow_const 2)]
        apply lintegral_congr_ae
        filter_upwards [hF.prodMk_right] with x hx
        exact (eLpNorm_two_sq _ _ hx).symm
      _ ≤ ∫⁻ _ : X, B ^ 2 ∂μ := lintegral_mono_ae (hB.mono fun _ hx => pow_le_pow_left' hx 2)
      _ = B ^ 2 := by simp
  exact (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp hs

end EinsteinRelation.Correctors
