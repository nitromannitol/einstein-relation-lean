import EinsteinFull.Frozen.ProfileFinitePart
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Taylor

/-! Integrability of the literal integrands defining the Gaussian profile finite part. -/

open MeasureTheory Set
open scoped BigOperators

namespace EinsteinFull

/-- Every finite differentiability order holds for the actual Gaussian profile. -/
theorem contDiff_gaussianProfile (u₀ u₂ γ : ℝ) (n : ℕ) :
    ContDiff ℝ n (gaussianProfile u₀ u₂ γ) := by
  unfold gaussianProfile
  exact (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).mul
    ((contDiff_const.mul (contDiff_id.pow 2)).exp)

/-- A polynomial of degree two times a Gaussian is integrable on the real line. -/
theorem integrable_gaussianProfile (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Integrable (gaussianProfile u₀ u₂ γ) := by
  have h₂ : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-γ * x ^ 2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hγ (s := (2 : ℝ)) (by norm_num))
  convert ((integrable_exp_neg_mul_sq hγ).const_mul u₀).add (h₂.const_mul u₂) using 1
  ext x
  simp only [gaussianProfile, Pi.add_apply]
  ring

/-- The tail in the literal finite-part definition is integrable for every natural order. -/
theorem integrableOn_gaussianProfile_div_pow_Ioi_one (d : ℕ) (u₀ u₂ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun u : ℝ => gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) (Ioi 1) := by
  apply (integrable_gaussianProfile u₀ u₂ hγ).norm.integrableOn.mono'
  · exact ((contDiff_gaussianProfile u₀ u₂ γ 0).continuous.measurable.div
      (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hpow : (1 : ℝ) ≤ u ^ (d + 1) := one_le_pow₀ (le_of_lt hu)
    rw [norm_div, Real.norm_eq_abs (u ^ (d + 1)), abs_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg (gaussianProfile u₀ u₂ γ u)) hpow

/-- Mathlib's within-set Taylor polynomial has the literal frozen profile coefficients. -/
theorem taylorWithinEval_gaussianProfile (d : ℕ) (u₀ u₂ γ u : ℝ) :
    taylorWithinEval (gaussianProfile u₀ u₂ γ) d (Icc 0 1) 0 u =
      ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val := by
  rw [taylor_within_apply, Fin.sum_univ_eq_sum_range
    (fun j => profileTaylorCoefficient u₀ u₂ γ j * u ^ j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    (contDiff_gaussianProfile u₀ u₂ γ j).contDiffAt (by simp)]
  simp only [sub_zero, smul_eq_mul, profileTaylorCoefficient, div_eq_mul_inv]
  ring

/-- Taylor subtraction through degree `d` leaves a bounded quotient on `(0, 1)`. -/
theorem exists_gaussianProfile_sub_taylor_div_pow_bound (d : ℕ) (u₀ u₂ γ : ℝ) :
    ∃ C : ℝ, ∀ u ∈ Ioo (0 : ℝ) 1,
      ‖(gaussianProfile u₀ u₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
          u ^ (d + 1)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1)
    (n := d) zero_le_one (contDiff_gaussianProfile u₀ u₂ γ (d + 1)).contDiffOn
  refine ⟨C, fun u hu => ?_⟩
  have hrem := hC u ⟨hu.1.le, hu.2.le⟩
  rw [taylorWithinEval_gaussianProfile, sub_zero] at hrem
  rw [norm_div, Real.norm_eq_abs (u ^ (d + 1)), abs_of_pos (pow_pos hu.1 _)]
  exact (div_le_iff₀ (pow_pos hu.1 _)).2 hrem

/-- The Taylor-subtracted integrand in the finite part is integrable at zero. -/
theorem integrableOn_gaussianProfile_sub_taylor_div_pow_Ioo (d : ℕ) (u₀ u₂ γ : ℝ) :
    IntegrableOn (fun u : ℝ =>
      (gaussianProfile u₀ u₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
          u ^ (d + 1)) (Ioo 0 1) := by
  obtain ⟨C, hC⟩ := exists_gaussianProfile_sub_taylor_div_pow_bound d u₀ u₂ γ
  apply IntegrableOn.of_bound (measure_Ioo_lt_top) (C := C)
  · apply Measurable.aestronglyMeasurable
    exact ((contDiff_gaussianProfile u₀ u₂ γ 0).continuous.measurable.sub
      (Finset.measurable_sum _ fun j _ => measurable_const.mul
        (measurable_id.pow_const _))).div (measurable_id.pow_const _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hC u hu

end EinsteinFull
