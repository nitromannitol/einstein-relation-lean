import EinsteinRelation.Correctors.TimeIntegralLpBound

/-! # Probability averages with almost-everywhere section bounds

Source: `paper/main.tex:1028–1041`. A common moment bound on almost every
parameter section passes to the actual parameter integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Probability integration preserves a common finite-exponent seminorm
bound (`paper/main.tex:1028–1041`). -/
theorem eLpNorm_integral_probability_le_ae_bound
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [SFinite μ] (ν : Measure S) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {g : Ω × S → ℝ}
    (hg : Measurable g) {B : ℝ≥0∞}
    (hb : ∀ᵐ z ∂ν, eLpNorm (fun ω => g (ω, z)) p μ ≤ B) :
    eLpNorm (fun ω => ∫ z, g (ω, z) ∂ν) p μ ≤ B := by
  have hJ := eLpNorm_kernel_integral_le (μ := μ) (Kernel.const Ω ν) hp hpt hg.stronglyMeasurable
  simp only [Kernel.const_apply, Measure.compProd_const] at hJ
  apply hJ.trans
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpower : ∀ᵐ z ∂ν, (∫⁻ ω, ‖g (ω, z)‖ₑ ^ p.toReal ∂μ) ≤ B ^ p.toReal := by
    filter_upwards [hb] with z hz
    have h := ENNReal.rpow_le_rpow hz hpr.le
    rw [eLpNorm_eq_eLpNorm' hp0 hpt,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr] at h
    exact h
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    lintegral_prod_symm _ (hg.enorm.pow_const p.toReal).aemeasurable]
  calc
    _ ≤ (∫⁻ _ : S, B ^ p.toReal ∂ν) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpower) (one_div_nonneg.mpr hpr.le)
    _ = B := by
      simp only [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul,
        mul_one_div_cancel hpr.ne', ENNReal.rpow_one]

end EinsteinRelation.Correctors
