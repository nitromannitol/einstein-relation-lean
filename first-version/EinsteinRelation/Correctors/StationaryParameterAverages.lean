import EinsteinRelation.Correctors.StationaryKernelConvolution

/-! # Stationary averages along measurable displacement maps

Source: `paper/main.tex:1028–1029`. Probability averaging over a parameter
space contracts moments when every integrand is a stationary translate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- A probability average of arbitrary measurable stationary displacements
contracts finite moments (`paper/main.tex:1028–1029`). -/
theorem eLpNorm_integral_stationary_param_le {d : ℕ} {S : Type*} [MeasurableSpace S]
    {Q : Measure (FieldPair d)} [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure S) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : FieldPair d → ℝ} (hf : Measurable f) {T : S → Vec d} (hT : Measurable T)
    {a : S → ℝ} (ha : Measurable a) (hab : ∀ z, |a z| ≤ 1) :
    eLpNorm (fun ω => ∫ z, a z * f (translate (T z) ω) ∂ν) p Q ≤ eLpNorm f p Q := by
  have ht : Measurable (fun q : FieldPair d × S => translate (T q.2) q.1) :=
    Probability.continuous_translate.measurable.comp ((hT.comp measurable_snd).prodMk measurable_fst)
  have hF : StronglyMeasurable (fun q : FieldPair d × S => a q.2 * f (translate (T q.2) q.1)) :=
    ((ha.comp measurable_snd).mul (hf.comp ht)).stronglyMeasurable
  have hJ := eLpNorm_kernel_integral_le (μ := Q) (Kernel.const (FieldPair d) ν) hp hpt hF
  simp only [Kernel.const_apply, Measure.compProd_const] at hJ
  apply hJ.trans
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm hp0 hpt]
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hpr.le)
  rw [lintegral_prod_symm _ (hF.enorm.pow_const p.toReal).aemeasurable]
  calc
    (∫⁻ z, ∫⁻ ω, ‖a z * f (translate (T z) ω)‖ₑ ^ p.toReal ∂Q ∂ν) ≤
        ∫⁻ z, ∫⁻ ω, ‖f (translate (T z) ω)‖ₑ ^ p.toReal ∂Q ∂ν := by
      apply lintegral_mono
      intro z
      apply lintegral_mono
      intro ω
      apply ENNReal.rpow_le_rpow _ hpr.le
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hab z)
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂Q := by
      have hs (z : S) : (∫⁻ ω, ‖f (translate (T z) ω)‖ₑ ^ p.toReal ∂Q) =
          ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂Q := by
        rw [← lintegral_map (hf.enorm.pow_const p.toReal) (Probability.measurable_translate (T z)),
          hQ (T z)]
      simp only [hs, lintegral_const, measure_univ, mul_one]

end EinsteinRelation.Correctors
