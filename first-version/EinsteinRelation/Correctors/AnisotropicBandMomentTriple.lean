import EinsteinRelation.Correctors.UniformAnisotropicBandMoments
import EinsteinRelation.Correctors.KernelWeakCalculus

/-! # Joint moment bounds for a band and its first two derivatives

Source: `paper/main.tex:1033–1041`. One constant, chosen before the law,
controls the actual scalar band, gradient, and Hessian used in the corrector.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Sharp band moments in the three orders needed by the corrected
function (`paper/main.tex:1033–1041`). -/
theorem anisotropicBand_moment_triple {d : ℕ} (hd : 2 ≤ d)
    {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(T (unitVector i)) j| ≤ b) →
      ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q], IsStationary Q →
      ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M r R : ℝ), 0 < M → 0 < r → 0 < R → r ≤ R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (anisotropicBandKernel T r) f) p Q ≤
          ENNReal.ofReal (C * M * r) ∧
      (∀ i, eLpNorm (fun ω => kernelGradient (anisotropicBandKernel T r) f ω i) p Q ≤
          ENNReal.ofReal (C * M)) ∧
      (∀ i j, eLpNorm (fun ω => kernelHessian (anisotropicBandKernel T r) f ω i j) p Q ≤
          ENNReal.ofReal (C * M / r)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := eLpNorm_anisotropicBand_uniform_le hd hb 0
  obtain ⟨C₁, hC₁, h₁⟩ := eLpNorm_anisotropicBand_uniform_le hd hb 1
  obtain ⟨C₂, hC₂, h₂⟩ := eLpNorm_anisotropicBand_uniform_le hd hb 2
  let C := C₀ + C₁ + C₂
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity,
    fun T hT Q _ hQ p hp hpt M r R hM hr hR hrR f hf hheat => ?_⟩
  constructor
  · have h := h₀ T hT [] rfl Q hQ p hp hpt M r R hM hr hR hrR f hf hheat
    simp only [coordinateIterate, pow_zero, div_one] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hM hr]))
  constructor
  · intro i
    have h := h₁ T hT [i] rfl Q hQ p hp hpt M r R hM hr hR hrR f hf hheat
    simp only [pow_one, div_self hr.ne', mul_one] at h
    change eLpNorm (-(horizontalMollify (coordinateIterate [i] (anisotropicBandKernel T r)) f)) p Q ≤ _
    rw [eLpNorm_neg]
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc₁ hM.le))
  · intro i j
    have h := h₂ T hT [j, i] rfl Q hQ p hp hpt M r R hM hr hR hrR f hf hheat
    change eLpNorm (horizontalMollify (coordinateIterate [j, i] (anisotropicBandKernel T r)) f) p Q ≤ _
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have he : C₂ * M * (r / r ^ 2) = C₂ * M / r := by field_simp [hr.ne']
    rw [he]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ hM.le) hr.le

end EinsteinRelation.Correctors
