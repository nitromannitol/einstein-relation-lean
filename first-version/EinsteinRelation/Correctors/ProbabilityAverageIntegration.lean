import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:751-753`. Integrating uniform annealed pointwise bounds. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

theorem lintegral_average_le_of_ae_section_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SFinite P] [SFinite μ]
    (hμ0 : μ Set.univ ≠ 0) (hμt : μ Set.univ ≠ ⊤)
    (F : Ω → X → ℝ≥0∞) (hF : Measurable (Function.uncurry F))
    (C : ℝ≥0∞) (hC : ∀ᵐ x ∂μ, (∫⁻ ω, F ω x ∂P) ≤ C) :
    (∫⁻ ω, (⨍⁻ x, F ω x ∂μ) ∂P) ≤ C := by
  have hμt_lt : μ Set.univ < ∞ := by
    simpa [lt_top_iff_ne_top] using hμt
  haveI : IsFiniteMeasure μ := ⟨hμt_lt⟩
  have hμuniv_ne_zero : μ Set.univ ≠ 0 := hμ0
  have hμuniv_ne_top : μ Set.univ ≠ ∞ := hμt
  have h_meas_inner : Measurable fun (ω : Ω) => ∫⁻ x, F ω x ∂μ :=
    hF.lintegral_prod_right
  have h_fubini : (∫⁻ ω, ∫⁻ x, F ω x ∂μ ∂P) = (∫⁻ x, ∫⁻ ω, F ω x ∂P ∂μ) :=
    (lintegral_prod (Function.uncurry F) hF.aemeasurable).symm.trans
      (lintegral_prod_symm (Function.uncurry F) hF.aemeasurable)
  calc
    (∫⁻ ω, (⨍⁻ x, F ω x ∂μ) ∂P) = (∫⁻ ω, ((μ Set.univ)⁻¹ * ∫⁻ x, F ω x ∂μ) ∂P) := by
      refine lintegral_congr (fun ω => ?_)
      rw [laverage_eq, ENNReal.div_eq_inv_mul]
    _ = (μ Set.univ)⁻¹ * (∫⁻ ω, ∫⁻ x, F ω x ∂μ ∂P) := by
      rw [lintegral_const_mul'' _ h_meas_inner.aemeasurable]
    _ = (μ Set.univ)⁻¹ * (∫⁻ x, ∫⁻ ω, F ω x ∂P ∂μ) := by rw [h_fubini]
    _ ≤ (μ Set.univ)⁻¹ * (∫⁻ x, C ∂μ) := by
      refine mul_le_mul_of_nonneg_left (lintegral_mono_ae hC) (zero_le _)
    _ = (μ Set.univ)⁻¹ * (C * μ Set.univ) := by simp [lintegral_const]
    _ = C * ((μ Set.univ)⁻¹ * μ Set.univ) := by
      simp [mul_comm, mul_assoc]
    _ = C * 1 := by rw [ENNReal.inv_mul_cancel hμuniv_ne_zero hμuniv_ne_top]
    _ = C := by simp

end EinsteinRelation.Correctors
