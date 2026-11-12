import EinsteinRelation.External.GantertSection7Support
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Probability

/-- Source `paper/main.tex:406–408`: detailed balance is preserved by a change of coordinates and a constant rescaling of the reference measure. -/
theorem conjugate_kernel_reversible {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hm : μ.map e = c • ν) (K : Kernel α α)
    (hr : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      (∫⁻ x in A, K x B ∂ν) = ∫⁻ x in B, K x A ∂ν) :
    ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      (∫⁻ x in A, (((K.comap e e.measurable).map e.symm) x) B ∂μ) =
        ∫⁻ x in B, (((K.comap e e.measurable).map e.symm) x) A ∂μ := by
  have hi (A : Set α) (hA : MeasurableSet A) (F : α → ℝ≥0∞) (hF : Measurable F) :
      (∫⁻ x in A, F (e x) ∂μ) = c * ∫⁻ y in e.symm ⁻¹' A, F y ∂ν := by
    calc
      _ = ∫⁻ y in e.symm ⁻¹' A, F y ∂μ.map e := by
        rw [setLIntegral_map (e.symm.measurable hA) hF e.measurable]
        simp only [Set.preimage_preimage, e.symm_apply_apply]
        rfl
      _ = _ := by rw [hm, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  intro A B hA hB
  have hB' := e.symm.measurable hB
  have hA' := e.symm.measurable hA
  simp only [Kernel.map_apply _ e.symm.measurable, Kernel.comap_apply,
    Measure.map_apply e.symm.measurable hA, Measure.map_apply e.symm.measurable hB]
  rw [hi A hA _ (K.measurable_coe hB'), hi B hB _ (K.measurable_coe hA'),
    hr _ _ hA' hB']

end EinsteinRelation.Probability
