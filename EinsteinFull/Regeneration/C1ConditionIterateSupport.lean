import EinsteinRelation.Regeneration.RenewalFromSliceFactor

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Conditioning a deterministic slice can be implemented by its measurable
past indicator when that indicator agrees with the conditioning event there. -/
theorem conditional_slice_of_indicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D S E : Set α) (hD : MeasurableSet D)
    (hS : MeasurableSet S)
    (hDE : ∀ᵐ x ∂μ.restrict S, x ∈ D ↔ x ∈ E)
    (f g : α → ℝ) (a : ℝ)
    (hfactor : (∫ x in S, E.indicator f x ∂μ) =
      (∫ x in S, E.indicator g x ∂μ) * a) :
    (∫ x in S, f x ∂ProbabilityTheory.cond μ D) =
      (∫ x in S, g x ∂ProbabilityTheory.cond μ D) * a := by
  have hind (u : α → ℝ) : (∫ x in S, u x ∂μ.restrict D) =
      ∫ x in S, E.indicator u x ∂μ := by
    rw [Measure.restrict_comm hS, ← integral_indicator hD]
    apply integral_congr_ae
    filter_upwards [hDE] with x hx
    by_cases hd : x ∈ D
    · simp only [Set.indicator_of_mem hd, Set.indicator_of_mem (hx.mp hd)]
    · simp only [Set.indicator_of_notMem hd,
        Set.indicator_of_notMem (mt hx.mpr hd)]
  change (∫ x in S, f x ∂((μ D)⁻¹ • μ.restrict D)) =
    (∫ x in S, g x ∂((μ D)⁻¹ • μ.restrict D)) * a
  simp only [Measure.restrict_smul]
  rw [integral_smul_measure, integral_smul_measure, hind f, hind g, hfactor]
  simp only [smul_eq_mul, mul_assoc]

end EinsteinFull.Regeneration
