import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.ConditionalCopyEuclideanJensen
import EinsteinRelation.Correctors.SharedObservationCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance nestedCopyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Enlarging the observed spatial set costs at most a factor of two in
the coupled Euclidean difference norm. Source: `paper/main.tex:878–886`. -/
theorem eLpNorm_reducedCopy_difference_le_of_subset
    {d : ℕ} (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (f : FieldPair d → EuclideanSpace ℝ (Fin d))
    (hfm : Measurable f) (hfi : Integrable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    eLpNorm (fun z : C(V, Mat d) × (FieldPair d × FieldPair d) => f z.2.1-f z.2.2)
      p (reducedConditionalCopyLaw μ V) ≤
    2 * eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => f z.2.1-f z.2.2)
      p (reducedConditionalCopyLaw μ U) := by
  obtain ⟨_,h₁,h₂,heq⟩ := reducedConditionalCopy_properties μ V hV
  have hm₁ : MeasurePreserving
      (fun z : C(V, Mat d) × (FieldPair d × FieldPair d) => z.2.1)
      (reducedConditionalCopyLaw μ V) μ := ⟨measurable_fst.comp measurable_snd,h₁⟩
  have hm₂ : MeasurePreserving
      (fun z : C(V, Mat d) × (FieldPair d × FieldPair d) => z.2.2)
      (reducedConditionalCopyLaw μ V) μ := ⟨measurable_snd.comp measurable_snd,h₂⟩
  have hshared : ∀ᵐ z ∂reducedConditionalCopyLaw μ V,
      reducedCoefficientRestriction U z.2.1 = reducedCoefficientRestriction U z.2.2 := by
    filter_upwards [heq] with z hz
    apply ContinuousMap.ext
    intro x
    exact hz (hUV x.property)
  exact (coupled_difference_le_shared_observation_residual μ
    (reducedConditionalCopyLaw μ V) _ _ hm₁ hm₂ (reducedCoefficientRestriction U)
    (measurable_reducedCoefficientRestriction U) f hfm hfi hp hshared).trans
    (mul_le_mul_right
      (eLpNorm_conditional_error_piL2_le_copy_difference (Fin d) μ
        (reducedCoefficientRestriction U) (measurable_reducedCoefficientRestriction U)
        hp hpt hfm hfi) 2)
end EinsteinRelation.Correctors
