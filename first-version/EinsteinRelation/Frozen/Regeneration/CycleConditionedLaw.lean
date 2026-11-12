import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Frozen.Regeneration.CycleConditioningEvent
import Mathlib.Probability.ConditionalProbability

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinRelation.Regeneration

/-- The literal law conditioned on the actual no-backtracking event, with its positive mass explicit. -/
noncomputable def cycleConditionedLaw {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (hd : 2 ≤ d) (R : ℝ)
    (hD : (annealedCoupledLaw Q K) (cycleConditioningEvent hd R) ≠ 0) :
    {μ : Measure (FieldPair d × CoupledSample d) // IsProbabilityMeasure μ} := by
  letI : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  exact ⟨ProbabilityTheory.cond (annealedCoupledLaw Q K) (cycleConditioningEvent hd R),
    ProbabilityTheory.cond_isProbabilityMeasure hD⟩

end EinsteinRelation.Regeneration
