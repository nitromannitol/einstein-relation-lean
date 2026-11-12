import EinsteinRelation.Regeneration.Coupling

open MeasureTheory ProbabilityTheory

noncomputable section

namespace EinsteinRelation.Frozen.ValidAnnealedLawCarriers

/-- Probability-law data for the coupled path/Bernoulli sample and environment law. -/
structure CoupledPathLawInput (d : ℕ) (hd : 2 ≤ d) where
  Q : Measure (FieldPair d)
  Q_probability : IsProbabilityMeasure Q
  K : Regeneration.CoupledQuenchedLaws d
  origin_probability : ∀ᵐ ω ∂Q,
    IsProbabilityMeasure (Regeneration.originCoupledLaw K ω)

end EinsteinRelation.Frozen.ValidAnnealedLawCarriers
