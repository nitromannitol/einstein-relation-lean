import EinsteinRelation.Diffusion.Basic

open MeasureTheory ProbabilityTheory

noncomputable section

namespace EinsteinRelation.Frozen.ValidAnnealedLawCarriers

/-- Probability-law data for the physical path at the origin and the environment law. -/
structure CoordinatePathLawInput (d : ℕ) (hd : 2 ≤ d) where
  Q : Measure (FieldPair d)
  Q_probability : IsProbabilityMeasure Q
  P : QuenchedPathLaws d
  origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)

end EinsteinRelation.Frozen.ValidAnnealedLawCarriers
