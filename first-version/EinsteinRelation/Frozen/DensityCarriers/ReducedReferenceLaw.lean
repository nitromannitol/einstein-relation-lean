import EinsteinRelation.Environment.Reduction

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Frozen.DensityCarriers

/-- The reduced coefficient and clock law induced by the physical environment law. -/
def reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Measure (FieldPair d) :=
  Measure.map reduce Q.measure

end EinsteinRelation.Frozen.DensityCarriers
