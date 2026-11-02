import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinRelation.Probability.ReductionLocality

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The actual pushforward law of the time-changed pair `(a, μ)` in Section 2.
Its second coordinate is the clock density, not a potential. -/
noncomputable def reducedLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Measure (FieldPair d) :=
  Q.measure.map reduce

end EinsteinFull
