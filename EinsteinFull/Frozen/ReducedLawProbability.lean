import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The literal time-change pushforward is a probability law. -/
theorem reducedLaw_probability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) := by
  unfold reducedLaw
  infer_instance

end EinsteinFull
