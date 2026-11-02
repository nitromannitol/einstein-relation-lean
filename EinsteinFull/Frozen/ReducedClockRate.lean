import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinRelation.Clock.ClockSpeedMeaningSupport

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The deterministic quenched rate of the actual reduced path clock
`A(t) = ∫_0^t exp(-2V(Y(s))) ds`, under a given origin path kernel. -/
def HasReducedClockRate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Y : QuenchedPathLaws d) (η : ℝ) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
    EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η

end EinsteinFull
