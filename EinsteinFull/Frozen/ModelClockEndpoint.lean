import EinsteinFull.Frozen.HomogeneousAverage
import EinsteinFull.Frozen.JointObservation

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

/-- The model clock endpoint zeta exp(T Lbar_zeta)(mu-E mu). -/
noncomputable def modelClockEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (T : ℝ) (hT : 0 < T) (ζ : ℂ) : Lp ℂ 2 (reducedLaw Q) :=
  ζ • homogeneousAverage Q ⟨0, by omega⟩ T hT ζ (Z (.inr ()))

end EinsteinFull
