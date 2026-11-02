import EinsteinFull.Frozen.EndpointComparisonError
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The two bilinear correlation errors in equation e:bridge. -/
noncomputable def forcedComparisonError {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R) (z : ℂ) (i : Fin d)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) : ℝ :=
  let T : ℝ := R ^ 2 / 2
  let hT : 0 < T := by positivity
  let ζ := z / (R : ℂ)
  ‖velocityCorrelation Q ⟨0, by omega⟩ i ζ P β a (R ^ 2).toNNReal -
      ∫ ω, modelTransposeEndpoint hd Q Z T hT ζ ω *
        modelVelocityEndpoint hd Q Z i T hT ζ ω ∂reducedLaw Q‖ +
  ‖clockCorrelation Q ⟨0, by omega⟩ ζ P β μ (R ^ 2).toNNReal -
      ∫ ω, modelTransposeEndpoint hd Q Z T hT ζ ω *
        modelClockEndpoint hd Q Z T hT ζ ω ∂reducedLaw Q‖

end EinsteinFull
