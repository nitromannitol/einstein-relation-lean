import EinsteinFull.Frozen.ModelTransposeEndpoint
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelClockEndpoint
import EinsteinFull.Frozen.TransposeEndpoint
import EinsteinFull.Frozen.VelocityEndpoint
import EinsteinFull.Frozen.ClockEndpoint

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The literal sum of d+2 L² endpoint errors at T=R²/2 and force z/R. -/
noncomputable def endpointComparisonError {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R) (z : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) : ℝ :=
  let T : ℝ := R ^ 2 / 2
  let hT : 0 < T := by positivity
  ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β T.toNNReal -
      modelTransposeEndpoint hd Q Z T hT (z / (R : ℂ))‖ +
  (∑ i : Fin d, ‖velocityEndpoint Q ⟨0, by omega⟩ i (z / (R : ℂ)) P β a T.toNNReal -
      modelVelocityEndpoint hd Q Z i T hT (z / (R : ℂ))‖) +
  ‖clockEndpoint Q (z / (R : ℂ)) P μ T.toNNReal -
      modelClockEndpoint hd Q Z T hT (z / (R : ℂ))‖

end EinsteinFull
