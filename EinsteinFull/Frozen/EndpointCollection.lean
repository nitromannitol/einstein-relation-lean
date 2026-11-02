import EinsteinFull.Frozen.TransposeEndpoint
import EinsteinFull.Frozen.VelocityEndpoint
import EinsteinFull.Frozen.ClockEndpoint

open MeasureTheory
open scoped NNReal

namespace EinsteinFull

open EinsteinRelation

/-- Precisely the d+2 displayed scalar endpoints, including the clock endpoint. -/
def endpointCollection {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) : Set (Lp ℂ 2 (reducedLaw Q)) :=
  {transposeEndpoint Q i Pdag β t} ∪
    Set.range (fun j => velocityEndpoint Q i j ζ P β a t) ∪
    {clockEndpoint Q ζ P μ t}

end EinsteinFull
