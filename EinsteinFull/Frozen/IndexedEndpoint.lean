import EinsteinFull.Frozen.EndpointIndex
import EinsteinFull.Frozen.EndpointCollection

open MeasureTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The actual d+2 stationary endpoints, retaining which equation each solves. -/
noncomputable def indexedEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) :=
  match ν with
  | .inl i => velocityEndpoint Q ⟨0, by omega⟩ i ζ P β a t
  | .inr true => transposeEndpoint Q ⟨0, by omega⟩ Pdag β t
  | .inr false => clockEndpoint Q ζ P μ t

end EinsteinFull
