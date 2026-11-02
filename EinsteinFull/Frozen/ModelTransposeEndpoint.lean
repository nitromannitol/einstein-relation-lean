import EinsteinFull.Frozen.HomogeneousDerivativeAverage
import EinsteinFull.Frozen.JointObservation

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

/-- The model transpose endpoint (1/2) exp(T Lbar_{-zeta}) div Xi_1. -/
noncomputable def modelTransposeEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (T : ℝ) (hT : 0 < T) (ζ : ℂ) : Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℂ) • ∑ j : Fin d,
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ T hT (-ζ) 1 (fun _ => j)
      (Z (.inl (j, ⟨0, by omega⟩)))

end EinsteinFull
