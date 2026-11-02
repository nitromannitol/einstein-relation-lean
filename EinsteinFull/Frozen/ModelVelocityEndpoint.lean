import EinsteinFull.Frozen.HomogeneousDerivativeAverage
import EinsteinFull.Frozen.JointObservation

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

/-- The model velocity endpoint exp(T Lbar_zeta)((1/2) div Xi_i+zeta Xi_{1i}). -/
noncomputable def modelVelocityEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (i : Fin d) (T : ℝ) (hT : 0 < T) (ζ : ℂ) : Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℂ) • (∑ j : Fin d,
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ T hT ζ 1 (fun _ => j)
      (Z (.inl (j,i)))) +
  ζ • homogeneousAverage Q ⟨0, by omega⟩ T hT ζ (Z (.inl (⟨0, by omega⟩,i)))

end EinsteinFull
