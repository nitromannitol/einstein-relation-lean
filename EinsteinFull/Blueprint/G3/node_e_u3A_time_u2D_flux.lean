import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.FiniteTimeFlux

open MeasureTheory
open scoped BigOperators NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:time-flux`, `paper/main.tex:1026–1043`.
Construct the actual endpoint gradients and literal time-integrated fluxes,
including their continuous-orbit integrability witnesses. The two endpoint
identities are stationary distributional identities tested against every
horizontal H1 function. The forward identity uses the uncentered endpoint;
its gradient agrees with that of the centered indexed endpoint. The transpose
is the actual bilinear transpose, and its conservative flux retains -2*zeta.
No gradient, flux, integral-existence or divergence premise is supplied. -/
def node_e_u3A_time_u2D_fluxStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∃ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F ∧
      ∀ (t : ℝ≥0) (v : Lp ℂ 2 (reducedLaw Q))
        (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
        (∀ i : Fin d,
          (∫ ω, (P t (β i + ζ • a ⟨0, by omega⟩ i)) ω * v ω ∂reducedLaw Q) =
            -(1 / 2 : ℂ) * (∫ ω, ∑ j, F t (.inl i) j ω * V j ω ∂reducedLaw Q) +
              ζ * (∫ ω, F t (.inl i) ⟨0, by omega⟩ ω * v ω ∂reducedLaw Q)) ∧
        (∫ ω, (Pdag t (β ⟨0, by omega⟩)) ω * v ω ∂reducedLaw Q) =
          -(1 / 2 : ℂ) * (∫ ω, ∑ j, F t (.inr ()) j ω * V j ω ∂reducedLaw Q)

end EinsteinFull.Blueprint
