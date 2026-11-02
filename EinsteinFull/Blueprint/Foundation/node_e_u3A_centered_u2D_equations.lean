import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.EndpointDriftSign
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:centered-equations`, `paper/main.tex:741–747`.
The actual centered velocity/clock endpoints and conservative transpose endpoint
satisfy the displayed distributional equations at every positive time. The
homogeneous operator is written in its spatial weak form with the actual
homogenized matrix, drift sign and factor one-half. The flux relation produces
the actual gradient and both literal fluxes; no PDE or regularity is a premise.
The transpose has zero mean. -/
def node_e_u3A_centered_u2D_equationsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (ν : EndpointIndex d) (t : ℝ≥0), 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      ∃ (G J : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)),
        IsEndpointWeakFlux hd Q ν ζ a U G J ∧
        HasDerivAt (fun r : ℝ =>
          indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) V (t : ℝ) ∧
        (ν = Sum.inr true → (∫ ω, U ω ∂reducedLaw Q) = 0) ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            (∫ x, V (translate x ω) * (φ x : ℂ)) +
              (1 / 2 : ℂ) * (∫ x, ∑ j : Fin d, ∑ k : Fin d,
                (homogenizedCoefficient Q j k : ℂ) * G k (translate x ω) *
                  (coordinateDerivative j φ x : ℂ)) -
              (endpointDriftSign ν : ℂ) * ζ *
                (∫ x, (∑ j : Fin d,
                  (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
                    G j (translate x ω)) * (φ x : ℂ)) =
            -(1 / 2 : ℂ) * (∫ x, ∑ j : Fin d,
              J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) +
              (match ν with
                | .inr true => 0
                | _ => ζ * (∫ x,
                    (J ⟨0, by omega⟩ (translate x ω) -
                      ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * (φ x : ℂ)))

end EinsteinFull.Blueprint
