import EinsteinFull.Frozen.IndexedEndpoint
import EinsteinFull.Frozen.HomogenizedCoefficient
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.ReducedLawStationary

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The actual centered-weak-flux precursor: (a-A)Du forward and
(a-A)(Du-2*zeta*e_1*u) transpose. The gradient relation is literal;
this predicate contains no norm or approximation estimate. -/
def IsEndpointWeakFlux {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (U : Lp ℂ 2 (reducedLaw Q)) (G J : Fin d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U G ∧
  ∀ j : Fin d, (J j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
    ∑ k : Fin d, (a j k ω - (homogenizedCoefficient Q j k : ℂ)) *
      (G k ω - match ν with
        | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω
        | _ => 0)

end EinsteinFull
