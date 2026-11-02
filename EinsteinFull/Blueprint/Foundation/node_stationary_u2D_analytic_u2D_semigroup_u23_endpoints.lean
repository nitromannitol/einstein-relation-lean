import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.IndexedEndpoint
import EinsteinFull.Frozen.ComplexLocalObservation
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `stationary-analytic-semigroup#endpoints`,
`paper/main.tex:749–754`. The actual stationary endpoints have finite-p
holomorphic representatives on bounded time intervals. Jointly local,
centered approximants have holomorphic Gaussian errors on the larger disc;
the endpoint difference and its local approximation factor through force zero
on the smaller disc. Constants precede the coefficient law. -/
def node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ) (hp : 2 ≤ p) (T B : ℝ), 0 ≤ T → 0 < B →
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ (ν : EndpointIndex d) (t : ℝ≥0), (t : ℝ) ≤ T →
    ∃ E H : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (∀ ζ, (E ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        (indexedEndpoint hd Q ν ζ (P ζ) (Pdag ζ) β a μ t : FieldPair d → ℂ)) ∧
      DifferentiableOn ℂ E {ζ | ‖ζ‖ < B + 1} ∧
      DifferentiableOn ℂ H {ζ | ‖ζ‖ < B} ∧
      (∀ ζ, ‖ζ‖ ≤ B + 1 → ‖E ζ‖ ≤ C) ∧
      (∀ ζ, ‖ζ‖ < B → E ζ - E 0 = ζ • H ζ ∧
        (∫ ω, H ζ ω ∂reducedLaw Q) = 0 ∧ ‖H ζ‖ ≤ C) ∧
      ∀ ρ : ℝ, C ≤ ρ →
      ∃ L K : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      ∃ L₂ K₂ : ℂ → Lp ℂ 2 (reducedLaw Q),
        (∀ ζ, (L ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] L₂ ζ ∧
          (K ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q] K₂ ζ ∧
          IsComplexLocalObservation Q ρ (L₂ ζ) ∧
          IsComplexLocalObservation Q ρ (K₂ ζ)) ∧
        DifferentiableOn ℂ L {ζ | ‖ζ‖ < B + 1} ∧
        DifferentiableOn ℂ (fun ζ => E ζ - L ζ) {ζ | ‖ζ‖ < B + 1} ∧
        DifferentiableOn ℂ K {ζ | ‖ζ‖ < B} ∧
        DifferentiableOn ℂ (fun ζ => H ζ - K ζ) {ζ | ‖ζ‖ < B} ∧
        (∀ ζ, ‖ζ‖ ≤ B + 1 →
          (∫ ω, L ζ ω ∂reducedLaw Q) = 0 ∧
          ‖L ζ‖ ≤ C ∧ ‖E ζ - L ζ‖ ≤ C * Real.exp (-c * ρ ^ 2)) ∧
        (∀ ζ, ‖ζ‖ < B →
          L ζ - L 0 = ζ • K ζ ∧
          (E ζ - L ζ) - (E 0 - L 0) = ζ • (H ζ - K ζ) ∧
          (∫ ω, K ζ ω ∂reducedLaw Q) = 0 ∧
          ‖K ζ‖ ≤ C ∧ ‖H ζ - K ζ‖ ≤ C * Real.exp (-c * ρ ^ 2))

end EinsteinFull.Blueprint
