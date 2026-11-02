import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinFull.Frozen.UncenteredEndpoint
import EinsteinFull.Frozen.ComplexLocalObservation
import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.CubeIntegralObservation
import EinsteinFull.Frozen.GaussianAverage
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:forced-locality`, `paper/main.tex:715`.
The actual uncentered endpoint and its horizontal gradient admit jointly local
approximants with a Gaussian spatial error, including the centered scalar and
cube-integral conclusions. The polynomial deterministic bound is retained.
The constants precede the law, force and endpoint. This is the smooth unit-scale
version used by the frozen local-estimates statement. -/
def node_e_u3A_forced_u2D_localityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ Cdet c : ℝ, ∃ N : ℕ, 1 ≤ Cdet ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t)) ∧
    (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, Cdet * Real.sqrt (t : ℝ) ≤ ρ →
      ∃ Uloc : Lp ℂ 2 (reducedLaw Q), ∃ Gloc : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexLocalObservation Q ρ Uloc ∧
      (∀ j, IsComplexLocalObservation Q ρ (Gloc j)) ∧
      (∀ᵐ ω ∂reducedLaw Q,
        ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - Uloc ω‖ +
          Real.sqrt (∑ j : Fin d, ‖G t j ω - Gloc j ω‖ ^ 2) ≤
        Cdet * (2 + (t : ℝ)) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
      (∀ᵐ ω ∂reducedLaw Q,
        ‖centeredComplexLp Q (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω -
          centeredComplexLp Q Uloc ω‖ ≤
        2 * Cdet * (2 + (t : ℝ)) ^ N *
          Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
      ∃ Ucube : Lp ℂ 2 (reducedLaw Q), ∃ Gcube : Fin d → Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) Ucube ∧
        (∀ j, IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (Gcube j)) ∧
        ∀ᵐ ω ∂reducedLaw Q,
          ‖cubeIntegralObservation Q ρ (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω - Ucube ω‖ +
          Real.sqrt (∑ j : Fin d,
            ‖cubeIntegralObservation Q ρ (G t j) ω - Gcube j ω‖ ^ 2) ≤
          Cdet * (2 + (t : ℝ) + ρ) ^ (N + d) *
            Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) ∧
    (∀ t : ℝ≥0, 0 < (t : ℝ) → ‖ζ‖ ≤ 4 → ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
        Real.sqrt (∑ j : Fin d, ‖G t j ω‖ ^ 2) ≤
      Cdet * (2 + (t : ℝ)) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ)))

end EinsteinFull.Blueprint
