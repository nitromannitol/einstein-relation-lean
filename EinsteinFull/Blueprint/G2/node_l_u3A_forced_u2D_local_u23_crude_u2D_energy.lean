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

/-- Node `l:forced-local#crude-energy`, `paper/main.tex:666` (proof: 713–715).
Deterministic endpoint and Euclidean gradient bounds; no moment-order constant. -/
def node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t)) ∧
      (∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        (∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
            Real.sqrt (∑ j : Fin d, ‖G t j ω‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) ∧
        (∀ (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
            localSpatialEnergy Q t ρ hρ x (G t) 0 ω ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))))

end EinsteinFull.Blueprint
