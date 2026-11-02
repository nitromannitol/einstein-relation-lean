import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `finite-time-analyticity`, `paper/main.tex:578`.
Entire complex-force dependence and compact-time/disc bounds for the actual
kernels. The bound precedes the law, observations and semigroup family. -/
def node_finite_u2D_time_u2D_analyticityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (T R : ℝ), 0 ≤ T → 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    (∀ ζ : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) ζ (P ζ)) →
    (∀ (t : ℝ≥0) (i : Fin d),
      Differentiable ℂ (fun ζ =>
        velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t)) ∧
    (∀ t : ℝ≥0, Differentiable ℂ (fun ζ =>
      clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t)) ∧
    ∀ (t : ℝ≥0) (ζ : ℂ), (t : ℝ) ≤ T → ‖ζ‖ ≤ R →
      ∀ i : Fin d,
        ‖velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t‖ +
          ‖clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t‖ ≤ C

end EinsteinFull.Blueprint
