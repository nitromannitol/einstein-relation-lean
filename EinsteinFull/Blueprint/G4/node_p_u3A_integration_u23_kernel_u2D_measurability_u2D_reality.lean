import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:integration#kernel-measurability-reality`, `paper/main.tex:578`.
Actual bilinear correlations are time measurable at each complex force
and real at real force, coordinate by coordinate. -/
def node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_realityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)),
    IsReducedDriftObservation Q hQ β →
    IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    (∀ ζ : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) ζ (P ζ)) →
    (∀ (ζ : ℂ) (i : Fin d),
      Measurable (fun t : ℝ => velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i ζ (P ζ) β a t.toNNReal)) ∧
    (∀ ζ : ℂ, Measurable (fun t : ℝ => clockCorrelation Q (⟨0, by omega⟩ : Fin d) ζ (P ζ) β μ t.toNNReal)) ∧
    (∀ (lam : ℝ) (t : ℝ≥0) (i : Fin d),
      (velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i (lam : ℂ)
        (P (lam : ℂ)) β a t).im = 0) ∧
    ∀ (lam : ℝ) (t : ℝ≥0),
      (clockCorrelation Q (⟨0, by omega⟩ : Fin d) (lam : ℂ)
        (P (lam : ℂ)) β μ t).im = 0

end EinsteinFull.Blueprint
