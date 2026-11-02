import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.VelocityCorrelation
import EinsteinFull.Frozen.ClockCorrelation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `p:tail`; frozen declaration
`EinsteinFull.Frozen.correlation_tail`, source `paper/main.tex:539–547`.
No anchor import or conclusion-bearing premise is used. -/
def node_p_u3A_tailStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c C_T : ℝ, 0 < C ∧ 0 < c ∧ 0 < C_T ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
      IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
      ∀ (lam : ℝ), 0 < |lam| → |lam| ≤ Real.exp (-1) →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P →
        ∀ (t : ℝ≥0), C_T / |lam| ^ 2 ≤ (t : ℝ) →
        ∀ j : Fin d,
          ‖velocityCorrelation Q (⟨0, by omega⟩ : Fin d) j (lam : ℂ) P β a t‖ ≤
              C * |lam| ^ (d + 2) *
                Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) -
                  c * lam ^ 2 * (t : ℝ)) ∧
          ‖clockCorrelation Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P β μ t‖ ≤
              C * |lam| ^ (d + 2) *
                Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) -
                  c * lam ^ 2 * (t : ℝ))

end EinsteinFull.Blueprint
