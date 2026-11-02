import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.FiniteTimeFlux
import EinsteinFull.Frozen.GaussianAveragingSeminorm
import EinsteinFull.Frozen.CenteredComplexLp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Exact statement mirror of `p:late`; frozen declaration
`EinsteinFull.Frozen.late_force_replacement`, source `paper/main.tex:1045–1054`.
No anchor import or conclusion-bearing premise is used. -/
def node_p_u3A_lateStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag P₀ P₀dag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P₀ →
      IsComplexTransposeSemigroup Q P₀ P₀dag →
    ∃ G F G₀ F₀ : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F ∧
      IsFiniteTimeFlux hd Q 0 P₀ P₀dag β a μ G₀ F₀ ∧
      ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
      ∀ ν : FluxIndex d,
        gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F t ν j)) ≤
          ENNReal.ofReal (C * Real.log (2 + (t : ℝ)) ^ M) ∧
        gaussianAveragingSeminorm hd Q
          (fun j => centeredComplexLp Q (F t ν j - F₀ t ν j)) ≤
          ENNReal.ofReal (C * ‖ζ‖ * Real.sqrt (t : ℝ) *
            Real.log (2 + (t : ℝ)) ^ M)

end EinsteinFull.Blueprint
