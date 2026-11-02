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
import EinsteinFull.Frozen.ComplexLocalObservation
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:late#cauchy`, `paper/main.tex:1082`.
Outer-disc averaging control, inner-disc Cauchy derivative and force replacement
for the actual flux family. All constants precede the law and averaging radius. -/
def node_p_u3A_late_u23_cauchyStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∃ G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (Pdag ζ) β a μ (G ζ) (F ζ)) ∧
      let A := fun (ζ : ℂ) (t : ℝ≥0) (ν : FluxIndex d) (ρ : ℝ) (j : Fin d) =>
        ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (centeredComplexLp Q (F ζ t ν j))
      (∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ∀ ν : FluxIndex d,
        ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
          gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F ζ t ν j)) ≤
            ENNReal.ofReal (C * Real.log (2 + (t : ℝ)) ^ M)) ∧
      (∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ∀ ν : FluxIndex d,
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
          (∀ j, DifferentiableAt ℂ (fun z => A z t ν ρ j) ζ) ∧
          ρ ^ ((d : ℝ) / 2) *
            Real.sqrt (∑ j : Fin d, ‖deriv (fun z => A z t ν ρ j) ζ‖ ^ 2) ≤
              C * Real.sqrt (t : ℝ) * Real.log (2 + (t : ℝ)) ^ M) ∧
      ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ∀ ν : FluxIndex d,
        ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
          gaussianAveragingSeminorm hd Q
            (fun j => centeredComplexLp Q (F ζ t ν j - F 0 t ν j)) ≤
            ENNReal.ofReal (C * ‖ζ‖ * Real.sqrt (t : ℝ) * Real.log (2 + (t : ℝ)) ^ M)

end EinsteinFull.Blueprint
