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

/-- Graph node `p:late#dyadic-increments`, `paper/main.tex:1073–1080`.
Stationary Euclidean L² bounds and joint-local approximants for the actual
velocity and transpose flux increments, including the first unit interval. -/
def node_p_u3A_late_u23_dyadic_u2D_incrementsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∃ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F ∧
      (‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖ ^ 2) ≤ C ∧
        ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, IsComplexLocalObservation Q (C * n) (V j)) ∧
          Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤
            C * Real.exp (-c * (n : ℝ) ^ 2)) ∧
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
        ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
        ∃ Y B : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, (Y j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
            fun ω => ∑ k : Fin d, a j k ω *
              (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k) ω) ∧
          (∀ j, (B j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
            fun ω => ν.elim (fun _ => 0) (fun _ =>
              -2 * ζ * a j ⟨0, by omega⟩ ω *
                (∫ r in Set.Icc (s : ℝ) (u : ℝ),
                  transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)) ∧
          (∀ j, F u ν j - F s ν j = Y j + B j) ∧
          Real.sqrt (∑ j : Fin d, ‖Y j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
          Real.sqrt (∑ j : Fin d, ‖B j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
          ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
            (∀ j, IsComplexLocalObservation Q (C * n * Real.sqrt (s : ℝ)) (V j)) ∧
            Real.sqrt (∑ j : Fin d, ‖F u ν j - F s ν j - V j‖ ^ 2) ≤
              C * (2 + (s : ℝ)) ^ N * Real.exp (-c * (n : ℝ) ^ 2)

end EinsteinFull.Blueprint
