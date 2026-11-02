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

/-- Graph node `stationary-analytic-semigroup#flux`, `paper/main.tex:1082`.
Holomorphy is in stationary complex L² of the reduced joint law. Polynomial
bounded-disc control here is only unweighted L² control; spatial averaging
seminorm bounds belong to the separate dyadic/Cauchy node. -/
def node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
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
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (ν : FluxIndex d) (j : Fin d),
        DifferentiableOn ℂ (fun ζ => F ζ t ν j)
          {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} ∧
        DifferentiableOn ℂ (fun ζ => deriv (fun z => F z t ν j) ζ)
          {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3}) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (ν : FluxIndex d) (ρ : ℝ),
        1 ≤ ρ → ∀ j : Fin d,
        DifferentiableOn ℂ (fun ζ => A ζ t ν ρ j)
          {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3} ∧
        DifferentiableOn ℂ (fun ζ => deriv (fun z => A z t ν ρ j) ζ)
          {ζ | ‖ζ‖ * Real.sqrt (t : ℝ) < 3}) ∧
      ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ∀ (ν : FluxIndex d),
        (∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
          Real.sqrt (∑ j : Fin d, ‖F ζ t ν j‖ ^ 2) ≤ C * (2 + (t : ℝ)) ^ N) ∧
        ∀ ρ : ℝ, 1 ≤ ρ → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
          Real.sqrt (∑ j : Fin d, ‖deriv (fun z => A z t ν ρ j) ζ‖ ^ 2) ≤
            C * Real.sqrt (t : ℝ) * (2 + (t : ℝ)) ^ N

end EinsteinFull.Blueprint
