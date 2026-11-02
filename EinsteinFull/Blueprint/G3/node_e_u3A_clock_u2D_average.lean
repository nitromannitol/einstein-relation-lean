import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointWeakFlux
import EinsteinFull.Frozen.GaussianAverage
import EinsteinFull.Frozen.ModelClockEndpoint
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelTransposeEndpoint
import EinsteinFull.Frozen.JointCovariance
import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinFull.Frozen.VelocityGaussianProfile
import EinsteinFull.Frozen.ClockGaussianProfile
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:clock-average`, `paper/main.tex:1193–1204`.
The quotient is the literal centered clock semigroup, including force zero;
the weak flux is that of W, with full horizontal gradient. -/
def node_e_u3A_clock_u2D_averageStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε C t₀ : ℝ, 0 < ε ∧ 0 < C ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ (r : ℝ≥0), 0 < (r : ℝ) →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r)) ∧
      ∀ (r : ℝ≥0), t₀ ≤ (r : ℝ) → ∀ (s : ℝ) (hs : 0 < s),
        2 * (r : ℝ) ≤ s →
        let W := fun ζ => centeredComplexLp Q (P ζ r μ)
        (∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 1 →
          clockEndpoint Q ζ (P ζ) μ r = ζ • W ζ ∧
          ‖gaussianAverage hd Q s hs (W ζ)‖ ≤ C * s ^ (-(d : ℝ) / 4) ∧
          ‖gaussianAverage hd Q s hs (W ζ - W 0)‖ ≤
            C * ‖ζ‖ * Real.sqrt (r : ℝ) * s ^ (-(d : ℝ) / 4)) ∧
        DifferentiableAt ℂ W 0 ∧
        deriv (fun ζ => clockEndpoint Q ζ (P ζ) μ r) 0 = W 0 ∧
        Real.sqrt (∑ j : Fin d,
          ‖gaussianAverage hd Q s hs (centeredComplexLp Q (J 0 r j))‖ ^ 2) ≤
            C * (r : ℝ) ^ (-1 / 2 - ε) * s ^ (-(d : ℝ) / 4)

end EinsteinFull.Blueprint
