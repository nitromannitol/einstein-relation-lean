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

/-- Graph node `stationary-analytic-semigroup#clock`, `paper/main.tex:1193–1204`.
Finite-p holomorphy of actual W, its full gradient and weak flux; the literal
clock endpoint and its flux factor through force zero. Outer-disc averaged
bounds are in L2, as needed by the clock Cauchy application. -/
def node_stationary_u2D_analytic_u2D_semigroup_u23_clockStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p B : ℝ) (hp : 2 ≤ p), 2 ≤ B →
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩

    ∃ C t₀ : ℝ, ∃ N : ℕ, 0 < C ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ (r : ℝ≥0), 0 < (r : ℝ) →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r) ∧
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (clockEndpoint Q ζ (P ζ) μ r)
          (fun j => ζ • G ζ r j) (fun j => ζ • J ζ r j)) ∧
      ∀ (r : ℝ≥0), t₀ ≤ (r : ℝ) →
      ∃ Wp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      ∃ Gp Jp : ℂ → Fin d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ ζ, (Wp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (centeredComplexLp Q (P ζ r μ) : FieldPair d → ℂ)) ∧
        (∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] G ζ r j ∧
          (Jp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] J ζ r j) ∧
        DifferentiableOn ℂ Wp {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1} ∧
        (∀ j, DifferentiableOn ℂ (fun ζ => Gp ζ j)
          {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1} ∧
          DifferentiableOn ℂ (fun ζ => Jp ζ j)
          {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1}) ∧
        (∀ ζ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ B →
          ‖Wp ζ‖ + Real.sqrt (∑ j : Fin d, ‖Gp ζ j‖ ^ 2) +
            Real.sqrt (∑ j : Fin d, ‖Jp ζ j‖ ^ 2) ≤ C * (2 + (r : ℝ)) ^ N) ∧
        ∀ (s : ℝ) (hs : 0 < s), 2 * (r : ℝ) ≤ s →
          let W := fun ζ => centeredComplexLp Q (P ζ r μ)
          let U := fun ζ => gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r)
          let V := fun ζ j => gaussianAverage hd Q s hs
            (centeredComplexLp Q (ζ • J ζ r j))
          DifferentiableOn ℂ U {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1} ∧
          (∀ j, DifferentiableOn ℂ (fun ζ => V ζ j)
            {ζ | ‖ζ‖ * Real.sqrt (r : ℝ) < B + 1}) ∧
          U 0 = 0 ∧ (∀ j, V 0 j = 0) ∧
          (∀ ζ, U ζ = ζ • gaussianAverage hd Q s hs (W ζ)) ∧
          (∀ ζ j, V ζ j = ζ • gaussianAverage hd Q s hs
            (centeredComplexLp Q (J ζ r j))) ∧
          ∀ ζ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 2 →
            ‖U ζ‖ ≤ C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) ∧
            Real.sqrt (∑ j : Fin d, ‖V ζ j‖ ^ 2) ≤
              C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4)

end EinsteinFull.Blueprint
