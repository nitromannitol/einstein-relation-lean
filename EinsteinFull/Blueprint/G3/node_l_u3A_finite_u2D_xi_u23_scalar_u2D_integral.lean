import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.ReducedCoefficientObservation
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.FiniteTimeCommutator
import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.GaussianDerivativeAverage
import EinsteinFull.Frozen.FiniteTimeFlux
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import EinsteinFull.Frozen.EndpointDriftSign
import EinsteinFull.Frozen.HomogeneousDerivativeAverage
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelTransposeEndpoint

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `l:finite-xi#scalar-integral`, `paper/main.tex:1126`.
Positive-order kernel derivatives of the literal finite-time scalar corrector;
the initial unit interval is included. No infinite-time scalar limit. -/
def node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integralStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ t₀ : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 2 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
    ∀ (i : Fin d) (k : ℕ), 1 ≤ k → ∀ dirs : Fin k → Fin d,
      ‖gaussianDerivativeAverage hd Q s hs k dirs
        (finiteTimeCorrector Q P hP.2.2.1 β τ i)‖ ≤
        Cder k * (τ : ℝ) * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)

end EinsteinFull.Blueprint
