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

/-- Graph node `p:endpoint-comparison#force-replacement`, `paper/main.tex:1172–1185`.
Early velocity/transpose flux force replacement after signed homogeneous
propagation, with delta=1/4 and both comparison windows. -/
def node_p_u3A_endpoint_u2D_comparison_u23_force_u2D_replacementStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ M : ℕ, ∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ R : ℝ, ∀ _hR : 0 < R, R₀ ≤ R → ∀ z : ℂ,
      (‖z‖ ≤ 2 ∨ ∃ x : ℝ, z = (x : ℂ) ∧
        |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
      let T := R ^ 2 / 2
      let τ := T ^ (1 - (1 / 4 : ℝ))
      let ζ := z / (R : ℂ)
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ (hP : ∀ w, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ w (P w))
      (_hPdag : ∀ w, IsComplexTransposeSemigroup Q (P w) (Pdag w)),
    ∃ G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ w, IsFiniteTimeFlux hd Q w (P w) (Pdag w) β a μ (G w) (F w)) ∧
    ∃ ht : 0 < T - τ,
      let E := fun (t : ℝ) (ht : 0 < t) (ν : FluxIndex d)
        (F : Fin d → Lp ℂ 2 (reducedLaw Q)) =>
        let signζ := ν.elim (fun _ => ζ) (fun _ => -ζ)
        (1 / 2 : ℂ) • (∑ j : Fin d,
          homogeneousDerivativeAverage Q ⟨0, by omega⟩ t ht signζ 1 (fun _ => j) (F j)) +
        ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ t ht ζ (F ⟨0, by omega⟩))
          (fun _ => 0)
      ‖ζ‖ * Real.sqrt τ ≤ 1 ∧
      ∀ ν : FluxIndex d,
        let diff := fun j => centeredComplexLp Q (F ζ τ.toNNReal ν j - F 0 τ.toNNReal ν j)
        ‖E (T - τ) ht ν diff‖ ≤
          C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
            (‖ζ‖ * Real.sqrt τ) * Real.log (2 + τ) ^ M ∧
        ‖E (T - τ) ht ν diff‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1 / 16)

end EinsteinFull.Blueprint
