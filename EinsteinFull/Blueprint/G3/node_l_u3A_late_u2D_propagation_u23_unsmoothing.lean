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

/-- Graph node `l:late-propagation#unsmoothing`, `paper/main.tex:1148–1158`.
Unsmoothing for both actual and homogeneous endpoints, homogeneous second kernel
derivatives, and the combined late estimate for every smaller positive gain. -/
def node_l_u3A_late_u2D_propagation_u23_unsmoothingStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε α : ℝ, 0 < ε ∧ 0 < α ∧
    ∀ (δ : ℝ) (hδ : 0 < δ) (_hδ : δ < 1 / 2),
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < ε * (1 - δ) / 2 → ρ < b * α / 2 → ρ < b →
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ T : ℝ, ∀ hT : 1 < T, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ θ : EndpointIndex d,
      let τ := T ^ (1 - δ)
      let s := T ^ (1 - b)
      let hs : 0 < s := Real.rpow_pos_of_pos (by linarith) _
      let ht : 0 < T - τ := by
        have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith)
        linarith
      let U := indexedEndpoint hd Q θ ζ P Pdag β a μ T.toNNReal
      let V := homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht
        ((endpointDriftSign θ : ℂ) * ζ)
        (indexedEndpoint hd Q θ ζ P Pdag β a μ τ.toNNReal)
      ‖U - gaussianAverage hd Q s hs U‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b * α / 2) ∧
      (∀ dirs : Fin 2 → Fin d,
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) ht
          ((endpointDriftSign θ : ℂ) * ζ) 2 dirs
          (indexedEndpoint hd Q θ ζ P Pdag β a μ τ.toNNReal)‖ ≤
            C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1)) ∧
      ‖V - gaussianAverage hd Q s hs V‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b) ∧
      ‖U - V‖ ≤ C * Real.exp (C * ‖ζ‖ ^ 2 * T) *
        T ^ (-(1 / 2 + (d : ℝ) / 4) - ρ)

end EinsteinFull.Blueprint
