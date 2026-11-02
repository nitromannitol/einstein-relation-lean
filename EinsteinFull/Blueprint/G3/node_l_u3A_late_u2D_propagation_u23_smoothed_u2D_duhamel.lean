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

/-- Graph node `l:late-propagation#smoothed-duhamel`, `paper/main.tex:1140–1148`.
Smoothed difference of actual endpoints and their signed homogeneous propagation.
The small smoothing exponent can be chosen after epsilon and L, before the law. -/
def node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamelStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε η L : ℝ, 0 < ε ∧ 0 < η ∧ 0 ≤ L ∧
    ∀ (δ : ℝ) (hδ : 0 < δ) (_hδ : δ < 1 / 2),
    ∀ b : ℝ, 0 < b → b < 1 →
      b < ε * (1 - δ) / (2 * (1 / 2 + (d : ℝ) / 4 + L)) →
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
      τ ≤ T / 2 ∧
      (∀ r : ℝ, τ ≤ r → r ≤ T → ‖ζ‖ * Real.sqrt r ≤ r ^ η) ∧
      ‖gaussianAverage hd Q s hs (U - V)‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) *
          T ^ (b * (1 / 2 + (d : ℝ) / 4 + L)) * τ ^ (-ε)

end EinsteinFull.Blueprint
