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

/-- Graph node `p:endpoint-comparison#unforced-identification`, `paper/main.tex:1187–1191`.
Literal zero-force flux decomposition, finite commutator replacement, corrector
correction and homogeneous time replacement; velocity and transpose only. -/
def node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε₁ gain : ℝ, 0 < ε₁ ∧ 0 < gain ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
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
      ∃ hT : 0 < T,
      ∃ H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t i, IsFiniteTimeCommutator Q (P 0) (hP 0).2.2.1
        β t i (H t i) (X t i)) ∧
      (∀ i j, centeredComplexLp Q (F 0 τ.toNNReal (.inl i) j) =
        centeredComplexLp Q (X τ.toNNReal i j) +
          ∑ k : Fin d, (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k) ∧
      (∀ j, F 0 τ.toNNReal (.inr ()) j = F 0 τ.toNNReal (.inl ⟨0, by omega⟩) j) ∧
      ∀ ν : FluxIndex d,
        let i := ν.elim id (fun _ => ⟨0, by omega⟩)
        let Xi := fun j => Z (.inl (j,i))
        let model := ν.elim (fun k => modelVelocityEndpoint hd Q Z k T hT ζ)
          (fun _ => modelTransposeEndpoint hd Q Z T hT ζ)
        ‖E (T - τ) ht ν (fun j => centeredComplexLp Q (X τ.toNNReal i j) - Xi j)‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * τ ^ (-ε₁) ∧
        ‖E (T - τ) ht ν (fun j => ∑ k : Fin d,
          (homogenizedCoefficient Q j k : ℂ) • H τ.toNNReal i k)‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) ∧
        ‖E (T - τ) ht ν Xi - model‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) ∧
        ‖indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) ζ
            (P ζ) (Pdag ζ) β a μ T.toNNReal - model‖ ≤
          C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)

end EinsteinFull.Blueprint
