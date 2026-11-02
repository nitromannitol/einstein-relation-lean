import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:integration#compact-extension`, `paper/main.tex:1402–1402`.
The same fixed force disc is controlled down to time one. The exponent may be reduced
within the original positive range before common windows are assembled. -/
def node_p_u3A_integration_u23_compact_u2D_extensionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ z : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) z (P z)) →
      let first : Fin d := ⟨0, by omega⟩
      let A := homogenizedCoefficient Q
      let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
      let γ : ℝ := A first first / 2
      let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => 0
        | some i => p₀ / 4 * ∑ j, ∑ k,
            (A⁻¹) j k * covariance (.inl (j, first)) (.inl (k, i))
      let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
        | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
      let K : Option (Fin d) → ℝ → ℂ → ℂ := fun κ t z => match κ with
        | none => clockCorrelation Q first z (P z) β μ t.toNNReal
        | some i => velocityCorrelation Q first i z (P z) β a t.toNNReal
      ∀ (κ : Option (Fin d)) (t : ℝ), 1 ≤ t →
        ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)

end EinsteinFull.Blueprint
