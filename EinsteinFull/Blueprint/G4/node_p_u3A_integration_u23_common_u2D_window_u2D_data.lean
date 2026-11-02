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

/-- Graph node `p:integration#common-window-data`, `paper/main.tex:1402–1402`.
All window families and tail constants precede the law and the finite list.
The reduced exponent, profile bounds and compact extension are conclusions. -/
def node_p_u3A_integration_u23_common_u2D_window_u2D_dataStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α C c C_T : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < C ∧ 0 < c ∧ 0 < C_T ∧
    ∃ Cw Tw : ℝ → ℝ,
      (∀ C₀ : ℝ, 0 < C₀ → 0 < Cw C₀) ∧
      (∀ C₀ : ℝ, 0 < C₀ → 1 ≤ Tw C₀) ∧
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
      c ≤ γ ∧ γ ≤ C ∧
      (∀ κ : Option (Fin d), |u₀ κ| + |u₂ κ| ≤ C) ∧
      (∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t → t ≤ 1 →
        ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K κ t z‖ ≤ C) ∧
      (∀ (κ : Option (Fin d)) (t : ℝ), 1 ≤ t →
        ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) ∧
      (∀ C₀ : ℝ, 0 < C₀ → ∀ (κ : Option (Fin d)) (t : ℝ), Tw C₀ ≤ t →
        ∀ lam : ℝ, |lam| * Real.sqrt t ≤
          C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
        ‖kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)‖ ≤
          Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2)) ∧
      (∀ (κ : Option (Fin d)) (lam : ℝ), 0 < |lam| → |lam| ≤ Real.exp (-1) →
        ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
        ‖K κ t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
          Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t))

end EinsteinFull.Blueprint
