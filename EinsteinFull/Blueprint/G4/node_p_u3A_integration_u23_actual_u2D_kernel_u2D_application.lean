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

/-- Graph node `p:integration#actual-kernel-application`, `paper/main.tex:1402–1402`.
Actual derivative integrability, coefficients and parity-dependent finite
parts are constructed together. There is no conditional kernel-bound premise. -/
def node_p_u3A_integration_u23_actual_u2D_kernel_u2D_applicationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C lamStar : ℝ, 0 < C ∧ 0 < lamStar ∧ lamStar ≤ Real.exp (-1) ∧
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
      ∃ (hγ : 0 < γ)
        (hK : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t → Differentiable ℂ (K κ t))
        (hR : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t →
          ∀ lam : ℝ, (K κ t (lam : ℂ)).im = 0)
        (hI : ∀ (κ : Option (Fin d)) (j : Fin (d + 1)),
          IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
            (kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)).re) 0 /
              (j.val.factorial : ℝ)) (Set.Ici 0)),
      let k : Option (Fin d) → Fin (d + 1) → ℝ := fun κ =>
        integratedKernelCoefficient d (u₀ κ) (u₂ κ) γ hγ (K κ) (hK κ) (hR κ) (hI κ)
      let χ : Option (Fin d) → ℝ := fun κ =>
        integratedKernelCriticalCoefficient d (u₀ κ) (u₂ κ) γ hγ
      (∀ (κ : Option (Fin d)) (j : Fin (d + 1)), |k κ j| ≤ C) ∧
      (∀ κ : Option (Fin d), |χ κ| ≤ C) ∧
      ∀ (κ : Option (Fin d)) (lam : ℝ) (h₀ : 0 < |lam|)
        (h₁ : |lam| ≤ lamStar) (hsmall : |lam| ≤ Real.exp (-1)),
        IntegrableOn (fun t : ℝ => (K κ t (lam : ℂ)).re) (Set.Ici 0) ∧
        |(∫ t in Set.Ici (0 : ℝ), (K κ t (lam : ℂ)).re) -
          (∑ j : Fin (d + 1), k κ j * lam ^ j.val) -
          χ κ * criticalKernelTerm d lam (abs_pos.mp h₀)| ≤
            C * |lam| ^ d * expansionModulus |lam| h₀ hsmall

end EinsteinFull.Blueprint
