import EinsteinFull.Proofs.KernelIntegration
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.CriticalKernelTerm
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull.Frozen

/-- Proposition 6.7. The bounded-time holomorphy and structural compact bounds
are the standing finite-time facts immediately preceding the proposition.
Window controls are supplied before the common output constants, never law by law. -/
theorem kernel_integration (d : ℕ) (hd : 2 ≤ d)
    (α C c C_T : ℝ) (hα : 0 < α) (hα' : α ≤ 1 / 4)
    (hC : 0 < C) (hc : 0 < c) (hCT : 0 < C_T)
    (Cw Tw : ℝ → ℝ) (hCw : ∀ C₀, 0 < C₀ → 0 < Cw C₀)
    (hTw : ∀ C₀, 0 < C₀ → 1 ≤ Tw C₀) :
    ∃ C_out lam_star : ℝ, 0 < C_out ∧ 0 < lam_star ∧ lam_star ≤ Real.exp (-1) ∧
    ∀ (u₀ u₂ γ : ℝ) (hγ : 0 < γ) (K : ℝ → ℂ → ℂ),
      |u₀| + |u₂| ≤ C → c ≤ γ → γ ≤ C →
      ∀ hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t),
      (∀ z : ℂ, Measurable (fun t : ℝ => K t z)) →
      ∀ hR : ∀ (t : ℝ), 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0,
      (∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ (t : ℝ), 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      (∀ C₀ : ℝ, 0 < C₀ → ∀ (t : ℝ), Tw C₀ ≤ t →
        ∀ lam : ℝ, |lam| * Real.sqrt t ≤
            C₀ * Real.log (Real.sqrt t) ^ (1 / 4 : ℝ) →
        ‖kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)‖ ≤
          Cw C₀ * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (Cw C₀ * (1 + |lam| * Real.sqrt t) ^ 2)) →
      (∀ lam : ℝ, 0 < |lam| → |lam| ≤ Real.exp (-1) →
        ∀ t : ℝ, C_T / |lam| ^ 2 ≤ t →
        ‖K t (lam : ℂ)‖ ≤ C * |lam| ^ (d + 2) *
          Real.exp (C * Real.sqrt (Real.log (1 / |lam|)) - c * lam ^ 2 * t)) →
      ∃ hI : ∀ j : Fin (d + 1),
        IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) (Set.Ici 0),
      (∀ j : Fin (d + 1),
        |integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j| ≤ C_out) ∧
      |integratedKernelCriticalCoefficient d u₀ u₂ γ hγ| ≤ C_out ∧
      ∀ lam : ℝ, ∀ h₀ : 0 < |lam|, ∀ h₁ : |lam| ≤ lam_star, ∀ hsmall : |lam| ≤ Real.exp (-1),
        IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Set.Ici 0) ∧
        |(∫ t in Set.Ici (0 : ℝ), (K t (lam : ℂ)).re) -
          (∑ j : Fin (d + 1), integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j * lam ^ j.val) -
          integratedKernelCriticalCoefficient d u₀ u₂ γ hγ *
            criticalKernelTerm d lam (by intro h; simp [h] at h₀)| ≤
          C_out * |lam| ^ d * expansionModulus |lam| h₀ hsmall := by
  exact EinsteinFull.Proofs.kernel_integration d hd α C c C_T hα hα' hC hc hCT Cw Tw hCw hTw

end EinsteinFull.Frozen
