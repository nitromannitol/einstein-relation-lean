import EinsteinFull.Work.W4.KernelIntegrationCoefficientSupport
import EinsteinFull.Work.W4.KernelIntegrationIntegrabilitySupport
import EinsteinFull.Work.W4.KernelIntegrationModulusSupport
import EinsteinFull.Work.W4.KernelIntegrationTaylorSupport

/-! The constructed coefficient and absolute-integrability conclusions of
Proposition 6.7, with structural witnesses before the actual profile and kernel.
The integrated Taylor error is a separate remaining proof obligation. -/

open MeasureTheory

namespace EinsteinFull

/-- The coefficient and integrability part of the frozen kernel integration
contract, using only its standing hypotheses. This intermediate result does
not assert the integrated expansion error. -/
theorem exists_uniform_kernel_coefficients_and_integrability (d : ℕ) (hd : 2 ≤ d)
    (α C c C_T : ℝ) (hα : 0 < α)
    (hC : 0 < C) (hc : 0 < c)
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
      ∀ lam : ℝ, 0 < |lam| → |lam| ≤ lam_star →
        IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Set.Ici 0) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_uniform_integratedKernelCoefficient_bound d hd α C c hα hC hc
  obtain ⟨s, hs, hs₁, hi⟩ :=
    exists_uniform_kernel_integrability_threshold d α C c C_T hα hC hc Cw Tw hCw hTw
  refine ⟨B, s, hB, hs, hs₁, ?_⟩
  intro u₀ u₂ γ hγ K ha hγc hγC hK hm hR hinit hfixed hwindow htail
  obtain ⟨hI, hb, hcrit⟩ := hb u₀ u₂ γ hγ K ha hγc hγC hK hm hR hinit hfixed
  exact ⟨hI, hb, hcrit, fun lam hl hls =>
    (hi u₀ u₂ γ hγ K hm hinit hfixed hwindow htail lam hl hls).2⟩

end EinsteinFull
