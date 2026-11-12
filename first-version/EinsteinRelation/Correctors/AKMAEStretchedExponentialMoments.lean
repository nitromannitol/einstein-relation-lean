import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Moments of almost-everywhere AKM stochastic bounds

Source: `paper/main.tex:724-731`; AKM Appendix A, (A.1)--(A.2), p. 455.
An almost-everywhere measurable random variable can be replaced by a
measurable version without changing either exponential or power moments.
-/

open MeasureTheory
namespace EinsteinRelation.External.AKM

/-- Finite moments are insensitive to changes on null sets. -/
theorem AEOsBound.moment_pos_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {θ p : ℝ}
    (h : AEOsBound P X 1 θ) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ p) ∂P) ≤
      ENNReal.ofReal (2 * θ ^ p * p ^ p) := by
  let Y := h.1.mk X
  have heq : X =ᵐ[P] Y := h.1.ae_eq_mk
  have hY : OsBound P Y 1 θ := by
    refine ⟨h.1.measurable_mk, h.2.1, h.2.2.1, ?_⟩
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ (1 : ℝ))) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [heq] with ω hω
        rw [hω]
      _ ≤ 2 := h.2.2.2
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ((max (Y ω) 0) ^ p) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ ≤ _ := hY.moment_pos_le hp

end EinsteinRelation.External.AKM
