import EinsteinFull.Calculus.C34FluxBlockScaleNormalization
import EinsteinFull.Calculus.C10FluxBlockTerminalEnvelope

noncomputable section

namespace EinsteinFull.Calculus

/-- The physical and terminal scale envelopes combine into the parabolic bound. -/
theorem c34_flux_block_good_event_terminal_scale
    (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t s η : ℝ) (ζ : ℂ),
      8 ≤ t → 1 ≤ s → 0 ≤ η →
      ((t : ℝ)⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
        ((Real.sqrt t)⁻¹ + ‖ζ‖) * ((t ^ (1/2 + η))⁻¹ + (Real.sqrt s)⁻¹)) *
        ((t/8) ^ (-(1/2 + (d : ℝ)/4)) + ‖ζ‖ * (t/8) ^ (-(d : ℝ)/4)) ≤
      C * t ^ (-1 - (1/2 + (d : ℝ)/4)) *
        (1 + ‖ζ‖ * Real.sqrt t) ^ 2 * (1 + t/s) := by
  obtain ⟨K, hK, hterminal⟩ := c10_flux_block_terminal_eighth_envelope d
  refine ⟨max 1 (6 * K), le_max_left _ _, ?_⟩
  intro t s η ζ ht hs hη
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := by linarith
  have hphysical := c34_flux_block_good_event_scale_factor t s η ζ (by linarith) hs hη
  have hterm := hterminal t ζ ht
  have hleft : 0 ≤ (t / 8) ^ (-(1/2 + (d : ℝ)/4)) +
      ‖ζ‖ * (t / 8) ^ (-(d : ℝ)/4) := by positivity
  have hright : 0 ≤ 6 * t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) * (1 + t / s) := by positivity
  have hprod := mul_le_mul hphysical hterm hleft hright
  have hp : t⁻¹ * t ^ (-(1/2 + (d : ℝ)/4)) =
      t ^ (-1 - (1/2 + (d : ℝ)/4)) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add htpos]
    congr 1 <;> ring
  have hfac : 0 ≤ t ^ (-1 - (1/2 + (d : ℝ)/4)) *
      (1 + ‖ζ‖ * Real.sqrt t) ^ 2 * (1 + t / s) := by positivity
  calc
    _ ≤ (6 * t⁻¹ * (1 + ‖ζ‖ * Real.sqrt t) * (1 + t / s)) *
        (K * t ^ (-(1/2 + (d : ℝ)/4)) * (1 + ‖ζ‖ * Real.sqrt t)) := hprod
    _ = (6 * K) * (t ^ (-1 - (1/2 + (d : ℝ)/4)) *
        (1 + ‖ζ‖ * Real.sqrt t) ^ 2 * (1 + t / s)) := by rw [← hp]; ring
    _ ≤ max 1 (6 * K) * (t ^ (-1 - (1/2 + (d : ℝ)/4)) *
        (1 + ‖ζ‖ * Real.sqrt t) ^ 2 * (1 + t / s)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hfac
    _ = _ := by ring

end EinsteinFull.Calculus
