import EinsteinRelation.Regeneration.ForcedBitSlice
import EinsteinRelation.Regeneration.TrialGeometry

/-! # Geometry on the actual forced-last-bit event

Source `paper/main.tex:365–374`. The prestart event retains the running-maximum
slack and displacement lower bound of the literal trial construction. The bit
update leaves the path untouched; no geometry assertion is assumed as a premise.
-/

open scoped NNReal ENNReal
namespace EinsteinRelation.Regeneration

/-- The explicit Γ event has the source prestart maximum and height bounds. -/
theorem forcedBitTrialEvent_geometry {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (z : CoupledSample d) (hz : z ∈ forcedBitTrialEvent Δ lam R i m) :
    coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
        z.1 ((m : ℝ≥0) * Δ) i - z.1 0 i + R ∧
      2 * R ≤ z.1 ((m : ℝ≥0) * Δ) i - z.1 0 i := by
  obtain ⟨n, hn⟩ := hz
  have hf : trialStartSequence Δ lam R (forceSampleBit m z) i n ≠ ⊤ :=
    hn ▸ ENNReal.coe_ne_top
  have hs := trial_prestart_maximum_slack Δ hΔ lam R hlam hR (forceSampleBit m z) i n hf
  have hh := trial_prestart_height_lower_bound Δ hΔ lam R hlam hR (forceSampleBit m z) i n hf
  have ht : (((m + 1 : ℕ) : ℝ≥0) * Δ) - Δ = (m : ℝ≥0) * Δ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_right]
  rw [hn, ENNReal.toNNReal_coe, ht] at hs hh
  exact ⟨hs, hh⟩

end EinsteinRelation.Regeneration
