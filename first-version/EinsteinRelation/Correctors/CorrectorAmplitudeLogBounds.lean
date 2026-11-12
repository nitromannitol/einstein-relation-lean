import EinsteinRelation.Correctors.ScalarDecompositionSums
import EinsteinRelation.Mobility.VelocityResolventRate

noncomputable section
namespace EinsteinRelation.Correctors

/-- The corrector amplitude is bounded by the common logarithmic band
weight, which grows slower than the scale (`paper/main.tex:1070–1082`). -/
theorem correctorAmplitude_log_bounds (d : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    1 ≤ Real.sqrt (Real.log (2 + r)) ∧
    Real.sqrt (Real.log (2 + r)) ≤ 3 * r ∧
    correctorAmplitude d r ≤ Real.sqrt (Real.log (2 + r)) := by
  have hlog : 1 ≤ Real.log (2 + r) := by
    have he : Real.exp 1 ≤ 2 + r := by linarith [Real.exp_one_lt_d9]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hs : 1 ≤ Real.sqrt (Real.log (2 + r)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlog
  have hu : Real.log (2 + r) ≤ (3 * r) ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
    nlinarith [sq_nonneg (r - 1)]
  refine ⟨hs, ?_, ?_⟩
  · calc
      _ ≤ Real.sqrt ((3 * r) ^ 2) := Real.sqrt_le_sqrt hu
      _ = _ := Real.sqrt_sq (by linarith)
  · unfold correctorAmplitude
    split
    · exact hs
    · exact le_rfl

theorem correctorAmplitude_log_weight {d : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    1 ≤ Real.sqrt (Real.log (2 + r)) ∧
      Real.sqrt (Real.log (2 + r)) ≤ 3 * r ∧
      correctorAmplitude d r ≤ Real.sqrt (Real.log (2 + r)) := by
  exact correctorAmplitude_log_bounds d hr

end EinsteinRelation.Correctors
