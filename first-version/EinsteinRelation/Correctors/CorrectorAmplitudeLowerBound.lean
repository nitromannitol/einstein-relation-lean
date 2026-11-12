import EinsteinRelation.Correctors.CorrectorAmplitude
import Mathlib.Analysis.Complex.ExponentialBounds
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:680-683,718-723`. The amplitude on every
allowed radius absorbs a deterministic constant. -/
theorem one_le_correctorAmplitude (d : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ correctorAmplitude d R := by
  unfold correctorAmplitude
  split
  · exact le_rfl
  · have he : Real.exp 1 ≤ 2 + R := by linarith [Real.exp_one_lt_d9]
    have hl : 1 ≤ Real.log (2 + R) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hl
end EinsteinRelation.Correctors
