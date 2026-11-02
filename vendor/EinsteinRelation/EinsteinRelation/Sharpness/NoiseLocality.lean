import EinsteinRelation.Sharpness.NoiseKernel
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Actual reflected-kernel support geometry for main.tex1212–1216.
This proves disjoint test evaluations at Euclidean separation, not full sigma-algebra
independence or existence of the manuscript's h. -/
namespace EinsteinRelation.Sharpness
open EinsteinRelation.TimeChange

private theorem kernel_euclideanNorm_neg {d : ℕ} (v : Vec d) :
    euclideanNorm (-v) = euclideanNorm v := by
  rw [← neg_one_smul ℝ v, euclideanNorm_smul]
  norm_num

/-- Compact kernels supported within Euclidean radius R produce disjoint reflected
translated tests at separation greater than 2R. -/
theorem kernelTest_mul_eq_zero_of_separated {d : ℕ} (K : NoiseTest d) (R : ℝ)
    (hK : ∀ u : Vec d, K u ≠ 0 → euclideanNorm u ≤ R) (x z : Vec d)
    (hsep : 2*R < euclideanNorm (x-z)) (y : Vec d) :
    kernelTest K x y * kernelTest K z y = 0 := by
  change K (x-y) * K (z-y) = 0
  by_cases hx : K (x-y) = 0
  · rw [hx, zero_mul]
  by_cases hz : K (z-y) = 0
  · rw [hz, mul_zero]
  have hxR := hK (x-y) hx
  have hzR := hK (z-y) hz
  have hid : x-z = (x-y) + -(z-y) := by abel
  have hb : euclideanNorm (x-z) ≤ euclideanNorm (x-y) + euclideanNorm (z-y) := by
    rw [hid]
    simpa only [kernel_euclideanNorm_neg] using
      euclideanNorm_add_le (x-y) (-(z-y))
  exfalso
  linarith
end EinsteinRelation.Sharpness