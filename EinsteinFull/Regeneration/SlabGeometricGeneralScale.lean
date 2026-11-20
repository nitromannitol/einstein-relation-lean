import EinsteinFull.Regeneration.SlabGeometricScale

/-!
# Cutoff constants for a finite family of slab scales

The transverse cutoff constants have one common bound for any prescribed
finite number of successive geometric slabs.
-/

namespace EinsteinFull.Regeneration

/-- The cutoff gradient bound holds uniformly over any finite scale range. -/
theorem slabGeometricRadius_gradient_le_of_lt (n N : ℕ) (s L : ℝ) (j : ℕ)
    (hj : j < N) :
    (32 * (n + 1 : ℝ)) / (slabGeometricRadius n s L j / 2) ≤
      (32 * (n + 1 : ℝ) * (2 : ℝ) ^ N) * Real.exp (-(s * L / (n + 1))) := by
  have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ N :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hscale : 0 ≤ 32 * (n + 1 : ℝ) * Real.exp (-(s * L / (n + 1))) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hp hscale
  have heq : (32 * (n + 1 : ℝ)) / (slabGeometricRadius n s L j / 2) =
      (32 * (n + 1 : ℝ) * (2 : ℝ) ^ (j + 1)) * Real.exp (-(s * L / (n + 1))) := by
    rw [Real.exp_neg]
    dsimp only [slabGeometricRadius]
    rw [pow_succ]
    field_simp
  rw [heq]
  nlinarith

end EinsteinFull.Regeneration
