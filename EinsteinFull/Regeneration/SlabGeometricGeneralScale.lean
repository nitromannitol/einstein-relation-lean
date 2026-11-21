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

/-- Every fixed geometric radius eventually exceeds one. -/
theorem exists_large_slabGeometricRadius (n N : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → 1 < slabGeometricRadius n s L N := by
  let d : ℝ := n + 1
  let M : ℝ := (2 : ℝ) ^ N
  have hd : 0 < d := by dsimp [d]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨max 1 (M * d / s), by positivity, ?_⟩
  intro L hL
  have hLbound : M * d / s ≤ L := (le_max_right _ _).trans hL
  have hscale : M ≤ s * L / d := by
    apply (le_div_iff₀ hd).2
    have h := (div_le_iff₀ hs).1 hLbound
    nlinarith
  have hexp := Real.add_one_le_exp (s * L / d)
  change 1 < Real.exp (s * L / d) / M
  apply (lt_div_iff₀ hM).2
  nlinarith

end EinsteinFull.Regeneration
