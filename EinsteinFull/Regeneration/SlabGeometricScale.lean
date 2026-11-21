import EinsteinFull.Regeneration.CenteredSlabNormalizedStep
import PDEFoundation.Measure.ShrinkingAxisBoxCollar

/-!
# Geometric scales for the slab energy iteration

The transverse radii halve at each step and their cutoff gradients are
uniformly controlled over the finite source iteration.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The transverse radius at an index in the slab energy iteration. -/
noncomputable def slabGeometricRadius (n : ℕ) (s L : ℝ) (j : ℕ) : ℝ :=
  Real.exp (s * L / (n + 1)) / (2 : ℝ) ^ j

/-- Geometric slab radii are positive. -/
theorem slabGeometricRadius_pos (n : ℕ) (s L : ℝ) (j : ℕ) :
    0 < slabGeometricRadius n s L j := by
  dsimp [slabGeometricRadius]
  positivity

/-- Every geometric radius is at most the initial source radius. -/
theorem slabGeometricRadius_le_source (n : ℕ) (s L : ℝ) (j : ℕ) :
    slabGeometricRadius n s L j ≤ Real.exp (s * L / (n + 1)) := by
  dsimp [slabGeometricRadius]
  exact div_le_self (Real.exp_pos _).le (one_le_pow₀ (by norm_num))

/-- Successive geometric radii differ by a factor of two. -/
theorem slabGeometricRadius_succ (n : ℕ) (s L : ℝ) (j : ℕ) :
    slabGeometricRadius n s L (j + 1) = slabGeometricRadius n s L j / 2 := by
  simp only [slabGeometricRadius, pow_succ]
  ring

/-- Cutoff gradients across the finite iteration share one exponential bound. -/
theorem slabGeometricRadius_gradient_le (n : ℕ) (s L : ℝ) (j : ℕ)
    (hj : j < 2 * (n + 1)) :
    (32 * (n + 1 : ℝ)) / (slabGeometricRadius n s L j / 2) ≤
      (32 * (n + 1 : ℝ) * (2 : ℝ) ^ (2 * (n + 1))) *
        Real.exp (-(s * L / (n + 1))) := by
  have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (2 * (n + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hscale : 0 ≤ 32 * (n + 1 : ℝ) * Real.exp (-(s * L / (n + 1))) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hp hscale
  have heq : (32 * (n + 1 : ℝ)) / (slabGeometricRadius n s L j / 2) =
      (32 * (n + 1 : ℝ) * (2 : ℝ) ^ (j + 1)) *
        Real.exp (-(s * L / (n + 1))) := by
    rw [Real.exp_neg]
    dsimp only [slabGeometricRadius]
    rw [pow_succ]
    field_simp
  rw [heq]
  nlinarith

/-- The canonical force-face collar widths shrink and remain disjoint. -/
theorem slab_force_collar_widths (L : ℝ) (hL : 0 < L) :
    Tendsto (fun k : ℕ => L / ((k : ℝ) + 2)) atTop (𝓝 0) ∧
    (∀ k : ℕ, 0 < L / ((k : ℝ) + 2)) ∧
    ∀ k : ℕ, -L + L / ((k : ℝ) + 2) < L - L / ((k : ℝ) + 2) := by
  refine ⟨PDE.tendsto_canonicalAxisBoxCollarWidth L, fun k => div_pos hL (by positivity), ?_⟩
  intro k
  have hden : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hle : L / ((k : ℝ) + 2) ≤ L / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num)).2
    nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  linarith


/-- The terminal transverse radius eventually exceeds one. -/
theorem exists_large_terminal_slab_radius (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      1 < slabGeometricRadius n s L (2 * (n + 1)) := by
  let d : ℝ := n + 1
  let M : ℝ := (2 : ℝ) ^ (2 * (n + 1))
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
