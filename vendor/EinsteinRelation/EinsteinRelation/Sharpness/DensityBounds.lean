import EinsteinRelation.Sharpness.Fields
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Uniform bounds for the clock density

Source: `paper/main.tex`, `eq.sharp-coefficients` and the sentence after it (line 1231).
Since `∇·(a e₁)` is bounded, a constant `δ > 0` can be fixed so that
`3/4 ≤ μ ≤ 5/4`, where `μ = 1 + (δ/2)∇·(a e₁)` is `densityField` by definition.

The divergence bound is an explicit hypothesis `hdiv` on the given `ψ`. This file
proves only deterministic algebra: it does not construct the random corrector,
bound its derivatives, or verify `hdiv`.
-/

namespace EinsteinRelation.Sharpness

/-- The clock density is `1 + (δ/2)` times the divergence of the first coefficient column. -/
private lemma densityField_eq_one_add_divergence {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (x : Vec d) :
    densityField i δ ψ x =
      1 + δ / 2 * divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x :=
  rfl

/-- Under the divergence bound, the clock density deviates from one by at most `δM/2`. -/
private lemma abs_densityField_sub_one_le {d : ℕ} (i : Fin d) (δ M : ℝ)
    (ψ : Vec d → ℝ) (hδ : 0 ≤ δ) (hsmall : δ * M ≤ (1 / 2 : ℝ))
    (hdiv : ∀ x, |divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x| ≤ M)
    (x : Vec d) :
    |densityField i δ ψ x - 1| ≤ (1 / 4 : ℝ) := by
  have hhalf : 0 ≤ δ / 2 := div_nonneg hδ (by norm_num)
  have hdev : densityField i δ ψ x - 1 =
      δ / 2 * divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x := by
    rw [densityField_eq_one_add_divergence]
    ring
  rw [hdev, abs_mul, abs_of_nonneg hhalf]
  calc δ / 2 * |divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x|
      ≤ δ / 2 * M := mul_le_mul_of_nonneg_left (hdiv x) hhalf
    _ = δ * M / 2 := by ring
    _ ≤ (1 / 4 : ℝ) := by linarith

/-- A divergence bound `|∇·(a e₁)| ≤ M` and `δM ≤ 1/2` give `3/4 ≤ μ ≤ 5/4`. The bound
`_hM` is not used by this argument; it is kept in the frozen signature. -/
theorem densityField_bounds_of_divergence_bound {d : ℕ} (i : Fin d) (δ M : ℝ)
    (ψ : Vec d → ℝ) (hδ : 0 ≤ δ) (_hM : 0 ≤ M) (hsmall : δ * M ≤ (1 / 2 : ℝ))
    (hdiv : ∀ x, |divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x| ≤ M) :
    ∀ x, (3 / 4 : ℝ) ≤ densityField i δ ψ x ∧ densityField i δ ψ x ≤ (5 / 4 : ℝ) := by
  intro x
  obtain ⟨h₁, h₂⟩ := abs_le.mp (abs_densityField_sub_one_le i δ M ψ hδ hsmall hdiv x)
  exact ⟨by linarith, by linarith⟩

/-- Choice of `δ` depending only on the divergence bound `M`, uniformly over `ψ`.
The witness `δ = 1/(2(M+1))` satisfies `δM ≤ 1/2`. -/
theorem exists_uniform_densityField_parameter {d : ℕ} (i : Fin d) (M : ℝ)
    (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : Vec d → ℝ,
      (∀ x, |divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x| ≤ M) →
      ∀ x, (3 / 4 : ℝ) ≤ densityField i δ ψ x ∧ densityField i δ ψ x ≤ (5 / 4 : ℝ) := by
  have hpos : 0 < 2 * (M + 1) := by linarith
  have hδ : 0 < 1 / (2 * (M + 1)) := one_div_pos.mpr hpos
  refine ⟨1 / (2 * (M + 1)), hδ, fun ψ hdiv => ?_⟩
  have hsmall : 1 / (2 * (M + 1)) * M ≤ (1 / 2 : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    linarith
  exact densityField_bounds_of_divergence_bound i (1 / (2 * (M + 1))) M ψ hδ.le hM hsmall hdiv

end EinsteinRelation.Sharpness
