import EinsteinRelation.Sharpness.Fields
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bounds for the physical potential

Source: `paper/main.tex`, `eq.sharp-coefficients`, the sentence after it (line 1231).
For the clock density `μ = densityField` with `3/4 ≤ μ ≤ 5/4`, the physical potential
`V = -(1/2) log μ` (`potentialField`) satisfies `|V| ≤ 1/6`. If `μ` is `L`-Lipschitz and
bounded below by `3/4`, then `V` is Lipschitz with constant `(2/3) L`.

These are deterministic real-analysis consequences. The density Lipschitz bound is an
explicit hypothesis `hL` of `potentialField_lipschitz_of_density`; this file does not
derive it from the derivative bounds of the corrector.
-/

namespace EinsteinRelation.Sharpness

/-- For `a ≥ 3/4`, the reciprocal satisfies `a⁻¹ ≤ 4/3`. -/
private lemma potential_inv_le_four_thirds {a : ℝ} (ha : (3 / 4 : ℝ) ≤ a) :
    a⁻¹ ≤ 4 / 3 := by
  have hpos : 0 < a := by linarith
  have hnn : 0 ≤ a⁻¹ := inv_nonneg.mpr hpos.le
  have hmul : a * a⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hnn]

/-- For `3/4 ≤ a ≤ 5/4`, `|log a| ≤ 1/3`, from `1 - a⁻¹ ≤ log a ≤ a - 1`. -/
private lemma potential_abs_log_le_third {a : ℝ} (ha : (3 / 4 : ℝ) ≤ a)
    (ha' : a ≤ (5 / 4 : ℝ)) : |Real.log a| ≤ (1 / 3 : ℝ) := by
  have hpos : 0 < a := by linarith
  have hlow : 1 - a⁻¹ ≤ Real.log a := Real.one_sub_inv_le_log_of_pos hpos
  have hup : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos hpos
  have hinv : a⁻¹ ≤ 4 / 3 := potential_inv_le_four_thirds ha
  rw [abs_le]
  constructor <;> linarith

/-- For `a, b ≥ 3/4`, `log a - log b ≤ (4/3) |a - b|`, from `log (a/b) ≤ a/b - 1`. -/
private lemma potential_log_sub_log_le {a b : ℝ} (ha : (3 / 4 : ℝ) ≤ a)
    (hb : (3 / 4 : ℝ) ≤ b) : Real.log a - Real.log b ≤ (4 / 3 : ℝ) * |a - b| := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hbinv : b⁻¹ ≤ 4 / 3 := potential_inv_le_four_thirds hb
  have hbinv_nn : 0 ≤ b⁻¹ := inv_nonneg.mpr hbpos.le
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hbpos.ne'
  have hlog : Real.log (a / b) = Real.log a - Real.log b :=
    Real.log_div hapos.ne' hbpos.ne'
  have hup : Real.log (a / b) ≤ a / b - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
  have hdiv : a / b - 1 = (a - b) * b⁻¹ := by
    rw [div_eq_mul_inv, sub_mul, hbb]
  have h₁ : (a - b) * b⁻¹ ≤ |a - b| * b⁻¹ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hbinv_nn
  have h₂ : |a - b| * b⁻¹ ≤ |a - b| * (4 / 3) :=
    mul_le_mul_of_nonneg_left hbinv (abs_nonneg _)
  linarith

/-- Symmetric form of `potential_log_sub_log_le`: `|log a - log b| ≤ (4/3) |a - b|`. -/
private lemma potential_abs_log_sub_log_le {a b : ℝ} (ha : (3 / 4 : ℝ) ≤ a)
    (hb : (3 / 4 : ℝ) ≤ b) : |Real.log a - Real.log b| ≤ (4 / 3 : ℝ) * |a - b| := by
  have h₁ := potential_log_sub_log_le ha hb
  have h₂ := potential_log_sub_log_le hb ha
  rw [abs_sub_comm b a] at h₂
  rw [abs_le]
  constructor <;> linarith

/-- Where the clock density lies in `[3/4, 5/4]`, the physical potential satisfies `|V| ≤ 1/6`.
Source: `paper/main.tex`, `eq.sharp-coefficients`, line 1231. -/
theorem potentialField_abs_le {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hμ : ∀ x, (3/4 : ℝ) ≤ densityField i δ ψ x ∧ densityField i δ ψ x ≤ (5/4 : ℝ))
    (x : Vec d) : |potentialField i δ ψ x| ≤ (1/6 : ℝ) := by
  obtain ⟨h₁, h₂⟩ := hμ x
  obtain ⟨hlo, hhi⟩ := abs_le.mp (potential_abs_log_le_third h₁ h₂)
  have hP : potentialField i δ ψ x = -(1 / 2 : ℝ) * Real.log (densityField i δ ψ x) := rfl
  rw [abs_le]
  constructor <;> linarith

/-- If the clock density is bounded below by `3/4` and is `L`-Lipschitz in the Euclidean
norm, then the physical potential is `(2/3) L`-Lipschitz in the Euclidean norm.
Source: `paper/main.tex`, `eq.sharp-coefficients`, line 1231. -/
theorem potentialField_lipschitz_of_density {d : ℕ} (i : Fin d) (δ L : ℝ)
    (ψ : Vec d → ℝ) (hμ : ∀ x, (3/4 : ℝ) ≤ densityField i δ ψ x)
    (hL : ∀ x y, |densityField i δ ψ x - densityField i δ ψ y| ≤
      L * euclideanNorm (x-y)) :
    ∀ x y, |potentialField i δ ψ x - potentialField i δ ψ y| ≤
      ((2/3 : ℝ)*L) * euclideanNorm (x-y) := by
  intro x y
  obtain ⟨hlo, hhi⟩ := abs_le.mp (potential_abs_log_sub_log_le (hμ x) (hμ y))
  have hd := hL x y
  have hP : potentialField i δ ψ x - potentialField i δ ψ y =
      -(1 / 2 : ℝ) * (Real.log (densityField i δ ψ x) - Real.log (densityField i δ ψ y)) := by
    unfold potentialField
    ring
  rw [abs_le]
  constructor <;> linarith

end EinsteinRelation.Sharpness
