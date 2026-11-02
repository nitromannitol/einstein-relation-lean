import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # A concrete nonnegative unit-mass kernel

Source: `paper/main.tex:753–756` and the sharpness construction1212–1216.
A normalized smooth bump on a small coordinate ball is proved to have support
strictly inside the Euclidean unit ball. The ambient coordinate norm is used
only in that construction, with an explicit Euclidean comparison proof.
-/

open MeasureTheory

namespace EinsteinRelation

private theorem euclideanNorm_le_dimension_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := by
  unfold euclideanNorm euclideanSq dot
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hi (i : Fin d) : x i * x i ≤ ‖x‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg (x i)) (norm_nonneg x)).mpr (norm_le_pi_norm x i)
    rw [Real.norm_eq_abs, sq_abs] at hs
    simpa only [pow_two] using hs
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) d]
  calc
    (∑ i, x i * x i) ≤ ∑ _ : Fin d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * ‖x‖ ^ 2 := by simp
    _ ≤ ((d : ℝ) + 1) ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
    _ = (((d : ℝ) + 1) * ‖x‖) ^ 2 := by ring

/-- A small coordinate bump used only to construct a source Euclidean mollifier. -/
private noncomputable def mollifierBump (d : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := ((d : ℝ) + 1)⁻¹ / 4
  rOut := ((d : ℝ) + 1)⁻¹ / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < ((d : ℝ) + 1)⁻¹ := by positivity
    linarith only [h]

/-- The nonnegative smooth unit-mass kernel fixed in `paper/main.tex:753`.
Its support lies inside the literal Euclidean unit ball. -/
noncomputable def mollifier (d : ℕ) : Vec d → ℝ :=
  (mollifierBump d).normed volume

theorem mollifier_nonneg (d : ℕ) (x : Vec d) : 0 ≤ mollifier d x :=
  (mollifierBump d).nonneg_normed x

theorem contDiff_mollifier (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollifier d) :=
  (mollifierBump d).contDiff_normed

theorem hasCompactSupport_mollifier (d : ℕ) : HasCompactSupport (mollifier d) :=
  (mollifierBump d).hasCompactSupport_normed

theorem integral_mollifier (d : ℕ) : (∫ x, mollifier d x) = 1 :=
  (mollifierBump d).integral_normed

theorem tsupport_mollifier_subset (d : ℕ) :
    tsupport (mollifier d) ⊆ {x : Vec d | euclideanNorm x < 1} := by
  intro x hx
  change x ∈ tsupport ((mollifierBump d).normed volume) at hx
  rw [(mollifierBump d).tsupport_normed_eq] at hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  change ‖x‖ ≤ ((d : ℝ) + 1)⁻¹ / 2 at hx
  have hd : 0 < (d : ℝ) + 1 := by positivity
  calc
    euclideanNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := euclideanNorm_le_dimension_mul_norm x
    _ ≤ ((d : ℝ) + 1) * (((d : ℝ) + 1)⁻¹ / 2) :=
      mul_le_mul_of_nonneg_left hx hd.le
    _ = 1 / 2 := by field_simp
    _ < 1 := by norm_num

end EinsteinRelation
