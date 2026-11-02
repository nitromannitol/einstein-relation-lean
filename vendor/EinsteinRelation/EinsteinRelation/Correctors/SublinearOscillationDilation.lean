import EinsteinRelation.Correctors.SpatialAverageDilation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sublinear oscillations under spatial dilation

Source: `paper/main.tex:693-702`. Normalized ball averages cancel the
Jacobian. The rescaled oscillation is `|c| * r` times the original
oscillation at radius `r * R`.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM

private theorem average_const_mul_real {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f : X → ℝ) (c : ℝ) :
    (⨍ x, c * f x ∂ν) = c * (⨍ x, f x ∂ν) := by
  simp only [average_eq, integral_const_mul, smul_eq_mul]
  ring

/-- Positive spatial dilation preserves sublinear normalized L² oscillations. -/
theorem sublinear_oscillation_dilation {d : ℕ} (u : Vec d → ℝ)
    (_hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume)) atTop (𝓝 0))
    (r c : ℝ) (hr : 0 < r) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (c * u (r • x) - ⨍ y in ball 0 R, c * u (r • y) ∂volume)^2 ∂volume))
      atTop (𝓝 0) := by
  have hlim := (hsub.comp ((tendsto_const_mul_atTop_of_pos hr).mpr tendsto_id)).const_mul
    (|c| * r)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hm : (⨍ y in ball (0 : Vec d) R, c * u (r • y) ∂volume) =
      c * (⨍ y in ball (0 : Vec d) (r * R), u y ∂volume) := by
    rw [average_const_mul_real, setAverage_euclideanBall_smul u r R hr hR]
  have hosc : (⨍ x in ball (0 : Vec d) R,
      (c * u (r • x) - ⨍ y in ball 0 R, c * u (r • y) ∂volume)^2 ∂volume) =
      c ^ 2 * (⨍ x in ball (0 : Vec d) (r * R),
        (u x - ⨍ y in ball 0 (r * R), u y ∂volume)^2 ∂volume) := by
    simp only [hm, ← mul_sub, mul_pow]
    rw [average_const_mul_real]
    congr 1
    exact setAverage_euclideanBall_smul
      (fun x => (u x - ⨍ y in ball 0 (r * R), u y ∂volume)^2) r R hr hR
  rw [hosc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  dsimp only [Function.comp_def, id_eq]
  rw [mul_inv]
  calc
    _ = |c| * (r * r⁻¹) * R⁻¹ * Real.sqrt (⨍ x in ball 0 (r * R),
      (u x - ⨍ y in ball 0 (r * R), u y ∂volume)^2 ∂volume) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hr.ne', mul_one]; ring

end EinsteinRelation.Correctors
