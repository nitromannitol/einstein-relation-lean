import EinsteinRelation.Correctors.SpatialBallVolume
import Mathlib.MeasureTheory.Integral.Average

/-!
# Squared and normalized ball Poincaré inequality

Source: `paper/main.tex:693-698,722-729`. Both spatial norms in the GT
input use the same Euclidean ball, so normalizing by its volume preserves
the dimension-only constant.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

private theorem normalize_sqrt_bound (C R V U G : ℝ)
    (hC : 0 < C) (hR : 0 < R) (hV : 0 < V) (hU : 0 ≤ U) (hG : 0 ≤ G)
    (h : Real.sqrt U ≤ C * R * Real.sqrt G) :
    (R ^ 2)⁻¹ * (V⁻¹ * U) ≤ C ^ 2 * (V⁻¹ * G) := by
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg U)
    (mul_nonneg (mul_nonneg hC.le hR.le) (Real.sqrt_nonneg G))).mpr h
  rw [Real.sq_sqrt hU, mul_pow, mul_pow, Real.sq_sqrt hG] at hs
  have hmul := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (inv_nonneg.mpr (sq_nonneg R)) (inv_nonneg.mpr hV.le))
  convert hmul using 1 <;> field_simp [hR.ne', hV.ne']

/-- Normalize and square the existing ball Poincaré estimate, preserving
its dependence only on the dimension. -/
theorem normalized_ball_poincare_square (hP : BallPoincareEstimate) (d : ℕ)
    (hd : 2 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        MemLp u 2 (volume.restrict (ball 0 R)) →
        MemLp g 2 (volume.restrict (ball 0 R)) → HasWeakGradient (ball 0 R) u g →
        (R^2)⁻¹ * (⨍ x in ball 0 R,
          (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume) ≤
          C * (⨍ x in ball 0 R, euclideanSq (g x) ∂volume) := by
  obtain ⟨C, hC, hp⟩ := hP d hd
  refine ⟨C^2, sq_pos_of_pos hC, ?_⟩
  intro R hR u g hu hg hw
  have h := hp 0 R hR u g hu hg hw
  simp only [sq_abs] at h
  have hU : 0 ≤ ∫ x in ball (0 : Vec d) R,
      (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume :=
    integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ ∫ x in ball (0 : Vec d) R, euclideanSq (g x) ∂volume := by
    apply integral_nonneg
    intro x
    change 0 ≤ ∑ j : Fin d, g x j * g x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (g x j)
  simpa only [average_eq, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using
    normalize_sqrt_bound C R (volume.real (ball (0 : Vec d) R)) _ _ hC hR
      (ball_volume_pos_finite d R hR) hU hG h

end EinsteinRelation.Correctors
