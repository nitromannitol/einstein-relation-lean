import EinsteinRelation.Correctors.AKMSpatialRescaling
import EinsteinRelation.Correctors.SpatialBallVolume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.Correctors.AKMSpatialRescaling

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem measurableSet_originBall_dilation {d : ℕ} (R : ℝ) :
    MeasurableSet (originBall d R) := by
  unfold originBall euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- Change of variables from the Euclidean ball of radius `r` to the unit ball. -/
private theorem integral_originBall_inv_smul_dilation {d : ℕ} (g : Vec d → ℝ) {r : ℝ}
    (hr : 0 < r) :
    (∫ x in originBall d r, g (r⁻¹ • x) ∂volume) =
      r ^ d * ∫ y in originBall d 1, g y ∂volume := by
  have hpre (x : Vec d) : x ∈ originBall d r ↔ r⁻¹ • x ∈ originBall d 1 := by
    simp only [originBall, Set.mem_setOf_eq, euclideanNorm_smul _ (inv_nonneg.mpr hr.le)]
    constructor
    · intro h
      calc r⁻¹ * euclideanNorm x < r⁻¹ * r := mul_lt_mul_of_pos_left h (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · intro h
      have h' := mul_lt_mul_of_pos_left h hr
      rwa [mul_inv_cancel_left₀ hr.ne', mul_one] at h'
  have hind : (fun x : Vec d => (originBall d 1).indicator g (r⁻¹ • x)) =
      (originBall d r).indicator (fun x => g (r⁻¹ • x)) := by
    funext x
    by_cases hx : x ∈ originBall d r
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hpre x).mp hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hpre x).mpr hx)]
  have h := Measure.integral_comp_inv_smul_of_nonneg volume ((originBall d 1).indicator g) hr.le
  rw [hind, integral_indicator (measurableSet_originBall_dilation r),
    integral_indicator (measurableSet_originBall_dilation 1)] at h
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul] using h

/-- The Euclidean ball volume scales like `r ^ d`. -/
private theorem volume_originBall_dilation {d : ℕ} {r : ℝ} (hr : 0 < r) :
    (volume (originBall d r)).toReal = r ^ d * (volume (originBall d 1)).toReal := by
  have h := integral_originBall_inv_smul_dilation (fun _ : Vec d => (1 : ℝ)) hr
  simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using h

/-- Source: `paper/main.tex:938–945`. Euclidean normalized averages
cancel the dilation Jacobian, even for totalized nonintegrable functions. -/
theorem average_originBall_inv_smul {d : ℕ} (f : Vec d → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (⨍ x in originBall d r, f (r⁻¹ • x) ∂volume) =
      ⨍ x in originBall d 1, f x ∂volume := by
  have hd : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  rw [integral_originBall_inv_smul_dilation f hr, volume_originBall_dilation hr, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hd, one_mul]

end EinsteinRelation.Correctors

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem measurableSet_ball_dilation_scaled {d : ℕ} (ρ : ℝ) :
    MeasurableSet (ball (0 : Vec d) ρ) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

theorem setAverage_euclideanBall_smul {d : ℕ} (f : Vec d → ℝ)
    (r R : ℝ) (hr : 0 < r) (_hR : 0 < R) :
    (⨍ x in ball 0 R, f (r • x) ∂volume) =
      ⨍ y in ball 0 (r * R), f y ∂volume := by
  have hpre (x : Vec d) : r • x ∈ ball (0 : Vec d) (r * R) ↔ x ∈ ball (0 : Vec d) R := by
    simp only [ball, Set.mem_setOf_eq, sub_zero, euclideanNorm_smul _ hr.le]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hr.le, fun h => mul_lt_mul_of_pos_left h hr⟩
  -- Change of variables for an arbitrary integrand, with the Jacobian `(r⁻¹)^d`.
  have key : ∀ g : Vec d → ℝ, (∫ x in ball (0 : Vec d) R, g (r • x) ∂volume) =
      (r⁻¹) ^ d * ∫ y in ball (0 : Vec d) (r * R), g y ∂volume := by
    intro g
    have hind : (fun x : Vec d => (ball (0 : Vec d) (r * R)).indicator g (r • x)) =
        (ball (0 : Vec d) R).indicator (fun x => g (r • x)) := by
      funext x
      by_cases hx : x ∈ ball (0 : Vec d) R
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hpre x).mpr hx)]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hpre x).mp hx)]
    have h := Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      ((ball (0 : Vec d) (r * R)).indicator g) (inv_nonneg.mpr hr.le)
    rw [inv_inv, hind, integral_indicator (measurableSet_ball_dilation_scaled R),
      integral_indicator (measurableSet_ball_dilation_scaled (r * R))] at h
    simpa only [Module.finrank_fin_fun, smul_eq_mul] using h
  -- Volume scales by the same Jacobian: take `g = 1` in `key`.
  have hvol : (volume (ball (0 : Vec d) R)).toReal =
      (r⁻¹) ^ d * (volume (ball (0 : Vec d) (r * R))).toReal := by
    have h1 := key (fun _ => (1 : ℝ))
    simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at h1
    exact h1
  have ha : (r⁻¹) ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero hr.ne')
  simp only [setAverage_eq, measureReal_def]
  rw [key f, hvol, smul_eq_mul, smul_eq_mul, mul_inv, mul_comm ((r⁻¹) ^ d)⁻¹ _, mul_assoc,
    inv_mul_cancel_left₀ ha]

end EinsteinRelation.Correctors
