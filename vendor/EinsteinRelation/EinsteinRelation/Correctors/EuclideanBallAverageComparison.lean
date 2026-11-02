import EinsteinRelation.Correctors.AKMSpatialRescaling
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Correctors.StationarySpatialWeakPotentials
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Comparing Euclidean ball averages with coordinate cube averages

Source: `paper/main.tex:693-698`. The comparison constant depends only on
the dimension. Coordinate cubes are used solely to transfer the stationary
maximal bound to the manuscript's Euclidean balls.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM

/-- Euclidean ball volume scales with the actual dimension. -/
theorem euclideanBall_volume_real {d : ℕ} (R : ℝ) (hR : 0 < R) :
    volume.real (ball (0 : Vec d) R) = R ^ d * volume.real (ball (0 : Vec d) 1) := by
  have h := integral_unitBall_inv_smul (d := d) (fun _ => (1 : ℝ)) (inv_pos.mpr hR)
  simp only [inv_inv, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at h
  change volume.real (ball (0 : Vec d) 1) =
    R⁻¹ ^ d * volume.real (ball (0 : Vec d) R) at h
  calc
    volume.real (ball (0 : Vec d) R) =
        R ^ d * (R⁻¹ ^ d * volume.real (ball (0 : Vec d) R)) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, one_mul]
    _ = R ^ d * volume.real (ball (0 : Vec d) 1) := by rw [← h]

/-- A nonnegative spatial average over a Euclidean ball is bounded by
the average over any enclosing coordinate cube with at most twice its
radius, with a dimension-only constant. -/
theorem exists_ball_average_le_cube_average (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < R → R ≤ r → r ≤ 2 * R →
      ∀ f : Vec d → ℝ, (∀ x, 0 ≤ f x) →
        IntegrableOn f (Metric.closedBall (0 : Vec d) r) volume →
        (⨍ x in ball 0 R, f x ∂volume) ≤
          C * (⨍ x in Metric.closedBall (0 : Vec d) r, f x ∂volume) := by
  let V := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := ball_volume_pos_finite d 1 zero_lt_one
  let C : ℝ := 4 ^ d / V
  have hC : 0 < C := div_pos (pow_pos (by norm_num) _) hV
  refine ⟨C, hC, ?_⟩
  intro R r hR hRr hr f hf hi
  have hrpos : 0 < r := hR.trans_le hRr
  have hsub : ball (0 : Vec d) R ⊆ Metric.closedBall 0 r :=
    (euclideanBall_subset_coordinateClosedBall R hR.le).trans
      (Metric.closedBall_subset_closedBall hRr)
  have hI : (∫ x in ball (0 : Vec d) R, f x ∂volume) ≤
      ∫ x in Metric.closedBall (0 : Vec d) r, f x ∂volume :=
    setIntegral_mono_set hi (ae_of_all _ hf) (ae_of_all _ fun _ hx => hsub hx)
  have hVr : 0 < volume.real (Metric.closedBall (0 : Vec d) r) := by
    rw [Measure.real, Real.volume_pi_closedBall _ hrpos.le,
      ENNReal.toReal_ofReal (by positivity)]
    exact pow_pos (by positivity) _
  have hVB : 0 < volume.real (ball (0 : Vec d) R) := ball_volume_pos_finite d R hR
  have hratio : (volume.real (ball (0 : Vec d) R))⁻¹ ≤
      C * (volume.real (Metric.closedBall (0 : Vec d) r))⁻¹ := by
    simp only [← one_div, mul_one_div]
    apply (div_le_div_iff₀ hVB hVr).mpr
    rw [euclideanBall_volume_real R hR]
    have hc : volume.real (Metric.closedBall (0 : Vec d) r) = (2 * r)^d := by
      rw [Measure.real, Real.volume_pi_closedBall _ hrpos.le,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [Fintype.card_fin]
    rw [one_mul, hc]
    change (2 * r)^d ≤ (4 ^ d / V) * (R ^ d * V)
    have hmul : (4 ^ d / V) * (R ^ d * V) = (4 * R)^d := by
      rw [div_eq_mul_inv, mul_pow]
      field_simp [hV.ne']
    rw [hmul]
    exact pow_le_pow_left₀ (by positivity) (by linarith : 2 * r ≤ 4 * R) d
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  calc
    _ ≤ (volume.real (ball (0 : Vec d) R))⁻¹ *
        ∫ x in Metric.closedBall (0 : Vec d) r, f x ∂volume :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hVB.le)
    _ ≤ (C * (volume.real (Metric.closedBall (0 : Vec d) r))⁻¹) *
        ∫ x in Metric.closedBall (0 : Vec d) r, f x ∂volume :=
      mul_le_mul_of_nonneg_right hratio (integral_nonneg hf)
    _ = _ := mul_assoc _ _ _

end EinsteinRelation.Correctors
