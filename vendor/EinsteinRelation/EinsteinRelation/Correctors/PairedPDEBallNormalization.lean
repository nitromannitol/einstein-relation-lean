import EinsteinRelation.Correctors.PairedPDECenteredAmplitude
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The normalized planar centered-amplitude bound

Source: `paper/main.tex:862–873`. Coordinate Lebesgue volume is transported
to Euclidean space before scaling. The resulting constant is independent
of the radius and of the nonnegative mass-one centering kernel.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- Exact volume scaling for the manuscript's Euclidean balls.
Source: `paper/main.tex:862–866`. -/
theorem paired_ball_volume_real {d : ℕ} {R : ℝ} (hR : 0 < R) :
    volume.real (ball (0 : Vec d) R) = R ^ d * volume.real (ball (0 : Vec d) 1) := by
  have hpre (r : ℝ) :
      (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' ball 0 r =
        Metric.ball 0 r := by
    ext x
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, sub_zero,
      TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_ofLp, Metric.mem_ball,
      dist_zero_right]
  have hvol (r : ℝ) : volume (ball (0 : Vec d) r) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [← hpre r]
    exact ((PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (paired_isOpen_ball 0 r).measurableSet.nullMeasurableSet).symm
  simp only [Measure.real, hvol]
  rw [Measure.addHaar_ball_of_pos volume 0 hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace, Fintype.card_fin]

/-- The exact conversion from unnormalized energy to normalized RMS.
Source: `paper/main.tex:862–866`. -/
theorem paired_sqrt_energy_eq_volume_mul_rms {d : ℕ} {R : ℝ} (hR : 0 < R)
    (G : Vec d → Vec d) :
    Real.sqrt (∫ x in ball (0 : Vec d) R, euclideanSq (G x)) =
      Real.sqrt (volume.real (ball (0 : Vec d) R)) * vectorRms volume (ball 0 R) G := by
  have hV := paired_ball_volume_pos_finite (d := d) hR
  simp only [vectorRms, average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change Real.sqrt _ = Real.sqrt (volume.real (ball (0 : Vec d) R)) *
    Real.sqrt ((volume.real (ball (0 : Vec d) R))⁻¹ * _)
  rw [← Real.sqrt_mul hV.le, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]

/-- The manuscript's planar centered amplitude is at most `C R` times
its normalized paired gradient energy. Constants precede all radii and
solutions; the regular representative and GT inputs remain explicit.
Source: `paper/main.tex:862–873`. -/
theorem paired_harmonic_centered_amplitude_planar_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (a : Vec 2 → Mat 2) (u : Vec 2 → ℝ) (G : Vec 2 → Vec 2),
        EllipticBound (ball 0 (2 * R)) a lam Λ →
        WeakSolution (ball 0 (2 * R)) a u G →
        ContinuousOn u (ball 0 R) →
        ∀ (w : Vec 2 → ℝ), Integrable w volume →
          Integrable (fun x => w x * u x) volume →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 →
          Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R,
            |u x₀ - ∫ x, w x * u x| ≤ C * R * vectorRms volume (ball 0 (2 * R)) G := by
  obtain ⟨CU, hCU, hU⟩ := paired_harmonic_centered_amplitude_of_gt h817 hP
    (by decide : 2 ≤ 2) hlam hΛ
  let V := volume.real (ball (0 : Vec 2) 1)
  have hV : 0 < V := unitBall_volume_pos_finite 2
  refine ⟨4 * CU * Real.sqrt V, by positivity, ?_⟩
  intro R hR a u G hell hweak hcont w hw hwu hw0 hw1 hws x₀ hx₀
  have h := hU R hR a u G hell hweak hcont w hw hwu hw0 hw1 hws x₀ hx₀
  have hvol : Real.sqrt (volume.real (ball (0 : Vec 2) (2 * R))) =
      (2 * R) * Real.sqrt V := by
    rw [paired_ball_volume_real (d := 2) (by positivity), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 * R)]
  rw [paired_sqrt_energy_eq_volume_mul_rms (by positivity) G, hvol] at h
  have hpow : R ^ (-(2 : ℝ) / 2) = R⁻¹ := by norm_num [Real.rpow_neg_one]
  change |u x₀ - ∫ x, w x * u x| ≤
    CU * R ^ (-(2 : ℝ) / 2) * (2 * R) *
      (2 * R * Real.sqrt V * vectorRms volume (ball 0 (2 * R)) G) at h
  rw [hpow] at h
  calc
    _ ≤ _ := h
    _ = _ := by field_simp [hR.ne']; ring

end EinsteinRelation.Correctors
