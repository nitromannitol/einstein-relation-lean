import EinsteinRelation.Correctors.BallPoincareTransfer
import EinsteinRelation.Correctors.PairedPDEAmplitude
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Scaling the coordinate Lebesgue volume of the actual Euclidean ball.
Source: `paper/main.tex:862–866`. -/
theorem paired_ball_volume_scale {d : ℕ} {R : ℝ} (hR : 0 < R) :
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
end EinsteinRelation.Correctors
