import EinsteinRelation.Sharpness.SeedDerivativeStationarity
import EinsteinRelation.Sharpness.SeedSegmentEnergy
import EinsteinRelation.Sharpness.SeedDifferenceEnergy
import EinsteinRelation.Sharpness.SeedSegmentFubini
open MeasureTheory
open EinsteinRelation.TimeChange
namespace EinsteinRelation.Sharpness
/-- Actual canonical seed gradient energy is positive in every coordinate.
Source main.tex1212–1218,1261–1265. Positive separated increments, actual FTC/CS,
true product integrability/Fubini, and derived derivative stationarity are consumed. -/
theorem integral_seedField_coordinateDerivative_sq_pos {d : ℕ}
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) (i : Fin d) :
    0 < ∫ W : NoiseSample d, (coordinateDerivative i (seedField d W) 0)^2 ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  have hunit : euclideanNorm (unitVector i) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  have hsep : (4 : ℝ) < euclideanNorm (0 - (5 : ℝ) • unitVector i) := by
    have heq : (0 : Vec d) - (5 : ℝ) • unitVector i = (-5 : ℝ) • unitVector i := by simp
    rw [heq, euclideanNorm_smul, hunit]
    norm_num
  have hpos := integral_seedField_difference_sq_pos hP ((5 : ℝ) • unitVector i) hsep
  have hFubini := integrable_and_integral_seedField_segment_derivative_sq_swap hP i
  have htimeInt : Integrable (fun W : NoiseSample d => ∫ t : ℝ in (0)..5,
      (coordinateDerivative i (seedField d W) (t • unitVector i))^2) P := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 5)] using
      hFubini.1.integral_prod_left
  have hincrement : Integrable (fun W =>
      (seedField d W ((5 : ℝ) • unitVector i) - seedField d W 0)^2) P := by
    refine (integrable_const (4 : ℝ)).mono'
      (((measurable_seedField d _).sub (measurable_seedField d 0)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with W
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := abs_le.mp (abs_seedField_le_one d W 0)
    have hx := abs_le.mp (abs_seedField_le_one d W ((5 : ℝ) • unitVector i))
    nlinarith [sq_nonneg (seedField d W ((5 : ℝ) • unitVector i) + seedField d W 0)]
  have hpoint (t : ℝ) :
      (∫ W : NoiseSample d, (coordinateDerivative i (seedField d W) (t • unitVector i))^2 ∂P) =
      ∫ W : NoiseSample d, (coordinateDerivative i (seedField d W) 0)^2 ∂P := by
    have hproc := identDistrib_seedField_derivative_process_translate hP [i] Unit
      (fun _ => 0) (t • unitVector i)
    have hscalar : ProbabilityTheory.IdentDistrib
        (fun W => coordinateDerivative i (seedField d W) (t • unitVector i))
        (fun W => coordinateDerivative i (seedField d W) 0) P P := by
      simpa only [Function.comp_def, add_zero, iteratedCoordinateDerivative_cons,
        iteratedCoordinateDerivative_nil] using hproc.comp (measurable_pi_apply ())
    exact (hscalar.comp (measurable_id.pow_const 2)).integral_eq
  have htime : (∫ W : NoiseSample d, (∫ t : ℝ in (0)..5,
      (coordinateDerivative i (seedField d W) (t • unitVector i))^2) ∂P) =
      5 * ∫ W : NoiseSample d, (coordinateDerivative i (seedField d W) 0)^2 ∂P := by
    rw [hFubini.2]
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const]
    norm_num [smul_eq_mul]
  have hle := integral_mono hincrement (htimeInt.const_mul 5)
    (fun W => seedField_segment_energy_le W i)
  rw [integral_const_mul, htime] at hle
  linarith
end EinsteinRelation.Sharpness

