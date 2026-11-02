import EinsteinRelation.Sharpness.SeedFieldNondegeneracy
import EinsteinRelation.Sharpness.SeedFieldFiniteRange
import EinsteinRelation.Sharpness.NoiseFieldStationarity
open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- Source main.tex1212–1216,1261–1265: separated actual seed values have strictly
positive squared difference expectation. This supplies the probability lower
bound needed before the segment estimate proves positive gradient energy. -/
theorem integral_seedField_difference_sq_pos {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (x : Vec d) (hx : (4 : ℝ) < euclideanNorm (0-x)) :
    0 < ∫ W, (seedField d W x - seedField d W 0)^2 ∂P := by
  letI : IsProbabilityMeasure P := hP.1
  have hproc := identDistrib_smoothedNoiseField_process_translate P id
    (fun f => External.measurable_noiseEvaluation f) hP.2
    (mollifierNoiseTest d) (mollifierNoiseTest d) Unit (fun _ => 0) x
  have hval : ProbabilityTheory.IdentDistrib (fun W => seedField d W x)
      (fun W => seedField d W 0) P P := by
    simpa only [Function.comp_def, add_zero, seedField, id_eq] using
      hproc.comp (measurable_pi_apply ())
  have hsign := positive_probability_seedField_signs hP
  have hxneg : 0 < P {W | seedField d W x < 0} := by
    change 0 < P ((fun W => seedField d W x) ⁻¹' Set.Iio (0 : ℝ))
    rw [hval.measure_mem_eq (s := Set.Iio (0 : ℝ)) measurableSet_Iio]
    exact hsign.2
  have hindproc := indepFun_seedField_processes_of_separated hP Unit Unit
    (fun _ => 0) (fun _ => x) (fun _ _ => hx)
  have hind : ProbabilityTheory.IndepFun (fun W => seedField d W 0)
      (fun W => seedField d W x) P := by
    exact hindproc.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  have hprod : P {W | 0 < seedField d W 0 ∧ seedField d W x < 0} =
      P {W | 0 < seedField d W 0} * P {W | seedField d W x < 0} :=
    hind.measure_inter_preimage_eq_mul (Set.Ioi 0) (Set.Iio 0) measurableSet_Ioi measurableSet_Iio
  have hevent : 0 < P {W | 0 < seedField d W 0 ∧ seedField d W x < 0} := by
    rw [hprod]
    exact ENNReal.mul_pos hsign.1.ne' hxneg.ne'
  have hint : Integrable (fun W => (seedField d W x - seedField d W 0)^2) P := by
    refine (integrable_const (4 : ℝ)).mono'
      (((measurable_seedField d x).sub (measurable_seedField d 0)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with W
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := abs_le.mp (abs_seedField_le_one d W 0)
    have h1 := abs_le.mp (abs_seedField_le_one d W x)
    nlinarith [sq_nonneg (seedField d W x + seedField d W 0)]
  apply (integral_pos_iff_support_of_nonneg (fun W => sq_nonneg _) hint).2
  refine lt_of_lt_of_le hevent (measure_mono ?_)
  intro W hW
  apply pow_ne_zero
  linarith [hW.1,hW.2]

end EinsteinRelation.Sharpness
