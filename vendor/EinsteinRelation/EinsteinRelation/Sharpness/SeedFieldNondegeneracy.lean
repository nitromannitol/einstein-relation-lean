import EinsteinRelation.Sharpness.SeedResidualSplit
import EinsteinRelation.Sharpness.NoiseResidualBound
import EinsteinRelation.Sharpness.GaussianMarginal
import EinsteinRelation.Sharpness.NoiseFieldSign
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- Both strict signs of the actual canonical seed at zero have positive probability.
Source: main.tex1212–1216. The compact residual bound and Gaussian scalar independence
are derived for the same white-noise law; no nonconstancy premise is supplied. -/
theorem positive_probability_seedField_signs {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) :
    (0 < P {W | 0 < seedField d W 0}) ∧ (0 < P {W | seedField d W 0 < 0}) := by
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨f, hf, ha, hind⟩ := exists_seedField_scalar_residual_split d
  let K := mollifierNoiseTest d
  let a : ℝ := (∫ u : Vec d, (f u)^2)⁻¹
  let C : Set (Vec d) := tsupport (K : Vec d → ℝ)
  let R : NoiseSample d → C → ℝ := fun W y => mollifiedNoise W K (0-y.1) - a * W f
  have heval (W : NoiseSample d) (y : Vec d) :
      W (kernelTest K (0-y) - a • f) = mollifiedNoise W K (0-y) - a * W f := by
    rw [map_sub, map_smul, smul_eq_mul]
    rfl
  obtain ⟨M, hE, hEp⟩ := exists_positive_probability_noise_residual_bound P id
    (fun g => External.measurable_noiseEvaluation g) K f 0 a C K.hasCompactSupport
  let E : Set (NoiseSample d) := {W | ∀ y ∈ C, |W (kernelTest K (0-y) - a • f)| ≤ (M : ℝ)}
  have hE' : MeasurableSet[(MeasurableSpace.pi : MeasurableSpace (C → ℝ)).comap R] E := by
    have hs : (MeasurableSpace.pi : MeasurableSpace (C → ℝ)).comap R =
        ⨆ y : C, (borel ℝ).comap (fun W : NoiseSample d => W (kernelTest K (0-y.1)-a • f)) := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp, Function.comp_def]
      congr 1
      funext y
      congr 1
      funext W
      exact (heval W y.1).symm
    rw [hs]
    exact hE
  have hind' : ProbabilityTheory.IndepFun (fun W : NoiseSample d => W f) R P := hind P hP
  have hupper (t : ℝ) : 0 < P {W | t < W f} :=
    noise_evaluation_upper_tail_pos P id (fun g => External.measurable_noiseEvaluation g)
      hP.2 f hf t
  have hlower (t : ℝ) : 0 < P {W | W f < t} := by
    have hp := noise_evaluation_upper_tail_pos P id
      (fun g => External.measurable_noiseEvaluation g) hP.2 (-f) (neg_ne_zero.mpr hf) (-t)
    simpa only [id_eq, map_neg, neg_lt_neg_iff] using hp
  have hinter (S : Set ℝ) (hS : MeasurableSet S) (hp : 0 < P ((fun W : NoiseSample d => W f) ⁻¹' S)) :
      0 < P (((fun W : NoiseSample d => W f) ⁻¹' S) ∩ E) := by
    rw [hind'.meas_inter (s := (fun W : NoiseSample d => W f) ⁻¹' S) (t := E)
      (MeasurableSpace.measurableSet_comap.mpr ⟨S, hS, rfl⟩) hE']
    exact ENNReal.mul_pos hp.ne' hEp.ne'
  have hup := hinter (Set.Ioi (((M : ℝ)+1)/a)) measurableSet_Ioi (hupper _)
  have hlow := hinter (Set.Iio (-((M : ℝ)+1)/a)) measurableSet_Iio (hlower _)
  have hnonneg (y : Vec d) : 0 ≤ K y := mollifier_nonneg d y
  constructor
  · refine lt_of_lt_of_le hup (measure_mono ?_)
    intro W hW
    apply smoothedNoiseField_pos_of_local_pos K K W 0 hnonneg (mollifierNoiseTest_ne_zero d)
    intro y hy
    have hyC : y ∈ C := subset_tsupport (K : Vec d → ℝ) (Function.mem_support.mpr hy)
    have hbound := (abs_le.mp (hW.2 y hyC)).1
    rw [heval] at hbound
    have hlarge : (M : ℝ)+1 < W f * a := (div_lt_iff₀ ha).mp hW.1
    nlinarith
  · refine lt_of_lt_of_le hlow (measure_mono ?_)
    intro W hW
    apply smoothedNoiseField_neg_of_local_neg K K W 0 hnonneg (mollifierNoiseTest_ne_zero d)
    intro y hy
    have hyC : y ∈ C := subset_tsupport (K : Vec d → ℝ) (Function.mem_support.mpr hy)
    have hbound := (abs_le.mp (hW.2 y hyC)).2
    rw [heval] at hbound
    have hlarge : W f * a < -((M : ℝ)+1) := (lt_div_iff₀ ha).mp hW.1
    nlinarith

end EinsteinRelation.Sharpness
