import EinsteinRelation.Sharpness.SeedField
import EinsteinRelation.Sharpness.NoiseFieldMean

/-! # Centering of the concrete canonical sharpness seed

Source `paper/main.tex:1212–1216`. Both kernels are the actual canonical
mollifier. Integrability and mean zero follow from the Gaussian reflection
argument and proved product domination/Fubini. The external hypothesis remains
exactly generic white-noise existence; the constructed seed is not assumed.
-/

open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- Actual one-point integrability and centering, for the same supplied noise law. -/
theorem integrable_and_integral_seedField_eq_zero {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (x : Vec d) :
    Integrable (fun W => seedField d W x) P ∧
      (∫ W, seedField d W x ∂P) = 0 := by
  letI : IsProbabilityMeasure P := hP.1
  exact integrable_and_integral_smoothedNoiseField_eq_zero P id
    (fun f => External.measurable_noiseEvaluation f) hP.2 _ _ x

/-- One generic input law supplies the actual compact-open probability law and
all centered observations. Stationarity, finite range and nondegeneracy remain
internal obligations beyond this consumer. -/
theorem exists_centered_seedFieldLaw {d : ℕ} (h : External.WhiteNoiseExistence d) :
    ∃ P : Measure (NoiseSample d), External.IsWhiteNoiseLaw P ∧
      IsProbabilityMeasure (seedFieldLaw P) ∧ ∀ x : Vec d,
        Integrable (fun W => seedField d W x) P ∧
          (∫ W, seedField d W x ∂P) = 0 := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, hP, isProbabilityMeasure_seedFieldLaw hP,
    fun x => integrable_and_integral_seedField_eq_zero hP x⟩

end EinsteinRelation.Sharpness
