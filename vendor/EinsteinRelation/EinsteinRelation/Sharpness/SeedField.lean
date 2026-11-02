import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Sharpness.NoiseField
import EinsteinRelation.Sharpness.NoiseMollifier

/-! # The canonical bounded smooth seed field for the sharpness construction

Source `paper/main.tex:1212–1216`: use the proved nonnegative, unit-mass compact
kernel as both ζ and K. The field is the actual two-stage convolution on genuine
distribution samples. The actual compact-open law below is a probability measure
under the unchanged explicit white-noise input. Centering, stationarity, finite
range, derivative bounds and nondegeneracy are separate internal arguments.
-/

open MeasureTheory
namespace EinsteinRelation

namespace Sharpness
/-- The source convolution, using the canonical admissible kernels. -/
noncomputable def seedField (d : ℕ) (W : NoiseSample d) : Vec d → ℝ :=
  smoothedNoiseField (mollifierNoiseTest d) (mollifierNoiseTest d) W

theorem contDiff_seedField (d : ℕ) (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) (seedField d W) :=
  contDiff_smoothedNoiseField _ _ _

theorem abs_seedField_le_one (d : ℕ) (W : NoiseSample d) (x : Vec d) :
    |seedField d W x| ≤ 1 := by
  have h := abs_smoothedNoiseField_le (mollifierNoiseTest d) (mollifierNoiseTest d) W x
  have hm : (∫ y : Vec d, |mollifierNoiseTest d y|) = 1 := by
    simp only [mollifierNoiseTest_apply, abs_of_nonneg (mollifier_nonneg d _)]
    exact integral_mollifier d
  exact hm ▸ h

theorem measurable_seedField_uncurry (d : ℕ) :
    Measurable (fun p : NoiseSample d × Vec d => seedField d p.1 p.2) :=
  measurable_smoothedNoiseField_uncurry id
    (fun f => External.measurable_noiseEvaluation f) _ _

/-- The same actual sample bundled in the compact-open continuous-field space. -/
noncomputable def seedContinuousField (d : ℕ) (W : NoiseSample d) : C(Vec d, ℝ) :=
  ⟨seedField d W, (contDiff_seedField d W).continuous⟩

@[simp] theorem seedContinuousField_apply (d : ℕ) (W : NoiseSample d) (x : Vec d) :
    seedContinuousField d W x = seedField d W x := rfl

theorem measurable_seedField (d : ℕ) (x : Vec d) :
    Measurable (fun W : NoiseSample d => seedField d W x) := by
  have hpair : Measurable (fun W : NoiseSample d => (W, x)) :=
    measurable_id.prodMk measurable_const
  exact Measurable.comp (g := fun p : NoiseSample d × Vec d => seedField d p.1 p.2)
    (f := fun W : NoiseSample d => (W, x)) (measurable_seedField_uncurry d) hpair

theorem measurable_seedContinuousField (d : ℕ) :
    @Measurable (NoiseSample d) C(Vec d, ℝ) inferInstance (borel C(Vec d, ℝ))
      (seedContinuousField d) := by
  refine measurable_continuousMap_of_evaluations (seedContinuousField d) ?_
  intro x
  simp only [seedContinuousField_apply]
  exact measurable_seedField d x

/-- The literal pushforward of the supplied noise law by the constructed field. -/
noncomputable def seedFieldLaw {d : ℕ} (P : Measure (NoiseSample d)) :
    @Measure C(Vec d, ℝ) (borel C(Vec d, ℝ)) :=
  @Measure.map (NoiseSample d) C(Vec d, ℝ) inferInstance (borel C(Vec d, ℝ))
    (seedContinuousField d) P

theorem isProbabilityMeasure_seedFieldLaw {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) : IsProbabilityMeasure (seedFieldLaw P) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  letI : IsProbabilityMeasure P := hP.1
  change IsProbabilityMeasure (P.map (seedContinuousField d))
  infer_instance

end Sharpness
end EinsteinRelation
