import EinsteinRelation.Sharpness.SeedFieldNondegeneracy
import Mathlib.Topology.Hom.ContinuousEvalConst
open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- Source main.tex1212–1216: strict signs for the actual compact-open field law. -/
theorem positive_probability_seedFieldLaw_signs {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) :
    0 < seedFieldLaw P {H | 0 < H 0} ∧ 0 < seedFieldLaw P {H | H 0 < 0} := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  have heval : Measurable (fun H : C(Vec d, ℝ) => H (0 : Vec d)) :=
    (continuous_eval_const 0).borel_measurable
  have hp : MeasurableSet {H : C(Vec d, ℝ) | 0 < H 0} := measurableSet_lt measurable_const heval
  have hn : MeasurableSet {H : C(Vec d, ℝ) | H 0 < 0} := measurableSet_lt heval measurable_const
  have ep : seedFieldLaw P {H | 0 < H 0} = P {W | 0 < seedField d W 0} :=
    Measure.map_apply (measurable_seedContinuousField d) hp
  have en : seedFieldLaw P {H | H 0 < 0} = P {W | seedField d W 0 < 0} :=
    Measure.map_apply (measurable_seedContinuousField d) hn
  rw [ep,en]
  exact positive_probability_seedField_signs hP

/-- The actual seed at zero is not almost surely any deterministic scalar. -/
theorem seedField_zero_not_ae_eq_const {d : ℕ} {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (c : ℝ) :
    ¬ ((fun W => seedField d W 0) =ᵐ[P] fun _ => c) := by
  intro h
  obtain ⟨hp,hn⟩ := positive_probability_seedField_signs hP
  by_cases hc : 0 ≤ c
  · have hneg : ∀ᵐ W ∂P, ¬ seedField d W 0 < 0 := by
      filter_upwards [h] with W hW
      rw [hW]
      exact not_lt.mpr hc
    have hz : P {W | seedField d W 0 < 0} = 0 := by
      simpa only [not_not] using ae_iff.mp hneg
    exact hn.ne' hz
  · have hpos : ∀ᵐ W ∂P, ¬ 0 < seedField d W 0 := by
      filter_upwards [h] with W hW
      rw [hW]
      exact not_lt.mpr (le_of_not_ge hc)
    have hz : P {W | 0 < seedField d W 0} = 0 := by
      simpa only [not_not] using ae_iff.mp hpos
    exact hp.ne' hz

end EinsteinRelation.Sharpness
