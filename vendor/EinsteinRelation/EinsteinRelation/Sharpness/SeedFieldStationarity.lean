import EinsteinRelation.Sharpness.SeedField
import EinsteinRelation.Sharpness.NoiseFieldStationarity
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map

/-! # Translation stationarity of the canonical sharpness seed

Source `paper/main.tex:1212–1218`: the seed `h := ζ * tanh(K * W)` with the canonical kernels
`ζ = K = mollifierNoiseTest d`. The stationarity that `paper/main.tex:1261–1265` uses for
`E[∂₁ψ] = 0` is the translation invariance proved here.

`identDistrib_seedField_process_translate` specializes the process-level stationarity of the
literal smoothed field to the canonical kernels, under the same white-noise characteristic
functional `hP.2`. `map_seedFieldLaw_translate` transfers this finite-dimensional law to the
compact-open Borel law of the seed. A countable dense evaluation is a measurable embedding of
`C(Vec d, ℝ)` into `D → ℝ`, so equality of the image laws determines the Borel law. The shift
`h` is a literal vector throughout; no stationarity of `h` and no shift carrier is assumed.
-/

open MeasureTheory

namespace EinsteinRelation

namespace Sharpness

/-- The literal translate `x ↦ H (h + x)` of a compact-open continuous field. -/
private def shiftContinuousField {d : ℕ} (h : Vec d) (H : C(Vec d, ℝ)) : C(Vec d, ℝ) :=
  ⟨fun x => H (h + x), H.continuous.comp (continuous_const.add continuous_id)⟩

/-- **Process-level stationarity of the canonical seed.** Source: `paper/main.tex:1212–1218`.
The specialization `ζ = K = mollifierNoiseTest d` of
`identDistrib_smoothedNoiseField_process_translate`, under the same white-noise characteristic
functional. The index type `T`, the family `xs` and the shift `h` are arbitrary. -/
theorem identDistrib_seedField_process_translate (d : ℕ) {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) (T : Type) (xs : T → Vec d) (h : Vec d) :
    ProbabilityTheory.IdentDistrib (fun W : NoiseSample d => fun t : T => seedField d W (h+xs t))
    (fun W : NoiseSample d => fun t : T => seedField d W (xs t)) P P := by
  haveI : IsProbabilityMeasure P := hP.1
  exact identDistrib_smoothedNoiseField_process_translate P (fun W : NoiseSample d => W)
    (fun f => External.measurable_noiseEvaluation f) hP.2
    (mollifierNoiseTest d) (mollifierNoiseTest d) T xs h

/-- **Compact-open law invariance of the canonical seed under translation.** Source:
`paper/main.tex:1212–1218`. The literal Borel law of the seed `x ↦ ζ * tanh(K * W)(h + x)`
equals the Borel law of the untranslated seed, for every fixed shift `h`. -/
theorem map_seedFieldLaw_translate (d : ℕ) {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) :
    letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
    ∀ h : Vec d, Measure.map (fun H : C(Vec d, ℝ) =>
      (⟨fun x => H (h+x), H.continuous.comp (continuous_const.add continuous_id)⟩ : C(Vec d, ℝ)))
      (seedFieldLaw P) = seedFieldLaw P := by
  intro h
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  haveI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  change Measure.map (shiftContinuousField h) (seedFieldLaw P) = seedFieldLaw P
  -- A countable dense index set gives a measurable embedding of the compact-open Borel carrier,
  -- as in `measurable_continuousMap_of_evaluations`.
  obtain ⟨D : Set (Vec d), hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  letI : Countable D := hDcount.to_subtype
  let E : C(Vec d, ℝ) → (D → ℝ) := fun f x => f x.1
  have hEcont : Continuous E := continuous_pi fun x => continuous_eval_const x.1
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.injective_restrict hDdense
    exact ContinuousMap.ext fun x => congrFun hfg x
  have hEmb : MeasurableEmbedding E := hEcont.measurableEmbedding hEinj
  have hE : Measurable E := hEmb.measurable
  have hS : Measurable (seedContinuousField d) := measurable_seedContinuousField d
  have hτ : Measurable (shiftContinuousField h) := by
    refine measurable_continuousMap_of_evaluations (shiftContinuousField h) fun x => ?_
    have hc : Continuous (fun f : C(Vec d, ℝ) => f (h + x)) := continuous_eval_const (h + x)
    exact hc.measurable
  -- The countable evaluation of the translated seed has the same law as that of the seed.
  have hid := identDistrib_seedField_process_translate d hP (↥D) (fun t : ↥D => (t : Vec d)) h
  have hmid : Measure.map E (Measure.map (shiftContinuousField h) (seedFieldLaw P)) =
      Measure.map E (seedFieldLaw P) := by
    calc Measure.map E (Measure.map (shiftContinuousField h) (seedFieldLaw P))
        = Measure.map (E ∘ shiftContinuousField h) (seedFieldLaw P) := Measure.map_map hE hτ
      _ = Measure.map ((E ∘ shiftContinuousField h) ∘ seedContinuousField d) P :=
          Measure.map_map (hE.comp hτ) hS
      _ = Measure.map
          (fun W : NoiseSample d => fun t : ↥D => seedField d W (h + (t : Vec d))) P := rfl
      _ = Measure.map (fun W : NoiseSample d => fun t : ↥D => seedField d W (t : Vec d)) P :=
          hid.map_eq
      _ = Measure.map (E ∘ seedContinuousField d) P := rfl
      _ = Measure.map E (Measure.map (seedContinuousField d) P) :=
          (Measure.map_map hE hS).symm
      _ = Measure.map E (seedFieldLaw P) := rfl
  -- Measurable embeddings reflect equality of image laws on Borel sets.
  refine Measure.ext fun s _ => ?_
  have hpre : E ⁻¹' (E '' s) = s := hEinj.preimage_image s
  calc Measure.map (shiftContinuousField h) (seedFieldLaw P) s
      = Measure.map E (Measure.map (shiftContinuousField h) (seedFieldLaw P)) (E '' s) := by
        rw [hEmb.map_apply, hpre]
    _ = Measure.map E (seedFieldLaw P) (E '' s) := by rw [hmid]
    _ = seedFieldLaw P s := by rw [hEmb.map_apply, hpre]

end Sharpness
end EinsteinRelation
