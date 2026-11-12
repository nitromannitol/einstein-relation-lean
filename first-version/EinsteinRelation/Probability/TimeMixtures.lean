import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! # Absolute continuity of actual time mixtures

The density construction in `paper/main.tex:436–443` first obtains absolute
continuity at fixed time from Girsanov and unforced invariance. This lemma
transfers those sectionwise assertions to the genuine product-law pushforward
at an independent time. No density or resolvent estimate is a premise.
-/

open MeasureTheory

namespace EinsteinRelation.Probability

/-- An independently sampled time preserves sectionwise absolute continuity. -/
theorem map_prod_absolutelyContinuous_of_ae_sections {T Ω E : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace E]
    (ν : Measure T) (μ : Measure Ω) [SFinite μ] (Q : Measure E)
    (f : T × Ω → E) (hf : Measurable f)
    (h : ∀ᵐ t ∂ν, (μ.map (fun ω => f (t, ω))) ≪ Q) :
    (ν.prod μ).map f ≪ Q := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hQs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs)]
  rw [← lintegral_zero (μ := ν)]
  apply lintegral_congr_ae
  filter_upwards [h] with t ht
  have hsect : Measurable (fun ω => f (t, ω)) := hf.comp measurable_prodMk_left
  change μ ((fun ω => f (t, ω)) ⁻¹' s) = 0
  rw [← Measure.map_apply hsect hs]
  exact ht hQs

end EinsteinRelation.Probability
