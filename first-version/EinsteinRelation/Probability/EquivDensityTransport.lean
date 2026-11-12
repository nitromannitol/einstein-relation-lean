import EinsteinRelation.External.GantertSection7Support
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Probability

/-- A measurable equivalence transports a measurable density by its
literal inverse coordinate map. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  change (∫⁻ x in e ⁻¹' s, f x ∂μ) =
    ∫⁻ y in s, (f ∘ e.symm) y ∂μ.map e
  rw [setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp only [Function.comp_apply, e.symm_apply_apply]

/-- The density transport identity also holds for an almost-everywhere
measurable density, with its original values retained. -/
theorem map_withDensity_equiv_of_aemeasurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  rw [withDensity_congr_ae hf.ae_eq_mk,
    map_withDensity_equiv e μ (hf.mk f) hf.measurable_mk]
  apply withDensity_congr_ae
  apply e.measurableEmbedding.ae_map_iff.mpr
  simpa only [e.symm_apply_apply] using hf.ae_eq_mk.symm

/-- Source `paper/main.tex:406–408`: the actual heat-kernel density is translated with its endpoint. -/
theorem map_sub_const_withDensity_volume {d : ℕ} (a : Vec d)
    (f : Vec d → ℝ≥0∞) (hf : AEMeasurable f (volume : Measure (Vec d))) :
    ((volume : Measure (Vec d)).withDensity f).map (fun y => y - a) =
      volume.withDensity (fun y => f (a + y)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  have hm : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have h := map_withDensity_equiv_of_aemeasurable e volume f hf
  rw [hm] at h
  simpa [e, sub_eq_add_neg, add_comm] using h

end EinsteinRelation.Probability
