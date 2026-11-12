import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped NNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:406–408`: translating paths preserves positive-time absolute continuity of their endpoint laws. -/
theorem map_recenterSample_endpoint_absolutelyContinuous {d : ℕ}
    (μ : Measure (CoupledSample d)) (a : Vec d) (t : ℝ≥0)
    (h : μ.map (fun z : CoupledSample d => z.1 t) ≪ (volume : Measure (Vec d))) :
    (μ.map (recenterSampleEquiv a)).map (fun z : CoupledSample d => z.1 t) ≪
      (volume : Measure (Vec d)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  have hp : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hm : Measurable (fun z : CoupledSample d => z.1 t) :=
    (measurable_pathPosition t).comp measurable_fst
  have hh := h.map e.measurable
  rw [hp, Measure.map_map e.measurable
    hm] at hh
  rw [Measure.map_map hm
    (recenterSampleEquiv a).measurable]
  simpa only [Function.comp_def, recenterSampleEquiv_apply, recenterSample,
    e, MeasurableEquiv.coe_addRight, sub_eq_add_neg] using hh

end EinsteinRelation.Regeneration
