import EinsteinRelation.Correctors.StationaryCenterTransport
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Spatially centered stationary fields are integrable

Source: `paper/main.tex:913–938`. For a finite outer center law `ν`, the field
`(x, (y, ω)) ↦ F(x - y, τ_y ω)` is integrable against `ν ⊗ (Leb ⊗ Q)` whenever
`F` is integrable against `Leb ⊗ Q`. The proof composes two measure-preserving
maps: translation of the inner environment about the inner center `y`, and the
reflection `y ↦ x - y` at each outer center `x`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Fiber of the spatial reflection at the outer center `x`:
`(y, ω) ↦ (x - y, ω)`. Source: `paper/main.tex:913–938`. -/
private def spatialReflect {d : ℕ} (x : Vec d) (z : Vec d × FieldPair d) :
    Vec d × FieldPair d :=
  (x - z.1, z.2)

/-- For each fixed outer center, the reflection of the inner pair preserves
the Lebesgue-times-stationary product law. Source: `paper/main.tex:913–938`. -/
private theorem measurePreserving_spatialReflect {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (x : Vec d) :
    MeasurePreserving (spatialReflect x) (volume.prod Q) (volume.prod Q) :=
  (Measure.measurePreserving_sub_left volume x).prod (MeasurePreserving.id Q)

private theorem measurable_spatialReflect {d : ℕ} :
    Measurable (fun p : Vec d × (Vec d × FieldPair d) => spatialReflect p.1 p.2) :=
  (measurable_fst.sub measurable_snd.fst).prodMk measurable_snd.snd

/-- Reflecting the inner center through the outer center, keeping the outer
center and the environment, preserves `ν.prod (volume.prod Q)`.
Source: `paper/main.tex:913–938`. -/
private theorem measurePreserving_spatialReflect_skew {d : ℕ}
    (ν : Measure (Vec d)) [SFinite ν] (Q : Measure (FieldPair d)) [SFinite Q] :
    MeasurePreserving (fun p : Vec d × (Vec d × FieldPair d) =>
      (p.1, spatialReflect p.1 p.2))
      (ν.prod (volume.prod Q)) (ν.prod (volume.prod Q)) :=
  (MeasurePreserving.id ν).skew_product measurable_spatialReflect
    (Filter.Eventually.of_forall fun x => (measurePreserving_spatialReflect Q x).map_eq)

/-- Translating the inner environment about the inner center, keeping the outer
center, preserves `ν.prod (volume.prod Q)`. Source: `paper/main.tex:913–938`. -/
private theorem measurePreserving_innerCenterTranslate {d : ℕ}
    (ν : Measure (Vec d)) [SFinite ν] (Q : Measure (FieldPair d)) [SFinite Q]
    (hQ : IsStationary Q) :
    MeasurePreserving (Prod.map id (fun z : Vec d × FieldPair d =>
      (z.1, translate z.1 z.2)))
      (ν.prod (volume.prod Q)) (ν.prod (volume.prod Q)) :=
  (MeasurePreserving.id ν).prod (measurePreserving_centerTranslate volume Q hQ)

/-- A spatially centered stationary field is integrable against a finite outer
center law times the Lebesgue-stationary product. Source: `paper/main.tex:913–938`. -/
theorem integrable_centered_stationary_spatial_field {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {F : Vec d × FieldPair d → ℝ} (hF : Integrable F (volume.prod Q)) :
    Integrable (fun p : Vec d × (Vec d × FieldPair d) =>
      F (p.1 - p.2.1, translate p.2.1 p.2.2)) (ν.prod (volume.prod Q)) := by
  have hF' : Integrable (fun z : Vec d × (Vec d × FieldPair d) => F z.2)
      (ν.prod (volume.prod Q)) :=
    hF.comp_snd ν
  have hT := measurePreserving_innerCenterTranslate ν Q hQ
  have hS := measurePreserving_spatialReflect_skew ν Q
  exact (hS.comp hT).integrable_comp_of_integrable hF'

/-- For almost every environment the same centered field is integrable jointly
in its center and spatial argument, with any finite spatial measure.
Source: `paper/main.tex:926–938`. -/
theorem ae_integrable_centered_stationary_spatial_field {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {F : Vec d × FieldPair d → ℝ} (hF : Integrable F (volume.prod Q)) :
    ∀ᵐ ω ∂Q, Integrable (fun z : Vec d × Vec d =>
      F (z.2 - z.1, translate z.1 ω)) (volume.prod ν) := by
  have hi := integrable_centered_stationary_spatial_field Q hQ ν hF
  have ha := (measurePreserving_prodAssoc ν (volume : Measure (Vec d)) Q).integrable_comp_of_integrable hi
  filter_upwards [ha.swap.prod_right_ae] with ω hω
  exact hω.swap

end EinsteinRelation.Correctors
