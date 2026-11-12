import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.TimeMixtures
import Mathlib.MeasureTheory.Integral.Prod

/-! # Equality of stationary fields from their spatial realizations

Source: `paper/main.tex:740–766,948–955`. Spatial almost-everywhere
identification of orbit fields also identifies their values almost surely
under a stationary environment law. Almost-everywhere strong measurability
suffices; no spatial evaluation of a null set at the origin is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Equality of the literal spatial orbits descends to equality under the
stationary law. Source: `paper/main.tex:740–766,948–955`. -/
theorem ae_eq_of_ae_spatial_orbit_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {f g : FieldPair d → ℝ} (hf : AEStronglyMeasurable f Q)
    (hg : AEStronglyMeasurable g Q)
    (hsp : ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate x ω) = g (translate x ω)) : f =ᵐ[Q] g := by
  let T : Vec d × FieldPair d → FieldPair d := fun z => translate z.1 z.2
  have hTm : Measurable T := Probability.continuous_translate.measurable
  have hT : Measure.QuasiMeasurePreserving T (volume.prod Q) Q := by
    refine ⟨hTm, Probability.map_prod_absolutelyContinuous_of_ae_sections volume Q Q T hTm ?_⟩
    apply ae_of_all
    intro x
    change Q.map (translate x) ≪ Q
    simpa only [hQ x] using (Measure.AbsolutelyContinuous.rfl : Q ≪ Q)
  have hT' : Measure.QuasiMeasurePreserving (fun z : FieldPair d × Vec d => translate z.2 z.1)
      (Q.prod volume) Q :=
    hT.comp (Measure.measurePreserving_swap (μ := Q) (ν := volume)).quasiMeasurePreserving
  have hfm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have hgm : Measurable (hg.mk g) := hg.stronglyMeasurable_mk.measurable
  have hfrep := Measure.ae_ae_of_ae_prod (hT'.ae_eq_comp hf.ae_eq_mk)
  have hgrep := Measure.ae_ae_of_ae_prod (hT'.ae_eq_comp hg.ae_eq_mk)
  have hsp' : ∀ᵐ ω ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      hf.mk f (translate x ω) = hg.mk g (translate x ω) := by
    filter_upwards [hsp, hfrep, hgrep] with ω hω hfω hgω
    filter_upwards [hω, hfω, hgω] with x hx hfx hgx
    exact hfx.symm.trans (hx.trans hgx)
  have hmeas : MeasurableSet {z : FieldPair d × Vec d |
      hf.mk f (translate z.2 z.1) = hg.mk g (translate z.2 z.1)} :=
    measurableSet_eq_fun
      (hfm.comp (Probability.continuous_translate.measurable.comp measurable_swap))
      (hgm.comp (Probability.continuous_translate.measurable.comp measurable_swap))
  obtain ⟨x, hx⟩ := ((Measure.ae_ae_comm hmeas).mp hsp').exists
  have hshift : MeasurePreserving (translate (-x)) Q Q :=
    ⟨Probability.measurable_translate (-x), hQ (-x)⟩
  have hback := hshift.quasiMeasurePreserving.ae_eq_comp hx
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk, hback] with ω hωf hωg hω
  simpa only [Function.comp_def, translate_add, add_neg_cancel, translate_zero,
    ← hωf, ← hωg] using hω

end EinsteinRelation.Correctors
