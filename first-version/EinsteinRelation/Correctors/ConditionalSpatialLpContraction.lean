import EinsteinRelation.Correctors.ConditionalSpatialIntegrability
import EinsteinRelation.Correctors.KernelLpContraction

/-! # Spatial moment contraction for joint conditional versions

Source: `paper/main.tex:913–925,942–947`. A spatially integrated source
moment passes to the joint conditional version. The source need only have
integrable sections almost everywhere in space.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Joint conditional averaging contracts the product-space finite-exponent
seminorm. Source: `paper/main.tex:913–925,942–947`. -/
theorem eLpNorm_conditionalSpatialAverage_product_le {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : Ω → Vec d → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (Function.uncurry u) p (μ.prod ν)) :
    eLpNorm (Function.uncurry (conditionalSpatialAverage m μ u)) p (μ.prod ν) ≤
      eLpNorm (Function.uncurry u) p (μ.prod ν) := by
  have hid : @Measurable (Ω × Vec d) (Ω × Vec d)
      (mΩ.prod inferInstance) (m.prod inferInstance) id :=
    ((measurable_id'' hm).comp measurable_fst).prodMk measurable_snd
  have hvm : StronglyMeasurable
      (Function.uncurry (conditionalSpatialAverage m μ u)) :=
    (stronglyMeasurable_conditionalSpatialAverage m μ u hum).comp_measurable hid
  have hsec : ∀ᵐ x ∂ν,
      eLpNorm (fun ω => conditionalSpatialAverage m μ u ω x) p μ ≤
        eLpNorm (fun ω => u ω x) p μ := by
    filter_upwards [(hu.integrable hp).prod_left_ae] with x hx
    rw [eLpNorm_congr_ae (conditionalSpatialAverage_ae_eq_condExp m μ hm u x hx)]
    have h := @eLpNorm_condExp_comap_le Ω Ω mΩ m μ inferInstance
      id (measurable_id'' hm) p hp hpt (fun ω => u ω x) hx
    simpa only [MeasurableSpace.comap_id] using h
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpower : ∀ᵐ x ∂ν,
      (∫⁻ ω, ‖conditionalSpatialAverage m μ u ω x‖ₑ ^ p.toReal ∂μ) ≤
        ∫⁻ ω, ‖u ω x‖ₑ ^ p.toReal ∂μ := by
    filter_upwards [hsec] with x hx
    have h := ENNReal.rpow_le_rpow hx hpr.le
    rw [eLpNorm_eq_eLpNorm' hp0 hpt, eLpNorm_eq_eLpNorm' hp0 hpt,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr] at h
    exact h
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    lintegral_prod_symm _ (hvm.enorm.pow_const p.toReal).aemeasurable,
    lintegral_prod_symm _ (hum.enorm.pow_const p.toReal).aemeasurable]
  exact ENNReal.rpow_le_rpow (lintegral_mono_ae hpower) (one_div_nonneg.mpr hpr.le)

end EinsteinRelation.Correctors
