import EinsteinRelation.Correctors.ConditionalWeakEquation

/-! # Product integrability of joint conditional averages

The actual conditional spatial versions preserve ordinary product integrability.
Source: `paper/main.tex:913–938`.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- Joint conditional spatial averages of a product-integrable field are
product-integrable. Source: `paper/main.tex:913–938`. -/
theorem integrable_conditionalSpatialAverage_product {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {d : ℕ} (ν : Measure (Vec d)) [SFinite ν] (u : Ω → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hui : Integrable (Function.uncurry u) (μ.prod ν)) :
    Integrable (Function.uncurry (conditionalSpatialAverage m μ u)) (μ.prod ν) := by
  have hid : @Measurable (Ω × Vec d) (Ω × Vec d)
      (mΩ.prod inferInstance) (m.prod inferInstance) id :=
    ((measurable_id'' hm).comp measurable_fst).prodMk measurable_snd
  have hmeas : StronglyMeasurable (Function.uncurry (conditionalSpatialAverage m μ u)) :=
    (stronglyMeasurable_conditionalSpatialAverage m μ u hum).comp_measurable hid
  have hae : AEStronglyMeasurable (Function.uncurry (conditionalSpatialAverage m μ u))
      (μ.prod ν) :=
    hmeas.aestronglyMeasurable
  -- Each spatial section of the joint version is integrable in the observation variable.
  have hsec : ∀ x : Vec d, Integrable (fun a => u a x) μ →
      Integrable (fun ω => conditionalSpatialAverage m μ u ω x) μ := fun x hx =>
    integrable_condExp.congr (conditionalSpatialAverage_ae_eq_condExp m μ hm u x hx).symm
  -- Tower property for fiber averages of integrable functions.
  have htower : ∀ g : Ω → ℝ, Integrable g μ →
      ∫ ω, (∫ a, g a ∂condExpKernel μ m ω) ∂μ = ∫ a, g a ∂μ := by
    intro g hg
    calc ∫ ω, (∫ a, g a ∂condExpKernel μ m ω) ∂μ
        = ∫ ω, (μ[g|m]) ω ∂μ :=
          integral_congr_ae (condExp_ae_eq_integral_condExpKernel hm hg).symm
      _ = ∫ a, g a ∂μ := integral_condExp hm
  -- Norm bound for the conditional average at a fixed spatial point.
  have hbound : ∀ x : Vec d, Integrable (fun a => u a x) μ →
      ∫ ω, ‖conditionalSpatialAverage m μ u ω x‖ ∂μ ≤ ∫ a, ‖u a x‖ ∂μ := by
    intro x hx
    have hxn : Integrable (fun a => ‖u a x‖) μ := hx.norm
    have hfib : Integrable (fun ω => ∫ a, ‖u a x‖ ∂condExpKernel μ m ω) μ :=
      integrable_condExp.congr (condExp_ae_eq_integral_condExpKernel hm hxn)
    have hpt : ∀ ω, ‖conditionalSpatialAverage m μ u ω x‖ ≤
        ∫ a, ‖u a x‖ ∂condExpKernel μ m ω := fun ω =>
      norm_integral_le_integral_norm (fun a => u a x)
    calc ∫ ω, ‖conditionalSpatialAverage m μ u ω x‖ ∂μ
        ≤ ∫ ω, (∫ a, ‖u a x‖ ∂condExpKernel μ m ω) ∂μ :=
          integral_mono (hsec x hx).norm hfib (fun ω => hpt ω)
      _ = ∫ a, ‖u a x‖ ∂μ := htower _ hxn
  -- Joint measurability of the norm, integrated over the observation variable.
  have hnormInt : StronglyMeasurable (fun x : Vec d =>
      ∫ ω, ‖Function.uncurry (conditionalSpatialAverage m μ u) (ω, x)‖ ∂μ) :=
    hmeas.norm.integral_prod_left
  refine (integrable_prod_iff' hae).mpr ⟨?_, ?_⟩
  · filter_upwards [hui.prod_left_ae] with x hx
    exact hsec x hx
  · refine Integrable.mono' hui.integral_norm_prod_right hnormInt.aestronglyMeasurable ?_
    filter_upwards [hui.prod_left_ae] with x hx
    have hx' : Integrable (fun a => u a x) μ := hx
    have hnn : 0 ≤ ∫ ω, ‖conditionalSpatialAverage m μ u ω x‖ ∂μ :=
      integral_nonneg fun ω => norm_nonneg _
    exact (Real.norm_of_nonneg hnn).le.trans (hbound x hx')

end EinsteinRelation.Correctors
