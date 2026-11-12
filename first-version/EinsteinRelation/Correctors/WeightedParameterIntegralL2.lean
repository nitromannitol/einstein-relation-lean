import EinsteinRelation.Correctors.IntegralCauchySquare
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- An integrable positive parameter weight turns a weighted product L²
bound into L² regularity of the parameter integral. Source:
`paper/main.tex:787–792,850`; integration of kernel solutions. -/
theorem memLp_two_integral_of_weighted_product
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [SFinite μ] (ν : Measure X) [IsFiniteMeasure ν]
    {w : Ω → ℝ} (hwm : Measurable w) (hw : Integrable w μ)
    (hwp : ∀ ω, 0 < w ω) {f : Ω × X → ℝ}
    (hfm : Measurable f)
    (hf : MemLp (fun z => f z / Real.sqrt (w z.1)) 2 (μ.prod ν)) :
    MemLp (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ∧ Integrable f (μ.prod ν) := by
  let g : Ω × X → ℝ := fun z => f z / Real.sqrt (w z.1)
  have hs : MemLp (fun ω => Real.sqrt (w ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hwm.sqrt.aestronglyMeasurable).mpr
    simpa only [Real.sq_sqrt (hwp _).le] using hw
  have hcancel (z : Ω × X) : g z * Real.sqrt (w z.1) = f z :=
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr (hwp z.1)).ne'
  have hfi : Integrable f (μ.prod ν) :=
    (hf.integrable_mul (hs.comp_fst ν)).congr (ae_of_all _ hcancel)
  refine ⟨?_,hfi⟩
  have havm : AEStronglyMeasurable (fun x => ∫ ω, f (ω,x) ∂μ) ν :=
    hfm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq havm).mpr
  have hsq := hf.integrable_sq
  have hb : Integrable (fun x => (∫ ω, w ω ∂μ) * (∫ ω, g (ω,x)^2 ∂μ)) ν :=
    hsq.integral_prod_right.const_mul _
  apply hb.mono' (havm.pow 2)
  filter_upwards [hsq.prod_left_ae] with x hx
  have hgx : MemLp (fun ω => g (ω,x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq ?_).mpr hx
    exact ((hfm.comp measurable_prodMk_right).div hwm.sqrt).aestronglyMeasurable
  have hc := integral_mul_sq_le_integral_sq_mul_integral_sq μ hgx hs
  have heq : (fun ω => g (ω,x)*Real.sqrt (w ω)) = fun ω => f (ω,x) :=
    funext fun ω => hcancel (ω,x)
  rw [heq] at hc
  simp only [Real.sq_sqrt (hwp _).le] at hc
  simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_sq,mul_comm] using hc

end EinsteinRelation.Correctors
