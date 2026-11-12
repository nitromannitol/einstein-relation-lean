import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Literal representatives of L2-valued integrals

Source: `paper/main.tex:1021–1029`. Testing on measurable sets identifies
the Bochner integral with the ordinary pointwise parameter integral.
-/

open MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
namespace EinsteinRelation

/-- A jointly integrable representative commutes with an `L²` Bochner
integral, as an almost-everywhere identity (`paper/main.tex:1021–1029`). -/
theorem ae_coe_L2_integral {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure S} [SFinite ν]
    {G : S → Lp ℝ 2 μ} (hG : Integrable G ν)
    {F : S × Ω → ℝ} (hF : Integrable F (ν.prod μ))
    (heq : ∀ᵐ z ∂ν, (G z : Ω → ℝ) =ᵐ[μ] fun ω => F (z, ω)) :
    (fun ω => (∫ z, G z ∂ν : Lp ℝ 2 μ) ω) =ᵐ[μ] fun ω => ∫ z, F (z, ω) ∂ν := by
  let Y : Lp ℝ 2 μ := ∫ z, G z ∂ν
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp Y).integrable one_le_two) hF.integral_prod_right
  intro s hs hμs
  have hFs : Integrable F (ν.prod (μ.restrict s)) := by
    have hi : Integrable F ((ν.restrict Set.univ).prod (μ.restrict s)) := by
      rw [Measure.prod_restrict]
      exact hF.integrableOn
    simpa only [Measure.restrict_univ] using hi
  calc
    (∫ ω in s, Y ω ∂μ) = inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) Y :=
      (L2.inner_indicatorConstLp_one hs hμs.ne Y).symm
    _ = ∫ z, inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) (G z) ∂ν :=
      (integral_inner hG _).symm
    _ = ∫ z, (∫ ω in s, F (z, ω) ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      rw [L2.inner_indicatorConstLp_one hs hμs.ne]
      exact integral_congr_ae (ae_restrict_of_ae hz)
    _ = ∫ ω in s, (∫ z, F (z, ω) ∂ν) ∂μ := integral_integral_swap hFs

end EinsteinRelation
