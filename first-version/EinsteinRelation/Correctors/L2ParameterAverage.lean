import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import EinsteinRelation.Correctors.KernelLpContraction
import EinsteinRelation.Correctors.ProbabilityAverageL2

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Averaging over a probability parameter contracts the scalar L² norm.
Source: `paper/main.tex:802`; temporal regularization in AKM Lemma 8.2. -/
theorem memLp_two_parameter_average {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {f : Ω × X → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ∧
      eLpNorm (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ≤ eLpNorm f 2 (μ.prod ν) := by
  have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  rcases hf with ⟨hf_meas, hf_fin⟩
  have h_ae : ∀ᵐ x ∂ν, AEStronglyMeasurable (fun ω => f (ω,x)) μ :=
    hf_meas.prodMk_right
  have h_meas : AEStronglyMeasurable (fun x => ∫ ω, f (ω,x) ∂μ) ν :=
    hf_meas.prod_swap.integral_prod_right'
  have h_bound_sq : eLpNorm (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ^ 2 ≤ eLpNorm f 2 (μ.prod ν) ^ 2 := by
    rw [eLpNorm_two_sq, eLpNorm_two_sq (μ := μ.prod ν)]
    have hj : ∀ᵐ x ∂ν, ‖(∫ ω, f (ω,x) ∂μ)‖ₑ ^ 2 ≤ ∫⁻ ω, ‖f (ω,x)‖ₑ ^ 2 ∂μ := by
      filter_upwards [h_ae] with x hx
      have h1 : ‖(∫ ω, f (ω,x) ∂μ)‖ₑ ≤ eLpNorm (fun ω => f (ω,x)) 2 μ :=
        enorm_integral_le_eLpNorm hp hx
      have h2 : eLpNorm (fun ω => f (ω,x)) 2 μ ^ 2 = ∫⁻ ω, ‖f (ω,x)‖ₑ ^ 2 ∂μ :=
        eLpNorm_two_sq _ _
      calc
        ‖(∫ ω, f (ω,x) ∂μ)‖ₑ ^ 2 ≤ (eLpNorm (fun ω => f (ω,x)) 2 μ) ^ 2 :=
          pow_le_pow_left' h1 2
        _ = ∫⁻ ω, ‖f (ω,x)‖ₑ ^ 2 ∂μ := by rw [h2]
    calc
      ∫⁻ x, ‖(∫ ω, f (ω,x) ∂μ)‖ₑ ^ 2 ∂ν ≤ ∫⁻ x, (∫⁻ ω, ‖f (ω,x)‖ₑ ^ 2 ∂μ) ∂ν :=
        lintegral_mono_ae hj
      _ = ∫⁻ ω, (∫⁻ x, ‖f (ω,x)‖ₑ ^ 2 ∂ν) ∂μ := by
        rw [lintegral_lintegral_swap (hf_meas.prod_swap.enorm.pow_const 2)]
      _ = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(μ.prod ν) := by
        rw [← lintegral_prod _ (hf_meas.enorm.pow_const 2)]
  have h_bound : eLpNorm (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ≤ eLpNorm f 2 (μ.prod ν) :=
    (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp h_bound_sq
  have h_fin : eLpNorm (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν < ∞ :=
    h_bound.trans_lt hf_fin
  exact ⟨⟨h_meas, h_fin⟩, h_bound⟩

end EinsteinRelation.Correctors
