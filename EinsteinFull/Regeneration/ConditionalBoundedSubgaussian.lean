import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional Hoeffding bound

A bounded conditionally centered real variable is conditionally sub-Gaussian.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A conditionally centered variable in `[-2,2]` is conditionally sub-Gaussian
with parameter four. -/
theorem bounded_conditional_centered_subgaussian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (Y : Ω → ℝ) (hY : @Measurable Ω ℝ mΩ _ Y)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-2 : ℝ) 2)
    (hmean : μ[Y | m] =ᵐ[μ] (fun _ => 0)) : HasCondSubgaussianMGF m hm Y 4 μ := by
  let : MeasurableSpace Ω := mΩ
  have hInt : Integrable Y μ := Integrable.of_mem_Icc (-2) 2 (hY.aemeasurable : AEMeasurable Y μ) hbound
  have hmeanTrim : μ[Y | m] =ᵐ[μ.trim hm] (fun _ => 0) :=
    (stronglyMeasurable_condExp.ae_eq_trim_iff hm stronglyMeasurable_const).mpr hmean
  have hkernelMean : ∀ᵐ ω ∂μ.trim hm, ∫ y, Y y ∂condExpKernel μ m ω = 0 := by
    filter_upwards [hmeanTrim, condExp_ae_eq_trim_integral_condExpKernel hm hInt] with ω h1 h2
    exact h2.symm.trans h1
  have hkernelBound : ∀ᵐ ω ∂μ.trim hm, ∀ᵐ y ∂condExpKernel μ m ω,
      Y y ∈ Set.Icc (-2 : ℝ) 2 := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hbound
  constructor
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hY.aemeasurable hbound
  · filter_upwards [hkernelMean, hkernelBound] with ω hmeanω hboundω t
    have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hY.aemeasurable hboundω hmeanω
    convert hs.mgf_le t using 1
    norm_num

end EinsteinFull.Regeneration
