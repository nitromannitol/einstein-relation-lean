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

/-- Conditional centering preserves boundedness and gives zero conditional mean. -/
theorem bounded_conditional_centering {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ mΩ _ X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : ℝ) 1) :
    @Measurable Ω ℝ mΩ _ (fun ω => μ[X | m] ω - X ω) ∧
    (∀ᵐ ω ∂μ, μ[X | m] ω - X ω ∈ Set.Icc (-2 : ℝ) 2) ∧
    μ[fun ω => μ[X | m] ω - X ω | m] =ᵐ[μ] (fun _ => 0) := by
  let : MeasurableSpace Ω := mΩ
  have hInt : Integrable X μ := Integrable.of_mem_Icc (-1) 1 hX.aemeasurable hbound
  have hlow : ∀ᵐ ω ∂μ, (-1 : ℝ) ≤ μ[X | m] ω := by
    have h := condExp_mono (m := m) (integrable_const (-1 : ℝ)) hInt
      (hbound.mono fun ω h => h.1)
    filter_upwards [h] with ω hω
    simpa only [condExp_const hm] using hω
  have hhigh : ∀ᵐ ω ∂μ, μ[X | m] ω ≤ (1 : ℝ) := by
    have h := condExp_mono (m := m) hInt (integrable_const (1 : ℝ))
      (hbound.mono fun ω h => h.2)
    filter_upwards [h] with ω hω
    simpa only [condExp_const hm] using hω
  refine ⟨((stronglyMeasurable_condExp.mono hm).measurable.sub hX), ?_, ?_⟩
  · filter_upwards [hbound, hlow, hhigh] with ω hb hl hh
    exact ⟨by linarith [hb.2], by linarith [hb.1]⟩
  · have hsub := condExp_sub (integrable_condExp : Integrable (μ[X | m]) μ) hInt m
    have htower := condExp_condExp_of_le (μ := μ) (f := X) (le_refl m) hm
    filter_upwards [hsub, htower] with ω hs ht
    change μ[(μ[X | m]) - X | m] ω = 0
    rw [hs, Pi.sub_apply, ht, sub_self]

end EinsteinFull.Regeneration
