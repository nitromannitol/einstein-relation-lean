import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Restricting a kernel to its probability fibres

The coupled laws in `paper/main.tex:265–279` have separate almost-everywhere
origin and spatial probability qualifiers. A raw kernel need not be globally
s-finite. This restriction preserves every probability fibre and makes the
measure–kernel product available without adding a pointwise source premise.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Probability

/-- Keep exactly probability fibres; all remaining fibres have zero mass. -/
noncomputable def probabilityPart {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : Kernel α β :=
  by
  classical
  exact Kernel.piecewise ((K.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)) K 0

@[simp] theorem probabilityPart_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) (a : α) :
    probabilityPart K a = if K a Set.univ = 1 then K a else 0 := by
  classical
  simp only [probabilityPart, Kernel.piecewise_apply, Set.mem_preimage,
    Set.mem_singleton_iff, Kernel.zero_apply]

instance probabilityPart_isFiniteKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : IsFiniteKernel (probabilityPart K) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
  classical
  rw [probabilityPart_apply]
  split_ifs with h
  · exact h.le
  · simp

/-- The restriction changes no probability measure. -/
theorem probabilityPart_eq_of_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (K : Kernel α β) (a : α)
    [IsProbabilityMeasure (K a)] : probabilityPart K a = K a := by
  rw [probabilityPart_apply, if_pos (measure_univ : K a Set.univ = 1)]

/-- An a.e. probability qualifier is preserved as literal a.e. equality of kernels. -/
theorem probabilityPart_ae_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (K : Kernel α β) (hK : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) :
    probabilityPart K =ᵐ[μ] K := by
  filter_upwards [hK] with a ha
  letI := ha
  exact probabilityPart_eq_of_isProbabilityMeasure K a

/-- The joint law is a probability law under the actual a.e. hypothesis. -/
theorem isProbabilityMeasure_compProd_probabilityPart {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α β) (hK : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) :
    IsProbabilityMeasure (μ.compProd (probabilityPart K)) := by
  constructor
  rw [Measure.compProd_apply MeasurableSet.univ]
  have hae : (fun a => probabilityPart K a (Prod.mk a ⁻¹' Set.univ)) =ᵐ[μ]
      fun _ => (1 : ℝ≥0∞) := by
    filter_upwards [hK] with a ha
    letI := ha
    simp [probabilityPart_eq_of_isProbabilityMeasure K a]
  rw [lintegral_congr_ae hae]
  simp

/-- Bounded joint observations have their genuine iterated quenched integral. -/
theorem integral_compProd_probabilityPart {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α β) (hK : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (f : α × β → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ z, |f z| ≤ C) :
    (∫ z, f z ∂μ.compProd (probabilityPart K)) =
      ∫ a, ∫ b, f (a, b) ∂K a ∂μ := by
  letI := isProbabilityMeasure_compProd_probabilityPart μ K hK
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable f (μ.compProd (probabilityPart K)) := by
    refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hC z
  rw [Measure.integral_compProd hint]
  apply integral_congr_ae
  filter_upwards [probabilityPart_ae_eq μ K hK] with a ha
  rw [ha]

end EinsteinRelation.Probability
