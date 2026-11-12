import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Restated from the library module `EinsteinRelation.Probability.ProbabilityPart`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

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
end EinsteinRelation.Probability
