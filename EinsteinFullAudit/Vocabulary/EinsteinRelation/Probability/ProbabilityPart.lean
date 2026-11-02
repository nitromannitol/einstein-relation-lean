import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Vocabulary for `EinsteinRelation.Probability.ProbabilityPart`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

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

end EinsteinRelation.Probability
