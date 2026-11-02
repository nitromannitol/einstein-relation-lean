import EinsteinRelation.External.GantertSection7Support
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coordinate changes of transition kernels

Source `paper/main.tex:400–402`. A measurable equivalence transports an
actual kernel and its test integrals, including integrals without a
separate integrability assumption.
-/

open MeasureTheory ProbabilityTheory
noncomputable section
namespace EinsteinRelation.Probability

/-- Change both the starting and ending coordinates of a state kernel. -/
def conjugateKernel {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (K : Kernel α α) : Kernel α α :=
  (K.comap e e.measurable).map e.symm

instance conjugateKernel_isMarkovKernel {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (conjugateKernel e K) := by
  exact Kernel.IsMarkovKernel.map _ e.symm.measurable

/-- The transported kernel is the pushforward of the actual source fibre. -/
theorem conjugateKernel_apply {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (K : Kernel α α) (x : α) :
    conjugateKernel e K x = (K (e x)).map e.symm := by
  rw [conjugateKernel, Kernel.map_apply _ e.symm.measurable, Kernel.comap_apply]

/-- All Bochner integrals respect the measurable coordinate equivalence. -/
theorem integral_conjugateKernel {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : α ≃ᵐ α) (K : Kernel α α) (x : α) (f : α → E) :
    (∫ y, f y ∂conjugateKernel e K x) = ∫ y, f (e.symm y) ∂K (e x) := by
  rw [conjugateKernel_apply, integral_map_equiv]


end EinsteinRelation.Probability
