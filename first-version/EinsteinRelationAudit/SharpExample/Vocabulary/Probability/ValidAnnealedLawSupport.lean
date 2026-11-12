import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import EinsteinRelationAudit.SharpExample.Vocabulary.Diffusion.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Regeneration.Coupling

/-! Restated from the library module `EinsteinRelation.Probability.ValidAnnealedLawSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Probability.ValidAnnealedLawSupport
/-- Environments at which the actual kernel fibre is a probability measure. -/
def ProbabilityFiberSet {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : Set α := {a | K a Set.univ = 1}
/-- The kernel is only evaluated on this source-valid domain. -/
abbrev ProbabilityFiber {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) := {a : α // a ∈ ProbabilityFiberSet K}
/-- Restrict the kernel domain to probability fibres; no off-domain value is chosen. -/
def probabilityFiberKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : Kernel (ProbabilityFiber K) β :=
  K.comap Subtype.val measurable_subtype_coe
instance probabilityFiberKernel_markov {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : IsMarkovKernel (probabilityFiberKernel K) := by
  refine ⟨fun a => ⟨?_⟩⟩
  change K a.1 Set.univ = 1
  exact a.2
/-- Form an annealed joint measure by integrating only over the subtype on which
the original kernel is a probability kernel. -/
def annealedJointOnProbabilityFibers {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) (K : Kernel α β)
    (_hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) : Measure (α × β) :=
  ((Q.comap Subtype.val).compProd (probabilityFiberKernel K)).map
    (fun ab => (ab.1.1, ab.2))
end EinsteinRelation.Probability.ValidAnnealedLawSupport
