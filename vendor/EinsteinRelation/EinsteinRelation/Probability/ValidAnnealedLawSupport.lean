import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Regeneration.Coupling
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Probability.ValidAnnealedLawSupport

/-- Environments at which the actual kernel fibre is a probability measure. -/
def ProbabilityFiberSet {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : Set α := {a | K a Set.univ = 1}

theorem measurableSet_probabilityFiberSet {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) : MeasurableSet (ProbabilityFiberSet K) := by
  exact (K.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)

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

theorem probabilityFiberBase_isProbabilityMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (Q : Measure α) [IsProbabilityMeasure Q] (K : Kernel α β)
    (hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) :
    IsProbabilityMeasure (Q.comap (Subtype.val : ProbabilityFiber K → α)) := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_probabilityFiberSet K)).isProbabilityMeasure_comap
  filter_upwards [hK] with a ha
  exact ⟨⟨a, ha.measure_univ⟩, rfl⟩

theorem annealedJointOnProbabilityFibers_lintegral {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (Q : Measure α) [IsProbabilityMeasure Q] (K : Kernel α β)
    (hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) (F : α × β → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ ab, F ab ∂annealedJointOnProbabilityFibers Q K hK =
      ∫⁻ a, ∫⁻ b, F (a, b) ∂K a ∂Q := by
  letI : IsProbabilityMeasure (Q.comap (Subtype.val : ProbabilityFiber K → α)) :=
    probabilityFiberBase_isProbabilityMeasure Q K hK
  have hvalid : ∀ᵐ a ∂Q, a ∈ ProbabilityFiberSet K := by
    filter_upwards [hK] with a ha
    exact ha.measure_univ
  have hmap : Measurable
      (fun ab : ProbabilityFiber K × β => (ab.1.1, ab.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hF' : Measurable
      (fun ab : ProbabilityFiber K × β => F (ab.1.1, ab.2)) := hF.comp hmap
  rw [annealedJointOnProbabilityFibers, lintegral_map hF hmap,
    Measure.lintegral_compProd hF']
  simp only [probabilityFiberKernel, Kernel.comap_apply]
  rw [lintegral_subtype_comap (measurableSet_probabilityFiberSet K)
    (fun a => ∫⁻ b, F (a, b) ∂K a)]
  rw [← lintegral_indicator (measurableSet_probabilityFiberSet K)]
  apply lintegral_congr_ae
  filter_upwards [hvalid] with a ha
  simp [ha]

theorem annealedJointOnProbabilityFibers_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (Q : Measure α) [IsProbabilityMeasure Q]
    (K : Kernel α β) (hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) :
    IsProbabilityMeasure (annealedJointOnProbabilityFibers Q K hK) := by
  letI : IsProbabilityMeasure (Q.comap (Subtype.val : ProbabilityFiber K → α)) :=
    probabilityFiberBase_isProbabilityMeasure Q K hK
  letI : IsProbabilityMeasure
      ((Q.comap (Subtype.val : ProbabilityFiber K → α)).compProd (probabilityFiberKernel K)) := by
    constructor
    rw [Measure.compProd_apply_univ]
    exact measure_univ
  unfold annealedJointOnProbabilityFibers
  infer_instance

end EinsteinRelation.Probability.ValidAnnealedLawSupport
