import EinsteinFull.Regeneration.SplitSegmentSequence
import EinsteinFull.Regeneration.TrajectoryShift

/-!
# The actual split sequence after a deterministic sampled prefix

The entire future sequence, including all its coins, is sampled by the same
literal sequence kernel at the last segment's endpoint and retained environment.
The joint law below retains the complete earlier segment prefix.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

variable {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

/-- Read the actual last endpoint and environment from a sampled prefix. -/
def splitPrefixEndpoint {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (u : (j : Finset.Iic n) → SplitSegmentState d) : Vec d × FieldPair d :=
  ((u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1 Δ,
    (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)

theorem measurable_splitPrefixEndpoint {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (splitPrefixEndpoint (d := d) Δ n) :=
  (((continuous_eval_const Δ).measurable.comp (measurable_pi_apply _).snd.fst).prodMk
    (measurable_pi_apply _).fst)

/-- The whole future of the canonical extension starts at the literal endpoint.
No restart assumption for an original or glued process occurs in this identity. -/
theorem map_splitSegmentExtensionKernel_shift (n : ℕ) :
    (splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n).map
        (sequenceShift (n + 1)) =
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).comap
        (splitPrefixEndpoint Δ n) (measurable_splitPrefixEndpoint Δ n) := by
  letI := isMarkovKernel_splitInitialStateKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  letI := isMarkovKernel_splitSegmentStepKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  ext u : 1
  rw [Kernel.map_apply _ (measurable_sequenceShift _), Kernel.comap_apply]
  change (Kernel.traj (X := fun _ : ℕ => SplitSegmentState d)
      (homogeneousHistoryKernel (splitSegmentStepKernel Δ δ R i hδ₀ hR P hminor)) n u).map
      (sequenceShift (n + 1)) = _
  rw [trajectory_shift]
  unfold seededTrajectory splitSegmentSequenceKernel splitSegmentExtensionKernel
    splitSegmentInitialPrefixKernel
  rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.map_apply _ (by fun_prop),
    Kernel.map_apply _ (by fun_prop)]
  rfl

/-- The full sampled past and the entire shifted future have the exact
endpoint-conditioned joint law, retaining every path/coin correlation. -/
theorem splitSegmentSequenceKernel_prefix_future_joint (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s => (frestrictLe n s, sequenceShift (n + 1) s)) =
      (Kernel.id ×ₖ (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).comap
        (splitPrefixEndpoint Δ n) (measurable_splitPrefixEndpoint Δ n)) ∘ₖ
        (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
          (frestrictLe n) := by
  letI : IsMarkovKernel (splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n) := by
    unfold splitSegmentExtensionKernel
    infer_instance
  have h := congrArg (fun κ => κ.map (Prod.map id (sequenceShift (n + 1))))
    (splitSegmentSequenceKernel_prefix_joint Δ δ R i hδ₀ hδ₁ hR P hminor n)
  rw [Kernel.map_comp, ← Kernel.map_prod_map _ _ measurable_id (measurable_sequenceShift _),
    Kernel.map_id, map_splitSegmentExtensionKernel_shift] at h
  rw [← Kernel.map_comp_right _ (by fun_prop)
    (measurable_id.prodMap (measurable_sequenceShift _))] at h
  exact h.symm

end EinsteinFull.Regeneration
