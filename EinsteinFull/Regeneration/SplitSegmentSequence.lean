import EinsteinFull.Regeneration.OneIntervalSplitKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Iterating the canonical split segments

The state records the unchanged environment and the last sampled path/coin.
The next segment starts at the last segment's endpoint. Ionescu–Tulcea gives
one joint kernel on infinite segment sequences, with the exact finite-prefix
laws and deterministic-prefix restart. Gluing these segments into a continuous
path, identifying that path law, and stopped locality are separate obligations.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- An actual sampled path/coin together with its environment. -/
abbrev SplitSegmentState (d : ℕ) := FieldPair d × (Path d × Bool)

variable {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

include hδ₁

/-- Sample the canonical first segment while retaining its actual environment. -/
def splitInitialStateKernel {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hδ₀ : 0 < δ) (hR : 0 < R)
    (P : QuenchedPathLaws d) [IsMarkovKernel P]
    (hminor : ∀ ω : FieldPair d,
      EinsteinFull.External.Source.GMP.HasSourceMinorization
        (fun x => P (x, ω)) Δ δ R i) :
    Kernel (Vec d × FieldPair d) (SplitSegmentState d) :=
  (Kernel.deterministic Prod.snd measurable_snd) ×ₖ
    oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor

/-- The retained environment and first segment form a probability kernel. -/
theorem isMarkovKernel_splitInitialStateKernel :
    IsMarkovKernel (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor) := by
  letI := isMarkovKernel_oneIntervalSplitKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  unfold splitInitialStateKernel
  infer_instance

/-- Advance by the canonical split law from the previous segment's endpoint.
The environment is copied, not resampled. -/
def splitSegmentStepKernel : Kernel (SplitSegmentState d) (SplitSegmentState d) :=
  (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).comap
    (fun s => (s.2.1 Δ, s.1))
    ((((continuous_eval_const Δ).measurable).comp measurable_snd.fst).prodMk measurable_fst)

/-- Each endpoint transition is a probability kernel. -/
theorem isMarkovKernel_splitSegmentStepKernel :
    IsMarkovKernel (splitSegmentStepKernel Δ δ R i hδ₀ hR P hminor) := by
  letI := isMarkovKernel_splitInitialStateKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  unfold splitSegmentStepKernel
  infer_instance

/-- The consecutive kernels read the last actual sampled segment of the prefix. -/
def splitSegmentHistoryKernel (n : ℕ) :
    Kernel ((j : Finset.Iic n) → SplitSegmentState d) (SplitSegmentState d) :=
  (splitSegmentStepKernel Δ δ R i hδ₀ hR P hminor).comap
    (fun s : (j : Finset.Iic n) → SplitSegmentState d => s ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n))

/-- Every consecutive history transition is a probability kernel. -/
theorem isMarkovKernel_splitSegmentHistoryKernel (n : ℕ) :
    IsMarkovKernel (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n) := by
  letI := isMarkovKernel_splitSegmentStepKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  unfold splitSegmentHistoryKernel
  infer_instance

/-- The time-zero prefix consists exactly of the sampled initial state. -/
def splitSegmentInitialPrefixKernel :
    Kernel (Vec d × FieldPair d) ((j : Finset.Iic 0) → SplitSegmentState d) :=
  (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map (fun s _ => s)

/-- The initial singleton prefix has probability one. -/
theorem isMarkovKernel_splitSegmentInitialPrefixKernel :
    IsMarkovKernel (splitSegmentInitialPrefixKernel Δ δ R i hδ₀ hR P hminor) := by
  letI := isMarkovKernel_splitInitialStateKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  unfold splitSegmentInitialPrefixKernel
  exact Kernel.IsMarkovKernel.map _ (Measurable.of_eval (fun _ => measurable_id))

/-- The canonical Ionescu–Tulcea extension of an actual finite prefix. -/
def splitSegmentExtensionKernel (n : ℕ) :
    Kernel ((j : Finset.Iic n) → SplitSegmentState d) (ℕ → SplitSegmentState d) :=
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  Kernel.traj (X := fun _ : ℕ => SplitSegmentState d)
    (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor) n

/-- The joint infinite sequence obtained by iterating the literal split kernel. -/
def splitSegmentSequenceKernel :
    Kernel (Vec d × FieldPair d) (ℕ → SplitSegmentState d) :=
  splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor 0 ∘ₖ
    splitSegmentInitialPrefixKernel Δ δ R i hδ₀ hR P hminor

instance isMarkovKernel_splitSegmentSequenceKernel :
    IsMarkovKernel (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor) := by
  letI := isMarkovKernel_splitSegmentInitialPrefixKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  unfold splitSegmentSequenceKernel splitSegmentExtensionKernel
  infer_instance

/-- Every finite prefix has exactly the consecutive composition law. -/
theorem map_splitSegmentSequenceKernel_prefix (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      (frestrictLe n) =
    Kernel.partialTraj (X := fun _ : ℕ => SplitSegmentState d)
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor) 0 n ∘ₖ
      splitSegmentInitialPrefixKernel Δ δ R i hδ₀ hR P hminor := by
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  rw [splitSegmentSequenceKernel, splitSegmentExtensionKernel, Kernel.map_comp,
    Kernel.traj_map_frestrictLe]

/-- The same joint infinite law restarts after any deterministic finite prefix.
This is a statement about the segment sequence; continuous-path restart still
requires the gluing and path-law identification. -/
theorem splitSegmentSequenceKernel_restart (n : ℕ) :
    splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n ∘ₖ
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) =
    splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor := by
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  rw [map_splitSegmentSequenceKernel_prefix, ← Kernel.comp_assoc,
    splitSegmentExtensionKernel,
    Kernel.traj_comp_partialTraj (Nat.zero_le n)]
  rfl

/-- Its initial state is the canonical first segment with the environment. -/
theorem map_splitSegmentSequenceKernel_zero :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (fun s => s 0) =
      splitInitialStateKernel Δ δ R i hδ₀ hR P hminor := by
  have hz : (fun s : ℕ → SplitSegmentState d => s 0) =
      (fun s : (j : Finset.Iic 0) → SplitSegmentState d => s ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0 := rfl
  rw [hz, Kernel.map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),
    map_splitSegmentSequenceKernel_prefix, Kernel.partialTraj_self, Kernel.id_comp,
    splitSegmentInitialPrefixKernel, ← Kernel.map_comp_right]
  · exact Kernel.map_id _
  · exact Measurable.of_eval (fun _ => measurable_id)
  · exact measurable_pi_apply _

/-- Forgetting the environment in the initial sample gives exactly the
canonical joint path/first-coin law, including its correlations. -/
theorem map_splitSegmentSequenceKernel_first :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      (fun s => (s 0).2) =
      oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor := by
  letI := isMarkovKernel_oneIntervalSplitKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  change (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
    (Prod.snd ∘ (fun s => s 0)) = _
  rw [Kernel.map_comp_right _ (measurable_pi_apply (0 : ℕ)) measurable_snd,
    map_splitSegmentSequenceKernel_zero, splitInitialStateKernel, ← Kernel.snd_eq,
    Kernel.snd_prod]

/-- The finite prefix and the entire sequence have exactly the joint law
obtained by sampling that prefix and then its canonical infinite extension. -/
theorem splitSegmentSequenceKernel_prefix_joint (n : ℕ) :
    (Kernel.id ×ₖ splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n) ∘ₖ
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) =
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
      (fun s => (frestrictLe n s, s)) := by
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  let κ := splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor
  have hjoint : (Kernel.id ×ₖ Kernel.traj (X := fun _ : ℕ => SplitSegmentState d) κ n) ∘ₖ
      Kernel.partialTraj (X := fun _ : ℕ => SplitSegmentState d) κ 0 n =
      (Kernel.traj (X := fun _ : ℕ => SplitSegmentState d) κ 0).map
        (fun s => (frestrictLe n s, s)) := by
    ext u A hA
    rw [Kernel.comp_apply' _ _ _ hA, Kernel.map_apply' _ (by fun_prop) _ hA]
    have h := congrArg (fun μ => μ A) (Kernel.partialTraj_compProd_traj
      (X := fun _ : ℕ => SplitSegmentState d) (κ := κ) (Nat.zero_le n) u)
    rw [Measure.compProd_apply hA, Measure.map_apply (by fun_prop) hA] at h
    rw [← h]
    apply lintegral_congr
    intro v
    rw [Kernel.prod_apply' _ _ _ hA, Kernel.id_apply,
      lintegral_dirac' _ (measurable_measure_prodMk_left hA)]
  rw [map_splitSegmentSequenceKernel_prefix, ← Kernel.comp_assoc,
    splitSegmentExtensionKernel,
    hjoint, ← Kernel.map_comp]
  rfl

/-- The initial state retains exactly the input environment. -/
theorem map_splitInitialStateKernel_environment :
    (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map Prod.fst =
      Kernel.deterministic Prod.snd measurable_snd := by
  letI := isMarkovKernel_oneIntervalSplitKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  rw [splitInitialStateKernel, ← Kernel.fst_eq, Kernel.fst_prod]

/-- Every step retains exactly its input environment. -/
theorem map_splitSegmentStepKernel_environment :
    (splitSegmentStepKernel Δ δ R i hδ₀ hR P hminor).map Prod.fst =
      Kernel.deterministic Prod.fst measurable_fst := by
  ext s : 1
  rw [Kernel.map_apply _ measurable_fst, splitSegmentStepKernel, Kernel.comap_apply,
    ← Kernel.map_apply _ measurable_fst,
    map_splitInitialStateKernel_environment (hδ₁ := hδ₁),
    Kernel.deterministic_apply, Kernel.deterministic_apply]

end EinsteinFull.Regeneration
