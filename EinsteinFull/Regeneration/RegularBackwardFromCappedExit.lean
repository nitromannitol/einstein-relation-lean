import EinsteinFull.Regeneration.AdaptedWalkBackwardTail
import EinsteinFull.Regeneration.CappedSlabAllTime
import EinsteinFull.Regeneration.CappedSlabPositiveExit

/-!
# Backward hitting from positive capped exits

A uniform positive capped-exit probability gives the exponential backward
hitting bound for a regular realization.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Positive capped exits give a backward-hitting estimate uniformly over regular laws. -/
theorem backward_hitting_le_of_regular_positive_capped_exit (L : ℝ) (hL : 0 < L) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      ∀ {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
        (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
        (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
        (_hfdd : ∀ I : Finset ℝ≥0,
          K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
            MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
              (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
        (x : Vec d) (i : Fin d) (g : ℝ≥0), 0 < g → 0 < lam →
        (∀ y : Vec d, (3 / 5 : ℝ) ≤ (K y).real
          {γ | cappedSlabIncrement γ i (L / lam) g 0 = 1}) →
        ∀ u : ℝ, K x {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
          ENNReal.ofReal (C * Real.exp (-κ * lam * u)) := by
  obtain ⟨κ, C, hκ, hC, hback⟩ := backward_hitting_le_of_adapted_walk L hL
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro d hd ω lam Λ hΛ hω K hK hfdd x i g hg hlam hpositive u
  have hr : 0 < L / lam := div_pos hL hlam
  apply hback (K x) id i (cappedSlabStoppedFiltration i (L / lam) g)
    (fun j γ => cappedSlabIncrement γ i (L / lam) g j)
  · exact stronglyAdapted_cappedSlabIncrement_stopped i _ _
  · intro j
    exact Filter.Eventually.of_forall fun γ => cappedSlabIncrement_mem_Icc γ i _ hr g j
  · exact initial_slab_mean_of_positive_exit (K x) i _ hr g (hpositive x)
  · intro j
    filter_upwards [condExp_cappedSlabIncrement_regular hd ω lam Λ hΛ hω K hfdd
      x i (L / lam) hr g j] with γ hcond
    rw [hcond]
    exact initial_slab_mean_of_positive_exit (K _) i _ hr g (hpositive _)
  · exact hlam
  · exact Filter.Eventually.of_forall fun γ t =>
      capped_slab_all_time_domination γ i (L / lam) hr g hg t

end EinsteinFull.Regeneration
