import EinsteinFull.Calculus.U1RegularKernelContinuity
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

/-!
# Maximum before a downcrossing

A path which rises before a downcrossing must subsequently make a larger
downcrossing from the first time it reaches that rise.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.Blueprint
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A finite downcrossing time witnesses an actual downcrossing. -/
theorem exists_crossing_of_firstHittingBelow_ne_top {d : ℕ} (γ : Path d)
    (i : Fin d) (a : ℝ) (hfin : firstHittingBelow γ i a ≠ ⊤) :
    ∃ t : ℝ≥0, γ t i - γ 0 i ≤ a := by
  by_contra h
  have hn : ∀ t : ℝ≥0, ¬ γ t i - γ 0 i ≤ a := by simpa only [not_exists] using h
  apply hfin
  unfold firstHittingBelow
  simp only [hn, iInf_of_empty, iInf_const]

/-- A maximum before a finite lower crossing forces a deeper crossing after the first rise. -/
theorem shifted_downcrossing_of_maximum {d : ℕ} (γ : Path d) (i : Fin d) (R b : ℝ)
    (hdown : firstHittingBelow γ i (-R) ≠ ⊤)
    (hmax : b < coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal) :
    firstHittingAbove γ i b ≠ ⊤ ∧
      firstHittingBelow (pathTimeShift γ (firstHittingAbove γ i b).toNNReal) i (-(R + b)) ≠ ⊤ := by
  have hex : ∃ s ∈ Set.Icc (0 : ℝ≥0) (firstHittingBelow γ i (-R)).toNNReal,
      b < γ s i - γ 0 i := by
    by_contra hn
    have hle : coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal ≤ b := by
      apply coordinateMaximum_le
      intro s hs
      exact le_of_not_gt (fun h => hn ⟨s, hs, h⟩)
    exact (not_le_of_gt hmax) hle
  obtain ⟨s, hs, hsheight⟩ := hex
  have hupper : firstHittingAbove γ i b ≤ firstHittingBelow γ i (-R) := by
    calc
      _ ≤ (s : ℝ≥0∞) := firstHittingAbove_le_of_crossing γ i b s hsheight.le
      _ ≤ _ := by
        rw [← ENNReal.coe_toNNReal hdown]
        exact_mod_cast hs.2
  have hupfin : firstHittingAbove γ i b ≠ ⊤ := ne_top_of_le_ne_top hdown hupper
  have hheight := ConditionalTrialExhaustion.crossing_at_firstHittingAbove_of_ne_top γ i b hupfin
  obtain ⟨t, ht⟩ := exists_crossing_of_firstHittingBelow_ne_top γ i (-R) hdown
  have htime : (firstHittingAbove γ i b).toNNReal ≤ t := by
    have hh := hupper.trans (firstHittingBelow_le_of_crossing γ i (-R) t ht)
    rw [← ENNReal.coe_toNNReal hupfin, ENNReal.coe_le_coe] at hh
    exact hh
  have hcross : (pathTimeShift γ (firstHittingAbove γ i b).toNNReal)
      (t - (firstHittingAbove γ i b).toNNReal) i -
      (pathTimeShift γ (firstHittingAbove γ i b).toNNReal) 0 i ≤ -(R + b) := by
    simp only [pathTimeShift, ContinuousMap.coe_mk, add_zero, add_tsub_cancel_of_le htime]
    linarith
  exact ⟨hupfin, ne_top_of_le_ne_top ENNReal.coe_ne_top
    (firstHittingBelow_le_of_crossing _ i _ _ hcross)⟩

end EinsteinFull.Regeneration
