import EinsteinRelation.Probability.FiniteHistoryBarrier

/-!
# Bounded history factors retaining the actual spatial barrier

Source `paper/main.tex:377–381`. A constrained next-history test can be
factored into the exact past and last interval with both barrier
constraints retained on every pair. This is the form needed for the
one-interval locality induction.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Probability

/-- The bounded joint factor can be chosen to vanish unless both of
its histories remain in the prescribed closed spatial set. -/
theorem exists_supported_splitHistory_factor {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (V : Set (Vec d)) (hV : IsClosed V)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → z ∈ historyStays Δ (n + 1) V) :
    ∃ G : CoupledSample d × CoupledSample d → ℝ,
      Measurable G ∧ BoundedRealTest G ∧ (∀ z, F z = G (splitHistory Δ n z)) ∧
      ∀ p, G p ≠ 0 → p.1 ∈ historyStays Δ n V ∧ p.2 ∈ historyStays Δ 1 V := by
  obtain ⟨G, hG, ⟨C, hbG⟩, heq⟩ := exists_bounded_splitHistory_factor Δ hΔ n F hF hb
  let B : Set (CoupledSample d × CoupledSample d) :=
    (historyStays Δ n V) ×ˢ (historyStays Δ 1 V)
  have hB : MeasurableSet B :=
    (isClosed_historyStays Δ n V hV).measurableSet.prod
      (isClosed_historyStays Δ 1 V hV).measurableSet
  refine ⟨B.indicator G, hG.indicator hB, ⟨max C 0, fun p => ?_⟩, ?_, ?_⟩
  · by_cases hp : p ∈ B
    · simpa only [Set.indicator_of_mem hp] using (hbG p).trans (le_max_left C 0)
    · simpa only [Set.indicator_of_notMem hp, abs_zero] using le_max_right C 0
  · intro z
    by_cases hz : z ∈ historyStays Δ (n + 1) V
    · have hsplit := (mem_historyStays_succ_iff Δ n V z).mp hz
      have hp : splitHistory Δ n z ∈ B :=
        ⟨(stoppedHistorySample_mem_historyStays_iff Δ n V z).mpr hsplit.1,
          (stoppedHistorySample_mem_historyStays_iff Δ 1 V _).mpr hsplit.2⟩
      rw [Set.indicator_of_mem hp, heq]
    · have hFzero : F z = 0 := by by_contra hn; exact hz (hsupport z hn)
      have hp : splitHistory Δ n z ∉ B := by
        intro hpair
        apply hz
        exact (mem_historyStays_succ_iff Δ n V z).mpr
          ⟨(stoppedHistorySample_mem_historyStays_iff Δ n V z).mp hpair.1,
            (stoppedHistorySample_mem_historyStays_iff Δ 1 V _).mp hpair.2⟩
      rw [hFzero, Set.indicator_of_notMem hp]
  · intro p hn
    have hp : p ∈ B := by
      by_contra hp
      exact hn (Set.indicator_of_notMem hp G)
    exact hp


end EinsteinRelation.Probability
