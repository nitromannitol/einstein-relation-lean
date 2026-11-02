import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- Unbounded coordinate excursions remain unbounded after any finite restart. -/
theorem c2_s3_shifted_unbounded {d : ℕ} (γ : Path d) (i : Fin d)
    (hunbounded : ∀ B : ℝ, ∃ t : ℝ≥0, B ≤ γ t i - γ 0 i)
    (s : ℝ≥0) (B : ℝ) :
    ∃ t : ℝ≥0, B ≤ (pathTimeShift γ s) t i - (pathTimeShift γ s) 0 i := by
  obtain ⟨u, hu⟩ := hunbounded (max (coordinateMaximum γ i s + 1) (B + γ s i - γ 0 i))
  have hsu : s ≤ u := by
    by_contra h
    have hm := displacement_le_coordinateMaximum γ i u s (le_of_not_ge h)
    have hc := (le_max_left (coordinateMaximum γ i s + 1) (B + γ s i - γ 0 i)).trans hu
    linarith
  refine ⟨u - s, ?_⟩
  have hc := (le_max_right (coordinateMaximum γ i s + 1) (B + γ s i - γ 0 i)).trans hu
  simpa only [pathTimeShift, ContinuousMap.coe_mk, add_zero, add_tsub_cancel_of_le hsu] using
    (show B ≤ γ u i - γ s i by linarith)

/-- A crossing of every level makes every recursively selected passage finite. -/
theorem c2_s3_passages_finite_of_unbounded {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (γ : Path d) (i : Fin d)
    (hunbounded : ∀ B : ℝ, ∃ t : ℝ≥0, B ≤ γ t i - γ 0 i) (n : ℕ) :
    passageSequence Δ lam R a γ i n ≠ ⊤ := by
  have hhit : ∀ b : ℝ, firstHittingAbove γ i b ≠ ⊤ := by
    intro b
    obtain ⟨t, ht⟩ := hunbounded b
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (firstHittingAbove_le_of_crossing γ i b t ht)
  induction n with
  | zero => exact hhit (a / lam)
  | succ n ih =>
    rw [passageSequence, ite_eq_right (ConditionalTrialExhaustion.roundUp_ne_top Δ _ ih)]
    exact hhit _

/-- Every passage after a finite restart is finite for a path with unbounded excursions. -/
theorem c2_s3_shifted_passages_finite_of_unbounded
    {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (γ : Path d) (i : Fin d)
    (hunbounded : ∀ B : ℝ, ∃ t : ℝ≥0, B ≤ γ t i - γ 0 i)
    (s : ℝ≥0) (a : ℝ) (n : ℕ) :
    passageSequence Δ lam R a (pathTimeShift γ s) i n ≠ ⊤ :=
  c2_s3_passages_finite_of_unbounded Δ lam R a _ i
    (c2_s3_shifted_unbounded γ i hunbounded s) n

end EinsteinFull.Blueprint
