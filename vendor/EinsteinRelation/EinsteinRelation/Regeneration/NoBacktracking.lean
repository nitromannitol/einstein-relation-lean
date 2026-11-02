import EinsteinRelation.Regeneration.TrialUniqueness

/-! # The actual regeneration future does not backtrack

Source `paper/main.tex:305–322,353–364,412–425`. The no-backtracking property
at a finite regeneration time follows from the literal infinite-failure guard.
This is a pathwise construction fact, not a stopping-time or renewal assumption.
-/

open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

private theorem roundUp_eq_top_iff (Δ : ℝ≥0) (t : ℝ≥0∞) :
    roundUp Δ t = ⊤ ↔ t = ⊤ := by
  by_cases ht : t = ⊤
  · rw [roundUp, if_pos ht]
    exact iff_of_true rfl ht
  · rw [roundUp, if_neg ht]
    exact iff_of_false ENNReal.coe_ne_top ht

/-- At a finite full-trial start, infinite failure is exactly the actual shifted D event. -/
theorem trialFailureTime_eq_top_iff_noBacktracking {d : ℕ} (Δ : ℝ≥0) (R : ℝ)
    (z : CoupledSample d) (i : Fin d) (S : ℝ≥0∞) (hS : S ≠ ⊤) :
    trialFailureTime Δ R z i S = ⊤ ↔
      NoBacktracking R (pathTimeShift z.1 S.toNNReal) i := by
  rw [trialFailureTime, roundUp_eq_top_iff, trialDownwardTime, if_neg hS, ENNReal.add_eq_top]
  simp only [hS, false_or, sampleTimeShift, NoBacktracking]

/-- A finite first regeneration time leaves a genuinely nonbacktracking path. -/
theorem firstRegenerationTime_noBacktracking {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤) :
    NoBacktracking R (pathTimeShift z.1 (firstRegenerationTime Δ lam R z i).toNNReal) i := by
  obtain ⟨n, hn, heq⟩ := firstRegenerationTime_attained Δ hΔ lam R z i hfin
  rw [heq]
  exact (trialFailureTime_eq_top_iff_noBacktracking Δ R z i _ hn.1).mp hn.2

private theorem pathTimeShift_add {d : ℕ} (γ : Path d) (s t : ℝ≥0) :
    pathTimeShift (pathTimeShift γ s) t = pathTimeShift γ (s + t) := by
  ext u i
  change γ (s + (t + u)) i = γ ((s + t) + u) i
  rw [add_assoc]

/-- Every finite positive regeneration iterate has the same pathwise D property. -/
theorem regenerationTime_succ_noBacktracking {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : regenerationTime Δ lam R z i (n + 1) ≠ ⊤) :
    NoBacktracking R (pathTimeShift z.1 (regenerationTime Δ lam R z i (n + 1)).toNNReal) i := by
  have ht : regenerationTime Δ lam R z i n ≠ ⊤ := by
    intro h
    apply hfin
    rw [regenerationTime, if_pos h]
  have hlocal : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i ≠ ⊤ := by
    intro h
    apply hfin
    rw [regenerationTime, if_neg ht, h, add_top]
  have hD := firstRegenerationTime_noBacktracking Δ hΔ lam R
    (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i hlocal
  change NoBacktracking R (pathTimeShift
    (pathTimeShift z.1 (regenerationTime Δ lam R z i n).toNNReal)
    (firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i).toNNReal) i at hD
  rw [pathTimeShift_add] at hD
  rw [regenerationTime, if_neg ht, ENNReal.toNNReal_add ht hlocal]
  exact hD

end EinsteinRelation.Regeneration
