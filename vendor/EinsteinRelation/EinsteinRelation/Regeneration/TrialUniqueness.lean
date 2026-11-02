import EinsteinRelation.Regeneration.RegenerationGrid

/-! # Uniqueness and deterministic slices of the actual regeneration trial

Source `paper/main.tex:305–322,353–364`. Infinite failure propagates through
all later trial starts. A finite regeneration trial is therefore unique, and the
literal first regeneration time has the expected finite-trial slice characterization.
No chronology, stopping-time or renewal premise is assumed.
-/

open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

private theorem failure_eq_top_of_start_eq_top {d : ℕ} (Δ : ℝ≥0) (R : ℝ)
    (z : CoupledSample d) (i : Fin d) {S : ℝ≥0∞} (hS : S = ⊤) :
    trialFailureTime Δ R z i S = ⊤ := by
  rw [trialFailureTime, trialDownwardTime, if_pos hS, roundUp, if_pos rfl]

/-- Infinite failure at one trial forces every later start to be infinite. -/
theorem trialStartSequence_eq_top_after_infinite_failure {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (n m : ℕ)
    (hfail : trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤)
    (hnm : n < m) : trialStartSequence Δ lam R z i m = ⊤ := by
  have hprop : ∀ k : ℕ, trialStartSequence Δ lam R z i (n + 1 + k) = ⊤ := by
    intro k
    induction k with
    | zero =>
      simp only [add_zero]
      rw [trialStartSequence, if_pos hfail]
    | succ k ih =>
      have hfailure := failure_eq_top_of_start_eq_top Δ R z i ih
      rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 by omega,
        trialStartSequence, if_pos hfailure]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hnm)
  rw [hk]
  exact hprop k

/-- A finite regeneration trial is unique among all actual trial indices. -/
theorem IsRegenerationTrial.unique {d : ℕ} {Δ : ℝ≥0} {lam R : ℝ}
    {z : CoupledSample d} {i : Fin d} {n m : ℕ}
    (hn : IsRegenerationTrial Δ lam R z i n)
    (hm : IsRegenerationTrial Δ lam R z i m) : n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact False.elim (hm.1 (trialStartSequence_eq_top_after_infinite_failure
      Δ lam R z i n m hn.2 hlt))
  · exact heq
  · exact False.elim (hn.1 (trialStartSequence_eq_top_after_infinite_failure
      Δ lam R z i m n hm.2 hgt))

/-- Any actual finite successful trial realizes the literal time infimum. -/
theorem firstRegenerationTime_eq_of_trial {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hn : IsRegenerationTrial Δ lam R z i n) :
    firstRegenerationTime Δ lam R z i = trialStartSequence Δ lam R z i n := by
  apply le_antisymm
  · exact iInf_le_of_le n (iInf_le_of_le hn le_rfl)
  · refine le_iInf fun m => le_iInf fun hm => ?_
    rw [hn.unique hm]

/-- At any fixed finite time the regeneration slice is an actual eligible-trial slice. -/
theorem firstRegenerationTime_eq_iff_trial {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (T : ℝ≥0) :
    firstRegenerationTime Δ lam R z i = (T : ℝ≥0∞) ↔
      ∃ n : ℕ, trialStartSequence Δ lam R z i n = (T : ℝ≥0∞) ∧
        trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤ := by
  constructor
  · intro ht
    have hfin : firstRegenerationTime Δ lam R z i ≠ ⊤ :=
      ht ▸ ENNReal.coe_ne_top
    obtain ⟨n, hn, heq⟩ := firstRegenerationTime_attained Δ hΔ lam R z i hfin
    exact ⟨n, heq.symm.trans ht, hn.2⟩
  · rintro ⟨n, htime, hfail⟩
    have hn : IsRegenerationTrial Δ lam R z i n := ⟨htime ▸ ENNReal.coe_ne_top, hfail⟩
    exact (firstRegenerationTime_eq_of_trial Δ lam R z i n hn).trans htime

end EinsteinRelation.Regeneration
