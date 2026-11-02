import EinsteinRelation.Regeneration.CandidateGrid

/-! # Actual trial and regeneration times lie on the construction grid

Source `paper/main.tex:299–322,353–364`. These are deterministic consequences
of the literal guarded recursion and positive grid spacing. Finite time infima
are attained at eligible trials by the well-ordering of the natural grid.
No stopping-time, tail, renewal or chronology premise is introduced.
-/

open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

private theorem finite_roundUp_grid (Δ : ℝ≥0) (t : ℝ≥0∞)
    (hfin : roundUp Δ t ≠ ⊤) :
    ∃ k : ℕ, roundUp Δ t = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have ht : t ≠ ⊤ := by
    intro h
    apply hfin
    rw [roundUp, if_pos h]
  exact ⟨Nat.ceil (t.toReal / (Δ : ℝ)), by rw [roundUp, if_neg ht]⟩

private theorem add_grid_times (Δ : ℝ≥0) {u v : ℝ≥0∞}
    (hu : ∃ k : ℕ, u = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hv : ∃ k : ℕ, v = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    ∃ k : ℕ, u + v = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨m, hm⟩ := hv
  refine ⟨k + m, ?_⟩
  rw [hk, hm, ← ENNReal.coe_add, Nat.cast_add, add_mul]

/-- A finite actual successful candidate is a grid time. -/
theorem firstSuccessfulCandidate_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstSuccessfulCandidate Δ lam R a z i ≠ ⊤) :
    ∃ k : ℕ, firstSuccessfulCandidate Δ lam R a z i =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨n, hn, heq⟩ := firstSuccessfulCandidate_attained Δ hΔ lam R a z i hfin
  rw [heq]
  exact roundedCandidateSequence_mem_grid Δ hΔ lam R a z i n hn.1

/-- The actual Bernoulli bit at a finite selected successful candidate is one. -/
theorem firstSuccessfulCandidate_bit {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstSuccessfulCandidate Δ lam R a z i ≠ ⊤) :
    z.2 (gridIndex Δ (firstSuccessfulCandidate Δ lam R a z i).toNNReal) = true := by
  obtain ⟨n, hn, heq⟩ := firstSuccessfulCandidate_attained Δ hΔ lam R a z i hfin
  rw [heq]
  exact hn.2

/-- Every finite rounded trial failure lies on the actual grid. -/
theorem trialFailureTime_mem_grid {d : ℕ} (Δ : ℝ≥0) (R : ℝ)
    (z : CoupledSample d) (i : Fin d) (S : ℝ≥0∞)
    (hfin : trialFailureTime Δ R z i S ≠ ⊤) :
    ∃ k : ℕ, trialFailureTime Δ R z i S =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
  finite_roundUp_grid Δ (trialDownwardTime Δ R z i S) hfin

/-- Each finite actual full-trial start is a grid time. -/
theorem trialStartSequence_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : trialStartSequence Δ lam R z i n ≠ ⊤) :
    ∃ k : ℕ, trialStartSequence Δ lam R z i n =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hstep : ∃ k : ℕ, (Δ : ℝ≥0∞) = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
    ⟨1, by simp only [Nat.cast_one, one_mul]⟩
  cases n with
  | zero =>
    have hN : firstSuccessfulCandidate Δ lam R (3 * lam * R) z i ≠ ⊤ := by
      intro h
      apply hfin
      rw [trialStartSequence, h, top_add]
    exact add_grid_times Δ
      (firstSuccessfulCandidate_mem_grid Δ hΔ lam R (3 * lam * R) z i hN) hstep
  | succ n =>
    let t := trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
    have ht : t ≠ ⊤ := by
      intro h
      apply hfin
      change (if t = ⊤ then ⊤ else _) = ⊤
      rw [if_pos h]
    let a := lam * (coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R)
    have hform : trialStartSequence Δ lam R z i (n + 1) =
        t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i + Δ := by
      change (if t = ⊤ then ⊤ else _) = _
      rw [if_neg ht]
    have hN : firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i ≠ ⊤ := by
      intro h
      apply hfin
      rw [hform, h, add_top, top_add]
    rw [hform]
    exact add_grid_times Δ (add_grid_times Δ
      (trialFailureTime_mem_grid Δ R z i _ ht)
      (firstSuccessfulCandidate_mem_grid Δ hΔ lam R a _ i hN)) hstep

private theorem regeneration_grid_inf_attained {Δ : ℝ≥0} (hΔ : 0 < Δ) (e : ℕ → Prop)
    (v : ℕ → ℝ≥0∞)
    (hgrid : ∀ n, e n → ∃ k : ℕ, v n = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hfin : (⨅ (n : ℕ) (_ : e n), v n) ≠ ⊤) :
    ∃ n, e n ∧ (⨅ (n : ℕ) (_ : e n), v n) = v n := by
  have hne : ∃ n, e n := by
    by_contra hnone
    apply hfin
    refine iInf_eq_top.mpr fun n => iInf_eq_top.mpr fun hn => ?_
    exact (hnone ⟨n, hn⟩).elim
  obtain ⟨n₀, hn₀⟩ := hne
  obtain ⟨k₀, hk₀⟩ := hgrid n₀ hn₀
  have hex : ∃ k : ℕ, ∃ n, e n ∧ v n = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
    ⟨k₀, n₀, hn₀, hk₀⟩
  obtain ⟨n, hn, hvn⟩ := Nat.find_spec hex
  refine ⟨n, hn, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le n (iInf_le_of_le hn le_rfl)
  · refine le_iInf fun m => le_iInf fun hm => ?_
    obtain ⟨j, hj⟩ := hgrid m hm
    have hp : ∃ n', e n' ∧ v n' = (((j : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := ⟨m, hm, hj⟩
    have hmin : Nat.find hex ≤ j := Nat.find_min' hex hp
    rw [hvn, hj]
    exact ENNReal.coe_le_coe.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmin) hΔ.le)

/-- A finite actual first regeneration time is attained at a genuine regeneration trial. -/
theorem firstRegenerationTime_attained {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤) :
    ∃ n : ℕ, IsRegenerationTrial Δ lam R z i n ∧
      firstRegenerationTime Δ lam R z i = trialStartSequence Δ lam R z i n := by
  refine regeneration_grid_inf_attained hΔ (IsRegenerationTrial Δ lam R z i)
    (trialStartSequence Δ lam R z i) ?_ hfin
  intro n hn
  exact trialStartSequence_mem_grid Δ hΔ lam R z i n hn.1

/-- The finite first regeneration time belongs to the actual grid. -/
theorem firstRegenerationTime_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤) :
    ∃ k : ℕ, firstRegenerationTime Δ lam R z i =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨n, hn, heq⟩ := firstRegenerationTime_attained Δ hΔ lam R z i hfin
  rw [heq]
  exact trialStartSequence_mem_grid Δ hΔ lam R z i n hn.1

/-- Every finite actual regeneration iterate is a grid time. -/
theorem regenerationTime_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : regenerationTime Δ lam R z i n ≠ ⊤) :
    ∃ k : ℕ, regenerationTime Δ lam R z i n =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  induction n with
  | zero => exact ⟨0, by simp only [regenerationTime, Nat.cast_zero, zero_mul, ENNReal.coe_zero]⟩
  | succ n ih =>
    have ht : regenerationTime Δ lam R z i n ≠ ⊤ := by
      intro h
      apply hfin
      rw [regenerationTime, if_pos h]
    have hstep : firstRegenerationTime Δ lam R
        (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i ≠ ⊤ := by
      intro h
      apply hfin
      rw [regenerationTime, if_neg ht, h, add_top]
    rw [regenerationTime, if_neg ht]
    exact add_grid_times Δ (ih ht)
      (firstRegenerationTime_mem_grid Δ hΔ lam R _ i hstep)

end EinsteinRelation.Regeneration
