import EinsteinFull.Regeneration.RegenerationCount

/-!
# Counting cycles after the first regeneration

The first regeneration interval may have a different law from later cycles. The delayed
clock starts at the first regeneration time and sums the durations of subsequent cycles.
-/

open Filter Finset EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The duration of the `k`-th cycle after the first regeneration. -/
noncomputable def laterCycleDuration {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ) : ℝ :=
  regenerationClock Δ lam R z i (k + 2) - regenerationClock Δ lam R z i (k + 1)

/-- Elapsed time from the first regeneration to a later regeneration. -/
noncomputable def delayedRegenerationClock {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ) : ℝ :=
  regenerationClock Δ lam R z i (k + 1) - regenerationClock Δ lam R z i 1

/-- Later-cycle durations telescope to the delayed regeneration clock. -/
theorem sum_laterCycleDuration {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ) :
    (∑ j ∈ range k, laterCycleDuration Δ lam R z i j) = delayedRegenerationClock Δ lam R z i k := by
  induction k with
  | zero => simp [delayedRegenerationClock]
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [laterCycleDuration, delayedRegenerationClock]
    ring

/-- Finite later regeneration times give the delayed clock positive increments. -/
theorem delayedRegenerationClock_step_ge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ)
    (hfin : regenerationTime Δ lam R z i (k + 2) ≠ ⊤) :
    (Δ : ℝ) ≤ delayedRegenerationClock Δ lam R z i (k + 1) -
      delayedRegenerationClock Δ lam R z i k := by
  have h := regenerationClock_step_ge Δ lam R z i (k + 1) (by simpa [Nat.add_assoc] using hfin)
  dsimp [delayedRegenerationClock]
  linarith

/-- The delayed clock is increasing whenever all regeneration times are finite. -/
theorem delayedRegenerationClock_monotone {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Monotone (delayedRegenerationClock Δ lam R z i) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := delayedRegenerationClock_step_ge Δ lam R z i k (hfinite (k + 2))
  have hΔ : 0 ≤ (Δ : ℝ) := Δ.property
  linarith

/-- The delayed clock diverges whenever all regeneration times are finite and the grid
interval is positive. -/
theorem delayedRegenerationClock_tendsto_atTop {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Tendsto (delayedRegenerationClock Δ lam R z i) atTop atTop := by
  have hbound (k : ℕ) : (k : ℝ) * (Δ : ℝ) ≤ delayedRegenerationClock Δ lam R z i k := by
    induction k with
    | zero => simp [delayedRegenerationClock]
    | succ k ih =>
      have h := delayedRegenerationClock_step_ge Δ lam R z i k (hfinite (k + 2))
      push_cast
      nlinarith
  have hΔ' : 0 < (Δ : ℝ) := by exact_mod_cast hΔ
  exact tendsto_atTop_mono hbound (tendsto_natCast_atTop_atTop.atTop_mul_const' hΔ')

/-- Count completed cycles after the first regeneration, in elapsed time from that moment. -/
noncomputable def laterRegenerationCount {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) (t : ℝ) : ℕ :=
  cycleCount (delayedRegenerationClock Δ lam R z i)
    (delayedRegenerationClock_tendsto_atTop Δ hΔ lam R z i hfinite) t

/-- The delayed count brackets elapsed time by sums of actual later-cycle durations. -/
theorem laterRegenerationCount_bracket {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ range (laterRegenerationCount Δ hΔ lam R z i hfinite t),
      laterCycleDuration Δ lam R z i j) ≤ t ∧
      t < ∑ j ∈ range (laterRegenerationCount Δ hΔ lam R z i hfinite t + 1),
        laterCycleDuration Δ lam R z i j := by
  simp only [sum_laterCycleDuration]
  apply cycleCount_bracket _ _ _ t ht
  simp [delayedRegenerationClock]

/-- The count of completed later cycles tends to infinity. -/
theorem laterRegenerationCount_tendsto_atTop {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Tendsto (laterRegenerationCount Δ hΔ lam R z i hfinite) atTop atTop := by
  exact cycleCount_tendsto_atTop (delayedRegenerationClock Δ lam R z i)
    (delayedRegenerationClock_tendsto_atTop Δ hΔ lam R z i hfinite)
    (by simp [delayedRegenerationClock])
    (delayedRegenerationClock_monotone Δ lam R z i hfinite)

end EinsteinFull.Regeneration
