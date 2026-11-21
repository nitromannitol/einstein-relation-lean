import EinsteinFull.Regeneration.CycleCount
import EinsteinFull.Regeneration.RegenerationCycleDuration

/-!
# Counting actual regeneration cycles

If the literal regeneration times are finite, their positive grid spacing makes their clock
increase to infinity. The completed-cycle count then has the bracket required in the
regeneration velocity argument.
-/

open Filter EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The real clock of the literal sequence of regeneration times. -/
noncomputable def regenerationClock {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ) : ℝ :=
  (regenerationTime Δ lam R z i k).toReal

/-- Finite regeneration times form a clock whose successive values differ by at least `Δ`. -/
theorem regenerationClock_step_ge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ)
    (hfin : regenerationTime Δ lam R z i (k + 1) ≠ ⊤) :
    (Δ : ℝ) ≤ regenerationClock Δ lam R z i (k + 1) - regenerationClock Δ lam R z i k := by
  simpa only [regenerationClock, ENNReal.coe_toNNReal_eq_toReal] using
    regeneration_cycle_duration_ge Δ lam R z i k hfin

/-- If all regeneration times are finite, their real clock is monotone. -/
theorem regenerationClock_monotone {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Monotone (regenerationClock Δ lam R z i) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := regenerationClock_step_ge Δ lam R z i k (hfinite (k + 1))
  have hΔ : 0 ≤ (Δ : ℝ) := Δ.property
  linarith

/-- A finite regeneration clock with positive grid spacing tends to infinity. -/
theorem regenerationClock_tendsto_atTop {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Tendsto (regenerationClock Δ lam R z i) atTop atTop := by
  have hbound (k : ℕ) : (k : ℝ) * (Δ : ℝ) ≤ regenerationClock Δ lam R z i k := by
    induction k with
    | zero => simp [regenerationClock, regenerationTime]
    | succ k ih =>
      have h := regenerationClock_step_ge Δ lam R z i k (hfinite (k + 1))
      push_cast
      nlinarith
  have hΔ' : 0 < (Δ : ℝ) := by exact_mod_cast hΔ
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) * (Δ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const' hΔ'
  exact tendsto_atTop_mono hbound hlim

/-- The number of completed actual regeneration cycles, when every time is finite. -/
noncomputable def regenerationCount {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) (t : ℝ) : ℕ :=
  cycleCount (regenerationClock Δ lam R z i)
    (regenerationClock_tendsto_atTop Δ hΔ lam R z i hfinite) t

/-- The actual regeneration count brackets each nonnegative observation time. -/
theorem regenerationCount_bracket {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) (t : ℝ) (ht : 0 ≤ t) :
    regenerationClock Δ lam R z i (regenerationCount Δ hΔ lam R z i hfinite t) ≤ t ∧
      t < regenerationClock Δ lam R z i (regenerationCount Δ hΔ lam R z i hfinite t + 1) := by
  apply cycleCount_bracket _ _ _ t ht
  simp [regenerationClock, regenerationTime]

/-- The number of completed actual regeneration cycles tends to infinity. -/
theorem regenerationCount_tendsto_atTop {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfinite : ∀ k, regenerationTime Δ lam R z i k ≠ ⊤) :
    Tendsto (regenerationCount Δ hΔ lam R z i hfinite) atTop atTop := by
  exact cycleCount_tendsto_atTop (regenerationClock Δ lam R z i)
    (regenerationClock_tendsto_atTop Δ hΔ lam R z i hfinite)
    (by simp [regenerationClock, regenerationTime])
    (regenerationClock_monotone Δ lam R z i hfinite)

end EinsteinFull.Regeneration
