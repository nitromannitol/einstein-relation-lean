import EinsteinRelation.Regeneration.Chronology

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Lower bounds for the actual regeneration times

Source `paper/main.tex:283–322,489–493`. The trial recursion itself proves
`τ_k ≥ 2kΔ`, retaining infinity and empty eligible infima.
-/

namespace EinsteinRelation.Regeneration

/-- The base level `3 λ R` is positive after division by `λ`. -/
private theorem three_lam_R_div_pos (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) :
    0 < (3 * lam * R) / lam :=
  div_pos (mul_pos (mul_pos (by norm_num) hlam) hR) hlam

/-- From any starting time, one successor trial adds at least `2Δ`. The next level
`λ (M(t) - (γ_t - γ_0) + R)` has positive ratio `/λ`, since the finite coordinate
maximum dominates the displacement at the same time. -/
private theorem two_mul_le_trial_succ {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d) (t : ℝ≥0∞) :
    (2 : ℝ≥0∞) * (Δ : ℝ≥0∞) ≤ t +
      firstSuccessfulCandidate Δ lam R
        (lam * (coordinateMaximum z.1 i t.toNNReal - (z.1 t.toNNReal i - z.1 0 i) + R))
        (sampleTimeShift Δ z t.toNNReal) i + (Δ : ℝ≥0∞) := by
  have hdisp : z.1 t.toNNReal i - z.1 0 i ≤ coordinateMaximum z.1 i t.toNNReal :=
    displacement_le_coordinateMaximum z.1 i t.toNNReal t.toNNReal le_rfl
  have hpos : 0 < lam * (coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R) / lam := by
    rw [mul_div_cancel_left₀ _ hlam.ne']
    linarith
  have hstep := step_le_firstSuccessfulCandidate Δ hΔ lam R _ hlam hR hpos
    (sampleTimeShift Δ z t.toNNReal) i
  rw [two_mul]
  refine le_trans (add_le_add hstep le_rfl) ?_
  exact add_le_add (le_add_of_nonneg_left zero_le) le_rfl

/-- Every actual trial start is at least `2Δ`, including the infinite branch. -/
theorem two_step_le_trialStartSequence {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    (2 : ℝ≥0∞) * (Δ : ℝ≥0∞) ≤ trialStartSequence Δ lam R z i n := by
  cases n with
  | zero =>
      rw [trialStartSequence, two_mul]
      exact add_le_add (step_le_firstSuccessfulCandidate Δ hΔ lam R (3 * lam * R)
        hlam hR (three_lam_R_div_pos lam R hlam hR) z i) le_rfl
  | succ n =>
      by_cases ht : trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) = ⊤
      · rw [trialStartSequence, if_pos ht]
        exact le_top
      · rw [trialStartSequence, if_neg ht]
        exact two_mul_le_trial_succ Δ hΔ lam R hlam hR z i
          (trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n))

/-- The first regeneration time is at least `2Δ`, by its infimum over eligible
trial indices. No nonemptiness premise is needed: an empty infimum is infinite. -/
theorem two_step_le_firstRegenerationTime {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d) :
    (2 : ℝ≥0∞) * (Δ : ℝ≥0∞) ≤ firstRegenerationTime Δ lam R z i := by
  rw [firstRegenerationTime]
  exact le_iInf fun n => le_iInf fun _ =>
    two_step_le_trialStartSequence Δ hΔ lam R hlam hR z i n

/-- Each iterate of the regeneration times advances by at least `2Δ`. -/
theorem nat_two_step_le_regenerationTime {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    (n : ℝ≥0∞) * ((2 : ℝ≥0∞) * (Δ : ℝ≥0∞)) ≤ regenerationTime Δ lam R z i n := by
  induction n with
  | zero => simp [regenerationTime]
  | succ n ih =>
      by_cases ht : regenerationTime Δ lam R z i n = ⊤
      · rw [regenerationTime, if_pos ht]
        exact le_top
      · rw [regenerationTime, if_neg ht]
        have hcast : ((n + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) * (Δ : ℝ≥0∞)) =
            (n : ℝ≥0∞) * ((2 : ℝ≥0∞) * (Δ : ℝ≥0∞)) + (2 : ℝ≥0∞) * (Δ : ℝ≥0∞) := by
          rw [Nat.cast_add_one, add_mul, one_mul]
        rw [hcast]
        exact add_le_add ih (two_step_le_firstRegenerationTime Δ hΔ lam R hlam hR
          (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i)

end EinsteinRelation.Regeneration
