import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Regeneration.GridStep
import EinsteinRelation.Regeneration.StrictPassageChronology

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Actual passage chronology and grid lower bounds

Source `paper/main.tex:283–322,365–374`. Actual construction definitions remain unchanged.
-/

namespace EinsteinRelation.Regeneration


theorem le_roundUp (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0∞) : t ≤ roundUp Δ t := by
  have h := Regeneration.le_extended_grid_rounding Δ hΔ t
  by_cases ht : t = ⊤
  · simp only [roundUp, if_pos ht]
    exact le_top
  · simpa only [roundUp, if_neg ht] using h

theorem step_le_roundUp (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0∞) (ht : 0 < t) :
    (Δ : ℝ≥0∞) ≤ roundUp Δ t := by
  have h := Regeneration.extended_grid_rounding_ge_step Δ hΔ t ht
  by_cases htop : t = ⊤
  · simp only [roundUp, if_pos htop]
    exact le_top
  · simpa only [roundUp, if_neg htop] using h

theorem firstHittingAbove_pos {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) (ha : 0 < a) :
    0 < firstHittingAbove γ i a := by
  have h := Regeneration.lt_upcrossing_above_coordinate_maximum γ i 0 a ha
  simpa [firstHittingAbove] using h

theorem rounded_passage_lt_next {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (hR : 0 < R) (γ : Path d) (i : Fin d) (n : ℕ)
    (ht : roundUp Δ (passageSequence Δ lam R a γ i n) ≠ ⊤) :
    roundUp Δ (passageSequence Δ lam R a γ i n) <
      passageSequence Δ lam R a γ i (n + 1) := by
  rw [passageSequence, if_neg ht]
  have h := Regeneration.lt_upcrossing_above_coordinate_maximum γ i
    (roundUp Δ (passageSequence Δ lam R a γ i n)).toNNReal R hR
  rw [ENNReal.coe_toNNReal ht] at h
  simpa only [firstHittingAbove, coordinateMaximum] using h

theorem monotone_passageSequence {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (hR : 0 < R) (γ : Path d) (i : Fin d) :
    Monotone (passageSequence Δ lam R a γ i) := by
  apply monotone_nat_of_le_succ
  intro n
  have hle := le_roundUp Δ hΔ (passageSequence Δ lam R a γ i n)
  by_cases ht : roundUp Δ (passageSequence Δ lam R a γ i n) = ⊤
  · rw [passageSequence, if_pos ht]
    exact le_top
  · exact hle.trans (rounded_passage_lt_next Δ lam R a hR γ i n ht).le

theorem step_le_firstRoundedCandidate {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hR : 0 < R) (ha : 0 < a / lam) (γ : Path d) (i : Fin d) :
    (Δ : ℝ≥0∞) ≤ firstRoundedCandidate Δ lam R a γ i := by
  rw [firstRoundedCandidate]
  refine le_iInf fun n => le_iInf fun _hn => ?_
  have h0 : 0 < passageSequence Δ lam R a γ i 0 := by
    simpa only [passageSequence] using firstHittingAbove_pos γ i (a / lam) ha
  have hn : 0 < passageSequence Δ lam R a γ i n :=
    h0.trans_le (monotone_passageSequence Δ hΔ lam R a hR γ i (Nat.zero_le n))
  exact step_le_roundUp Δ hΔ _ hn

theorem step_le_roundedCandidateSequence {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : 0 < lam) (hR : 0 < R) (ha : 0 < a / lam)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    (Δ : ℝ≥0∞) ≤ roundedCandidateSequence Δ lam R a z i n := by
  cases n with
  | zero => exact step_le_firstRoundedCandidate Δ hΔ lam R a hR ha z.1 i
  | succ n =>
      by_cases ht : roundedCandidateSequence Δ lam R a z i n = ⊤
      · rw [roundedCandidateSequence, if_pos ht]
        exact le_top
      · rw [roundedCandidateSequence, if_neg ht]
        have hpos : 0 < (3 * lam * R) / lam :=
          div_pos (mul_pos (mul_pos (by norm_num) hlam) hR) hlam
        have hstep := step_le_firstRoundedCandidate Δ hΔ lam R (3 * lam * R) hR hpos
          (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i
        exact hstep.trans (le_add_of_nonneg_left zero_le)

theorem step_le_firstSuccessfulCandidate {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (hlam : 0 < lam) (hR : 0 < R) (ha : 0 < a / lam)
    (z : CoupledSample d) (i : Fin d) :
    (Δ : ℝ≥0∞) ≤ firstSuccessfulCandidate Δ lam R a z i := by
  rw [firstSuccessfulCandidate]
  exact le_iInf fun n => le_iInf fun _hn =>
    step_le_roundedCandidateSequence Δ hΔ lam R a hlam hR ha z i n

end EinsteinRelation.Regeneration
