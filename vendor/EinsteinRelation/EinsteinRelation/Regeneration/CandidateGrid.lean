import EinsteinRelation.Probability.FutureFieldDecoder
import EinsteinRelation.Regeneration.Geometry
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-! # Literal candidate grid slices

Source `paper/main.tex:283–321,353–370`. Finite first rounded candidates and the
rounded candidate sequence are integer multiples of the grid step `Δ`; the first
successful candidate is attained at an eligible index of least grid position.
-/

namespace EinsteinRelation.Regeneration

/-- A finite first rounded candidate is an integer multiple of the grid step.
Attainment selects an eligible passage, and the literal ceiling in `roundUp`
supplies the integer. -/
theorem firstRoundedCandidate_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (γ : Path d) (i : Fin d) (hfin : firstRoundedCandidate Δ lam R a γ i ≠ ⊤) :
    ∃ k : ℕ, firstRoundedCandidate Δ lam R a γ i =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  have hex : ∃ n, IsGoodPassage Δ lam R a γ i n := by
    by_contra hnone
    apply hfin
    rw [firstRoundedCandidate]
    refine iInf_eq_top.mpr fun n => iInf_eq_top.mpr fun hn => ?_
    exact (hnone ⟨n, hn⟩).elim
  obtain ⟨n, hn, hrep⟩ := firstRoundedCandidate_attained Δ hΔ lam R a γ i hex
  have hnfin : passageSequence Δ lam R a γ i n ≠ ⊤ := hn.1
  refine ⟨Nat.ceil ((passageSequence Δ lam R a γ i n).toReal / (Δ : ℝ)), ?_⟩
  rw [hrep, roundUp, if_neg hnfin]

/-- Every finite term of the rounded candidate sequence is an integer multiple of
the grid step. A finite successor forces both summands to be finite, and a sum of
two grid multiples is again a grid multiple. -/
theorem roundedCandidateSequence_mem_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : roundedCandidateSequence Δ lam R a z i n ≠ ⊤) :
    ∃ k : ℕ, roundedCandidateSequence Δ lam R a z i n =
      (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  induction n with
  | zero => exact firstRoundedCandidate_mem_grid Δ hΔ lam R a z.1 i hfin
  | succ n ih =>
    have hprev : roundedCandidateSequence Δ lam R a z i n ≠ ⊤ := by
      intro ht
      apply hfin
      rw [roundedCandidateSequence, if_pos ht]
    obtain ⟨k, hk⟩ := ih hprev
    have hstep : firstRoundedCandidate Δ lam R (3 * lam * R)
        (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i ≠ ⊤ := by
      intro htop
      apply hfin
      rw [roundedCandidateSequence, if_neg hprev, htop, add_top]
    obtain ⟨m, hm⟩ := firstRoundedCandidate_mem_grid Δ hΔ lam R (3 * lam * R)
      (pathTimeShift z.1 (roundedCandidateSequence Δ lam R a z i n).toNNReal) i hstep
    refine ⟨k + m, ?_⟩
    rw [roundedCandidateSequence, if_neg hprev, hm, hk, ← ENNReal.coe_add, ← add_mul,
      Nat.cast_add]

/-- Attainment for an infimum over eligible grid-valued candidates. The eligible
indices need not be monotone, so the minimal grid position is chosen by `Nat.find`. -/
private theorem iInf_eq_attained_of_grid {Δ : ℝ≥0} (hΔ : 0 < Δ) (e : ℕ → Prop)
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

/-- A finite first successful candidate is attained by a successful rounded
candidate in the sequence. -/
theorem firstSuccessfulCandidate_attained {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d)
    (hfin : firstSuccessfulCandidate Δ lam R a z i ≠ ⊤) :
    ∃ n : ℕ, IsSuccessfulCandidate Δ lam R a z i n ∧
      firstSuccessfulCandidate Δ lam R a z i = roundedCandidateSequence Δ lam R a z i n := by
  refine iInf_eq_attained_of_grid hΔ (IsSuccessfulCandidate Δ lam R a z i)
    (roundedCandidateSequence Δ lam R a z i) ?_ hfin
  intro n hn
  exact roundedCandidateSequence_mem_grid Δ hΔ lam R a z i n hn.1

end EinsteinRelation.Regeneration
