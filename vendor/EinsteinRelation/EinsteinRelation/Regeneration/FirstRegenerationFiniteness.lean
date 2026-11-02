import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.RegenerationGrid
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite positive grid support of the first regeneration time

Source `paper/main.tex:323–329,409–411`. The cited exponential tail implies
almost-sure finiteness of the literal first regeneration time. The deterministic
construction then places it on a positive grid slice, justifying coverage by
the countable slices used in the renewal proof.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinRelation.Regeneration

/-- Each trial starts after at least one full grid interval
(`paper/main.tex:305–318`). -/
theorem delta_le_trialStartSequence {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    (Δ : ℝ≥0∞) ≤ trialStartSequence Δ lam R z i n := by
  cases n with
  | zero =>
    rw [trialStartSequence]
    exact le_add_left le_rfl
  | succ n =>
    rw [trialStartSequence]
    split_ifs
    · exact le_top
    · exact le_add_left le_rfl

/-- The infimum defining the first regeneration time is at least one grid
interval (`paper/main.tex:305–318`). -/
theorem delta_le_firstRegenerationTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) :
    (Δ : ℝ≥0∞) ≤ firstRegenerationTime Δ lam R z i := by
  refine le_iInf fun n => le_iInf fun _ => ?_
  exact delta_le_trialStartSequence Δ lam R z i n

/-- The frozen exponential tail forces the actual first regeneration time to
be finite almost surely (`paper/main.tex:323–329,409–411`). -/
theorem firstRegenerationTime_ne_top_ae_of_tail {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d) (Δ : ℝ≥0)
    (lam R c C : ℝ) (hc : 0 < c) (hlam : 0 < lam) (i : Fin d)
    (htail : HasFirstRegenerationTail Q Δ lam R c C i K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤ := by
  have hrate : 0 < c * lam ^ 2 := mul_pos hc (sq_pos_of_pos hlam)
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (C * Real.exp (-t))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  have hmass : annealedCoupledLaw Q K
      {ωz | firstRegenerationTime Δ lam R ωz.2 i = ⊤} ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hsub : {ωz : FieldPair d × CoupledSample d |
        firstRegenerationTime Δ lam R ωz.2 i = ⊤} ⊆
        {ωz | ENNReal.ofReal (t / (c * lam ^ 2)) <
          firstRegenerationTime Δ lam R ωz.2 i} := by
      intro ωz hωz
      rw [Set.mem_setOf_eq] at hωz ⊢
      rw [hωz]
      exact ENNReal.ofReal_lt_top
    have h := (measure_mono hsub).trans
      (htail (t / (c * lam ^ 2)) (div_nonneg ht hrate.le))
    have heq : -c * lam ^ 2 * (t / (c * lam ^ 2)) = -t := by
      field_simp
    rwa [heq] at h
  exact (measure_eq_zero_iff_ae_notMem).mp (bot_unique hmass)

/-- A finite first regeneration time belongs to one of the positive grid
slices used in the renewal sum (`paper/main.tex:353–364,409–411`). -/
theorem firstRegenerationTime_eq_succ_grid_of_ne_top {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤) :
    ∃ m : ℕ, firstRegenerationTime Δ lam R z i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨k, hk⟩ := firstRegenerationTime_mem_grid Δ hΔ lam R z i hfin
  have hk0 : k ≠ 0 := by
    intro h
    have hbound := delta_le_firstRegenerationTime Δ lam R z i
    rw [hk, h, Nat.cast_zero, zero_mul, ENNReal.coe_zero] at hbound
    exact (not_le_of_gt hΔ) (ENNReal.coe_le_coe.mp hbound)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  exact ⟨m, hk⟩

/-- The positive grid slices cover the actual annealed law under the frozen
tail bound (`paper/main.tex:353–364,409–411`). -/
theorem firstRegenerationTime_mem_positive_grid_ae_of_tail {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R c C : ℝ) (hc : 0 < c) (hlam : 0 < lam) (i : Fin d)
    (htail : HasFirstRegenerationTail Q Δ lam R c C i K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∃ m : ℕ,
      firstRegenerationTime Δ lam R ωz.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
  (firstRegenerationTime_ne_top_ae_of_tail Q K Δ lam R c C hc hlam i htail).mono
    fun ωz hfin => firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R ωz.2 i hfin


end EinsteinRelation.Regeneration
