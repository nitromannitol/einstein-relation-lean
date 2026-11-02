import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.RegenerationGrid

/-! # Actual last successful bit at a regeneration trial start

Source `paper/main.tex:305–322,353–364`. A finite actual full-trial start equal to
`(m+1)Δ` closes the grid slice whose selected successful bit sits at index `m`.
The argument is deterministic: the successful-candidate bit at the selected grid
index is read through `sampleTimeShift`, and the positive grid spacing is
cancelled. No positivity of `lam` or `R` and no coupling or freshness premise is
used, and the actual bit value is never assumed.
-/

open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- Cancel a positive grid spacing between two grid multiples. -/
private theorem grid_nat_eq_of_mul_eq {Δ : ℝ≥0} (hΔ : 0 < Δ) {p q : ℕ}
    (h : (p : ℝ≥0) * Δ = (q : ℝ≥0) * Δ) : p = q := by
  have hpq : (p : ℝ≥0) = (q : ℝ≥0) := mul_right_cancel₀ hΔ.ne' h
  exact_mod_cast hpq

/-- The time-shifted bit sequence reads the original bits from the grid index onward. -/
private theorem sampleTimeShift_apply_bit {d : ℕ} (Δ : ℝ≥0) (z : CoupledSample d)
    (t : ℝ≥0) (n : ℕ) : (sampleTimeShift Δ z t).2 n = z.2 (gridIndex Δ t + n) := rfl

/-- Source trial starts: a finite start `(m+1)Δ` has the actual original bit `m` true. -/
theorem trialStartSequence_last_bit {d : ℕ} (Δ : ℝ≥0) (_hΔ : 0 < Δ) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (n m : ℕ)
    (_hstart : trialStartSequence Δ lam R z i n = ((((m+1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    (z.2 m = true : Prop) := by
  cases n with
  | zero =>
    rw [trialStartSequence] at _hstart
    have hN : firstSuccessfulCandidate Δ lam R (3 * lam * R) z i ≠ ⊤ := by
      intro h
      rw [h, top_add] at _hstart
      exact ENNReal.coe_ne_top _hstart.symm
    obtain ⟨k, hk⟩ := firstSuccessfulCandidate_mem_grid Δ _hΔ lam R (3 * lam * R) z i hN
    have hbit := firstSuccessfulCandidate_bit Δ _hΔ lam R (3 * lam * R) z i hN
    rw [hk, ENNReal.toNNReal_coe, gridIndex_mul Δ _hΔ k] at hbit
    rw [hk, ← ENNReal.coe_add, ENNReal.coe_inj] at _hstart
    have hkm : ((k + 1 : ℕ) : ℝ≥0) * Δ = ((m + 1 : ℕ) : ℝ≥0) * Δ := by
      rw [← _hstart]
      push_cast
      ring
    have hkm' : k + 1 = m + 1 := grid_nat_eq_of_mul_eq _hΔ hkm
    have hkm2 : k = m := by omega
    rw [hkm2] at hbit
    exact hbit
  | succ n =>
    let t := trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n)
    have ht : t ≠ ⊤ := by
      intro h
      have hTop : trialStartSequence Δ lam R z i (n + 1) = ⊤ := by
        change (if t = ⊤ then ⊤ else _) = ⊤
        rw [if_pos h]
      rw [_hstart] at hTop
      exact ENNReal.coe_ne_top hTop
    let a := lam * (coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R)
    have hform : trialStartSequence Δ lam R z i (n + 1) =
        t + firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i + Δ := by
      change (if t = ⊤ then ⊤ else _) = _
      rw [if_neg ht]
    have hsum := hform.symm.trans _hstart
    have hN : firstSuccessfulCandidate Δ lam R a (sampleTimeShift Δ z t.toNNReal) i ≠ ⊤ := by
      intro h
      rw [h, add_top, top_add] at hsum
      exact ENNReal.coe_ne_top hsum.symm
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t = (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
      trialFailureTime_mem_grid Δ R z i (trialStartSequence Δ lam R z i n) ht
    obtain ⟨j, hj⟩ := firstSuccessfulCandidate_mem_grid Δ _hΔ lam R a
      (sampleTimeShift Δ z t.toNNReal) i hN
    have hbit := firstSuccessfulCandidate_bit Δ _hΔ lam R a
      (sampleTimeShift Δ z t.toNNReal) i hN
    rw [hj, ENNReal.toNNReal_coe, gridIndex_mul Δ _hΔ j, sampleTimeShift_apply_bit, hk,
      ENNReal.toNNReal_coe, gridIndex_mul Δ _hΔ k] at hbit
    rw [hj, hk, ← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_inj] at hsum
    have hkj : ((k + j + 1 : ℕ) : ℝ≥0) * Δ = ((m + 1 : ℕ) : ℝ≥0) * Δ := by
      rw [← hsum]
      push_cast
      ring
    have hkj' : k + j + 1 = m + 1 := grid_nat_eq_of_mul_eq _hΔ hkj
    have hkjm : k + j = m := by omega
    rw [hkjm] at hbit
    exact hbit

/-- Source first regeneration time: a finite first time `(m+1)Δ` has the actual original
bit `m` true, because it is attained at a genuine trial start on the same grid time. -/
theorem firstRegenerationTime_last_bit {d : ℕ} (Δ : ℝ≥0) (_hΔ : 0 < Δ) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (m : ℕ)
    (_htime : firstRegenerationTime Δ lam R z i = ((((m+1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    (z.2 m = true : Prop) := by
  have hfin : firstRegenerationTime Δ lam R z i ≠ ⊤ := by
    rw [_htime]
    exact ENNReal.coe_ne_top
  obtain ⟨n, _, heq⟩ := firstRegenerationTime_attained Δ _hΔ lam R z i hfin
  exact trialStartSequence_last_bit Δ _hΔ lam R z i n m (heq.symm.trans _htime)

end EinsteinRelation.Regeneration
