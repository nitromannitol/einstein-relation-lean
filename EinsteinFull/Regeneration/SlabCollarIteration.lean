import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Iteration over shrinking slab collars

A uniform energy bound on an outer slab lets a contracting collar estimate
be iterated through infinitely many nested slabs.
-/

open Filter
open scoped Topology

namespace EinsteinFull.Regeneration

/-- A contracting collar recurrence with geometrically growing error is
controlled by its geometric series when the outer energies are bounded. -/
theorem energy_le_of_collar_recurrence (E : ℕ → ℝ) (C b q M : ℝ)
    (hC : 0 ≤ C) (hb : 1 ≤ b) (hq : 0 ≤ q) (hqb : q * b < 1)
    (hbound : ∀ k, E k ≤ M)
    (hstep : ∀ k, E k ≤ C * b ^ k + q * E (k + 1)) :
    E 0 ≤ C / (1 - q * b) := by
  let K := C / (1 - q * b)
  have hb0 : 0 ≤ b := by linarith
  have hden : 0 < 1 - q * b := by linarith
  have hK : 0 ≤ K := div_nonneg hC hden.le
  have hK_eq : C + q * K * b = K := by
    dsimp [K]
    field_simp
    <;> ring
  have hq1 : q < 1 := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hb)]
  have hiter : ∀ n k, E k ≤ K * b ^ k + q ^ n * M := by
    intro n
    induction n with
    | zero =>
        intro k
        have hk : 0 ≤ K * b ^ k := mul_nonneg hK (pow_nonneg hb0 k)
        simp only [pow_zero, one_mul]
        linarith [hbound k]
    | succ n ih =>
        intro k
        have hh := mul_le_mul_of_nonneg_left (ih (k + 1)) hq
        have hs := hstep k
        rw [pow_succ] at hh
        rw [pow_succ]
        have heq : C * b ^ k + q * (K * (b ^ k * b) + q ^ n * M) =
            K * b ^ k + (q ^ n * q) * M := by
          calc
            _ = (C + q * K * b) * b ^ k + (q ^ n * q) * M := by ring
            _ = _ := by rw [hK_eq]
        linarith
  have ht : Tendsto (fun n : ℕ => K * b ^ 0 + q ^ n * M) atTop (𝓝 K) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const M)
  exact ge_of_tendsto' ht (fun n => hiter n 0)

end EinsteinFull.Regeneration
