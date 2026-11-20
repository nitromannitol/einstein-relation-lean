import EinsteinFull.Regeneration.SlabEnergyRecurrence
import EinsteinFull.Regeneration.SlabEnergyIteration

/-!
# Contradiction from slab cutoff energy estimates

The cutoff-error and initial-energy bounds in Gantert–Mathieu–Piatnitski,
Lemma 4.4, force the final scaled energy below any fixed positive threshold.
-/

namespace EinsteinFull.Regeneration

/-- The source cutoff estimates contradict a reciprocal slab-width lower bound. -/
theorem exists_slab_width_of_gmp_cutoff_bounds (d : ℕ) (hd : 0 < d)
    (A K D c : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K) (hc : 0 < c) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ E T S : ℕ → ℝ,
      (∀ j < 2 * d, 0 ≤ E j ∧ 0 ≤ T j ∧ 0 ≤ S j ∧
        T j ≤ A * Real.exp (-(L / d)) + K * L ^ 2 * E j ∧
        S j ≤ A * Real.exp (-(L / d)) + K * E j ∧
        E (j + 1) ≤ K * A * Real.exp (-(L / d)) +
          K * Real.exp (-(L / d)) ^ 2 * T j +
          2 * K * Real.exp (-(L / d)) * Real.sqrt (T j) * Real.sqrt (S j)) →
      E 0 ≤ D * Real.exp (((2 * d - 1) / d) * L) → L * E (2 * d) < c := by
  let C : ℝ := K * (4 * A + 3 * K + 1)
  have hK0 : 0 ≤ K := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨L₀, hL₀⟩ := exists_slab_width_of_gmp_energy_recurrence d hd C C D c hC hC hc
  refine ⟨max L₀ 1, ?_⟩
  intro L hL E T S hstep hinit
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hε : 0 ≤ Real.exp (-(L / d)) := (Real.exp_pos _).le
  have hε1 : Real.exp (-(L / d)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (div_nonneg (by linarith) hdpos.le)
  apply hL₀ L ((le_max_left _ _).trans hL) E
  · intro j hj
    obtain ⟨hEj, hTj, hSj, hTb, hSb, hNj⟩ := hstep j hj
    have h := slab_energy_recurrence_of_error_bounds A K L (Real.exp (-(L / d)))
      (E j) (T j) (S j) (E (j + 1)) hA hK hL1 hε hε1 hEj hTj hSj hTb hSb hNj
    dsimp [C] at *
    nlinarith
  · exact hinit

/-- The cutoff-error iteration also works for the actual positive force weight. -/
theorem exists_slab_width_of_force_cutoff_bounds (d : ℕ) (hd : 0 < d)
    (s A K D c : ℝ) (hs : 0 < s) (hA : 0 ≤ A) (hK : 1 ≤ K) (hc : 0 < c) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ E T S : ℕ → ℝ,
      (∀ j < 2 * d, 0 ≤ E j ∧ 0 ≤ T j ∧ 0 ≤ S j ∧
        T j ≤ A * Real.exp (-(s * L / d)) + K * L ^ 2 * E j ∧
        S j ≤ A * Real.exp (-(s * L / d)) + K * E j ∧
        E (j + 1) ≤ K * A * Real.exp (-(s * L / d)) +
          K * Real.exp (-(s * L / d)) ^ 2 * T j +
          2 * K * Real.exp (-(s * L / d)) * Real.sqrt (T j) * Real.sqrt (S j)) →
      E 0 ≤ D * Real.exp ((s * (2 * d - 1) / d) * L) → L * E (2 * d) < c := by
  let C : ℝ := K * (4 * A + 3 * K + 1)
  have hK0 : 0 ≤ K := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨L₀, hL₀⟩ :=
    exists_slab_width_of_force_energy_recurrence d hd s C C D c hs hC hC hc
  refine ⟨max L₀ 1, ?_⟩
  intro L hL E T S hstep hinit
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hε : 0 ≤ Real.exp (-(s * L / d)) := (Real.exp_pos _).le
  have hε1 : Real.exp (-(s * L / d)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg hs.le (by linarith)) hdpos.le)
  apply hL₀ L ((le_max_left _ _).trans hL) E
  · intro j hj
    obtain ⟨hEj, hTj, hSj, hTb, hSb, hNj⟩ := hstep j hj
    have h := slab_energy_recurrence_of_error_bounds A K L (Real.exp (-(s * L / d)))
      (E j) (T j) (S j) (E (j + 1)) hA hK hL1 hε hε1 hEj hTj hSj hTb hSb hNj
    dsimp [C] at *
    nlinarith
  · exact hinit

end EinsteinFull.Regeneration
