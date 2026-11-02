import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Constants and weights for the scalar bootstrap

Explicit inner-fraction absorption, quadratic-exponential domination,
decay-weight comparisons and terminal-window restrictions. These are numerical
prerequisites of the independently reviewed SCALAR-SCOPE-1 closure. They do not
assert any endpoint, locality, semigroup or weak-flux estimate.
-/

namespace EinsteinFull

/-- A moment-dependent inner fraction absorbs the normalized Holder error. -/
theorem inner_smoothing_absorption (a B α : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (hα : 0 < α) :
    let b := min a ((2 * B) ^ (-2 / α))
    0 < b ∧ b ≤ a ∧ B * b ^ (α / 2) ≤ 1 / 2 := by
  dsimp only
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hbase : 0 < 2 * B := mul_pos (by norm_num) hBpos
  have hb : 0 < min a ((2 * B) ^ (-2 / α)) :=
    lt_min ha (Real.rpow_pos_of_pos hbase _)
  refine ⟨hb, min_le_left _ _, ?_⟩
  calc
    B * (min a ((2 * B) ^ (-2 / α))) ^ (α / 2) ≤
        B * (((2 * B) ^ (-2 / α)) ^ (α / 2)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hb.le (min_le_right _ _) (by linarith only [hα])) hBpos.le
    _ = 1 / 2 := by
      rw [← Real.rpow_mul hbase.le]
      have hexponent : (-2 / α) * (α / 2) = (-1 : ℝ) := by
        field_simp
      rw [hexponent, Real.rpow_neg_one]
      field_simp

/-- Shrinking the smoothing time costs the larger of the two decay exponents. -/
theorem scalar_decay_weight_mul_le (b t m h g : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 0 < t) (hm : 0 ≤ m) (hgh : g ≤ h) :
    (b * t) ^ (-h) + m * (b * t) ^ (-g) ≤
      b ^ (-h) * (t ^ (-h) + m * t ^ (-g)) := by
  rw [Real.mul_rpow hb.le ht.le, Real.mul_rpow hb.le ht.le]
  have hpow : b ^ (-g) ≤ b ^ (-h) :=
    Real.rpow_le_rpow_of_exponent_ge hb hb1 (neg_le_neg hgh)
  have hterm := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg hm (Real.rpow_nonneg ht.le (-g)))
  nlinarith only [hterm]

/-- A terminal wide-force window holds at every positive earlier time. -/
theorem scalar_force_window_mono (m t F η : ℝ) (hm : 0 ≤ m) (ht : 0 < t)
    (htF : t ≤ F) (hη : η ≤ 1 / 2)
    (hterminal : m * Real.sqrt F ≤ F ^ η) :
    m * Real.sqrt t ≤ t ^ η := by
  have hF : 0 < F := ht.trans_le htF
  have hnormalized : m * F ^ (1 / 2 - η) ≤ 1 := by
    rw [Real.rpow_sub hF, ← mul_div_assoc, ← Real.sqrt_eq_rpow]
    exact (div_le_one (Real.rpow_pos_of_pos hF η)).2 hterminal
  have hsmall : m * t ^ (1 / 2 - η) ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ht.le htF (sub_nonneg.mpr hη)) hm).trans hnormalized
  rw [Real.rpow_sub ht, ← mul_div_assoc, ← Real.sqrt_eq_rpow] at hsmall
  exact (div_le_one (Real.rpow_pos_of_pos ht η)).1 hsmall

/-- A quadratic exponential absorbs any fixed nonnegative polynomial power. -/
theorem polynomial_mul_gaussian_le (M N D : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hD : 1 ≤ D) :
    (1 + M) ^ N * Real.exp (-D * M ^ 2) ≤ Real.exp (N ^ 2 / 4) := by
  have hpower : (1 + M) ^ N ≤ Real.exp (M * N) := by
    rw [Real.exp_mul]
    apply Real.rpow_le_rpow (by linarith only [hM]) _ hN
    simpa only [add_comm] using Real.add_one_le_exp M
  calc
    (1 + M) ^ N * Real.exp (-D * M ^ 2) ≤
        Real.exp (M * N) * Real.exp (-D * M ^ 2) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ = Real.exp (M * N + -D * M ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (N ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have hterm := mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg M)
      nlinarith only [sq_nonneg (M - N / 2), hterm]

/-- Explicit finite constants absorb the whole normalized Holder prefactor. -/
theorem normalized_holder_absorption (a A N α : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (hN : 0 ≤ N) (hα : 0 < α) :
    let B := max 1 (A * Real.exp (N ^ 2 / 4))
    let b := min a ((2 * B) ^ (-2 / α))
    0 < b ∧ b ≤ a ∧ ∀ M D : ℝ, 0 ≤ M → 1 ≤ D →
      A * b ^ (α / 2) * (1 + M) ^ N * Real.exp (-D * M ^ 2) ≤ 1 / 2 := by
  dsimp only
  obtain ⟨hb, hba, habsorb⟩ := inner_smoothing_absorption a
    (max 1 (A * Real.exp (N ^ 2 / 4))) α ha (le_max_left _ _) hα
  refine ⟨hb, hba, ?_⟩
  intro M D hM hD
  have hp := polynomial_mul_gaussian_le M N D hM hN hD
  have hscale := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hA (Real.rpow_nonneg hb.le (α / 2)))
  have hmax := mul_le_mul_of_nonneg_right
    (le_max_right 1 (A * Real.exp (N ^ 2 / 4)))
    (Real.rpow_nonneg hb.le (α / 2))
  calc
    _ ≤ (A * Real.exp (N ^ 2 / 4)) *
        (min a ((2 * max 1 (A * Real.exp (N ^ 2 / 4))) ^ (-2 / α))) ^ (α / 2) := by
      nlinarith only [hscale]
    _ ≤ 1 / 2 := hmax.trans habsorb

/-- On a bounded parabolic force disc, both decay terms have the faster rate. -/
theorem scalar_decay_weight_le_of_force_bound (d : ℕ) (m t M : ℝ) (ht : 0 < t)
    (hforce : m * Real.sqrt t ≤ M) :
    t ^ (-(1 / 2 + (d : ℝ) / 4)) + m * t ^ (-(d : ℝ) / 4) ≤
      (1 + M) * t ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  have hidentity : Real.sqrt t * t ^ (-(1 / 2 + (d : ℝ) / 4)) =
      t ^ (-(d : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right hforce
    (Real.rpow_nonneg ht.le (-(1 / 2 + (d : ℝ) / 4)))
  rw [mul_assoc, hidentity] at h
  linarith only [h]

/-- A fixed force disc is contained in the wide window beyond an explicit time. -/
theorem scalar_compact_window_subset_wide (m t η : ℝ) (hm : 0 ≤ m) (ht : 4 ≤ t)
    (hη : 0 < η) (hthreshold : (2 : ℝ) ^ (1 / η) ≤ t)
    (hforce : m * Real.sqrt t ≤ 2) :
    m ≤ 1 ∧ m * Real.sqrt t ≤ t ^ η := by
  have hsqrt : 2 ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt ht
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have hpow : 2 ≤ t ^ η := by
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / η)) hthreshold hη.le
    simpa only [one_div, Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hη.ne'] using h
  exact ⟨by nlinarith only [mul_nonneg hm (sub_nonneg.mpr hsqrt), hforce],
    hforce.trans hpow⟩

end EinsteinFull
