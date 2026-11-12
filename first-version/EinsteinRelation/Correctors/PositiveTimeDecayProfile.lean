import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # Joining bounded initial layers to a power decay profile

Source: `paper/main.tex:842–847`. A single explicit constant joins the
bounded initial layer and the large-time power bound.
-/

namespace EinsteinRelation.Correctors

/-- The bounded initial layer is absorbed into the shifted power profile.
Source: `paper/main.tex:842–847`. -/
theorem le_shifted_power_profile_of_small_time {D C β t : ℝ}
    (hD : 0 ≤ D) (hβ : 0 ≤ β) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    D ≤ (2 ^ β * max D C) * (1+t)^(-β) := by
  have hpow : (2 : ℝ)^(-β) ≤ (1+t)^(-β) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hβ)
  have hmax : 0 ≤ max D C := hD.trans (le_max_left _ _)
  calc
    D ≤ max D C := le_max_left _ _
    _ = ((2 : ℝ)^β * max D C) * (2 : ℝ)^(-β) := by
      rw [Real.rpow_neg (by norm_num), mul_right_comm,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos (by norm_num) β).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hmax)

/-- The large-time power bound is absorbed into the same shifted profile.
Source: `paper/main.tex:842–847`. -/
theorem power_le_shifted_power_profile_of_large_time {D C β t : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 1 ≤ t) :
    C * t^(-β) ≤ (2 ^ β * max D C) * (1+t)^(-β) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hpow : (2*t)^(-β) ≤ (1+t)^(-β) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hβ)
  have hmax : 0 ≤ max D C := hC.trans (le_max_right _ _)
  calc
    C * t^(-β) ≤ max D C * t^(-β) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht0.le _)
    _ = ((2 : ℝ)^β * max D C) * (2*t)^(-β) := by
      have hcancel : (2 : ℝ)^β * (2 : ℝ)^(-β) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          add_neg_cancel, Real.rpow_zero]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0.le]
      calc
        _ = ((2 : ℝ)^β * (2 : ℝ)^(-β)) * (max D C * t^(-β)) := by
          rw [hcancel, one_mul]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hmax)

end EinsteinRelation.Correctors
