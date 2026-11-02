import Mathlib
import EinsteinFull.Calculus.K4AnnularCore

namespace EinsteinFull.Calculus.K7

open EinsteinFull.Calculus.K4

theorem annular_series_shift (d : ℕ) {τ c : ℝ} (hc : 0 < c) (hτ : c ≤ τ) :
    ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * τ) ≤
      Real.exp (-τ / 2) *
        ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * (c / 2)) := by
  have hτpos : 0 < τ := hc.trans_le hτ
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_two_rpow_mul_exp_neg_four_pow d hτpos)
    ((summable_two_rpow_mul_exp_neg_four_pow d (half_pos hc)).mul_left _)
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hexp : Real.exp (-4 ^ n * τ) ≤ Real.exp (-τ / 2) * Real.exp (-4 ^ n * (c / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (by linarith : 0 ≤ τ - c / 2)]
  calc (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * τ)
      ≤ (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
          (Real.exp (-τ / 2) * Real.exp (-4 ^ n * (c / 2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (-τ / 2) *
          ((2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * (c / 2))) := by ring

theorem annular_constant_domination (d : ℕ) {η κ Cloc : ℝ} (hη : 0 < η) (hκ : κ < 1)
    (hCloc : 1 ≤ Cloc) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ z : ℝ, 0 ≤ z → z * Real.sqrt t ≤ t ^ (η / 4) →
      ∀ s : ℝ, 0 < s → ∀ (k Lb : ℕ) (K growth : ℝ), 1 ≤ K → 0 ≤ growth →
        (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) * (t ^ (1 / 2 + η)) ^ d *
            s ^ (-(k : ℝ) / 2) * Real.exp (-(t ^ (2 * η) / Cloc) / 2) ≤
          K * Real.exp (growth * z ^ 2 * t / 2) * t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
            (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ Lb := by
  have hC0 : 0 < Cloc := by linarith
  obtain ⟨T, hT1, hT⟩ := eventually_poly_exp_le (C := 2 * Cloc) (a := 3 / 2 + (d : ℝ) / 4)
    (β := η / 2) (γ := 2 * η) (by linarith) (by linarith) (by linarith)
  refine ⟨T, hT1, fun t ht z hz hzt s hs k Lb K growth hK hg => ?_⟩
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := by linarith
  set a : ℝ := 3 / 2 + (d : ℝ) / 4 with ha
  set r : ℝ := t ^ (1 / 2 + η) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow ht1 (by linarith)
  -- z² t ≤ t^(η/2)
  have hz2 : z ^ 2 * t ≤ t ^ (η / 2) := by
    have h1 : (z * Real.sqrt t) ^ 2 = z ^ 2 * t := by
      rw [mul_pow, Real.sq_sqrt ht0.le]
    have h2 : (t ^ (η / 4)) ^ 2 = t ^ (η / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num; ring_nf
    rw [← h1, ← h2]
    exact pow_le_pow_left₀ (by positivity) hzt 2
  -- main exponential-polynomial bound
  have hP := hT t ht
  have hx : t ^ (2 * η) / (2 * Cloc) = -(-(t ^ (2 * η) / Cloc) / 2) := by ring
  have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht0 _
  have h2C : (2 + t) ^ Cloc ≤ (2 + t) ^ (2 * Cloc) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hB : Real.exp (Cloc * z ^ 2 * t) ≤ Real.exp (2 * Cloc * t ^ (η / 2)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ t ^ (η / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hz2 hC0.le]
  have hkey : (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) *
      Real.exp (-(t ^ (2 * η) / Cloc) / 2) ≤ t ^ (-a) := by
    have hE : Real.exp (-(t ^ (2 * η) / Cloc) / 2) * Real.exp (t ^ (2 * η) / (2 * Cloc)) = 1 := by
      rw [← Real.exp_add, hx]; simp
    have hAB : (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) ≤
        (2 + t) ^ (2 * Cloc) * Real.exp (2 * Cloc * t ^ (η / 2)) :=
      mul_le_mul h2C hB (Real.exp_pos _).le (by positivity)
    have hP' : (2 + t) ^ (2 * Cloc) * Real.exp (2 * Cloc * t ^ (η / 2)) * t ^ a ≤
        Real.exp (t ^ (2 * η) / (2 * Cloc)) := by
      have := hP
      calc _ = (2 + t) ^ (2 * Cloc) * t ^ a * Real.exp (2 * Cloc * t ^ (η / 2)) := by ring
        _ ≤ _ := this
    have hE0 : 0 < Real.exp (-(t ^ (2 * η) / Cloc) / 2) := Real.exp_pos _
    have hnegmul : t ^ (-a) * t ^ a = 1 := by
      rw [← Real.rpow_add ht0]; simp
    calc (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) *
          Real.exp (-(t ^ (2 * η) / Cloc) / 2)
        ≤ (2 + t) ^ (2 * Cloc) * Real.exp (2 * Cloc * t ^ (η / 2)) *
          Real.exp (-(t ^ (2 * η) / Cloc) / 2) := mul_le_mul_of_nonneg_right hAB hE0.le
      _ = t ^ (-a) * ((2 + t) ^ (2 * Cloc) * Real.exp (2 * Cloc * t ^ (η / 2)) * t ^ a) *
          Real.exp (-(t ^ (2 * η) / Cloc) / 2) := by
        rw [← mul_assoc (t ^ (-a)), mul_comm (t ^ (-a)), mul_assoc _ (t ^ (-a)) (t ^ a), hnegmul]
        ring
      _ ≤ t ^ (-a) * Real.exp (t ^ (2 * η) / (2 * Cloc)) *
          Real.exp (-(t ^ (2 * η) / Cloc) / 2) := by
        gcongr
      _ = t ^ (-a) := by linear_combination t ^ (-a) * hE
  -- power comparison
  have hpow : r ^ d ≤ r ^ ((d : ℝ) + 1 - κ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hexp : -1 - (1 / 2 + (d : ℝ) / 4) = -a := by rw [ha]; ring
  rw [hexp]
  have hS : 0 ≤ s ^ (-(k : ℝ) / 2) := by positivity
  have hLb : 1 ≤ (1 + t / s) ^ Lb :=
    one_le_pow₀ (by have : 0 ≤ t / s := by positivity
                    linarith)
  have hG : 1 ≤ Real.exp (growth * z ^ 2 * t / 2) := by
    apply Real.one_le_exp; positivity
  have hRb : 0 ≤ t ^ (-a) * r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) := by positivity
  calc (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) * r ^ d * s ^ (-(k : ℝ) / 2) *
        Real.exp (-(t ^ (2 * η) / Cloc) / 2)
      = ((2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) *
          Real.exp (-(t ^ (2 * η) / Cloc) / 2)) * r ^ d * s ^ (-(k : ℝ) / 2) := by ring
    _ ≤ t ^ (-a) * r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) := by
        gcongr
    _ = 1 * 1 * (t ^ (-a) * r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2)) * 1 := by ring
    _ ≤ K * Real.exp (growth * z ^ 2 * t / 2) *
          (t ^ (-a) * r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2)) * (1 + t / s) ^ Lb := by
        gcongr
    _ = _ := by ring

end EinsteinFull.Calculus.K7
