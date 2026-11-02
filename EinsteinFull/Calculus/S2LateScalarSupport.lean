import EinsteinFull.Calculus.S2ForcedFluxScale

/-!
# Scalar bookkeeping for the late force replacement

Elementary real-variable facts at `T = R² / 2`, `τ = T^{3/4}`: size of `τ`, the product
`‖ζ‖ √τ` for `ζ = z / R`, the polynomial growth of `log (2 + x)^M`, and the combination of the
exponential factors into the second (`T^{-1/16}`) bound.
-/

namespace EinsteinFull

theorem log_pow_le_rpow (M : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 1 ≤ x → Real.log (2 + x) ^ M ≤ c * x ^ (1 / 32 : ℝ) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow hx (by norm_num)
  · have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (32 * M) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; positivity
    refine ⟨3 * (32 * (M : ℝ)) ^ M, by positivity, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have h2x : 0 ≤ 2 + x := by linarith
    have hl := Real.log_le_rpow_div h2x hδpos
    have hl0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    have e1 : δ * (M : ℝ) = 1 / 32 := by
      rw [hδ]
      field_simp
    have e2 : (δ ^ M)⁻¹ = (32 * (M : ℝ)) ^ M := by
      rw [hδ, one_div, inv_pow, inv_inv]
    have h3 : (3 : ℝ) ^ (1 / 32 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (1 / 32 : ℝ) ≤ 3 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    calc Real.log (2 + x) ^ M ≤ ((2 + x) ^ δ / δ) ^ M := pow_le_pow_left₀ hl0 hl M
      _ = (2 + x) ^ (1 / 32 : ℝ) * (32 * (M : ℝ)) ^ M := by
          rw [div_pow, ← Real.rpow_natCast ((2 + x) ^ δ) M, ← Real.rpow_mul h2x, e1,
            div_eq_mul_inv ((2 + x) ^ (1 / 32 : ℝ)) (δ ^ M), e2]
      _ ≤ (3 * x) ^ (1 / 32 : ℝ) * (32 * (M : ℝ)) ^ M := by
          gcongr
          linarith
      _ = 3 ^ (1 / 32 : ℝ) * x ^ (1 / 32 : ℝ) * (32 * (M : ℝ)) ^ M := by
          rw [Real.mul_rpow (by norm_num) hx0]
      _ ≤ 3 * x ^ (1 / 32 : ℝ) * (32 * (M : ℝ)) ^ M := by
          gcongr
      _ = _ := by ring

theorem tau_facts {T : ℝ} (hT : 16 ≤ T) :
    2 ≤ T ^ (1 - 1 / 4 : ℝ) ∧ T ^ (1 - 1 / 4 : ℝ) ≤ T / 2 := by
  have hTpos : 0 < T := by linarith
  have h34 : T ^ (1 - 1 / 4 : ℝ) = (T ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    norm_num
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hq : 2 ≤ T ^ (1 / 4 : ℝ) := by
    calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := h16.symm
      _ ≤ T ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) hT (by norm_num)
  have hsplit : T = (T ^ (1 / 4 : ℝ)) ^ 3 * T ^ (1 / 4 : ℝ) := by
    rw [← h34, ← Real.rpow_add hTpos]
    norm_num
  rw [h34]
  have hq0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hTpos.le _
  constructor
  · nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq 3]
  · have h3 : 0 ≤ (T ^ (1 / 4 : ℝ)) ^ 3 := pow_nonneg hq0 3
    nlinarith

theorem zeta_sqrt_tau_le {R zn : ℝ} (hR : 0 < R) (hzn : 0 ≤ zn) :
    zn / R * Real.sqrt ((R ^ 2 / 2) ^ (1 - 1 / 4 : ℝ)) ≤ zn * (R ^ 2 / 2) ^ (-(1 / 8) : ℝ) := by
  have hT : 0 < R ^ 2 / 2 := by positivity
  have hsq : Real.sqrt ((R ^ 2 / 2) ^ (1 - 1 / 4 : ℝ)) = (R ^ 2 / 2) ^ (3 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
    norm_num
  have hRT : (R ^ 2 / 2) ^ (1 / 2 : ℝ) ≤ R := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (R ^ 2 / 2) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = R := Real.sqrt_sq hR.le
  have hinv : R⁻¹ ≤ (R ^ 2 / 2) ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hT.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hT _) hRT
  have hexp : (R ^ 2 / 2) ^ (-(1 / 2) : ℝ) * (R ^ 2 / 2) ^ (3 / 8 : ℝ) =
      (R ^ 2 / 2) ^ (-(1 / 8) : ℝ) := by
    rw [← Real.rpow_add hT]
    norm_num
  rw [hsq, div_eq_mul_inv zn R]
  calc zn * R⁻¹ * (R ^ 2 / 2) ^ (3 / 8 : ℝ)
      ≤ zn * (R ^ 2 / 2) ^ (-(1 / 2) : ℝ) * (R ^ 2 / 2) ^ (3 / 8 : ℝ) := by
        gcongr
    _ = _ := by rw [mul_assoc, hexp]

theorem window_small {R zn : ℝ} (hR : 2 ≤ R) (hzn : 0 ≤ zn) (hz : zn ≤ R ^ (1 / 16 : ℝ)) :
    zn / R * Real.sqrt ((R ^ 2 / 2) ^ (1 - 1 / 4 : ℝ)) ≤ 1 := by
  have hR0 : 0 < R := by linarith
  have hT : 0 < R ^ 2 / 2 := by positivity
  have h1 := zeta_sqrt_tau_le hR0 hzn
  have hRT : R ≤ R ^ 2 / 2 := by nlinarith
  have hinv : (R ^ 2 / 2) ^ (-(1 / 8) : ℝ) ≤ R ^ (-(1 / 8) : ℝ) := by
    rw [Real.rpow_neg hT.le, Real.rpow_neg hR0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hR0 _)
      (Real.rpow_le_rpow hR0.le hRT (by norm_num))
  have h2 : R ^ (1 / 16 : ℝ) * R ^ (-(1 / 8) : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hR0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  calc _ ≤ zn * (R ^ 2 / 2) ^ (-(1 / 8) : ℝ) := h1
    _ ≤ R ^ (1 / 16 : ℝ) * R ^ (-(1 / 8) : ℝ) :=
        mul_le_mul hz hinv (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hR0.le _)
    _ ≤ 1 := h2

/-- Combination of the exponential factors into the second bound. -/
theorem scalar_combine {A B c T zn p L : ℝ} {a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hT : 1 ≤ T) (hzn : 0 ≤ zn) (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hpz : p ≤ zn * T ^ (-(1 / 8) : ℝ)) (hLT : L ≤ c * T ^ (1 / 32 : ℝ)) (e : ℝ)
    (he : e = B * (zn ^ 2 / 2)) :
    A * Real.exp e * T ^ (-a) * (p * L) ≤
      A * c * Real.exp ((B + 1) * (1 + zn) ^ 2) * T ^ (-a - 1 / 16) := by
  have hT0 : 0 < T := by linarith
  have h1 : p * L ≤ zn * T ^ (-(1 / 8) : ℝ) * (c * T ^ (1 / 32 : ℝ)) :=
    mul_le_mul hpz hLT hL (mul_nonneg hzn (Real.rpow_nonneg hT0.le _))
  have h2 : T ^ (-(1 / 8) : ℝ) * T ^ (1 / 32 : ℝ) ≤ T ^ (-(1 / 16) : ℝ) := by
    rw [← Real.rpow_add hT0]
    exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h3 : zn ≤ Real.exp ((1 + zn) ^ 2) := by
    refine (le_exp_sq_of_nonneg hzn).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have h4 : Real.exp e ≤ Real.exp (B * (1 + zn) ^ 2) :=
    Real.exp_le_exp.mpr (by
      rw [he]
      nlinarith [mul_nonneg hB (sq_nonneg zn), mul_nonneg hB hzn])
  have h5 : p * L ≤ c * zn * T ^ (-(1 / 16) : ℝ) := by
    calc p * L ≤ zn * T ^ (-(1 / 8) : ℝ) * (c * T ^ (1 / 32 : ℝ)) := h1
      _ = c * zn * (T ^ (-(1 / 8) : ℝ) * T ^ (1 / 32 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc hzn)
  have hTa : T ^ (-a - 1 / 16) = T ^ (-a) * T ^ (-(1 / 16) : ℝ) := by
    rw [show -a - 1 / 16 = -a + -(1 / 16) by ring, Real.rpow_add hT0]
  have hTa0 : 0 ≤ T ^ (-a) := Real.rpow_nonneg hT0.le _
  have hexp : Real.exp (B * (1 + zn) ^ 2) * Real.exp ((1 + zn) ^ 2) =
      Real.exp ((B + 1) * (1 + zn) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc A * Real.exp e * T ^ (-a) * (p * L)
      ≤ A * Real.exp (B * (1 + zn) ^ 2) * T ^ (-a) *
          (c * Real.exp ((1 + zn) ^ 2) * T ^ (-(1 / 16) : ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h4 hA) hTa0) _ (by positivity) (by positivity)
        calc p * L ≤ c * zn * T ^ (-(1 / 16) : ℝ) := h5
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
            exact mul_le_mul_of_nonneg_left h3 hc
    _ = A * c * (Real.exp (B * (1 + zn) ^ 2) * Real.exp ((1 + zn) ^ 2)) *
          (T ^ (-a) * T ^ (-(1 / 16) : ℝ)) := by ring
    _ = _ := by rw [hexp, hTa]

end EinsteinFull
