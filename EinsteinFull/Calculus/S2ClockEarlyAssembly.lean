import EinsteinFull.Calculus.S2ClockEarlySupport

/-!
# Assembly pieces for the last clause of `e:clock-early`

The clock endpoint minus the model endpoint splits into the late-propagation error and the three
propagated errors of the early clock smoothing; the four bounds combine into one with the common
exponent `gain = min (late gain, 1/8)`.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

theorem clock_error_decomposition {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (H : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ)
    (U Hm' w1 w0 m : Lp ℂ 2 (reducedLaw Q)) :
    U - ζ • Hm' = (U - H (ζ • w1)) + ζ • H (w1 - w0) + ζ • H (w0 - m) + ζ • (H m - Hm') := by
  simp only [map_smul, map_sub, smul_sub]
  abel

theorem sqrt_tau_div_le {T τ gain : ℝ} (hT : 1 ≤ T) (hτ : τ = T ^ (1 - (1 / 4 : ℝ)))
    (hg : gain ≤ 1 / 8) : Real.sqrt (τ / T) ≤ T ^ (-gain) := by
  have hT0 : 0 < T := by linarith
  have h1 : τ / T = T ^ (-(1 / 4) : ℝ) := by
    rw [hτ, show -(1 / 4 : ℝ) = (1 - 1 / 4) - 1 by ring,
      Real.rpow_sub hT0 (1 - 1 / 4 : ℝ) 1, Real.rpow_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

theorem tau_div_le {T τ gain : ℝ} (hT : 1 ≤ T) (hτ : τ = T ^ (1 - (1 / 4 : ℝ)))
    (hg : gain ≤ 1 / 8) : τ / T ≤ T ^ (-gain) := by
  have hT0 : 0 < T := by linarith
  have h1 : τ / T = T ^ (-(1 / 4) : ℝ) := by
    rw [hτ, show -(1 / 4 : ℝ) = (1 - 1 / 4) - 1 by ring,
      Real.rpow_sub hT0 (1 - 1 / 4 : ℝ) 1, Real.rpow_one]
  rw [h1]
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

theorem sum_four_scale {T z2 C₂ C₃ C₄ CL a gl gain τ n₂ n₃ n₄ nL : ℝ} (hT : 1 ≤ T)
    (hz : 0 ≤ z2) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hCL : 0 ≤ CL)
    (hτ : τ = T ^ (1 - (1 / 4 : ℝ))) (hgl : gain ≤ gl) (hg8 : gain ≤ 1 / 8)
    (h2 : n₂ ≤ C₂ * Real.exp (C₂ * z2 * T) * T ^ (-a) * Real.sqrt (τ / T))
    (h3 : n₃ ≤ C₃ * Real.exp (C₃ * z2 * T) * T ^ (-a) * Real.sqrt (τ / T))
    (h4 : n₄ ≤ C₄ * Real.exp (C₄ * z2 * T) * T ^ (-a) * (τ / T))
    (hL : nL ≤ CL * Real.exp (CL * z2 * T) * T ^ (-a - gl)) :
    n₂ + n₃ + n₄ + nL ≤ (C₂ + C₃ + C₄ + CL) *
      Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) * T ^ (-a - gain) := by
  have hT0 : 0 < T := by linarith
  have hzT : 0 ≤ z2 * T := mul_nonneg hz hT0.le
  have hP : T ^ (-a - gain) = T ^ (-a) * T ^ (-gain) := by
    rw [show -a - gain = -a + -gain by ring, Real.rpow_add hT0]
  have hTa : 0 ≤ T ^ (-a) := Real.rpow_nonneg hT0.le _
  have hexp : ∀ C : ℝ, 0 ≤ C → C ≤ C₂ + C₃ + C₄ + CL →
      Real.exp (C * z2 * T) ≤ Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) := by
    intro C hC hle
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_right hle hzT]
  have hs2 := sqrt_tau_div_le hT hτ hg8
  have hs4 := tau_div_le hT hτ hg8
  have hs0 : 0 ≤ Real.sqrt (τ / T) := Real.sqrt_nonneg _
  have hτ0 : 0 ≤ τ / T := by rw [hτ]; positivity
  have hLP : T ^ (-a - gl) ≤ T ^ (-a - gain) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have term : ∀ (C n s : ℝ), 0 ≤ C → 0 ≤ s → s ≤ T ^ (-gain) → C ≤ C₂ + C₃ + C₄ + CL →
      n ≤ C * Real.exp (C * z2 * T) * T ^ (-a) * s →
      n ≤ C * Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) * T ^ (-a - gain) := by
    intro C n s hC hs hsg hCle hn
    rw [hP]
    calc n ≤ C * Real.exp (C * z2 * T) * T ^ (-a) * s := hn
      _ ≤ C * Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) * T ^ (-a) * T ^ (-gain) :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hexp C hC hCle) hC) hTa) hsg hs
          (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hTa)
      _ = _ := by ring
  have t2 := term C₂ n₂ _ hC₂ hs0 hs2 (by linarith) h2
  have t3 := term C₃ n₃ _ hC₃ hs0 hs2 (by linarith) h3
  have t4 := term C₄ n₄ _ hC₄ hτ0 hs4 (by linarith) h4
  have tL : nL ≤ CL * Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) * T ^ (-a - gain) := by
    calc nL ≤ CL * Real.exp (CL * z2 * T) * T ^ (-a - gl) := hL
      _ ≤ CL * Real.exp ((C₂ + C₃ + C₄ + CL) * z2 * T) * T ^ (-a - gain) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hexp CL hCL (by linarith)) hCL) hLP
          (Real.rpow_nonneg hT0.le _) (mul_nonneg hCL (Real.exp_pos _).le)
  nlinarith [t2, t3, t4, tL]

end EinsteinFull
