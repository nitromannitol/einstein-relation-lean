import EinsteinFull.Calculus.S5CoefficientSupport

/-!
# Pointwise forward and transpose energy inequalities

With `ρ = φ²` the square of the weight, `D = ∇ρ` with `|D| ≤ 2qρ`, `X` the gradient and `u`
the value of the solution at a point, the real part of the weak-form integrand tested against
`ρ ū` is bounded by `κ ρ |u|²`, `κ = 5 Λ³ (q² + |ζ|²)`.
-/

open scoped BigOperators

noncomputable section
namespace EinsteinFull

section S5Pointwise

variable {d : ℕ} {A : Fin d → Fin d → ℝ} {Λ : ℝ}

theorem s5_core_ineq {Λ ρ N U β : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) :
    -(Λ⁻¹ / 2 * ρ * N ^ 2) + ρ * (β * U * N) ≤ Λ * β ^ 2 / 2 * ρ * U ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛne : Λ ≠ 0 := hΛ0.ne'
  have key : 0 ≤ Λ⁻¹ * (N - Λ * β * U) ^ 2 :=
    mul_nonneg (inv_nonneg.2 hΛ0.le) (sq_nonneg _)
  have e : Λ⁻¹ * (N - Λ * β * U) ^ 2 =
      Λ⁻¹ * N ^ 2 - 2 * β * U * N + Λ * β ^ 2 * U ^ 2 := by
    field_simp
    ring
  rw [e] at key
  nlinarith [mul_nonneg hρ key]

theorem s5_const_le {Λ q Z : ℝ} (hΛ : 1 ≤ Λ) :
    Λ * (2 * Λ * (q + Z)) ^ 2 / 2 + Λ * (q ^ 2 + Z ^ 2) ≤ 5 * Λ ^ 3 * (q ^ 2 + Z ^ 2) := by
  have hΛ0 : 0 < Λ := by linarith
  have h3 : 0 ≤ Λ ^ 3 := (pow_pos hΛ0 3).le
  have h1 : Λ ≤ Λ ^ 3 := by nlinarith [sq_nonneg (Λ - 1), sq_nonneg Λ]
  have hq : 0 ≤ q ^ 2 + Z ^ 2 := by positivity
  have h2 := mul_nonneg h3 (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (q - Z)))
    hq)
  have h4 := mul_le_mul_of_nonneg_right h1 hq
  nlinarith [h2, h4]

theorem s5_row_eq (h : S5Elliptic A Λ) (i : Fin d) (X : Fin d → ℂ) :
    ∑ j, ∑ k, (((Pi.single i (1 : ℝ) : Fin d → ℝ) j : ℝ) : ℂ) * (A j k : ℂ) * X k =
      ∑ j, (A j i : ℂ) * X j := by
  have e : ∀ j, ∑ k, (((Pi.single i (1 : ℝ) : Fin d → ℝ) j : ℝ) : ℂ) * (A j k : ℂ) * X k =
      if j = i then ∑ k, (A j k : ℂ) * X k else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun k _ => by rw [h.symm i k]

theorem s5Nrm_single (i : Fin d) : s5Nrm (Pi.single i (1 : ℝ) : Fin d → ℝ) = 1 := by
  unfold s5Nrm
  have : ∑ j, ((Pi.single i (1 : ℝ) : Fin d → ℝ) j) ^ 2 = 1 := by
    simp [Pi.single_apply]
  rw [this, Real.sqrt_one]

theorem s5_row_norm_le (h : S5Elliptic A Λ) (i : Fin d) (X : Fin d → ℂ) :
    ‖∑ j, (A j i : ℂ) * X j‖ ≤ 2 * Λ * s5CNrm X := by
  have h1 := s5_cbil_norm_le h (Pi.single i (1 : ℝ)) X
  rw [s5_row_eq h i X, s5Nrm_single, mul_one] at h1
  exact h1

theorem s5_row_real_le (h : S5Elliptic A Λ) (i : Fin d) (D : Fin d → ℝ) :
    |∑ j, D j * A j i| ≤ Λ * s5Nrm D := by
  have h1 := s5Bil_abs_le h D (Pi.single i (1 : ℝ))
  have e : s5Bil A D (Pi.single i (1 : ℝ)) = ∑ j, D j * A j i := by
    simp [s5Bil, Pi.single_apply]
  rw [e, s5Nrm_single, mul_one] at h1
  exact h1

theorem s5CNrm_conj (X : Fin d → ℂ) :
    s5CNrm (fun j => (starRingEnd ℂ) (X j)) = s5CNrm X := by
  unfold s5CNrm
  simp only [Complex.norm_conj]

/-- Complex-number algebra for the forward estimate. -/
theorem s5_alg_forward {Λ N B ρ q : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (hN : 0 ≤ N) (hB : B ≤ 2 * q * ρ) (T1 T2 T3 u ζ : ℂ)
    (h1 : Λ⁻¹ * N ^ 2 ≤ T1.re) (h2 : ‖T2‖ ≤ 2 * Λ * B * N) (h3 : ‖T3‖ ≤ 2 * Λ * N) :
    (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
      ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re ≤
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hΛ0 : 0 < Λ := by linarith
  have c1 : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [c1]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  have hU : 0 ≤ ‖u‖ := norm_nonneg u
  have hZ : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hb2 : -((starRingEnd ℂ) u * T2).re ≤ ‖u‖ * (2 * Λ * B * N) := by
    have := (abs_le.mp (Complex.abs_re_le_norm ((starRingEnd ℂ) u * T2))).1
    rw [norm_mul, Complex.norm_conj] at this
    have h5 : ‖u‖ * ‖T2‖ ≤ ‖u‖ * (2 * Λ * B * N) := mul_le_mul_of_nonneg_left h2 hU
    linarith
  have hb3 : (ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re ≤ ‖ζ‖ * (2 * Λ * N) * ρ * ‖u‖ := by
    have := Complex.re_le_norm (ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ] at this
    have h5 : ‖ζ‖ * (‖T3‖ * ρ * ‖u‖) ≤ ‖ζ‖ * ((2 * Λ * N) * ρ * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hρ) hU) hZ
    nlinarith [h5]
  have P1 : ρ * (Λ⁻¹ * N ^ 2) ≤ ρ * T1.re := mul_le_mul_of_nonneg_left h1 hρ
  have hB' : B * N ≤ (2 * q * ρ) * N := mul_le_mul_of_nonneg_right hB hN
  have P2 : (‖u‖ * (2 * Λ)) * (B * N) ≤ (‖u‖ * (2 * Λ)) * ((2 * q * ρ) * N) :=
    mul_le_mul_of_nonneg_left hB' (by positivity)
  have step : -(1 / 2) * (ρ * T1.re + ((starRingEnd ℂ) u * T2).re) +
      (ζ * (T3 * (ρ : ℂ) * (starRingEnd ℂ) u)).re ≤
      -(Λ⁻¹ / 2 * ρ * N ^ 2) + ρ * ((2 * Λ * (q + ‖ζ‖)) * ‖u‖ * N) := by
    nlinarith [P1, P2, hb2, hb3]
  have core := s5_core_ineq (Λ := Λ) (ρ := ρ) (N := N) (U := ‖u‖) (β := 2 * Λ * (q + ‖ζ‖))
    hΛ hρ
  have hc := s5_const_le (Λ := Λ) (q := q) (Z := ‖ζ‖) hΛ
  have hz : 0 ≤ Λ * (q ^ 2 + ‖ζ‖ ^ 2) := by positivity
  have h6 : Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2 * ρ * ‖u‖ ^ 2 ≤
      (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
    have h7 : 0 ≤ ρ * ‖u‖ ^ 2 := by positivity
    have h8 : Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2 ≤ 5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) := by
      nlinarith [hc, hz]
    calc Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2 * ρ * ‖u‖ ^ 2
        = (Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2) * (ρ * ‖u‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h8 h7
  linarith [step, core, h6]

/-- Complex-number algebra for the transpose estimate. -/
theorem s5_alg_transpose {Λ N B ρ q : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (hN : 0 ≤ N) (hB : B ≤ 2 * q * ρ) (T1 T2 T4 T5 u ζ : ℂ)
    (h1 : Λ⁻¹ * N ^ 2 ≤ T1.re) (h2 : ‖T2‖ ≤ 2 * Λ * B * N) (h4 : ‖T4‖ ≤ 2 * Λ * N)
    (h5 : ‖T5‖ ≤ Λ * B) :
    (-(1 / 2 : ℂ) * ((ρ : ℂ) * T1 + (starRingEnd ℂ) u * T2) +
      ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re ≤
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hΛ0 : 0 < Λ := by linarith
  have c1 : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [c1]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  have hU : 0 ≤ ‖u‖ := norm_nonneg u
  have hZ : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hb2 : -((starRingEnd ℂ) u * T2).re ≤ ‖u‖ * (2 * Λ * B * N) := by
    have := (abs_le.mp (Complex.abs_re_le_norm ((starRingEnd ℂ) u * T2))).1
    rw [norm_mul, Complex.norm_conj] at this
    have h5 : ‖u‖ * ‖T2‖ ≤ ‖u‖ * (2 * Λ * B * N) := mul_le_mul_of_nonneg_left h2 hU
    linarith
  have hb3 : (ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re ≤
      ‖ζ‖ * (‖u‖ * (ρ * (2 * Λ * N) + ‖u‖ * (Λ * B))) := by
    have := Complex.re_le_norm (ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5)))
    rw [norm_mul, norm_mul] at this
    have hs : ‖(ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5‖ ≤ ρ * (2 * Λ * N) + ‖u‖ * (Λ * B) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ]
      exact add_le_add (mul_le_mul_of_nonneg_left h4 hρ) (mul_le_mul_of_nonneg_left h5 hU)
    have h7 : ‖ζ‖ * (‖u‖ * ‖(ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5‖) ≤
        ‖ζ‖ * (‖u‖ * (ρ * (2 * Λ * N) + ‖u‖ * (Λ * B))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hU) hZ
    linarith
  have P1 : ρ * (Λ⁻¹ * N ^ 2) ≤ ρ * T1.re := mul_le_mul_of_nonneg_left h1 hρ
  have hB' : B * N ≤ (2 * q * ρ) * N := mul_le_mul_of_nonneg_right hB hN
  have P2 : (‖u‖ * (2 * Λ)) * (B * N) ≤ (‖u‖ * (2 * Λ)) * ((2 * q * ρ) * N) :=
    mul_le_mul_of_nonneg_left hB' (by positivity)
  have P3 : (‖ζ‖ * ‖u‖ * ‖u‖ * Λ) * B ≤ (‖ζ‖ * ‖u‖ * ‖u‖ * Λ) * (2 * q * ρ) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have step : -(1 / 2) * (ρ * T1.re + ((starRingEnd ℂ) u * T2).re) +
      (ζ * (u * ((ρ : ℂ) * T4 + (starRingEnd ℂ) u * T5))).re ≤
      -(Λ⁻¹ / 2 * ρ * N ^ 2) + ρ * ((2 * Λ * (q + ‖ζ‖)) * ‖u‖ * N) +
        2 * Λ * ‖ζ‖ * q * (ρ * ‖u‖ ^ 2) := by
    nlinarith [P1, P2, P3, hb2, hb3]
  have core := s5_core_ineq (Λ := Λ) (ρ := ρ) (N := N) (U := ‖u‖) (β := 2 * Λ * (q + ‖ζ‖))
    hΛ hρ
  have hc := s5_const_le (Λ := Λ) (q := q) (Z := ‖ζ‖) hΛ
  have h7 : 0 ≤ ρ * ‖u‖ ^ 2 := by positivity
  have hyoung : 2 * Λ * ‖ζ‖ * q ≤ Λ * (q ^ 2 + ‖ζ‖ ^ 2) := by
    nlinarith [mul_nonneg hΛ0.le (sq_nonneg (q - ‖ζ‖))]
  have h8 : Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2 + 2 * Λ * ‖ζ‖ * q ≤
      5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2) := by linarith [hc, hyoung]
  have h9 : (Λ * (2 * Λ * (q + ‖ζ‖)) ^ 2 / 2 + 2 * Λ * ‖ζ‖ * q) * (ρ * ‖u‖ ^ 2) ≤
      (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_right h8 h7
  nlinarith [step, core, h9]

end S5Pointwise

end EinsteinFull
