import EinsteinFull.Calculus.S2ForcedFluxBound

/-!
# Parabolic scaling of the flux propagator bound

The bound of `S2ForcedFluxBound` is stated at the propagation time `s`; for `T / 2 ≤ s ≤ T` it
becomes `C exp ((K + 1) ‖ζ‖² T) T^{-(1/2 + d/4)}` times the seminorm bound of the datum.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem sqrt_rpow_half_eq (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    Real.sqrt x ^ ((d : ℝ) / 2) = x ^ ((d : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem rho_lower {ε T s : ℝ} (hε : 0 < ε) (hT : 0 < T) (hTs : T / 2 ≤ s) (d : ℕ) :
    (ε / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4) ≤
      Real.sqrt (ε * (s / 2) / 2) ^ ((d : ℝ) / 2) := by
  have h1 : ε * T / 8 ≤ ε * (s / 2) / 2 := by
    have := mul_le_mul_of_nonneg_left hTs hε.le
    linarith
  have hnn : 0 ≤ ε * T / 8 := by positivity
  rw [sqrt_rpow_half_eq _ (hnn.trans h1), ← Real.mul_rpow (by positivity) hT.le]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  have : ε / 8 * T = ε * T / 8 := by ring
  rw [this]
  exact h1

theorem csqrt_le {K T s : ℝ} (hK : 0 < K) (hT : 0 < T) (hs : 0 < s) (hTs : T / 2 ≤ s) :
    Real.sqrt (2 * K * (s / 2)) / (s / 2) ≤ 3 * Real.sqrt K * T ^ (-(1 / 2 : ℝ)) := by
  have hy : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hx : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hxy : 2 * Real.sqrt T ≤ 3 * Real.sqrt s := by
    have h4 : 4 * T ≤ 9 * s := by linarith
    have := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)] at this
    exact this
  have e1 : Real.sqrt (2 * K * (s / 2)) = Real.sqrt K * Real.sqrt s := by
    rw [← Real.sqrt_mul hK.le]
    congr 1
    ring
  have e2 : s / 2 = Real.sqrt s ^ 2 / 2 := by rw [Real.sq_sqrt hs.le]
  have e3 : T ^ (-(1 / 2 : ℝ)) = (Real.sqrt T)⁻¹ := by
    rw [Real.rpow_neg hT.le, Real.sqrt_eq_rpow]
  rw [e1, e3, ← sub_nonneg]
  have hq : 3 * Real.sqrt K * (Real.sqrt T)⁻¹ - Real.sqrt K * Real.sqrt s / (s / 2) =
      Real.sqrt K * ((3 * Real.sqrt s - 2 * Real.sqrt T) / (Real.sqrt T * Real.sqrt s)) := by
    rw [e2]
    field_simp
  rw [hq]
  exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (by linarith) (by positivity))

theorem le_exp_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp (x ^ 2) := by
  have h1 := Real.add_one_le_exp (x ^ 2)
  nlinarith [sq_nonneg (x - 1)]

theorem le_exp_mul_rpow {T : ℝ} (hT : 0 < T) (z : ℝ) (hz : 0 ≤ z) :
    z ≤ Real.exp (z ^ 2 * T) * T ^ (-(1 / 2 : ℝ)) := by
  have hx : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have e3 : T ^ (-(1 / 2 : ℝ)) = (Real.sqrt T)⁻¹ := by
    rw [Real.rpow_neg hT.le, Real.sqrt_eq_rpow]
  have h1 := le_exp_sq_of_nonneg (mul_nonneg hz hx.le)
  rw [e3]
  calc z = (z * Real.sqrt T) * (Real.sqrt T)⁻¹ := by field_simp
    _ ≤ Real.exp ((z * Real.sqrt T) ^ 2) * (Real.sqrt T)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hx.le)
    _ = Real.exp (z ^ 2 * T) * (Real.sqrt T)⁻¹ := by rw [mul_pow, Real.sq_sqrt hT.le]

theorem norm_forcedFluxE_le_scale (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {T s : ℝ}
    (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T) (hTs : T / 2 ≤ s)
    (hεs : 2 ≤ deconvEps Λ₀ * (s / 2)) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hsem : gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C) (ζ : ℂ)
    (ν : FluxIndex d) :
    ‖forcedFluxE hd Q s hs ζ ν F‖ ≤
      ((deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4))⁻¹ *
        ((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) + 1) *
          Real.exp ((sourceReducedBound Λ₀ + 1) * ‖ζ‖ ^ 2 * T) *
            T ^ (-(1 / 2 + (d : ℝ) / 4)) * C := by
  have hK := sourceReducedBound_pos_of_law Q
  have hε := deconvEps_pos Q
  have hb := norm_forcedFluxE_le hd Q hs hεs F hC hsem ζ ν
  have hρ0 := rho_lower hε hT hTs d
  have hρ0pos : 0 < (deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4) := by positivity
  have hcs := csqrt_le hK hT hs hTs
  have hwpos : 0 < T ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hT _
  have hX1 : 1 ≤ Real.exp (‖ζ‖ ^ 2 * T) := Real.one_le_exp (by positivity)
  have hζ : ‖ζ‖ ≤ Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ)) :=
    le_exp_mul_rpow hT ‖ζ‖ (norm_nonneg ζ)
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsqK : 0 ≤ Real.sqrt (sourceReducedBound Λ₀) := Real.sqrt_nonneg _
  have he1 : Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT (by positivity))
  have hbr : (d : ℝ) / 2 * (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2)) +
      ‖ζ‖ ≤ ((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) + 1) *
        Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ)) := by
    have hc1 : (d : ℝ) / 2 * (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2)) ≤
        (d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀) * T ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have hc2 : T ^ (-(1 / 2 : ℝ)) ≤ Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ)) :=
      le_mul_of_one_le_left hwpos.le hX1
    have hc3 : (d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) *
        T ^ (-(1 / 2 : ℝ)) ≤ (d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) *
        (Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    nlinarith [hc1, hc3, hζ]
  have hnormE : 0 ≤ ‖forcedFluxE hd Q s hs ζ ν F‖ := norm_nonneg _
  have h1 : ‖forcedFluxE hd Q s hs ζ ν F‖ ≤
      ((deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4))⁻¹ *
        (Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          ‖forcedFluxE hd Q s hs ζ ν F‖) := by
    calc _ = ((deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4))⁻¹ *
          (((deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4)) *
            ‖forcedFluxE hd Q s hs ζ ν F‖) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ0 hnormE)
          (inv_nonneg.mpr hρ0pos.le)
  have hbrnn : 0 ≤ (d : ℝ) / 2 *
      (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2)) + ‖ζ‖ := by positivity
  have h2 : Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖forcedFluxE hd Q s hs ζ ν F‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
        (((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) + 1) *
          Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ))) * C :=
    hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul he1 hbr hbrnn (Real.exp_pos _).le) hC)
  have hTpow : T ^ (-(1 / 2 + (d : ℝ) / 4)) =
      T ^ (-(1 / 2 : ℝ)) * (T ^ ((d : ℝ) / 4))⁻¹ := by
    rw [show -(1 / 2 + (d : ℝ) / 4) = -(1 / 2 : ℝ) + -((d : ℝ) / 4) by ring,
      Real.rpow_add hT, Real.rpow_neg hT.le ((d : ℝ) / 4)]
  have hexp : Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) * Real.exp (‖ζ‖ ^ 2 * T) =
      Real.exp ((sourceReducedBound Λ₀ + 1) * ‖ζ‖ ^ 2 * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ _ := h1
    _ ≤ ((deconvEps Λ₀ / 8) ^ ((d : ℝ) / 4) * T ^ ((d : ℝ) / 4))⁻¹ *
        (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
          (((d : ℝ) / 2 * (3 * Real.sqrt (sourceReducedBound Λ₀)) + 1) *
            Real.exp (‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 : ℝ))) * C) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hρ0pos.le)
    _ = _ := by
      rw [mul_inv, hTpow, ← hexp]
      ring

end EinsteinFull
