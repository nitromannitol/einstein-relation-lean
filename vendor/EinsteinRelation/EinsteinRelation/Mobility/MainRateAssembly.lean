import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.TimeChange.InverseClock

/-! # Algebraic assembly of the rate bound in Theorem 1.2

Source: `paper/main.tex`, proof of `t.main` (lines 1187-1196). With `η = η(λ)` the
clock value and `m = 𝔼μ` the mean, the rescaled velocity splits as
`ℓ_X/λ - Σ_X e₁ = η⁻¹ (ℓ/λ - ā e₁) + (η⁻¹ - m⁻¹) ā e₁`. Both scalars lie in
`[Λ⁻¹, Λ]` and `‖ā e₁‖ ≤ Λ`, so the two error terms are controlled by the velocity
and clock estimates. All norms are the Euclidean norm `euclideanNorm` on `Vec d`.
-/

open EinsteinRelation.TimeChange (euclideanNorm_add_le euclideanNorm_smul inv_sub_inv_bound)

namespace EinsteinRelation

private theorem mainRate_euclideanNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- Algebraic assembly of the rate bound. The velocity error `‖λ⁻¹ ℓ - ā e₁‖ ≤ C₁ λ`
and the clock error `|η - m| ≤ C₂ λ` combine into `‖λ⁻¹ η⁻¹ ℓ - m⁻¹ ā e₁‖ ≤ (Λ C₁ + Λ³ C₂) λ`.
The positivity of `λ` is not used by the estimate. -/
theorem main_rate_assembly {d : ℕ} {lam C₁ C₂ Λ η m : ℝ} {ell abarE1 : Vec d}
    (_hlam : 0 < lam) (hΛ : 1 ≤ Λ)
    (hη : Λ⁻¹ ≤ η ∧ η ≤ Λ) (hm : Λ⁻¹ ≤ m ∧ m ≤ Λ) (ha : euclideanNorm abarE1 ≤ Λ)
    (h1 : euclideanNorm (lam⁻¹ • ell - abarE1) ≤ C₁ * lam) (h2 : |η - m| ≤ C₂ * lam) :
    euclideanNorm (lam⁻¹ • (η⁻¹ • ell) - m⁻¹ • abarE1) ≤ (Λ * C₁ + Λ ^ 3 * C₂) * lam := by
  have hΛ0 : 0 < Λ := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (inv_pos.mpr hΛ0) hη.1
  have hηi : η⁻¹ ≤ Λ := by
    have h := inv_anti₀ (inv_pos.mpr hΛ0) hη.1
    rwa [inv_inv] at h
  have hηi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη0.le
  have hsplit : lam⁻¹ • (η⁻¹ • ell) - m⁻¹ • abarE1
      = η⁻¹ • (lam⁻¹ • ell - abarE1) + (η⁻¹ - m⁻¹) • abarE1 := by
    rw [smul_sub, sub_smul, smul_comm lam⁻¹ η⁻¹ ell]
    abel
  have hC₂lam : 0 ≤ C₂ * lam := le_trans (abs_nonneg _) h2
  have hdiff : |η⁻¹ - m⁻¹| ≤ Λ ^ 2 * (C₂ * lam) :=
    le_trans (inv_sub_inv_bound Λ η m hΛ0 hη.1 hm.1)
      (mul_le_mul_of_nonneg_left h2 (sq_nonneg Λ))
  have hT1 : η⁻¹ * euclideanNorm (lam⁻¹ • ell - abarE1) ≤ Λ * (C₁ * lam) :=
    le_trans (mul_le_mul_of_nonneg_right hηi (mainRate_euclideanNorm_nonneg _))
      (mul_le_mul_of_nonneg_left h1 hΛ0.le)
  have hT2 : |η⁻¹ - m⁻¹| * euclideanNorm abarE1 ≤ Λ ^ 2 * (C₂ * lam) * Λ :=
    le_trans (mul_le_mul_of_nonneg_right hdiff (mainRate_euclideanNorm_nonneg _))
      (mul_le_mul_of_nonneg_left ha (mul_nonneg (sq_nonneg Λ) hC₂lam))
  calc euclideanNorm (lam⁻¹ • (η⁻¹ • ell) - m⁻¹ • abarE1)
      = euclideanNorm (η⁻¹ • (lam⁻¹ • ell - abarE1) + (η⁻¹ - m⁻¹) • abarE1) := by
        rw [hsplit]
    _ ≤ euclideanNorm (η⁻¹ • (lam⁻¹ • ell - abarE1))
          + euclideanNorm ((η⁻¹ - m⁻¹) • abarE1) := euclideanNorm_add_le _ _
    _ = |η⁻¹| * euclideanNorm (lam⁻¹ • ell - abarE1)
          + |η⁻¹ - m⁻¹| * euclideanNorm abarE1 := by
        rw [euclideanNorm_smul, euclideanNorm_smul]
    _ = η⁻¹ * euclideanNorm (lam⁻¹ • ell - abarE1)
          + |η⁻¹ - m⁻¹| * euclideanNorm abarE1 := by
        rw [abs_of_nonneg hηi0]
    _ ≤ Λ * (C₁ * lam) + Λ ^ 2 * (C₂ * lam) * Λ := add_le_add hT1 hT2
    _ = (Λ * C₁ + Λ ^ 3 * C₂) * lam := by ring

end EinsteinRelation
