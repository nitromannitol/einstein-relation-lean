import Mathlib.Tactic

/-!
# Arithmetic of the slab shell estimate

Substitution of value and gradient error bounds yields an affine energy
recurrence with explicit coefficients.
-/

namespace EinsteinFull.Regeneration

/-- Value and gradient shell bounds give an explicit affine energy estimate. -/
theorem slab_shell_substitution (Ein P α β T S lam A B E : ℝ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hvalue : lam * T ≤ lam * A + B * E)
    (hgrad : lam * S ≤ lam * A + E)
    (henergy : Ein ≤ P + α * T + β * S) :
    Ein ≤ P + (α + β) * A + ((α * B + β) / lam) * E := by
  have ht : T ≤ A + (B / lam) * E := by
    have h : T ≤ (lam * A + B * E) / lam :=
      (le_div_iff₀ hlam).2 (by nlinarith [hvalue])
    have heq : (lam * A + B * E) / lam = A + (B / lam) * E := by
      field_simp
    simpa only [heq] using h
  have hs : S ≤ A + E / lam := by
    have h : S ≤ (lam * A + E) / lam :=
      (le_div_iff₀ hlam).2 (by nlinarith [hgrad])
    have heq : (lam * A + E) / lam = A + E / lam := by
      field_simp
    simpa only [heq] using h
  have htmul := mul_le_mul_of_nonneg_left ht hα
  have hsmul := mul_le_mul_of_nonneg_left hs hβ
  have heq : P + α * (A + (B / lam) * E) + β * (A + E / lam) =
      P + (α + β) * A + ((α * B + β) / lam) * E := by ring
  rw [← heq]
  linarith


/-- Normalize the explicit cutoff coefficients when the cutoff gradient is
bounded by a constant times the small exponential scale. -/
theorem slab_shell_coefficients_le (lam Λ C ε K D L : ℝ)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 0 ≤ K) (hKC : K ≤ C * ε) (hD : 0 ≤ D) (hL : 1 ≤ L) :
    let α := Λ * (K ^ 2 + K)
    let β := 2 * Λ * K
    (Λ + α + β) * (D * ε) ≤ D * Λ * (1 + C ^ 2 + 3 * C) * ε ∧
    (α * (2 * L) ^ 2 + β) / lam ≤
      (Λ * (4 * C ^ 2 + 6 * C) / lam) * L ^ 2 * ε := by
  dsimp only
  have hCε : C * ε ≤ C := by nlinarith [mul_nonneg hC (sub_nonneg.mpr hε1)]
  have hKleC : K ≤ C := hKC.trans hCε
  have hsq' := mul_le_mul hKC hKleC hK (mul_nonneg hC hε)
  have hsq : K ^ 2 ≤ C ^ 2 * ε := by nlinarith [hsq']
  have hα : Λ * (K ^ 2 + K) ≤ Λ * (C ^ 2 + C) * ε := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hsq hKC) hΛ
    nlinarith
  have hβ : 2 * Λ * K ≤ 2 * Λ * C * ε := by
    have h := mul_le_mul_of_nonneg_left hKC (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hΛ)
    nlinarith
  have hP : 0 ≤ Λ * (C ^ 2 + 3 * C) := by positivity
  have hcoef : Λ + Λ * (K ^ 2 + K) + 2 * Λ * K ≤ Λ * (1 + C ^ 2 + 3 * C) := by
    have h := mul_le_mul_of_nonneg_left hε1 hP
    nlinarith [hα, hβ]
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hβscale : 2 * Λ * K ≤ 2 * Λ * C * ε * L ^ 2 := by
    have hp : 0 ≤ 2 * Λ * C * ε := by positivity
    nlinarith [hβ, mul_nonneg hp (sub_nonneg.mpr hLsq)]
  have hαscale := mul_le_mul_of_nonneg_right hα (sq_nonneg (2 * L))
  have hcoefB : Λ * (K ^ 2 + K) * (2 * L) ^ 2 + 2 * Λ * K ≤
      Λ * (4 * C ^ 2 + 6 * C) * L ^ 2 * ε := by nlinarith [hαscale, hβscale]
  constructor
  · have h := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hD hε)
    nlinarith
  · have h := div_le_div_of_nonneg_right hcoefB hlam.le
    have heq : (Λ * (4 * C ^ 2 + 6 * C) * L ^ 2 * ε) / lam =
        (Λ * (4 * C ^ 2 + 6 * C) / lam) * L ^ 2 * ε := by ring
    simpa only [heq] using h

end EinsteinFull.Regeneration
