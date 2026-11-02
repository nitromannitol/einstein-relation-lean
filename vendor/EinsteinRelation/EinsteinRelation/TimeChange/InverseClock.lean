import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Inverse-clock error bounds for the time change

Source: `paper/main.tex`, proof of `t.main` (lines 1187–1195). The time-change
identities give
`ℓ_X(λ)/λ - Σ_X e₁ = η(λ)⁻¹ (ℓ(λ)/λ - â e₁) + (η(λ)⁻¹ - (𝔼μ)⁻¹) â e₁`,
and both clock values lie in `[Λ⁻¹, Λ]`.

The bounds are generic over real normed spaces, so they apply to the Euclidean
transport used later. They are internal prerequisites, not the final theorems.
-/

namespace EinsteinRelation.TimeChange

/-- Inverse-difference estimate: on `[Λ⁻¹, ∞)` the map `x ↦ x⁻¹` is `Λ²`-Lipschitz. -/
theorem inv_sub_inv_bound (Λ η m : ℝ) (hΛ : 0 < Λ)
    (hη : Λ⁻¹ ≤ η) (hm : Λ⁻¹ ≤ m) :
    |η⁻¹ - m⁻¹| ≤ Λ ^ 2 * |η - m| := by
  have hη0 : 0 < η := lt_of_lt_of_le (inv_pos.mpr hΛ) hη
  have hm0 : 0 < m := lt_of_lt_of_le (inv_pos.mpr hΛ) hm
  have hηi : η⁻¹ ≤ Λ := by
    have h := inv_anti₀ (inv_pos.mpr hΛ) hη
    rwa [inv_inv] at h
  have hmi : m⁻¹ ≤ Λ := by
    have h := inv_anti₀ (inv_pos.mpr hΛ) hm
    rwa [inv_inv] at h
  have hηi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη0.le
  have hmi0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm0.le
  have hprod : η⁻¹ * m⁻¹ ≤ Λ * Λ :=
    le_trans (mul_le_mul_of_nonneg_right hηi hmi0) (mul_le_mul_of_nonneg_left hmi hΛ.le)
  have hab : |m - η| = |η - m| := abs_sub_comm m η
  have habs : |η⁻¹ - m⁻¹| = η⁻¹ * |m - η| * m⁻¹ := by
    rw [inv_sub_inv' hη0.ne' hm0.ne', abs_mul, abs_mul, abs_of_nonneg hηi0,
      abs_of_nonneg hmi0]
  rw [habs]
  calc η⁻¹ * |m - η| * m⁻¹ = (η⁻¹ * m⁻¹) * |m - η| := by ring
    _ ≤ (Λ * Λ) * |m - η| := mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
    _ = Λ ^ 2 * |η - m| := by rw [hab, sq]

/-- Generic time-change error bound in a real normed space. A velocity error
`‖u - a‖ ≤ Cv·lam` and a clock error `|η - m| ≤ Cc·lam` with `‖a‖ ≤ Λ` give
`‖η⁻¹ • u - m⁻¹ • a‖ ≤ (Λ·Cv + Λ³·Cc)·lam`. -/
theorem time_change_error_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ η m lam Cv Cc : ℝ) (u a : E) (hΛ : 0 < Λ) (_hlam : 0 ≤ lam)
    (hη : Λ⁻¹ ≤ η) (hm : Λ⁻¹ ≤ m) (ha : ‖a‖ ≤ Λ)
    (hv : ‖u - a‖ ≤ Cv * lam) (hc : |η - m| ≤ Cc * lam) :
    ‖η⁻¹ • u - m⁻¹ • a‖ ≤ (Λ * Cv + Λ ^ 3 * Cc) * lam := by
  have hη0 : 0 < η := lt_of_lt_of_le (inv_pos.mpr hΛ) hη
  have hηi : η⁻¹ ≤ Λ := by
    have h := inv_anti₀ (inv_pos.mpr hΛ) hη
    rwa [inv_inv] at h
  have hηi0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη0.le
  have hCv : 0 ≤ Cv * lam := le_trans (norm_nonneg _) hv
  have hCc : 0 ≤ Cc * lam := le_trans (abs_nonneg _) hc
  have hdiff : |η⁻¹ - m⁻¹| ≤ Λ ^ 2 * (Cc * lam) :=
    le_trans (inv_sub_inv_bound Λ η m hΛ hη hm) (mul_le_mul_of_nonneg_left hc (sq_nonneg Λ))
  have hsplit : η⁻¹ • u - m⁻¹ • a = η⁻¹ • (u - a) + (η⁻¹ - m⁻¹) • a := by
    rw [smul_sub, sub_smul]
    abel
  have h1 : ‖η⁻¹ • (u - a)‖ ≤ Λ * (Cv * lam) := by
    rw [norm_smul, Real.norm_of_nonneg hηi0]
    calc η⁻¹ * ‖u - a‖ ≤ η⁻¹ * (Cv * lam) := mul_le_mul_of_nonneg_left hv hηi0
      _ ≤ Λ * (Cv * lam) := mul_le_mul_of_nonneg_right hηi hCv
  have h2 : ‖(η⁻¹ - m⁻¹) • a‖ ≤ Λ ^ 3 * (Cc * lam) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |η⁻¹ - m⁻¹| * ‖a‖ ≤ |η⁻¹ - m⁻¹| * Λ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
      _ ≤ (Λ ^ 2 * (Cc * lam)) * Λ := mul_le_mul_of_nonneg_right hdiff hΛ.le
      _ = Λ ^ 3 * (Cc * lam) := by ring
  calc ‖η⁻¹ • u - m⁻¹ • a‖ = ‖η⁻¹ • (u - a) + (η⁻¹ - m⁻¹) • a‖ := by rw [hsplit]
    _ ≤ ‖η⁻¹ • (u - a)‖ + ‖(η⁻¹ - m⁻¹) • a‖ := norm_add_le _ _
    _ ≤ Λ * (Cv * lam) + Λ ^ 3 * (Cc * lam) := add_le_add h1 h2
    _ = (Λ * Cv + Λ ^ 3 * Cc) * lam := by ring

end EinsteinRelation.TimeChange
