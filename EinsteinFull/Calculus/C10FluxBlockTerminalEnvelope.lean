import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace EinsteinFull.Calculus

/-- The terminal eighth-time powers admit the standard whole-time envelope. -/
theorem c10_flux_block_terminal_eighth_envelope (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (ζ : ℂ), 8 ≤ t →
      (t / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
        ‖ζ‖ * (t / 8) ^ (-(d : ℝ) / 4) ≤
      C * t ^ (-(1 / 2 + (d : ℝ) / 4)) * (1 + ‖ζ‖ * Real.sqrt t) := by
  let a : ℝ := 1 / 2 + (d : ℝ) / 4
  let b : ℝ := (d : ℝ) / 4
  let A : ℝ := (8 : ℝ) ^ a
  let B : ℝ := (8 : ℝ) ^ b
  refine ⟨max 1 (A + B), le_max_left _ _, ?_⟩
  intro t ζ ht
  have htpos : 0 < t := by linarith
  have hA : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
  have hB : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
  have hT : 0 ≤ t ^ (-a) := Real.rpow_nonneg htpos.le _
  have hZ : 0 ≤ ‖ζ‖ * Real.sqrt t := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hpow : t ^ (-b) = t ^ (-a) * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add htpos]
    congr 1
    dsimp [a, b]
    ring
  have hdiv (x : ℝ) : (t / 8) ^ (-x) = t ^ (-x) * (8 : ℝ) ^ x := by
    rw [Real.div_rpow htpos.le (by norm_num), Real.rpow_neg (x := (8 : ℝ)) (by norm_num)]
    simp only [div_inv_eq_mul]
  rw [show -(d : ℝ) / 4 = -b by dsimp [b]; ring]
  change (t / 8) ^ (-a) + ‖ζ‖ * (t / 8) ^ (-b) ≤
    max 1 (A + B) * t ^ (-a) * (1 + ‖ζ‖ * Real.sqrt t)
  rw [hdiv a, hdiv b, hpow]
  have hc : A + B ≤ max 1 (A + B) := le_max_right _ _
  have hAB : A + (‖ζ‖ * Real.sqrt t) * B ≤ (A + B) * (1 + ‖ζ‖ * Real.sqrt t) := by
    nlinarith [mul_nonneg hA hZ]
  have hbound : A + (‖ζ‖ * Real.sqrt t) * B ≤
      max 1 (A + B) * (1 + ‖ζ‖ * Real.sqrt t) :=
    hAB.trans (mul_le_mul_of_nonneg_right hc (by linarith))
  have := mul_le_mul_of_nonneg_left hbound hT
  nlinarith

/-- Normalize the scalar prefactors in the Gaussian derivative estimate. -/
theorem c10_flux_gaussian_prefactor_normalization
    (d : ℕ) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k) :
    ∃ Cder : ℕ → ℝ, (∀ k, 1 ≤ Cder k) ∧
    ∀ (k : ℕ) (t s r W : ℝ) (ζ : ℂ),
      1 ≤ t → 1 ≤ s → 0 < r → 0 ≤ W →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      (t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹) *
        (D k * s ^ (-(k : ℝ) / 2) * W) +
      ((Real.sqrt t)⁻¹ + ‖ζ‖) *
        (Real.sqrt (d : ℝ) *
          (D k * (R / r) * s ^ (-(k : ℝ) / 2) +
            D (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W) ≤
      Cder k * s ^ (-(k : ℝ) / 2) * W *
        (t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
          ((Real.sqrt t)⁻¹ + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹)) := by
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let C : ℕ → ℝ := fun k => max 1 (D k + Real.sqrt (d : ℝ) * (D k * R + D (k + 1)))
  refine ⟨C, fun k => le_max_left _ _, ?_⟩
  intro k t s r W ζ ht hs hr hW
  dsimp only
  have hspos : 0 < s := by linarith
  have hpow : s ^ (-((k + 1 : ℕ) : ℝ) / 2) =
      s ^ (-(k : ℝ) / 2) * (Real.sqrt s)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hspos.le, ← Real.rpow_add hspos]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hp : 0 ≤ s ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hspos.le _
  have hx : 0 ≤ t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ := by positivity
  have hy : 0 ≤ (Real.sqrt t)⁻¹ + ‖ζ‖ := by positivity
  have hu : 0 ≤ r⁻¹ := by positivity
  have hv : 0 ≤ (Real.sqrt s)⁻¹ := by positivity
  have hc : D k + Real.sqrt (d : ℝ) * (D k * R + D (k + 1)) ≤ C k := le_max_right _ _
  have hcoef1 : D k ≤ C k := by nlinarith [hD k, hD (k + 1), mul_nonneg (hD k) hR]
  have hcoef2 : Real.sqrt (d : ℝ) * (D k * R) ≤ C k := by
    nlinarith [hD k, hD (k + 1), mul_nonneg hd (hD (k + 1))]
  have hcoef3 : Real.sqrt (d : ℝ) * D (k + 1) ≤ C k := by
    nlinarith [hD k, hD (k + 1), mul_nonneg hd (mul_nonneg (hD k) hR)]
  have h1 := mul_le_mul_of_nonneg_right hcoef1 hx
  have h2 := mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg hy hu)
  have h3 := mul_le_mul_of_nonneg_right hcoef3 (mul_nonneg hy hv)
  have hsum : D k * (t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹) +
      (Real.sqrt (d : ℝ) * (D k * R)) * (((Real.sqrt t)⁻¹ + ‖ζ‖) * r⁻¹) +
      (Real.sqrt (d : ℝ) * D (k + 1)) * (((Real.sqrt t)⁻¹ + ‖ζ‖) * (Real.sqrt s)⁻¹) ≤
      C k * (t⁻¹ + ‖ζ‖ * (Real.sqrt t)⁻¹ +
        ((Real.sqrt t)⁻¹ + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹)) := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hsum (mul_nonneg hp hW)
  dsimp [R] at hfinal
  convert hfinal using 1 <;> ring

end EinsteinFull.Calculus
