import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Deterministic time-decay bound for the paired corrector, the scale conversion in
`paper/main.tex:839–856` (Step 2 of the paired-corrector energy bound). For
`n > 1 + d/2` and `R ≥ 1`, the time integral of the decay `(1+t)^{-(1+d/2)/n}` over
`[0, 4R²]`, raised to `n/2` and multiplied by `√(4R²) R^{-n}`, is at most a constant
times `R^{-d/2}`. The constant depends only on `d` and `n`.

This file proves only this real-variable inequality. It does not prove the PDE or
corrector estimate that supplies the integrand, and it uses no external assumption.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Explicit primitive of the shifted power: for `r > -1`,
`∫₀ᵀ (1+t)^r dt = ((1+T)^(r+1) - 1)/(r+1)`. The shift `t ↦ 1+t` reduces to
`integral_rpow`. -/
private theorem paired_decay_integral_eq {r T : ℝ} (hr : -1 < r) :
    (∫ t in (0 : ℝ)..T, (1 + t) ^ r) = ((1 + T) ^ (r + 1) - 1) / (r + 1) := by
  have hshift : (∫ t in (0 : ℝ)..T, (1 + t) ^ r) = ∫ x in (1 : ℝ)..(1 + T), x ^ r := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := T)
      (fun x : ℝ => x ^ r) (1 : ℝ)
    rw [add_zero] at h
    exact h
  rw [hshift, integral_rpow (a := (1 : ℝ)) (b := 1 + T) (r := r) (Or.inl hr), Real.one_rpow]

/-- Nonnegativity and the explicit upper bound `∫₀ᵀ (1+t)^r dt ≤ (1+T)^(r+1)/(r+1)`
for `r + 1 > 0` and `T ≥ 0`. -/
private theorem paired_decay_integral_bounds {r T : ℝ} (hβ : 0 < r + 1) (hT : 0 ≤ T) :
    0 ≤ (∫ t in (0 : ℝ)..T, (1 + t) ^ r) ∧
      (∫ t in (0 : ℝ)..T, (1 + t) ^ r) ≤ (1 + T) ^ (r + 1) / (r + 1) := by
  have hX : (1 : ℝ) ≤ (1 + T) ^ (r + 1) := Real.one_le_rpow (by linarith) hβ.le
  rw [paired_decay_integral_eq (r := r) (T := T) (by linarith)]
  exact ⟨div_nonneg (by linarith) hβ.le, div_le_div_of_nonneg_right (by linarith) hβ.le⟩

/-- Deterministic core of the scale conversion, with the exponent identity
`r N = -(1 + D/2)` (that is, `r = -(1+D/2)/N`) and `r + 1 > 0`. For `R ≥ 1` the
left side is at most `2 (5^{r+1}/(r+1))^{N/2} R^{-D/2}`. -/
private theorem paired_decay_core {r N D R : ℝ} (hβ : 0 < r + 1) (hN : 0 < N)
    (hrN : r * N = -(1 + D / 2)) (hR : 1 ≤ R) :
    Real.sqrt (4 * R ^ 2) * R ^ (-N) * (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ r) ^ (N / 2)
      ≤ (2 * ((5 : ℝ) ^ (r + 1) / (r + 1)) ^ (N / 2)) * R ^ (-D / 2) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hR2nn : (0 : ℝ) ≤ R ^ 2 := by positivity
  have hT : (0 : ℝ) ≤ 4 * R ^ 2 := by positivity
  have hhalf : (0 : ℝ) ≤ N / 2 := div_nonneg hN.le (by norm_num)
  have hK0 : (0 : ℝ) ≤ (5 : ℝ) ^ (r + 1) / (r + 1) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) hβ.le
  have hY0 : (0 : ℝ) ≤ (R ^ 2) ^ (r + 1) := Real.rpow_nonneg hR2nn _
  obtain ⟨hI0, hIle⟩ := paired_decay_integral_bounds hβ hT
  have h5R : (5 * R ^ 2) ^ (r + 1) = (5 : ℝ) ^ (r + 1) * (R ^ 2) ^ (r + 1) :=
    Real.mul_rpow (by norm_num) hR2nn
  have hpow : (1 + 4 * R ^ 2) ^ (r + 1) ≤ (5 * R ^ 2) ^ (r + 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hβ.le
  have hI_le : (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ r) ≤
      ((5 : ℝ) ^ (r + 1) / (r + 1)) * (R ^ 2) ^ (r + 1) := by
    calc (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ r)
        ≤ (1 + 4 * R ^ 2) ^ (r + 1) / (r + 1) := hIle
      _ ≤ (5 * R ^ 2) ^ (r + 1) / (r + 1) := div_le_div_of_nonneg_right hpow hβ.le
      _ = ((5 : ℝ) ^ (r + 1) / (r + 1)) * (R ^ 2) ^ (r + 1) := by rw [h5R]; ring
  have hIpow : (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ r) ^ (N / 2) ≤
      ((5 : ℝ) ^ (r + 1) / (r + 1)) ^ (N / 2) * ((R ^ 2) ^ (r + 1)) ^ (N / 2) := by
    rw [← Real.mul_rpow hK0 hY0]
    exact Real.rpow_le_rpow hI0 hI_le hhalf
  have hYpow : ((R ^ 2) ^ (r + 1)) ^ (N / 2) = R ^ (N - 1 - D / 2) := by
    rw [← Real.rpow_mul hR2nn, ← Real.rpow_two R, ← Real.rpow_mul hR0.le,
      show (2 : ℝ) * ((r + 1) * (N / 2)) = N - 1 - D / 2 by linear_combination hrN]
  rw [hYpow] at hIpow
  have hrad : R * R ^ (-N) * R ^ (N - 1 - D / 2) = R ^ (-D / 2) := by
    rw [show -D / 2 = (1 + -N) + (N - 1 - D / 2) by ring,
      Real.rpow_add hR0, Real.rpow_add hR0, Real.rpow_one]
  have hsqrt : Real.sqrt (4 * R ^ 2) = 2 * R := by
    rw [show (4 : ℝ) * R ^ 2 = (2 * R) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [hsqrt]
  calc 2 * R * R ^ (-N) * (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ r) ^ (N / 2)
      ≤ 2 * R * R ^ (-N) * (((5 : ℝ) ^ (r + 1) / (r + 1)) ^ (N / 2) * R ^ (N - 1 - D / 2)) :=
        mul_le_mul_of_nonneg_left hIpow (mul_nonneg (by linarith) (Real.rpow_nonneg hR0.le _))
    _ = (2 * ((5 : ℝ) ^ (r + 1) / (r + 1)) ^ (N / 2)) * (R * R ^ (-N) * R ^ (N - 1 - D / 2)) := by
        ring
    _ = (2 * ((5 : ℝ) ^ (r + 1) / (r + 1)) ^ (N / 2)) * R ^ (-D / 2) := by rw [hrad]

/-- `corrector.conditional`, Step 2, `paper/main.tex:839–856`. The constant `C` depends
only on `d` and `n`, not on `R`. This is the deterministic real-power estimate; the
PDE/corrector input is not proved here. -/
theorem paired_time_decay_bound : ∀ (d n : ℕ), 2 ≤ d →
  1 + (d : ℝ)/2 < (n : ℝ) → ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
  Real.sqrt (4*R^2) * R^(-(n : ℝ)) *
    (∫ t in (0 : ℝ)..(4*R^2), (1+t)^(-(1+(d : ℝ)/2)/(n : ℝ)))^((n : ℝ)/2)
    ≤ C * R^(-(d : ℝ)/2) := by
  intro d n _hd hn
  have hNpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  have hq : (1 + (d : ℝ)/2) / (n : ℝ) < 1 := (div_lt_one hNpos).mpr hn
  have hβ : (0 : ℝ) < -(1 + (d : ℝ)/2) / (n : ℝ) + 1 := by
    rw [neg_div]; linarith
  have hrN : -(1 + (d : ℝ)/2) / (n : ℝ) * (n : ℝ) = -(1 + (d : ℝ)/2) :=
    div_mul_cancel₀ _ hNpos.ne'
  have hK : (0 : ℝ) < (5 : ℝ) ^ (-(1 + (d : ℝ)/2) / (n : ℝ) + 1) /
      (-(1 + (d : ℝ)/2) / (n : ℝ) + 1) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) hβ
  refine ⟨2 * ((5 : ℝ) ^ (-(1 + (d : ℝ)/2) / (n : ℝ) + 1) /
    (-(1 + (d : ℝ)/2) / (n : ℝ) + 1)) ^ ((n : ℝ)/2),
    mul_pos two_pos (Real.rpow_pos_of_pos hK _), ?_⟩
  intro R hR
  exact paired_decay_core hβ hNpos hrN hR

end EinsteinRelation.Correctors
