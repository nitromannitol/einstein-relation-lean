import Mathlib

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

theorem abs_le_of_two_sided_moser_bound {d : ℕ} {x K J R p : ℝ} (hp : 0 < p)
    (hR : 0 < R) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hpos : |max x 0| ^ p ≤ K * (((2 * R) ^ d)⁻¹ * J))
    (hneg : |max (-x) 0| ^ p ≤ K * (((2 * R) ^ d)⁻¹ * J)) :
    |x| ≤ (K * (2 ^ d)⁻¹) ^ (1 / p) * R ^ (-(d : ℝ) / p) * J ^ (1 / p) := by
  -- Either one-sided bound controls `|x| ^ p`, according to the sign of `x`.
  have hM : |x| ^ p ≤ K * (((2 * R) ^ d)⁻¹ * J) := by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx] at hpos
      exact hpos
    · have hx' : 0 ≤ -x := neg_nonneg.mpr hx
      rw [max_eq_left hx', abs_neg] at hneg
      exact hneg
  -- Raise to the power `1 / p`; `(|x| ^ p) ^ (1 / p) = |x|`.
  have hsq : |x| ≤ (K * (((2 * R) ^ d)⁻¹ * J)) ^ (1 / p) := by
    have h1 : (|x| ^ p) ^ (1 / p) ≤ (K * (((2 * R) ^ d)⁻¹ * J)) ^ (1 / p) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg x) p) hM (one_div_nonneg.mpr hp.le)
    rwa [← Real.rpow_mul (abs_nonneg x), mul_one_div, div_self hp.ne', Real.rpow_one] at h1
  -- Nonnegativity of the factors, needed to split the real power.
  have h2inv : 0 ≤ (2 ^ d : ℝ)⁻¹ := inv_nonneg.mpr (pow_nonneg (by norm_num) d)
  have hRinv : 0 ≤ (R ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hR.le d)
  have hK2 : 0 ≤ K * (2 ^ d)⁻¹ := mul_nonneg hK h2inv
  have hKR : 0 ≤ K * (2 ^ d)⁻¹ * (R ^ d)⁻¹ := mul_nonneg hK2 hRinv
  -- Regroup `(2 * R) ^ d` as `2 ^ d * R ^ d`.
  have key : K * (((2 * R) ^ d)⁻¹ * J) = K * (2 ^ d)⁻¹ * (R ^ d)⁻¹ * J := by
    rw [mul_pow, mul_inv]
    ring
  -- `((R ^ d)⁻¹) ^ (1 / p) = R ^ (-d / p)`.
  have hRd : ((R ^ d)⁻¹) ^ (1 / p) = R ^ (-(d : ℝ) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hR.le, ← Real.rpow_mul hR.le, mul_one_div]
  have hrhs : (K * (((2 * R) ^ d)⁻¹ * J)) ^ (1 / p)
      = (K * (2 ^ d)⁻¹) ^ (1 / p) * R ^ (-(d : ℝ) / p) * J ^ (1 / p) := by
    rw [key, Real.mul_rpow hKR hJ, Real.mul_rpow hK2 hRinv, hRd]
  exact hsq.trans_eq hrhs

end EinsteinRelation.Correctors
