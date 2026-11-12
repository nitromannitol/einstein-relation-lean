import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Time integration of the scalar heat-decay bound

Source: `paper/main.tex:1033–1041`. The averaging assumption has decay
`(1+t)^(-1/2) + R^(-1)`. Its integral up to `r²`, with `r ≤ R`, is at most `3r`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The decay weight is continuous on every nonnegative time interval
(`paper/main.tex:1033–1041`). -/
theorem continuousOn_inv_sqrt_one_add (T : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.sqrt (1 + t))⁻¹) (Set.Icc 0 T) := by
  refine ((continuous_const.add continuous_id).sqrt.continuousOn).inv₀ ?_
  intro t ht
  change Real.sqrt (1 + t) ≠ 0
  exact (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'

/-- The primitive of the decaying part of the scalar averaging bound
(`paper/main.tex:1033–1041`). -/
theorem integral_inv_sqrt_one_add {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (Real.sqrt (1 + t))⁻¹) =
      2 * (Real.sqrt (1 + T) - 1) := by
  have hcont := continuousOn_inv_sqrt_one_add T
  have hint : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 + t))⁻¹) volume 0 T :=
    hcont.intervalIntegrable_of_Icc hT
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt (1 + t)) ((Real.sqrt (1 + t))⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have htpos : 0 < 1 + t := by linarith [ht.1]
    have h := (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).sqrt htpos.ne').const_mul 2
    convert h using 1
    dsimp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    _ = 2 * Real.sqrt (1 + T) - 2 * Real.sqrt (1 + 0) := h
    _ = _ := by rw [add_zero, Real.sqrt_one]; ring

/-- The complete time integral is linear in the band scale
(`paper/main.tex:1033–1041`). -/
theorem integral_heatDecay_le_three_mul {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hR : 0 < R) :
    (∫ t in (0 : ℝ)..r ^ 2, ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) ≤ 3 * r := by
  have hint : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 + t))⁻¹)
      volume 0 (r ^ 2) := by
    exact (continuousOn_inv_sqrt_one_add (r ^ 2)).intervalIntegrable_of_Icc (sq_nonneg r)
  rw [intervalIntegral.integral_add hint intervalIntegrable_const,
    integral_inv_sqrt_one_add (sq_nonneg r), intervalIntegral.integral_const]
  have hsqrt : Real.sqrt (1 + r ^ 2) ≤ r + 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith, by nlinarith⟩
  have hsmall : r ^ 2 * R⁻¹ ≤ r := by
    rw [← div_eq_mul_inv, div_le_iff₀ hR]
    nlinarith
  simp only [sub_zero, smul_eq_mul]
  linarith

end EinsteinRelation.Correctors
