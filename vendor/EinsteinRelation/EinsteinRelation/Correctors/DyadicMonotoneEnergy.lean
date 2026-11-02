import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! # Interpolating dyadic spatial energy decay

Source: `paper/main.tex:693-698,798-806`. Nonnegative energy integrals
increase with the ball radius, so convergence at dyadic radii controls
all sufficiently large real radii.
-/
open Filter Topology
namespace EinsteinRelation.Correctors

/-- Dyadic decay of a normalized monotone energy gives decay at all radii. -/
theorem tendsto_normalized_monotone_of_dyadic (E : ℝ → ℝ)
    (hE : ∀ R, 0 ≤ E R) (hmono : MonotoneOn E (Set.Ioi 0)) (k : ℕ)
    (hlim : Tendsto (fun n : ℕ => E ((2:ℝ)^n)/((2:ℝ)^n)^k) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => E R/R^k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  have hc : 0 < (2:ℝ)^k := by positivity
  obtain ⟨N, hN⟩ := hlim (ε/(2:ℝ)^k) (div_pos hε hc)
  refine ⟨max 1 ((2:ℝ)^N), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRN : (2:ℝ)^N ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨n, hnR, hRn⟩ := exists_nat_pow_near hR1 (by norm_num : (1:ℝ)<2)
  have hnN : N ≤ n+1 := by
    by_contra h
    have hp : (2:ℝ)^(n+1) ≤ (2:ℝ)^N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hn := hN (n+1) hnN
  have hnp : 0 < (2:ℝ)^(n+1) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hE _) (pow_nonneg hnp.le _))] at hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hE R) (pow_nonneg hR0.le _))]
  calc
    E R/R^k ≤ E ((2:ℝ)^(n+1))/((2:ℝ)^n)^k := by
      apply div_le_div₀ (hE ((2:ℝ)^(n+1)))
      · exact hmono hR0 hnp hRn.le
      · positivity
      · exact pow_le_pow_left₀ (by positivity) hnR k
    _ = (2:ℝ)^k * (E ((2:ℝ)^(n+1))/((2:ℝ)^(n+1))^k) := by
      rw [pow_succ, mul_pow]
      field_simp
    _ < (2:ℝ)^k * (ε/(2:ℝ)^k) := mul_lt_mul_of_pos_left hn hc
    _ = ε := mul_div_cancel₀ ε hc.ne'

end EinsteinRelation.Correctors
