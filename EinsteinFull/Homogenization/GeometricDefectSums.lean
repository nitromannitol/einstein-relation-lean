import EinsteinFull.Homogenization.WeightedSquareRoot
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Geometric summation of defect tails

Interchanging finite sums reduces weighted defect tails to a single geometric
sum, as used in the multiscale flatness argument of Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2.
-/

namespace EinsteinFull.Homogenization

/-- The sum of powers of three up to `n` is bounded by `3/2` times the last
power. -/
theorem sum_pow_three_le (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), (3 : ℝ) ^ m) ≤ (3 / 2 : ℝ) * 3 ^ n := by
  have h := geom_sum_mul (3 : ℝ) (n + 1)
  rw [pow_succ] at h
  nlinarith

/-- Geometrically weighted tails of a nonnegative finite sequence are
controlled by a single geometric weighted sum. -/
theorem sum_pow_three_mul_tail_le (N : ℕ) (τ : ℕ → ℝ) (hτ : ∀ l, 0 ≤ τ l) :
    (∑ m ∈ Finset.range N, (3 : ℝ) ^ m * ∑ l ∈ Finset.Ico m N, τ l) ≤
      (3 / 2 : ℝ) * ∑ l ∈ Finset.range N, (3 : ℝ) ^ l * τ l := by
  calc
    _ = ∑ m ∈ Finset.Ico 0 N, ∑ l ∈ Finset.Ico m N, (3 : ℝ) ^ m * τ l := by
      simp only [Nat.Ico_zero_eq_range, Finset.mul_sum]
    _ = ∑ l ∈ Finset.Ico 0 N, ∑ m ∈ Finset.Ico 0 (l + 1), (3 : ℝ) ^ m * τ l :=
      Finset.sum_Ico_Ico_comm 0 N (fun m l => (3 : ℝ) ^ m * τ l)
    _ = ∑ l ∈ Finset.range N, (∑ m ∈ Finset.range (l + 1), (3 : ℝ) ^ m) * τ l := by
      simp only [Nat.Ico_zero_eq_range, Finset.sum_mul]
    _ ≤ ∑ l ∈ Finset.range N, ((3 / 2 : ℝ) * 3 ^ l) * τ l := by
      exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (sum_pow_three_le l) (hτ l))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

end EinsteinFull.Homogenization
