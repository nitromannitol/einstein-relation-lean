import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Geometric recurrences

Iteration of the one-step fluctuation estimate used in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 2.13.
-/

namespace EinsteinFull.Homogenization

/-- A one-step recurrence with a nonnegative multiplier is bounded by its
initial value and a geometrically weighted sum of errors. -/
theorem le_geometric_weighted_sum (a b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ n, a (n + 1) ≤ t * a n + b n) (n : ℕ) :
    a n ≤ t ^ n * a 0 + ∑ k ∈ Finset.range n, t ^ (n - 1 - k) * b k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      a (n + 1) ≤ t * a n + b n := h n
      _ ≤ t * (t ^ n * a 0 + ∑ k ∈ Finset.range n, t ^ (n - 1 - k) * b k) + b n :=
        by simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left ih ht) (b n)
      _ = t ^ (n + 1) * a 0 + ∑ k ∈ Finset.range (n + 1),
          t ^ (n + 1 - 1 - k) * b k := by
        rw [Finset.sum_range_succ]
        have hs : (∑ k ∈ Finset.range n, t ^ (n + 1 - 1 - k) * b k) =
            t * ∑ k ∈ Finset.range n, t ^ (n - 1 - k) * b k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have he : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
          rw [he, pow_succ]
          ring
        rw [hs]
        simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, pow_succ]
        ring

end EinsteinFull.Homogenization
