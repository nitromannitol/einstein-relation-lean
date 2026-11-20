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

/-- If a geometric ratio is at least `3/2`, its initial partial sum is at
most three times its last term. -/
theorem sum_pow_le_three_last (x : ℝ) (hx : (3 / 2 : ℝ) ≤ x) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), x ^ m) ≤ 3 * x ^ n := by
  let S : ℝ := ∑ m ∈ Finset.range (n + 1), x ^ m
  have hS : 0 ≤ S := Finset.sum_nonneg (fun m _ => pow_nonneg (by linarith) m)
  have hgeom : S * (x - 1) = x ^ n * x - 1 := by
    simpa only [S, pow_succ] using geom_sum_mul x (n + 1)
  have hslack : 0 ≤ S * (2 * x - 3) := mul_nonneg hS (by linarith)
  have hprod : 0 ≤ x * (3 * x ^ n - S) := by nlinarith
  have hxpos : 0 < x := by linarith
  nlinarith

/-- A shifted geometric sum with ratio `3θ ≥ 3/2` is bounded by three
times its last term. -/
theorem sum_pow_three_mul_shifted_geometric_le
    (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ) (N l : ℕ) (hl : l ≤ N) :
    (∑ m ∈ Finset.Ico l (N + 1), (3 : ℝ) ^ m * θ ^ (m - l)) ≤
      3 * 3 ^ N * θ ^ (N - l) := by
  have hx : (3 / 2 : ℝ) ≤ 3 * θ := by linarith
  have hgeom := sum_pow_le_three_last (3 * θ) hx (N - l)
  have hN : N + 1 - l = (N - l) + 1 := by omega
  calc
    _ = ∑ t ∈ Finset.range (N - l + 1), (3 : ℝ) ^ (l + t) * θ ^ t := by
      rw [Finset.sum_Ico_eq_sum_range, hN]
      simp only [Nat.add_sub_cancel_left]
    _ = (3 : ℝ) ^ l * ∑ t ∈ Finset.range (N - l + 1), (3 * θ) ^ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_add, mul_pow]
      ring
    _ ≤ (3 : ℝ) ^ l * (3 * (3 * θ) ^ (N - l)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by
      rw [mul_pow]
      calc
        _ = 3 * ((3 : ℝ) ^ l * 3 ^ (N - l)) * θ ^ (N - l) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hl]

/-- The weighted geometric decay term is controlled by its final scale. -/
theorem sum_pow_three_mul_geometric_le (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * θ ^ m) ≤
      3 * 3 ^ N * θ ^ N := by
  have h := sum_pow_le_three_last (3 * θ) (by linarith) N
  simpa only [mul_pow, mul_assoc] using h

/-- Interchanging the scale and defect sums controls the weighted geometric
convolution by a single convolution at the final scale. -/
theorem sum_pow_three_mul_geometric_defects_le
    (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ) (N : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ l, 0 ≤ τ l) :
    (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m *
      ∑ l ∈ Finset.range (m + 1), θ ^ (m - l) * τ l) ≤
    3 * 3 ^ N * ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l := by
  calc
    _ = ∑ m ∈ Finset.Ico 0 (N + 1), ∑ l ∈ Finset.Ico 0 (m + 1),
        ((3 : ℝ) ^ m * θ ^ (m - l)) * τ l := by
      simp only [Nat.Ico_zero_eq_range, Finset.mul_sum, mul_assoc]
    _ = ∑ l ∈ Finset.Ico 0 (N + 1), ∑ m ∈ Finset.Ico l (N + 1),
        ((3 : ℝ) ^ m * θ ^ (m - l)) * τ l :=
      (Finset.sum_Ico_Ico_comm 0 (N + 1)
        (fun l m => ((3 : ℝ) ^ m * θ ^ (m - l)) * τ l)).symm
    _ = ∑ l ∈ Finset.range (N + 1),
        (∑ m ∈ Finset.Ico l (N + 1), (3 : ℝ) ^ m * θ ^ (m - l)) * τ l := by
      simp only [Nat.Ico_zero_eq_range, Finset.sum_mul]
    _ ≤ ∑ l ∈ Finset.range (N + 1), (3 * 3 ^ N * θ ^ (N - l)) * τ l := by
      apply Finset.sum_le_sum
      intro l hl
      have hlN : l ≤ N := by simp only [Finset.mem_range] at hl; omega
      exact mul_le_mul_of_nonneg_right
        (sum_pow_three_mul_shifted_geometric_le θ hθ N l hlN) (hτ l)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- Every lower-scale power of three is bounded by the final-scale power
times the geometric decay factor. -/
theorem pow_three_le_last_mul_geometric (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (N l : ℕ) (hl : l ≤ N) :
    (3 : ℝ) ^ l ≤ 3 ^ N * θ ^ (N - l) := by
  have hx : (1 : ℝ) ≤ 3 * θ := by linarith
  have hp : (1 : ℝ) ≤ (3 * θ) ^ (N - l) := one_le_pow₀ hx
  have hmul := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 3 ^ l by positivity)
  have heq : (3 : ℝ) ^ l * (3 * θ) ^ (N - l) = 3 ^ N * θ ^ (N - l) := by
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hl]
  simpa only [mul_one, heq] using hmul

/-- Weighted tails of nonnegative defects are bounded by a single final-scale
geometric convolution. -/
theorem sum_pow_three_mul_tail_le_geometric
    (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ) (N : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ l, 0 ≤ τ l) :
    (∑ m ∈ Finset.range N, (3 : ℝ) ^ m * ∑ l ∈ Finset.Ico m N, τ l) ≤
      (3 / 2 : ℝ) * 3 ^ N *
        ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l := by
  have hθ0 : 0 ≤ θ := by linarith
  have hsum : (∑ l ∈ Finset.range N, (3 : ℝ) ^ l * τ l) ≤
      3 ^ N * ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l := by
    calc
      _ ≤ ∑ l ∈ Finset.range N, (3 ^ N * θ ^ (N - l)) * τ l := by
        apply Finset.sum_le_sum
        intro l hl
        have hlN : l ≤ N := (Finset.mem_range.mp hl).le
        exact mul_le_mul_of_nonneg_right (pow_three_le_last_mul_geometric θ hθ N l hlN) (hτ l)
      _ = 3 ^ N * ∑ l ∈ Finset.range N, θ ^ (N - l) * τ l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
        intro l _ _
        exact mul_nonneg (pow_nonneg hθ0 _) (hτ l)
  calc
    _ ≤ (3 / 2 : ℝ) * ∑ l ∈ Finset.range N, (3 : ℝ) ^ l * τ l :=
      sum_pow_three_mul_tail_le N τ hτ
    _ ≤ (3 / 2 : ℝ) * (3 ^ N *
        ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

/-- Three nested defect contributions are reduced to one geometric
convolution at the final scale. -/
theorem sum_weighted_defect_bounds_le
    (θ α β B D : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (N : ℕ) (τ : ℕ → ℝ) (hτ : ∀ l, 0 ≤ τ l) :
    (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m *
      (α * (∑ l ∈ Finset.Ico m N, τ l) +
       α * (θ ^ m * B + D * ∑ l ∈ Finset.range (m + 1), θ ^ (m - l) * τ l) +
       β * ∑ l ∈ Finset.Ico m N, τ l)) ≤
    3 * 3 ^ N * ((α * B) * θ ^ N + (α + β + α * D) *
      ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l) := by
  let tail : ℝ := ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * ∑ l ∈ Finset.Ico m N, τ l
  let base : ℝ := ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * θ ^ m
  let conv : ℝ := ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m *
    ∑ l ∈ Finset.range (m + 1), θ ^ (m - l) * τ l
  let last : ℝ := ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * τ l
  let W : ℝ := (3 : ℝ) ^ N
  have hθ0 : 0 ≤ θ := by linarith
  have hlast : 0 ≤ last := Finset.sum_nonneg (fun l _ => mul_nonneg (pow_nonneg hθ0 _) (hτ l))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have htail : tail ≤ (3 / 2 : ℝ) * W * last := by
    dsimp only [tail, W, last]
    rw [Finset.sum_range_succ]
    simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero]
    exact sum_pow_three_mul_tail_le_geometric θ hθ N τ hτ
  have htail' : tail ≤ 3 * W * last := by
    have hnonneg := mul_nonneg hW hlast
    nlinarith
  have hbase : base ≤ 3 * W * θ ^ N := by
    exact sum_pow_three_mul_geometric_le θ hθ N
  have hconv : conv ≤ 3 * W * last := by
    exact sum_pow_three_mul_geometric_defects_le θ hθ N τ hτ
  have hident :
      (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m *
        (α * (∑ l ∈ Finset.Ico m N, τ l) +
         α * (θ ^ m * B + D * ∑ l ∈ Finset.range (m + 1), θ ^ (m - l) * τ l) +
         β * ∑ l ∈ Finset.Ico m N, τ l)) =
      (α + β) * tail + (α * B) * base + (α * D) * conv := by
    let t : ℕ → ℝ := fun m => ∑ l ∈ Finset.Ico m N, τ l
    let v : ℕ → ℝ := fun m => ∑ l ∈ Finset.range (m + 1), θ ^ (m - l) * τ l
    change (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m *
      (α * t m + α * (θ ^ m * B + D * v m) + β * t m)) =
      (α + β) * (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * t m) +
      (α * B) * (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * θ ^ m) +
      (α * D) * (∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ m * v m)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hident]
  calc
    _ ≤ (α + β) * (3 * W * last) + (α * B) * (3 * W * θ ^ N) +
        (α * D) * (3 * W * last) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left htail' (add_nonneg hα hβ))
        (mul_le_mul_of_nonneg_left hbase (mul_nonneg hα hB)))
        (mul_le_mul_of_nonneg_left hconv (mul_nonneg hα hD))
    _ = _ := by dsimp only [W, last]; ring

end EinsteinFull.Homogenization
