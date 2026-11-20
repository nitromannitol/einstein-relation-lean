import EinsteinFull.Homogenization.GeometricDefectSumsBeforeScale

/-!
# The last defect in a geometric sum

The change from a preceding-scale slope contributes one last response defect,
which is absorbed into the geometric convolution in the optimizer flatness
estimate of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.15.
-/

namespace EinsteinFull.Homogenization

/-- A shifted convolution and the last defect are bounded by the unshifted
geometric convolution. -/
theorem shifted_geometric_and_last_defect_le (θ M D : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hM : 0 ≤ M)
    (n : ℕ) (τ : ℕ → ℝ) (hτ : ∀ l, 0 ≤ τ l) :
    2 * M * (θ ^ (n + 1) + ∑ l ∈ Finset.range (n + 1),
      θ ^ (n + 1 - l) * τ l) + 2 * D ^ 2 * τ n ≤
      (2 * M + 2 * D ^ 2) * (θ ^ n + ∑ l ∈ Finset.range (n + 1),
        θ ^ (n - l) * τ l) := by
  let S : ℝ := θ ^ n + ∑ l ∈ Finset.range (n + 1), θ ^ (n - l) * τ l
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (pow_nonneg hθ0 _) (Finset.sum_nonneg fun l _ =>
      mul_nonneg (pow_nonneg hθ0 _) (hτ l))
  have hpow : θ ^ (n + 1) ≤ θ ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hθ0 _) hθ1
  have hsum : (∑ l ∈ Finset.range (n + 1), θ ^ (n + 1 - l) * τ l) ≤
      ∑ l ∈ Finset.range (n + 1), θ ^ (n - l) * τ l := by
    apply Finset.sum_le_sum
    intro l hl
    have heq : n + 1 - l = (n - l) + 1 := by have := Finset.mem_range.mp hl; omega
    rw [heq, pow_succ]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg hθ0 _) hθ1) (hτ l)
  have hlast : τ n ≤ S := by
    dsimp [S]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, one_mul]
    have hs : 0 ≤ ∑ l ∈ Finset.range n, θ ^ (n - l) * τ l :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (pow_nonneg hθ0 _) (hτ l))
    linarith [pow_nonneg hθ0 n]
  have hshift : θ ^ (n + 1) + ∑ l ∈ Finset.range (n + 1),
      θ ^ (n + 1 - l) * τ l ≤ S := by dsimp [S]; linarith
  have h1 := mul_le_mul_of_nonneg_left hshift (show 0 ≤ 2 * M by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlast (show 0 ≤ 2 * D ^ 2 by positivity)
  nlinarith

end EinsteinFull.Homogenization
