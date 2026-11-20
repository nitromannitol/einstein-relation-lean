import EinsteinFull.Homogenization.GeometricDefectSums

/-!
# Geometric multiscale sums using earlier defects

The finite-scale sums in the optimizer flatness estimate involve only defect
indices below the parent scale, as in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.15.
-/

namespace EinsteinFull.Homogenization

/-- A multiscale majorant involving only earlier defects is bounded by a
single geometric convolution up to the preceding scale. -/
theorem multiscale_majorant_bound_le_geometric_before
    (θ α β B D A : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hB : 0 ≤ B) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (N : ℕ) (τ : ℕ → ℝ) (hτ : ∀ l, 0 ≤ τ l) :
    let T := fun j => α * (∑ l ∈ Finset.Ico (N - j) N, τ l) +
      α * (θ ^ (N - j) * B + D * ∑ l ∈ Finset.range (N - j), θ ^ (N - j - l) * τ l) +
      β * ∑ l ∈ Finset.Ico (N - j) N, τ l
    2 * A + 2 * ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
      ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T j) ≤
    (3 : ℝ) ^ (2 * N) * (2 * A + 9 * (α * B + α + β + α * D)) *
      (θ ^ N + ∑ l ∈ Finset.range N, θ ^ (N - l) * τ l) := by
  intro T
  let σ : ℕ → ℝ := fun l => if l < N then τ l else 0
  let T' := fun j => α * (∑ l ∈ Finset.Ico (N - j) N, σ l) +
      α * (θ ^ (N - j) * B + D * ∑ l ∈ Finset.range (N - j + 1), θ ^ (N - j - l) * σ l) +
      β * ∑ l ∈ Finset.Ico (N - j) N, σ l
  have hθ0 : 0 ≤ θ := by linarith
  have hσ (l : ℕ) : 0 ≤ σ l := by
    dsimp [σ]
    split
    · exact hτ l
    · exact le_rfl
  have htail (j : ℕ) : (∑ l ∈ Finset.Ico (N - j) N, τ l) =
      ∑ l ∈ Finset.Ico (N - j) N, σ l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlN := (Finset.mem_Ico.mp hl).2
    simp [σ, hlN]
  have hrange (j : ℕ) : (∑ l ∈ Finset.range (N - j), θ ^ (N - j - l) * τ l) ≤
      ∑ l ∈ Finset.range (N - j + 1), θ ^ (N - j - l) * σ l := by
    rw [Finset.sum_range_succ]
    have heq : (∑ l ∈ Finset.range (N - j), θ ^ (N - j - l) * τ l) =
        ∑ l ∈ Finset.range (N - j), θ ^ (N - j - l) * σ l := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlN : l < N := lt_of_lt_of_le (Finset.mem_range.mp hl) (Nat.sub_le _ _)
      simp [σ, hlN]
    rw [heq]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hθ0 _) (hσ _))
  have hT (j : ℕ) : T j ≤ T' j := by
    dsimp only [T, T']
    rw [htail j]
    have h := mul_le_mul_of_nonneg_left (hrange j) hD
    nlinarith [mul_le_mul_of_nonneg_left h hα]
  have hsum : (∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * σ l) =
      ∑ l ∈ Finset.range N, θ ^ (N - l) * τ l := by
    rw [Finset.sum_range_succ]
    simp only [σ, lt_irrefl, ↓reduceIte, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    simp [Finset.mem_range.mp hl]
  have hgeom := multiscale_majorant_bound_le_geometric θ α β B D A hθ hα hβ hB hD hA N σ hσ
  change 2 * A + 2 * ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T' j) ≤ _ at hgeom
  rw [hsum] at hgeom
  calc
    _ ≤ 2 * A + 2 * ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T' j) := by
      gcongr with j hj
      exact hT j
    _ ≤ _ := hgeom

end EinsteinFull.Homogenization
