import Homogenization.Besov.Poincare.Projection
import Homogenization.Besov.Duality.GlobalComparison

/-!
# Truncation of negative Besov norms

The small scales of a negative Besov norm can be controlled by an `L²` norm.
This is the truncation used in the multiscale Poincaré estimate of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Corollary 1.14.
-/

open scoped ENNReal
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- The negative Besov norm is controlled by its first `N` scales and an
explicit geometric remainder involving the normalized cube `L²` norm. -/
theorem cubeBesovCircNorm_one_two_le_scales_add_tail
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) 1 u ≤
      (∑ j ∈ Finset.range N, cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) u j) +
      (cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) u) *
        ((1 / 3 : ℝ) ^ N / (1 - 1 / 3)) := by
  let F : ℕ → ℝ := fun j => cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) u j
  let A : ℝ := cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) u
  have hA : 0 ≤ A := mul_nonneg (cubeBesovScaleWeight_nonneg _ _) (cubeLpNorm_nonneg _ _ _)
  have hF (j : ℕ) : 0 ≤ F j := cubeBesovCircDepthSeminorm_nonneg _ _ _ _ _
  have hbound (j : ℕ) : F j ≤ A * (1 / 3 : ℝ) ^ j := by
    have h := cubeBesovCircDepthSeminorm_le_scaleWeight_neg_mul_geom_mul_cubeLpNorm
      Q 1 (2 : ℝ≥0∞) u j (by norm_num) (by norm_num) hu
    simp only [Real.rpow_neg_one] at h
    dsimp only [F, A]
    convert h using 1; ring
  apply cubeBesovCircNorm_le_of_forall_partialNorm_le Q 1 (2 : ℝ≥0∞) 1 u (by norm_num)
  intro M
  rw [cubeBesovCircPartialNorm_one_eq_sum]
  change (∑ j ∈ Finset.range (M + 1), F j) ≤
    (∑ j ∈ Finset.range N, F j) + A * ((1 / 3 : ℝ) ^ N / (1 - 1 / 3))
  by_cases hNM : N ≤ M + 1
  · rw [← Finset.sum_range_add_sum_Ico F hNM]
    have htail : (∑ j ∈ Finset.Ico N (M + 1), F j) ≤
        A * ((1 / 3 : ℝ) ^ N / (1 - 1 / 3)) := by
      calc
        ∑ j ∈ Finset.Ico N (M + 1), F j ≤
          ∑ j ∈ Finset.Ico N (M + 1), A * (1 / 3 : ℝ) ^ j :=
          Finset.sum_le_sum (fun j _ => hbound j)
        _ = A * ∑ j ∈ Finset.Ico N (M + 1), (1 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
        _ ≤ A * ((1 / 3 : ℝ) ^ N / (1 - 1 / 3)) := by
          exact mul_le_mul_of_nonneg_left
            (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)) hA
    linarith
  · have hle : M + 1 ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNM)
    have hsum : (∑ j ∈ Finset.range (M + 1), F j) ≤ ∑ j ∈ Finset.range N, F j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle) (fun j _ _ => hF j)
    have htail : 0 ≤ A * ((1 / 3 : ℝ) ^ N / (1 - 1 / 3)) := by positivity
    linarith

end EinsteinFull.Homogenization
