import EinsteinRelation.Correctors.CoordinateMomentProjections
open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:733-745`. A common entry bound controls the
Frobenius norm with the exact dimension factor. -/
theorem frobeniusNorm_le_dimension_mul {d : ℕ} (A : Mat d) (M : ℝ)
    (hM : 0 ≤ M) (hA : ∀ j k, |A j k| ≤ M) :
    frobeniusNorm A ≤ (d : ℝ) * M := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  unfold frobeniusSq
  calc
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, M ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have h := pow_le_pow_left₀ (abs_nonneg (A j k)) (hA j k) 2
      nlinarith [sq_abs (A j k)]
    _ = _ := by simp; ring
end EinsteinRelation.Correctors
