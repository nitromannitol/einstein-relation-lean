import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The Euclidean norm on the coordinate carrier

The source norm (`paper/main.tex:194`, also used in `eq.main-rate`) is the
square root of the sum of squared coordinates. This bridge uses Mathlib's
Euclidean space locally and leaves the default norm on `Vec d` unchanged.
-/

open WithLp

namespace EinsteinRelation.TimeChange

/-- The manuscript norm agrees with the Hilbert space norm after transport. -/
theorem euclideanNorm_eq_norm_toLp {d : ℕ} (x : Vec d) :
    euclideanNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change x i * x i = ‖x i‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs, pow_two]

/-- Triangle inequality in the actual norm used by the paper. -/
theorem euclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_toLp, euclideanNorm_eq_norm_toLp,
    euclideanNorm_eq_norm_toLp]
  exact norm_add_le (toLp 2 x) (toLp 2 y)

/-- Homogeneity in the actual norm used by the paper. -/
theorem euclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  rw [euclideanNorm_eq_norm_toLp, euclideanNorm_eq_norm_toLp]
  exact norm_smul c (toLp 2 x : EuclideanSpace ℝ (Fin d))

end EinsteinRelation.TimeChange
