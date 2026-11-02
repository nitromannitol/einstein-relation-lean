import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.Sharpness.MatrixDefs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-! # Explicit Euclidean pairing and small-gradient Jacobian bounds

`paper/main.tex`, the Euclidean norm in the notation section (line 194) and the
sharpness Jacobian `J = I + e₁ ⊗ ∇ψ`, `j = 1 + ∂₁ψ` with `3/4 ≤ j ≤ 5/4` when
`‖J - I‖ ≤ 1/4` (lines 1218–1231, `eq.sharp-map`, `eq.sharp-coefficients`).

All norms are the explicit coordinate expressions `euclideanNorm`, `euclideanSq`
and `dot` from `Environment/Basic.lean`. The default supremum norm on `Fin d → ℝ`
is never used. Cauchy–Schwarz is taken directly on the coordinate sums.
-/

open scoped BigOperators

namespace EinsteinRelation.TimeChange

/-- The squared Euclidean norm as a coordinate sum of squares. -/
private theorem pairing_euclideanSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    euclideanSq x = ∑ i, x i ^ 2 := by
  unfold euclideanSq dot
  exact Finset.sum_congr rfl fun i _ => (pow_two (x i)).symm

/-- The squared Euclidean norm is nonnegative. -/
private theorem pairing_euclideanSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ euclideanSq x := by
  rw [pairing_euclideanSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- Cauchy–Schwarz for the Euclidean pairing, on the explicit coordinate sums. -/
theorem abs_dot_le_euclideanNorm {d : ℕ} (x y : Vec d) :
    |dot x y| ≤ euclideanNorm x * euclideanNorm y := by
  unfold euclideanNorm
  rw [← Real.sqrt_mul (pairing_euclideanSq_nonneg x)]
  apply Real.abs_le_sqrt
  rw [pairing_euclideanSq_eq_sum_sq x, pairing_euclideanSq_eq_sum_sq y]
  unfold dot
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

/-- The manuscript's squared norm is the square of the Euclidean norm. -/
theorem euclideanSq_eq_sq_euclideanNorm {d : ℕ} (g : Vec d) :
    euclideanSq g = euclideanNorm g ^ 2 := by
  unfold euclideanNorm
  rw [Real.sq_sqrt (pairing_euclideanSq_nonneg g)]

end EinsteinRelation.TimeChange

namespace EinsteinRelation.Sharpness

/-- Each coordinate is bounded by the Euclidean norm of the gradient. -/
private theorem pairing_abs_coord_le_euclideanNorm {d : ℕ} (i : Fin d) (g : Vec d) :
    |g i| ≤ euclideanNorm g := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [pow_two]
  exact Finset.single_le_sum (f := fun j => g j * g j)
    (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)

/-- For a gradient of Euclidean norm at most `1/4`, the Jacobian determinant
factor `1 + gᵢ` lies in `[3/4, 5/4]`. -/
theorem jacobianFactor_bounds {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ jacobianFactor i g ∧ jacobianFactor i g ≤ (5 / 4 : ℝ) := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp ((pairing_abs_coord_le_euclideanNorm i g).trans hg)
  unfold jacobianFactor
  constructor <;> linarith

end EinsteinRelation.Sharpness
