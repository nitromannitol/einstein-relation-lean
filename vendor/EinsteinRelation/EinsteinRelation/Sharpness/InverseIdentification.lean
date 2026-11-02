import EinsteinRelation.Sharpness.RankOne
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Identifying the candidate with the actual inverse

`paper/main.tex:1220–1226,1257–1259`. These identities connect the explicit
rank-one formula to the literal determinant and inverse in the manuscript.
-/

namespace EinsteinRelation.Sharpness

/-- The candidate is the actual nonsingular matrix inverse. -/
theorem inverseCandidate_eq_inv {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) :
    inverseCandidate i g = (jacobian i g)⁻¹ :=
  (Matrix.inv_eq_right_inv (jacobian_mul_inverseCandidate i g hj)).symm

/-- The coefficient agrees with the manuscript's inverse-Jacobian formula. -/
theorem coefficient_eq_inverse_formula {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) :
    coefficient i g = jacobianFactor i g •
      ((jacobian i g)⁻¹ * ((jacobian i g)⁻¹).transpose) := by
  rw [coefficient, inverseCandidate_eq_inv i g hj]

/-- The determinant is exactly the claimed rank-one scalar factor. -/
theorem det_jacobian {d : ℕ} (i : Fin d) (g : Vec d) :
    (jacobian i g).det = jacobianFactor i g := by
  have htensor : outer (unitVector i) g =
      Matrix.replicateCol Unit (unitVector i) * Matrix.replicateRow Unit g := by
    ext k l
    simp only [outer, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Fintype.sum_unique]
  rw [jacobian, htensor, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [jacobianFactor, dotProduct, unitVector, Pi.single_apply]

end EinsteinRelation.Sharpness
