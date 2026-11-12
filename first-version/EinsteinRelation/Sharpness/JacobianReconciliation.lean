import EinsteinRelation.Sharpness.JacobianAlgebra
import EinsteinRelation.Sharpness.MatrixDefs
import EinsteinRelation.Sharpness.RankOne
import EinsteinRelation.Sharpness.InverseIdentification
import EinsteinRelation.TimeChange.Pairing

/-! # Reconciling the sharpness Jacobian with the rank-one coefficient

`JacobianAlgebra` states the sharpness Jacobian `sharpJ`, its factor `sharpJac` and the
coefficient `sharpCoeff` directly from `paper/main.tex`, `eq.sharp-map` and
`eq.sharp-coefficients`. `MatrixDefs` defines the same objects as `jacobian`, `jacobianFactor`,
`inverseCandidate` and `coefficient` through the explicit rank-one formula. This file identifies
the two families and restates the `JacobianAlgebra` results for `coefficient`.

Where `RankOne` or `InverseIdentification` already proves a statement, the restatement is proved
from that lemma. The remaining restatements are transported along `sharpCoeff_eq_coefficient`.
-/

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-! ### Identification of the Jacobian, its factor, and the coefficient -/

/-- The `JacobianAlgebra` Jacobian `1 + vecMulVec e g` is the rank-one Jacobian `1 + e ⊗ g`. -/
theorem sharpJ_eq_jacobian (i : Fin d) (g : Vec d) : sharpJ i g = jacobian i g := by
  ext k l
  simp [sharpJ, jacobian, outer, Matrix.vecMulVec_apply]

/-- The `JacobianAlgebra` Jacobian factor is the scalar `1 + gᵢ` of `MatrixDefs`. -/
theorem sharpJac_eq_jacobianFactor (i : Fin d) (g : Vec d) :
    sharpJac i g = jacobianFactor i g := rfl

/-- Under the gradient bound `|g| ≤ 1/4`, the Jacobian factor `1 + gᵢ` is nonzero. -/
theorem jacobianFactor_ne_zero_of_norm_le (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : jacobianFactor i g ≠ 0 := by
  have h : (0 : ℝ) < jacobianFactor i g := by linarith [(jacobianFactor_bounds i g hg).1]
  exact h.ne'

/-- The inverse of the `JacobianAlgebra` Jacobian is the rank-one candidate inverse. -/
theorem sharpJ_inv_eq_inverseCandidate (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) :
    (sharpJ i g)⁻¹ = inverseCandidate i g := by
  rw [sharpJ_eq_jacobian, inverseCandidate_eq_inv i g (jacobianFactor_ne_zero_of_norm_le i g hg)]

/-- The `JacobianAlgebra` coefficient `jac g • (J g)⁻¹ ((J g)⁻¹)ᵀ` is the rank-one `coefficient`
under the gradient bound. -/
theorem sharpCoeff_eq_coefficient (i : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    sharpCoeff i g = coefficient i g := by
  unfold sharpCoeff coefficient
  rw [sharpJ_inv_eq_inverseCandidate i g hg, sharpJac_eq_jacobianFactor]

/-! ### `JacobianAlgebra` results restated for `coefficient`

The transpose identity needs no hypothesis and is `RankOne.coefficient_transpose`. -/

/-- Harmonic identity `a (e + ∇ψ) = e` for the rank-one coefficient. -/
theorem coefficient_mulVec_harmonic (i : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    (coefficient i g).mulVec (unitVector i + g) = unitVector i :=
  coefficient_mulVec i g (jacobianFactor_ne_zero_of_norm_le i g hg)

/-- Diagonal entry `a₁₁ = 1 - g₁ + |g|² / (1 + g₁)` of the rank-one coefficient. -/
theorem coefficient_apply_self (i : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4) :
    coefficient i g i i = 1 - g i + euclideanSq g / jacobianFactor i g := by
  unfold jacobianFactor
  exact coefficient_diagonal i g (jacobianFactor_ne_zero_of_norm_le i g hg)

/-- The pairing `dot (a e) g = 1 - a₁₁` of the rank-one coefficient. -/
theorem coefficient_dot_mulVec_unitVector (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) :
    dot ((coefficient i g).mulVec (unitVector i)) g = 1 - coefficient i g i i := by
  rw [← sharpCoeff_eq_coefficient i g hg]
  exact sharpCoeff_dot_mulVec_unitVector i g hg

/-- Uniform ellipticity of the rank-one coefficient with the constants `1/4` and `20/9`. -/
theorem coefficient_uniformlyElliptic (i : Fin d) (g : Vec d) (hg : euclideanNorm g ≤ 1 / 4)
    (ξ : Vec d) :
    1 / 4 * euclideanSq ξ ≤ dot ξ ((coefficient i g).mulVec ξ) ∧
      dot ξ ((coefficient i g).mulVec ξ) ≤ 20 / 9 * euclideanSq ξ := by
  rw [← sharpCoeff_eq_coefficient i g hg]
  exact sharpCoeff_uniformlyElliptic i g hg ξ

end EinsteinRelation.Sharpness
