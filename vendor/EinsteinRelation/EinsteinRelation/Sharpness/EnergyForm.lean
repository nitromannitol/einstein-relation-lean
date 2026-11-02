import EinsteinRelation.Sharpness.InverseIdentification
import EinsteinRelation.Sharpness.Energy

/-! # Quadratic form of the sharpness coefficient

`paper/main.tex`, lines 1225–1231: the coefficient `a = j J⁻¹ J⁻ᵀ` is symmetric and
uniformly elliptic. Here `inverseCandidate i g` is `B = J⁻¹` (`inverseCandidate_eq_inv`),
so `coefficient i g = j B Bᵀ` and its Euclidean quadratic form is `j |Bᵀ ξ|²`.

The first identity uses no hypothesis on `1 + gᵢ`. Positivity uses only the inverse relation
`B J = 1` from `RankOne` (valid since `0 < jacobianFactor`), which gives injectivity of `Bᵀ`;
no separate invertibility input is added. This file proves positive quadratic forms only,
not the uniform constants.
-/

namespace EinsteinRelation.Sharpness

/-- Scalar multiples pass through the coordinate scalar product. -/
private theorem dot_smul_right {d : ℕ} (c : ℝ) (x y : Vec d) :
    dot x (c • y) = c * dot x y := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For `w = Bᵀ ξ`, the pairing `ξ · (B w)` equals the squared norm `|Bᵀ ξ|²`. -/
private theorem dot_mulVec_transpose {d : ℕ} (B : Mat d) (ξ : Vec d) :
    dot ξ (B.mulVec (B.transpose.mulVec ξ)) = euclideanSq (B.transpose.mulVec ξ) := by
  have h1 : dot ξ (B.mulVec (B.transpose.mulVec ξ)) =
      dotProduct (Matrix.vecMul ξ B) (B.transpose.mulVec ξ) :=
    Matrix.dotProduct_mulVec ξ B (B.transpose.mulVec ξ)
  have h2 : Matrix.vecMul ξ B = B.transpose.mulVec ξ := (Matrix.mulVec_transpose B ξ).symm
  rw [h1, h2]
  rfl

/-- The coefficient quadratic form is `j |Bᵀ ξ|²` for every `i`, `g`, and `ξ`, including
`d = 0`. No hypothesis on `1 + gᵢ` is needed. Source: `paper/main.tex`, lines 1225–1231. -/
theorem coefficient_quadratic_form {d : ℕ} (i : Fin d) (g ξ : Vec d) :
    dot ξ ((coefficient i g).mulVec ξ) =
      jacobianFactor i g * euclideanSq ((inverseCandidate i g).transpose.mulVec ξ) := by
  have hcoef : (coefficient i g).mulVec ξ = jacobianFactor i g •
      (inverseCandidate i g).mulVec ((inverseCandidate i g).transpose.mulVec ξ) := by
    rw [coefficient, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  rw [hcoef, dot_smul_right, dot_mulVec_transpose]

/-- Positivity of the coefficient quadratic form when `1 + gᵢ > 0` and `ξ ≠ 0`.
The transpose candidate `Bᵀ` is injective, since `Jᵀ Bᵀ = 1` from `B J = 1`.
Source: `paper/main.tex`, lines 1225–1231. -/
theorem coefficient_quadratic_pos {d : ℕ} (i : Fin d) (g ξ : Vec d)
    (hj : 0 < jacobianFactor i g) (hξ : ξ ≠ 0) :
    0 < dot ξ ((coefficient i g).mulVec ξ) := by
  have hBJ : inverseCandidate i g * jacobian i g = 1 :=
    inverseCandidate_mul_jacobian i g hj.ne'
  have hT : (jacobian i g).transpose * (inverseCandidate i g).transpose = 1 := by
    rw [← Matrix.transpose_mul, hBJ, Matrix.transpose_one]
  have hinj : (inverseCandidate i g).transpose.mulVec ξ ≠ 0 := by
    intro h
    have hid : (jacobian i g).transpose.mulVec
        ((inverseCandidate i g).transpose.mulVec ξ) = ξ := by
      rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
    have hξ0 : ξ = 0 := by
      rw [← hid, h, Matrix.mulVec_zero]
    exact hξ hξ0
  rw [coefficient_quadratic_form i g ξ]
  exact mul_pos hj ((euclideanSq_pos_iff _).2 hinj)

end EinsteinRelation.Sharpness
