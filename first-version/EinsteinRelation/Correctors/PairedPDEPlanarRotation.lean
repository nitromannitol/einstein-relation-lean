import EinsteinRelation.Correctors.EllipticInvertibility

/-! # Rotation in the planar paired flux equation

Source: `paper/main.tex:877–880`. -/

namespace EinsteinRelation.Correctors

/-- The ninety-degree rotation matrix in the planar flux equation.
Source: `paper/main.tex:877–880`. -/
def planarRotation : Mat 2 := !![0, -1; 1, 0]

/-- Rotation preserves the actual Euclidean quadratic form.
Source: `paper/main.tex:877–880`. -/
theorem euclideanSq_planarRotation (v : Vec 2) :
    euclideanSq (planarRotation.mulVec v) = euclideanSq v := by
  simp [planarRotation, euclideanSq, dot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The rotation agrees with the coordinate convention in the weak skew equation.
Source: `paper/main.tex:877–880`. -/
theorem planarRotation_mulVec (v : Vec 2) :
    planarRotation.mulVec v = ![-v 1, v 0] := by
  ext j
  fin_cases j <;> simp [planarRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Two successive quarter-turns negate the vector.
Source: `paper/main.tex:877–880`. -/
theorem planarRotation_twice (v : Vec 2) :
    planarRotation.mulVec (planarRotation.mulVec v) = -v := by
  simp only [planarRotation_mulVec]
  ext j
  fin_cases j <;> simp

/-- Transpose rotation is the negative rotation.
Source: `paper/main.tex:877–880`. -/
theorem planarRotation_transpose_mulVec (v : Vec 2) :
    planarRotation.transpose.mulVec v = -(planarRotation.mulVec v) := by
  ext j
  fin_cases j <;>
    simp [planarRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]

/-- The rotated inverse sends the rotated original flux back to the rotated
ordinary gradient. Invertibility follows from genuine ellipticity downstream.
Source: `paper/main.tex:877–880`. -/
theorem planar_dual_flux (a : Mat 2) (ha : IsUnit a.det) (v : Vec 2) :
    (planarRotation.transpose * a⁻¹ * planarRotation).mulVec
      (planarRotation.mulVec (a.mulVec v)) = planarRotation.mulVec v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, planarRotation_twice,
    Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha,
    Matrix.one_mulVec, Matrix.mulVec_neg, planarRotation_transpose_mulVec, neg_neg]

/-- Both standard orientations give the manuscript's same dual matrix.
Source: `paper/main.tex:877–880`. -/
theorem planar_dual_orientation (a : Mat 2) :
    planarRotation.transpose * a⁻¹ * planarRotation =
      planarRotation * a⁻¹ * planarRotation.transpose := by
  have ht : planarRotation.transpose = -planarRotation := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planarRotation, Matrix.transpose_apply]
  simp only [ht, neg_mul, mul_neg]

end EinsteinRelation.Correctors
