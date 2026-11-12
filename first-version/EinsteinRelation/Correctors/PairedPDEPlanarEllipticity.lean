import EinsteinRelation.Correctors.PairedPDEInverse
import EinsteinRelation.Correctors.PairedPDEPlanarRotation

/-! # Ellipticity of the planar dual equation

Source: `paper/main.tex:874–883`. Rotating the inverse of an anisotropic
symmetric elliptic coefficient preserves its ellipticity parameter. This
is the coefficient in the scalar equation for the independent skew entry.
-/

namespace EinsteinRelation.Correctors

/-- The quadratic form of the rotated inverse is the inverse quadratic
form evaluated at the rotated vector. Source: `paper/main.tex:877–880`. -/
theorem dot_planar_dual (a : Mat 2) (v : Vec 2) :
    dot v ((planarRotation.transpose * a⁻¹ * planarRotation).mulVec v) =
      dot (planarRotation.mulVec v) (a⁻¹.mulVec (planarRotation.mulVec v)) := by
  change dotProduct v _ = dotProduct _ _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- No invertibility or isotropy assumption is added to the planar dual
coefficient: its bounds follow from the original quadratic bounds.
Source: `paper/main.tex:877–883`. -/
theorem planar_dual_quadratic_bounds (a : Mat 2) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hs : a.transpose = a)
    (ha : ∀ v : Vec 2, c * euclideanSq v ≤ dot v (a.mulVec v) ∧
      dot v (a.mulVec v) ≤ C * euclideanSq v) (v : Vec 2) :
    C⁻¹ * euclideanSq v ≤
      dot v ((planarRotation.transpose * a⁻¹ * planarRotation).mulVec v) ∧
    dot v ((planarRotation.transpose * a⁻¹ * planarRotation).mulVec v) ≤
      c⁻¹ * euclideanSq v := by
  rw [dot_planar_dual]
  simpa only [euclideanSq_planarRotation] using
    inverse_euclidean_quadratic_bounds a hc hC hs ha (planarRotation.mulVec v)

/-- The planar dual is symmetric whenever the original coefficient is.
Source: `paper/main.tex:877–883`. -/
theorem planar_dual_symmetric (a : Mat 2) (hs : a.transpose = a) :
    (planarRotation.transpose * a⁻¹ * planarRotation).transpose =
      planarRotation.transpose * a⁻¹ * planarRotation := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hs, Matrix.mul_assoc]

/-- The manuscript's reciprocal ellipticity bounds persist under the
planar dual operation. Source: `paper/main.tex:877–883`. -/
theorem isElliptic_planar_dual {L : ℝ} (hL : 0 < L)
    {a : Vec 2 → Mat 2} (ha : IsElliptic L a) :
    IsElliptic L (fun x => planarRotation * (a x)⁻¹ * planarRotation.transpose) := by
  intro x
  dsimp only
  rw [← planar_dual_orientation]
  refine ⟨planar_dual_symmetric (a x) (ha x).1, ?_⟩
  intro v
  simpa only [inv_inv] using planar_dual_quadratic_bounds (a x)
    (inv_pos.mpr hL) hL (ha x).1 ((ha x).2) v

end EinsteinRelation.Correctors
