import EinsteinRelation.Correctors.EllipticInvertibility
import EinsteinRelation.Correctors.EllipticOperatorBound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # Quadratic bounds for an inverse elliptic matrix

Source: `paper/main.tex:877–883`. Inverse bounds use the actual symmetric
anisotropic matrix; no scalar or isotropic specialization is made.
-/

namespace EinsteinRelation.Correctors

/-- Inverting an anisotropic symmetric elliptic matrix reverses its
quadratic bounds. Source: `paper/main.tex:877–883`. -/
theorem inverse_euclidean_quadratic_bounds {d : ℕ} (a : Mat d) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hs : a.transpose = a)
    (ha : ∀ v : Vec d, c * euclideanSq v ≤ dot v (a.mulVec v) ∧
      dot v (a.mulVec v) ≤ C * euclideanSq v) (v : Vec d) :
    C⁻¹ * euclideanSq v ≤ dot v (a⁻¹.mulVec v) ∧
      dot v (a⁻¹.mulVec v) ≤ c⁻¹ * euclideanSq v := by
  let y := a⁻¹.mulVec v
  have hinv := isUnit_det_of_euclidean_coercivity hc a (fun w => (ha w).1)
  have hay : a.mulVec y = v := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec]
  have hsq (w : Vec d) : 0 ≤ euclideanSq w := by
    change 0 ≤ ∑ j : Fin d, w j * w j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (w j)
  have hsymm (x z : Vec d) : dot x (a.mulVec z) = dot (a.mulVec x) z := by
    change dotProduct x (a.mulVec z) = dotProduct (a.mulVec x) z
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hs]
  have hcomm (x z : Vec d) : dot x z = dot z x := dotProduct_comm x z
  have heU : euclideanSq (v - c • y) =
      euclideanSq v - 2*c*dot v y + c^2*euclideanSq y := by
    change dotProduct (v - c • y) (v - c • y) = _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    change dot v v - c * dot y v - c * (dot v y - c * dot y y) = _
    rw [hcomm y v]
    unfold euclideanSq
    ring
  have hyL := (ha y).1
  rw [hay, hcomm y v] at hyL
  have hU : c * dot v y ≤ euclideanSq v := by
    have hp := hsq (v - c • y)
    rw [heU] at hp
    have hscale := mul_le_mul_of_nonneg_left hyL hc.le
    nlinarith only [hp, hscale]
  have hupper : dot v y ≤ c⁻¹ * euclideanSq v := by
    apply (mul_le_mul_iff_right₀ hc).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hU
  have heL : dot (C • y - v) (a.mulVec (C • y - v)) =
      C^2*dot v y - 2*C*euclideanSq v + dot v (a.mulVec v) := by
    change dotProduct (C • y - v) (a.mulVec (C • y - v)) = _
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      sub_dotProduct, dotProduct_sub, smul_eq_mul]
    change C * (C * dot y (a.mulVec y) - dot v (a.mulVec y)) -
      (C * dot y (a.mulVec v) - dot v (a.mulVec v)) = _
    rw [hay, hsymm y v, hay, hcomm y v]
    unfold euclideanSq
    ring
  have hlow : euclideanSq v ≤ C * dot v y := by
    have hp := (ha (C • y - v)).1
    have hpos : 0 ≤ dot (C • y - v) (a.mulVec (C • y - v)) :=
      (mul_nonneg hc.le (hsq _)).trans hp
    rw [heL] at hpos
    have hvU := (ha v).2
    have hmul : 0 ≤ C * (C * dot v y - euclideanSq v) := by
      nlinarith only [hpos, hvU]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hmul hC)
  constructor
  · apply (mul_le_mul_iff_right₀ hC).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hlow
  · exact hupper

end EinsteinRelation.Correctors
