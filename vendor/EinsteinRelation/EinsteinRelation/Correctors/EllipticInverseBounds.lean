import EinsteinRelation.Correctors.EllipticInvertibility
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Euclidean ellipticity of inverse coefficients

Source: `paper/main.tex:867–873`. Completing squares in the original
coefficient form proves both inverse bounds. The planar rotation then
preserves these bounds, without an isotropy assumption.
-/

namespace EinsteinRelation.Correctors

/-- Symmetric Euclidean ellipticity is preserved by the actual matrix
inverse. Source: `paper/main.tex:867–873`. -/
theorem isElliptic_inverse {d : ℕ} {L : ℝ} (hL : 0 < L)
    {a : Vec d → Mat d} (ha : IsElliptic L a) :
    IsElliptic L (fun x => (a x)⁻¹) := by
  intro x
  have hdet := isElliptic_isUnit_det hL ha x
  refine ⟨?_, fun ξ => ?_⟩
  · rw [Matrix.transpose_nonsing_inv, (ha x).1]
  · let w := (a x)⁻¹.mulVec ξ
    have hw : (a x).mulVec w = ξ := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hcross : dot w ((a x).mulVec ξ) = euclideanSq ξ := by
      change dotProduct w ((a x).mulVec ξ) = _
      rw [Matrix.dotProduct_mulVec, ← (ha x).1, Matrix.vecMul_transpose, hw]
      rfl
    have hcomm : dot w ξ = dot ξ w := dotProduct_comm _ _
    have hsq (v : Vec d) : 0 ≤ euclideanSq v := by
      change 0 ≤ ∑ j : Fin d, v j * v j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hpos : 0 ≤ dot (w - L⁻¹ • ξ) ((a x).mulVec (w - L⁻¹ • ξ)) :=
      le_trans (mul_nonneg (inv_nonneg.mpr hL.le) (hsq _)) ((ha x).2 _).1
    have hexpand : dot (w - L⁻¹ • ξ) ((a x).mulVec (w - L⁻¹ • ξ)) =
        dot ξ w - 2 * L⁻¹ * euclideanSq ξ + L⁻¹ ^ 2 * dot ξ ((a x).mulVec ξ) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hw]
      change dotProduct (w - L⁻¹ • ξ) (ξ - L⁻¹ • (a x).mulVec ξ) = _
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      change dot w ξ - L⁻¹ * dot w ((a x).mulVec ξ) -
        (L⁻¹ * dot ξ ξ - L⁻¹ * (L⁻¹ * dot ξ ((a x).mulVec ξ))) = _
      rw [hcross, hcomm]
      change _ - _ - (L⁻¹ * euclideanSq ξ - _) = _
      ring
    rw [hexpand] at hpos
    have hupper := ((ha x).2 ξ).2
    have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg L⁻¹)
    have hcancel : L⁻¹ ^ 2 * (L * euclideanSq ξ) = L⁻¹ * euclideanSq ξ := by
      field_simp [hL.ne']
    have hlo : L⁻¹ * euclideanSq ξ ≤ dot ξ w := by
      rw [hcancel] at hscaled
      nlinarith only [hpos, hscaled]
    have hcoerc := ((ha x).2 w).1
    rw [hw, hcomm] at hcoerc
    have hnorm : 0 ≤ euclideanSq (w - L • ξ) := hsq _
    have heuc : euclideanSq (w - L • ξ) =
        euclideanSq w - 2 * L * dot ξ w + L ^ 2 * euclideanSq ξ := by
      change dotProduct (w - L • ξ) (w - L • ξ) = _
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      change euclideanSq w - L * dot w ξ -
        (L * dot ξ w - L * (L * euclideanSq ξ)) = _
      rw [hcomm]
      ring
    rw [heuc] at hnorm
    have hcoerc' : euclideanSq w ≤ L * dot ξ w := by
      have h := mul_le_mul_of_nonneg_left hcoerc hL.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] using h
    have hhi : dot ξ w ≤ L * euclideanSq ξ := by
      apply (mul_le_mul_iff_right₀ hL).mp
      nlinarith only [hnorm, hcoerc']
    exact ⟨hlo, hhi⟩

/-- Rotation of the inverse planar coefficient preserves both symmetric
ellipticity bounds. Source: `paper/main.tex:867–873`. -/
theorem isElliptic_planar_rotated_inverse {L : ℝ} (hL : 0 < L)
    {a : Vec 2 → Mat 2} (ha : IsElliptic L a) :
    IsElliptic L (fun x => (!![0, -1; 1, 0] : Mat 2) * (a x)⁻¹ *
      (!![0, -1; 1, 0] : Mat 2).transpose) := by
  let J : Mat 2 := !![0, -1; 1, 0]
  have hi := isElliptic_inverse hL ha
  intro x
  refine ⟨?_, fun ξ => ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, (hi x).1, Matrix.mul_assoc]
  · have hsq : euclideanSq (J.transpose.mulVec ξ) = euclideanSq ξ := by
      norm_num [J, euclideanSq, dot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    have hdot : dot ξ ((J * (a x)⁻¹ * J.transpose).mulVec ξ) =
        dot (J.transpose.mulVec ξ) ((a x)⁻¹.mulVec (J.transpose.mulVec ξ)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change dotProduct ξ (J.mulVec _) = _
      rw [Matrix.dotProduct_mulVec ξ J, ← Matrix.mulVec_transpose]
      rfl
    change L⁻¹ * euclideanSq ξ ≤ dot ξ ((J * (a x)⁻¹ * J.transpose).mulVec ξ) ∧
      dot ξ ((J * (a x)⁻¹ * J.transpose).mulVec ξ) ≤ L * euclideanSq ξ
    rw [hdot, ← hsq]
    exact (hi x).2 _

end EinsteinRelation.Correctors
