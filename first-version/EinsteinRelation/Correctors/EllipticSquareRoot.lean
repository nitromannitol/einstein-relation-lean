import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Correctors.RadialPoissonKernel
import Mathlib.Analysis.Matrix.Order

/-! # The linear change of coordinates for anisotropic kernels

Source: `paper/main.tex:1003–1018`. A symmetric elliptic matrix has an
invertible symmetric square root. Both coordinate changes have Euclidean
operator bounds depending only on the ellipticity parameter.
-/

open scoped MatrixOrder

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

private theorem sq_norm_mulVec {S : Mat d} (hS : S.transpose = S) (x : Vec d) :
    euclideanNorm (S.mulVec x) ^ 2 = dot x ((S * S).mulVec x) := by
  rw [euclideanNorm_sq_eq, ← Matrix.mulVec_mulVec]
  change dotProduct (S.mulVec x) (S.mulVec x) = dotProduct x (S.mulVec (S.mulVec x))
  have hv : Matrix.vecMul x S = S.mulVec x := by
    simpa only [hS] using Matrix.vecMul_transpose S x
  calc
    _ = dotProduct (Matrix.vecMul x S) (S.mulVec x) := by rw [hv]
    _ = _ := (Matrix.dotProduct_mulVec x S (S.mulVec x)).symm

/-- A symmetric elliptic matrix has an actual invertible symmetric square
root with uniform bounds in both directions (`paper/main.tex:1003–1018`). -/
theorem exists_elliptic_squareRoot {L : ℝ} (hL : 0 < L) (A : Mat d)
    (hA : A.transpose = A)
    (hlow : ∀ x : Vec d, L⁻¹ * euclideanSq x ≤ dot x (A.mulVec x))
    (hup : ∀ x : Vec d, dot x (A.mulVec x) ≤ L * euclideanSq x) :
    ∃ S : Mat d, S.transpose = S ∧ S * S = A ∧ IsUnit S ∧
      (∀ x : Vec d, euclideanNorm (S.mulVec x) ≤ Real.sqrt L * euclideanNorm x) ∧
      (∀ x : Vec d, euclideanNorm (S⁻¹.mulVec x) ≤ Real.sqrt L * euclideanNorm x) := by
  have hpos : A.PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, fun x hx => ?_⟩
    · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
    · have h := (mul_pos (inv_pos.mpr hL) (euclideanSq_pos_of_ne_zero hx)).trans_le (hlow x)
      simpa only [star_trivial] using h
  let S : Mat d := CFC.sqrt A
  have hSpos : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hSsym : S.transpose = S := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hSpos.isHermitian
  have hSsq : S * S = A := CFC.sqrt_mul_sqrt_self A hpos.posSemidef.nonneg
  have hSi : IsUnit S := by
    apply (Matrix.isUnit_iff_isUnit_det S).mpr
    have hu : IsUnit (S.det * S.det) := by
      rw [← Matrix.det_mul, hSsq]
      exact (Matrix.isUnit_iff_isUnit_det A).mp hpos.isUnit
    exact isUnit_of_mul_isUnit_left hu
  refine ⟨S, hSsym, hSsq, hSi, ?_, ?_⟩
  · intro x
    have hsq : euclideanNorm (S.mulVec x) ^ 2 ≤
        (Real.sqrt L * euclideanNorm x) ^ 2 := by
      rw [sq_norm_mulVec hSsym, hSsq, mul_pow, Real.sq_sqrt hL.le, euclideanNorm_sq_eq]
      exact hup x
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg L) (Real.sqrt_nonneg (euclideanSq x)))
  · intro x
    have hcancel : S.mulVec (S⁻¹.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S
        ((Matrix.isUnit_iff_isUnit_det S).mp hSi), Matrix.one_mulVec]
    have hs := hlow (S⁻¹.mulVec x)
    rw [← hSsq, ← sq_norm_mulVec hSsym, hcancel, ← euclideanNorm_sq_eq] at hs
    have hsq : euclideanNorm (S⁻¹.mulVec x) ^ 2 ≤
        (Real.sqrt L * euclideanNorm x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hL.le]
      have h := (mul_le_mul_of_nonneg_left hs hL.le)
      simpa only [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] using h
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg L) (Real.sqrt_nonneg (euclideanSq x)))

end EinsteinRelation.Correctors
