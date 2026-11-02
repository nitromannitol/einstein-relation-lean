import EinsteinRelation.Environment.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

/-! # Invertibility of the actual elliptic coefficient matrices

Source: `paper/main.tex:867–873`. The lower Euclidean quadratic bound
makes every coefficient matrix invertible, including anisotropic matrices.
-/

namespace EinsteinRelation.Correctors

/-- Positive Euclidean coercivity rules out a nonzero kernel vector.
Source: `paper/main.tex:867–870`. -/
theorem isUnit_det_of_euclidean_coercivity {d : ℕ} {c : ℝ} (hc : 0 < c)
    (a : Mat d) (ha : ∀ v : Vec d, c * euclideanSq v ≤ dot v (a.mulVec v)) :
    IsUnit a.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hav⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := a)).mpr hdet
  have hlow := ha v
  rw [hav, show dot v (0 : Vec d) = 0 by simp [dot]] at hlow
  have hsq : euclideanSq v ≤ 0 := by
    exact nonpos_of_mul_nonpos_right hlow hc
  apply hv
  ext j
  have hj : v j * v j ≤ euclideanSq v :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  change v j = 0
  nlinarith only [hj, hsq, sq_nonneg (v j)]

/-- The stated ellipticity supplies the matrix-inverse hypothesis at every
spatial point. Source: `paper/main.tex:867–873`. -/
theorem isElliptic_isUnit_det {d : ℕ} {L : ℝ} (hL : 0 < L)
    {a : Vec d → Mat d} (ha : IsElliptic L a) (x : Vec d) :
    IsUnit (a x).det :=
  isUnit_det_of_euclidean_coercivity (inv_pos.mpr hL) (a x) (fun v => ((ha x).2 v).1)

end EinsteinRelation.Correctors
