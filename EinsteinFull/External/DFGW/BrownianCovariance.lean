import EinsteinFull.External.DFGW.LinearBrownian
import Mathlib.Analysis.Matrix.Order

/-! # Brownian laws with prescribed covariance

A Brownian law with identity covariance yields a Brownian law for every symmetric positive
semidefinite covariance by applying the matrix square root.
-/

open MeasureTheory EinsteinRelation
open scoped MatrixOrder

namespace EinsteinFull.External.DFGW

variable {d : ℕ}

/-- A Brownian law with identity covariance gives a law with any symmetric positive semidefinite
covariance, including singular matrices. -/
theorem exists_brownianLaw_of_identity {W : Measure (Path d)}
    (hW : IsBrownianLaw (1 : Mat d) W) (D : Mat d) (hsymm : D.transpose = D)
    (hpsd : ∀ x : Vec d, 0 ≤ dot x (D.mulVec x)) :
    ∃ Q : Measure (Path d), IsBrownianLaw D Q := by
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
    · intro x
      simpa only [star_trivial, dot, dotProduct] using hpsd x
  have hs : (CFC.sqrt D).transpose = CFC.sqrt D := by
    have hs0 : (0 : Mat d) ≤ CFC.sqrt D := CFC.sqrt_nonneg D
    have h := (Matrix.nonneg_iff_posSemidef.mp hs0).isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hsq : CFC.sqrt D * CFC.sqrt D = D := by
    simpa only [sq] using CFC.sq_sqrt D hD.nonneg
  refine ⟨W.map (matrixPath (CFC.sqrt D)), ?_⟩
  have h := isBrownianLaw_map_matrixPath hW (CFC.sqrt D)
  simpa only [mul_one, hs, hsq] using h

end EinsteinFull.External.DFGW
