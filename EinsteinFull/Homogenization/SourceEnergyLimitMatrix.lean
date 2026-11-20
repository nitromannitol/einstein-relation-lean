import EinsteinFull.Homogenization.SourceEnergyLimitForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Matrix of the limiting annealed energy

The limiting expected Dirichlet energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
is represented by a symmetric matrix.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The matrix of twice the limiting expected Dirichlet energy. -/
noncomputable def limitingAnnealedDirichletMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) :
    Mat d :=
  (2 : ℝ) • (limitingAnnealedDirichletForm hK P hP).toMatrix'

/-- The limiting annealed matrix is symmetric. -/
theorem limitingAnnealedDirichletMatrix_isSymm {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) :
    (limitingAnnealedDirichletMatrix hK P hP).IsSymm := by
  apply Matrix.IsSymm.smul
  exact QuadraticForm.isSymm_toMatrix' (limitingAnnealedDirichletForm hK P hP)

/-- The limiting energy equals one half of the limiting matrix quadratic form. -/
theorem iInf_expected_sourceDirichletEnergy_eq_matrix {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) =
      (1 / 2 : ℝ) * vecDot e (matVecMul (limitingAnnealedDirichletMatrix hK P hP) e) := by
  let Q := limitingAnnealedDirichletForm hK P hP
  have h : vecDot e (matVecMul Q.toMatrix' e) = Q e := by
    have hb := dotProduct_toMatrix₂_mulVec (Pi.basisFun ℝ (Fin d))
      (Pi.basisFun ℝ (Fin d)) Q.associated e e
    simpa [LinearMap.toMatrix₂_basisFun, QuadraticForm.toMatrix', vecDot, matVecMul,
      dotProduct, Matrix.mulVec, QuadraticMap.associated_eq_self_apply] using hb
  rw [limitingAnnealedDirichletMatrix, smul_matVecMul, vecDot_smul_right, h]
  change Q e = (1 / 2 : ℝ) * (2 * Q e)
  ring

end EinsteinFull.Homogenization
