import EinsteinFull.Homogenization.SourceResponseDefect
import EinsteinFull.Homogenization.SourceDualMatrix
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# Uniform dual coarse-matrix bounds

The ellipticity bounds for the dual energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
provide uniform bounds for its coarse matrix.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The dual coarse matrix has a dimension-dependent norm bound on every
triadic cube. -/
theorem sourceDualCoarseMatrix_norm_le {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) :
    Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) ≤ 2 * d := by
  let U := Book.Ch02.cubeDomain Q
  let A := sourceCoeffOn a U k hk
  let M := Book.Ch02.sigmaStarInvCoarse U A
  have hdiag (i : Fin d) : M i i ≤ 2 := by
    have hb := (sourceDualEnergy_cube_bounds a Q (Pi.single i 1)).2
    rw [sourceDualEnergy_eq_coarseMatrix a U k hk] at hb
    have hn : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
      rw [vecNormSq, vecDot_single_left, Pi.single_eq_same]
    rw [hn] at hb
    have heq : vecDot (Pi.single i (1 : ℝ)) (matVecMul M (Pi.single i 1)) = M i i := by
      rw [matVecMul_single, vecDot_single_left]
    change (1 / 2 : ℝ) * vecDot (Pi.single i 1) (matVecMul M (Pi.single i 1)) ≤ 1 at hb
    rw [heq] at hb
    linarith
  calc
    Book.Ch02.matrixNorm M ≤ Matrix.trace M :=
      Book.Ch02.matrixNorm_le_trace_of_posSemidef M
        (Book.Ch02.sigmaStarInvCoarse_posDef U A).posSemidef
    _ ≤ 2 * d := by
      unfold Matrix.trace
      calc
        ∑ i : Fin d, M i i ≤ ∑ _i : Fin d, (2 : ℝ) := Finset.sum_le_sum fun i _ => hdiag i
        _ = 2 * d := by simp [mul_comm]

end EinsteinFull.Homogenization
