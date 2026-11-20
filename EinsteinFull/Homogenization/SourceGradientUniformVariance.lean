import EinsteinFull.Homogenization.SourceOptimizerGradientMoments
import EinsteinFull.Homogenization.SourceDualCoarseBound
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# Uniform optimizer-gradient variance

The ellipticity bounds give a uniform initial variance for the iteration in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Under a probability law, every optimizer-gradient coordinate has variance
bounded uniformly in the cube and in unit-ball loadings. -/
theorem variance_sourceResponseAverageGradient_le
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (Q : TriadicCube d) (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p ≤ 1) (hq : vecNormSq q ≤ 1) (i : Fin d) :
    ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i) P ≤
      2 * (1 + (2 * d : ℝ) ^ 2) := by
  let X := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
    (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i
  have hX : MemLp X 2 P := memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2
  have hpoint (a : Coefficient d K) : (X a) ^ 2 ≤ 2 * (1 + (2 * d : ℝ) ^ 2) := by
    let M := Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    let v := Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
    have hv : v = -p + matVecMul M q := by
      dsimp only [v, M]
      rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
      have hz := (Book.Ch02.responseSymmetricDirichletNeumannTheory
        (Book.Ch02.cubeDomain Q) (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
        (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain Q) k hk)).kappa_eq_zero
      have hzero : matVecMul (0 : Mat d) p = 0 := by
        ext l
        simp [matVecMul]
      rw [hz, hzero, add_zero]
    have hN : Book.Ch02.matrixOperatorNorm M ≤ (2 * d : ℝ) := by
      simpa [Book.Ch02.matrixNorm_eq_matrixOperatorNorm, M] using
        sourceDualCoarseMatrix_norm_le a Q k hk
    have hN0 : 0 ≤ Book.Ch02.matrixOperatorNorm M := Book.Ch02.matrixOperatorNorm_nonneg M
    have hN2 : Book.Ch02.matrixOperatorNorm M ^ 2 ≤ (2 * d : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Book.Ch02.matrixOperatorNorm M), Nat.cast_nonneg (α := ℝ) d]
    have hMq : vecNormSq (matVecMul M q) ≤ (2 * d : ℝ) ^ 2 := by
      calc
        _ ≤ Book.Ch02.matrixOperatorNorm M ^ 2 * vecNormSq q :=
          Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq M q
        _ ≤ (2 * d : ℝ) ^ 2 * 1 :=
          mul_le_mul hN2 hq (vecNormSq_nonneg q) (sq_nonneg _)
        _ = _ := mul_one _
    have hneg : vecNormSq (-p) = vecNormSq p := by
      simp [vecNormSq, vecDot]
    have hvbound : vecNormSq v ≤ 2 * (1 + (2 * d : ℝ) ^ 2) := by
      rw [hv]
      have h := vecNormSq_add_le (-p) (matVecMul M q)
      rw [hneg] at h
      linarith
    have hcoord : (v i) ^ 2 ≤ vecNormSq v := by
      unfold vecNormSq vecDot
      rw [sq]
      exact Finset.single_le_sum (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
    exact hcoord.trans hvbound
  calc
    ProbabilityTheory.variance X P ≤ ∫ a, (X a) ^ 2 ∂P :=
      ProbabilityTheory.variance_le_expectation_sq hX.aestronglyMeasurable
    _ ≤ ∫ _a : Coefficient d K, 2 * (1 + (2 * d : ℝ) ^ 2) ∂P :=
      integral_mono hX.integrable_sq (integrable_const _) hpoint
    _ = _ := by simp

end EinsteinFull.Homogenization
