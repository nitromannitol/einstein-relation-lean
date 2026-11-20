import EinsteinFull.Homogenization.SourceDualCoercivity
import EinsteinFull.Homogenization.SourceDualMatrix

/-!
# Annealed dual matrices

The expected dual coarse matrix in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
is positive definite at every triadic scale.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The expectation of the pure-flux coarse matrix on a centered triadic cube. -/
noncomputable def annealedDualMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) : Mat d :=
  fun i j => ∫ a, Book.Ch02.sigmaStarInvCoarse
    (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
    (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) i j ∂P

/-- The annealed dual matrix is symmetric. -/
theorem annealedDualMatrix_isSymm {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    (annealedDualMatrix P n k hk).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply integral_congr_ae
  exact ae_of_all _ fun a =>
    (Book.Ch02.sigmaStarInvCoarse_isSymm _ _).apply i j

/-- Expected dual energy is the quadratic form of the annealed dual matrix. -/
theorem expected_sourceDualEnergy_eq_annealedDualMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (q : Vec d) :
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedDualMatrix P n k hk) q) := by
  simp_rw [sourceDualEnergy_eq_coarseMatrix _ _ k hk]
  rw [integral_const_mul]
  congr 1
  simp only [vecDot, matVecMul, annealedDualMatrix]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_finsetSum _ (fun j _ =>
      (integrable_sourceDualCoarseMatrix_entry P n k hk i j).mul_const (q j))).const_mul (q i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    (integrable_sourceDualCoarseMatrix_entry P n k hk i j).mul_const (q j))]
  simp only [integral_mul_const]

/-- The annealed dual matrix is strictly positive definite. -/
theorem annealedDualMatrix_posDef {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    (annealedDualMatrix P n k hk).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using annealedDualMatrix_isSymm P n k hk
  · intro q hq
    have hqpos : 0 < vecNormSq q :=
      lt_of_le_of_ne (vecNormSq_nonneg q) (Ne.symm (mt vecNormSq_eq_zero hq))
    have hbound := expected_sourceDualEnergy_originCube_lower k hk P (n : ℤ) q
    rw [expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk q] at hbound
    have hc : 0 < (4 * ((k : ℝ) + 1))⁻¹ := by positivity
    have hp : 0 < (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q := mul_pos hc hqpos
    have : 0 < vecDot q (matVecMul (annealedDualMatrix P n k hk) q) := by linarith
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using this

end EinsteinFull.Homogenization
