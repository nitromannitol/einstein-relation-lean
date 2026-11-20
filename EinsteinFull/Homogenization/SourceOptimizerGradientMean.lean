import EinsteinFull.Homogenization.SourceDualMatrixMeanConvergence
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities

/-!
# Mean convergence of averaged optimizer gradients

The spatially averaged gradient of the dual maximizer in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, is represented by the pure-flux coarse matrix.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- An averaged dual-maximizer gradient coordinate converges in mean to the
corresponding polarization of the limiting expected dual energy. -/
theorem tendsto_integral_abs_averageGradient_dualMaximizer_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => ∫ a,
      |Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk))
          0 (Pi.single j 1)).toSolution i -
      ((⨅ m : ℕ, ∫ b, sourceDualEnergy b
         (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1 + Pi.single j 1) ∂P) -
       (⨅ m : ℕ, ∫ b, sourceDualEnergy b
         (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single i 1) ∂P) -
       (⨅ m : ℕ, ∫ b, sourceDualEnergy b
         (Book.Ch02.cubeDomain (originCube d (m : ℤ))) (Pi.single j 1) ∂P))| ∂P)
      atTop (𝓝 0) := by
  have h := tendsto_integral_abs_sourceDualCoarseMatrix_entry_sub_limit
    hK P hP hstat k hk i j
  convert h using 1
  funext n
  apply integral_congr_ae
  filter_upwards [] with a
  rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
  simp only [neg_zero, matVecMul_zero, add_zero, zero_add, matVecMul_single]

end EinsteinFull.Homogenization
