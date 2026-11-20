import EinsteinFull.Homogenization.SourceEnergyMatrixConvergence

/-!
# Convergence of the annealed coarse matrix

The Dirichlet block of the coarse matrix of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
has integrable entries whose expectations converge to the limiting matrix.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Entries of the Dirichlet block are polarized source energies. -/
theorem sourceCoarseMatrix_entry_eq_polar {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (n k : ℕ) (hK : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hK)).upperLeft i j =
    sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single i 1 + Pi.single j 1) -
      sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single i 1) -
      sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single j 1) := by
  let U := Book.Ch02.cubeDomain (originCube d (n : ℤ))
  let M := (Book.Ch02.coarseBlockMatrix U (sourceCoeffOn a U k hK)).upperLeft
  have hs : M i j = M j i := by
    simpa [M, blockMatEntry] using
      (Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U (sourceCoeffOn a U k hK)
        (Sum.inl i) (Sum.inl j))
  rw [sourceTriadicCube_eq_openCubeSet]
  change M i j = sourceDirichletEnergy a U (Pi.single i 1 + Pi.single j 1) -
    sourceDirichletEnergy a U (Pi.single i 1) - sourceDirichletEnergy a U (Pi.single j 1)
  rw [sourceDirichletEnergy_eq_coarseMatrix a U k hK,
    sourceDirichletEnergy_eq_coarseMatrix a U k hK,
    sourceDirichletEnergy_eq_coarseMatrix a U k hK]
  change M i j = (1 / 2 : ℝ) * vecDot (Pi.single i 1 + Pi.single j 1)
      (matVecMul M (Pi.single i 1 + Pi.single j 1)) -
    (1 / 2 : ℝ) * vecDot (Pi.single i 1) (matVecMul M (Pi.single i 1)) -
    (1 / 2 : ℝ) * vecDot (Pi.single j 1) (matVecMul M (Pi.single j 1))
  rw [basis_sum_pairing, matVecMul_single, matVecMul_single, vecDot_single_left,
    vecDot_single_left]
  linarith

/-- Every entry of the finite-scale Dirichlet block is integrable. -/
theorem integrable_sourceCoarseMatrix_entry {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Integrable (fun a =>
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).upperLeft i j) P := by
  have h := ((integrable_sourceDirichletEnergy hK P n (Pi.single i 1 + Pi.single j 1)).sub
    (integrable_sourceDirichletEnergy hK P n (Pi.single i 1))).sub
    (integrable_sourceDirichletEnergy hK P n (Pi.single j 1))
  convert h using 1
  funext a
  exact sourceCoarseMatrix_entry_eq_polar a n k hk i j

/-- The expected finite-scale Dirichlet block converges entrywise. -/
theorem tendsto_expected_sourceCoarseMatrix_entry {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => ∫ a,
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).upperLeft i j ∂P)
      atTop (𝓝 (limitingAnnealedDirichletMatrix hK P hP i j)) := by
  convert tendsto_expected_sourceDirichletEnergy_polar_to_matrix hK P hP i j using 1
  funext n
  simp_rw [sourceCoarseMatrix_entry_eq_polar]
  let F : Vec d → Coefficient d K → ℝ := fun e a =>
    sourceDirichletEnergy a (sourceTriadicCube d n) e
  have hF (e : Vec d) : Integrable (F e) P := integrable_sourceDirichletEnergy hK P n e
  change (∫ a, F (Pi.single i 1 + Pi.single j 1) a - F (Pi.single i 1) a -
    F (Pi.single j 1) a ∂P) = _
  calc
    _ = (∫ a, F (Pi.single i 1 + Pi.single j 1) a - F (Pi.single i 1) a ∂P) -
        ∫ a, F (Pi.single j 1) a ∂P :=
      integral_sub ((hF (Pi.single i 1 + Pi.single j 1)).sub (hF (Pi.single i 1)))
        (hF (Pi.single j 1))
    _ = _ := by rw [integral_sub (hF (Pi.single i 1 + Pi.single j 1)) (hF (Pi.single i 1))]

end EinsteinFull.Homogenization
