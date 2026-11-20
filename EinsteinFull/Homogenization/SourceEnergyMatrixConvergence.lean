import EinsteinFull.Homogenization.SourceEnergyLimitMatrixProperties

/-!
# Convergence of polarized annealed energies

The polarized expected Dirichlet energies in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
converge entrywise to the limiting symmetric matrix.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Polarized expected energies converge to each entry of the limiting matrix. -/
theorem tendsto_expected_sourceDirichletEnergy_polar_to_matrix {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (i j : Fin d) :
    Tendsto (fun n : ℕ =>
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n)
        (Pi.single i 1 + Pi.single j 1) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single i 1) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single j 1) ∂P))
      atTop (𝓝 (limitingAnnealedDirichletMatrix hK P hP i j)) := by
  rw [limitingAnnealedDirichletMatrix_apply hK P hP i j]
  exact ((tendsto_expected_sourceDirichletEnergy hK P hP
      (Pi.single i 1 + Pi.single j 1)).sub
    (tendsto_expected_sourceDirichletEnergy hK P hP (Pi.single i 1))).sub
    (tendsto_expected_sourceDirichletEnergy hK P hP (Pi.single j 1))

end EinsteinFull.Homogenization
