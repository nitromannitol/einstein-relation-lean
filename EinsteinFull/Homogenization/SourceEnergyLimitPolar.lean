import EinsteinFull.Homogenization.SourceEnergyLimitQuadratic
import EinsteinFull.Homogenization.SourceEnergyAnnealedPolar

/-!
# Polarization of the limiting annealed Dirichlet energy

The limiting expected Dirichlet energy in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
has a bilinear polarization.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The limiting energy polarization is additive in its first argument. -/
theorem iInf_expected_sourceDirichletEnergy_polar_add_left {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (x y z : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y + z) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (z) ∂P) =
      ((⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + z) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (z) ∂P)) +
      ((⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (y + z) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (y) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (z) ∂P)) := by
  have hleft := (((tendsto_expected_sourceDirichletEnergy hK P hP (x + y + z)).sub (tendsto_expected_sourceDirichletEnergy hK P hP (x + y))).sub (tendsto_expected_sourceDirichletEnergy hK P hP (z)))
  have hright := (((tendsto_expected_sourceDirichletEnergy hK P hP (x + z)).sub (tendsto_expected_sourceDirichletEnergy hK P hP (x))).sub (tendsto_expected_sourceDirichletEnergy hK P hP (z))).add
    (((tendsto_expected_sourceDirichletEnergy hK P hP (y + z)).sub (tendsto_expected_sourceDirichletEnergy hK P hP (y))).sub (tendsto_expected_sourceDirichletEnergy hK P hP (z)))
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDirichletEnergy_polar_add_left hK P n x y z).symm

/-- The limiting energy polarization is homogeneous in its first argument. -/
theorem iInf_expected_sourceDirichletEnergy_polar_smul_left {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (c : ℝ) (x y : Vec d) :
    (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (c • x + y) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (c • x) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (y) ∂P) =
      c * ((⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x) ∂P) - (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (y) ∂P)) := by
  have hleft := (((tendsto_expected_sourceDirichletEnergy hK P hP (c • x + y)).sub (tendsto_expected_sourceDirichletEnergy hK P hP (c • x))).sub (tendsto_expected_sourceDirichletEnergy hK P hP (y)))
  have hright := (tendsto_const_nhds (x := c)).mul
    (((tendsto_expected_sourceDirichletEnergy hK P hP (x + y)).sub (tendsto_expected_sourceDirichletEnergy hK P hP (x))).sub (tendsto_expected_sourceDirichletEnergy hK P hP (y)))
  apply tendsto_nhds_unique hleft
  refine hright.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceDirichletEnergy_polar_smul_left hK P n c x y).symm

end EinsteinFull.Homogenization
