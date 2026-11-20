import EinsteinFull.Homogenization.SourceDualBlockBridge

/-!
# Local measurability of the dual energy

The dual energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.1), is measurable with respect
to coefficient observations in the corresponding triadic cube.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy of an open cube is measurable for observations on the
corresponding half-open triadic cube. -/
theorem measurable_sourceDualEnergy_cube {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (q : Vec d) :
    @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => sourceDualEnergy a (Book.Ch02.cubeDomain Q) q) := by
  have h := measurable_regularCoefficient_Mu (K := K) Q (0, q)
  convert h using 1
  funext a
  rw [sourceDualEnergy_eq_Mu]
  change Mu (openCubeSet Q) (0, q) (regularCoefficient a).toFun = _
  exact (Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (0, q) (regularCoefficient a).toFun).symm

/-- The dual energy of a triadic cube is measurable for the coefficient sigma
algebra. -/
theorem measurable_sourceDualEnergy_cube_full {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (q : Vec d) :
    Measurable (fun a : Coefficient d K => sourceDualEnergy a (Book.Ch02.cubeDomain Q) q) :=
  (measurable_sourceDualEnergy_cube Q q).mono
    (coefficientLocalSigma_le_coefficientSigma _) le_rfl

end EinsteinFull.Homogenization
