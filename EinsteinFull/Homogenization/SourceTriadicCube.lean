import EinsteinRelation.External.AKMEnergyDensitySources
import EinsteinFull.Homogenization.BlockEnergyMeasurability
import Homogenization.CoarseGraining.OriginCubeOpenBridge

/-!
# Source triadic cubes

The centered cubes used in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.20),
agree with the open triadic cubes of CoarseGraining. The corresponding
half-open cubes give the same doubled variational energy.
-/

namespace EinsteinFull.Homogenization

open EinsteinRelation

/-- The source centered triadic cube is the open realization of the matching
CoarseGraining cube. -/
theorem sourceTriadicCube_eq_openCubeSet (d n : ℕ) :
    External.AKM.sourceTriadicCube d n =
      _root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d (n : ℤ)) := by
  ext x
  simp only [External.AKM.sourceTriadicCube, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo, _root_.Homogenization.mem_openCubeSet_originCube_iff, zpow_natCast]
  have hl : -((3 : ℝ) ^ n) / 2 = -(1 / 2 : ℝ) * (3 : ℝ) ^ n := by ring
  have hr : (3 : ℝ) ^ n / 2 = (1 / 2 : ℝ) * (3 : ℝ) ^ n := by ring
  rw [hl, hr]

/-- The source open cube and the half-open partition cube have the same
CoarseGraining block variational energy. -/
theorem Mu_sourceTriadicCube_eq_cubeSet {d : ℕ} [NeZero d] (n : ℕ)
    (P : _root_.Homogenization.BlockVec d) (a : _root_.Homogenization.CoeffField d) :
    _root_.Homogenization.Mu (External.AKM.sourceTriadicCube d n) P a =
      _root_.Homogenization.Mu
        (_root_.Homogenization.cubeSet (_root_.Homogenization.originCube d (n : ℤ))) P a := by
  rw [sourceTriadicCube_eq_openCubeSet]
  exact (_root_.Homogenization.Mu_cubeSet_originCube_eq_openCubeSet (n : ℤ) P a).symm

/-- The block energy on the source cube is measurable for observations on
the corresponding half-open partition cube. -/
theorem measurable_regularCoefficient_Mu_sourceTriadicCube {d : ℕ} [NeZero d] {K : ℝ}
    (n : ℕ) (P : _root_.Homogenization.BlockVec d) :
    @Measurable (Environment.AKMTestIntegralSupport.Coefficient d K) ℝ
      (Environment.AKMTestIntegralSupport.localSigma
        (_root_.Homogenization.cubeSet (_root_.Homogenization.originCube d (n : ℤ)))) _
      (fun a => _root_.Homogenization.Mu (External.AKM.sourceTriadicCube d n) P
        (regularCoefficient a).toFun) := by
  simpa only [Mu_sourceTriadicCube_eq_cubeSet] using
    (measurable_regularCoefficient_Mu (_root_.Homogenization.originCube d (n : ℤ)) P)

end EinsteinFull.Homogenization
