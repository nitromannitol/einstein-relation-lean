import EinsteinFull.Homogenization.SourceDualMeasurability
import EinsteinFull.Homogenization.SourceEnergyCoercivity

/-!
# Bounds for the dual energy

The dual energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.1), has uniform ellipticity
bounds on centered triadic cubes.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy on a centered triadic cube is nonnegative and is bounded
above by the squared magnitude of the flux loading. -/
theorem sourceDualEnergy_originCube_bounds {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (m : ℤ) (q : Vec d) :
    0 ≤ sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d m)) q ∧
      sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d m)) q ≤ vecNormSq q := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  let Q := originCube d m
  let U := Book.Ch02.cubeDomain Q
  let A := unitLowerSourceCoeffOn a U k hK
  let A' := Internal.Ch02.BookCh02.pointwiseCoeffField U A
  have hEll : IsEllipticFieldOn 1 ((k : ℝ) + 1) (cubeSet Q) A' :=
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet Q A
  have hupper := mu_le_diag_upper_cube hEll (0, q)
  have hlower := diag_lower_le_mu_cube hEll (0, q)
  have hae : A' =ᵐ[volumeMeasureOn (openCubeSet Q)] (regularCoefficient a).toFun := by
    simpa [A', A, U, unitLowerSourceCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U A
  have heq : Mu (cubeSet Q) (0, q) A' = sourceDualEnergy a U q := by
    rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (0, q) A',
      Mu_congr_of_ae_eq hae (0, q)]
    exact (sourceDualEnergy_eq_Mu a U q).symm
  rw [heq] at hupper hlower
  have hpos : 0 ≤ (4 * ((k : ℝ) + 1))⁻¹ * vecNormSq q :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (vecNormSq_nonneg q)
  constructor
  · simpa using le_trans hpos (by simpa [vecNormSq, vecDot] using hlower)
  · simpa [vecNormSq, vecDot] using hupper

/-- The dual energy on a centered triadic cube is integrable under any finite
coefficient law. -/
theorem integrable_sourceDualEnergy_originCube {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (m : ℤ) (q : Vec d) :
    Integrable (fun a => sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d m)) q) P := by
  apply (integrable_const (vecNormSq q)).mono'
    (measurable_sourceDualEnergy_cube_full (originCube d m) q).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_of_nonneg (sourceDualEnergy_originCube_bounds a m q).1]
    exact (sourceDualEnergy_originCube_bounds a m q).2

end EinsteinFull.Homogenization
