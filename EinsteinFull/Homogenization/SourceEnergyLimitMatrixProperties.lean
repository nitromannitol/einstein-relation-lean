import EinsteinFull.Homogenization.SourceEnergyLimitMatrix
import EinsteinFull.Homogenization.SourceEnergyLimitBounds

/-!
# Properties of the limiting annealed matrix

The symmetric matrix representing the limiting expected Dirichlet energy in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Chapter 2, has explicit polarized entries and inherits
the energy bounds.
-/

open MeasureTheory
open _root_.Homogenization
open EinsteinRelation (euclideanSq)

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The entries of the limiting matrix are the polarized limiting energies. -/
theorem limitingAnnealedDirichletMatrix_apply {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (i j : Fin d) :
    limitingAnnealedDirichletMatrix hK P hP i j =
      (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n)
        (Pi.single i 1 + Pi.single j 1) ∂P) -
      (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single i 1) ∂P) -
      (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (Pi.single j 1) ∂P) := by
  let Q := limitingAnnealedDirichletForm hK P hP
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (Vec d) =>
    B (Pi.single i 1) (Pi.single j 1)) (QuadraticMap.two_nsmul_associated ℝ Q)
  change (2 : ℝ) * Q.associated (Pi.single i 1) (Pi.single j 1) =
    Q (Pi.single i 1 + Pi.single j 1) - Q (Pi.single i 1) - Q (Pi.single j 1)
  simpa only [LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar] using h

/-- The limiting matrix is nonnegative and bounded by the affine competitor. -/
theorem limitingAnnealedDirichletMatrix_bounds {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (e : Vec d) :
    0 ≤ vecDot e (matVecMul (limitingAnnealedDirichletMatrix hK P hP) e) ∧
      vecDot e (matVecMul (limitingAnnealedDirichletMatrix hK P hP) e) ≤ K * euclideanSq e := by
  have h := iInf_expected_sourceDirichletEnergy_bounds hK P e
  rw [iInf_expected_sourceDirichletEnergy_eq_matrix hK P hP e] at h
  constructor <;> linarith [h.1, h.2]

end EinsteinFull.Homogenization
