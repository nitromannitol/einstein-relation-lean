import EinsteinFull.Homogenization.SourceAnnealedMinimizerLimit
import EinsteinFull.Homogenization.SourceGradientMeanSquare

/-!
# Averaged gradients at the limiting flux

For the limiting flux in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, the spatially
averaged response-optimizer gradient converges to zero in mean square.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The averaged optimizer-gradient coordinates vanish in mean square when
loaded by the inverse limiting dual matrix. -/
theorem integrable_and_tendsto_integral_sq_sourceGradient_limitingFlux
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p : Vec d) (i : Fin d) :
    let q := matVecMul (limitingAnnealedDualMatrix P)⁻¹ p
    let F := fun (n : ℕ) (a : Coefficient d K) => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i
    (∀ n, Integrable (fun a => (F n a) ^ 2) P) ∧
    Tendsto (fun n => ∫ a, (F n a) ^ 2 ∂P) atTop (𝓝 0) := by
  intro q F
  have hunit := (Matrix.isUnit_iff_isUnit_det (A := limitingAnnealedDualMatrix P)).mp
    (limitingAnnealedDualMatrix_posDef P hstat).isUnit
  have hMq : matVecMul (limitingAnnealedDualMatrix P) q = p := by
    dsimp only [q]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hunit]
    exact Matrix.one_mulVec p
  have h := integrable_and_tendsto_integral_sq_sourceResponseAverageGradient_sub_limit
    hK P hP hstat k hk p q i
  change (∀ n, Integrable (fun a => (F n a - (-p i +
      matVecMul (limitingAnnealedDualMatrix P) q i)) ^ 2) P) ∧
    Tendsto (fun n => ∫ a, (F n a - (-p i +
      matVecMul (limitingAnnealedDualMatrix P) q i)) ^ 2 ∂P) atTop (𝓝 0) at h
  simpa only [hMq, neg_add_cancel, sub_zero] using h

end EinsteinFull.Homogenization
