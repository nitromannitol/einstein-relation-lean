import EinsteinFull.Homogenization.SourceAnnealedResponseMinimizer
import EinsteinFull.Homogenization.SourceGradientMeanMatrix

/-!
# Mean gradient at the minimizing flux

The minimizing flux for the expected response in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
makes the expected spatially averaged optimizer gradient vanish.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- At the minimizing flux the spatially averaged response gradient has zero
expectation in every coordinate. -/
theorem integral_sourceResponseAverageGradient_minimizer
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p : Vec d) (i : Fin d) :
    let M := annealedDualMatrix P n k hk
    let q₀ := matVecMul M⁻¹ p
    let U := Book.Ch02.cubeDomain (originCube d (n : ℤ))
    let F := fun a : Coefficient d K => Book.Ch02.averageGradient U
      (sourceCoeffOn a U k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory U (sourceCoeffOn a U k hk)) p q₀).toSolution i
    Integrable F P ∧ (∫ a, F a ∂P) = 0 := by
  intro M q₀ U F
  have hunit := (Matrix.isUnit_iff_isUnit_det (A := M)).mp
    (annealedDualMatrix_posDef P n k hk).isUnit
  have hMq₀ : matVecMul M q₀ = p := by
    dsimp only [q₀]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hunit]
    exact Matrix.one_mulVec p
  have h := integral_sourceResponseAverageGradient_eq P n k hk p q₀ i
  refine ⟨h.1, ?_⟩
  rw [h.2.2]
  change -p i + matVecMul M q₀ i = 0
  rw [hMq₀]
  exact neg_add_cancel _

end EinsteinFull.Homogenization
