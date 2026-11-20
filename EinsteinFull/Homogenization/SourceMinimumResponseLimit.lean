import EinsteinFull.Homogenization.SourceAnnealedMinimizerLimit
import EinsteinFull.Homogenization.SourceAnnealedResponseMinimizer
import EinsteinFull.Homogenization.SourceEnergyLimitMatrix

/-!
# Limit of the minimum expected response

The minimum expected response in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
converges to half the difference of the limiting primal and inverse dual
quadratic forms.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- At its minimizing flux, the expected response is the difference between
the expected Dirichlet energy and half the inverse dual quadratic form. -/
theorem expected_sourceResponseJ_min_eq {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p : Vec d) :
    let M := annealedDualMatrix P n k hk
    let q := matVecMul M⁻¹ p
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) =
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) -
        (1 / 2 : ℝ) * vecDot p q := by
  intro M q
  have hunit := (Matrix.isUnit_iff_isUnit_det (A := M)).mp
    (annealedDualMatrix_posDef P n k hk).isUnit
  have hMq : matVecMul M q = p := by
    dsimp only [q]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hunit]
    exact Matrix.one_mulVec p
  rw [expected_sourceResponseJ_eq hK P n k hk p q,
    expected_sourceDualEnergy_eq_annealedDualMatrix P n k hk q]
  change _ + (1 / 2 : ℝ) * vecDot q (matVecMul M q) - vecDot p q = _
  rw [hMq, vecDot_comm q p]
  ring

/-- The minimizing responses are integrable and their expectations converge
to the quadratic-form gap between the primal and inverse dual limits. -/
theorem integrable_and_tendsto_expected_sourceResponseJ_min
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p : Vec d) :
    let q := fun n => matVecMul (annealedDualMatrix P n k hk)⁻¹ p
    (∀ n : ℕ, Integrable (fun a => Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p (q n)) P) ∧
    Tendsto (fun n : ℕ => ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p (q n) ∂P)
      atTop (𝓝 ((1 / 2 : ℝ) *
        (vecDot p (matVecMul (limitingAnnealedDirichletMatrix hK P hstat) p) -
          vecDot p (matVecMul (limitingAnnealedDualMatrix P)⁻¹ p)))) := by
  intro q
  refine ⟨fun n => integrable_sourceResponseJ hK P n k hk p (q n), ?_⟩
  have hq := tendsto_annealedResponse_minimizingFlux P hstat k hk p
  have hdot : Tendsto (fun n => vecDot p (q n)) atTop
      (𝓝 (vecDot p (matVecMul (limitingAnnealedDualMatrix P)⁻¹ p))) := by
    change Tendsto (fun n => ∑ i : Fin d, p i * q n i) atTop
      (𝓝 (∑ i : Fin d, p i * matVecMul (limitingAnnealedDualMatrix P)⁻¹ p i))
    exact tendsto_finsetSum _ fun i _ =>
      (tendsto_const_nhds (x := p i)).mul ((tendsto_pi_nhds.mp hq) i)
  have h := (tendsto_expected_sourceDirichletEnergy hK P hstat (-p)).sub
    ((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hdot)
  rw [iInf_expected_sourceDirichletEnergy_eq_matrix hK P hstat (-p),
    matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg] at h
  convert h.congr' (Filter.Eventually.of_forall fun n =>
    (expected_sourceResponseJ_min_eq hK P n k hk p).symm) using 1
  ring

end EinsteinFull.Homogenization
