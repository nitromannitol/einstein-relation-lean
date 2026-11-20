import EinsteinFull.Homogenization.SourceEnergyLimitMatrix
import EinsteinFull.Homogenization.SourceLimitingDualMatrix
import EinsteinFull.Homogenization.SourceResponseAnnealed

/-!
# Comparison of limiting energies

The limiting Dirichlet and dual energies in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
obey the inequality inherited from nonnegativity of the response.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The limiting response remains nonnegative for any pair of loadings. -/
theorem limiting_annealedResponse_nonneg {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (p q : Vec d) :
    0 ≤ (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) +
      (⨅ n : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) - vecDot p q := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  apply ge_of_tendsto (tendsto_expected_sourceResponseJ hK P hstat k hk' p q)
  exact Filter.Eventually.of_forall fun n => integral_nonneg fun a =>
    Book.Ch02.responseJ_nonneg _ _ _ _

/-- The inverse limiting dual matrix is bounded above by the limiting
Dirichlet matrix in quadratic form order. -/
theorem limiting_inv_dualMatrix_le_dirichletMatrix {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (p : Vec d) :
    vecDot p (matVecMul (limitingAnnealedDualMatrix P)⁻¹ p) ≤
      vecDot p (matVecMul (limitingAnnealedDirichletMatrix hK P hstat) p) := by
  let M := limitingAnnealedDualMatrix P
  let q := matVecMul M⁻¹ p
  have hunit := (Matrix.isUnit_iff_isUnit_det (A := M)).mp
    (limitingAnnealedDualMatrix_posDef P hstat).isUnit
  have hMq : matVecMul M q = p := by
    dsimp only [q]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv M hunit]
    exact Matrix.one_mulVec p
  have h := limiting_annealedResponse_nonneg hK P hstat p q
  rw [iInf_expected_sourceDirichletEnergy_eq_matrix hK P hstat (-p),
    iInf_expected_sourceDualEnergy_eq_matrix P hstat q] at h
  change 0 ≤ (1 / 2 : ℝ) * vecDot (-p)
    (matVecMul (limitingAnnealedDirichletMatrix hK P hstat) (-p)) +
    (1 / 2 : ℝ) * vecDot q (matVecMul M q) - vecDot p q at h
  rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg, hMq,
    vecDot_comm q p] at h
  change vecDot p q ≤ _
  linarith

end EinsteinFull.Homogenization
