import EinsteinFull.Homogenization.SourceResponseGradientMismatch
import EinsteinFull.Homogenization.SourceDualCoarseBound

/-!
# Uniform gradient mismatch estimate

The second-variation argument in Lemma 2.13 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, bounds
parent-child optimizer gradient differences by the response defect.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The mean squared parent-child gradient mismatch is bounded by `4d` times
 the response partition defect. -/
theorem descendantsAverage_sourceGradientMismatch_le_four_mul_dim_mul_defect
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K)
    (Q : TriadicCube d) (j k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun -
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun)) ≤
      (4 * d) *
        (descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
        Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (regularCoefficient a) (regularCoefficient_locallyElliptic a)
  have hcell (R : TriadicCube d) : Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤ 2 * d := by
    have heq : Book.Ch02.CoeffOn.AEEq (F.coeffOn R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) := Filter.EventuallyEq.rfl
    unfold Book.Ch02.coarseSigmaStarInvMatrixNorm
    rw [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq heq]
    exact sourceDualCoarseMatrix_norm_le a R k hk
  have hscale : Q.scale - (j : ℤ) ≤ Q.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hmax : Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F ≤
      2 * d := by
    unfold Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    exact Book.Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty Q hscale) (fun R _ => hcell R)
  have hdef : 0 ≤ descendantsAverage Q j
      (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q :=
    sub_nonneg.mpr (sourceResponseJ_le_descendantsAverage a Q j k hk p q)
  have h := descendantsAverage_sourceGradientMismatch_le_responseDefect a Q j k hk p q
  have hmul := mul_le_mul_of_nonneg_right hmax hdef
  dsimp only at h
  nlinarith

end EinsteinFull.Homogenization
