import EinsteinFull.Homogenization.SourceResponseDefect
import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.EnergyDefect

/-!
# Response optimizer gradient mismatch

The response partition defect controls the averaged gradient mismatch in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemmas 2.12 and 2.13.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The mean squared parent-child gradient mismatch is bounded by the source
response defect times the maximal descendant dual coarse-matrix norm. -/
theorem descendantsAverage_sourceGradientMismatch_le_responseDefect
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K)
    (Q : TriadicCube d) (j k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (regularCoefficient a) (regularCoefficient_locallyElliptic a)
    descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun -
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun)) ≤
      2 * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ)) F *
        (descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
        Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) := by
  intro F
  have h := Book.Ch05.Section53.WeakNormsMaximizer.descendantsAverage_ch04GradientMismatch_le_maxSigmaStarInv_mul_responseDefect
      (regularCoefficient a) (regularCoefficient_locallyElliptic a) Q j p q
  unfold responseJPartitionDefectOnFamilyAtDepth childResponseJAverageOnFamilyAtDepth at h
  simpa only [responseJ_regularCoefficient_eq_source a _ k hk p q] using h

end EinsteinFull.Homogenization
