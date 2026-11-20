import EinsteinFull.Homogenization.SourceOptimizerGradientBridge
import Homogenization.Book.Ch02.Theorems.GradientUniqueness

/-!
# Descendant averages of the response optimizer gradient

The measurable descendant-gradient representative agrees with the gradient of
the canonical source-coefficient optimizer in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The measurable descendant-gradient representative equals the descendant
averages of the canonical optimizer for the source coefficient. -/
theorem sourceCanonicalGradientAverage_descendant_eq {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q R : TriadicCube d) (j k : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun =
    cubeAverageVec R (fun x => (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution.toH1.grad x) := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (regularCoefficient a) (regularCoefficient_locallyElliptic a)
  let A : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) := F.coeffOn Q
  let B : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk
  let v := (Book.Ch02.canonicalMaximizer
    (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) A) p q).toSolution
  let w := (Book.Ch02.canonicalMaximizer
    (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) B) p q).toSolution
  have hrep := Book.Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
    (regularCoefficient a) (regularCoefficient_locallyElliptic a) hR p q
  calc
    _ = cubeAverageVec R (fun x => v.toH1.grad x) := by simpa [F, A, v] using hrep
    _ = cubeAverageVec R (fun x => w.toH1.grad x) := by
      rfl
    _ = _ := rfl

end EinsteinFull.Homogenization
