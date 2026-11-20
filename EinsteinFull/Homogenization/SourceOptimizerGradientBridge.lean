import EinsteinFull.Homogenization.SourceOptimizerGradientLocality
import EinsteinFull.Homogenization.SourceResponseDefect
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CoarseAverages

/-!
# Whole-cube optimizer gradient representatives

The whole-cube gradient average used for the response energy of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Chapter 2, agrees with the measurable representative used for
its descendant averages.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The Chapter 4 whole-cube representative equals the Chapter 2 average on
source coefficients. -/
theorem sourceCanonicalGradientAverage_self_eq {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
      (regularCoefficient a).toFun =
    Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (regularCoefficient a) (regularCoefficient_locallyElliptic a)
  let A : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) := F.coeffOn Q
  let B : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk
  let v := (Book.Ch02.canonicalMaximizer
    (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) A) p q).toSolution
  have hself : Q ∈ descendantsAtDepth Q 0 := by simp [descendantsAtDepth_zero]
  have havg := Book.Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
    (regularCoefficient a) (regularCoefficient_locallyElliptic a) (Q := Q) (R := Q)
    (j := 0) hself p q
  have hcube : cubeAverageVec Q (fun x => v.toH1.grad x) =
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q) A v := by
    ext i
    rw [Book.Ch02.averageGradient, Book.Ch02.averageVec,
      Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have hcoeff : A.toCoeffField =ᵐ[volumeMeasureOn (Book.Ch02.cubeDomain Q)] B.toCoeffField :=
    Filter.EventuallyEq.rfl
  calc
    _ = cubeAverageVec Q (fun x => v.toH1.grad x) := by simpa [F, A, v] using havg
    _ = Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q) A v := hcube
    _ = -p + matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) A)
        (q + matVecMul (Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain Q) A) p) :=
      Book.Ch02.averageGradient_canonicalMaximizer_eq _ _ _ _
    _ = -p + matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) B)
        (q + matVecMul (Book.Ch02.kappaCoarse (Book.Ch02.cubeDomain Q) B) p) := by
      rw [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hcoeff,
        Book.Ch02.kappaCoarse_eq_ofAEEq hcoeff]
    _ = _ := (Book.Ch02.averageGradient_canonicalMaximizer_eq _ _ _ _).symm

/-- Whole-cube Chapter 4 gradient representatives on separated cubes are
jointly independent, coordinate by coordinate. -/
theorem iIndepFun_sourceCanonicalGradientAverage_of_separated {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (hP : AKMFiniteRange P) (s : ℝ) (hs : 1 < s)
    (Q : ι → TriadicCube d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ cubeSet (Q i), ∀ y ∈ cubeSet (Q j),
      s ≤ EinsteinRelation.euclideanNorm (x - y))
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : ι → Vec d) (coord : ι → Fin d) :
    ProbabilityTheory.iIndepFun (fun i a =>
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet (Q i) (Q i)
        (p i) (q i) (regularCoefficient a).toFun (coord i)) P := by
  simpa only [sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using
    iIndepFun_sourceResponseAverageGradient_of_separated P hP s hs Q hsep k hk p q coord

end EinsteinFull.Homogenization
