import EinsteinFull.Homogenization.SourceOptimizerGradientBridge
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities

/-!
# Partition of response optimizer gradients

The average gradient of a response optimizer equals the average of its
subcube averages, as used in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The whole-cube optimizer gradient coordinate is the average of its
coordinates over any fixed generation of descendants. -/
theorem sourceResponseGradientAverage_eq_descendantsAverage
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K) (Q : TriadicCube d)
    (j : ℕ) (p q : Vec d) (i : Fin d) :
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i =
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun i) := by
  let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (regularCoefficient a) (regularCoefficient_locallyElliptic a)
  let A := F.coeffOn Q
  let v := (Book.Ch02.canonicalMaximizer
    (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q) A) p q).toSolution
  have hf : IntegrableOn (fun x => v.toH1.grad x i) (cubeSet Q) volume := by
    have h := canonicalMaximizerGradientDefectOnCube_component_integrableOn Q A p q 0 i
    simpa [canonicalMaximizerGradientDefectOnCube, canonicalMaximizerGradientOnCube,
      canonicalMaximizerSolutionOnCube, v] using h
  have hrep (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun i = cubeAverage R (fun x => v.toH1.grad x i) := by
    have h := congrFun
      (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
        (regularCoefficient a) (regularCoefficient_locallyElliptic a) hR p q) i
    simpa [cubeAverageVec, F, A, v] using h
  have hself : Q ∈ descendantsAtDepth Q 0 := by simp
  have hrepQ := congrFun
    (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
      (regularCoefficient a) (regularCoefficient_locallyElliptic a) hself p q) i
  calc
    _ = cubeAverage Q (fun x => v.toH1.grad x i) := by
      simpa [cubeAverageVec, F, A, v] using hrepQ
    _ = descendantsAverage Q j (fun R => cubeAverage R (fun x => v.toH1.grad x i)) :=
      cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hf
    _ = _ := by
      apply descendantsAverage_congr_of_eq_on_descendants
      intro R hR
      exact (hrep R hR).symm

end EinsteinFull.Homogenization
