import EinsteinFull.Homogenization.SourceOptimizerGradientStationarity

/-!
# Stationarity of mean optimizer gradients

Stationarity of the coefficient law identifies the expected averaged response
optimizer gradients on cubes of the same scale, as in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The expected optimizer gradient coordinate is independent of the cube
position at a fixed nonnegative scale. -/
theorem integral_sourceResponseAverageGradient_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n k : ℕ) (hscale : Q.scale = n)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    (∫ a, Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i ∂P) =
    ∫ a, Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i ∂P := by
  let z : LatticeIndex d := fun l => Q.index l * (3 : ℤ) ^ n
  have hmp : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hP z⟩
  let F := fun R a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
    (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution i
  change (∫ a, F Q a ∂P) = ∫ a, F (originCube d (n : ℤ)) a ∂P
  have hf : F Q = fun a => F (originCube d (n : ℤ))
      (translateCoefficient (latticeShift z) a) := by
    funext a
    exact sourceResponseAverageGradient_cube_eq_origin a Q n k hscale hk p q i
  rw [hf]
  have hm := (measurable_sourceResponseAverageGradient_cube (K := K)
    (originCube d (n : ℤ)) k hk p q i).mono
      (coefficientLocalSigma_le_coefficientSigma _) le_rfl
  have hi := integral_map hmp.measurable.aemeasurable (by
    rw [hmp.map_eq]
    exact hm.aestronglyMeasurable)
  rw [hmp.map_eq] at hi
  exact hi.symm

end EinsteinFull.Homogenization
