import EinsteinFull.Homogenization.SourceOptimizerGradientLocality
import EinsteinFull.Homogenization.SourceDualAnnealed
import Mathlib.Probability.Moments.Variance

/-!
# Stationarity of averaged optimizer gradients

Translation covariance of the response optimizer in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, gives the same variance on all cubes of a given scale.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- A dual coarse-matrix entry on a translated cube is the corresponding entry
at the origin for the translated coefficient field. -/
theorem sourceDualCoarseMatrix_entry_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (n k : ℕ)
    (hscale : Q.scale = n) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    let z : LatticeIndex d := fun l => Q.index l * (3 : ℤ) ^ n
    Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) i j =
    Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn (translateCoefficient (latticeShift z) a)
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) i j := by
  intro z
  simp_rw [sourceDualCoarseMatrix_entry_eq_polar]
  have hq (q : Vec d) : sourceDualEnergy a (Book.Ch02.cubeDomain Q) q =
      sourceDualEnergy (translateCoefficient (latticeShift z) a)
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q := by
    apply sourceDualEnergy_translate
    change openCubeSet Q = translateSet (latticeShift z) (openCubeSet (originCube d (n : ℤ)))
    simpa only [sourceTriadicCube_eq_openCubeSet] using
      openCubeSet_eq_latticeTranslate_sourceTriadicCube Q n hscale
  simp_rw [hq]

/-- The response optimizer's averaged gradient coordinate commutes with
translation of a cube and the coefficient field. -/
theorem sourceResponseAverageGradient_cube_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (n k : ℕ)
    (hscale : Q.scale = n) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let z : LatticeIndex d := fun l => Q.index l * (3 : ℤ) ^ n
    Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i =
    Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn (translateCoefficient (latticeShift z) a)
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn (translateCoefficient (latticeShift z) a)
            (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i := by
  intro z
  rw [Book.Ch02.averageGradient_canonicalMaximizer_eq,
    Book.Ch02.averageGradient_canonicalMaximizer_eq]
  have hz (b : Coefficient d K) (R : TriadicCube d) :=
    (Book.Ch02.responseSymmetricDirichletNeumannTheory
      (Book.Ch02.cubeDomain R) (sourceCoeffOn b (Book.Ch02.cubeDomain R) k hk)
      (sourceCoeffOn_isSymmetric b (Book.Ch02.cubeDomain R) k hk)).kappa_eq_zero
  simp only [hz, matVecMul_zero, add_zero, Pi.add_apply, Pi.neg_apply]
  congr 1
  simp only [matVecMul]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceDualCoarseMatrix_entry_eq_origin a Q n k hscale hk i j]

/-- Under stationarity, the variance of an averaged gradient coordinate depends
only on the nonnegative triadic scale. -/
theorem variance_sourceResponseAverageGradient_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n k : ℕ) (hscale : Q.scale = n)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i) P =
    ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution i) P := by
  let z : LatticeIndex d := fun l => Q.index l * (3 : ℤ) ^ n
  have hmp : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hP z⟩
  have hm := (measurable_sourceResponseAverageGradient_cube (K := K)
    (originCube d (n : ℤ)) k hk p q i).mono
      (coefficientLocalSigma_le_coefficientSigma _) le_rfl
  let F := fun R a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
    (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution i
  change ProbabilityTheory.variance (F Q) P =
    ProbabilityTheory.variance (F (originCube d (n : ℤ))) P
  have hf : F Q = fun a => F (originCube d (n : ℤ))
      (translateCoefficient (latticeShift z) a) := by
    funext a
    exact sourceResponseAverageGradient_cube_eq_origin a Q n k hscale hk p q i
  rw [hf]
  exact hmp.variance_fun_comp hm.aemeasurable

end EinsteinFull.Homogenization
