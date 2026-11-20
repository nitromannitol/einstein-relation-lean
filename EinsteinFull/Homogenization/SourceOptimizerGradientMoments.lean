import EinsteinFull.Homogenization.SourceOptimizerGradientStationarity

/-!
# Moments of averaged optimizer gradients

The ellipticity bounds on dual energies give finite moments for the averaged
response optimizer gradients in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy on any triadic cube belongs to every Lp space under a
finite coefficient law. -/
theorem memLp_sourceDualEnergy_cube {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (Q : TriadicCube d)
    (q : Vec d) (r : ENNReal) :
    MemLp (fun a => sourceDualEnergy a (Book.Ch02.cubeDomain Q) q) r P := by
  apply MemLp.of_bound (measurable_sourceDualEnergy_cube_full Q q).aestronglyMeasurable
    (vecNormSq q)
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (sourceDualEnergy_cube_bounds a Q q).1]
  exact (sourceDualEnergy_cube_bounds a Q q).2

/-- Every coordinate of the averaged optimizer gradient has finite moments. -/
theorem memLp_sourceResponseAverageGradient_cube {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) (r : ENNReal) :
    MemLp (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution i) r P := by
  have hM (j : Fin d) : MemLp (fun a =>
      Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) i j) r P := by
    have h := ((memLp_sourceDualEnergy_cube P Q (Pi.single i 1 + Pi.single j 1) r).sub
      (memLp_sourceDualEnergy_cube P Q (Pi.single i 1) r)).sub
      (memLp_sourceDualEnergy_cube P Q (Pi.single j 1) r)
    convert h using 1
    funext a
    exact sourceDualCoarseMatrix_entry_eq_polar a _ k hk i j
  have h := (memLp_const (-p i)).add (memLp_finsetSum' Finset.univ (fun j _ =>
    (hM j).mul_const (q j)))
  convert h using 1
  funext a
  rw [Book.Ch02.averageGradient_canonicalMaximizer_eq]
  have hz := (Book.Ch02.responseSymmetricDirichletNeumannTheory
    (Book.Ch02.cubeDomain Q) (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    (sourceCoeffOn_isSymmetric a (Book.Ch02.cubeDomain Q) k hk)).kappa_eq_zero
  simp [hz, matVecMul]

end EinsteinFull.Homogenization
