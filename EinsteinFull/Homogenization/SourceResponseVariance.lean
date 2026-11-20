import EinsteinFull.Homogenization.SourceResponseIndependence
import Mathlib.Probability.Moments.Variance

/-!
# Moments of separated responses

The bounded response energies of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, have finite
moments and satisfy variance additivity on separated cubes.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Uniform ellipticity bounds the response on every triadic cube. -/
theorem sourceResponseJ_cube_bounds {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (a : Coefficient d K) (Q : TriadicCube d) (k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    0 ≤ Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∧
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ≤
      (K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q := by
  refine ⟨Book.Ch02.responseJ_nonneg _ _ _ _, ?_⟩
  rw [responseJ_eq_sourceDirichlet_add_sourceDual]
  have hd := sourceDirichletEnergy_le_ellipticity hK a (openCubeSet Q)
    (ne_of_lt (volume_openCubeSet_lt_top Q)) (-p)
  have hq := (sourceDualEnergy_cube_bounds a Q q).2
  change sourceDirichletEnergy a (openCubeSet Q) (-p) +
    sourceDualEnergy a (Book.Ch02.cubeDomain Q) q - vecDot p q ≤ _
  linarith

/-- Response energies belong to every finite or infinite Lp space under a
finite coefficient law. -/
theorem memLp_sourceResponseJ_cube {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (r : ENNReal) :
    MemLp (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) r P := by
  have hm := (measurable_sourceResponseJ_cube Q k hk p q).mono
    (coefficientLocalSigma_le_coefficientSigma _) le_rfl
  apply MemLp.of_bound hm.aestronglyMeasurable
    ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q)
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (sourceResponseJ_cube_bounds hK a Q k hk p q).1]
  exact (sourceResponseJ_cube_bounds hK a Q k hk p q).2

/-- The variance of a sum of separated responses is the sum of their variances. -/
theorem variance_sum_sourceResponseJ_of_separated {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (s : ℝ) (hs : 1 < s) (Q : ι → TriadicCube d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ cubeSet (Q i), ∀ y ∈ cubeSet (Q j),
      s ≤ EinsteinRelation.euclideanNorm (x - y))
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : ι → Vec d) (S : Finset ι) :
    ProbabilityTheory.variance (∑ i ∈ S, fun a =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) (p i) (q i)) P =
    ∑ i ∈ S, ProbabilityTheory.variance (fun a =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) (p i) (q i)) P := by
  apply ProbabilityTheory.IndepFun.variance_sum
  · intro i _
    exact memLp_sourceResponseJ_cube hK P (Q i) k hk (p i) (q i) 2
  · intro i _ j _ hij
    exact (iIndepFun_sourceResponseJ_of_separated P hP s hs Q hsep k hk p q).indepFun hij

end EinsteinFull.Homogenization
