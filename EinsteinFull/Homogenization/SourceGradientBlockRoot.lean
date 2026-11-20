import EinsteinFull.Homogenization.SourceGradientBlockGeometric
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

/-!
# Expected root mean square of optimizer block deviations

The square-root form of the block estimate is used in the multiscale
flatness argument of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 2.2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- Expected root mean square block deviations obey the square root of the
geometric response-defect bound. -/
theorem integrable_and_integral_sqrt_sourceGradientBlockDeviation_le_geometric
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (m N r k : ℕ) (hmN : m ≤ N) (hmr : m ≤ r) (hk : K ≤ (k : ℝ) + 1)
    (p q : Vec d) (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let B : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
    let D : ℝ := (1 + 2 / η) * (4 * d)
    let F := fun s a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (s : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (s : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (s : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (s : ℤ))) k hk)) p q).toSolution
    let b := fun i => ∫ a, F r a i ∂P
    let G := fun a => descendantsAverage (originCube d (N : ℤ)) (N - m) (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet
        (originCube d (N : ℤ)) R p q (regularCoefficient a).toFun - b))
    (∀ s i, Integrable (fun a => F s a i) P) ∧ Integrable G P ∧
    Integrable (fun a => Real.sqrt (G a)) P ∧
    (∫ a, Real.sqrt (G a) ∂P) ≤ Real.sqrt (
      (8 * d) * (∑ l ∈ Finset.Ico m N, sourceResponseTau P l k hk) +
      (8 * d) * (θ ^ m * B + D * ∑ l ∈ Finset.range (m + 1),
        θ ^ (m - l) * sourceResponseTau P l k hk) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico m r, sourceResponseTau P l k hk) := by
  intro η θ B D F b G
  have h := integrable_and_integral_sourceGradientBlockDeviation_le_geometric
    hK P hP hstat m N r k hmN hmr hk p q hp hq
  change Integrable G P ∧ (∀ s i, Integrable (fun a => F s a i) P) ∧ _ at h
  have hnonneg (a : Coefficient d K) : 0 ≤ G a := by
    apply descendantsAverage_nonneg
    intro R _
    exact vecNormSq_nonneg _
  have hS := memLp_sqrt_two_of_integrable_of_ae_nonneg h.1
    (Filter.Eventually.of_forall hnonneg)
  refine ⟨h.2.1, h.1, hS.integrable (by norm_num), ?_⟩
  have hcs := integral_sqrt_mul_sqrt_le_sqrt_integral_mul_sqrt_integral
    h.1 (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall (fun _ : Coefficient d K => (show (0 : ℝ) ≤ 1 by norm_num)))
  simp only [Real.sqrt_one, mul_one, integral_const, probReal_univ, one_smul] at hcs
  exact hcs.trans (Real.sqrt_le_sqrt h.2.2)

end EinsteinFull.Homogenization
