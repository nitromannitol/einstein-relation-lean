import EinsteinFull.Homogenization.SourceGradientDeviationVariance
import EinsteinFull.Homogenization.SourceGradientMeanVectorScale

/-!
# Block deviations and response defects

The response defect sums control the mean-gradient and response-gap terms in
the block estimate of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.50).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected parent-optimizer gradient deviation on descendant blocks is
bounded by response-defect sums and the descendant optimizer variance. -/
theorem integrable_and_integral_sourceGradientBlockDeviation_le_tau
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (m N r k : ℕ) (hmN : m ≤ N) (hmr : m ≤ r) (hk : K ≤ (k : ℝ) + 1)
    (p q : Vec d) (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let F := fun s a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (s : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (s : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (s : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (s : ℤ))) k hk)) p q).toSolution
    let b := fun i => ∫ a, F r a i ∂P
    let G := fun a => descendantsAverage (originCube d (N : ℤ)) (N - m) (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet
        (originCube d (N : ℤ)) R p q (regularCoefficient a).toFun - b))
    Integrable G P ∧ (∀ s i, Integrable (fun a => F s a i) P) ∧
    (∫ a, G a ∂P) ≤
      (8 * d) * (∑ l ∈ Finset.Ico m N, sourceResponseTau P l k hk) +
      4 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => F m a i) P) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico m r, sourceResponseTau P l k hk := by
  intro F b G
  let Q := originCube d (N : ℤ)
  have hscale : Q.scale = (m : ℤ) + ((N - m : ℕ) : ℤ) := by
    dsimp [Q]
    simp only [originCube, Nat.cast_sub hmN]
    ring
  have hblock := integrable_and_integral_sourceGradientBlockDeviation_le_variance
    hK P hstat Q (N - m) m hscale k hk p q b
  change Integrable G P ∧ _ at hblock
  have hmean := integrable_and_vecNormSq_integral_sourceGradient_sub_le_sum_tau
    hK P hstat m r k hmr hk p q hp hq
  have hgap := expected_sourceResponseJ_sub_le_sum_tau hK P m N k hmN hk p q hp hq
  have hmean' : vecNormSq ((fun i => ∫ a, F m a i ∂P) - b) ≤
      (4 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico m r, sourceResponseTau P l k hk := by
    have hh := hmean.2
    change vecNormSq (fun i => (∫ a, F r a i ∂P) - (∫ a, F m a i ∂P)) ≤ _ at hh
    have heven : vecNormSq ((fun i => ∫ a, F m a i ∂P) - b) =
        vecNormSq (fun i => (∫ a, F r a i ∂P) - (∫ a, F m a i ∂P)) := by
      dsimp only [b, vecNormSq, vecDot, Pi.sub_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heven]
    exact hh
  have hgap' := mul_le_mul_of_nonneg_left hgap.2 (show 0 ≤ (8 * d : ℝ) by positivity)
  have hmean'' := mul_le_mul_of_nonneg_left hmean' (show (0 : ℝ) ≤ 4 by norm_num)
  refine ⟨hblock.1, ?_, ?_⟩
  · intro s i
    exact (memLp_sourceResponseAverageGradient_cube P (originCube d (s : ℤ)) k hk p q i 2).integrable (by norm_num)
  · have hb := hblock.2.2.2.2
    change (∫ a, G a ∂P) ≤
      (8 * d) * ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk) p q ∂P) -
      ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (N : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (N : ℤ))) k hk) p q ∂P) +
      4 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => F m a i) P) +
      4 * vecNormSq ((fun i => ∫ a, F m a i ∂P) - b) at hb
    linarith [hgap', hmean'']

end EinsteinFull.Homogenization
