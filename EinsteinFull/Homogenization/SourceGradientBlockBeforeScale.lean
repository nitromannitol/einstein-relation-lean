import EinsteinFull.Homogenization.SourceGradientBlockTau
import EinsteinFull.Homogenization.SourceGradientVarianceBeforeScale

/-!
# Geometric control of optimizer block deviations

The response-defect and gradient-variance estimates combine in the multiscale
argument of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.50).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Expected squared gradient deviations on descendant blocks are bounded by
response defects and the geometric variance estimate. -/
theorem integrable_and_integral_sourceGradientBlockDeviation_le_geometric_before
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
    Integrable G P ∧ (∀ s i, Integrable (fun a => F s a i) P) ∧
    (∫ a, G a ∂P) ≤
      (8 * d) * (∑ l ∈ Finset.Ico m N, sourceResponseTau P l k hk) +
      (8 * d) * (θ ^ m * B + D * ∑ l ∈ Finset.range m,
        θ ^ (m - l) * sourceResponseTau P l k hk) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico m r, sourceResponseTau P l k hk := by
  intro η θ B D F b G
  have h := integrable_and_integral_sourceGradientBlockDeviation_le_tau
    hK P hstat m N r k hmN hmr hk p q hp hq
  change Integrable G P ∧ (∀ s i, Integrable (fun a => F s a i) P) ∧ _ at h
  have hF (i : Fin d) : MemLp (fun a => F m a i) 2 P :=
    memLp_sourceResponseAverageGradient_cube P (originCube d (m : ℤ)) k hk p q i 2
  have hident := integrable_and_integral_vecNormSq_sub_mean_eq_sum_variance P (F m) hF
  have hvar := integrable_and_sourceGradientVectorVariance_le_geometric_before
    hK P hP hstat k hk p q hp hq m
  change (∀ i, Integrable (fun a => F m a i) P) ∧
    Integrable (fun a => vecNormSq (F m a - fun i => ∫ b, F m b i ∂P)) P ∧
    (∫ a, vecNormSq (F m a - fun i => ∫ b, F m b i ∂P) ∂P) ≤
      2 * (d : ℝ) * (θ ^ m * B + D * ∑ l ∈ Finset.range m,
        θ ^ (m - l) * sourceResponseTau P l k hk) at hvar
  have hsum : (∑ i : Fin d, ProbabilityTheory.variance (fun a => F m a i) P) ≤
      2 * (d : ℝ) * (θ ^ m * B + D * ∑ l ∈ Finset.range m,
        θ ^ (m - l) * sourceResponseTau P l k hk) := by
    rw [← hident.2.2]
    exact hvar.2.2
  refine ⟨h.1, h.2.1, ?_⟩
  have hb := h.2.2
  change (∫ a, G a ∂P) ≤
    (8 * d) * (∑ l ∈ Finset.Ico m N, sourceResponseTau P l k hk) +
    4 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => F m a i) P) +
    (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico m r, sourceResponseTau P l k hk at hb
  linarith [hb, hsum]

end EinsteinFull.Homogenization
