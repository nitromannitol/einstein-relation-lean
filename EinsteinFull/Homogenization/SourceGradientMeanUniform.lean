import EinsteinFull.Homogenization.SourceGradientBlockGeometric
import EinsteinFull.Homogenization.SourceDualCoarseBound
import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
import Homogenization.Probability.EfronStein.TwoPoint

/-!
# Uniform bound for the mean optimizer gradient

Uniform ellipticity and the response-energy estimate bound the annealed
optimizer gradient in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 2.2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The canonical optimizer's average gradient is uniformly bounded for
unit-ball loadings, on every triadic cube. -/
theorem vecNormSq_sourceOptimizer_averageGradient_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K) (a : Coefficient d K) (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    vecNormSq (Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution) ≤
      (2 * d) * (K + 4) := by
  let U := Book.Ch02.cubeDomain Q
  let A := sourceCoeffOn a U k hk
  let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
  let J := Book.Ch02.responseJ U A p q
  let E := Book.Ch02.variationEnergyValue U A v
  have hdot : -1 ≤ vecDot p q := by
    have h := neg_le_abs (vecDot p q)
    have habs := abs_vecDot_le_add_halves_vecNormSq p q
    linarith
  have heq : EinsteinRelation.euclideanSq (-p) = vecNormSq p := by
    simp [EinsteinRelation.euclideanSq, EinsteinRelation.dot, vecNormSq, vecDot]
  have hJ : J ≤ K / 2 + 2 := by
    have h := (sourceResponseJ_cube_bounds hK a Q k hk p q).2
    rw [heq] at h
    dsimp only [J, U, A]
    nlinarith [vecNormSq_nonneg p, vecNormSq_nonneg q]
  have hJ0 : 0 ≤ J := Book.Ch02.responseJ_nonneg U A p q
  have hJE : J = (1 / 2 : ℝ) * E :=
    Book.Ch02.responseJ_eq_energy_of_isResponseMaximizer
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).isMaximizer
  have hE0 : 0 ≤ E := by linarith
  have hE : E ≤ K + 4 := by linarith
  have hM := sourceDualCoarseMatrix_norm_le a Q k hk
  have hpoint := Book.Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue U A v
  calc
    _ ≤ Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U A) * E := hpoint
    _ ≤ (2 * d) * (K + 4) :=
      mul_le_mul hM hE hE0 (by positivity)

/-- The annealed optimizer gradient is uniformly bounded for unit loadings. -/
theorem integrable_and_vecNormSq_mean_sourceGradient_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution
    (∀ i, Integrable (fun a => F a i) P) ∧
    vecNormSq (fun i => ∫ a, F a i ∂P) ≤ (2 * (d : ℝ) ^ 2) * (K + 4) := by
  classical
  intro F
  let C : ℝ := (2 * d) * (K + 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (a : Coefficient d K) : vecNormSq (F a) ≤ C :=
    vecNormSq_sourceOptimizer_averageGradient_le hK a (originCube d (n : ℤ)) k hk p q hp hq
  have hsq (a : Coefficient d K) (i : Fin d) : (F a i) ^ 2 ≤ C :=
    (sq_apply_le_vecNormSq (F a) i).trans (hbound a)
  have hm (i : Fin d) : Measurable (fun a => F a i) :=
    (measurable_sourceResponseAverageGradient_cube (K := K)
      (originCube d (n : ℤ)) k hk p q i).mono
      (coefficientLocalSigma_le_coefficientSigma _) le_rfl
  have hF (i : Fin d) : MemLp (fun a => F a i) 2 P :=
    memLp_sourceResponseAverageGradient_cube P (originCube d (n : ℤ)) k hk p q i 2
  have hi (i : Fin d) : (∫ a, F a i ∂P) ^ 2 ≤ C := by
    have habs (a : Coefficient d K) : |F a i| ≤ Real.sqrt C := by
      have h := hsq a i
      nlinarith [Real.sqrt_nonneg C, Real.sq_sqrt hC, sq_abs (F a i)]
    have hj := sq_integral_le_integral_sq P (hm i) habs
    have he := integral_mono (hF i).integrable_sq (integrable_const C) (fun a => hsq a i)
    simp only [integral_const, probReal_univ, one_smul] at he
    linarith
  refine ⟨fun i => (hF i).integrable (by norm_num), ?_⟩
  unfold vecNormSq vecDot
  calc
    _ = ∑ i : Fin d, (∫ a, F a i ∂P) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sq _).symm
    _ ≤ ∑ _i : Fin d, C := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, C]; ring

end EinsteinFull.Homogenization
