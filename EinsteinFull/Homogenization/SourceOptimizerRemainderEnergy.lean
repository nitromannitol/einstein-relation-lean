import EinsteinFull.Homogenization.SourceOptimizerEnergyBound
import EinsteinFull.Homogenization.SourceGradientMeanUniform

/-!
# Uniform optimizer remainder energy

The response optimizer's gradient relative to the annealed mean slope has
uniform normalized `L²` energy, as in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (2.49).
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- For unit loadings, the optimizer gradient relative to any scale's mean
slope has a scale-uniform `L²` bound depending only on dimension and the
ellipticity bound. -/
theorem integrable_and_sourceOptimizer_meanSlope_energy_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n r k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution
    let b := fun i => ∫ a, F a i ∂P
    (∀ i, Integrable (fun a => F a i) P) ∧
    ∀ a : Coefficient d K,
      let Q := originCube d (n : ℤ)
      let U := Book.Ch02.cubeDomain Q
      let A := sourceCoeffOn a U k hk
      let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
      MemLp (fun x => euclideanNorm (v.toH1.grad x - b)) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ∧
      (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x - b))) ^ 2 ≤
        (2 + 4 * (d : ℝ) ^ 2) * (K + 4) := by
  intro F b
  have hmean := integrable_and_vecNormSq_mean_sourceGradient_le hK P r k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧
    vecNormSq b ≤ (2 * (d : ℝ) ^ 2) * (K + 4) at hmean
  refine ⟨hmean.1, ?_⟩
  intro a Q U A v
  have hgrad := memLp_and_sourceOptimizer_gradient_sub_norm_sq_le_response a Q k hk p q b
  change MemLp (fun x => euclideanNorm (v.toH1.grad x - b)) (2 : ℝ≥0∞)
    (normalizedCubeMeasure Q) ∧ _ at hgrad
  refine ⟨hgrad.1, ?_⟩
  have hdot : -1 ≤ vecDot p q := by
    have h := neg_le_abs (vecDot p q)
    have habs := abs_vecDot_le_add_halves_vecNormSq p q
    linarith
  have heq : EinsteinRelation.euclideanSq (-p) = vecNormSq p := by
    simp [EinsteinRelation.euclideanSq, EinsteinRelation.dot, vecNormSq, vecDot]
  have hJ : Book.Ch02.responseJ U A p q ≤ K / 2 + 2 := by
    have h := (sourceResponseJ_cube_bounds hK a Q k hk p q).2
    rw [heq] at h
    nlinarith [vecNormSq_nonneg p, vecNormSq_nonneg q]
  calc
    _ ≤ 4 * Book.Ch02.responseJ U A p q + 2 * vecNormSq b := hgrad.2
    _ ≤ 4 * (K / 2 + 2) + 2 * ((2 * (d : ℝ) ^ 2) * (K + 4)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hJ (by norm_num))
        (mul_le_mul_of_nonneg_left hmean.2 (by norm_num))
    _ = _ := by ring

end EinsteinFull.Homogenization
