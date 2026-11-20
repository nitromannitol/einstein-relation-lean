import EinsteinFull.Homogenization.SourceOptimizerFlatnessPreviousScale
import EinsteinFull.Homogenization.SourceAnnealedDualMatrix
import EinsteinFull.Homogenization.SourceGradientMeanMatrix

/-!
# Flatness at the annealed matrix slope

The preceding-scale optimizer gradient has the annealed matrix expression
used in the flatness estimate of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.15.
-/

open scoped ENNReal
open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The preceding-scale mean gradient equals the affine slope defined by the
annealed dual coarse matrix. -/
theorem integral_sourceGradient_eq_annealedDualMatrix
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let R := originCube d (n : ℤ)
    let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution
    (∀ i, Integrable (fun a => F a i) P) ∧
      (fun i => ∫ a, F a i ∂P) = matVecMul (annealedDualMatrix P n k hk) q - p := by
  intro R F
  refine ⟨fun i => (integral_sourceResponseAverageGradient_eq P n k hk p q i).1, ?_⟩
  funext i
  have h := (integral_sourceResponseAverageGradient_eq P n k hk p q i).2.2
  change (∫ a, F a i ∂P) = -p i + ∑ j : Fin d,
    (∫ a, Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) i j ∂P) * q j at h
  simpa only [annealedDualMatrix, matVecMul, Pi.sub_apply, neg_add_eq_sub] using h

/-- At the annealed dual-matrix slope, normalized optimizer remainders admit
nonnegative square-integrable majorants with a common vanishing second-moment
bound over unit loadings. -/
theorem exists_tendsto_zero_sourceOptimizer_annealedSlope_majorant
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ (n : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 →
      let Q := originCube d ((n + 1 : ℕ) : ℤ)
      let R := originCube d (n : ℤ)
      let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
            (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution
      let b := matVecMul (annealedDualMatrix P n k hk) q - p
      (∀ i, Integrable (fun a => F a i) P) ∧
      ∃ H : Coefficient d K → ℝ, MemLp H 2 P ∧ (∀ a, 0 ≤ H a) ∧
        (∀ a, let U := Book.Ch02.cubeDomain Q
          let A := sourceCoeffOn a U k hk
          let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤
            C * (3 : ℝ) ^ (n + 1) * H a) ∧
        Integrable (fun a => (H a) ^ 2) P ∧ (∫ a, (H a) ^ 2 ∂P) ≤ B n := by
  obtain ⟨C, hC, B, hB, hmajor⟩ :=
    exists_tendsto_zero_sourceOptimizer_previousSlope_majorant hK P hP hstat k hk
  refine ⟨C, hC, B, hB, ?_⟩
  intro n p q hp hq Q R F b
  have h := hmajor n p q hp hq
  have hb : (fun i => ∫ a, F a i ∂P) = b :=
    (integral_sourceGradient_eq_annealedDualMatrix P n k hk p q).2
  dsimp only at h
  rw [hb] at h
  exact h

end EinsteinFull.Homogenization
