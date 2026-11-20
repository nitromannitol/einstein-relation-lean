import EinsteinFull.Homogenization.SourceOptimizerFlatnessMajorant
import EinsteinFull.Homogenization.WeightedSquareRoot

/-!
# Mean-square bound for weighted optimizer block deviations

A weighted Cauchy–Schwarz inequality combines the block estimates in the
flatness argument of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.15.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The weighted sum of block root mean squares is square-integrable, and its
second moment is bounded by the corresponding geometric defect expression. -/
theorem integrable_and_integral_sq_sourceOptimizer_weightedBlocks_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (N k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let B : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
    let D : ℝ := (1 + 2 / η) * (4 * d)
    let Q := originCube d (N : ℤ)
    let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
    let b := fun i => ∫ a, F a i ∂P
    let G := fun j a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun - b))
    let T := fun j =>
      (8 * d) * (∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk) +
      (8 * d) * (θ ^ (N - j) * B + D * ∑ l ∈ Finset.range (N - j + 1),
        θ ^ (N - j - l) * sourceResponseTau P l k hk) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk
    let Y := fun a => ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
    (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (Y a) ^ 2) P ∧
    (∫ a, (Y a) ^ 2 ∂P) ≤
      (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T j := by
  intro η θ B D Q F b G T Y
  have hG (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      Integrable (G j) P ∧ (∫ a, G j a ∂P) ≤ T j := by
    have hjN : j ≤ N := by simp only [Finset.mem_range] at hj; omega
    have hdiff : N - (N - j) = j := by omega
    have h := integrable_and_integral_sourceGradientBlockDeviation_le_geometric
      hK P hP hstat (N - j) N N k (Nat.sub_le _ _) (Nat.sub_le _ _) hk p q hp hq
    constructor
    · simpa only [hdiff] using h.1
    · simpa only [hdiff] using h.2.2
  have hG0 (j : ℕ) (a : Coefficient d K) : 0 ≤ G j a := by
    apply descendantsAverage_nonneg
    intro R _
    exact vecNormSq_nonneg _
  have hw (j : ℕ) (_ : j ∈ Finset.range (N + 1)) : 0 ≤ (3 : ℝ) ^ (N - j) := by positivity
  have hs := integrable_and_integral_sq_sum_weighted_sqrt_le P (Finset.range (N + 1))
    (fun j => (3 : ℝ) ^ (N - j)) G hw (fun j hj => (hG j hj).1)
    (fun j _ a => hG0 j a)
  change Integrable (fun a => (Y a) ^ 2) P ∧ _ at hs
  refine ⟨fun i => (memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2).integrable
    (by norm_num), hs.1, ?_⟩
  calc
    _ ≤ (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * ∫ a, G j a ∂P := hs.2
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg hw)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hG j hj).2 (hw j hj)

/-- The full multiscale majorant has an explicit second-moment bound in
terms of response-defect sums. -/
theorem integrable_and_integral_sq_sourceOptimizer_flatnessMajorant_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (N k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let B : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
    let D : ℝ := (1 + 2 / η) * (4 * d)
    let Q := originCube d (N : ℤ)
    let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
    let b := fun i => ∫ a, F a i ∂P
    let G := fun j a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun - b))
    let T := fun j =>
      (8 * d) * (∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk) +
      (8 * d) * (θ ^ (N - j) * B + D * ∑ l ∈ Finset.range (N - j + 1),
        θ ^ (N - j - l) * sourceResponseTau P l k hk) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk
    let Y := fun a => ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
    let A : ℝ := (2 + 4 * (d : ℝ) ^ 2) * (K + 4)
    let H := fun a => Real.sqrt A + Y a
    (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (H a) ^ 2) P ∧
    (∫ a, (H a) ^ 2 ∂P) ≤ 2 * A +
      2 * ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T j) := by
  intro η θ B D Q F b G T Y A H
  have hw := integrable_and_integral_sq_sourceOptimizer_weightedBlocks_le
    hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (Y a) ^ 2) P ∧ _ at hw
  obtain ⟨C, hC, hmajor⟩ := exists_sourceOptimizer_flatness_majorant d
  have hmaj := hmajor hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ MemLp H 2 P ∧ _ at hmaj
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (a : Coefficient d K) : (H a) ^ 2 ≤ 2 * A + 2 * (Y a) ^ 2 := by
    dsimp only [H]
    nlinarith [sq_nonneg (Real.sqrt A - Y a), Real.sq_sqrt hA]
  have hH := hmaj.2.1.integrable_sq
  have hY : (∫ a, (Y a) ^ 2 ∂P) ≤
      (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T j := hw.2.2
  refine ⟨hw.1, hH, ?_⟩
  calc
    _ ≤ ∫ a, 2 * A + 2 * (Y a) ^ 2 ∂P :=
      integral_mono hH ((integrable_const _).add (hw.2.1.const_mul 2)) hpoint
    _ = 2 * A + 2 * (∫ a, (Y a) ^ 2 ∂P) := by
      rw [integral_add (integrable_const _) (hw.2.1.const_mul 2), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      rw [integral_const_mul]
    _ ≤ _ := by
      have h2 := mul_le_mul_of_nonneg_left hY (show (0 : ℝ) ≤ 2 by norm_num)
      linarith

end EinsteinFull.Homogenization
