import EinsteinFull.Homogenization.SourceOptimizerRemainderEnergy
import EinsteinFull.Homogenization.SourceGradientBlockRoot
import EinsteinFull.Homogenization.SourceOptimizerGradientDescendantBridge

/-!
# A multiscale majorant for optimizer flatness

The deterministic multiscale Poincaré bound and finite-range block estimates
provide a square-integrable majorant for the optimizer's affine remainder in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemma 2.15.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The optimizer's affine remainder is dominated by a square-integrable sum
of block root mean squares, with a dimension-only Poincaré constant. -/
theorem exists_sourceOptimizer_flatness_majorant (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ} (_hK : 0 ≤ K)
      (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (_hP : AKMFiniteRange P)
      (_hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
      (N k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
      (_hp : vecNormSq p < 1) (_hq : vecNormSq q < 1),
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
      let H := fun a => Real.sqrt ((2 + 4 * (d : ℝ) ^ 2) * (K + 4)) +
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
      (∀ i, Integrable (fun a => F a i) P) ∧ MemLp H 2 P ∧
      ∀ a : Coefficient d K,
        let U := Book.Ch02.cubeDomain Q
        let A := sourceCoeffOn a U k hk
        let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤ C * H a := by
  obtain ⟨C, hC, hPoinc⟩ := exists_sourceOptimizer_multiscalePoincare d
  refine ⟨C, hC, ?_⟩
  intro K hK P _ hP hstat N k hk p q hp hq Q F b G H
  have henergy := integrable_and_sourceOptimizer_meanSlope_energy_le hK P N N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ _ at henergy
  have hG (j : ℕ) (hj : j ∈ Finset.range (N + 1)) : Integrable (G j) P := by
    have hjN : j ≤ N := by simp only [Finset.mem_range] at hj; omega
    have hdiff : N - (N - j) = j := by omega
    have h := integrable_and_integral_sourceGradientBlockDeviation_le_geometric
      hK P hP hstat (N - j) N N k (Nat.sub_le _ _) (Nat.sub_le _ _) hk p q hp hq
    simpa only [hdiff] using h.1
  have hG0 (j : ℕ) (a : Coefficient d K) : 0 ≤ G j a := by
    apply descendantsAverage_nonneg
    intro R _
    exact vecNormSq_nonneg _
  have hHs : MemLp H 2 P := by
    have hs := memLp_finsetSum (Finset.range (N + 1)) (fun j hj =>
      (memLp_sqrt_two_of_integrable_of_ae_nonneg (hG j hj)
        (Filter.Eventually.of_forall (hG0 j))).const_mul ((3 : ℝ) ^ (N - j)))
    have hc : MemLp (fun _ : Coefficient d K => Real.sqrt ((2 + 4 * (d : ℝ) ^ 2) * (K + 4))) 2 P :=
      memLp_const _
    exact hc.add hs
  refine ⟨henergy.1, hHs, ?_⟩
  intro a U A v
  have hbound := hPoinc N k hk a p q b
  change _ ∧ _ ∧ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤ _ at hbound
  have hgrad := (henergy.2 a).2
  change (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x - b))) ^ 2 ≤ _ at hgrad
  have hT : 0 ≤ (2 + 4 * (d : ℝ) ^ 2) * (K + 4) := by positivity
  have hL : cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x - b)) ≤
      Real.sqrt ((2 + 4 * (d : ℝ) ^ 2) * (K + 4)) := by
    nlinarith [cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => euclideanNorm (v.toH1.grad x - b)),
      Real.sqrt_nonneg ((2 + 4 * (d : ℝ) ^ 2) * (K + 4)), Real.sq_sqrt hT]
  have hrep (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      descendantsAverage Q j (fun R => vecNormSq
        (fun i => cubeAverage R (fun x => v.toH1.grad x i) - b i)) = G j a := by
    apply descendantsAverage_congr_of_eq_on_descendants
    intro R hR
    have h := sourceCanonicalGradientAverage_descendant_eq a Q R j k hR hk p q
    change Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun = cubeAverageVec R (fun x => v.toH1.grad x) at h
    rw [h]
    rfl
  calc
    _ ≤ _ := hbound.2.2
    _ ≤ C * H a := by
      apply mul_le_mul_of_nonneg_left _ hC
      dsimp only [H]
      apply add_le_add hL
      apply Finset.sum_le_sum
      intro j hj
      rw [hrep j hj]

end EinsteinFull.Homogenization
