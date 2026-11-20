import EinsteinFull.Homogenization.SourceOptimizerWeightedBlocksBeforeScale
import EinsteinFull.Homogenization.GeometricDefectSumsBeforeScale

/-!
# Geometric estimate for the optimizer flatness majorant

The multiscale majorant has a second-moment bound in the geometric form used
in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemma 2.15.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The flatness majorant's second moment is controlled by a geometric decay
term and a geometric convolution of the response defects. -/
theorem integrable_and_integral_sq_sourceOptimizer_flatnessMajorant_le_geometric_before
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
    let _T := fun j =>
      (8 * d) * (∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk) +
      (8 * d) * (θ ^ (N - j) * B + D * ∑ l ∈ Finset.range (N - j),
        θ ^ (N - j - l) * sourceResponseTau P l k hk) +
      (16 * (d : ℝ) ^ 2) * ∑ l ∈ Finset.Ico (N - j) N, sourceResponseTau P l k hk
    let Y := fun a => ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
    let A : ℝ := (2 + 4 * (d : ℝ) ^ 2) * (K + 4)
    let H := fun a => Real.sqrt A + Y a
    (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (H a) ^ 2) P ∧
    (∫ a, (H a) ^ 2 ∂P) ≤
      (3 : ℝ) ^ (2 * N) *
        (2 * A + 9 * ((8 * d) * B + (8 * d) + (16 * (d : ℝ) ^ 2) + (8 * d) * D)) *
        (θ ^ N + ∑ l ∈ Finset.range N, θ ^ (N - l) * sourceResponseTau P l k hk) := by
  intro η θ B D Q F b G T Y A H
  have hraw := integrable_and_integral_sq_sourceOptimizer_flatnessMajorant_le_before
    hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (H a) ^ 2) P ∧ _ at hraw
  have hθ : (1 / 2 : ℝ) ≤ θ := (sourceGradientVarianceDecayFactor_bounds d).1
  have hD : 0 ≤ D := by dsimp [D, η]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hgeom := multiscale_majorant_bound_le_geometric_before θ (8 * d) (16 * (d : ℝ) ^ 2)
    B D A hθ (by positivity) (by positivity) hB hD hA N
    (fun l => sourceResponseTau P l k hk) (fun l => sourceResponseTau_nonneg hK P l k hk)
  change 2 * A + 2 * ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j)) *
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * T j) ≤ _ at hgeom
  refine ⟨hraw.1, hraw.2.1, ?_⟩
  exact hraw.2.2.trans hgeom

end EinsteinFull.Homogenization
