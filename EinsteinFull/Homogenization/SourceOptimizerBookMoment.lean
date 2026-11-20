import EinsteinFull.Homogenization.SourceOptimizerAnnealedGeometricMoment
import EinsteinFull.Homogenization.SquareIntegrableMajorant
import EinsteinFull.Homogenization.GeometricLastDefect

/-!
# Geometric optimizer flatness moments

The optimizer flatness majorant yields a geometric second-moment bound at the
annealed slope, provided the normalized optimizer norm is almost everywhere
measurable. This has the geometric form of Lemma 2.15 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Almost everywhere measurability of the normalized remainder permits the
geometric majorant estimate to be transferred to its second moment. -/
theorem exists_sourceOptimizer_annealedSlope_book_moment_of_aemeasurable
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ} (_hK : 0 ≤ K)
      (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (_hP : AKMFiniteRange P)
      (_hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
      (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
      (_hp : vecNormSq p < 1) (_hq : vecNormSq q < 1),
      let N := n + 1
      let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
      let θ : ℝ := 1 - η / 2
      let B₀ : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
      let D₀ : ℝ := (1 + 2 / η) * (4 * d)
      let A : ℝ := (2 + 4 * (d : ℝ) ^ 2) * (K + 4)
      let M : ℝ := 2 * A + 9 * ((8 * d) * B₀ + (8 * d) + (16 * (d : ℝ) ^ 2) + (8 * d) * D₀)
      let D : ℝ := 2 * (d : ℝ) ^ 2
      let Q := originCube d (N : ℤ)
      let b := matVecMul (annealedDualMatrix P n k hk) q - p
      let f := fun a : Coefficient d K => ((3 : ℝ) ^ N)⁻¹ *
        (let U := Book.Ch02.cubeDomain Q
         let A' := sourceCoeffOn a U k hk
         let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A') p q).toSolution
         cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b x))
      AEMeasurable f P → MemLp f 2 P ∧ Integrable (fun a => (f a) ^ 2) P ∧
        (∫ a, (f a) ^ 2 ∂P) ≤ C ^ 2 *
          ((2 * M + 2 * D ^ 2) * (θ ^ n + ∑ l ∈ Finset.range (n + 1),
            θ ^ (n - l) * sourceResponseTau P l k hk)) := by
  obtain ⟨C, hC, hmajor⟩ := exists_sourceOptimizer_annealedSlope_geometric_moment_of_aemeasurable d
  refine ⟨C, hC, ?_⟩
  intro K hK P _ hP hstat n k hk p q hp hq N η θ B₀ D₀ A M D Q b f hmeas
  have h := hmajor hK P hP hstat n k hk p q hp hq
  dsimp only at h
  have h := h hmeas
  change MemLp f 2 P ∧ Integrable (fun a => (f a) ^ 2) P ∧
    (∫ a, (f a) ^ 2 ∂P) ≤ C ^ 2 *
      (2 * M * (θ ^ N + ∑ l ∈ Finset.range N, θ ^ (N - l) * sourceResponseTau P l k hk) +
        2 * D ^ 2 * sourceResponseTau P n k hk) at h
  have hθ : (1 / 2 : ℝ) ≤ θ := (sourceGradientVarianceDecayFactor_bounds d).1
  have hθ1 : θ ≤ 1 := (sourceGradientVarianceDecayFactor_bounds d).2.le
  have hM : 0 ≤ M := by dsimp [M, A, B₀, D₀, η]; positivity
  have hg := shifted_geometric_and_last_defect_le θ M D (by linarith) hθ1 hM n
    (fun l => sourceResponseTau P l k hk) (fun l => sourceResponseTau_nonneg hK P l k hk)
  refine ⟨h.1, h.2.1, ?_⟩
  exact h.2.2.trans (mul_le_mul_of_nonneg_left hg (sq_nonneg C))

end EinsteinFull.Homogenization
