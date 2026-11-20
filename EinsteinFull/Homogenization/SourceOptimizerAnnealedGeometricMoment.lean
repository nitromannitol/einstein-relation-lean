import EinsteinFull.Homogenization.SourceOptimizerAnnealedGeometricBeforeScale
import EinsteinFull.Homogenization.SquareIntegrableMajorant

/-!
# Geometric optimizer flatness moments

The optimizer flatness majorant yields a geometric second-moment bound at the
annealed slope, provided the normalized optimizer norm is almost everywhere
measurable. This is related to Lemma 2.15 of Armstrong, Kuusi and Mourrat,
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
theorem exists_sourceOptimizer_annealedSlope_geometric_moment_of_aemeasurable
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
          (2 * M * (θ ^ N + ∑ l ∈ Finset.range N,
            θ ^ (N - l) * sourceResponseTau P l k hk) + 2 * D ^ 2 * sourceResponseTau P n k hk) := by
  obtain ⟨C, hC, hmajor⟩ := exists_sourceOptimizer_annealedSlope_geometric_majorant_before d
  refine ⟨C, hC, ?_⟩
  intro K hK P _ hP hstat n k hk p q hp hq N η θ B₀ D₀ A M D Q b f hmeas
  have h := hmajor hK P hP hstat n k hk p q hp hq
  dsimp only at h
  obtain ⟨hF, hmem, hH, hbound, hint, hsecond⟩ := h
  let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
    (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
  let b₁ := fun i => ∫ a, F a i ∂P
  let G := fun (j : ℕ) (a : Coefficient d K) => descendantsAverage Q j (fun R =>
    vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun - b₁))
  let H₀ := fun a => Real.sqrt A +
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
  let H := fun a => ((3 : ℝ) ^ N)⁻¹ * H₀ a + D * Real.sqrt (sourceResponseTau P n k hk)
  change MemLp H 2 P at hmem
  change ∀ a, 0 ≤ H a at hH
  change (∫ a, (H a) ^ 2 ∂P) ≤ _ at hsecond
  have hpow : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hf (a : Coefficient d K) : 0 ≤ f a := by
    dsimp only [f]
    exact mul_nonneg (inv_nonneg.mpr hpow.le) (cubeLpNorm_nonneg _ _ _)
  have hbound' (a : Coefficient d K) : f a ≤ C * H a := by
    have hb := hbound a
    change _ ≤ C * (3 : ℝ) ^ N * H a at hb
    calc
      f a ≤ ((3 : ℝ) ^ N)⁻¹ * (C * (3 : ℝ) ^ N * H a) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpow.le)
      _ = C * H a := by field_simp
  exact memLp_and_integral_sq_le_of_majorant P f H C _ hC hf hH hbound' hmeas hmem hsecond

end EinsteinFull.Homogenization
