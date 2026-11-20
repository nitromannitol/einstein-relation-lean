import EinsteinFull.Homogenization.SourceOptimizerFlatnessGeometric
import EinsteinFull.Homogenization.GeometricSummableConvolution

/-!
# A vanishing majorant for optimizer flatness

The multiscale estimate yields square-integrable majorants of the
rescaled optimizer remainders that vanish uniformly over unit loadings. This
is related to Lemma 2.15 of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*.
-/

open scoped ENNReal
open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The rescaled affine remainder admits square-integrable
majorants whose second moments vanish uniformly over unit loadings. -/
theorem exists_tendsto_zero_sourceOptimizer_flatness_majorant
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ (N : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 →
      let Q := originCube d (N : ℤ)
      let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
            (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
      let b := fun i => ∫ a, F a i ∂P
      (∀ i, Integrable (fun a => F a i) P) ∧
      ∃ H : Coefficient d K → ℝ, MemLp H 2 P ∧ (∀ a, 0 ≤ H a) ∧
        (∀ a, let U := Book.Ch02.cubeDomain Q
          let A := sourceCoeffOn a U k hk
          let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤
            C * (3 : ℝ) ^ N * H a) ∧
        Integrable (fun a => (H a) ^ 2) P ∧ (∫ a, (H a) ^ 2 ∂P) ≤ B N := by
  obtain ⟨C, hC, hmajor⟩ := exists_sourceOptimizer_flatness_majorant d
  let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
  let θ : ℝ := 1 - η / 2
  let B₀ : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
  let D : ℝ := (1 + 2 / η) * (4 * d)
  let A : ℝ := (2 + 4 * (d : ℝ) ^ 2) * (K + 4)
  let M : ℝ := 2 * A + 9 * ((8 * d) * B₀ + (8 * d) + (16 * (d : ℝ) ^ 2) + (8 * d) * D)
  let B : ℕ → ℝ := fun N => M * (θ ^ N +
    ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * sourceResponseTau P l k hk)
  have hθ0 : 0 ≤ θ := by have h := (sourceGradientVarianceDecayFactor_bounds d).1; dsimp [θ, η]; linarith
  have hθ1 : θ < 1 := (sourceGradientVarianceDecayFactor_bounds d).2
  have hpw := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
  have hconv := tendsto_sum_geometric_mul_of_summable θ hθ0 hθ1
    (fun n => sourceResponseTau P n k hk) (fun n => sourceResponseTau_nonneg hK P n k hk)
    (summable_sourceResponseTau hK P hstat k hk)
  have hconv' := hconv.comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto B atTop (𝓝 0) := by
    have h := (hpw.add hconv').const_mul M
    simpa only [B, Function.comp_apply, Nat.add_sub_cancel, zero_add, mul_zero] using h
  refine ⟨C, hC, B, hB, ?_⟩
  intro N p q hp hq Q F b
  let G := fun (j : ℕ) (a : Coefficient d K) => descendantsAverage Q j (fun R =>
    vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun - b))
  let H₀ := fun a => Real.sqrt A +
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
  let H := fun a => ((3 : ℝ) ^ N)⁻¹ * H₀ a
  have hm := hmajor hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ MemLp H₀ 2 P ∧ _ at hm
  have hg := integrable_and_integral_sq_sourceOptimizer_flatnessMajorant_le_geometric
    hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (H₀ a) ^ 2) P ∧
    (∫ a, (H₀ a) ^ 2 ∂P) ≤ (3 : ℝ) ^ (2 * N) * M *
      (θ ^ N + ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * sourceResponseTau P l k hk) at hg
  have hH₀ (a) : 0 ≤ H₀ a := by
    apply add_nonneg (Real.sqrt_nonneg _)
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hpow : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hH : MemLp H 2 P := hm.2.1.const_mul _
  refine ⟨hm.1, H, hH, (fun a => mul_nonneg (inv_nonneg.mpr hpow.le) (hH₀ a)), ?_, hH.integrable_sq, ?_⟩
  · intro a U A' v
    have hv := hm.2.2 a
    change cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤ C * H₀ a at hv
    calc
      _ ≤ C * H₀ a := hv
      _ = C * (3 : ℝ) ^ N * H a := by dsimp [H]; field_simp
  · have hid : (∫ a, (H a) ^ 2 ∂P) = (((3 : ℝ) ^ N)⁻¹) ^ 2 * ∫ a, (H₀ a) ^ 2 ∂P := by
      simp only [H, mul_pow, integral_const_mul]
    rw [hid]
    calc
      _ ≤ (((3 : ℝ) ^ N)⁻¹) ^ 2 * ((3 : ℝ) ^ (2 * N) * M *
        (θ ^ N + ∑ l ∈ Finset.range (N + 1), θ ^ (N - l) * sourceResponseTau P l k hk)) :=
          mul_le_mul_of_nonneg_left hg.2.2 (sq_nonneg _)
      _ = B N := by dsimp [B]; rw [mul_comm 2 N, pow_mul]; field_simp

end EinsteinFull.Homogenization
