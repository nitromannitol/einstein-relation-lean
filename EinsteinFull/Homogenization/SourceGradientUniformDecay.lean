import EinsteinFull.Homogenization.GeometricSummableConvolution
import EinsteinFull.Homogenization.SourceGradientVarianceTau
import EinsteinFull.Homogenization.SourceGradientUniformVariance

/-!
# Uniform decay of optimizer-gradient variance

The variance estimate in Lemma 2.13 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, tends to
zero uniformly over unit-ball loadings.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Under stationarity and finite-range dependence, the optimizer-gradient
coordinate variances have a common bound tending to zero over unit loadings. -/
theorem exists_tendsto_zero_uniform_sourceGradient_variance
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ (m : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 → ∀ i : Fin d,
        ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient
          (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ))) k hk)
          (Book.Ch02.canonicalMaximizer
            (Book.Ch02.responseExistenceTheory
              (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ)))
              (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ))) k hk))
            p q).toSolution i) P ≤ B m := by
  let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
  let θ : ℝ := 1 - η / 2
  let C : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
  let D : ℝ := (1 + 2 / η) * (4 * d)
  let f : ℕ → ℝ := fun n => D * sourceResponseTau P (n + 1) k hk
  let B : ℕ → ℝ := fun m => θ ^ m * C +
    ∑ n ∈ Finset.range m, θ ^ (m - 1 - n) * f n
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) : (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hηle : η ≤ 1 := by dsimp [η]; nlinarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hf0 (n : ℕ) : 0 ≤ f n :=
    mul_nonneg hD (sourceResponseTau_nonneg hK P (n + 1) k hk)
  have hf : Summable f := by
    exact ((summable_nat_add_iff 1).2 (summable_sourceResponseTau hK P hstat k hk)).mul_left D
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const C
  have hs := tendsto_sum_geometric_mul_of_summable θ hθ0 hθ1 f hf0 hf
  have hB : Tendsto B atTop (𝓝 0) := by
    have h := ht.add hs
    simpa only [zero_mul, zero_add] using h
  refine ⟨B, hB, ?_⟩
  intro m p q hp hq i
  have h := variance_sourceGradient_le_geometric_tau hK P hP hstat k hk p q hp hq i m
  have hbase := variance_sourceResponseAverageGradient_le P (originCube d 1) k hk p q hp.le hq.le i
  dsimp only at h
  dsimp only [B, f, D, θ, η, C]
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      gcongr
      exact hbase

end EinsteinFull.Homogenization
