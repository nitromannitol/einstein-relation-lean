import EinsteinFull.Homogenization.SourceGradientVectorVariance

/-!
# Response gradient variance at all scales

The gradient-variance estimate of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.13,
holds at every nonnegative triadic scale.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The geometric factor in the gradient-variance estimate lies in `[1/2, 1)`. -/
theorem sourceGradientVarianceDecayFactor_bounds (d : ℕ) :
    (1 / 2 : ℝ) ≤ 1 - ((((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2) / 2 ∧
      1 - ((((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2) / 2 < 1 := by
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) :
      (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hsq : (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2 ≤ 1 := by nlinarith
  have hsqpos : 0 < (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2 := by positivity
  constructor <;> linarith

/-- A shifted nonnegative geometric sum is bounded by the corresponding sum
starting at zero. -/
theorem shifted_geometric_sum_le (θ : ℝ) (τ : ℕ → ℝ)
    (hθ : 0 ≤ θ) (hτ : ∀ n, 0 ≤ τ n) (m : ℕ) :
    (∑ n ∈ Finset.range m, θ ^ (m - 1 - n) * τ (n + 1)) ≤
      ∑ n ∈ Finset.range (m + 1), θ ^ (m - n) * τ n := by
  rw [Finset.sum_range_succ']
  have hzero : 0 ≤ θ ^ m * τ 0 := mul_nonneg (pow_nonneg hθ _) (hτ 0)
  have heq : (∑ n ∈ Finset.range m, θ ^ (m - 1 - n) * τ (n + 1)) =
      ∑ n ∈ Finset.range m, θ ^ (m - (n + 1)) * τ (n + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    omega
  rw [heq]
  simpa only [Nat.sub_zero] using le_add_of_nonneg_right hzero


/-- The response-gradient vector variance has geometric decay with a weighted
sum of response additivity defects, at every triadic scale. -/
theorem integrable_and_sourceGradientVectorVariance_le_all_scales
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) (m : ℕ) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let B : ℝ := 2 * (1 + (2 * d : ℝ) ^ 2)
    let D : ℝ := (1 + 2 / η) * (4 * d)
    let F : Coefficient d K → Vec d := fun a =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory
            (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk))
          p q).toSolution
    (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - fun i => ∫ b, F b i ∂P)) P ∧
    (∫ a, vecNormSq (F a - fun i => ∫ b, F b i ∂P) ∂P) ≤
      (d : ℝ) * (θ ^ (m - 1) * B + D * ∑ n ∈ Finset.range m,
        θ ^ (m - 1 - n) * sourceResponseTau P n k hk) := by
  classical
  intro η θ B D F
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) :
      (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hηle : η ≤ 1 := by dsimp [η]; nlinarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  cases m with
  | zero =>
      have h := integrable_and_sourceGradientVectorVariance_le_uniform P (originCube d 0)
        k hk p q hp.le hq.le
      simpa [F, B] using h
  | succ m =>
      have h := integrable_and_sourceGradientVectorVariance_le hK P hP hstat k hk p q hp hq m
      change (∀ i, Integrable (fun a => F a i) P) ∧
        Integrable (fun a => vecNormSq (F a - fun i => ∫ b, F b i ∂P)) P ∧
        (∫ a, vecNormSq (F a - fun i => ∫ b, F b i ∂P) ∂P) ≤
          (d : ℝ) * (θ ^ m * B + ∑ n ∈ Finset.range m,
            θ ^ (m - 1 - n) * (D * sourceResponseTau P (n + 1) k hk)) at h
      refine ⟨h.1, h.2.1, ?_⟩
      have hs := shifted_geometric_sum_le θ (fun n => sourceResponseTau P n k hk) hθ
        (fun n => sourceResponseTau_nonneg hK P n k hk) m
      have hsum : (∑ n ∈ Finset.range m,
          θ ^ (m - 1 - n) * (D * sourceResponseTau P (n + 1) k hk)) =
          D * ∑ n ∈ Finset.range m, θ ^ (m - 1 - n) * sourceResponseTau P (n + 1) k hk := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      calc
        _ ≤ _ := h.2.2
        _ ≤ _ := by
          rw [hsum]
          have hd : (0 : ℝ) ≤ d := by positivity
          have hm := mul_le_mul_of_nonneg_left hs hD
          simp only [Nat.succ_sub_one]
          apply mul_le_mul_of_nonneg_left _ hd
          simpa only [add_comm] using add_le_add_left hm (θ ^ m * B)

end EinsteinFull.Homogenization
