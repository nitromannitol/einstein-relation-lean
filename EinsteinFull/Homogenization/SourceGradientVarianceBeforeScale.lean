import EinsteinFull.Homogenization.SourceGradientVarianceAllScales

/-!
# Optimizer-gradient variance using earlier defects

The finite-scale gradient-variance estimate uses response defects strictly
below the scale considered, as in Lemma 2.13 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Shifting a geometric exponent by one costs at most a factor of two. -/
theorem geometric_defect_sum_pred_le_before (θ : ℝ) (hθ : (1 / 2 : ℝ) ≤ θ)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 ≤ τ n) (m : ℕ) :
    (∑ n ∈ Finset.range m, θ ^ (m - 1 - n) * τ n) ≤
      2 * ∑ n ∈ Finset.range m, θ ^ (m - n) * τ n := by
  calc
    _ ≤ ∑ n ∈ Finset.range m, (2 * (θ ^ (m - n) * τ n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have heq : m - 1 - n = (m - n) - 1 := by omega
      rw [heq]
      have h := mul_le_mul_of_nonneg_right (geometric_power_pred_le θ hθ (m - n)) (hτ n)
      nlinarith
    _ = _ := by rw [Finset.mul_sum]

/-- The optimizer-gradient vector variance is bounded by a geometric sum of
response defects at strictly smaller scales. -/
theorem integrable_and_sourceGradientVectorVariance_le_geometric_before
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
      2 * (d : ℝ) * (θ ^ m * B + D * ∑ n ∈ Finset.range m,
        θ ^ (m - n) * sourceResponseTau P n k hk) := by
  intro η θ B D F
  have hθ : (1 / 2 : ℝ) ≤ θ := (sourceGradientVarianceDecayFactor_bounds d).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D, η]; positivity
  have hd : (0 : ℝ) ≤ d := by positivity
  have h := integrable_and_sourceGradientVectorVariance_le_all_scales hK P hP hstat k hk p q hp hq m
  change (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - fun i => ∫ b, F b i ∂P)) P ∧
    (∫ a, vecNormSq (F a - fun i => ∫ b, F b i ∂P) ∂P) ≤
      (d : ℝ) * (θ ^ (m - 1) * B + D * ∑ n ∈ Finset.range m,
        θ ^ (m - 1 - n) * sourceResponseTau P n k hk) at h
  refine ⟨h.1, h.2.1, ?_⟩
  have hpw := mul_le_mul_of_nonneg_right (geometric_power_pred_le θ hθ m) hB
  have hsum := mul_le_mul_of_nonneg_left
    (geometric_defect_sum_pred_le_before θ hθ (fun n => sourceResponseTau P n k hk)
      (fun n => sourceResponseTau_nonneg hK P n k hk) m) hD
  calc
    _ ≤ _ := h.2.2
    _ ≤ _ := by
      have ha := mul_le_mul_of_nonneg_left (add_le_add hpw hsum) hd
      nlinarith

end EinsteinFull.Homogenization
