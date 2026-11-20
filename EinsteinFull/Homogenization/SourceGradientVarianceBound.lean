import EinsteinFull.Homogenization.SourceGradientVarianceTau
import EinsteinFull.Homogenization.SourceGradientUniformVariance

/-!
# Uniform optimizer gradient variance bound

The initial-scale estimate and the response-defect iteration give a uniform
coordinate bound in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The optimizer-gradient coordinate variance has a uniform geometric term and
an error given by the weighted response additivity defects. -/
theorem variance_sourceGradient_le_uniform_geometric_tau
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) (i : Fin d) (m : ℕ) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let A : ℕ → ℝ := fun n => ProbabilityTheory.variance (fun a =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory
            (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk))
          p q).toSolution i) P
    A m ≤ θ ^ m * (2 * (1 + (2 * d : ℝ) ^ 2)) + ∑ n ∈ Finset.range m,
      θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk) := by
  classical
  intro η θ A
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) :
      (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hηle : η ≤ 1 := by dsimp [η]; nlinarith
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have h0 : A 0 ≤ 2 * (1 + (2 * d : ℝ) ^ 2) := by
    simpa [A] using
      variance_sourceResponseAverageGradient_le P (originCube d 1) k hk p q hp.le hq.le i
  have h := variance_sourceGradient_le_geometric_tau hK P hP hstat k hk p q hp hq i m
  change A m ≤ θ ^ m * A 0 + ∑ n ∈ Finset.range m,
    θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk) at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      simpa only [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_left h0 (pow_nonneg hθ m))
        (∑ n ∈ Finset.range m, θ ^ (m - 1 - n) *
          ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk))

end EinsteinFull.Homogenization
