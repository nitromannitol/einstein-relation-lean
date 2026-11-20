import EinsteinFull.Homogenization.SourceGradientVarianceIteration
import EinsteinFull.Homogenization.SourceResponseDecrement

/-!
# Optimizer gradient variance and the additivity defect

The response additivity defect controls optimizer-gradient variance as in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- For unit-ball loadings, optimizer-gradient coordinate variance is bounded
by the initial variance and geometrically weighted uniform response defects. -/
theorem variance_sourceGradient_le_geometric_tau
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
    A m ≤ θ ^ m * A 0 + ∑ n ∈ Finset.range m,
      θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk) := by
  classical
  intro η θ A
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) :
      (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hηle : η ≤ 1 := by dsimp [η]; nlinarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  let J : ℕ → ℝ := fun n => ∫ a, Book.Ch02.responseJ
    (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
    (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P
  have h := variance_sourceGradient_le_geometric_response_decrements hK P hP hstat k hk p q i m
  dsimp only at h
  change A m ≤ θ ^ m * A 0 + ∑ n ∈ Finset.range m,
    θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * (J n - J (n + 1))) at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      gcongr with n hn
      have hdec := sourceResponseDecrement_le_tau hK P (n + 1) k hk p q hp hq
      simpa only [J, Nat.add_assoc] using hdec

end EinsteinFull.Homogenization
