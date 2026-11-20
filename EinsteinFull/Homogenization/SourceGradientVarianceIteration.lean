import EinsteinFull.Homogenization.SourceGradientVarianceStep
import EinsteinFull.Homogenization.GeometricRecurrence

/-!
# Iterated optimizer gradient variance estimate

Iteration of the response-decrement estimate follows Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- At scales starting from one, the optimizer-gradient variance is bounded by
its initial value and a geometrically weighted sum of response decrements. -/
theorem variance_sourceGradient_le_geometric_response_decrements
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) (m : ℕ) :
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
    let J : ℕ → ℝ := fun n => ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P
    A m ≤ θ ^ m * A 0 + ∑ n ∈ Finset.range m,
      θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * (J n - J (n + 1))) := by
  classical
  intro η θ A J
  have hN : (1 : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) :
      (1 : ℝ) ≤ (3 : ℝ) ^ d)
  have hinv : 0 ≤ (((3 ^ d : ℕ) : ℝ)⁻¹) := by positivity
  have hinvle : (((3 ^ d : ℕ) : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hN
  have hηle : η ≤ 1 := by
    dsimp [η]
    nlinarith
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  let B : ℕ → ℝ := fun n => (1 + 2 / η) * (4 * d) * (J n - J (n + 1))
  have hrec (n : ℕ) : A (n + 1) ≤ θ * A n + B n := by
    have hs : (originCube d ((n + 2 : ℕ) : ℤ)).scale = (n : ℤ) + 2 := by
      simp [originCube]
    have h := variance_sourceGradient_le_contraction_add_response_decrement
      hK P hP hstat (originCube d ((n + 2 : ℕ) : ℤ)) n k hs hk p q i
    dsimp only at h
    simp only [sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] at h
    simpa only [A, B, J, θ, η, Nat.add_assoc, mul_assoc] using h
  exact le_geometric_weighted_sum A B θ hθ hrec m

end EinsteinFull.Homogenization
