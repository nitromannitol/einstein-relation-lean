import EinsteinFull.Homogenization.SourceGradientVarianceBound

/-!
# Vector variance of optimizer gradients

The vector convention for variance in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.13,
is the expected squared Euclidean distance from the mean.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- At scales at least one, the response optimizer gradient has a uniform
vector-variance bound in terms of geometrically weighted additivity defects. -/
theorem integrable_and_sourceGradientVectorVariance_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d)
    (hp : vecNormSq p < 1) (hq : vecNormSq q < 1) (m : ℕ) :
    let η : ℝ := (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2
    let θ : ℝ := 1 - η / 2
    let F : Coefficient d K → Vec d := fun a =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory
            (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((m + 1 : ℕ) : ℤ))) k hk))
          p q).toSolution
    (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - fun i => ∫ b, F b i ∂P)) P ∧
    (∫ a, vecNormSq (F a - fun i => ∫ b, F b i ∂P) ∂P) ≤
      (d : ℝ) * (θ ^ m * (2 * (1 + (2 * d : ℝ) ^ 2)) + ∑ n ∈ Finset.range m,
        θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk)) := by
  classical
  intro η θ F
  have hF (i : Fin d) : MemLp (fun a => F a i) 2 P :=
    memLp_sourceResponseAverageGradient_cube P (originCube d ((m + 1 : ℕ) : ℤ)) k hk p q i 2
  have hint (i : Fin d) : Integrable (fun a => F a i) P := (hF i).integrable (by norm_num)
  let G : Fin d → Coefficient d K → ℝ := fun i a => (F a i - ∫ b, F b i ∂P) ^ 2
  have hG (i : Fin d) : Integrable (G i) P :=
    ((hF i).sub (memLp_const _)).integrable_sq
  have hsum : Integrable (fun a => vecNormSq (F a - fun i => ∫ b, F b i ∂P)) P := by
    have h := integrable_finsetSum Finset.univ (fun i _ => hG i)
    simpa [vecNormSq, vecDot, G, pow_two] using h
  refine ⟨hint, hsum, ?_⟩
  have heq : (∫ a, vecNormSq (F a - fun i => ∫ b, F b i ∂P) ∂P) =
      ∑ i : Fin d, ProbabilityTheory.variance (fun a => F a i) P := by
    calc
      _ = ∑ i : Fin d, ∫ a, G i a ∂P := by
        simpa [vecNormSq, vecDot, G, pow_two] using
          (integral_finsetSum Finset.univ (fun i _ => hG i))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ProbabilityTheory.variance_eq_integral (hF i).aemeasurable).symm
  rw [heq]
  have hcoord (i : Fin d) : ProbabilityTheory.variance (fun a => F a i) P ≤
      θ ^ m * (2 * (1 + (2 * d : ℝ) ^ 2)) + ∑ n ∈ Finset.range m,
        θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk) := by
    exact variance_sourceGradient_le_uniform_geometric_tau hK P hP hstat k hk p q hp hq i m
  calc
    _ ≤ ∑ _i : Fin d, (θ ^ m * (2 * (1 + (2 * d : ℝ) ^ 2)) + ∑ n ∈ Finset.range m,
        θ ^ (m - 1 - n) * ((1 + 2 / η) * (4 * d) * sourceResponseTau P (n + 1) k hk)) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := by simp; ring

end EinsteinFull.Homogenization
