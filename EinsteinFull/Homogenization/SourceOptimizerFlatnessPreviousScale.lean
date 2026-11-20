import EinsteinFull.Homogenization.SourceOptimizerFlatnessDecay
import EinsteinFull.Homogenization.OriginCubeSlopeChange

/-!
# Flatness with the preceding-scale slope

The rescaled optimizer remainder admits vanishing square-integrable majorants
when its affine slope is the mean gradient at the preceding scale, as in the
flatness argument in Lemma 2.15 of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*.
-/

open scoped ENNReal
open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The affine remainder using the preceding-scale mean gradient has
square-integrable majorants vanishing uniformly over unit loadings. -/
theorem exists_tendsto_zero_sourceOptimizer_previousSlope_majorant
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ (n : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 →
      let Q := originCube d ((n + 1 : ℕ) : ℤ)
      let R := originCube d (n : ℤ)
      let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
            (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution
      let b := fun i => ∫ a, F a i ∂P
      (∀ i, Integrable (fun a => F a i) P) ∧
      ∃ H : Coefficient d K → ℝ, MemLp H 2 P ∧ (∀ a, 0 ≤ H a) ∧
        (∀ a, let U := Book.Ch02.cubeDomain Q
          let A := sourceCoeffOn a U k hk
          let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x) ≤
            C * (3 : ℝ) ^ (n + 1) * H a) ∧
        Integrable (fun a => (H a) ^ 2) P ∧ (∫ a, (H a) ^ 2 ∂P) ≤ B n := by
  obtain ⟨C, hC, B, hB, hmajor⟩ :=
    exists_tendsto_zero_sourceOptimizer_flatness_majorant hK P hP hstat k hk
  let D : ℝ := 2 * (d : ℝ) ^ 2
  let T : ℕ → ℝ := fun n => 2 * B (n + 1) + 2 * D ^ 2 * sourceResponseTau P n k hk
  have hB' := hB.comp (tendsto_add_atTop_nat 1)
  have htau := tendsto_sourceResponseTau_zero hK P hstat k hk
  have hT : Tendsto T atTop (𝓝 0) := by
    have h := (hB'.const_mul 2).add (htau.const_mul (2 * D ^ 2))
    simpa only [T, Function.comp_apply, mul_zero, zero_add] using h
  refine ⟨C + 1, by linarith, T, hT, ?_⟩
  intro n p q hp hq Q R F b
  obtain ⟨hF₁, H, hmem, hH, hbound, hint, hsecond⟩ := hmajor (n + 1) p q hp hq
  let F₁ := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
    (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
    (Book.Ch02.canonicalMaximizer
      (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
  let b₁ := fun i => ∫ a, F₁ a i ∂P
  let t := sourceResponseTau P n k hk
  let δ := D * Real.sqrt t
  let H' := fun a => H a + δ
  have ht : 0 ≤ t := sourceResponseTau_nonneg hK P n k hk
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hδ : 0 ≤ δ := mul_nonneg hD (Real.sqrt_nonneg _)
  have hmean := integrable_and_vecNormSq_integral_sourceGradient_sub_le_sum_tau
    hK P hstat n (n + 1) k (Nat.le_succ n) hk p q hp hq
  have hF : ∀ i, Integrable (fun a => F a i) P := by
    intro i
    exact hmean.1 n i
  have hvec : vecNormSq (b₁ - b) ≤ (4 * (d : ℝ) ^ 2) * t := by
    have h := hmean.2
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton] at h
    exact h
  have hsqrt : Real.sqrt (vecNormSq (b₁ - b)) ≤ 2 * (d : ℝ) * Real.sqrt t := by
    have hd : 0 ≤ (d : ℝ) := by positivity
    calc
      _ ≤ Real.sqrt ((4 * (d : ℝ) ^ 2) * t) := Real.sqrt_le_sqrt hvec
      _ = _ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * (d : ℝ) ^ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hd]
        norm_num
  have hmem' : MemLp H' 2 P := hmem.add (memLp_const δ)
  refine ⟨hF, H', hmem', (fun a => add_nonneg (hH a) hδ), ?_, hmem'.integrable_sq, ?_⟩
  · intro a U A v
    have hv := hbound a
    change cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b₁ x) ≤
      C * (3 : ℝ) ^ (n + 1) * H a at hv
    have hc := cubeLpNorm_sub_vecDot_le_changeSlope (n + 1) v.toH1 b b₁
    change cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b x) ≤ _ at hc
    have hp3 : 0 ≤ (3 : ℝ) ^ (n + 1) := by positivity
    have hc' : (d : ℝ) * (3 : ℝ) ^ (n + 1) * Real.sqrt (vecNormSq (b₁ - b)) ≤
        (3 : ℝ) ^ (n + 1) * δ := by
      dsimp [δ, D]
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by positivity : (0 : ℝ) ≤ d) hp3)]
    calc
      _ ≤ _ := hc
      _ ≤ C * (3 : ℝ) ^ (n + 1) * H a + (3 : ℝ) ^ (n + 1) * δ := add_le_add hv hc'
      _ ≤ (C + 1) * (3 : ℝ) ^ (n + 1) * H' a := by
        dsimp [H']; nlinarith [mul_nonneg hC hδ, mul_nonneg hp3 (hH a), mul_nonneg hp3 hδ]
  · have hpoint (a : Coefficient d K) : (H' a) ^ 2 ≤ 2 * (H a) ^ 2 + 2 * δ ^ 2 := by
      dsimp [H']; nlinarith [sq_nonneg (H a - δ)]
    have hright : Integrable (fun a => 2 * (H a) ^ 2 + 2 * δ ^ 2) P :=
      (hint.const_mul 2).add (integrable_const _)
    calc
      _ ≤ ∫ a, 2 * (H a) ^ 2 + 2 * δ ^ 2 ∂P := integral_mono hmem'.integrable_sq hright hpoint
      _ = 2 * (∫ a, (H a) ^ 2 ∂P) + 2 * δ ^ 2 := by
        rw [integral_add (hint.const_mul 2) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ T n := by
        dsimp [T, δ, t]
        rw [mul_pow, Real.sq_sqrt ht]
        nlinarith

end EinsteinFull.Homogenization
