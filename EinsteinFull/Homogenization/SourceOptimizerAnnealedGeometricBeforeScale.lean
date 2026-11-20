import EinsteinFull.Homogenization.SourceOptimizerAnnealedSlope
import EinsteinFull.Homogenization.SourceOptimizerFlatnessGeometricBeforeScale

/-!
# Geometric flatness majorant at the annealed slope

The multiscale majorant for the optimizer remainder can be expressed using
the preceding-scale annealed dual matrix, as in Lemma 2.15 of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*. The bound uses response defects at scales below the parent cube.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- At the preceding-scale annealed slope, a nonnegative normalized majorant
has an explicit geometric second-moment bound in the response defects. -/
theorem exists_sourceOptimizer_annealedSlope_geometric_majorant_before (d : ℕ) [NeZero d] :
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
      let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
            (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
      let b₁ := fun i => ∫ a, F a i ∂P
      let b := matVecMul (annealedDualMatrix P n k hk) q - p
      let G := fun j a => descendantsAverage Q j (fun R =>
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun - b₁))
      let H₀ := fun a => Real.sqrt A +
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (N - j) * Real.sqrt (G j a)
      let H := fun a => ((3 : ℝ) ^ N)⁻¹ * H₀ a + D * Real.sqrt (sourceResponseTau P n k hk)
      (∀ i, Integrable (fun a => F a i) P) ∧ MemLp H 2 P ∧ (∀ a, 0 ≤ H a) ∧
      (∀ a, let U := Book.Ch02.cubeDomain Q
        let A' := sourceCoeffOn a U k hk
        let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A') p q).toSolution
        cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b x) ≤ C * (3 : ℝ) ^ N * H a) ∧
      Integrable (fun a => (H a) ^ 2) P ∧
      (∫ a, (H a) ^ 2 ∂P) ≤
        2 * M * (θ ^ N + ∑ l ∈ Finset.range N,
          θ ^ (N - l) * sourceResponseTau P l k hk) +
        2 * D ^ 2 * sourceResponseTau P n k hk := by
  obtain ⟨C, hC, hmajor⟩ := exists_sourceOptimizer_flatness_majorant d
  refine ⟨C + 1, by linarith, ?_⟩
  intro K hK P _ hP hstat n k hk p q hp hq N η θ B₀ D₀ A M D Q F b₁ b G H₀ H
  have hm := hmajor hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ MemLp H₀ 2 P ∧ _ at hm
  have hg := integrable_and_integral_sq_sourceOptimizer_flatnessMajorant_le_geometric_before
    hK P hP hstat N k hk p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) ∧ Integrable (fun a => (H₀ a) ^ 2) P ∧
    (∫ a, (H₀ a) ^ 2 ∂P) ≤ (3 : ℝ) ^ (2 * N) * M *
      (θ ^ N + ∑ l ∈ Finset.range N, θ ^ (N - l) * sourceResponseTau P l k hk) at hg
  let t := sourceResponseTau P n k hk
  let δ := D * Real.sqrt t
  let H₁ := fun a => ((3 : ℝ) ^ N)⁻¹ * H₀ a
  let S : ℝ := θ ^ N + ∑ l ∈ Finset.range N, θ ^ (N - l) * sourceResponseTau P l k hk
  have ht : 0 ≤ t := sourceResponseTau_nonneg hK P n k hk
  have hδ : 0 ≤ δ := by dsimp [δ, D]; positivity
  have hH₀ (a) : 0 ≤ H₀ a := by
    apply add_nonneg (Real.sqrt_nonneg _)
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hpow : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hH₁ (a) : 0 ≤ H₁ a := mul_nonneg (inv_nonneg.mpr hpow.le) (hH₀ a)
  have hmem₁ : MemLp H₁ 2 P := hm.2.1.const_mul _
  have hmem : MemLp H 2 P := hmem₁.add (memLp_const δ)
  have hsecond : (∫ a, (H₁ a) ^ 2 ∂P) ≤ M * S := by
    have hid : (∫ a, (H₁ a) ^ 2 ∂P) = (((3 : ℝ) ^ N)⁻¹) ^ 2 * ∫ a, (H₀ a) ^ 2 ∂P := by
      simp only [H₁, mul_pow, integral_const_mul]
    rw [hid]
    calc
      _ ≤ (((3 : ℝ) ^ N)⁻¹) ^ 2 * ((3 : ℝ) ^ (2 * N) * M * S) :=
        mul_le_mul_of_nonneg_left hg.2.2 (sq_nonneg _)
      _ = M * S := by rw [mul_comm 2 N, pow_mul]; field_simp
  have hmean := integrable_and_vecNormSq_integral_sourceGradient_sub_le_sum_tau
    hK P hstat n N k (by dsimp [N]; omega) hk p q hp hq
  have hb := (integral_sourceGradient_eq_annealedDualMatrix P n k hk p q).2
  have hvec : vecNormSq (b₁ - b) ≤ (4 * (d : ℝ) ^ 2) * t := by
    have hh := hmean.2
    dsimp only [N] at hh
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton] at hh
    dsimp only [b]
    rw [← hb]
    exact hh
  have hsqrt : Real.sqrt (vecNormSq (b₁ - b)) ≤ 2 * (d : ℝ) * Real.sqrt t := by
    have hd : 0 ≤ (d : ℝ) := by positivity
    calc
      _ ≤ Real.sqrt ((4 * (d : ℝ) ^ 2) * t) := Real.sqrt_le_sqrt hvec
      _ = _ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * (d : ℝ) ^ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hd]
        norm_num
  refine ⟨hm.1, hmem, (fun a => add_nonneg (hH₁ a) hδ), ?_, hmem.integrable_sq, ?_⟩
  · intro a U A' v
    have hv := hm.2.2 a
    change cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b₁ x) ≤ C * H₀ a at hv
    have hc := cubeLpNorm_sub_vecDot_le_changeSlope N v.toH1 b b₁
    change cubeLpNorm Q 2 (fun x => v.toH1 x - vecDot b x) ≤ _ at hc
    have hc' : (d : ℝ) * (3 : ℝ) ^ N * Real.sqrt (vecNormSq (b₁ - b)) ≤
        (3 : ℝ) ^ N * δ := by
      dsimp [δ, D]
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by positivity : (0 : ℝ) ≤ d) hpow.le)]
    calc
      _ ≤ _ := hc
      _ ≤ C * H₀ a + (3 : ℝ) ^ N * δ := add_le_add hv hc'
      _ = C * (3 : ℝ) ^ N * H₁ a + (3 : ℝ) ^ N * δ := by dsimp [H₁]; field_simp
      _ ≤ (C + 1) * (3 : ℝ) ^ N * H a := by
        change _ ≤ (C + 1) * (3 : ℝ) ^ N * (H₁ a + δ)
        nlinarith [mul_nonneg hC hδ, mul_nonneg hpow.le (hH₁ a), mul_nonneg hpow.le hδ]
  · have hpoint (a) : (H a) ^ 2 ≤ 2 * (H₁ a) ^ 2 + 2 * δ ^ 2 := by
      change (H₁ a + δ) ^ 2 ≤ _
      nlinarith [sq_nonneg (H₁ a - δ)]
    have hright : Integrable (fun a => 2 * (H₁ a) ^ 2 + 2 * δ ^ 2) P :=
      (hmem₁.integrable_sq.const_mul 2).add (integrable_const _)
    calc
      _ ≤ ∫ a, 2 * (H₁ a) ^ 2 + 2 * δ ^ 2 ∂P := integral_mono hmem.integrable_sq hright hpoint
      _ = 2 * (∫ a, (H₁ a) ^ 2 ∂P) + 2 * δ ^ 2 := by
        rw [integral_add (hmem₁.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
        change _ ≤ 2 * M * S + 2 * D ^ 2 * t
        dsimp [δ]
        rw [mul_pow, Real.sq_sqrt ht]
        nlinarith

end EinsteinFull.Homogenization
