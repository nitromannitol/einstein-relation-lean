import EinsteinFull.Homogenization.WholeSpaceOrthogonality

/-!
# Weighted cube averages for the div-curl argument

Cauchy–Schwarz inequalities for cube averages weighted by the square of a smooth cutoff, the
lower bound on the average of the squared inner cube cutoff, and the elementary real-number
argument that turns approximate identities for the weighted energy into bounds on the
homogenized quadratic form. These are the deterministic parts of the classical div-curl
argument identifying the homogenized energy, as in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Section 1.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- Cauchy–Schwarz for cube averages. -/
theorem sq_cubeAverage_mul_le (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x * g x) ^ 2 ≤
      cubeAverage Q (fun x => f x ^ 2) * cubeAverage Q (fun x => g x ^ 2) := by
  have h := abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate Q 2 2 f g hf hg
  have hf2 := (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq Q f hf).2
  have hg2 := (integrable_and_cubeLpNorm_sq_eq_cubeAverage_sq Q g hg).2
  have h0 : 0 ≤ cubeLpNorm Q 2 f * cubeLpNorm Q 2 g :=
    mul_nonneg (cubeLpNorm_nonneg _ _ _) (cubeLpNorm_nonneg _ _ _)
  calc cubeAverage Q (fun x => f x * g x) ^ 2 = |cubeAverage Q (fun x => f x * g x)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (cubeLpNorm Q 2 f * cubeLpNorm Q 2 g) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = cubeAverage Q (fun x => f x ^ 2) * cubeAverage Q (fun x => g x ^ 2) := by
        rw [mul_pow, hf2, hg2]

theorem memLp_normalizedCubeMeasure_of_bound (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) {c : ℝ} (hc : ∀ x, |f x| ≤ c) :
    MemLp f 2 (normalizedCubeMeasure Q) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact MemLp.of_bound hf c (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hc x)

/-- The average of the squared inner cube cutoff is at least the volume fraction of the inner
cube. -/
theorem pow_le_cubeAverage_sq_innerCubeCutoff (R : TriadicCube d) {τ : ℝ} (hτ : 0 < τ)
    (hτ' : τ ≤ 1 / 4) :
    (1 - 2 * τ) ^ d ≤ cubeAverage R (fun x => innerCubeCutoff R τ x ^ 2) := by
  set S := scaledClosedCubeSet R (1 - 2 * τ)
  have hS : MeasurableSet S := measurableSet_scaledClosedCubeSet R _
  have hSR : S ⊆ cubeSet R :=
    (scaledClosedCubeSet_subset_openCubeSet R (by linarith)).trans (openCubeSet_subset_cubeSet R)
  have hRfin : volume (cubeSet R) < ⊤ := volume_cubeSet_lt_top R
  have hηc : Continuous (innerCubeCutoff R τ) := (innerCubeCutoff_smooth R hτ hτ').continuous
  have hpt (x : Vec d) : S.indicator (fun _ => (1 : ℝ)) x ≤ innerCubeCutoff R τ x ^ 2 := by
    by_cases hx : x ∈ S
    · have h1 : innerCubeCutoff R τ x = 1 :=
        QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner (by linarith) (by linarith) hx
      rw [Set.indicator_of_mem hx, h1]
      norm_num
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg _
  have hind : IntegrableOn (S.indicator fun _ => (1 : ℝ)) (cubeSet R) volume :=
    ((MeasureTheory.integrable_indicator_iff hS).mpr
      (integrableOn_const (C := (1 : ℝ)) ((measure_mono hSR).trans_lt hRfin).ne)).integrableOn
  have hsq : IntegrableOn (fun x => innerCubeCutoff R τ x ^ 2) (cubeSet R) volume :=
    IntegrableOn.of_bound hRfin (hηc.pow 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        have h0 := innerCubeCutoff_nonneg R τ x
        have h1 := innerCubeCutoff_le_one R τ x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith)
  have hle := setIntegral_mono_on hind hsq (measurableSet_cubeSet R) fun x _ => hpt x
  have hval : ∫ x in cubeSet R, S.indicator (fun _ => (1 : ℝ)) x =
      (1 - 2 * τ) ^ d * cubeVolume R := by
    rw [setIntegral_indicator hS, setIntegral_const, Set.inter_eq_right.mpr hSR]
    simp only [smul_eq_mul, mul_one, Measure.real]
    rw [volume_scaledClosedCubeSet_toReal R (by linarith)]
  have hvol : 0 < cubeVolume R := cubeVolume_pos R
  unfold cubeAverage
  rw [le_inv_mul_iff₀ hvol]
  linarith

theorem le_of_forall_le_add_mul {x y C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → x ≤ y + C * ε) : x ≤ y := by
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  set ε := min 1 (ε' / (C + 1)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ ε' / (C + 1) := min_le_right _ _
  have h1 := h ε hε0 hε1
  have h2 : C * ε ≤ ε' := by
    calc C * ε ≤ (C + 1) * ε := by nlinarith
      _ ≤ (C + 1) * (ε' / (C + 1)) := mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ = ε' := by field_simp
  linarith

/-- The lower bound of the div-curl argument: approximate identities for the weighted energy
and the weighted mean gradient give `|p|² ≤ p · s̄ p`. -/
theorem sq_le_of_approx {q P c : ℝ} (hq : 0 ≤ q) (hP : 0 ≤ P) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ s a P' g : ℝ, c ≤ s ∧ s ≤ 1 ∧ 0 ≤ g ∧
      |P' - q * s| ≤ ε ∧ |a - P'| ≤ ε ∧ P * s - ε ≤ g ∧ g ^ 2 ≤ s * a) :
    P ^ 2 ≤ q := by
  refine le_of_forall_le_add_mul (C := (3 + 2 * P) / c ^ 2) (by positivity) fun ε hε hε1 => ?_
  obtain ⟨s, a, P', g, hcs, hs1, hg0, h1, h2, h3, h4⟩ := h ε hε
  have hs0 : 0 < s := lt_of_lt_of_le hc hcs
  have ha : a ≤ q * s + 2 * ε := by
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).2
    linarith
  have hc2 : c ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hc.le hcs 2
  have hkey : P ^ 2 * s ^ 2 ≤ q * s ^ 2 + (3 + 2 * P) * ε := by
    by_cases hneg : 0 ≤ P * s - ε
    · have hsq : (P * s - ε) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hneg h3 2
      have hsa : s * a ≤ q * s ^ 2 + 2 * ε := by
        have := mul_le_mul_of_nonneg_left ha hs0.le
        nlinarith
      have hPs1 : P * s ≤ P := mul_le_of_le_one_right hP hs1
      have hPs2 : P * s * ε ≤ P * ε := mul_le_mul_of_nonneg_right hPs1 hε.le
      have hexp : (P * s - ε) ^ 2 = P ^ 2 * s ^ 2 - 2 * (P * s * ε) + ε ^ 2 := by ring
      nlinarith [sq_nonneg ε]
    · push_neg at hneg
      have hPs : P * s < ε := by linarith
      have : (P * s) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) hPs.le 2
      have hqs : 0 ≤ q * s ^ 2 := by positivity
      nlinarith
  have hdiv : P ^ 2 ≤ q + (3 + 2 * P) * ε / s ^ 2 := by
    rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    nlinarith
  have hmono : (3 + 2 * P) * ε / s ^ 2 ≤ (3 + 2 * P) / c ^ 2 * ε := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hc2
  linarith

/-- The upper bound of the div-curl argument: approximate identities for the weighted energy
and for the weighted pairing of the flux with `p` give `p · s̄ p ≤ K² |p|²`. -/
theorem le_sq_mul_of_approx {q P K c : ℝ} (hq : 0 ≤ q) (hP : 0 ≤ P) (hK : 0 ≤ K) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ s a P' : ℝ, c ≤ s ∧ s ≤ 1 ∧ 0 ≤ a ∧
      |P' - q * s| ≤ ε ∧ |a - P'| ≤ ε ∧ P' ≤ K * P * Real.sqrt s * Real.sqrt a) :
    q ≤ K ^ 2 * P ^ 2 := by
  have hq2 : q ^ 2 ≤ K ^ 2 * P ^ 2 * q := by
    refine le_of_forall_le_add_mul (C := (3 * q + 2 * K ^ 2 * P ^ 2) / c) (by positivity)
      fun ε hε hε1 => ?_
    obtain ⟨s, a, P', hcs, hs1, ha0, h1, h2, h3⟩ := h ε hε
    have hs0 : 0 < s := lt_of_lt_of_le hc hcs
    have ha : a ≤ q * s + 2 * ε := by
      have := (abs_le.mp h1).2
      have := (abs_le.mp h2).2
      linarith
    have hP' : q * s - ε ≤ P' := by
      have := (abs_le.mp h1).1
      linarith
    have hkey : q ^ 2 * s ≤ K ^ 2 * P ^ 2 * q * s + (3 * q + 2 * K ^ 2 * P ^ 2) * ε := by
      by_cases hneg : 0 ≤ q * s - ε
      · have hsqa : Real.sqrt a ≤ Real.sqrt (q * s + 2 * ε) := Real.sqrt_le_sqrt ha
        have hKP : 0 ≤ K * P * Real.sqrt s := by positivity
        have hle : q * s - ε ≤ K * P * Real.sqrt s * Real.sqrt (q * s + 2 * ε) :=
          hP'.trans (h3.trans (mul_le_mul_of_nonneg_left hsqa hKP))
        have hsq := pow_le_pow_left₀ hneg hle 2
        have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
        have hsa : Real.sqrt (q * s + 2 * ε) ^ 2 = q * s + 2 * ε := Real.sq_sqrt (by positivity)
        have hexp : (K * P * Real.sqrt s * Real.sqrt (q * s + 2 * ε)) ^ 2 =
            K ^ 2 * P ^ 2 * s * (q * s + 2 * ε) := by
          rw [mul_pow, mul_pow, mul_pow, hss, hsa]
        rw [hexp] at hsq
        have hs2 : s ^ 2 ≤ s := by nlinarith
        have h4 : q ^ 2 * s ^ 2 ≤ K ^ 2 * P ^ 2 * q * s ^ 2 +
            (2 * q * s + 2 * K ^ 2 * P ^ 2 * s) * ε := by nlinarith
        have h5 : q ^ 2 * s ≤ K ^ 2 * P ^ 2 * q * s + (2 * q + 2 * K ^ 2 * P ^ 2) * ε := by
          have h6 : s * (q ^ 2 * s) ≤ s * (K ^ 2 * P ^ 2 * q * s +
              (2 * q + 2 * K ^ 2 * P ^ 2) * ε) := by nlinarith
          exact le_of_mul_le_mul_left h6 hs0
        nlinarith
      · push_neg at hneg
        have hqs : q * s < ε := by linarith
        have h7 : q * (q * s) ≤ q * ε := mul_le_mul_of_nonneg_left hqs.le hq
        have h8 : 0 ≤ K ^ 2 * P ^ 2 * q * s := by positivity
        have h9 : q ^ 2 * s = q * (q * s) := by ring
        have h10 : 0 ≤ q * ε := mul_nonneg hq hε.le
        have h11 : 0 ≤ K ^ 2 * P ^ 2 * ε := by positivity
        nlinarith
    have hdiv : q ^ 2 ≤ K ^ 2 * P ^ 2 * q + (3 * q + 2 * K ^ 2 * P ^ 2) * ε / s := by
      rw [← sub_le_iff_le_add', le_div_iff₀ hs0]
      nlinarith
    have hmono : (3 * q + 2 * K ^ 2 * P ^ 2) * ε / s ≤ (3 * q + 2 * K ^ 2 * P ^ 2) / c * ε := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hc hcs
    linarith
  rcases hq.lt_or_eq with hqpos | hqz
  · have h := hq2
    rw [sq] at h
    exact le_of_mul_le_mul_right (by linarith) hqpos
  · rw [← hqz]
    positivity

namespace EllipticWholeSpaceSolution

variable {K : ℝ} (s : EllipticWholeSpaceSolution d K)

theorem memLp_normalized_Dv [NeZero d] (N : ℕ) (i : Fin d) :
    MemLp (fun x => s.Dv x i) 2 (normalizedCubeMeasure (originCube d (N : ℤ))) :=
  (s.memLp_cubeSet_Dv N i).smul_measure ENNReal.ofReal_ne_top

theorem vecNormSq_le_energyDensity (x : Vec d) :
    vecNormSq (s.Dv x) ≤ vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)) := by
  have h := (s.elliptic x).2.2.1 (s.Dv x)
  linarith

theorem abs_vecDot_flux_le (hK : 1 ≤ K) (p x : Vec d) :
    |vecDot p (matVecMul (s.coeff x) (s.Dv x))| ≤
      K * Real.sqrt (vecNormSq p) * Real.sqrt (vecNormSq (s.Dv x)) := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq p (matVecMul (s.coeff x) (s.Dv x))
  have hfb := vecNormSq_matVecMul_le_of_isEllipticMatrix (s.elliptic x) (s.Dv x)
  have hK0 : 0 ≤ K := by linarith
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (vecDot p (matVecMul (s.coeff x) (s.Dv x)) ^ 2)
      ≤ Real.sqrt (vecNormSq p * (K ^ 2 * vecNormSq (s.Dv x))) :=
        Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hfb (vecNormSq_nonneg p)))
    _ = K * Real.sqrt (vecNormSq p) * Real.sqrt (vecNormSq (s.Dv x)) := by
        rw [Real.sqrt_mul (vecNormSq_nonneg p), Real.sqrt_mul (by positivity), Real.sqrt_sq hK0]
        ring

theorem abs_energyDensity_le (hK : 1 ≤ K) (x : Vec d) :
    |vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))| ≤ K * vecNormSq (s.Dv x) := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))
  have hfb := vecNormSq_matVecMul_le_of_isEllipticMatrix (s.elliptic x) (s.Dv x)
  have hnn := vecNormSq_nonneg (s.Dv x)
  have h2 : vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)) ^ 2 ≤ (K * vecNormSq (s.Dv x)) ^ 2 := by
    calc _ ≤ vecNormSq (s.Dv x) * vecNormSq (matVecMul (s.coeff x) (s.Dv x)) := hcs
      _ ≤ vecNormSq (s.Dv x) * (K ^ 2 * vecNormSq (s.Dv x)) :=
        mul_le_mul_of_nonneg_left hfb hnn
      _ = (K * vecNormSq (s.Dv x)) ^ 2 := by ring
  exact abs_le_of_sq_le_sq' h2 (by nlinarith) |>.elim fun h1 h3 => abs_le.mpr ⟨h1, h3⟩

theorem aestronglyMeasurable_normalized_energyDensity [NeZero d] (N : ℕ) :
    AEStronglyMeasurable (fun x => vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have hmeasf (i j : Fin d) : Measurable (fun x => s.coeff x i j) :=
    (measurable_pi_iff.mp (measurable_pi_iff.mp s.measurable_coeff i)) j
  have hDv (i : Fin d) := (s.memLp_normalized_Dv N i).aestronglyMeasurable
  simp only [vecDot, matVecMul]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hDv i).mul ?_
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
    ((hmeasf i j).aestronglyMeasurable).mul (hDv j)

theorem integrable_normalized_vecNormSq_Dv [NeZero d] (N : ℕ) :
    Integrable (fun x => vecNormSq (s.Dv x)) (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have h := integrable_finsetSum (μ := normalizedCubeMeasure (originCube d (N : ℤ)))
    Finset.univ fun i _ => (s.memLp_normalized_Dv N i).integrable_sq
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [vecNormSq, vecDot, sq]

section Weighted

variable [NeZero d] (N : ℕ) {η : Vec d → ℝ} (hηc : Continuous η) (hη0 : ∀ x, 0 ≤ η x)
  (hη1 : ∀ x, η x ≤ 1)
include hηc hη0 hη1

theorem memLp_normalized_cutoff :
    MemLp η 2 (normalizedCubeMeasure (originCube d (N : ℤ))) :=
  memLp_normalizedCubeMeasure_of_bound _ hηc.aestronglyMeasurable
    (c := 1) fun x => abs_le.mpr ⟨by linarith [hη0 x], hη1 x⟩

theorem memLp_normalized_cutoff_mul_Dv (i : Fin d) :
    MemLp (fun x => η x * s.Dv x i) 2 (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    ⟨normalizedCubeMeasure_apply_univ _⟩
  have hb : MemLp η ⊤ (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    memLp_top_of_bound hηc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hη0 x], hη1 x⟩)
  exact hb.fun_mul (s.memLp_normalized_Dv N i)


theorem integrable_normalized_weightedEnergy (hK : 1 ≤ K) :
    Integrable (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  refine Integrable.mono' ((s.integrable_normalized_vecNormSq_Dv N).const_mul K)
    ((hηc.pow 2).aestronglyMeasurable.mul (s.aestronglyMeasurable_normalized_energyDensity N))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have h1 := s.abs_energyDensity_le hK x
  have h2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
  have h3 : 0 ≤ K * vecNormSq (s.Dv x) := by
    have := vecNormSq_nonneg (s.Dv x)
    nlinarith
  calc η x ^ 2 * |vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))|
      ≤ 1 * (K * vecNormSq (s.Dv x)) :=
        mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
    _ = K * vecNormSq (s.Dv x) := one_mul _

/-- **Weighted Cauchy–Schwarz for the mean gradient.** -/
theorem sum_sq_cubeAverage_le_weightedEnergy (hK : 1 ≤ K) :
    ∑ i, cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2 * s.Dv x i) ^ 2 ≤
      cubeAverage (originCube d (N : ℤ)) (fun x => η x ^ 2) *
        cubeAverage (originCube d (N : ℤ))
          (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) := by
  set Q := originCube d (N : ℤ)
  have hcoord (i : Fin d) : cubeAverage Q (fun x => η x ^ 2 * s.Dv x i) ^ 2 ≤
      cubeAverage Q (fun x => η x ^ 2) * cubeAverage Q (fun x => (η x * s.Dv x i) ^ 2) := by
    have h := sq_cubeAverage_mul_le Q (memLp_normalized_cutoff N hηc hη0 hη1)
      (s.memLp_normalized_cutoff_mul_Dv N hηc hη0 hη1 i)
    have heq : (fun x => η x * (η x * s.Dv x i)) = fun x => η x ^ 2 * s.Dv x i := by
      funext x
      ring
    rw [heq] at h
    exact h
  have hsum : ∑ i, cubeAverage Q (fun x => (η x * s.Dv x i) ^ 2) =
      cubeAverage Q (fun x => η x ^ 2 * vecNormSq (s.Dv x)) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← integral_finsetSum _ fun i _ =>
      (s.memLp_normalized_cutoff_mul_Dv N hηc hη0 hη1 i).integrable_sq]
    congr 1
    funext x
    simp only [vecNormSq, vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmono : cubeAverage Q (fun x => η x ^ 2 * vecNormSq (s.Dv x)) ≤
      cubeAverage Q (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    refine integral_mono ?_ (s.integrable_normalized_weightedEnergy N hηc hη0 hη1 hK)
      fun x => mul_le_mul_of_nonneg_left (s.vecNormSq_le_energyDensity x) (sq_nonneg _)
    have h := integrable_finsetSum (μ := normalizedCubeMeasure Q) Finset.univ fun i _ =>
      (s.memLp_normalized_cutoff_mul_Dv N hηc hη0 hη1 i).integrable_sq
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecNormSq, vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hη2 : 0 ≤ cubeAverage Q (fun x => η x ^ 2) :=
    cubeAverage_nonneg_of_nonneg Q fun x => sq_nonneg _
  calc ∑ i, cubeAverage Q (fun x => η x ^ 2 * s.Dv x i) ^ 2
      ≤ ∑ i, cubeAverage Q (fun x => η x ^ 2) * cubeAverage Q (fun x => (η x * s.Dv x i) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = cubeAverage Q (fun x => η x ^ 2) * cubeAverage Q (fun x => η x ^ 2 * vecNormSq (s.Dv x)) := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hη2

theorem memLp_normalized_cutoff_mul_normDv :
    MemLp (fun x => η x * Real.sqrt (vecNormSq (s.Dv x))) 2
      (normalizedCubeMeasure (originCube d (N : ℤ))) := by
  have hmeasN : AEStronglyMeasurable (fun x => vecNormSq (s.Dv x))
      (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    (s.integrable_normalized_vecNormSq_Dv N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x => η x * Real.sqrt (vecNormSq (s.Dv x)))
      (normalizedCubeMeasure (originCube d (N : ℤ))) :=
    hηc.aestronglyMeasurable.mul (Real.continuous_sqrt.comp_aestronglyMeasurable hmeasN)
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' (s.integrable_normalized_vecNormSq_Dv N) (hmeas.pow 2)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow,
    Real.sq_sqrt (vecNormSq_nonneg _)]
  have h2 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
  have := vecNormSq_nonneg (s.Dv x)
  nlinarith

theorem cubeAverage_weighted_vecNormSq_le (hK : 1 ≤ K) :
    cubeAverage (originCube d (N : ℤ)) (fun x => (η x * Real.sqrt (vecNormSq (s.Dv x))) ^ 2) ≤
      cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_mono (s.memLp_normalized_cutoff_mul_normDv N hηc hη0 hη1).integrable_sq
    (s.integrable_normalized_weightedEnergy N hηc hη0 hη1 hK) fun x => ?_
  rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (s.vecNormSq_le_energyDensity x) (sq_nonneg _)

/-- **Weighted Cauchy–Schwarz for the flux.** -/
theorem cubeAverage_flux_le (hK : 1 ≤ K) (p : Vec d) :
    cubeAverage (originCube d (N : ℤ))
        (fun x => η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x))) ≤
      K * Real.sqrt (vecNormSq p) * Real.sqrt (cubeAverage (originCube d (N : ℤ))
          (fun x => η x ^ 2)) *
        Real.sqrt (cubeAverage (originCube d (N : ℤ))
          (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x)))) := by
  set Q := originCube d (N : ℤ)
  have hK0 : 0 ≤ K := by linarith
  have hfg := s.memLp_normalized_cutoff_mul_normDv N hηc hη0 hη1
  have hf := memLp_normalized_cutoff N hηc hη0 hη1
  have hprod : Integrable (fun x => η x * (η x * Real.sqrt (vecNormSq (s.Dv x))))
      (normalizedCubeMeasure Q) := hf.integrable_mul hfg
  have hmeasflux : AEStronglyMeasurable (fun x => vecDot p (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure Q) := by
    have hmeasf (i j : Fin d) : Measurable (fun x => s.coeff x i j) :=
      (measurable_pi_iff.mp (measurable_pi_iff.mp s.measurable_coeff i)) j
    have hDv (i : Fin d) := (s.memLp_normalized_Dv N i).aestronglyMeasurable
    simp only [vecDot, matVecMul]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => aestronglyMeasurable_const.mul ?_
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      ((hmeasf i j).aestronglyMeasurable).mul (hDv j)
  have hpt (x : Vec d) : η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x)) ≤
      K * Real.sqrt (vecNormSq p) * (η x * (η x * Real.sqrt (vecNormSq (s.Dv x)))) := by
    have h := s.abs_vecDot_flux_le hK p x
    have h2 := le_abs_self (vecDot p (matVecMul (s.coeff x) (s.Dv x)))
    have h3 : η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x)) ≤
        η x ^ 2 * (K * Real.sqrt (vecNormSq p) * Real.sqrt (vecNormSq (s.Dv x))) :=
      mul_le_mul_of_nonneg_left (h2.trans h) (sq_nonneg _)
    calc _ ≤ _ := h3
      _ = _ := by ring
  have hint1 : Integrable (fun x => η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x)))
      (normalizedCubeMeasure Q) := by
    refine Integrable.mono' (hprod.const_mul (K * Real.sqrt (vecNormSq p)))
      ((hηc.pow 2).aestronglyMeasurable.mul hmeasflux) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h := s.abs_vecDot_flux_le hK p x
    have hη := hη0 x
    calc η x ^ 2 * |vecDot p (matVecMul (s.coeff x) (s.Dv x))|
        ≤ η x ^ 2 * (K * Real.sqrt (vecNormSq p) * Real.sqrt (vecNormSq (s.Dv x))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by ring
  have hmono : cubeAverage Q (fun x => η x ^ 2 * vecDot p (matVecMul (s.coeff x) (s.Dv x))) ≤
      K * Real.sqrt (vecNormSq p) *
        cubeAverage Q (fun x => η x * (η x * Real.sqrt (vecNormSq (s.Dv x)))) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← integral_const_mul]
    exact integral_mono hint1 (hprod.const_mul _) hpt
  have hcs := sq_cubeAverage_mul_le Q hf hfg
  have hcs' : cubeAverage Q (fun x => η x * (η x * Real.sqrt (vecNormSq (s.Dv x)))) ≤
      Real.sqrt (cubeAverage Q (fun x => η x ^ 2)) *
        Real.sqrt (cubeAverage Q (fun x => (η x * Real.sqrt (vecNormSq (s.Dv x))) ^ 2)) := by
    rw [← Real.sqrt_mul (cubeAverage_nonneg_of_nonneg Q fun x => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hcs
  have hw := s.cubeAverage_weighted_vecNormSq_le N hηc hη0 hη1 hK
  have hc0 : 0 ≤ K * Real.sqrt (vecNormSq p) := by positivity
  calc _ ≤ _ := hmono
    _ ≤ K * Real.sqrt (vecNormSq p) * (Real.sqrt (cubeAverage Q (fun x => η x ^ 2)) *
          Real.sqrt (cubeAverage Q (fun x => (η x * Real.sqrt (vecNormSq (s.Dv x))) ^ 2))) :=
        mul_le_mul_of_nonneg_left hcs' hc0
    _ ≤ K * Real.sqrt (vecNormSq p) * (Real.sqrt (cubeAverage Q (fun x => η x ^ 2)) *
          Real.sqrt (cubeAverage Q
            (fun x => η x ^ 2 * vecDot (s.Dv x) (matVecMul (s.coeff x) (s.Dv x))))) := by
        gcongr
    _ = _ := by ring

end Weighted

end EllipticWholeSpaceSolution

end EinsteinFull.Homogenization
