import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Moment form of Hoeffding's inequality

For independent centred random variables `X i` with `|X i| ≤ c i` almost surely,
Hoeffding's lemma makes each summand sub-Gaussian. Independence then makes the sum over a
finite set `s` sub-Gaussian with variance proxy `∑ i ∈ s, c i ^ 2`. For `m ≥ 1`, the `m`-th
absolute moment of the sum is at most `hoeffdingMomentConst m * (∑ i ∈ s, c i ^ 2) ^ (m / 2)`,
where the constant depends only on `m`.

The proof avoids a layer-cake integration. Rescaling by the standard deviation `σ` of the sum,
the pointwise bound `|x| ^ m ≤ σ ^ m (m / e) ^ m (exp (x / σ) + exp (-x / σ))` turns the moment
into two exponential moments, which the sub-Gaussian bound controls.

This is the moment bound used for the clock spatial averages in `paper/main.tex`
(eq. `clock-spatial-averages`, lines 1159–1163).
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Probability

/-- The explicit constant `2 e^{1/2} (m / e) ^ m` of the Hoeffding moment bound. -/
noncomputable def hoeffdingMomentConst (m : ℝ) : ℝ :=
  2 * Real.exp (1 / 2) * (m / Real.exp 1) ^ m

/-- For `x ≥ 0` and `m > 0`, `x ^ m ≤ (m / e) ^ m * exp x`: the function `x ^ m exp (-x)`
is maximal at `x = m`, where it equals `(m / e) ^ m`. -/
private lemma hoeffding_rpow_le_mul_exp {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) :
    x ^ m ≤ (m / Real.exp 1) ^ m * Real.exp x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.zero_rpow hm.ne']
    exact mul_nonneg (Real.rpow_nonneg (div_nonneg hm.le (Real.exp_pos 1).le) m)
      (Real.exp_pos 0).le
  · have hlog : Real.log (x / m) ≤ x / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hx hm)
    rw [Real.log_div hx.ne' hm.ne'] at hlog
    have h1 : m * (Real.log x - Real.log m) ≤ m * (x / m - 1) :=
      mul_le_mul_of_nonneg_left hlog hm.le
    have h2 : m * (x / m - 1) = x - m := by
      rw [mul_sub, mul_div_cancel₀ x hm.ne', mul_one]
    have h3 : m * (Real.log x - Real.log m) = Real.log x * m - Real.log m * m := by ring
    have h4 : (Real.log m - 1) * m = Real.log m * m - m := by ring
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (div_pos hm (Real.exp_pos 1)),
      ← Real.exp_add, Real.exp_le_exp, Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp]
    linarith

/-- Pointwise domination of `|x| ^ m` by two exponentials of `t * x`, with the scale `t⁻¹`. -/
private lemma hoeffding_abs_rpow_le_exp_add {t m : ℝ} (x : ℝ) (ht : 0 < t) (hm : 0 < m) :
    |x| ^ m ≤ t⁻¹ ^ m * ((m / Real.exp 1) ^ m * (Real.exp (t * x) + Real.exp ((-t) * x))) := by
  have hu0 : 0 ≤ t * |x| := mul_nonneg ht.le (abs_nonneg x)
  have hx : |x| = t⁻¹ * (t * |x|) := by
    rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  have hexp : Real.exp (t * |x|) ≤ Real.exp (t * x) + Real.exp ((-t) * x) := by
    rw [show t * |x| = |t * x| by rw [abs_mul, abs_of_pos ht], neg_mul]
    exact Real.exp_abs_le (t * x)
  have hinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  calc |x| ^ m = t⁻¹ ^ m * (t * |x|) ^ m := by
        rw [← Real.mul_rpow hinv hu0, ← hx]
    _ ≤ t⁻¹ ^ m * ((m / Real.exp 1) ^ m * Real.exp (t * |x|)) :=
        mul_le_mul_of_nonneg_left (hoeffding_rpow_le_mul_exp hu0 hm) (Real.rpow_nonneg hinv m)
    _ ≤ t⁻¹ ^ m * ((m / Real.exp 1) ^ m * (Real.exp (t * x) + Real.exp ((-t) * x))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp
            (Real.rpow_nonneg (div_nonneg hm.le (Real.exp_pos 1).le) m))
          (Real.rpow_nonneg hinv m)

/-- The Hoeffding variance proxy `(‖x - -x‖₊ / 2) ^ 2` of the interval `[-x, x]` equals `x ^ 2`. -/
private lemma coe_hoeffding_param (x : ℝ) :
    (((‖x - -x‖₊ / 2) ^ 2 : NNReal) : ℝ) = x ^ 2 := by
  have h1 : ((‖x - -x‖₊ : NNReal) : ℝ) = 2 * |x| := by
    rw [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
  have h2 : ((2 : NNReal) : ℝ) = 2 := by norm_num
  have h3 : 2 * |x| / 2 = |x| := by ring
  rw [NNReal.coe_pow, NNReal.coe_div, h1, h2, h3, sq_abs]

/-- Hoeffding's lemma for each summand, and independence for the sum: the sum over `s` of
independent centred variables with `|X i| ≤ c i` is sub-Gaussian with variance proxy
`∑ i ∈ s, c i ^ 2`, written through the Hoeffding parameters of the intervals `[-c i, c i]`. -/
private lemma hasSubgaussianMGF_sum_bounded {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ) (hindep : iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i)) (c : ι → ℝ) (hc : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, (‖c i - -c i‖₊ / 2) ^ 2) μ := by
  have hsubi : ∀ i, HasSubgaussianMGF (X i) ((‖c i - -c i‖₊ / 2) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i).aemeasurable
      ((hc i).mono fun ω h => Set.mem_Icc.mpr (abs_le.mp h)) (hmean i)
  exact HasSubgaussianMGF.sum_of_iIndepFun hindep (fun i _ => hsubi i)

/-- **Moment form of Hoeffding's inequality.** For independent centred random variables with
`|X i| ≤ c i` almost surely, the `m`-th absolute moment of the sum over a finite set `s`
is at most `hoeffdingMomentConst m * (∑ i ∈ s, c i ^ 2) ^ (m / 2)`, for every `m ≥ 1`. -/
theorem lintegral_abs_sum_rpow_le_of_iIndepFun {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) (X : ι → Ω → ℝ) (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (c : ι → ℝ) (hc : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (m : ℝ) (hm : 1 ≤ m) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m) ∂μ
      ≤ ENNReal.ofReal (hoeffdingMomentConst m * (∑ i ∈ s, c i ^ 2) ^ (m / 2)) := by
  have hm0 : 0 < m := by linarith
  have hV : 0 ≤ ∑ i ∈ s, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  rcases hV.eq_or_lt with hV0 | hV0
  · -- Degenerate case: all `c i` with `i ∈ s` vanish, so the sum is zero almost surely.
    have hc0 : ∀ i ∈ s, c i = 0 := by
      intro i hi
      have h1 : c i ^ 2 ≤ ∑ j ∈ s, c j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (c j)) hi
      have h2 : c i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      exact (pow_eq_zero_iff two_ne_zero).mp h2
    have hS : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = 0 :=
      (Filter.eventually_all_finset s).mpr fun i hi => by
        show ∀ᵐ ω ∂μ, X i ω = 0
        filter_upwards [hc i] with ω hω
        rw [hc0 i hi] at hω
        obtain ⟨h1, h2⟩ := abs_le.mp hω
        linarith
    have hae : (fun ω => ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hS] with ω hω
      show ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m) = 0
      rw [Finset.sum_eq_zero hω, abs_zero, Real.zero_rpow hm0.ne', ENNReal.ofReal_zero]
    have hL : ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m) ∂μ = 0 := by
      rw [lintegral_congr_ae hae, lintegral_zero]
    exact (le_of_eq hL).trans zero_le
  · -- Nondegenerate case: scale by the standard deviation `σ` of the sum.
    obtain ⟨σ, hσ, hσsq⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = ∑ i ∈ s, c i ^ 2 :=
      ⟨Real.sqrt (∑ i ∈ s, c i ^ 2), Real.sqrt_pos.mpr hV0, Real.sq_sqrt hV⟩
    have hsub := hasSubgaussianMGF_sum_bounded s X hindep hmeas c hc hmean
    have hcoe : ((∑ i ∈ s, (‖c i - -c i‖₊ / 2) ^ 2 : NNReal) : ℝ) = σ ^ 2 := by
      rw [NNReal.coe_sum, hσsq]
      exact Finset.sum_congr rfl fun i _ => coe_hoeffding_param (c i)
    -- Exponential moments at the two scales `t` with `t ^ 2 σ ^ 2 = 1`.
    have hmgf : ∀ t : ℝ, t ^ 2 * σ ^ 2 = 1 →
        ∫ ω, Real.exp (t * ∑ i ∈ s, X i ω) ∂μ ≤ Real.exp (1 / 2) := by
      intro t ht
      have h := hsub.mgf_le t
      rw [hcoe, show σ ^ 2 * t ^ 2 / 2 = 1 / 2 by rw [mul_comm, ht]] at h
      exact h
    have ht1 : (σ⁻¹) ^ 2 * σ ^ 2 = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hσ.ne')]
    have ht2 : (-σ⁻¹) ^ 2 * σ ^ 2 = 1 := by
      rw [neg_sq, ht1]
    have hA : Integrable (fun ω => Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω)) μ :=
      hsub.integrable_exp_mul σ⁻¹
    have hB : Integrable (fun ω => Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω)) μ :=
      hsub.integrable_exp_mul (-σ⁻¹)
    -- Pointwise domination of the moment by the two exponentials.
    have hpt : ∀ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m) ≤
        ENNReal.ofReal (σ ^ m * ((m / Real.exp 1) ^ m *
          (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω)))) := by
      intro ω
      refine ENNReal.ofReal_le_ofReal ?_
      have h := hoeffding_abs_rpow_le_exp_add (t := σ⁻¹) (∑ i ∈ s, X i ω) (inv_pos.mpr hσ) hm0
      rwa [inv_inv] at h
    have hI : Integrable (fun ω => σ ^ m * ((m / Real.exp 1) ^ m *
        (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω)))) μ :=
      ((hA.add hB).const_mul ((m / Real.exp 1) ^ m)).const_mul (σ ^ m)
    have hnn : ∀ ω, 0 ≤ σ ^ m * ((m / Real.exp 1) ^ m *
        (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω))) := fun ω =>
      mul_nonneg (Real.rpow_nonneg hσ.le m)
        (mul_nonneg (Real.rpow_nonneg (div_nonneg hm0.le (Real.exp_pos 1).le) m)
          (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    have hcalc := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)
    have hsum : ∫ ω, (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω)) ∂μ
        ≤ 2 * Real.exp (1 / 2) := by
      rw [integral_add hA hB]
      linarith [hmgf σ⁻¹ ht1, hmgf (-σ⁻¹) ht2]
    have hbound : ∫ ω, σ ^ m * ((m / Real.exp 1) ^ m *
        (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω))) ∂μ
        ≤ σ ^ m * ((m / Real.exp 1) ^ m * (2 * Real.exp (1 / 2))) := by
      rw [integral_const_mul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum
          (Real.rpow_nonneg (div_nonneg hm0.le (Real.exp_pos 1).le) m))
        (Real.rpow_nonneg hσ.le m)
    have hpow : (σ ^ 2) ^ (m / 2) = σ ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
      congr 1
      push_cast
      ring
    calc ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ s, X i ω| ^ m) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (σ ^ m * ((m / Real.exp 1) ^ m *
            (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω)))) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (∫ ω, σ ^ m * ((m / Real.exp 1) ^ m *
            (Real.exp (σ⁻¹ * ∑ i ∈ s, X i ω) + Real.exp ((-σ⁻¹) * ∑ i ∈ s, X i ω))) ∂μ) :=
          hcalc.symm
      _ ≤ ENNReal.ofReal (σ ^ m * ((m / Real.exp 1) ^ m * (2 * Real.exp (1 / 2)))) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (hoeffdingMomentConst m * (∑ i ∈ s, c i ^ 2) ^ (m / 2)) := by
          rw [← hσsq, hpow, hoeffdingMomentConst]
          congr 1
          ring

end EinsteinRelation.Probability
