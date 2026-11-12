import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Convex.Integral

/-! The centering step in the L²-to-Lᵐ argument, `paper/main.tex:735-739`. -/
open MeasureTheory
open Set
open ENNReal

namespace EinsteinRelation.Correctors

/-- For a probability measure and `p ≥ 1`, `|∫ f| ≤ eLpNorm f (ENNReal.ofReal p) μ` in ENNReal. -/
private lemma abs_integral_le_eLpNorm_ofReal {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {p : ℝ} {f : X → ℝ} (hf : Integrable f μ) (hp : 1 ≤ p) :
    ENNReal.ofReal (|∫ x, f x ∂μ|) ≤ eLpNorm f (ENNReal.ofReal p) μ := by
  have hp_pos : 0 < p := by linarith
  calc
    ENNReal.ofReal (|∫ x, f x ∂μ|) ≤ ENNReal.ofReal (∫ x, |f x| ∂μ) := by
      gcongr
      exact abs_integral_le_integral_abs
    _ = ∫⁻ x, ENNReal.ofReal (|f x|) ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun x => abs_nonneg _)]
    _ = eLpNorm f 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      refine lintegral_congr_ae ?_
      filter_upwards with x
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    _ ≤ eLpNorm f (ENNReal.ofReal p) μ := by
      refine eLpNorm_le_eLpNorm_of_exponent_le ?_ hf.1
      simpa using ENNReal.one_le_ofReal.mpr hp

/-- Centering a scalar function costs at most 2^p in its p-th moment. -/
theorem lintegral_centered_abs_rpow_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (u : X → ℝ) (c p : ℝ)
    (hp : 1 ≤ p) (hu : MemLp u (ENNReal.ofReal p) μ) :
    (∫⁻ x, ENNReal.ofReal (|u x - ∫ y, u y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) *
        (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) := by
  set m := ∫ y, u y ∂μ with hm
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := by linarith
  have hENNRealp : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.one_le_ofReal.mpr hp
  have hu_int : Integrable u μ := hu.integrable hENNRealp

  set v := fun x : X => u x - c with hv_def
  have hv_int : Integrable v μ := hu_int.sub (integrable_const c)
  have hmv : ∫ y, v y ∂μ = m - c := by
    rw [hv_def]
    calc
      ∫ y, (u y - c) ∂μ = (∫ y, u y ∂μ) - (∫ y, c ∂μ) :=
        integral_sub hu_int (integrable_const c)
      _ = m - (∫ y, c ∂μ) := by rw [← hm]
      _ = m - (μ.real univ • c) := by rw [integral_const]
      _ = m - (1 • c) := by simp
      _ = m - c := by simp

  let f : X → ℝ≥0∞ := fun x => ENNReal.ofReal (|v x|)
  let g_enn : X → ℝ≥0∞ := fun _ => ENNReal.ofReal (|m - c|)

  have h_meas_f : AEMeasurable f μ := by
    have : AEMeasurable (fun x : X => |v x|) μ :=
      hv_int.abs.aestronglyMeasurable.aemeasurable
    exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable this)
  have h_meas_g : AEMeasurable g_enn μ := aemeasurable_const

  have h_pointwise (x : X) : |u x - m| ≤ |v x| + |m - c| := by
    calc
      |u x - m| = |(u x - c) - (m - c)| := by congr 1; ring
      _ = |v x - (m - c)| := by rw [hv_def]
      _ ≤ |v x| + |m - c| := abs_sub _ _

  have h_enn (x : X) : ENNReal.ofReal (|u x - m|) ≤ f x + g_enn x := by
    dsimp [f, g_enn]
    calc
      ENNReal.ofReal (|u x - m|) ≤ ENNReal.ofReal (|v x| + |m - c|) :=
        ENNReal.ofReal_le_ofReal (h_pointwise x)
      _ ≤ ENNReal.ofReal (|v x|) + ENNReal.ofReal (|m - c|) :=
        ENNReal.ofReal_add_le

  have h_pow (x : X) : ENNReal.ofReal (|u x - m| ^ p) ≤ ((f + g_enn) x) ^ p := by
    calc
      ENNReal.ofReal (|u x - m| ^ p) = (ENNReal.ofReal (|u x - m|)) ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_nonneg]
      _ ≤ (f x + g_enn x) ^ p := by gcongr; exact h_enn x
      _ = ((f + g_enn) x) ^ p := rfl

  have h_int_ineq : (∫⁻ x, ENNReal.ofReal (|u x - m| ^ p) ∂μ) ≤
      (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) :=
    lintegral_mono h_pow

  have h_minkowski : (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) + (∫⁻ x, (g_enn x) ^ p ∂μ) ^ (1 / p) :=
    lintegral_Lp_add_le h_meas_f h_meas_g hp

  have h_const_int : (∫⁻ x, (g_enn x) ^ p ∂μ) = (ENNReal.ofReal (|m - c|)) ^ p := by
    simp [g_enn, lintegral_const, measure_univ, mul_one]

  have h_const_term : (∫⁻ x, (g_enn x) ^ p ∂μ) ^ (1 / p) = ENNReal.ofReal (|m - c|) := by
    rw [h_const_int]
    calc
      ((ENNReal.ofReal (|m - c|)) ^ p) ^ (1 / p) =
          (ENNReal.ofReal (|m - c|)) ^ (p * (1 / p)) := by
        rw [ENNReal.rpow_mul (ENNReal.ofReal (|m - c|)) p (1 / p)]
      _ = (ENNReal.ofReal (|m - c|)) ^ (1 : ℝ) := by
        rw [mul_one_div_cancel hp_pos.ne']
      _ = ENNReal.ofReal (|m - c|) := by rw [ENNReal.rpow_one]

  have h_key : ENNReal.ofReal (|m - c|) ≤ (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
    have h_abs_int : ENNReal.ofReal (|∫ x, v x ∂μ|) ≤ eLpNorm v (ENNReal.ofReal p) μ :=
      abs_integral_le_eLpNorm_ofReal μ hv_int hp
    rw [hmv] at h_abs_int

    have h_eLpNorm_eq : eLpNorm v (ENNReal.ofReal p) μ = (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
      have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
        simpa using ENNReal.ofReal_pos.mpr hp_pos
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero ENNReal.ofReal_ne_top]
      have h_exp : (ENNReal.ofReal p).toReal = p := by simp [hp_nonneg]
      rw [h_exp]
      refine congrArg (fun t => t ^ (1 / p)) ?_
      refine lintegral_congr_ae ?_
      filter_upwards with x
      dsimp [f, v]
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    rw [h_eLpNorm_eq] at h_abs_int
    exact h_abs_int

  have h_minkowski' : (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) ^ (1 / p) ≤
      2 * (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
    rw [h_const_term] at h_minkowski

    have h_sum : (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) + ENNReal.ofReal (|m - c|) ≤
        2 * (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
      have h_add : (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) + ENNReal.ofReal (|m - c|) ≤
          (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) + (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) :=
        add_le_add_right h_key ((∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p))
      have h_two : (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) + (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) =
          2 * (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) := by
        ring
      rw [h_two] at h_add
      exact h_add
    exact le_trans h_minkowski h_sum

  set A := (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) ^ (1 / p) with hA
  set B := (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) with hB
  have hA_eq : (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) = A ^ p := by
    rw [hA]
    rw [← ENNReal.rpow_mul (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) (1 / p) p,
      one_div_mul_cancel hp_pos.ne', ENNReal.rpow_one]
  have hB_eq : (∫⁻ x, (f x) ^ p ∂μ) = B ^ p := by
    rw [hB]
    rw [← ENNReal.rpow_mul (∫⁻ x, (f x) ^ p ∂μ) (1 / p) p,
      one_div_mul_cancel hp_pos.ne', ENNReal.rpow_one]
  have h_pow_ineq : A ^ p ≤ (2 * B) ^ p := by
    gcongr

  have h_mid : (2 * B) ^ p ≤ ENNReal.ofReal (2 ^ p) * (B ^ p) := by
    apply le_of_eq
    calc
      (2 * B) ^ p = (2 : ℝ≥0∞) ^ p * B ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg (2 : ℝ≥0∞) B hp_nonneg]
      _ = ENNReal.ofReal (2 ^ p) * B ^ p := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp_nonneg]
  have h_final : A ^ p ≤ ENNReal.ofReal (2 ^ p) * (B ^ p) :=
    h_pow_ineq.trans h_mid

  have h_f_pow_eq : (∫⁻ x, (f x) ^ p ∂μ) = (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    dsimp [f, v]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_nonneg]

  calc
    (∫⁻ x, ENNReal.ofReal (|u x - m| ^ p) ∂μ) ≤ (∫⁻ x, ((f + g_enn) x) ^ p ∂μ) := h_int_ineq
    _ = A ^ p := by rw [hA_eq]
    _ ≤ ENNReal.ofReal (2 ^ p) * (B ^ p) := h_final
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ x, (f x) ^ p ∂μ) := by rw [hB_eq]
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) := by rw [h_f_pow_eq]

end EinsteinRelation.Correctors
