import EinsteinRelation.Correctors.PairedPDEQuadraticConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded multiplier limits for the temporal regularization

Source: `paper/main.tex:822–830`. Bounded pointwise convergent difference
quotients can be multiplied by the actual L² solution before taking the
strong limit. No time derivative of the solution is used.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Dominated convergence of bounded multipliers holds in the actual
strong L² seminorm after multiplication by an L² field.
Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_bounded_multiplier_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u q : X → ℝ} {qs : ℕ → X → ℝ}
    (hu : MemLp u 2 μ) (hq : AEStronglyMeasurable q μ)
    (hqs : ∀ k, AEStronglyMeasurable (qs k) μ)
    {B : ℝ} (hqb : ∀ᵐ x ∂μ, ‖q x‖ ≤ B)
    (hqsb : ∀ k, ∀ᵐ x ∂μ, ‖qs k x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => qs k x) atTop (𝓝 (q x))) :
    Tendsto (fun k => eLpNorm (fun x => (qs k x - q x) * u x) 2 μ)
      atTop (𝓝 0) := by
  let D : ℕ → X → ℝ := fun k x => (qs k x - q x) * u x
  have hqm : MemLp q ∞ μ := memLp_top_of_bound hq B hqb
  have hqsm (k : ℕ) : MemLp (qs k) ∞ μ := memLp_top_of_bound (hqs k) B (hqsb k)
  have hD (k : ℕ) : MemLp (D k) 2 μ := ((hqsm k).sub hqm).fun_mul hu
  have hbound (k : ℕ) : ∀ᵐ x ∂μ, ‖(D k x)^2‖ ≤ (2 * B)^2 * (u x)^2 := by
    filter_upwards [hqsb k, hqb] with x hx hy
    have hd : ‖qs k x - q x‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith only [hx, hy])
    calc
      ‖(D k x)^2‖ = ‖qs k x - q x‖^2 * (u x)^2 := by
        simp only [D, norm_pow, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ (2 * B)^2 * (u x)^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hd 2) (sq_nonneg _)
  have hzero : ∀ᵐ x ∂μ, Tendsto (fun k => (D k x)^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have ht := ((hx.sub_const (q x)).mul_const (u x)).pow 2
    simpa only [D, sub_self, zero_mul, zero_pow (by decide : 2 ≠ 0)] using ht
  have hI : Tendsto (fun k => ∫ x, (D k x)^2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using! tendsto_integral_of_dominated_convergence
      (fun x => (2 * B)^2 * (u x)^2)
      (fun k => (hD k).aestronglyMeasurable.pow 2)
      (hu.integrable_sq.const_mul ((2 * B)^2)) hbound hzero
  have hn (k : ℕ) : ‖(hD k).toLp (D k)‖ = Real.sqrt (∫ x, (D k x)^2 ∂μ) := by
    have hs : ‖(hD k).toLp (D k)‖^2 = ∫ x, (D k x)^2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hD k).coeFn_toLp] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  have hN : Tendsto (fun k => ‖(hD k).toLp (D k)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hn, Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hI
  have hE := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hN
  simpa only [Function.comp_def, ofReal_norm_eq_enorm, Lp.enorm_toLp,
    ENNReal.ofReal_zero, D] using hE

end EinsteinRelation.Correctors
