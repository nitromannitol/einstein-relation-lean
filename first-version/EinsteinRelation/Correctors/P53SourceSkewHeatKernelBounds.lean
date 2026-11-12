import EinsteinRelation.Correctors.HeatKernelConvolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Translates of the heat kernel at large times

Source: `paper/main.tex:740-756`; AKM Lemma 6.1, Step 4. Translating the Euclidean
heat kernel by a fixed vector changes it by an `L¹`-small amount at large times:
by parabolic scaling this is the `L¹` continuity of translation for the unit-time
Gaussian, proved by dominated convergence with a wider Gaussian.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

variable {d : ℕ}

private theorem euclideanSq_le_two_mul_add (u h : Vec d) :
    euclideanSq u ≤ 2 * euclideanSq (u + h) + 2 * euclideanSq h := by
  unfold euclideanSq dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i + 2 * h i)]

private theorem euclideanSq_le_of_norm_le_one {h : Vec d} (hh : ‖h‖ ≤ 1) :
    euclideanSq h ≤ d := by
  unfold euclideanSq dot
  calc (∑ i, h i * h i) ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := (norm_le_pi_norm h i).trans hh
        rw [Real.norm_eq_abs] at hi
        nlinarith [abs_nonneg (h i), abs_mul_abs_self (h i)]
    _ = d := by simp

/-- A unit-time Gaussian translated by at most one is dominated by a wider Gaussian. -/
private theorem euclideanHeatKernel_one_add_le {u h : Vec d} (hh : ‖h‖ ≤ 1) :
    euclideanHeatKernel 1 (u + h) ≤
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (d / 4) * Real.exp (-(euclideanSq u) / 8) := by
  unfold euclideanHeatKernel
  rw [mul_one, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h1 := euclideanSq_le_two_mul_add u h
  have h2 := euclideanSq_le_of_norm_le_one hh
  linarith

private theorem integrable_exp_neg_euclideanSq_div_eight :
    Integrable (fun u : Vec d => Real.exp (-(euclideanSq u) / 8)) volume := by
  have h := (integrable_euclideanHeatKernel (d := d) (by norm_num : (0 : ℝ) < 2)).const_mul
    ((4 * Real.pi * 2) ^ ((d : ℝ) / 2))
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [euclideanHeatKernel]
  rw [← mul_assoc, ← Real.rpow_add (by positivity)]
  rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  norm_num

/-- `L¹` continuity of translation for the unit-time heat kernel. -/
theorem tendsto_integral_abs_heatKernel_one_translate_sub :
    Tendsto (fun h : Vec d => ∫ u, |euclideanHeatKernel 1 (u + h) - euclideanHeatKernel 1 u|)
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (euclideanHeatKernel (d := d) 1) := continuous_euclideanHeatKernel 1
  set K : ℝ := (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (d / 4) with hKdef
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Vec d))) (l := 𝓝 (0 : Vec d))
    (F := fun h u => |euclideanHeatKernel 1 (u + h) - euclideanHeatKernel 1 u|)
    (f := fun _ => 0)
    (fun u => K * Real.exp (-(euclideanSq u) / 8) + euclideanHeatKernel 1 u)
    (Eventually.of_forall fun h => ((hc.comp (continuous_id.add continuous_const)).sub
      hc).abs.aestronglyMeasurable)
    (by
      filter_upwards [Metric.closedBall_mem_nhds (0 : Vec d) one_pos] with h hh
      refine ae_of_all _ fun u => ?_
      rw [Metric.mem_closedBall, dist_zero_right] at hh
      have h0 := euclideanHeatKernel_nonneg (d := d) zero_le_one (u + h)
      have h1 := euclideanHeatKernel_nonneg (d := d) zero_le_one u
      have h2 := euclideanHeatKernel_one_add_le (u := u) hh
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith)
    ((integrable_exp_neg_euclideanSq_div_eight.const_mul K).add
      (integrable_euclideanHeatKernel zero_lt_one))
    (ae_of_all _ fun u => by
      have ht : Tendsto (fun h : Vec d => euclideanHeatKernel 1 (u + h)) (𝓝 0)
          (𝓝 (euclideanHeatKernel 1 u)) := by
        simpa using (hc.tendsto (u + 0)).comp
          ((continuous_const.add continuous_id).tendsto (0 : Vec d))
      have h2 := (ht.sub (tendsto_const_nhds (x := euclideanHeatKernel 1 u))).abs
      simpa using h2)
  simpa using hdom

/-- Parabolic scaling of the translation difference. -/
theorem integral_abs_heatKernel_translate_sub_eq {t : ℝ} (ht : 0 < t) (w : Vec d) :
    (∫ y, |euclideanHeatKernel t (y + w) - euclideanHeatKernel t y|) =
      ∫ u, |euclideanHeatKernel 1 (u + (Real.sqrt t)⁻¹ • w) - euclideanHeatKernel 1 u| := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun y => |euclideanHeatKernel t (y + w) - euclideanHeatKernel t y|) (Real.sqrt t)
  simp only [Module.finrank_fin_fun] at hchange
  have hpt (u : Vec d) : |euclideanHeatKernel t (Real.sqrt t • u + w) -
      euclideanHeatKernel t (Real.sqrt t • u)| =
      (Real.sqrt t ^ d)⁻¹ * |euclideanHeatKernel 1 (u + (Real.sqrt t)⁻¹ • w) -
        euclideanHeatKernel 1 u| := by
    have hw : Real.sqrt t • u + w = Real.sqrt t • (u + (Real.sqrt t)⁻¹ • w) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    rw [hw, euclideanHeatKernel_sqrt_smul ht, euclideanHeatKernel_sqrt_smul ht, ← mul_sub,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (Real.sqrt t ^ d)⁻¹)]
  simp_rw [hpt, integral_const_mul] at hchange
  have hne : (Real.sqrt t ^ d)⁻¹ ≠ 0 := by positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < ((Real.sqrt t) ^ d)⁻¹), smul_eq_mul] at hchange
  exact (mul_left_cancel₀ hne hchange).symm

/-- Translates of the heat kernel are `L¹`-close along integer times. -/
theorem tendsto_integral_abs_heatKernel_translate_sub (w : Vec d) :
    Tendsto (fun n : ℕ => ∫ y, |euclideanHeatKernel ((n + 1 : ℕ) : ℝ) (y + w) -
      euclideanHeatKernel ((n + 1 : ℕ) : ℝ) y|) atTop (𝓝 0) := by
  have hpos (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp_rw [integral_abs_heatKernel_translate_sub_eq (hpos _)]
  refine tendsto_integral_abs_heatKernel_one_translate_sub.comp ?_
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsq : Tendsto (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hinv
    simpa only [Function.comp_def, Real.sqrt_inv, Real.sqrt_zero] using h
  simpa using hsq.smul_const w

end EinsteinRelation.Correctors
