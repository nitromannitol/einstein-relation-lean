import EinsteinRelation.Correctors.HeatTransferIdentity
import EinsteinRelation.Clock.HeatCubeMasses
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Scaling and initial values of heat-kernel convolutions

Source: `paper/main.tex:1020–1022`. A compact continuous spatial kernel
convolved with the Euclidean heat kernel tends to its initial value as time
decreases to zero. The proof uses Gaussian scaling and dominated convergence.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Spatial smoothness of the Gaussian (`paper/main.tex:1020–1022`). -/
theorem contDiff_euclideanHeatKernel (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanHeatKernel (d := d) t) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSq x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∑ i, x i * x i)
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  exact contDiff_const.mul ((hsq.neg.div_const (4 * t)).exp)

/-- Parabolic scaling of the actual Euclidean heat kernel
(`paper/main.tex:1020–1022`). -/
theorem euclideanHeatKernel_scale {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (x : Vec d) :
    euclideanHeatKernel (c ^ 2 * t) (c • x) =
      (c ^ d)⁻¹ * euclideanHeatKernel t x := by
  have hsq : euclideanSq (c • x) = c ^ 2 * euclideanSq x := by
    change (∑ i, (c * x i) * (c * x i)) = c ^ 2 * ∑ i, x i * x i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbase : 4 * Real.pi * (c ^ 2 * t) = c ^ 2 * (4 * Real.pi * t) := by ring
  have hpow : (c ^ 2) ^ (-(d : ℝ) / 2) = (c ^ d)⁻¹ := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by ring,
      Real.rpow_neg hc.le, Real.rpow_natCast]
  unfold euclideanHeatKernel
  rw [hsq, hbase, Real.mul_rpow (sq_nonneg c) (by positivity), hpow]
  have hexp : -(c ^ 2 * euclideanSq x) / (4 * (c ^ 2 * t)) =
      -(euclideanSq x) / (4 * t) := by
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  rw [hexp]
  ring

/-- A spatial heat convolution can be written with a fixed unit-time
Gaussian (`paper/main.tex:1020–1022`). -/
theorem integral_kernel_heat_eq_scaled {K : Vec d → ℝ} {t : ℝ} (ht : 0 < t) (x : Vec d) :
    (∫ z, K z * euclideanHeatKernel t (x - z)) =
      ∫ z, euclideanHeatKernel 1 z * K (x - Real.sqrt t • z) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hscale (z : Vec d) : euclideanHeatKernel t (Real.sqrt t • z) =
      ((Real.sqrt t) ^ d)⁻¹ * euclideanHeatKernel 1 z := by
    simpa only [Real.sq_sqrt ht.le, mul_one] using
      euclideanHeatKernel_scale hs (by norm_num : (0 : ℝ) < 1) z
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun z => K (x - z) * euclideanHeatKernel t z) (Real.sqrt t)
  simp only [Module.finrank_pi, Fintype.card_fin,
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _))] at hchange
  have hsub : (∫ z, K (x - z) * euclideanHeatKernel t z) =
      ∫ z, K z * euclideanHeatKernel t (x - z) := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun z => K z * euclideanHeatKernel t (x - z)) volume x)
  rw [hsub] at hchange
  simp_rw [hscale] at hchange
  have hfun : (fun z => K (x - Real.sqrt t • z) *
      (((Real.sqrt t) ^ d)⁻¹ * euclideanHeatKernel 1 z)) =
      fun z => ((Real.sqrt t) ^ d)⁻¹ *
        (euclideanHeatKernel 1 z * K (x - Real.sqrt t • z)) := funext fun z => by ring
  rw [hfun, integral_const_mul] at hchange
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hs.ne')) hchange).symm

/-- Initial value of a spatial heat convolution with a compact continuous
kernel (`paper/main.tex:1020–1022`). -/
theorem tendsto_integral_kernel_heat_zero {K : Vec d → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (x : Vec d) :
    Tendsto (fun t : ℝ => ∫ z, K z * euclideanHeatKernel t (x - z))
      (𝓝[>] 0) (𝓝 (K x)) := by
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuous hK
  have hp : Continuous (euclideanHeatKernel (d := d) 1) :=
    (contDiff_euclideanHeatKernel 1).continuous
  have hbound : Integrable (fun z : Vec d => euclideanHeatKernel 1 z * C) volume :=
    (Clock.integrable_euclideanHeatKernel (by norm_num : (0 : ℝ) < 1)).mul_const C
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (f := fun z => euclideanHeatKernel 1 z * K x)
    (F := fun (t : ℝ) (z : Vec d) => euclideanHeatKernel 1 z * K (x - Real.sqrt t • z))
    (fun z : Vec d => euclideanHeatKernel 1 z * C)
    (Filter.Eventually.of_forall fun t : ℝ =>
      (hp.mul (hK.comp (show Continuous (fun z : Vec d => x - Real.sqrt t • z) by
        fun_prop))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t : ℝ => ae_of_all _ fun z => by
      show ‖euclideanHeatKernel 1 z * K (x - Real.sqrt t • z)‖ ≤ euclideanHeatKernel 1 z * C
      rw [norm_mul, Real.norm_of_nonneg (Clock.euclideanHeatKernel_nonneg (by norm_num) z)]
      exact mul_le_mul_of_nonneg_left (hC _) (Clock.euclideanHeatKernel_nonneg (by norm_num) z))
    hbound (ae_of_all _ fun z : Vec d => ?_)
  · simp only [integral_mul_const, Clock.integral_euclideanHeatKernel (by norm_num : (0 : ℝ) < 1),
      one_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (integral_kernel_heat_eq_scaled ht x).symm
  · have ht : Tendsto (fun t : ℝ => Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
    have hx : Tendsto (fun t : ℝ => x - Real.sqrt t • z) (𝓝[>] 0) (𝓝 x) := by
      simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub (ht.smul_const z)
    exact tendsto_const_nhds.mul (hK.continuousAt.tendsto.comp hx)

end EinsteinRelation.Correctors
