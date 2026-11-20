import EinsteinFull.External.DFGW.IntegralCauchy

/-! # Variance under sublinear mean-square approximation

A process whose mean-square distance from a linear-variance process is `o(t)` has the same
asymptotic variance rate.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A sublinear mean-square approximation preserves the normalized variance limit. -/
theorem tendsto_variance_of_sublinear_approximation
    (A M : ℝ≥0 → Ω → ℝ) (hA : ∀ t, MemLp (A t) 2 P) (hM : ∀ t, MemLp (M t) 2 P)
    (c : ℝ) (hc : 0 ≤ c)
    (hvar : ∀ t, (∫ ω, M t ω ^ 2 ∂P) = (t : ℝ) * c)
    (hrem : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
      ∫ ω, (A t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ ω, A t ω ^ 2 ∂P) atTop (𝓝 c) := by
  let E : ℝ≥0 → ℝ := fun t => (t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) ^ 2 ∂P
  let C : ℝ≥0 → ℝ := fun t => (t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) * M t ω ∂P
  have hE : Tendsto E atTop (𝓝 0) := hrem
  have hC2 : Tendsto (fun t => C t ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun t => sq_nonneg (C t)) ?_
      (by simpa only [zero_mul] using hE.mul_const c)
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have htR : 0 < (t : ℝ) := by exact_mod_cast ht
    have hcs := integral_mul_sq_le (fun ω => A t ω - M t ω) (M t) ((hA t).sub (hM t)) (hM t)
    rw [hvar t] at hcs
    have hs := mul_le_mul_of_nonneg_left hcs (sq_nonneg ((t : ℝ)⁻¹))
    change ((t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) * M t ω ∂P) ^ 2 ≤
      ((t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) ^ 2 ∂P) * c
    have hid : ((t : ℝ)⁻¹) ^ 2 * ((∫ ω, (A t ω - M t ω) ^ 2 ∂P) * ((t : ℝ) * c)) =
        ((t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) ^ 2 ∂P) * c := by
      field_simp
    calc
      _ = ((t : ℝ)⁻¹) ^ 2 * (∫ ω, (A t ω - M t ω) * M t ω ∂P) ^ 2 := by ring
      _ ≤ _ := hs
      _ = _ := hid
  have hC : Tendsto C atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hC2
    change Tendsto (fun t => Real.sqrt (C t ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simp_rw [Real.sqrt_sq_eq_abs, ← Real.norm_eq_abs, Real.sqrt_zero] at h
    exact h
  have htotal : Tendsto (fun t => c + E t + 2 * C t) atTop (𝓝 c) := by
    simpa only [add_zero, mul_zero] using (tendsto_const_nhds.add hE).add (hC.const_mul 2)
  apply htotal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hr : MemLp (fun ω => A t ω - M t ω) 2 P := (hA t).sub (hM t)
  have hsq : (fun ω => A t ω ^ 2) =
      fun ω => ((A t ω - M t ω) ^ 2 + M t ω ^ 2) + 2 * ((A t ω - M t ω) * M t ω) := by
    funext ω
    ring
  have hsum : Integrable (fun ω => (A t ω - M t ω) ^ 2 + M t ω ^ 2) P :=
    hr.integrable_sq.add (hM t).integrable_sq
  have hcross : Integrable (fun ω => 2 * ((A t ω - M t ω) * M t ω)) P :=
    (hr.integrable_mul (hM t)).const_mul 2
  have hidentity : (∫ ω, A t ω ^ 2 ∂P) = (∫ ω, (A t ω - M t ω) ^ 2 ∂P) +
      (∫ ω, M t ω ^ 2 ∂P) + 2 * ∫ ω, (A t ω - M t ω) * M t ω ∂P := by
    rw [hsq, integral_add hsum hcross, integral_add hr.integrable_sq (hM t).integrable_sq,
      integral_const_mul]
  change c + (t : ℝ)⁻¹ * (∫ ω, (A t ω - M t ω) ^ 2 ∂P) +
    2 * ((t : ℝ)⁻¹ * ∫ ω, (A t ω - M t ω) * M t ω ∂P) =
    (t : ℝ)⁻¹ * ∫ ω, A t ω ^ 2 ∂P
  rw [hidentity, hvar t]
  field_simp
  ring

end EinsteinFull.External.DFGW
