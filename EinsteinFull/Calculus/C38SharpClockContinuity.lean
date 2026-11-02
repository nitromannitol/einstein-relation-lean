import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open EinsteinRelation EinsteinRelation.Sharpness MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace EinsteinFull.Blueprint

/-- Quantitative transfer from the coefficient average error to the normalized
sharp velocity error, with the signed force retained. -/
theorem sharp_velocity_quadratic_error_of_average_error
    {d : ℕ} (i : Fin d) (lam η avg m E : ℝ) (hlam : lam ≠ 0)
    (hη : (1/2 : ℝ) ≤ η) (hE : 0 ≤ E)
    (hclock : η = 1-EinsteinFull.Work.W8.clockParameter i*lam*(avg-1))
    (havg : |avg-m| ≤ E) :
    |(lam/η-lam)/lam^2-EinsteinFull.Work.W8.clockParameter i*(m-1)|
    ≤ 2*EinsteinFull.Work.W8.clockParameter i*E+
      2*(EinsteinFull.Work.W8.clockParameter i)^2* |m-1| * |lam| * |avg-1| := by
  let δ := EinsteinFull.Work.W8.clockParameter i
  have hδ : 0 < δ := EinsteinFull.Work.W8.clockParameter_pos i
  have hηpos : 0 < η := by linarith
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hinv : 1 / η ≤ 2 := by
    apply (div_le_iff₀ hηpos).2
    linarith
  have hid : (lam/η-lam)/lam^2-δ*(m-1) =
      δ*(avg-m)/η + δ*(m-1)*(δ*lam*(avg-1))/η := by
    have hc : η = 1-δ*lam*(avg-1) := hclock
    field_simp [hlam, hηne]
    rw [hc]
    ring
  have hfirst : |δ*(avg-m)/η| ≤ 2*δ*E := by
    rw [abs_div, abs_mul, abs_of_pos hδ, abs_of_pos hηpos, div_eq_mul_inv]
    have hi : η⁻¹ ≤ 2 := by simpa [one_div] using hinv
    calc
      δ * |avg - m| * η⁻¹ ≤ δ * E * 2 := by
        gcongr
      _ = 2 * δ * E := by ring
  have hsecond : |δ*(m-1)*(δ*lam*(avg-1))/η| ≤
      2*δ^2* |m-1| * |lam| * |avg-1| := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_pos hδ, abs_of_pos hηpos, div_eq_mul_inv]
    have hi : η⁻¹ ≤ 2 := by simpa [one_div] using hinv
    calc
      δ * |m - 1| * (δ * |lam| * |avg - 1|) * η⁻¹ ≤
          δ * |m - 1| * (δ * |lam| * |avg - 1|) * 2 := by
        gcongr
      _ = 2*δ^2* |m-1| * |lam| * |avg-1| := by ring
  change |(lam/η-lam)/lam^2-δ*(m-1)| ≤ _
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)


/-- Explicit power-rate transfer for the sharp quadratic velocity response. -/
theorem sharp_velocity_quadratic_power_error
    {d : ℕ} (i : Fin d) (lam avg m C B α : ℝ) (hlam : lam ≠ 0)
    (hC : 0 ≤ C)
    (havg : |avg-m| ≤ C* |lam|^α) (havgB : |avg-1| ≤ B)
    (hsmall : EinsteinFull.Work.W8.clockParameter i* |lam| *B ≤ (1/2 : ℝ)) :
    |(lam/(1-EinsteinFull.Work.W8.clockParameter i*lam*(avg-1))-lam)/lam^2-
       EinsteinFull.Work.W8.clockParameter i*(m-1)|
    ≤ 2*EinsteinFull.Work.W8.clockParameter i*C* |lam|^α+
      2*(EinsteinFull.Work.W8.clockParameter i)^2* |m-1| *B* |lam| := by
  let δ := EinsteinFull.Work.W8.clockParameter i
  have hδ : 0 < δ := EinsteinFull.Work.W8.clockParameter_pos i
  have habs : |δ*lam*(avg-1)| ≤ δ* |lam| *B := by
    rw [abs_mul, abs_mul, abs_of_pos hδ]
    gcongr
  have hη : (1/2 : ℝ) ≤ 1-δ*lam*(avg-1) := by
    have hle := le_abs_self (δ*lam*(avg-1))
    linarith
  have hE : 0 ≤ C* |lam|^α := mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
  have h := sharp_velocity_quadratic_error_of_average_error i lam
    (1-δ*lam*(avg-1)) avg m (C* |lam|^α) hlam hη hE rfl havg
  calc
    _ ≤ 2*δ*(C* |lam|^α) + 2*δ^2* |m-1| * |lam| * |avg-1| := h
    _ ≤ 2*δ*C* |lam|^α + 2*δ^2* |m-1| *B* |lam| := by
      have hb : 2*δ^2* |m-1| * |lam| * |avg-1| ≤
          2*δ^2* |m-1| * |lam| *B := by
        gcongr
      nlinarith

/-- A convergent coefficient average yields the right quadratic response. -/
theorem sharp_right_quadratic_response_of_average_limit
    {d : ℕ} (i : Fin d) (avg : ℝ → ℝ) (m : ℝ)
    (havg : Tendsto avg (𝓝[>] (0 : ℝ)) (𝓝 m)) :
    Tendsto (fun lam : ℝ =>
      (lam/(1-EinsteinFull.Work.W8.clockParameter i*lam*(avg lam-1))-lam)/lam^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (EinsteinFull.Work.W8.clockParameter i*(m-1))) := by
  let δ := EinsteinFull.Work.W8.clockParameter i
  have harg : Tendsto (fun lam : ℝ => avg lam - 1) (𝓝[>] (0 : ℝ)) (𝓝 (m - 1)) :=
    havg.sub tendsto_const_nhds
  have hlam : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun lam : ℝ => 1 - δ * lam * (avg lam - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul hlam).mul harg)
  have hquot : Tendsto (fun lam : ℝ => δ * (avg lam - 1) /
      (1 - δ * lam * (avg lam - 1))) (𝓝[>] (0 : ℝ)) (𝓝 (δ * (m - 1))) := by
    change Tendsto ((fun lam : ℝ => δ * (avg lam - 1)) /
      (fun lam : ℝ => 1 - δ * lam * (avg lam - 1))) _ _
    simpa only [div_one] using
      (tendsto_const_nhds.mul harg).div hden (one_ne_zero : (1 : ℝ) ≠ 0)
  apply hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0))] with lam hlampos hne
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  let η := 1 - δ * lam * (avg lam - 1)
  have hηne : η ≠ 0 := hne
  change δ * (avg lam - 1) / η = (lam / η - lam) / lam^2
  field_simp [hlamne, hηne]
  dsimp only [η]
  ring


/-- A two-sided convergent coefficient average yields the signed quadratic response. -/
theorem sharp_signed_quadratic_response_of_average_limit
    {d : ℕ} (i : Fin d) (avg : ℝ → ℝ) (m : ℝ)
    (havg : Tendsto avg (𝓝 (0 : ℝ)) (𝓝 m)) :
    Tendsto (fun lam : ℝ =>
      (lam/(1-EinsteinFull.Work.W8.clockParameter i*lam*(avg lam-1))-lam)/lam^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (EinsteinFull.Work.W8.clockParameter i*(m-1))) := by
  let δ := EinsteinFull.Work.W8.clockParameter i
  have harg : Tendsto (fun lam : ℝ => avg lam - 1) (𝓝[≠] (0 : ℝ)) (𝓝 (m - 1)) :=
    (havg.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds
  have hlam : Tendsto (fun lam : ℝ => lam) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun lam : ℝ => 1 - δ * lam * (avg lam - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul hlam).mul harg)
  have hquot : Tendsto (fun lam : ℝ => δ * (avg lam - 1) /
      (1 - δ * lam * (avg lam - 1))) (𝓝[≠] (0 : ℝ)) (𝓝 (δ * (m - 1))) := by
    change Tendsto ((fun lam : ℝ => δ * (avg lam - 1)) /
      (fun lam : ℝ => 1 - δ * lam * (avg lam - 1))) _ _
    simpa only [div_one] using
      (tendsto_const_nhds.mul harg).div hden (one_ne_zero : (1 : ℝ) ≠ 0)
  apply hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0))] with lam hlamne hne
  have hlamne' : lam ≠ 0 := by simpa using hlamne
  let η := 1 - δ * lam * (avg lam - 1)
  have hηne : η ≠ 0 := hne
  change δ * (avg lam - 1) / η = (lam / η - lam) / lam^2
  field_simp [hlamne', hηne]
  dsimp only [η]
  ring


/-- The absolute quadratic response holds for forces approaching zero from either side. -/
theorem sharp_signed_absolute_quadratic_response_of_average_limit
    {d : ℕ} (i : Fin d) (avg : ℝ → ℝ) (m : ℝ)
    (havg : Tendsto avg (𝓝 (0 : ℝ)) (𝓝 m)) :
    Tendsto (fun lam : ℝ =>
      |lam/(1-EinsteinFull.Work.W8.clockParameter i*lam*(avg lam-1))-lam|/lam^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (EinsteinFull.Work.W8.clockParameter i*|m-1|)) := by
  have h := (sharp_signed_quadratic_response_of_average_limit i avg m havg).abs
  simpa only [abs_div, abs_sq, abs_mul,
    abs_of_pos (EinsteinFull.Work.W8.clockParameter_pos i)] using h

/-- The actual finite-time reduced coefficient average varies continuously with the path. -/
theorem sharp_finite_time_coefficient_average_continuous
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (T : ℝ≥0) :
    Continuous (fun γ : EinsteinRelation.Path d => (T : ℝ)⁻¹ *
      ∫ u in (0 : ℝ)..(T : ℝ),
        reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i) := by
  have hj (x : Vec d) : jacobianFactor i (gradient (EinsteinFull.Work.W8.corrector W) x) ≠ 0 := by
    have hb := (jacobianFactor_bounds i _ (EinsteinFull.Work.W8.corrector_gradient_bound W x)).1
    have hp : 0 < jacobianFactor i (gradient (EinsteinFull.Work.W8.corrector W) x) := by linarith
    exact hp.ne'
  have hc : Continuous (fun x : Vec d =>
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i) := by
    have h := continuous_coefficientField i (EinsteinFull.Work.W8.corrector W)
      (EinsteinFull.Work.W8.corrector_contDiff W) hj
    have hentry : Continuous (fun x : Vec d =>
        coefficientField i (EinsteinFull.Work.W8.corrector W) x i i) :=
      (continuous_apply i).comp ((continuous_apply i).comp h)
    simpa only [EinsteinFull.Work.W8.physicalPair_reducedCoefficient] using hentry
  apply Continuous.const_mul
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => (3 : ℝ))
  · intro γ
    exact (hc.comp (γ.continuous.comp continuous_real_toNNReal)).aestronglyMeasurable
  · intro γ
    filter_upwards with u hu
    simpa only [Real.norm_eq_abs] using
      (EinsteinRelation.Correctors.IsElliptic.entry_abs_le (by norm_num : (0 : ℝ) < 3)
        (EinsteinFull.Work.W8.reducedCoefficient_isElliptic i W) (γ u.toNNReal) i i)
  · exact intervalIntegrable_const
  · filter_upwards with u hu
    exact hc.comp (continuous_eval_const u.toNNReal)

/-- The actual finite-time reduced coefficient average is bounded by the ellipticity
constant, uniformly in the noise sample and the path. -/
theorem sharp_finite_time_coefficient_average_abs_le
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (γ : Path d) (T : ℝ≥0) :
    |(T : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(T : ℝ),
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i| ≤ 3 := by
  have hint : ‖∫ u in (0 : ℝ)..(T : ℝ),
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i‖
      ≤ 3 * |(T : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u _
    simpa only [Real.norm_eq_abs] using
      (EinsteinRelation.Correctors.IsElliptic.entry_abs_le (by norm_num : (0 : ℝ) < 3)
        (EinsteinFull.Work.W8.reducedCoefficient_isElliptic i W) (γ u.toNNReal) i i)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg T.coe_nonneg] at hint
  rw [abs_mul, abs_inv, abs_of_nonneg T.coe_nonneg]
  rcases eq_or_ne (T : ℝ) 0 with h0 | h0
  · rw [h0]; norm_num
  · have hT : 0 < (T : ℝ) := lt_of_le_of_ne T.coe_nonneg (Ne.symm h0)
    rw [inv_mul_le_iff₀ hT]
    linarith

/-- Any limit of the actual reduced coefficient averages along the path is bounded by the
ellipticity constant; existence of the limit is not asserted. -/
theorem sharp_coefficient_average_limit_abs_le_three
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (γ : Path d) (avg : ℝ)
    (havg : Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W)
        (γ u.toNNReal) i i) atTop (𝓝 avg)) : |avg| ≤ 3 := by
  refine le_of_tendsto havg.abs ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := sharp_finite_time_coefficient_average_abs_le i W γ t.toNNReal
  rwa [Real.coe_toNNReal t ht] at h

end EinsteinFull.Blueprint
