import EinsteinFull.External.DFGW.Positive

/-! # Strong continuity from correlations

For a contraction semigroup on a real Hilbert space, convergence of the autocorrelation at
zero implies strong continuity of that orbit at zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Convergence of an autocorrelation at zero implies strong continuity of its orbit. -/
theorem tendsto_transitionOperator_of_correlation (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ)
    (h : Tendsto (fun t : ℝ≥0 => inner ℝ f (transitionOperator hP t f)) (𝓝 0)
      (𝓝 (‖f‖ ^ 2))) :
    Tendsto (fun t : ℝ≥0 => transitionOperator hP t f) (𝓝 0) (𝓝 f) := by
  have hupper : Tendsto (fun t : ℝ≥0 => 2 *
      (‖f‖ ^ 2 - inner ℝ f (transitionOperator hP t f))) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ≥0 => ‖f‖ ^ 2) (𝓝 0) (𝓝 (‖f‖ ^ 2)) := tendsto_const_nhds
    simpa only [sub_self, mul_zero] using (hc.sub h).const_mul 2
  have hsq : Tendsto (fun t : ℝ≥0 => ‖transitionOperator hP t f - f‖ ^ 2) (𝓝 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun t => sq_nonneg _) ?_
    intro t
    have hnorm : ‖transitionOperator hP t f‖ ≤ ‖f‖ := by
      have h₁ := (transitionOperator hP t).le_opNorm f
      have h₂ := norm_transitionOperator_le_one hP t
      nlinarith [mul_le_mul_of_nonneg_right h₂ (norm_nonneg f)]
    change ‖transitionOperator hP t f - f‖ ^ 2 ≤
      2 * (‖f‖ ^ 2 - inner ℝ f (transitionOperator hP t f))
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [sq_nonneg (‖f‖ - ‖transitionOperator hP t f‖), norm_nonneg f,
      norm_nonneg (transitionOperator hP t f)]
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end EinsteinFull.External.DFGW
