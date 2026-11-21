import EinsteinFull.External.DFGW.StateCorrelationLimit

/-! # Mixing of centered state observables

A centered square-integrable state observable is driven to zero in `L²` by positive-time
transition iterates.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A centered state observable converges to zero in `L²` along any positive time grid. -/
theorem tendsto_transitionOperator_grid_of_integral_eq_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f : Lp ℝ 2 μ) (hf : ∫ x, f x ∂μ = 0) :
    Tendsto (fun n : ℕ => transitionOperator hP (n • t) f) atTop (𝓝 0) := by
  have hcorr : Tendsto (fun n : ℕ => inner ℝ f (transitionOperator hP (n • t) f))
      atTop (𝓝 0) := by
    simpa only [hf, zero_mul] using tendsto_state_autocorrelation_grid hP hμ ht f
  have hbound (u : ℝ≥0) : ‖transitionOperator hP u f‖ ^ 2 ≤
      inner ℝ f (transitionOperator hP u f) := by
    have heq : transitionOperator hP u f =
        transitionOperator hP (u / 2) (transitionOperator hP (u / 2) f) := by
      calc
        _ = transitionOperator hP (u / 2 + u / 2) f := by rw [add_halves]
        _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
          (transitionOperator_add hP (u / 2) (u / 2))
    have hinner : inner ℝ f (transitionOperator hP u f) =
        ‖transitionOperator hP (u / 2) f‖ ^ 2 := by
      rw [heq, ← inner_transitionOperator, real_inner_self_eq_norm_sq]
    have hcontract : ‖transitionOperator hP u f‖ ≤ ‖transitionOperator hP (u / 2) f‖ := by
      rw [heq]
      have h₁ := (transitionOperator hP (u / 2)).le_opNorm (transitionOperator hP (u / 2) f)
      have h₂ := norm_transitionOperator_le_one hP (u / 2)
      nlinarith [norm_nonneg (transitionOperator hP (u / 2) f)]
    rw [hinner]
    nlinarith [norm_nonneg (transitionOperator hP u f),
      norm_nonneg (transitionOperator hP (u / 2) f)]
  have hsq : Tendsto (fun n : ℕ => ‖transitionOperator hP (n • t) f‖ ^ 2)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcorr
      (fun n => sq_nonneg _) (fun n => hbound (n • t))
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

end EinsteinFull.External.DFGW
