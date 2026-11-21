import EinsteinFull.Regeneration.ExitBallProbability

/-!
# Discounted exit payoffs

For bounded payoffs, expectations of the finite-exit payoff converge to the
undiscounted expectation as a nonnegative discount tends to zero.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace EinsteinFull.Regeneration

/-- Discounted finite-exit payoff integrals converge as the discount vanishes. -/
theorem tendsto_discounted_exitPayoff
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (P : Measure (MarkovProcess.ContinuousPath α)) [IsFiniteMeasure P]
    (U : Set α) (hU : IsOpen U) (f : α → ℝ) (hf : Measurable f)
    (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ γ,
      {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => Real.exp (-(a n * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) *
          f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂P) atTop
      (𝓝 (∫ γ, {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}.indicator
        (fun γ => f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) γ ∂P)) := by
  let E : Set (MarkovProcess.ContinuousPath α) :=
    {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤}
  let τ : MarkovProcess.ContinuousPath α → ℝ :=
    fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal
  let F : MarkovProcess.ContinuousPath α → ℝ :=
    fun γ => f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))
  have hE : MeasurableSet E := MarkovProcess.ContinuousPath.measurableSet_exitTime_lt_top U hU
  have hτ : Measurable τ := ENNReal.measurable_toReal.comp
    (MarkovProcess.ContinuousPath.measurable_exitTime U hU)
  have hF : Measurable F := hf.comp
    (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU)
  have hF0 : ∀ γ, 0 ≤ F γ := fun γ => hzero _
  have hF1 : ∀ γ, F γ ≤ 1 := fun γ => hone _
  change Tendsto (fun n : ℕ => ∫ γ, E.indicator (fun γ => Real.exp (-(a n * τ γ)) * F γ) γ ∂P)
    atTop (𝓝 (∫ γ, E.indicator F γ ∂P))
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (((Real.measurable_exp.comp ((measurable_const.mul hτ).neg)).mul hF).indicator hE).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards with γ
    by_cases hγ : γ ∈ E
    · rw [Set.indicator_of_mem hγ, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (hF0 γ))]
      have hw : Real.exp (-(a n * τ γ)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (mul_nonneg (ha n) ENNReal.toReal_nonneg)
      exact (mul_le_mul_of_nonneg_right hw (hF0 γ)).trans (by simpa only [one_mul] using hF1 γ)
    · simp only [Set.indicator_of_notMem hγ, norm_zero, zero_le_one]
  · filter_upwards with γ
    by_cases hγ : γ ∈ E
    · simp only [Set.indicator_of_mem hγ]
      have hw : Tendsto (fun n => Real.exp (-(a n * τ γ))) atTop (𝓝 1) := by
        have h : Tendsto (fun n => -(a n * τ γ)) atTop (𝓝 0) := by
          simpa only [zero_mul, neg_zero] using (ha0.mul_const (τ γ)).neg
        simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h
      simpa only [one_mul] using hw.mul_const (F γ)
    · simp only [Set.indicator_of_notMem hγ]
      exact tendsto_const_nhds

end EinsteinFull.Regeneration
