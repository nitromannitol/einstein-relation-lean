import MarkovProcess.Trajectory.ExitLaw

/-!
# Bounds and boundary values for exit payoffs

The expectation of a unit-interval payoff stays in the unit interval. A
process started outside the domain exits immediately and returns the payoff
at its starting point.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace EinsteinFull.Regeneration

/-- A bounded measurable payoff of an open-domain exit is integrable. -/
theorem integrable_exitPayoff {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (P : Measure (MarkovProcess.ContinuousPath α))
    [IsProbabilityMeasure P] (U : Set α) (hU : IsOpen U) (f : α → ℝ)
    (hf : Measurable f) (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1) :
    Integrable (fun γ => f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))) P := by
  apply Integrable.of_bound
    (hf.comp (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU)).aestronglyMeasurable 1
  filter_upwards with γ
  change ‖f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (hzero _)]
  exact hone _

/-- The expected exit payoff is in the unit interval. -/
theorem integral_exitPayoff_mem_Icc {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (P : Measure (MarkovProcess.ContinuousPath α))
    [IsProbabilityMeasure P] (U : Set α) (hU : IsOpen U) (f : α → ℝ)
    (hf : Measurable f) (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1) :
    (∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂P) ∈ Icc (0 : ℝ) 1 := by
  have hint := integrable_exitPayoff P U hU f hf hzero hone
  constructor
  · exact integral_nonneg fun γ => hzero _
  · have h := integral_mono_ae hint (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun γ => hone (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)))
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] using h

/-- When the start lies outside the domain, the expected exit payoff equals its value there. -/
theorem integral_exitPayoff_of_notMem {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (P : Measure (MarkovProcess.ContinuousPath α))
    [IsProbabilityMeasure P] (U : Set α) (x : α) (hx : x ∉ U) (f : α → ℝ)
    (hstart : ∀ᵐ γ ∂P, γ 0 = x) :
    (∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂P) = f x := by
  have heq : ∀ᵐ γ ∂P, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) = f x := by
    filter_upwards [hstart] with γ hγ
    have hnot : γ 0 ∉ U := hγ ▸ hx
    have htime : MarkovProcess.ContinuousPath.exitTime U γ = 0 :=
      le_antisymm (MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ 0 hnot) bot_le
    rw [MarkovProcess.ContinuousPath.exitTimeTop_apply, htime]
    change f (γ 0) = f x
    rw [hγ]
  rw [integral_congr_ae heq]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]

end EinsteinFull.Regeneration
