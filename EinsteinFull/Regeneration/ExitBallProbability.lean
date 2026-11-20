import EinsteinFull.Regeneration.ExitBallExhaustion
import MarkovProcess.Trajectory.ExitLaw
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Exit probabilities under bounded-domain exhaustion

Almost-sure finite exit and path continuity imply convergence of exit-event
probabilities along an exhaustion by intersections with expanding balls.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace EinsteinFull.Regeneration

/-- Paths that exit a domain finitely and land in a prescribed target. -/
def finiteExitEvent {α : Type*} [PseudoMetricSpace α]
    (U B : Set α) : Set (MarkovProcess.ContinuousPath α) :=
  {γ | MarkovProcess.ContinuousPath.exitTime U γ < ⊤ ∧
    γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) ∈ B}

/-- Finite exit events are measurable for open domains and measurable targets. -/
theorem measurableSet_finiteExitEvent {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (U B : Set α) (hU : IsOpen U) (hB : MeasurableSet B) :
    MeasurableSet (finiteExitEvent U B) := by
  exact (MarkovProcess.ContinuousPath.measurableSet_exitTime_lt_top U hU).inter
    ((MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU) hB)

/-- Exit-event measures converge along bounded-domain exhaustion. -/
theorem tendsto_finiteExitEvent_ball (α : Type*) [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure (MarkovProcess.ContinuousPath α))
    [IsFiniteMeasure μ] (U B : Set α) (hU : IsOpen U) (hB : MeasurableSet B) (x : α)
    (hfin : ∀ᵐ γ ∂μ, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    Tendsto (fun n : ℕ => μ (finiteExitEvent (U ∩ Metric.ball x n) B)) atTop
      (𝓝 (μ (finiteExitEvent U B))) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_finiteExitEvent U B hU hB)
    (fun n : ℕ => measurableSet_finiteExitEvent (U ∩ Metric.ball x n) B (hU.inter Metric.isOpen_ball) hB)
  filter_upwards [hfin] with γ hγ
  obtain ⟨R₀, _, hR⟩ := exists_ball_exitTime_eq U γ x hγ
  obtain ⟨N, hN⟩ := exists_nat_gt R₀
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : R₀ ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
  have heq := hR n hle
  change (MarkovProcess.ContinuousPath.exitTime (U ∩ Metric.ball x n) γ < ⊤ ∧
    γ ((MarkovProcess.ContinuousPath.exitTimeTop (U ∩ Metric.ball x n) γ).untopD 0) ∈ B) ↔
      (MarkovProcess.ContinuousPath.exitTime U γ < ⊤ ∧
    γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0) ∈ B)
  rw [MarkovProcess.ContinuousPath.exitTimeTop_apply,
    MarkovProcess.ContinuousPath.exitTimeTop_apply, heq]

/-- Bounded measurable exit payoffs converge along bounded-domain exhaustion. -/
theorem tendsto_integral_exitPayoff_ball (α : Type*) [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure (MarkovProcess.ContinuousPath α))
    [IsFiniteMeasure μ] (U : Set α) (hU : IsOpen U) (x : α) (f : α → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C)
    (hfin : ∀ᵐ γ ∂μ, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop
      (U ∩ Metric.ball x n) γ).untopD 0)) ∂μ) atTop
      (𝓝 (∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact (hf.comp (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop
      (U ∩ Metric.ball x n) (hU.inter Metric.isOpen_ball))).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact Filter.Eventually.of_forall fun γ => hC _
  · filter_upwards [hfin] with γ hγ
    obtain ⟨R₀, _, hR⟩ := exists_ball_exitTime_eq U γ x hγ
    obtain ⟨N, hN⟩ := exists_nat_gt R₀
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : R₀ ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
    have heq := hR n hle
    rw [MarkovProcess.ContinuousPath.exitTimeTop_apply,
      MarkovProcess.ContinuousPath.exitTimeTop_apply, heq]

end EinsteinFull.Regeneration
