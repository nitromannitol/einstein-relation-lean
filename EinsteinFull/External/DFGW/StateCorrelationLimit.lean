import EinsteinFull.External.DFGW.CorrelationMonotone
import EinsteinFull.External.DFGW.StateCorrelationAverage
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Decay of state autocorrelations

Reversibility makes autocorrelations monotone, so the mean ergodic theorem yields convergence
along each positive time grid without averaging.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- State autocorrelations at integer multiples of a positive time converge to the squared mean. -/
theorem tendsto_state_autocorrelation_grid
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => inner ℝ f (transitionOperator hP (n • t) f)) atTop
      (𝓝 ((∫ x, f x ∂μ) * (∫ x, f x ∂μ))) := by
  let a : ℕ → ℝ := fun n => inner ℝ f (transitionOperator hP (n • t) f)
  have ha : Antitone a := by
    intro i j hij
    apply antitone_inner_transitionOperator hP f
    exact nsmul_le_nsmul_left (show 0 ≤ t from bot_le) hij
  have hbound : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact inner_transitionOperator_nonneg hP (n • t) f
  have hlim : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf ha hbound
  have hc := hlim.cesaro
  have havg := tendsto_average_state_correlation hP hμ ht f f
  have heq : (⨅ n, a n) = (∫ x, f x ∂μ) * (∫ x, f x ∂μ) :=
    tendsto_nhds_unique hc havg
  rw [← heq]
  exact hlim

end EinsteinFull.External.DFGW
