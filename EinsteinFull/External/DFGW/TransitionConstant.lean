import EinsteinFull.External.DFGW.TransitionOperator

/-! # Constant transition observables

The stationary Markov transition operators preserve constant `L²` observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every constant observable is fixed by every stationary Markov transition operator. -/
theorem transitionOperator_indicator_univ (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hμ : μ Set.univ ≠ ∞) (c : ℝ) (t : ℝ≥0) :
    transitionOperator hP t (indicatorConstLp 2 MeasurableSet.univ hμ c) =
      indicatorConstLp 2 MeasurableSet.univ hμ c := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  let f := indicatorConstLp 2 MeasurableSet.univ hμ c
  have hfc : f =ᵐ[μ] fun _ => c := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hμ) (c := c)] with x hx
    simpa only [Set.indicator_univ] using hx
  have hker := MarkovProcess.kernelIntegral_congr_ae (le_of_eq (kernel_comp_eq hP t)) hfc
  apply Lp.ext
  filter_upwards [transitionOperator_ae_eq hP t f, hfc, hker] with x hx hc hk
  change (transitionOperator hP t f) x = f x
  rw [hx, hc]
  change (∫ y, f y ∂T t x) = ∫ y, c ∂T t x at hk
  rw [hk, integral_const]
  simp

end EinsteinFull.External.DFGW
