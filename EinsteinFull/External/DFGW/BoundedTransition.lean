import EinsteinFull.External.DFGW.Semigroup

/-! # Preservation of bounded observables

The Markov transition semigroup preserves almost-everywhere bounds on observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A Markov transition preserves an almost-everywhere bound. -/
theorem transitionSemigroup_ae_norm_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) (C : ℝ) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖transitionSemigroup hP t f x‖ ≤ C := by
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  have hker := MarkovProcess.ae_ae_kernel_of_comp_le (le_of_eq (kernel_comp_eq hP t)) hf
  filter_upwards [transitionSemigroup_ae_eq hP t f, hker] with x heq hx
  rw [heq]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using norm_integral_le_of_norm_le_const hx

end EinsteinFull.External.DFGW
