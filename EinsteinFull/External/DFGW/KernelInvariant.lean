import EinsteinFull.External.DFGW.KernelSymmetry
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Invariance of the stationary marginal

The Markov transition kernel preserves the expectation of every bounded measurable observable.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The invariant marginal integrates a bounded observable identically before and after transition. -/
theorem integral_kernel_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) (t : ℝ≥0) :
    (∫ x, ∫ y, f y ∂T t x ∂μ) = ∫ x, f x ∂μ := by
  have h := integral_kernel_mul_eq_correlation hP f (fun _ => 1) hf measurable_const hfb
    ⟨1, fun _ => by norm_num⟩ t
  simp only [mul_one] at h
  have hm := integral_map (μ := P) (continuous_eval_const (t : ℝ)).measurable.aemeasurable
    (f := f) (by rw [hP.marginal]; exact hf.aestronglyMeasurable)
  rw [hP.marginal] at hm
  exact h.trans hm.symm

/-- The transition kernel preserves the stationary marginal as a measure. -/
theorem kernel_comp_eq (hP : Draft.IsDFGWTrajectoryProcess P μ T) (t : ℝ≥0) :
    T t ∘ₘ μ = μ := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let : IsMarkovKernel (T t) := hP.markov_kernel t
  ext A hA
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.1
  have h := integral_kernel_eq hP (A.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hA) ⟨1, fun x => by
      by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]⟩ t
  simp_rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def] at h
  rw [Measure.bind_apply hA (T t).aemeasurable]
  rw [← integral_toReal ((T t).measurable_coe hA).aemeasurable
    (ae_of_all μ fun x => measure_lt_top (T t x) A)]
  exact h

end EinsteinFull.External.DFGW
