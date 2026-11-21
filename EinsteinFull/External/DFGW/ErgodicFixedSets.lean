import EinsteinFull.External.DFGW.SemigroupFixedPoints

/-! # Ergodic fixed sets

The state-space ergodicity assumption forces measurable sets whose indicator is fixed by one
positive-time transition operator to have probability zero or one.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A measurable set whose indicator is fixed at a positive time has measure zero or one. -/
theorem measure_eq_zero_or_one_of_indicator_fixed
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) {A : Set S} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) {t : ℝ≥0} (ht : 0 < t)
    (hf : transitionOperator hP t
      (indicatorConstLp 2 hA hμA (1 : ℝ)) =
        indicatorConstLp 2 hA hμA (1 : ℝ)) :
    μ A = 0 ∨ μ A = 1 := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let f := indicatorConstLp 2 hA hμA (1 : ℝ)
  apply hP.ergodic A hA
  intro u
  let : IsMarkovKernel (T u) := hP.markov_kernel u
  have hfix : transitionOperator hP u f = f :=
    transitionOperator_fixed_of_pos hP ht f hf u
  have hker := MarkovProcess.kernelIntegral_congr_ae (le_of_eq (kernel_comp_eq hP u))
    (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA)
      (c := (1 : ℝ)))
  filter_upwards [transitionOperator_ae_eq hP u f, indicatorConstLp_coeFn
    (p := 2) (hs := hA) (hμs := hμA) (c := (1 : ℝ)), hker] with x hx hi hk hxA
  have heq : (T u x A).toReal = 1 := by
    have hx' : f x = ∫ y, f y ∂T u x := by simpa only [hfix] using hx
    have hv : f x = 1 := by simpa only [f, Set.indicator_of_mem hxA] using hi
    rw [hv] at hx'
    change (∫ y, f y ∂T u x) = ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂T u x at hk
    rw [hk, integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one] at hx'
    exact hx'.symm
  exact ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top |>.1 (by simpa using heq)

end EinsteinFull.External.DFGW
