import EinsteinFull.External.DFGW.FixedObservableEvents
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-! # Ergodic semigroup fixed points

Under state-space ergodicity, the only fixed points of a positive-time transition operator are
constant observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A fixed `L²` observable of an ergodic reversible semigroup is almost everywhere constant. -/
theorem ae_eq_const_of_transitionOperator_fixed
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    {t : ℝ≥0} (ht : 0 < t) (hf : transitionOperator hP t f = f) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g : S → ℝ := (Lp.memLp f).aestronglyMeasurable.mk f
  have hg : Measurable g := (Lp.memLp f).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] g := (Lp.memLp f).aestronglyMeasurable.ae_eq_mk
  let ν : Measure ℝ := μ.map g
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  let : IsZeroOneMeasure ν := ⟨fun {B} hB => by
    rw [Measure.map_apply hg hB]
    exact measure_preimage_eq_zero_or_one_of_fixed hP f ht hf g hg hfg.symm B hB⟩
  obtain ⟨c, hc⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := ν)
  refine ⟨c, ?_⟩
  have he : ∀ᵐ y ∂ν, y = c := by rw [hc]; simp
  have he' : ∀ᵐ x ∂μ, g x = c :=
    (ae_map_iff hg.aemeasurable (measurableSet_eq_fun measurable_id measurable_const)).1 he
  filter_upwards [hfg, he'] with x hx hy
  exact hx.trans hy

end EinsteinFull.External.DFGW
