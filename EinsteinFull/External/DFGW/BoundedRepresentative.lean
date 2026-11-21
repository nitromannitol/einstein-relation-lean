import EinsteinFull.External.DFGW.BoundedResolvent

/-! # Bounded representatives of resolvents

An essentially bounded `L²` function has a bounded measurable representative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

omit [TopologicalSpace S] [BorelSpace S] in
/-- An essentially bounded `L²` vector has a bounded measurable representative. -/
theorem exists_bounded_measurable_rep (f : Lp ℝ 2 μ) (C : ℝ)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ∃ g : S → ℝ, Measurable g ∧ (∃ B, ∀ x, |g x| ≤ B) ∧
      ∃ hg : MemLp g 2 μ, hg.toLp g = f := by
  let B := max C 0
  let g : S → ℝ := fun x => max (-B) (min B (f x))
  have hB : 0 ≤ B := le_max_right C 0
  have hg : Measurable g := measurable_const.max (measurable_const.min (Lp.stronglyMeasurable f).measurable)
  have hgf : g =ᵐ[μ] f := by
    filter_upwards [hf] with x hx
    have hb : |f x| ≤ B := (by simpa only [Real.norm_eq_abs] using hx : |f x| ≤ C).trans (le_max_left _ _)
    have hh := abs_le.mp hb
    change max (-B) (min B (f x)) = f x
    rw [min_eq_right hh.2, max_eq_right hh.1]
  have hL2 : MemLp g 2 μ := (Lp.memLp f).ae_eq hgf.symm
  refine ⟨g, hg, ⟨B, ?_⟩, hL2, ?_⟩
  · intro x
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (neg_le_self hB) (min_le_left _ _)
  · apply Lp.ext
    exact (MemLp.coeFn_toLp hL2).trans hgf

end EinsteinFull.External.DFGW
