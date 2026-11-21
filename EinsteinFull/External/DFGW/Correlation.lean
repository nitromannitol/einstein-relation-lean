import EinsteinFull.External.DFGW.Semigroup

/-! # Mixed correlations

Diagonal correlation integrability controls all mixed correlations by positivity of the
reversible semigroup.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Diagonal correlation integrability implies absolute integrability of the mixed correlation. -/
theorem integrableOn_mixed_correlation (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : Lp ℝ 2 μ)
    (hf : IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal f))
      (Set.Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => inner ℝ g (transitionOperator hP t.toNNReal g))
      (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal g)) (Set.Ioi 0) := by
  have hcont : Continuous (fun t : ℝ => inner ℝ f (transitionOperator hP t.toNNReal g)) := by
    change Continuous (fun t : ℝ => inner ℝ f (transitionSemigroup hP t.toNNReal g))
    exact continuous_const.inner (((transitionSemigroup hP).continuous_orbit g).comp
      continuous_real_toNNReal)
  have hmajor : IntegrableOn (fun t : ℝ =>
      (inner ℝ f (transitionOperator hP t.toNNReal f) +
        inner ℝ g (transitionOperator hP t.toNNReal g)) / 2) (Set.Ioi 0) :=
    (hf.add hg).div_const 2
  refine hmajor.mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using abs_inner_transitionOperator_le hP t.toNNReal f g

end EinsteinFull.External.DFGW
