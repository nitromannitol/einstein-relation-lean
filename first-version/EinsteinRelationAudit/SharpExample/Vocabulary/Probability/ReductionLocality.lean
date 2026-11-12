import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma

/-! Restated from the library module `EinsteinRelation.Probability.ReductionLocality`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

namespace EinsteinRelation.Probability
/-- The physical-to-reduced map is continuous for locally uniform convergence. -/
theorem continuous_reduce {d : ℕ} : Continuous (reduce (d := d)) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.snd.eval continuous_snd))).smul
        (continuous_fst.fst.eval continuous_snd)
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.snd.eval continuous_snd))
/-- The concrete reduced pair defines a measurable pushforward law. -/
theorem measurable_reduce {d : ℕ} : Measurable (reduce (d := d)) :=
  continuous_reduce.measurable
/-- Stationarity is preserved by the actual pointwise environment reduction. -/
theorem isStationary_map_reduce {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d))
    (hQ : IsStationary Q) : IsStationary (MeasureTheory.Measure.map reduce Q) := by
  intro x
  rw [MeasureTheory.Measure.map_map (measurable_translate x) measurable_reduce]
  change MeasureTheory.Measure.map (reduce ∘ translate x) Q =
    MeasureTheory.Measure.map reduce Q
  rw [← MeasureTheory.Measure.map_map measurable_reduce (measurable_translate x), hQ x]
end EinsteinRelation.Probability
