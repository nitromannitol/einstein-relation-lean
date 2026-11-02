import EinsteinFull.Frozen.ReducedLaw

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- Translation covariance of the literal time change preserves the actual
stationary law; this supplies the horizontal calculus on reduced pairs. -/
theorem reducedLaw_stationary {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsStationary (reducedLaw Q) := by
  intro x
  rw [reducedLaw, Measure.map_map (Probability.measurable_translate x)
    Probability.measurable_reduce]
  have hcomp : translate x ∘ reduce = reduce ∘ translate x := by
    funext ω
    exact (reduce_translate ω x).symm
  rw [hcomp, ← Measure.map_map Probability.measurable_reduce
    (Probability.measurable_translate x), Q.stationary x]

end EinsteinFull
