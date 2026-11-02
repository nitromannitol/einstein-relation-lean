import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.FiniteHistoryFiltration
import EinsteinRelation.Probability.PathMaps

/-! # One-interval observations of the coupled sample

Source `paper/main.tex:272,377–378`. The observation retains the complete
continuous segment on one grid interval and its success bit. The segment
is extended constantly after its right endpoint.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinRelation.Regeneration

/-- The continuous segment on grid interval `n`, extended constantly. -/
def intervalPath {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (γ : Path d) : Path d :=
  ⟨fun t => γ ((n : ℝ≥0) * Δ + min t Δ),
    γ.continuous.comp (continuous_const.add (continuous_id.min continuous_const))⟩

@[simp] theorem intervalPath_apply {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (γ : Path d) (t : ℝ≥0) :
    intervalPath Δ n γ t = γ ((n : ℝ≥0) * Δ + min t Δ) := rfl

/-- One interval of the path and the single bit attached to that interval. -/
def intervalObservation {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d) :
    Path d × Bool := (intervalPath Δ n z.1, z.2 n)

/-- The one-interval path observation is continuous in the original path. -/
theorem continuous_intervalPath {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Continuous (intervalPath (d := d) Δ n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.eval (continuous_const.add (continuous_snd.min continuous_const))

/-- The segment and success-bit observation is measurable on the coupled space. -/
theorem measurable_intervalObservation {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (intervalObservation (d := d) Δ n) :=
  ((continuous_intervalPath Δ n).measurable.comp measurable_fst).prodMk
    ((measurable_pi_apply n).comp measurable_snd)

end EinsteinRelation.Regeneration
