import EinsteinFull.Regeneration.CappedSlabExitMeasurability

/-!
# Normalized capped slab increments

The actual capped slab displacements are measurable, bounded by one, and
sum to the total displacement along the capped clock.
-/

open Filter Set MeasureTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The normalized force-coordinate displacement over one capped slab step. -/
noncomputable def cappedSlabIncrement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) (n : ℕ) : ℝ :=
  (γ (cappedSlabExitTime γ i r g (n + 1)) i - γ (cappedSlabExitTime γ i r g n) i) / r

/-- Each actual normalized capped slab increment is measurable. -/
theorem measurable_cappedSlabIncrement {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) (n : ℕ) :
    Measurable (fun γ : Path d => cappedSlabIncrement γ i r g n) := by
  have heval (k : ℕ) : Measurable (fun γ : Path d => γ (cappedSlabExitTime γ i r g k) i) :=
    (measurable_pi_apply i).comp (continuous_eval.measurable.comp
      (measurable_id.prodMk (measurable_cappedSlabExitTime i r g k)))
  exact ((heval (n + 1)).sub (heval n)).div_const r

/-- Normalized capped slab increments stay between minus one and one. -/
theorem cappedSlabIncrement_mem_Icc {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    cappedSlabIncrement γ i r g n ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_le.mp (capped_slab_exit_step_bound γ i r hr g n)
  constructor
  · apply (le_div_iff₀ hr).2
    nlinarith [h.1]
  · apply (div_le_iff₀ hr).2
    nlinarith [h.2]

/-- Summing the actual normalized increments recovers the coordinate displacement. -/
theorem sum_cappedSlabIncrement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    r * (∑ j ∈ range n, cappedSlabIncrement γ i r g j) =
      γ (cappedSlabExitTime γ i r g n) i - γ 0 i := by
  induction n with
  | zero => simp [cappedSlabExitTime]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have h : r ≠ 0 := ne_of_gt hr
    simp only [cappedSlabIncrement]
    field_simp
    ring

end EinsteinFull.Regeneration
