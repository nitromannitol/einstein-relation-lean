import EinsteinFull.Regeneration.CappedSlabExitClock
import EinsteinRelation.Probability.PathMaps
import MarkovProcess.Path.ExitTimeShift

/-!
# Measurability of the capped slab clock

Recentering converts each moving slab to a fixed open set, so the exit time
and every successive capped time are measurable functions of the path.
-/

open Filter Set MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Recenter a path at its initial position. -/
def initialRecenteredPath {d : ℕ} (γ : Path d) : Path d :=
  ⟨fun t => γ t - γ 0, γ.continuous.sub continuous_const⟩

/-- Recentering at the initial position is continuous on path space. -/
theorem continuous_initialRecenteredPath {d : ℕ} :
    Continuous (initialRecenteredPath (d := d)) := by
  exact Probability.continuous_path_recenter.comp
    ((continuous_eval_const 0).prodMk continuous_id)

/-- A moving-center exit is a fixed-slab exit of the recentered path. -/
theorem coordinateSlabExit_eq_recentered {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) :
    coordinateSlabExit γ i r =
      MarkovProcess.ContinuousPath.exitTime (coordinateSlab i 0 r) (initialRecenteredPath γ) := by
  unfold coordinateSlabExit MarkovProcess.ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, coordinateSlab, initialRecenteredPath, ContinuousMap.coe_mk,
    Pi.sub_apply, Pi.zero_apply, sub_zero]

/-- The first exit from the path-centered slab is measurable. -/
theorem measurable_coordinateSlabExit {d : ℕ} (i : Fin d) (r : ℝ) :
    Measurable (fun γ : Path d => coordinateSlabExit γ i r) := by
  simp_rw [coordinateSlabExit_eq_recentered]
  exact (MarkovProcess.ContinuousPath.measurable_exitTime (coordinateSlab i 0 r)
    (isOpen_coordinateSlab i 0 r)).comp continuous_initialRecenteredPath.measurable

/-- The time-capped coordinate slab exit is measurable. -/
theorem measurable_cappedCoordinateSlabExit {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    Measurable (fun γ : Path d => cappedCoordinateSlabExit γ i r g) := by
  unfold cappedCoordinateSlabExit
  exact Measurable.ite (measurableSet_eq_fun (measurable_coordinateSlabExit i r) measurable_const)
    measurable_const ((measurable_coordinateSlabExit i r).ennreal_toNNReal.min measurable_const)

/-- Each time in the successive capped slab clock is measurable. -/
theorem measurable_cappedSlabExitTime {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) (n : ℕ) :
    Measurable (fun γ : Path d => cappedSlabExitTime γ i r g n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hshift : Measurable (fun γ : Path d =>
        pathTimeShift γ (cappedSlabExitTime γ i r g n)) :=
      Probability.continuous_path_time_shift.measurable.comp (ih.prodMk measurable_id)
    convert ih.add ((measurable_cappedCoordinateSlabExit i r g).comp hshift) using 1
    funext γ
    rfl

end EinsteinFull.Regeneration
