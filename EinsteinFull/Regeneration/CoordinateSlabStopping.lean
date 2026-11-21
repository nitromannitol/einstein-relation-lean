import EinsteinFull.Regeneration.CappedSlabExitMeasurability
import MarkovProcess.Path.Stopping

/-!
# Stopping at a coordinate slab

The first exit from a slab centered at the initial point is a stopping time
for the canonical path filtration.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The first moving-slab exit before a fixed time depends only on the path prefix. -/
theorem coordinateSlabExit_le_iff_of_prefix {d : ℕ} (γ η : Path d) (i : Fin d) (r : ℝ)
    (T : ℝ≥0) (hprefix : ∀ t ≤ T, γ t = η t) :
    coordinateSlabExit γ i r ≤ (T : ℝ≥0∞) ↔
      coordinateSlabExit η i r ≤ (T : ℝ≥0∞) := by
  rw [coordinateSlabExit_eq_recentered, coordinateSlabExit_eq_recentered]
  rw [MarkovProcess.ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
    (isOpen_coordinateSlab i 0 r),
    MarkovProcess.ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
    (isOpen_coordinateSlab i 0 r)]
  simp only [MarkovProcess.ContinuousPath.hitsSetBy, Set.mem_ofPred_eq]
  have hzero : γ 0 = η 0 := hprefix 0 (by positivity)
  constructor <;> rintro ⟨s, hs⟩ <;> refine ⟨s, ?_⟩
  · simpa only [initialRecenteredPath, ContinuousMap.coe_mk, hprefix s s.property, hzero] using hs
  · simpa only [initialRecenteredPath, ContinuousMap.coe_mk, hprefix s s.property, hzero] using hs

/-- Deterministic path stopping is measurable from the corresponding canonical history. -/
theorem measurable_stoppedPath_canonicalHistory {d : ℕ} (T : ℝ≥0) :
    @Measurable (Path d) (Path d)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
      (borel (Path d)) (MarkovProcess.ContinuousPath.stoppedPath T) := by
  let : MeasurableSpace (Path d) :=
    MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun γ : Path d => γ (min t T))
  exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
    (alpha := Vec d) (min t T)).mono
      (MarkovProcess.ContinuousPath.canonicalFiltration.mono (min_le_right t T)) le_rfl

/-- The first exit from a slab centered at the initial position is a stopping time. -/
theorem isStoppingTime_coordinateSlabExit {d : ℕ} (i : Fin d) (r : ℝ) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => coordinateSlabExit γ i r) := by
  intro T
  have heq : {γ : Path d | coordinateSlabExit γ i r ≤ (T : ℝ≥0∞)} =
      (MarkovProcess.ContinuousPath.stoppedPath T) ⁻¹'
        {γ : Path d | coordinateSlabExit γ i r ≤ (T : ℝ≥0∞)} := by
    ext γ
    exact coordinateSlabExit_le_iff_of_prefix γ
      (MarkovProcess.ContinuousPath.stoppedPath T γ) i r T
      (fun t ht => (MarkovProcess.ContinuousPath.stoppedPath_apply_of_le T γ t ht).symm)
  change @MeasurableSet (Path d)
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) T)
    {γ : Path d | coordinateSlabExit γ i r ≤ (T : ℝ≥0∞)}
  rw [heq]
  exact measurable_stoppedPath_canonicalHistory T
    ((measurable_coordinateSlabExit i r) measurableSet_Iic)

/-- A deterministic time cap preserves the moving-slab stopping time. -/
theorem isStoppingTime_cappedCoordinateSlabExit {d : ℕ} (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ : Path d => (cappedCoordinateSlabExit γ i r g : ℝ≥0∞)) := by
  have heq : (fun γ : Path d => (cappedCoordinateSlabExit γ i r g : ℝ≥0∞)) =
      fun γ => min (coordinateSlabExit γ i r) (g : ℝ≥0∞) := by
    funext γ
    by_cases hfin : coordinateSlabExit γ i r = ⊤
    · simp [cappedCoordinateSlabExit, hfin]
    · simp [cappedCoordinateSlabExit, hfin, ENNReal.coe_min, ENNReal.coe_toNNReal hfin]
  rw [heq]
  exact (isStoppingTime_coordinateSlabExit i r).min_const g

end EinsteinFull.Regeneration
