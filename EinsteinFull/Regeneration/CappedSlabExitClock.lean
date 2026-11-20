import EinsteinFull.Regeneration.SuccessiveSlabExits

/-!
# Time-capped coordinate slab exits

Capping each exit gives the bounded comparison clock used for forward
hitting estimates, while retaining the slab displacement bound.
-/

open Filter Set MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A coordinate slab exit stopped at a finite time horizon. -/
noncomputable def cappedCoordinateSlabExit {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) : ℝ≥0 :=
  if coordinateSlabExit γ i r = ⊤ then g else min (coordinateSlabExit γ i r).toNNReal g

/-- A capped exit takes no longer than the horizon. -/
theorem cappedCoordinateSlabExit_le {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) : cappedCoordinateSlabExit γ i r g ≤ g := by
  unfold cappedCoordinateSlabExit
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- At a capped exit, the coordinate displacement does not exceed the slab radius. -/
theorem capped_coordinate_slab_exit_displacement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) :
    |γ (cappedCoordinateSlabExit γ i r g) i - γ 0 i| ≤ r := by
  by_cases hfin : coordinateSlabExit γ i r = ⊤
  · have hstay := (MarkovProcess.ContinuousPath.exitTime_eq_top_iff
      (coordinateSlab i (γ 0) r) γ).mp hfin
    have h := hstay g
    change |γ g i - γ 0 i| < r at h
    simpa [cappedCoordinateSlabExit, hfin] using h.le
  · apply coordinate_slab_before_exit γ i r hr hfin
    simp only [cappedCoordinateSlabExit, hfin, ↓reduceIte]
    exact min_le_left _ _

/-- Recursively cap each new slab exit at the same time horizon. -/
noncomputable def cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (g : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | n + 1 =>
    let t := cappedSlabExitTime γ i r g n
    t + cappedCoordinateSlabExit (pathTimeShift γ t) i r g

/-- The capped exit clock starts at zero. -/
theorem cappedSlabExitTime_zero {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    cappedSlabExitTime γ i r g 0 = 0 := rfl

/-- Each step of the capped exit clock adds the exit of the shifted path. -/
theorem cappedSlabExitTime_succ {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ)
    (g : ℝ≥0) (n : ℕ) :
    cappedSlabExitTime γ i r g (n + 1) = cappedSlabExitTime γ i r g n +
      cappedCoordinateSlabExit (pathTimeShift γ (cappedSlabExitTime γ i r g n)) i r g := rfl

/-- The capped exit clock is nondecreasing. -/
theorem monotone_cappedSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (g : ℝ≥0) :
    Monotone (cappedSlabExitTime γ i r g) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cappedSlabExitTime_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- The `n`th capped exit occurs by `n` times the horizon. -/
theorem cappedSlabExitTime_le {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ)
    (g : ℝ≥0) (n : ℕ) : cappedSlabExitTime γ i r g n ≤ (n : ℝ≥0) * g := by
  induction n with
  | zero => simp [cappedSlabExitTime]
  | succ n ih =>
    rw [cappedSlabExitTime_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add ih (cappedCoordinateSlabExit_le _ _ _ _)

/-- A capped-clock step stays within one slab radius in the force coordinate. -/
theorem capped_slab_exit_step_bound {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) :
    |γ (cappedSlabExitTime γ i r g (n + 1)) i - γ (cappedSlabExitTime γ i r g n) i| ≤ r := by
  have h := capped_coordinate_slab_exit_displacement
    (pathTimeShift γ (cappedSlabExitTime γ i r g n)) i r hr g
  simpa only [cappedSlabExitTime_succ, pathTimeShift, ContinuousMap.coe_mk, add_zero] using h

end EinsteinFull.Regeneration
