import EinsteinFull.Regeneration.CoordinateSlabExit

/-!
# Successive coordinate slab exits

The successive slab-exit clock records the embedded path of the comparison
argument. Finite exits have a fixed coordinate step and cannot accumulate.
-/

open Filter Set MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- First exit from the coordinate slab centered at the path's starting point. -/
noncomputable def coordinateSlabExit {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) : ℝ≥0∞ :=
  MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ

/-- The successive slab-exit clock, with extended exits converted only for evaluation. -/
noncomputable def successiveSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) : ℕ → ℝ≥0
  | 0 => 0
  | n + 1 =>
    let t := successiveSlabExitTime γ i r n
    t + (coordinateSlabExit (pathTimeShift γ t) i r).toNNReal

/-- The successive exit clock begins at zero. -/
theorem successiveSlabExitTime_zero {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) :
    successiveSlabExitTime γ i r 0 = 0 := rfl

/-- The next clock time adds the exit time of the shifted path. -/
theorem successiveSlabExitTime_succ {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (n : ℕ) :
    successiveSlabExitTime γ i r (n + 1) = successiveSlabExitTime γ i r n +
      (coordinateSlabExit (pathTimeShift γ (successiveSlabExitTime γ i r n)) i r).toNNReal := rfl

/-- The successive exit clock is nondecreasing. -/
theorem monotone_successiveSlabExitTime {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) :
    Monotone (successiveSlabExitTime γ i r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [successiveSlabExitTime_succ]
  exact le_add_of_nonneg_right (by positivity)

/-- Each finite successive exit has exactly the slab radius as coordinate step. -/
theorem successive_slab_exit_step {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (hfin : coordinateSlabExit
      (pathTimeShift γ (successiveSlabExitTime γ i r n)) i r ≠ ⊤) :
    |γ (successiveSlabExitTime γ i r (n + 1)) i - γ (successiveSlabExitTime γ i r n) i| = r := by
  have h := coordinate_slab_exit_displacement
    (pathTimeShift γ (successiveSlabExitTime γ i r n)) i r hr hfin
  simpa only [coordinateSlabExit, successiveSlabExitTime_succ, pathTimeShift,
    ContinuousMap.coe_mk, add_zero] using h

/-- Finite successive slab exits diverge to infinity. -/
theorem successive_slab_exit_times_tendsto_atTop {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r)
    (hfin : ∀ n, coordinateSlabExit (pathTimeShift γ (successiveSlabExitTime γ i r n)) i r ≠ ⊤) :
    Tendsto (successiveSlabExitTime γ i r) atTop atTop :=
  slab_exit_times_tendsto_atTop γ i (successiveSlabExitTime γ i r)
    (monotone_successiveSlabExitTime γ i r) r hr
    (fun n => (successive_slab_exit_step γ i r hr n (hfin n)).symm.le)

/-- Between two finite successive exits, the coordinate stays within one slab radius. -/
theorem successive_slab_exit_confinement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (n : ℕ)
    (hfin : coordinateSlabExit (pathTimeShift γ (successiveSlabExitTime γ i r n)) i r ≠ ⊤)
    (t : ℝ≥0) (hlo : successiveSlabExitTime γ i r n ≤ t)
    (hhi : t ≤ successiveSlabExitTime γ i r (n + 1)) :
    -r ≤ γ t i - γ (successiveSlabExitTime γ i r n) i := by
  let s := successiveSlabExitTime γ i r n
  let v := (coordinateSlabExit (pathTimeShift γ s) i r).toNNReal
  have ht : t - s ≤ v := by
    apply tsub_le_iff_right.mpr
    simpa only [s, v, successiveSlabExitTime_succ, add_comm] using hhi
  have hh := coordinate_slab_before_exit (pathTimeShift γ s) i r hr hfin (t - s) ht
  have hslo : s ≤ t := hlo
  have habs : |γ t i - γ s i| ≤ r := by
    simpa only [coordinateSlabExit, pathTimeShift, ContinuousMap.coe_mk, add_zero,
      add_tsub_cancel_of_le hslo] using hh
  exact (abs_le.mp habs).1

end EinsteinFull.Regeneration
