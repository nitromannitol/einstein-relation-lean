import EinsteinFull.Regeneration.CappedSlabDivergence
import EinsteinFull.Regeneration.SlabWalkDomination

/-!
# All-time domination by capped slab increments

The capped clock diverges and the path stays within a slab between successive
clock times. The sum of actual increments therefore controls every path time.
-/

open Filter EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Between capped slab times the coordinate remains within one radius. -/
theorem capped_slab_exit_confinement {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (n : ℕ) (t : ℝ≥0)
    (hlo : cappedSlabExitTime γ i r g n ≤ t)
    (hhi : t ≤ cappedSlabExitTime γ i r g (n + 1)) :
    -r ≤ γ t i - γ (cappedSlabExitTime γ i r g n) i := by
  let s := cappedSlabExitTime γ i r g n
  let η := pathTimeShift γ s
  have hstep : t - s ≤ cappedCoordinateSlabExit η i r g := by
    apply tsub_le_iff_right.mpr
    simpa only [s, η, cappedSlabExitTime_succ, add_comm] using hhi
  have hcoord : |η (t - s) i - η 0 i| ≤ r := by
    by_cases hfin : coordinateSlabExit η i r = ⊤
    · have hstay := (MarkovProcess.ContinuousPath.exitTime_eq_top_iff
        (coordinateSlab i (η 0) r) η).mp hfin
      exact le_of_lt (hstay (t - s))
    · apply coordinate_slab_before_exit η i r hr hfin
      exact hstep.trans (by
        change cappedCoordinateSlabExit η i r g ≤ (coordinateSlabExit η i r).toNNReal
        simp only [cappedCoordinateSlabExit, hfin, ↓reduceIte, min_le_left])
  have hcoord' : |γ t i - γ s i| ≤ r := by
    have hlo' : s ≤ t := hlo
    have hsum : s + (t - s) = t := add_tsub_cancel_of_le hlo'
    simpa only [η, pathTimeShift, ContinuousMap.coe_mk, add_zero, hsum] using hcoord
  exact (abs_le.mp hcoord').1

/-- Every coordinate value is bounded below by the actual capped-step sum,
with one radius of slack. -/
theorem capped_slab_all_time_domination {d : ℕ} (γ : Path d) (i : Fin d)
    (r : ℝ) (hr : 0 < r) (g : ℝ≥0) (hg : 0 < g) (t : ℝ≥0) :
    ∃ n : ℕ, r * ((∑ j ∈ range n, cappedSlabIncrement γ i r g j) - 1) ≤
      γ t i - γ 0 i := by
  let τ := cappedSlabExitTime γ i r g
  let clock : ℕ → ℝ := fun n => τ n
  have htop : Tendsto clock atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr (capped_slab_exit_times_tendsto_atTop γ i r hr g hg)
  have hzero : clock 0 = 0 := by simp [clock, τ, cappedSlabExitTime_zero]
  let n := cycleCount clock htop t
  have hn := cycleCount_bracket clock htop hzero t t.coe_nonneg
  have hlo : τ n ≤ t := NNReal.coe_le_coe.mp hn.1
  have hhi : t ≤ τ (n + 1) := NNReal.coe_le_coe.mp hn.2.le
  have hs := capped_slab_exit_confinement γ i r hr g n t hlo hhi
  have hc := sum_cappedSlabIncrement γ i r hr g n
  refine ⟨n, ?_⟩
  nlinarith

end EinsteinFull.Regeneration
