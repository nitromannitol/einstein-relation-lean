import EinsteinFull.Regeneration.SlabExitClock
import MarkovProcess.Path.ExitTime

/-!
# Coordinate slab exits

Continuity fixes the displacement at a finite slab exit and bounds the path
before that exit.
-/

open Set Filter MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The open coordinate slab of radius `r` about `x`. -/
def coordinateSlab {d : ℕ} (i : Fin d) (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {y | |y i - x i| < r}

/-- A coordinate slab is open. -/
theorem isOpen_coordinateSlab {d : ℕ} (i : Fin d) (x : Vec d) (r : ℝ) :
    IsOpen (coordinateSlab i x r) :=
  isOpen_lt (((continuous_apply i).sub continuous_const).abs) continuous_const

/-- At a finite exit from a positive slab, the coordinate displacement equals its radius. -/
theorem coordinate_slab_exit_displacement {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (hr : 0 < r)
    (hfin : MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ ≠ ⊤) :
    |γ (MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ).toNNReal i - γ 0 i| = r := by
  let U := coordinateSlab i (γ 0) r
  have hU : IsOpen U := isOpen_coordinateSlab i (γ 0) r
  have h0 : γ 0 ∈ U := by simpa [U, coordinateSlab] using hr
  have hfront := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier U hU γ h0 hfin
  have hclosed : IsClosed {y : Vec d | |y i - γ 0 i| ≤ r} :=
    isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const
  have hsubset : U ⊆ {y : Vec d | |y i - γ 0 i| ≤ r} := by
    intro y hy
    change |y i - γ 0 i| < r at hy
    exact le_of_lt hy
  have hle : |γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - γ 0 i| ≤ r :=
    closure_minimal hsubset hclosed hfront.1
  have hge : r ≤ |γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal i - γ 0 i| := by
    have hn : γ (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal ∉ U := by
      simpa only [hU.interior_eq] using hfront.2
    exact le_of_not_gt hn
  exact le_antisymm hle hge

/-- Until a finite slab exit, the coordinate stays within the slab radius. -/
theorem coordinate_slab_before_exit {d : ℕ} (γ : Path d) (i : Fin d) (r : ℝ) (hr : 0 < r)
    (hfin : MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ ≠ ⊤)
    (t : ℝ≥0) (ht : t ≤ (MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ).toNNReal) :
    |γ t i - γ 0 i| ≤ r := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have ht' : (t : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime (coordinateSlab i (γ 0) r) γ := by
      rw [← ENNReal.coe_toNNReal hfin]
      exact_mod_cast hlt
    exact le_of_lt (MarkovProcess.ContinuousPath.mem_of_lt_exitTime
      (coordinateSlab i (γ 0) r) γ t ht')
  · exact (coordinate_slab_exit_displacement γ i r hr hfin).le

end EinsteinFull.Regeneration
