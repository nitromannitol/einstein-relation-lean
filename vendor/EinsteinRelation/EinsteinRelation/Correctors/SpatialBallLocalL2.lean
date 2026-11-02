import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Environment.EuclideanLipschitz

/-! Source: `paper/main.tex:693-702`. Euclidean balls exhaust every compact spatial region. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Local L² on all Euclidean balls gives L² on every compact set. -/
theorem memLp_on_compacts_of_euclidean_balls {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : Vec d → E)
    (hf : ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (ball 0 R))) :
    ∀ K : Set (Vec d), IsCompact K → MemLp f 2 (volume.restrict K) := by
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  let S := max R 0 + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hRS : R < S := lt_of_le_of_lt (le_max_left R 0) (lt_add_one _)
  apply (hf (((d : ℝ) + 1) * S) (mul_pos (by positivity) hS)).mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  change euclideanNorm (x - 0) < ((d : ℝ) + 1) * S
  rw [sub_zero]
  have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  exact (euclideanNorm_le_dimension_mul_norm x).trans_lt
    (mul_lt_mul_of_pos_left (hxR.trans_lt hRS) (by positivity))

end EinsteinRelation.Correctors
