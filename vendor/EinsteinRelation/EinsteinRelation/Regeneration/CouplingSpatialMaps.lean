import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import EinsteinRelation.Probability.PathMaps

/-! # Spatial maps for the one-interval coupling

Source `paper/main.tex:268,331–340,377–390`. Spatial recentering is an invertible
measurable map, preserves the bits, and transports the two coupling balls.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinRelation.Regeneration

/-- Subtract the initial spatial point from every path position. -/
def recenterPath {d : ℕ} (x : Vec d) (γ : Path d) : Path d :=
  ⟨fun t => γ t - x, γ.continuous.sub continuous_const⟩

@[simp] theorem recenterPath_apply {d : ℕ} (x : Vec d) (γ : Path d) (t : ℝ≥0) :
    recenterPath x γ t = γ t - x := rfl

theorem measurable_recenterPath {d : ℕ} (x : Vec d) : Measurable (recenterPath x) :=
  Probability.continuous_path_recenter.measurable.comp
    (measurable_const.prodMk measurable_id)

@[simp] theorem recenterPath_zero {d : ℕ} (γ : Path d) : recenterPath 0 γ = γ := by
  ext t
  exact sub_zero _

@[simp] theorem recenterPath_recenterPath {d : ℕ} (x y : Vec d) (γ : Path d) :
    recenterPath x (recenterPath y γ) = recenterPath (x + y) γ := by
  ext t i
  simp only [recenterPath_apply, Pi.sub_apply, Pi.add_apply]
  ring

@[simp] theorem recenterSample_fst {d : ℕ} (x : Vec d) (z : CoupledSample d) :
    (recenterSample x z).1 = recenterPath x z.1 := rfl

@[simp] theorem recenterSample_snd {d : ℕ} (x : Vec d) (z : CoupledSample d) :
    (recenterSample x z).2 = z.2 := rfl

@[simp] theorem recenterSample_zero {d : ℕ} (z : CoupledSample d) :
    recenterSample 0 z = z := by
  apply Prod.ext
  · exact recenterPath_zero _
  · rfl

/-- The killed-segment region is translated with the starting point (line 268). -/
theorem sub_mem_couplingRegion_iff {d : ℕ} (i : Fin d) (R : ℝ) (x y z : Vec d) :
    y - x ∈ couplingRegion i R (z - x) ↔ y ∈ couplingRegion i R z := by
  have heq : y - x - (z - x + (5 * R) • unitVector i) =
      y - (z + (5 * R) • unitVector i) := by abel
  change euclideanNorm _ < 6 * R ↔ euclideanNorm _ < 6 * R
  rw [heq]

/-- The successful endpoint ball is translated with the starting point (line 268). -/
theorem sub_mem_endpointBall_iff {d : ℕ} (i : Fin d) (R : ℝ) (x y z : Vec d) :
    y - x ∈ endpointBall i R (z - x) ↔ y ∈ endpointBall i R z := by
  have heq : y - x - (z - x + (9 * R) • unitVector i) =
      y - (z + (9 * R) • unitVector i) := by abel
  change euclideanNorm _ < R ↔ euclideanNorm _ < R
  rw [heq]

end EinsteinRelation.Regeneration
