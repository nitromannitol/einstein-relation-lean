import Mathlib
import EinsteinRelation.Environment.Basic

/-! # Transport of `Lᵖ` membership along the Euclidean coordinate map

The coordinate map `WithLp.ofLp` from the Euclidean space `EuclideanSpace ℝ (Fin d)` to the
coordinate space `Vec d` is a measurable equivalence and preserves Lebesgue measure. Membership
in `Lᵖ` of a restriction to a set therefore transfers between the two carriers.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Membership in `Lᵖ` of `f` on a set `U` of coordinate space is equivalent to membership
of the composite with `WithLp.ofLp` on the Euclidean preimage of `U`. -/
theorem memLp_comp_ofLp_iff {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (U : Set (Vec d)) (f : Vec d → F) (p : ℝ≥0∞) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp x)) p
        (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) ↔
      MemLp f p (volume.restrict U) := by
  have he : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  have hmap : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
      (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U)) =
        volume.restrict U :=
    ((PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage_emb he U).map_eq
  refine (he.memLp_map_measure_iff (g := f)).symm.trans ?_
  rw [hmap]

end EinsteinRelation.Correctors
