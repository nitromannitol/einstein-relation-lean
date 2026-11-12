import Mathlib
import EinsteinRelation.Environment.Basic

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Change of variables along the coordinate map `WithLp.ofLp` from the Euclidean space
`EuclideanSpace ℝ (Fin d)` to the coordinate space `Vec d`. The map is a volume-preserving
measurable embedding, so no measurability of the set `U` is needed. -/
theorem setIntegral_comp_ofLp {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) :
    (∫ x in (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' U, f (WithLp.ofLp x)) =
      ∫ x in U, f x := by
  have hemb : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Vec d)).symm.measurableEmbedding
  exact (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb hemb f U

end EinsteinRelation.Correctors
