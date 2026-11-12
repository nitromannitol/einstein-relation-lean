import Mathlib
import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.TimeChange.EuclideanTransport
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- An almost-everywhere property transfers between the Euclidean ball in
`EuclideanSpace` and the coordinate-carrier ball `External.AKM.ball`, because
`WithLp.ofLp` is a volume-preserving measurable embedding. -/
theorem ae_restrict_ball_comp_ofLp_iff {d : ℕ} (y : Vec d) (R : ℝ) (P : Vec d → Prop) :
    (∀ᵐ x ∂volume.restrict (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R),
        P (WithLp.ofLp x)) ↔
      ∀ᵐ x ∂volume.restrict (External.AKM.ball y R), P x := by
  have hpre : Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R =
      (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' External.AKM.ball y R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, External.AKM.ball,
      Set.mem_setOf_eq, TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_sub,
      WithLp.toLp_ofLp]
  have hE : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have hmap : Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d)
      (volume.restrict ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹'
        External.AKM.ball y R)) = volume.restrict (External.AKM.ball y R) :=
    ((PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage_emb hE
      (External.AKM.ball y R)).map_eq
  rw [hpre, ← hmap, hE.ae_map_iff]

end EinsteinRelation.Correctors
