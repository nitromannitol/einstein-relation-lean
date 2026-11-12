import Mathlib
import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.TimeChange.EuclideanTransport
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- The coordinate map pulls the Euclidean ball `External.AKM.ball y R` back to the
Hilbert-space ball of radius `R` about `y`, since both are defined by the same Euclidean
distance. -/
theorem preimage_ofLp_ball {d : ℕ} (y : Vec d) (R : ℝ) :
    (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' External.AKM.ball y R =
      Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R := by
  ext x
  simp only [Set.mem_preimage, External.AKM.ball, Set.mem_setOf_eq, Metric.mem_ball,
    dist_eq_norm]
  rw [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_sub, WithLp.toLp_ofLp]

end EinsteinRelation.Correctors
