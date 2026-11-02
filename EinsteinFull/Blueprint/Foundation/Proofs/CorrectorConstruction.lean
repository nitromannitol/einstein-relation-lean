import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinRelation.Correctors.HomogenizedMatrixBounds

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The canonical variational construction supplies the corrector gradient and
its expected-flux matrix, including in dimension two. The structural constant
is chosen before the dimension and law. -/
theorem node_corrector_u2D_construction_of_deps
    (hstationary : node_stationary_u2D_environmentStmt)
    (hbounds : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_corrector_u2D_constructionStmt := by
  -- The canonical producers already derive these properties from EnvironmentLaw.
  have _ := hstationary
  have _ := hbounds
  intro L hL
  have hK : 1 ≤ sourceReducedBound L := by
    have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith only [hL])
    have hp : 1 ≤ 3 * L ^ 2 + L + 1 := by
      nlinarith only [sq_nonneg L, hL]
    simpa only [one_mul, sourceReducedBound] using
      (mul_le_mul he hp (by norm_num) (Real.exp_pos _).le)
  refine ⟨sourceReducedBound L, hK, ?_⟩
  intro d _hd r₀ Q
  refine ⟨homogenizedMatrix_isElliptic Q, ?_⟩
  intro i
  refine ⟨Correctors.canonicalCorrectorGradient Q i, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact Correctors.canonicalCorrectorGradient_variational_horizontalH1 Q i
  · intro G' hG'
    exact Correctors.correctorGradient_eq_canonical_of_horizontal_variational Q i G' hG'
  · exact Correctors.canonicalCorrectorGradient_mean_zero Q i
  · exact Correctors.canonicalCorrectorFlux_integrable Q i
  · intro j
    rfl

end EinsteinFull.Blueprint
