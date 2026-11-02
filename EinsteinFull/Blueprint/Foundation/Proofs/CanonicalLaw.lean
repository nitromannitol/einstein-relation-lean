import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment_u23_canonical_u2D_law

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual reduced joint law has the canonical measurable environment structure. -/
theorem node_stationary_u2D_environment_u23_canonical_u2D_law_of_deps
    (hdeps : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_stationary_u2D_environment_u23_canonical_u2D_lawStmt := by
  intro d Λ₀ r₀ Q
  obtain ⟨Λ, A, B, _, _, _, _, hstruct⟩ := hdeps Λ₀ Q.ellipticity_parameter
  obtain ⟨hstationary, hrange, _⟩ := hstruct d r₀ Q
  refine ⟨?_, rfl, ?_, Probability.continuous_translate.measurable,
    hstationary, hrange, ?_⟩
  · rfl
  · unfold reducedLaw
    infer_instance
  · intro U _
    exact Probability.localSigma_le_borel U

end EinsteinFull.Blueprint
