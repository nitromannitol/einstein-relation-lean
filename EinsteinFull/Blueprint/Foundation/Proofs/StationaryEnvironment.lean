import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual reduced law carries the full horizontal translation calculus. -/
theorem node_stationary_u2D_environment_of_deps
    (hdeps : node_stationary_u2D_environment_u23_canonical_u2D_lawStmt) :
    node_stationary_u2D_environmentStmt := by
  intro d hd Λ₀ r₀ Q
  letI : Fact (2 ≤ d) := ⟨hd⟩
  let P := Correctors.reducedEnvironmentLaw Q
  let hP := Correctors.reducedEnvironmentLaw_stationary Q
  letI : IsProbabilityMeasure P := (hdeps d Λ₀ r₀ Q).2.2.1
  refine ⟨translationLp_zero P hP, translationLp_add P hP,
    norm_translationLp P hP, surjective_translationLp P hP,
    continuous_translationLp P hP,
    Correctors.horizontalH1_iff_weakHorizontalLpDerivative hP,
    hasHorizontalLpDerivative_horizontalH1Gradient P hP, ?_⟩
  intro f
  exact ⟨Correctors.ae_horizontalH1_hasWeakGradient_orbit P hP f,
    fun g i => Correctors.horizontalH1_integration_by_parts P hP f g i⟩

end EinsteinFull.Blueprint
