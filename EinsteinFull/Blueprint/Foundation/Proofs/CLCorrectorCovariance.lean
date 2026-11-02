import EinsteinFull.Calculus.CLDFGWApplicationV2
import EinsteinFull.Calculus.CLDiffusivityIdentification
import EinsteinFull.Calculus.CLConstantEnvironmentDiffusivity
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeCorrectorCovariance
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeUnforced
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise
import EinsteinFull.Blueprint.Foundation.Proofs.D1PathwiseV2
import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction

/-!
# The corrector covariance (`eq.time-change-identities#corrector-covariance`, V2)

The reduced diffusion has an annealed invariance principle whose covariance is the homogenized
coefficient, for every law with Assumption 1.2 smoothness. Translation ergodicity and finite range
leave two cases (`environmentLaw_period_dichotomy`). For aperiodic laws the admitted input
`EinsteinFull.External.dfgw_invariance` (De Masi–Ferrari–Goldstein–Wick, Theorem 2.2) applies to
the two-sided environment process on its trajectory space, and its diffusion matrix is the
homogenized coefficient (`dfgw_matrix_eq_homogenizedCoefficient`). Otherwise the law is a point mass
at a translation invariant field and the reduced diffusion is Brownian with that covariance
(`hasDiffusivity_of_constant`). The pathwise time change is its closed proof.
-/

namespace EinsteinFull.Blueprint

open MeasureTheory ProbabilityTheory Filter EinsteinRelation EinsteinFull
open EinsteinFull.External.Draft

/-- `eq.time-change-identities#corrector-covariance` (V2) from the unforced process and the
corrector construction. -/
theorem node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covariance_of_deps
    (hUnforced : node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2)
    (_hCorrector : node_corrector_u2D_constructionStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_corrector_u2D_covarianceStmtV2 := by
  intro d hd Λ₀ r₀ b Q hΛ₀ hr₀ hb hsm Y hY
  let D : StructuralData d := ⟨Λ₀, r₀, b, hΛ₀, hr₀, hb⟩
  have hQ : HasSmoothBounds D Q := hsm
  have hunf : UnforcedAt hd Q := hUnforced d hd D Q hQ
  have hpath : PathwiseAt Q := fun i lam =>
    node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps d hd D Q hQ i lam
  rcases environmentLaw_period_dichotomy Q hd with hap | ⟨c, hc, hQc⟩
  · have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
      hY.mono fun _ h => h.1
    obtain ⟨K, hKm, hK, -⟩ := exists_unforced_reduced_kernel hd D Q hQ Y hY hprob
    obtain ⟨C, Dm, hC, hD, W, hW, hconv⟩ :=
      dfgw_hasDiffusivity_axiom hd D Q hQ hunf hpath hap hK Y hY
    have hDm := dfgw_matrix_eq_homogenizedCoefficient hd D Q hQ hunf hpath hap hK hC hD hW.2.1
    rw [← hDm]
    exact ⟨W, hW, hconv⟩
  · exact hasDiffusivity_of_constant hd D Q hQ hc hQc Y hY

end EinsteinFull.Blueprint
