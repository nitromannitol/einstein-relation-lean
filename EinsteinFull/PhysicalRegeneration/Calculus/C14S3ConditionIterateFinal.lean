import EinsteinFull.Calculus.C14S3ConditionIterateFinal
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS6ConditionIterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS6FirstSlicePositivity
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3ConditionedFinitePositive
import EinsteinFull.PhysicalRegeneration.Calculus.C14S3ConditionIterateAssembly
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C14S3ConditionIterateFinal`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

namespace EinsteinFull.Blueprint
/-- The physical-kernel version of
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps`. -/
theorem node_app_u3A_factorization_u23_condition_u2D_iterate_of_deps_phys
    (h1 : node_app_u3A_factorization_u23_independenceStmtV2_phys)
    (h2 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h3 : node_app_u3A_regen_u2D_tailsStmt_phys) :
    node_app_u3A_factorization_u23_condition_u2D_iterateStmt_phys := by
  exact c14_s3_condition_iterate_of_requested_killed_analytic_phys
    (s6_requested_killed_orbit_analytic_of_semigroup_analytic.{0}
      u5_symmetric_contraction_semigroup_scalar_analytic) h1 h2 h3

end EinsteinFull.Blueprint
