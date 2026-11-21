import EinsteinFull.Blueprint.Foundation.Proofs.F2PastKernelReduction
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3ActualPastKernel
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3PastAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.Foundation.Proofs.F2PastKernelReduction`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

namespace EinsteinFull.Blueprint
/-- The physical-kernel version of
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_past_u2D_kernel_of_deps`. -/
theorem node_app_u3A_factorization_u23_past_u2D_kernel_of_deps_phys :
    node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys :=
  EinsteinFull.c10_actual_past_kernel_phys

end EinsteinFull.Blueprint
