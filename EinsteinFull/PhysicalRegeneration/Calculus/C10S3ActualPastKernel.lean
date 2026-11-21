import EinsteinFull.Calculus.C10S3ActualPastKernel
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
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
`EinsteinFull.Calculus.C10S3ActualPastKernel`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull
/-- The physical-kernel version of `EinsteinFull.c10_actual_past_kernel`. -/
theorem c10_actual_past_kernel_phys :
    Blueprint.node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys := by
  apply Blueprint.c2_s3_past_kernel_of_requested_locality_phys
  intro d hd Λ₀ r₀ hΛ₀ Q lam l δ hl h0 h1 P K hK v
  dsimp only
  intro ω ω' hω hω' r r' hr hr' hagree y hy
  let U : Set (Vec d) := {z | z (Renewal.forceCoord hd) < v + 3 * (l / lam)}
  have hU : IsOpen U := isOpen_lt (continuous_apply _) continuous_const
  have hyU : y ∈ U := by
    dsimp [U]
    have hR : 0 < l / lam := div_pos hl h0
    linarith
  let : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  apply s2_supplied_stopped_locality_of_killed_fdd U hU _ _
  apply s7_supplied_killed_trace_fdd_of_killed_marginals hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0.le h1 r r' U hU ?_ y hyU
  apply s6_supplied_killed_marginals_of_local_coefficients hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0.le h1 r r' U hU
  intro z hz
  have hfields := hagree z (le_of_lt hz)
  exact ⟨hfields.1, hfields.2⟩

end EinsteinFull
