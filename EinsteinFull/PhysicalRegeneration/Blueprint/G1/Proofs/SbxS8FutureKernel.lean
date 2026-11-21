import EinsteinFull.Blueprint.G1.Proofs.SbxS8FutureKernel
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS2FutureKernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS8FutureKernel`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS8_killedPathBitKernel_stopped_of_coupling`. -/
theorem sbxS8_killedPathBitKernel_stopped_of_coupling_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      sbxS8KilledPathBitKernel R i K ω =
        (sbxS2StoppedOriginKernel R i K ω).restrict {z | NoBacktracking R z.1 i} := by
  filter_upwards [sbxS2_stoppedOriginKernel_restrict_of_coupling_phys
    hd Q lam l δ h₀ h₁ P K hK R hR i] with ω he
  exact he.symm

end EinsteinFull.Blueprint
