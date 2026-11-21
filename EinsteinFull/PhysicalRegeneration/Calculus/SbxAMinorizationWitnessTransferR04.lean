import EinsteinFull.Calculus.SbxAMinorizationWitnessTransferR04
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxAMinorizationWitnessTransferR04`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP
open scoped NNReal
noncomputable section
namespace EinsteinFull.Blueprint
/-- The physical-kernel version of
`EinsteinFull.Blueprint.source_minorization_transfer_supplied_kernel`. -/
theorem source_minorization_transfer_supplied_kernel_phys
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (P P' : QuenchedPathLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ h0 h1 P)
    (hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ h0 h1 P')
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (hminor : ∀ᵐ ω ∂Q.measure,
      HasSourceMinorization (fun x => P (x, ω)) Δ δ R i) :
    ∀ᵐ ω ∂Q.measure, HasSourceMinorization (fun x => P' (x, ω)) Δ δ R i :=
  (source_minorization_ae_iff_of_all_start_eq Q P P' Δ δ R i
    (EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique_phys hd Q μ h0 h1 P P' hP hP')).mp hminor

end EinsteinFull.Blueprint
