import EinsteinFull.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxBCenteredLocalReturnClosureR15`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open EinsteinRelation EinsteinFull.External.Source.GMP
namespace EinsteinFull
/-- The physical-kernel version of `EinsteinFull.b_centered_local_return_unconditional_r15`. -/
theorem b_centered_local_return_unconditional_r15_phys : b_centered_local_return_input_phys := by
  apply b_centered_local_return_of_continuous_native_primitives_phys
  · intro d hd κ hκ R hR ρ α hell hρ
    obtain ⟨s, u, G, hs, hb, hv, hc, hz, hcert⟩ :=
      b_actual_spectrum_selection_r14 hd hκ hR hell
    exact ⟨bNativeSpectralKernelR13 s, G,
      hcert (b_native_initial_delta_of_continuous_density_r15 hd hκ hR hell hρ s)⟩
  · intro d hd κ hκ
    obtain ⟨δ, hδ, hmass⟩ := b_renewal_native_half_survival_of_ellipticity d hd κ hκ
    refine ⟨δ, hδ, ?_⟩
    intro R hR ρ α hell K G hK x r u hr hball hu hut
    exact hmass R ρ α K G hell hK x r u hr hball hu hut
  · intro d hd κ hκ
    obtain ⟨δ, H, hδ, hH, hcomp⟩ := b_renewal_native_harnack_of_ellipticity d hd κ hκ
    refine ⟨δ, H, hδ, hH, ?_⟩
    intro R hR ρ α hell K G hK x y r u hr hball hy hu hut hxy
    exact hcomp R ρ α K G hell hK x y r u hr hball hy hu hut hxy

end EinsteinFull
