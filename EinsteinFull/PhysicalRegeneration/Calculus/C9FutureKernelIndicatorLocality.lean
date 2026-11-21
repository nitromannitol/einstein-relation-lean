import EinsteinFull.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C9FutureKernelIndicatorLocality`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
open EinsteinRelation.Diffusion EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.future_locality_ae_starts_at_origin_of_coupling`. -/
theorem future_locality_ae_starts_at_origin_of_coupling_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀ h₁ P K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω), z.1 0 = 0 := by
  filter_upwards [hK.2.1.1, hK.2.2.1] with ω hm hp
  obtain ⟨_, r, hr⟩ := hp
  have hs := r.pathLaw_starts_at 0
  rw [← hr 0, ← hm] at hs
  exact ae_of_ae_map measurable_fst.aemeasurable hs

end EinsteinFull.Blueprint
