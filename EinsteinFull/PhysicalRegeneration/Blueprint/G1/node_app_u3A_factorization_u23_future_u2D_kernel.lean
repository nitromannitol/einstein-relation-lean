import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The physical-kernel version of
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_future_u2D_kernelStmt`. -/
def node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K),
    ∀ (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}] B ∧
        (fun ω => ∫ z, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q.measure] B

end EinsteinFull.Blueprint
