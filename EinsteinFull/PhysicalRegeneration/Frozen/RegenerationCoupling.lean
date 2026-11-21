import EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Frozen.RegenerationCoupling`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation
/-- The physical-kernel version of `EinsteinFull.IsRegenerationCoupling`. -/
abbrev IsRegenerationCouplingPhys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) : Prop :=
  Regeneration.Renewal.IsGMPCouplingV2Phys hd Q.ellipticity_parameter Q
    lam l δ h₀ h₁ P K

end EinsteinFull
