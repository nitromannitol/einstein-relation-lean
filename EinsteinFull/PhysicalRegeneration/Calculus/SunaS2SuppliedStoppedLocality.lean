import EinsteinFull.Calculus.SunaS2SuppliedStoppedLocality
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SunaS2SuppliedStoppedLocality`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal Topology
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration
/-- The physical-kernel version of `EinsteinFull.s2_future_supplied_stopped_locality`. -/
theorem s2_future_supplied_stopped_locality_phys
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0.le h1 P K)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    ∀ (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) ω)
    (hω' : IsRegular (sourceReducedBound Λ₀) ω')
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) ω hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) ω' hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, -R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) := by
  have hk : S2SuppliedKilledFDDLocality :=
    s7_supplied_killed_fdd_locality_of_endpoint_locality
      (fun hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t =>
        s6_supplied_killed_endpoint_eq_of_local_coefficients hd L hL ω ω' hω hω'
          lam h0 h1 G G' U hU hag t)
  exact s2_future_supplied_stopped_locality_of_killed_fdd_phys hk hd hΛ₀ Q lam l δ hl h0 h1 P K _hK

end EinsteinFull
