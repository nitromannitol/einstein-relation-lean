import EinsteinRelation.Regeneration.RenewalCarriers
import EinsteinFull.Regeneration.PhysicalKernelPredicate

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.RenewalCarriers`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration.Renewal
/-- The physical-kernel version of `EinsteinRelation.Regeneration.Renewal.IsGMPCouplingV2`. -/
def IsGMPCouplingV2Phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) : Prop :=
  HasProbabilityLaws Q.measure K ∧
  HasPathMarginals Q.measure K P ∧
  EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam hl0 hl1 P ∧
  HasFreshBits Q.measure (regenDelta lam) δ K ∧
  HasDeterministicRestart Q.measure (regenDelta lam) K ∧
  HasSuccessfulBridgeSupport Q.measure (regenDelta lam) (forceCoord hd) (l / lam) K ∧
  HasUniformSuccessfulEndpoint Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd) K ∧
  HasOneIntervalKernel Q.measure (regenDelta lam) δ (l / lam) (forceCoord hd) P K

end EinsteinRelation.Regeneration.Renewal
end
