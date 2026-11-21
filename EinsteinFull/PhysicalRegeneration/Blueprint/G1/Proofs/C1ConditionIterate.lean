import EinsteinFull.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.C1ConditionIterate`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
/-- The physical-kernel version of `EinsteinFull.Blueprint.c1_prebridge_survival`. -/
theorem c1_prebridge_survival_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd (l / lam) ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Renewal.regenDelta lam →
          -(l / lam) < q.2.1 s (Renewal.forceCoord hd)) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    (Renewal.regenDelta lam) hΔ lam (l / lam) h₀ (div_pos hl h₀)
    (Renewal.forceCoord hd) (n - 1) hK.2.2.2.2.2.1
  have hstart := ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  filter_upwards [hbar, hstart] with q hq hq0
  intro ht
  have htime : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) =
      ((((n - 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n)] using ht
  have hb := hq htime
  simpa only [regenerationNoReturn, Set.mem_ofPred_eq, hq0, Pi.zero_apply, sub_zero]
    using hb

end EinsteinFull.Blueprint
