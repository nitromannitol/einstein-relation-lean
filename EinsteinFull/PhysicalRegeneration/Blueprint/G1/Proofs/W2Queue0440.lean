import EinsteinFull.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.W2Queue0440`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_slices_of_deps`. -/
theorem node_app_u3A_factorization_u23_slices_of_deps_phys :
    node_app_u3A_factorization_u23_slicesStmt_phys := by
  intro d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl _hr _hδ _hδ₁ P K _hK
  let R := l / lam
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta lam
  have hR : 0 < R := div_pos hl h₀
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (pow_pos h₀ 2))
  dsimp only
  intro n hn
  refine ⟨measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i (n - 1),
    ?_, ?_⟩
  · intro z
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R z i (n - 1)
  · intro z hz hΓ
    obtain ⟨hmax, hheight⟩ :=
      forcedBitTrialEvent_geometry Δ hΔ lam R h₀ hR i (n - 1) z hΓ
    have hz0 : z.1 0 i = 0 := congrFun hz i
    rw [hz0, sub_zero] at hmax hheight
    refine ⟨hheight, ?_, ?_⟩
    · intro t ht
      have hdisp := displacement_le_coordinateMaximum z.1 i t
        ((n - 1 : ℕ) * Δ) ht
      rw [hz0, sub_zero] at hdisp
      exact hdisp.trans hmax
    · intro y hy
      have hcoord := coordinate_abs_le_euclideanNorm
        (y - (z.1 ((n - 1 : ℕ) * Δ) + (9 * R) • unitVector i)) i
      have hball : euclideanNorm
          (y - (z.1 ((n - 1 : ℕ) * Δ) + (9 * R) • unitVector i)) < R := hy
      have hlow := (abs_lt.mp (lt_of_le_of_lt hcoord hball)).1
      have hshift : (y - (z.1 ((n - 1 : ℕ) * Δ) + (9 * R) • unitVector i)) i =
          y i - (z.1 ((n - 1 : ℕ) * Δ) i + 9 * R) := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          unitVector, Pi.single_eq_same, mul_one]
      rw [hshift] at hlow
      refine ⟨by linarith only [hlow, hheight], ?_⟩
      exact forcedBitTrialEvent_endpoint_past_barrier Δ hΔ lam R h₀ hR i
        (n - 1) z hΓ y hy

end EinsteinFull.Blueprint
