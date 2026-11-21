import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices`

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
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_slicesStmt`. -/
def node_app_u3A_factorization_u23_slicesStmt_phys : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (n : ℕ), 2 ≤ n →
    let T := ((n - 1 : ℕ) : ℝ≥0) * Δ
    let Γ := Regeneration.forcedBitTrialEvent Δ lam R i (n - 1)
    MeasurableSet[Regeneration.finiteHistorySigma Δ (n - 1)] Γ ∧
      (∀ z : Regeneration.CoupledSample d,
        regenerationTime hd lam l 1 z = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
          z ∈ Γ ∧ z.2 (n - 1) = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i) ∧
      (∀ z : Regeneration.CoupledSample d, z.1 0 = 0 → z ∈ Γ →
        let a := z.1 T
        2 * R ≤ a i ∧
          (∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ a i + R) ∧
          ∀ y : Vec d, y ∈ Regeneration.endpointBall i R a →
            10 * R ≤ y i ∧
              ∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ y i - 7 * R)

end EinsteinFull.Blueprint
