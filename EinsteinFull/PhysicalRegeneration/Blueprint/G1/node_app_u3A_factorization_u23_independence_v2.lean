import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2`

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
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_independenceStmtV2`. -/
def node_app_u3A_factorization_u23_independenceStmtV2_phys : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K),
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    ∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
    (∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
      Regeneration.BoundedRealTest F →
    ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
      Regeneration.BoundedRealTest H →
    let A := fun (y : Vec d) (ω : FieldPair d) =>
      F ω * Regeneration.firstSlicePastIntegral Δ lam R i (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)
    ((r₀ < 2 * R) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), y i < 10 * R → A y =ᵐ[Q.measure] 0) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), 10 * R ≤ y i →
        (∃ A' B' : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A' ∧
          Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B' ∧
          A y =ᵐ[Q.measure] A' ∧ B y =ᵐ[Q.measure] B') ∧
        (∫ ω, A y ω * B y ω ∂Q.measure) =
          (∫ ω, A y ω ∂Q.measure) * ∫ ω, B y ω ∂Q.measure) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, B y ω ∂Q.measure) =
        ∫ q in regenerationNoReturn hd R, Φ (regenerationRecord hd lam l 0 q) ∂μ) ∧
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂μ) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) ∧
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν

end EinsteinFull.Blueprint
