import EinsteinFull.Regeneration.FirstRegenerationFiniteness
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.GuardEstimate
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.FirstRegenerationFiniteness`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.Blueprint
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.first_regeneration_finite_of_hitting_and_return`. -/
theorem first_regeneration_finite_of_hitting_and_return_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (κ C : ℝ) (hκ : 0 < κ)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let μ := annealedCoupledLaw Q.measure K
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let E := {q : FieldPair d × CoupledSample d | trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | NoBacktracking R
        (pathTimeShift q.2.1 (trialStartSequence Δ lam R q.2 i n).toNNReal) i})) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤ := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨ε, hε, hε1, hguard⟩ := guard_estimate_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  have hhit' := annealed_forward_hitting_bound Q.measure P K hK.1 hK.2.1 lam κ C
    (Renewal.forceCoord hd) hhit
  have hpass := ae_shifted_passages_finite_of_forward_hitting_bound
    (annealedCoupledLaw Q.measure K) (Renewal.forceCoord hd) lam κ C h0 hκ hhit'
  apply coupling_scope_ae_first_regeneration_finite_of_guard_and_return_estimates
    Q.measure K hK.1 (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0)
    δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0 (div_pos hl h0) (Renewal.forceCoord hd)
    ε hε hε1 _ hguard η hη hη1 hreturn
  intro m A _hA
  filter_upwards [hpass] with q hq n
  exact hq (Renewal.regenDelta lam) (l / lam) ((m : ℝ≥0) * Renewal.regenDelta lam) (A q.2) n

end EinsteinFull.Regeneration
