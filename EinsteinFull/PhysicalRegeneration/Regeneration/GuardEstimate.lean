import EinsteinFull.Regeneration.GuardEstimate
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
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GuardEstimate`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.Blueprint
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of `EinsteinFull.Regeneration.guard_estimate`. -/
theorem guard_estimate_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ (m : ℕ) (A : CoupledSample d → ℝ),
        @Measurable (CoupledSample d) ℝ
          (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A →
      ∀ N : ℕ,
        let Δ := Renewal.regenDelta lam
        let R := l / lam
        let i := Renewal.forceCoord hd
        let μ := annealedCoupledLaw Q.measure K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}) := by
  obtain ⟨ε, hε, hε1, htube⟩ := reduced_centered_survival_phys hd Λ₀ r₀ l hl
  refine ⟨ε, hε, hε1, ?_⟩
  intro m A hA N
  let μ := annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure Q.measure := Q.probability
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hbase := htube Q lam (by simpa only [abs_of_pos h0] using h0)
    (by simpa only [abs_of_pos h0] using h1) P (by
      simpa only [abs_of_pos h0] using hK.2.2.1)
  have htube' := c10_s3_stopped_tube_of_uniform_quenched_tube_phys hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK ε hε (by
      simpa only [abs_of_pos h0] using hbase) m A hA N
  exact coupling_scope_guard_estimate_of_tube_estimate μ (Renewal.regenDelta lam)
    (EinsteinRelation.regenDelta_pos h0) lam (l / lam) ε A m (Renewal.forceCoord hd) N htube'

end EinsteinFull.Regeneration
